//! Parser for one grundy statement or statement sequence.

use super::ast::{
    BinaryOp, Binding, DataSort, Expr, LambdaBinder, RelOp, StarLiteral, Statement, UnaryOp,
};
use super::error::{GrundyError, GrundyErrorKind, GrundyResult, Span};
use super::lex::{lex, Token, TokenKind};
use ogdoad::scalar::Ordinal;

/// Parse one complete source statement.
pub fn parse_statement(src: &str) -> GrundyResult<Statement> {
    let tokens = lex(src)?;
    let mut parser = Parser { tokens, pos: 0 };
    if parser.tokens.is_empty() {
        return Err(GrundyError::new(
            GrundyErrorKind::Parse,
            Span::point(0),
            "empty statement",
        ));
    }
    let stmt = parser.parse_statement_seq()?;
    parser.expect_end()?;
    Ok(stmt)
}

fn seq_value_error() -> GrundyError {
    GrundyError::new(
        GrundyErrorKind::SeqValue,
        Span::point(0),
        "intermediate program statements must be bindings",
    )
}

fn block_tail_error() -> GrundyError {
    GrundyError::new(
        GrundyErrorKind::SeqValue,
        Span::point(0),
        "a parenthesized body sequence must end in an expression",
    )
}

fn conditional_words_error(span: Span) -> GrundyError {
    GrundyError::new(
        GrundyErrorKind::Parse,
        span,
        "`?` and `:` are not conditional-expression syntax",
    )
    .with_hint("write conditionals as `if a then b else c`")
}

fn statement_to_block_expr(stmt: Statement) -> GrundyResult<Expr> {
    match stmt {
        Statement::Expr(expr) => Ok(expr),
        Statement::Binding { .. } => Err(block_tail_error()),
        Statement::Seq { bindings, tail } => match *tail {
            Statement::Expr(body) => Ok(Expr::Block {
                bindings,
                body: Box::new(body),
            }),
            Statement::Binding { .. } | Statement::Seq { .. } => Err(block_tail_error()),
        },
    }
}

fn seq_from_parts(bindings: Vec<Binding>, tail: Statement) -> Statement {
    if bindings.is_empty() {
        tail
    } else {
        Statement::Seq {
            bindings,
            tail: Box::new(tail),
        }
    }
}

fn index_expr(expr: Expr) -> Expr {
    if matches!(expr, Expr::Index(_)) {
        expr
    } else {
        Expr::Index(Box::new(expr))
    }
}

fn call_arg_is_index(name: &str, index: usize) -> bool {
    matches!(
        (name, index),
        ("grade" | "coef" | "left" | "right", 1) | ("tr", 1)
    )
}

impl Parser {
    fn parse_statement_seq(&mut self) -> GrundyResult<Statement> {
        let mut bindings = Vec::new();
        loop {
            let stmt = self.parse_single_statement()?;
            if !matches!(self.peek_kind(), Some(TokenKind::Semicolon)) {
                return Ok(seq_from_parts(bindings, stmt));
            }
            self.bump();
            match stmt {
                Statement::Binding {
                    name,
                    expr,
                    recursive,
                } => bindings.push(Binding {
                    name,
                    expr,
                    recursive,
                }),
                Statement::Expr(_) | Statement::Seq { .. } => return Err(seq_value_error()),
            }
        }
    }

    fn parse_single_statement(&mut self) -> GrundyResult<Statement> {
        if self.is_reserved_word_binding() {
            return Err(GrundyError::new(
                GrundyErrorKind::Reserved,
                self.span(),
                "reserved word cannot be rebound",
            ));
        }
        if let (Some(TokenKind::Ident(name)), Some(assign)) =
            (self.peek_kind(), self.peek_kind_at(1))
        {
            if !matches!(assign, TokenKind::Assign | TokenKind::RecursiveAssign) {
                return Ok(Statement::Expr(self.parse_lambda_or_expression()?));
            }
            let name = name.clone();
            let recursive = matches!(assign, TokenKind::RecursiveAssign);
            self.bump();
            self.bump();
            let expr = self.parse_lambda_or_expression()?;
            Ok(Statement::Binding {
                name,
                expr,
                recursive,
            })
        } else {
            Ok(Statement::Expr(self.parse_lambda_or_expression()?))
        }
    }
}

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }

    fn peek_kind(&self) -> Option<&TokenKind> {
        self.peek().map(|t| &t.kind)
    }

    fn peek_kind_at(&self, offset: usize) -> Option<&TokenKind> {
        self.tokens.get(self.pos + offset).map(|t| &t.kind)
    }

    fn span(&self) -> Span {
        self.peek().map_or(Span::point(0), |t| t.span)
    }

    fn bump(&mut self) -> Option<Token> {
        let tok = self.tokens.get(self.pos).cloned();
        if tok.is_some() {
            self.pos += 1;
        }
        tok
    }

    fn expect_end(&self) -> GrundyResult<()> {
        if let Some(tok) = self.peek() {
            if matches!(tok.kind, TokenKind::Question | TokenKind::Colon) {
                return Err(conditional_words_error(tok.span));
            }
            let err = GrundyError::new(
                GrundyErrorKind::Parse,
                tok.span,
                "unexpected trailing token",
            );
            Err(match tok.kind {
                TokenKind::Pipe => {
                    err.with_hint("the braceform bar is structural; fuzzy is `∥` (sugar `!`)")
                }
                TokenKind::Star => {
                    err.with_hint("`*` is the nimber prefix; the product is `⋅` (sugar `.`)")
                }
                TokenKind::Assign
                    if matches!(
                        self.tokens.first().map(|token| &token.kind),
                        Some(TokenKind::Ident(_))
                    ) && matches!(
                        self.tokens.get(1).map(|token| &token.kind),
                        Some(TokenKind::LParen)
                    ) =>
                {
                    err.with_hint("functions are lambdas: `name := x ↦ …`")
                }
                _ => err,
            })
        } else {
            Ok(())
        }
    }

    fn eat(&mut self, pred: impl FnOnce(&TokenKind) -> bool) -> Option<Token> {
        if self.peek_kind().is_some_and(pred) {
            self.bump()
        } else {
            None
        }
    }

    fn expect(&mut self, pred: impl FnOnce(&TokenKind) -> bool, what: &str) -> GrundyResult<Token> {
        self.eat(pred).ok_or_else(|| {
            GrundyError::new(
                GrundyErrorKind::Parse,
                self.span(),
                format!("expected {what}"),
            )
        })
    }

    fn is_reserved_word_binding(&self) -> bool {
        matches!(
            self.peek_kind(),
            Some(
                TokenKind::And
                    | TokenKind::Or
                    | TokenKind::Not
                    | TokenKind::If
                    | TokenKind::Then
                    | TokenKind::Else
                    | TokenKind::True
                    | TokenKind::False
                    | TokenKind::Up
                    | TokenKind::Down
                    | TokenKind::Dim
            )
        ) && matches!(
            self.peek_kind_at(1),
            Some(TokenKind::Assign | TokenKind::RecursiveAssign)
        )
    }

    fn parse_lambda_or_expression(&mut self) -> GrundyResult<Expr> {
        if let Some(binders) = self.try_parse_binders() {
            self.expect(|k| matches!(k, TokenKind::Arrow), "`↦`")?;
            let body = self.parse_lambda_or_expression()?;
            return Ok(Expr::Lambda {
                binders,
                body: Box::new(body),
            });
        }
        self.parse_expression()
    }

    fn try_parse_binders(&mut self) -> Option<Vec<LambdaBinder>> {
        let save = self.pos;
        let out = match self.peek_kind() {
            Some(TokenKind::Ident(_)) if matches!(self.peek_kind_at(1), Some(TokenKind::Arrow)) => {
                Some(vec![self.parse_lambda_binder().expect("peeked binder")])
            }
            Some(TokenKind::Index | TokenKind::Question)
                if matches!(self.peek_kind_at(1), Some(TokenKind::Ident(_)))
                    && matches!(self.peek_kind_at(2), Some(TokenKind::Arrow)) =>
            {
                Some(vec![self
                    .parse_lambda_binder()
                    .expect("peeked marked binder")])
            }
            Some(TokenKind::LParen) => {
                self.bump();
                let mut binders = Vec::new();
                loop {
                    let Some(binder) = self.parse_lambda_binder() else {
                        self.pos = save;
                        return None;
                    };
                    binders.push(binder);
                    if !matches!(self.peek_kind(), Some(TokenKind::Comma)) {
                        break;
                    }
                    self.bump();
                }
                if !matches!(self.peek_kind(), Some(TokenKind::RParen)) {
                    self.pos = save;
                    return None;
                }
                self.bump();
                if matches!(self.peek_kind(), Some(TokenKind::Arrow)) {
                    Some(binders)
                } else {
                    self.pos = save;
                    return None;
                }
            }
            _ => None,
        };
        if out.is_none() {
            self.pos = save;
        }
        out
    }

    fn parse_lambda_binder(&mut self) -> Option<LambdaBinder> {
        let declared_sort = match self.peek_kind() {
            Some(TokenKind::Index) => {
                self.bump();
                Some(DataSort::Index)
            }
            Some(TokenKind::Question) => {
                self.bump();
                Some(DataSort::Bool)
            }
            _ => None,
        };
        let Some(Token {
            kind: TokenKind::Ident(name),
            ..
        }) = self.bump()
        else {
            return None;
        };
        Some(LambdaBinder {
            name,
            declared_sort,
        })
    }

    fn parse_expression(&mut self) -> GrundyResult<Expr> {
        if matches!(
            self.peek_kind(),
            Some(TokenKind::Question | TokenKind::Colon)
        ) {
            return Err(conditional_words_error(self.span()));
        }
        if matches!(self.peek_kind(), Some(TokenKind::If)) {
            self.bump();
            let cond = self.parse_expression()?;
            self.expect(|kind| matches!(kind, TokenKind::Then), "`then`")?;
            let then_expr = self.parse_expression()?;
            self.expect(|kind| matches!(kind, TokenKind::Else), "`else`")?;
            let else_expr = self.parse_expression()?;
            return Ok(Expr::If {
                cond: Box::new(cond),
                then_expr: Box::new(then_expr),
                else_expr: Box::new(else_expr),
            });
        }
        let expr = self.parse_or()?;
        if matches!(
            self.peek_kind(),
            Some(TokenKind::Question | TokenKind::Colon)
        ) {
            return Err(conditional_words_error(self.span()));
        }
        Ok(expr)
    }

    fn parse_or(&mut self) -> GrundyResult<Expr> {
        let mut expr = self.parse_and()?;
        while matches!(self.peek_kind(), Some(TokenKind::Or)) {
            self.bump();
            let rhs = self.parse_and()?;
            expr = Expr::Binary {
                op: BinaryOp::Or,
                lhs: Box::new(expr),
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_and(&mut self) -> GrundyResult<Expr> {
        let mut expr = self.parse_not()?;
        while matches!(self.peek_kind(), Some(TokenKind::And)) {
            self.bump();
            let rhs = self.parse_not()?;
            expr = Expr::Binary {
                op: BinaryOp::And,
                lhs: Box::new(expr),
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_not(&mut self) -> GrundyResult<Expr> {
        if matches!(self.peek_kind(), Some(TokenKind::Not)) {
            self.bump();
            let expr = self.parse_not()?;
            return Ok(Expr::Unary {
                op: UnaryOp::Not,
                expr: Box::new(expr),
            });
        }
        self.parse_relation()
    }

    fn parse_relation(&mut self) -> GrundyResult<Expr> {
        let lhs = self.parse_append()?;
        let Some(op) = self.parse_relop()? else {
            return Ok(lhs);
        };
        if op == RelOp::Fuzzy && matches!(self.peek_kind(), Some(TokenKind::Eq)) {
            return Err(GrundyError::new(
                GrundyErrorKind::Parse,
                self.span(),
                "not-equal is `not (a = b)`",
            )
            .with_hint("not-equal is `not (a = b)`; `!` is fuzzy `∥`"));
        }
        let rhs = self.parse_append()?;
        if self.parse_relop()?.is_some() {
            return Err(GrundyError::new(
                GrundyErrorKind::Parse,
                self.span(),
                "relations are top-level and non-associative",
            ));
        }
        Ok(Expr::Relation {
            op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        })
    }

    fn parse_relop(&mut self) -> GrundyResult<Option<RelOp>> {
        let Some(kind) = self.peek_kind() else {
            return Ok(None);
        };
        Ok(match kind {
            TokenKind::Eq => {
                self.bump();
                Some(RelOp::Eq)
            }
            TokenKind::Less => {
                self.bump();
                Some(RelOp::Lt)
            }
            TokenKind::Greater => {
                self.bump();
                Some(RelOp::Gt)
            }
            TokenKind::Parallel => {
                self.bump();
                Some(RelOp::Fuzzy)
            }
            TokenKind::Equiv => {
                self.bump();
                Some(RelOp::Equiv)
            }
            TokenKind::Outcome(cell) => {
                let cell = *cell;
                self.bump();
                Some(RelOp::Outcome(cell))
            }
            TokenKind::DrawAtom => {
                return Err(GrundyError::new(
                    GrundyErrorKind::Parse,
                    self.span(),
                    "mover-result atoms come in pairs",
                )
                .with_hint("mover-result atoms come in pairs"));
            }
            _ => None,
        })
    }

    fn parse_append(&mut self) -> GrundyResult<Expr> {
        let lhs = self.parse_additive()?;
        if !matches!(self.peek_kind(), Some(TokenKind::Append)) {
            return Ok(lhs);
        }
        self.bump();
        let rhs = self.parse_append()?;
        Ok(Expr::Binary {
            op: BinaryOp::Append,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        })
    }

    fn parse_additive(&mut self) -> GrundyResult<Expr> {
        let mut expr = self.parse_mulexpr()?;
        loop {
            let op = match self.peek_kind() {
                Some(TokenKind::Plus) => BinaryOp::Add,
                Some(TokenKind::Minus) => BinaryOp::Sub,
                _ => break,
            };
            self.bump();
            let rhs = self.parse_mulexpr()?;
            expr = Expr::Binary {
                op,
                lhs: Box::new(expr),
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_mulexpr(&mut self) -> GrundyResult<Expr> {
        let mut expr = self.parse_wedge()?;
        loop {
            let op = match self.peek_kind() {
                Some(TokenKind::Dot) => BinaryOp::Mul,
                Some(TokenKind::Slash) => BinaryOp::Div,
                Some(TokenKind::Percent) => BinaryOp::Rem,
                _ => break,
            };
            self.bump();
            let rhs = self.parse_wedge()?;
            expr = Expr::Binary {
                op,
                lhs: Box::new(expr),
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_wedge(&mut self) -> GrundyResult<Expr> {
        let mut expr = self.parse_unary()?;
        while matches!(self.peek_kind(), Some(TokenKind::Wedge)) {
            self.bump();
            let rhs = self.parse_unary()?;
            expr = Expr::Binary {
                op: BinaryOp::Wedge,
                lhs: Box::new(expr),
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_unary(&mut self) -> GrundyResult<Expr> {
        let mut ops = Vec::new();
        loop {
            match self.peek_kind() {
                Some(TokenKind::Minus) => {
                    self.bump();
                    ops.push(UnaryOp::Neg);
                }
                Some(TokenKind::Slash) => {
                    self.bump();
                    ops.push(UnaryOp::Inv);
                }
                _ => break,
            }
        }
        let mut expr = self.parse_power()?;
        for op in ops.into_iter().rev() {
            expr = Expr::Unary {
                op,
                expr: Box::new(expr),
            };
        }
        Ok(expr)
    }

    fn parse_power(&mut self) -> GrundyResult<Expr> {
        let base = self.parse_appl()?;
        if !matches!(self.peek_kind(), Some(TokenKind::Power)) {
            return Ok(base);
        }
        self.bump();
        let rhs = if matches!(self.peek_kind(), Some(TokenKind::Minus))
            && matches!(self.peek_kind_at(1), Some(TokenKind::Int(_)))
        {
            self.bump();
            let tok = self.bump().expect("peeked int");
            let TokenKind::Int(n) = tok.kind else {
                unreachable!()
            };
            Expr::Unary {
                op: UnaryOp::Neg,
                expr: Box::new(Expr::Int(n)),
            }
        } else {
            self.parse_power()?
        };
        // The base-`ω` exception accepts a Scalar exponent in surreal-family
        // worlds. Leaving it unwrapped also keeps an explicit `#(...)` as an
        // Index assertion instead of silently lowering it to that exception.
        let omega_base = base.is_omega_atom();
        Ok(Expr::Binary {
            op: BinaryOp::Pow,
            lhs: Box::new(base),
            rhs: Box::new(if omega_base { rhs } else { index_expr(rhs) }),
        })
    }

    fn parse_appl(&mut self) -> GrundyResult<Expr> {
        let mut expr = self.parse_atom()?;
        while matches!(self.peek_kind(), Some(TokenKind::At)) {
            self.bump();
            let args = self.parse_appl_args()?;
            expr = Expr::Apply {
                callee: Box::new(expr),
                args,
            };
        }
        Ok(expr)
    }

    fn parse_appl_args(&mut self) -> GrundyResult<Vec<Expr>> {
        if !matches!(self.peek_kind(), Some(TokenKind::LParen)) {
            return self.parse_atom().map(|expr| vec![expr]);
        }
        self.bump();
        let first = statement_to_block_expr(self.parse_statement_seq()?)?;
        if !matches!(self.peek_kind(), Some(TokenKind::Comma)) {
            self.expect(|k| matches!(k, TokenKind::RParen), "`)`")?;
            return Ok(vec![first]);
        }
        let mut items = vec![first];
        while matches!(self.peek_kind(), Some(TokenKind::Comma)) {
            self.bump();
            items.push(statement_to_block_expr(self.parse_statement_seq()?)?);
        }
        self.expect(|k| matches!(k, TokenKind::RParen), "`)`")?;
        Ok(items)
    }

    fn parse_call_args(&mut self, name: &str) -> GrundyResult<Vec<Expr>> {
        self.expect(|kind| matches!(kind, TokenKind::LParen), "`(`")?;
        let mut args = Vec::new();
        if !matches!(self.peek_kind(), Some(TokenKind::RParen)) {
            loop {
                let expr = self.parse_expression()?;
                let index = args.len();
                args.push(if call_arg_is_index(name, index) {
                    index_expr(expr)
                } else {
                    expr
                });
                if !matches!(self.peek_kind(), Some(TokenKind::Comma)) {
                    break;
                }
                self.bump();
            }
        }
        self.expect(|kind| matches!(kind, TokenKind::RParen), "`)`")?;
        Ok(args)
    }

    fn parse_literal_atom(&mut self, name: &str, atom: Expr) -> GrundyResult<Expr> {
        if matches!(self.peek_kind(), Some(TokenKind::LParen)) {
            Ok(Expr::Call {
                name: name.to_string(),
                args: self.parse_call_args(name)?,
            })
        } else {
            Ok(atom)
        }
    }

    fn parse_atom(&mut self) -> GrundyResult<Expr> {
        let tok = self.bump().ok_or_else(|| {
            GrundyError::new(GrundyErrorKind::Parse, Span::point(0), "expected atom")
        })?;
        match tok.kind {
            TokenKind::Int(n) => Ok(Expr::Int(n)),
            TokenKind::True => Ok(Expr::Bool(true)),
            TokenKind::False => Ok(Expr::Bool(false)),
            TokenKind::Star => self.parse_star(),
            TokenKind::Index => self.parse_index(),
            TokenKind::Omega => Ok(Expr::Omega),
            TokenKind::Blade(i) => Ok(Expr::Blade(i)),
            TokenKind::Up => self.parse_literal_atom("up", Expr::Up),
            TokenKind::Down => self.parse_literal_atom("down", Expr::Down),
            TokenKind::Dim => self.parse_literal_atom("dim", Expr::Dim),
            TokenKind::Ident(name) => {
                if matches!(self.peek_kind(), Some(TokenKind::LParen)) {
                    let args = self.parse_call_args(&name)?;
                    Ok(Expr::Call { name, args })
                } else {
                    Ok(Expr::Ident(name))
                }
            }
            TokenKind::LParen => {
                let expr = statement_to_block_expr(self.parse_statement_seq()?)?;
                self.expect(|k| matches!(k, TokenKind::RParen), "`)`")?;
                Ok(expr)
            }
            TokenKind::LBracket => {
                let mut items = Vec::new();
                if !matches!(self.peek_kind(), Some(TokenKind::RBracket)) {
                    loop {
                        items.push(statement_to_block_expr(self.parse_statement_seq()?)?);
                        if !matches!(self.peek_kind(), Some(TokenKind::Comma)) {
                            break;
                        }
                        self.bump();
                    }
                }
                self.expect(|k| matches!(k, TokenKind::RBracket), "`]`")?;
                Ok(Expr::Container(items))
            }
            TokenKind::LBrace => self.parse_braceform(),
            TokenKind::Question | TokenKind::Colon => Err(conditional_words_error(tok.span)),
            _ => Err(GrundyError::new(
                GrundyErrorKind::Parse,
                tok.span,
                "expected atom",
            )),
        }
    }

    fn parse_braceform(&mut self) -> GrundyResult<Expr> {
        if matches!(self.peek_kind(), Some(TokenKind::RBrace)) {
            return Err(GrundyError::new(
                GrundyErrorKind::Parse,
                self.span(),
                "game forms require a structural bar",
            )
            .with_hint("`[]` is the empty list; braces are game forms `{L | R}`"));
        }

        let mut first = Vec::new();
        if !matches!(self.peek_kind(), Some(TokenKind::Pipe)) {
            first = self.parse_brace_items()?;
        }
        if !matches!(self.peek_kind(), Some(TokenKind::Pipe)) {
            return Err(GrundyError::new(
                GrundyErrorKind::Parse,
                self.span(),
                "game forms require a structural bar",
            )
            .with_hint("`[a, b]` is the list; braces are game forms `{L | R}`"));
        }
        self.bump();
        let right = if matches!(self.peek_kind(), Some(TokenKind::RBrace)) {
            Vec::new()
        } else {
            self.parse_brace_items()?
        };
        self.expect(|k| matches!(k, TokenKind::RBrace), "`}`")?;
        Ok(Expr::GameForm { left: first, right })
    }

    fn parse_brace_items(&mut self) -> GrundyResult<Vec<Expr>> {
        let mut items = vec![self.parse_brace_item()?];
        while matches!(self.peek_kind(), Some(TokenKind::Comma)) {
            self.bump();
            items.push(self.parse_brace_item()?);
        }
        Ok(items)
    }

    fn parse_brace_item(&mut self) -> GrundyResult<Expr> {
        let start = self.pos;
        let mut depth = 0usize;
        let mut end = start;
        while let Some(token) = self.tokens.get(end) {
            match token.kind {
                TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
                TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace if depth > 0 => {
                    depth -= 1
                }
                TokenKind::Comma | TokenKind::Pipe | TokenKind::RBrace if depth == 0 => break,
                _ => {}
            }
            end += 1;
        }
        if end == start {
            return Err(GrundyError::new(
                GrundyErrorKind::Parse,
                self.span(),
                "expected expression in braces",
            ));
        }
        let mut nested = Parser {
            tokens: self.tokens[start..end].to_vec(),
            pos: 0,
        };
        let expr = nested.parse_lambda_or_expression()?;
        nested.expect_end()?;
        self.pos = end;
        Ok(expr)
    }

    fn parse_star(&mut self) -> GrundyResult<Expr> {
        match self.peek_kind() {
            Some(TokenKind::Int(n)) => {
                let n = *n;
                self.bump();
                Ok(Expr::Star(StarLiteral::Finite(n)))
            }
            Some(TokenKind::Omega) => {
                self.bump();
                Ok(Expr::Star(StarLiteral::Cnf(Ordinal::omega())))
            }
            Some(TokenKind::LParen) => {
                self.bump();
                let cnf = self.parse_cnf()?;
                self.expect(|k| matches!(k, TokenKind::RParen), "`)`")?;
                Ok(Expr::Star(StarLiteral::Cnf(cnf)))
            }
            _ => Ok(Expr::Star(StarLiteral::Finite(1))),
        }
    }

    fn parse_index(&mut self) -> GrundyResult<Expr> {
        match self.peek_kind() {
            Some(TokenKind::Int(n)) => {
                let n = *n;
                self.bump();
                Ok(Expr::Index(Box::new(Expr::Int(n))))
            }
            Some(TokenKind::LParen) => {
                self.bump();
                let expr = self.parse_expression()?;
                self.expect(|kind| matches!(kind, TokenKind::RParen), "`)`")?;
                Ok(index_expr(expr))
            }
            _ => Err(GrundyError::new(
                GrundyErrorKind::Parse,
                self.span(),
                "`#` needs an Index literal or parenthesized Index expression",
            )),
        }
    }

    fn parse_cnf(&mut self) -> GrundyResult<Ordinal> {
        let mut terms = Vec::<(Ordinal, u128)>::new();
        loop {
            terms.push(self.parse_cnf_term()?);
            if !matches!(self.peek_kind(), Some(TokenKind::Plus)) {
                break;
            }
            self.bump();
        }
        for pair in terms.windows(2) {
            if pair[0].0.cmp(&pair[1].0) != std::cmp::Ordering::Greater {
                return Err(GrundyError::new(
                    GrundyErrorKind::CnfOrder,
                    self.span(),
                    "CNF exponents must be strictly descending",
                )
                .with_hint("CNF indices are structural: write `*(ω + 1)`, not `*(1 + ω)`"));
            }
        }
        let mut out = Ordinal::from_u128(0);
        for (exp, coeff) in terms {
            let term = if exp.is_zero() {
                Ordinal::from_u128(coeff)
            } else {
                Ordinal::monomial(exp, coeff)
            };
            out = out.nim_add(&term);
        }
        Ok(out)
    }

    fn parse_cnf_term(&mut self) -> GrundyResult<(Ordinal, u128)> {
        match self.bump() {
            Some(Token {
                kind: TokenKind::Int(n),
                ..
            }) => Ok((Ordinal::from_u128(0), n)),
            Some(Token {
                kind: TokenKind::Omega,
                ..
            }) => {
                let exp = if matches!(self.peek_kind(), Some(TokenKind::Power)) {
                    self.bump();
                    self.parse_cnf_exp()?
                } else {
                    Ordinal::from_u128(1)
                };
                let coeff = if matches!(self.peek_kind(), Some(TokenKind::Dot)) {
                    self.bump();
                    match self.bump() {
                        Some(Token {
                            kind: TokenKind::Int(n),
                            ..
                        }) => n,
                        Some(tok) => {
                            return Err(GrundyError::new(
                                GrundyErrorKind::Parse,
                                tok.span,
                                "expected finite CNF coefficient",
                            ));
                        }
                        None => {
                            return Err(GrundyError::new(
                                GrundyErrorKind::Parse,
                                Span::point(0),
                                "expected finite CNF coefficient",
                            ));
                        }
                    }
                } else {
                    1
                };
                Ok((exp, coeff))
            }
            Some(tok) => Err(GrundyError::new(
                GrundyErrorKind::Parse,
                tok.span,
                "expected CNF term",
            )),
            None => Err(GrundyError::new(
                GrundyErrorKind::Parse,
                Span::point(0),
                "expected CNF term",
            )),
        }
    }

    fn parse_cnf_exp(&mut self) -> GrundyResult<Ordinal> {
        match self.bump() {
            Some(Token {
                kind: TokenKind::Int(n),
                ..
            }) => Ok(Ordinal::from_u128(n)),
            Some(Token {
                kind: TokenKind::Omega,
                ..
            }) => {
                if matches!(self.peek_kind(), Some(TokenKind::Power)) {
                    self.bump();
                    let exp = self.parse_cnf_exp()?;
                    Ok(Ordinal::omega_pow(exp))
                } else {
                    Ok(Ordinal::omega())
                }
            }
            Some(Token {
                kind: TokenKind::LParen,
                ..
            }) => {
                let cnf = self.parse_cnf()?;
                self.expect(|k| matches!(k, TokenKind::RParen), "`)`")?;
                Ok(cnf)
            }
            Some(tok) => Err(GrundyError::new(
                GrundyErrorKind::Parse,
                tok.span,
                "expected CNF exponent",
            )),
            None => Err(GrundyError::new(
                GrundyErrorKind::Parse,
                Span::point(0),
                "expected CNF exponent",
            )),
        }
    }
}
