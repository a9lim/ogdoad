//! Recursive-descent parser from tokens to syntax trees.
//!
//! The grammar is world- and type-independent: every literal form parses
//! everywhere, and the type checker decides legality.

use super::super::error::{GrundyError, GrundyErrorKind, GrundyResult, Span};
use super::ast::*;
use super::lex::{lex, Keyword, Tok, Token};

/// The deepest nesting the parser accepts before refusing the input.
pub const NESTING_LIMIT: usize = 1536;

/// Parse one statement (a data declaration, or bindings and an optional
/// final expression).
pub fn parse_statement(src: &str) -> GrundyResult<Stmt> {
    let tokens = lex(src)?;
    check_delimiter_depth(&tokens)?;
    let mut parser = Parser {
        src,
        tokens,
        pos: 0,
        depth: 0,
    };
    let stmt = parser.statement()?;
    parser.expect_end()?;
    Ok(stmt)
}

/// Parse a standalone expression.
pub fn parse_expr(src: &str) -> GrundyResult<Expr> {
    let tokens = lex(src)?;
    check_delimiter_depth(&tokens)?;
    let mut parser = Parser {
        src,
        tokens,
        pos: 0,
        depth: 0,
    };
    let expr = parser.expr()?;
    parser.expect_end()?;
    Ok(expr)
}

/// Parse a standalone type expression.
pub fn parse_type(src: &str) -> GrundyResult<TypeExpr> {
    let tokens = lex(src)?;
    check_delimiter_depth(&tokens)?;
    let mut parser = Parser {
        src,
        tokens,
        pos: 0,
        depth: 0,
    };
    let ty = parser.ty()?;
    parser.expect_end()?;
    Ok(ty)
}

fn check_delimiter_depth(tokens: &[Token]) -> GrundyResult<()> {
    let mut depth = 0usize;
    for token in tokens {
        match token.kind {
            Tok::LParen | Tok::LBracket | Tok::LBrace => {
                depth += 1;
                if depth > NESTING_LIMIT {
                    return Err(GrundyError::new(
                        GrundyErrorKind::Parse,
                        token.span,
                        format!("source nesting exceeds {NESTING_LIMIT} delimiters"),
                    ));
                }
            }
            Tok::RParen | Tok::RBracket | Tok::RBrace => depth = depth.saturating_sub(1),
            _ => {}
        }
    }
    Ok(())
}

struct Parser<'a> {
    src: &'a str,
    tokens: Vec<Token>,
    pos: usize,
    depth: usize,
}

type PResult<T> = GrundyResult<T>;

impl Parser<'_> {
    // ---------------------------------------------------------------- helpers

    fn peek(&self) -> Option<&Tok> {
        self.tokens.get(self.pos).map(|token| &token.kind)
    }

    fn peek_at(&self, offset: usize) -> Option<&Tok> {
        self.tokens.get(self.pos + offset).map(|token| &token.kind)
    }

    fn span_here(&self) -> Span {
        self.tokens
            .get(self.pos)
            .map(|token| token.span)
            .unwrap_or_else(|| Span::point(self.src.len()))
    }

    fn prev_end(&self) -> usize {
        self.pos
            .checked_sub(1)
            .and_then(|index| self.tokens.get(index))
            .map_or(0, |token| token.span.end)
    }

    fn bump(&mut self) -> Token {
        let token = self.tokens[self.pos].clone();
        self.pos += 1;
        token
    }

    fn eat(&mut self, tok: &Tok) -> bool {
        if self.peek() == Some(tok) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, tok: &Tok, what: &str) -> PResult<Span> {
        if self.peek() == Some(tok) {
            Ok(self.bump().span)
        } else {
            Err(self.error_here(format!("expected {what}")))
        }
    }

    fn error_here(&self, message: impl Into<String>) -> GrundyError {
        GrundyError::new(GrundyErrorKind::Parse, self.span_here(), message)
    }

    fn expect_end(&self) -> PResult<()> {
        match self.peek() {
            None => Ok(()),
            Some(Tok::Bar) => Err(self
                .error_here("unexpected `|` outside a game form")
                .with_hint("the brace bar is structural; fuzzy is `∥` (sugar `!`)")),
            Some(Tok::Semi) => Err(self
                .error_here("only bindings may precede `;`")
                .with_hint("a discarded value is dead code; bind it with `name := …`")),
            Some(Tok::Star) => Err(self
                .error_here("unexpected `*` after a complete operand")
                .with_hint("`*` is the nimber prefix; the product is `⋅` (sugar `.`)")),
            Some(tok) if is_relop(tok) => Err(self
                .error_here("relations don't chain")
                .with_hint("parenthesize the Bool: `(a < b) = c`")),
            _ => Err(self.error_here("unexpected trailing token")),
        }
    }

    fn enter(&mut self) -> PResult<()> {
        self.depth += 1;
        if self.depth > NESTING_LIMIT {
            Err(self.error_here(format!("expression nesting exceeds {NESTING_LIMIT} levels")))
        } else {
            Ok(())
        }
    }

    fn leave(&mut self) {
        self.depth -= 1;
    }

    /// Position of the token matching the open delimiter at `self.pos`.
    fn matching_close(&self, from: usize) -> Option<usize> {
        let mut depth = 0usize;
        for (index, token) in self.tokens.iter().enumerate().skip(from) {
            match token.kind {
                Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
                Tok::RParen | Tok::RBracket | Tok::RBrace => {
                    depth -= 1;
                    if depth == 0 {
                        return Some(index);
                    }
                }
                _ => {}
            }
        }
        None
    }

    // ------------------------------------------------------------- statements

    fn statement(&mut self) -> PResult<Stmt> {
        if self.peek() == Some(&Tok::Kw(Keyword::Data)) {
            return self.data_decl().map(Stmt::Data);
        }
        let mut bindings = Vec::new();
        loop {
            if self.at_binding() {
                bindings.push(self.binding()?);
                if self.eat(&Tok::Semi) {
                    continue;
                }
                return Ok(Stmt::Seq(bindings, None));
            }
            let expr = self.expr()?;
            if self.peek() == Some(&Tok::Semi) {
                return Err(self
                    .error_here("only bindings may precede `;`")
                    .with_hint("a discarded value is dead code; bind it with `name := …`"));
            }
            return Ok(Stmt::Seq(bindings, Some(expr)));
        }
    }

    fn data_decl(&mut self) -> PResult<DataDecl> {
        let start = self.bump().span;
        let name = match self.peek() {
            Some(Tok::Upper(name)) => name.clone(),
            _ => return Err(self.error_here("expected an uppercase type name after `data`")),
        };
        self.pos += 1;
        self.expect(&Tok::Eq, "`=` after the data type name")?;
        let mut ctors = Vec::new();
        loop {
            let span = self.span_here();
            let ctor = match self.peek() {
                Some(Tok::Upper(ctor)) => ctor.clone(),
                _ => return Err(self.error_here("expected an uppercase constructor name")),
            };
            self.pos += 1;
            let mut fields = Vec::new();
            if self.eat(&Tok::LParen) {
                loop {
                    fields.push(self.ty()?);
                    if self.eat(&Tok::Comma) {
                        continue;
                    }
                    self.expect(&Tok::RParen, "`)` after constructor fields")?;
                    break;
                }
            }
            ctors.push(CtorDecl {
                name: ctor,
                fields,
                span: span.join(Span::point(self.prev_end())),
            });
            if !self.eat(&Tok::Bar) {
                break;
            }
        }
        Ok(DataDecl {
            name,
            ctors,
            span: start.join(Span::point(self.prev_end())),
        })
    }

    /// Whether the tokens at the cursor begin `pattern := …` or `name =: …`.
    fn at_binding(&mut self) -> bool {
        let saved = (self.pos, self.depth);
        let ok = self.pattern().is_ok()
            && matches!(self.peek(), Some(Tok::Assign) | Some(Tok::RecAssign));
        (self.pos, self.depth) = saved;
        ok
    }

    fn binding(&mut self) -> PResult<Binding> {
        let start = self.span_here();
        let pat = self.pattern()?;
        let kind = match self.peek() {
            Some(Tok::Assign) => BindKind::Let,
            Some(Tok::RecAssign) => BindKind::Rec,
            _ => return Err(self.error_here("expected `:=` or `=:`")),
        };
        self.pos += 1;
        if kind == BindKind::Rec && !matches!(pat.kind, PatKind::Var(_)) {
            return Err(GrundyError::new(
                GrundyErrorKind::Parse,
                pat.span,
                "a recursive binding names one variable",
            )
            .with_hint("destructure afterwards: `x =: …; (a, b) := x`"));
        }
        let expr = self.expr()?;
        Ok(Binding {
            pat,
            kind,
            span: start.join(expr.span),
            expr,
        })
    }

    // ------------------------------------------------------------ expressions

    fn expr(&mut self) -> PResult<Expr> {
        self.enter()?;
        let result = self.expr_inner();
        self.leave();
        result
    }

    fn expr_inner(&mut self) -> PResult<Expr> {
        if let Some(params_end) = self.lambda_params_end() {
            return self.lambda(params_end);
        }
        let expr = self.cond()?;
        if self.eat(&Tok::Colon) {
            let ty = self.ty()?;
            let span = expr.span.join(ty.span);
            return Ok(Expr::new(ExprKind::Annot(Box::new(expr), ty), span));
        }
        Ok(expr)
    }

    /// If a lambda starts here, the index of the `↦`.
    fn lambda_params_end(&self) -> Option<usize> {
        match self.peek()? {
            Tok::Ident(_) | Tok::Underscore if self.peek_at(1) == Some(&Tok::MapsTo) => {
                Some(self.pos + 1)
            }
            Tok::LParen => {
                let close = self.matching_close(self.pos)?;
                (self.tokens.get(close + 1).map(|token| &token.kind) == Some(&Tok::MapsTo))
                    .then_some(close + 1)
            }
            _ => None,
        }
    }

    fn lambda(&mut self, arrow: usize) -> PResult<Expr> {
        let start = self.span_here();
        let mut params = Vec::new();
        if self.peek() == Some(&Tok::LParen) {
            self.pos += 1;
            if !self.eat(&Tok::RParen) {
                loop {
                    let pat = self.pattern()?;
                    let ty = if self.eat(&Tok::Colon) {
                        Some(self.ty()?)
                    } else {
                        None
                    };
                    params.push(Param { pat, ty });
                    if self.eat(&Tok::Comma) {
                        continue;
                    }
                    self.expect(&Tok::RParen, "`)` after lambda parameters")?;
                    break;
                }
            }
        } else {
            params.push(Param {
                pat: self.pattern()?,
                ty: None,
            });
        }
        if self.pos != arrow {
            return Err(self.error_here("expected `↦` after lambda parameters"));
        }
        self.pos += 1;
        let body = self.expr()?;
        let span = start.join(body.span);
        Ok(Expr::new(ExprKind::Lambda(params, Box::new(body)), span))
    }

    fn cond(&mut self) -> PResult<Expr> {
        match self.peek() {
            Some(Tok::Kw(Keyword::If)) => {
                let start = self.bump().span;
                let cond = self.expr()?;
                self.expect(&Tok::Kw(Keyword::Then), "`then`")?;
                let then_branch = self.expr()?;
                if self.peek() != Some(&Tok::Kw(Keyword::Else)) {
                    return Err(self
                        .error_here("expected `else`")
                        .with_hint("every expression has a value; `else` is mandatory"));
                }
                self.pos += 1;
                let else_branch = self.expr()?;
                let span = start.join(else_branch.span);
                Ok(Expr::new(
                    ExprKind::If(Box::new(cond), Box::new(then_branch), Box::new(else_branch)),
                    span,
                ))
            }
            Some(Tok::Kw(Keyword::Match)) => {
                let start = self.bump().span;
                let scrutinee = self.or_expr()?;
                self.expect(&Tok::LBrace, "`{` opening the match arms")?;
                let mut arms = Vec::new();
                while self.peek() != Some(&Tok::RBrace) {
                    let pat = self.pattern()?;
                    self.expect(&Tok::MapsTo, "`↦` after a match pattern")?;
                    let body = self.expr()?;
                    arms.push((pat, body));
                    if !self.eat(&Tok::Comma) {
                        break;
                    }
                }
                let end = self.expect(&Tok::RBrace, "`}` closing the match arms")?;
                if arms.is_empty() {
                    return Err(GrundyError::new(
                        GrundyErrorKind::Parse,
                        start.join(end),
                        "a match needs at least one arm",
                    ));
                }
                Ok(Expr::new(
                    ExprKind::Match(Box::new(scrutinee), arms),
                    start.join(end),
                ))
            }
            _ => self.or_expr(),
        }
    }

    fn or_expr(&mut self) -> PResult<Expr> {
        let mut lhs = self.and_expr()?;
        while self.eat(&Tok::Kw(Keyword::Or)) {
            let rhs = self.and_expr()?;
            lhs = binary(BinaryOp::Or, lhs, rhs);
        }
        Ok(lhs)
    }

    fn and_expr(&mut self) -> PResult<Expr> {
        let mut lhs = self.not_expr()?;
        while self.eat(&Tok::Kw(Keyword::And)) {
            let rhs = self.not_expr()?;
            lhs = binary(BinaryOp::And, lhs, rhs);
        }
        Ok(lhs)
    }

    fn not_expr(&mut self) -> PResult<Expr> {
        if self.peek() == Some(&Tok::Kw(Keyword::Not)) {
            let start = self.bump().span;
            self.enter()?;
            let inner = self.not_expr();
            self.leave();
            let inner = inner?;
            let span = start.join(inner.span);
            return Ok(Expr::new(
                ExprKind::Unary(UnaryOp::Not, Box::new(inner)),
                span,
            ));
        }
        self.rel_expr()
    }

    fn rel_expr(&mut self) -> PResult<Expr> {
        let lhs = self.cat_expr()?;
        let Some(op) = self.peek().and_then(relop_of) else {
            return Ok(lhs);
        };
        self.pos += 1;
        if op == RelOp::Fuzzy && self.peek() == Some(&Tok::Eq) {
            return Err(self
                .error_here("`!=` is not an operator")
                .with_hint("not-equal is `not (a = b)`; `!` is fuzzy `∥`"));
        }
        let rhs = self.cat_expr()?;
        if self.peek().and_then(relop_of).is_some() {
            return Err(self
                .error_here("relations don't chain")
                .with_hint("parenthesize the Bool: `(a < b) = c`"));
        }
        let span = lhs.span.join(rhs.span);
        Ok(Expr::new(
            ExprKind::Relation(op, Box::new(lhs), Box::new(rhs)),
            span,
        ))
    }

    fn cat_expr(&mut self) -> PResult<Expr> {
        let lhs = self.range_expr()?;
        if self.eat(&Tok::Concat) {
            self.enter()?;
            let rhs = self.cat_expr();
            self.leave();
            return Ok(binary(BinaryOp::Concat, lhs, rhs?));
        }
        Ok(lhs)
    }

    fn range_expr(&mut self) -> PResult<Expr> {
        let lo = self.additive()?;
        let inclusive = match self.peek() {
            Some(Tok::DotDot) => false,
            Some(Tok::DotDotEq) => true,
            _ => return Ok(lo),
        };
        self.pos += 1;
        let hi = self.additive()?;
        let span = lo.span.join(hi.span);
        Ok(Expr::new(
            ExprKind::Range {
                lo: Box::new(lo),
                hi: Box::new(hi),
                inclusive,
            },
            span,
        ))
    }

    fn additive(&mut self) -> PResult<Expr> {
        let mut lhs = self.mul_expr()?;
        loop {
            let op = match self.peek() {
                Some(Tok::Plus) => BinaryOp::Add,
                Some(Tok::Minus) => BinaryOp::Sub,
                _ => return Ok(lhs),
            };
            self.pos += 1;
            let rhs = self.mul_expr()?;
            lhs = binary(op, lhs, rhs);
        }
    }

    fn mul_expr(&mut self) -> PResult<Expr> {
        let mut lhs = self.wedge()?;
        loop {
            let op = match self.peek() {
                Some(Tok::Dot) => BinaryOp::Mul,
                Some(Tok::Slash) => BinaryOp::Div,
                Some(Tok::Percent) => BinaryOp::Rem,
                Some(Tok::Star) => {
                    return Err(self
                        .error_here("unexpected `*` after a complete operand")
                        .with_hint("`*` is the nimber prefix; the product is `⋅` (sugar `.`)"))
                }
                _ => return Ok(lhs),
            };
            self.pos += 1;
            let rhs = self.wedge()?;
            if op == BinaryOp::Div {
                if let (Some(num), Some(den)) = (self.literal_int(&lhs), self.literal_int(&rhs)) {
                    if let Some(frac) = fraction(num, den) {
                        let span = lhs.span.join(rhs.span);
                        lhs = Expr::new(frac, span);
                        continue;
                    }
                }
            }
            lhs = binary(op, lhs, rhs);
        }
    }

    /// A signed integer literal written without parentheses: `7` or `-7`.
    fn literal_int(&self, expr: &Expr) -> Option<i128> {
        let first = self.src[expr.span.start..].chars().next()?;
        match &expr.kind {
            ExprKind::Int(n) if first.is_ascii_digit() => i128::try_from(*n).ok(),
            ExprKind::Unary(UnaryOp::Neg, inner) if first == '-' => match inner.kind {
                ExprKind::Int(n)
                    if self.src[inner.span.start..]
                        .chars()
                        .next()
                        .is_some_and(|c| c.is_ascii_digit()) =>
                {
                    i128::try_from(n).ok().map(|n| -n)
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn wedge(&mut self) -> PResult<Expr> {
        let mut lhs = self.unary()?;
        while self.eat(&Tok::Wedge) {
            let rhs = self.unary()?;
            lhs = binary(BinaryOp::Wedge, lhs, rhs);
        }
        Ok(lhs)
    }

    fn unary(&mut self) -> PResult<Expr> {
        let op = match self.peek() {
            Some(Tok::Minus) => UnaryOp::Neg,
            Some(Tok::Slash) => UnaryOp::Recip,
            _ => return self.power(),
        };
        let start = self.bump().span;
        self.enter()?;
        let inner = self.unary();
        self.leave();
        let inner = inner?;
        let span = start.join(inner.span);
        Ok(Expr::new(ExprKind::Unary(op, Box::new(inner)), span))
    }

    fn power(&mut self) -> PResult<Expr> {
        let base = self.postfix()?;
        if self.eat(&Tok::Pow) {
            self.enter()?;
            let exponent = self.unary();
            self.leave();
            return Ok(binary(BinaryOp::Pow, base, exponent?));
        }
        Ok(base)
    }

    fn postfix(&mut self) -> PResult<Expr> {
        let mut expr = self.atom()?;
        loop {
            match self.peek() {
                Some(Tok::LParen) => {
                    self.pos += 1;
                    let mut args = Vec::new();
                    if !self.eat(&Tok::RParen) {
                        loop {
                            args.push(self.expr()?);
                            if self.eat(&Tok::Comma) {
                                continue;
                            }
                            self.expect(&Tok::RParen, "`)` closing the arguments")?;
                            break;
                        }
                    }
                    let span = expr.span.join(Span::point(self.prev_end()));
                    expr = Expr::new(ExprKind::Call(Box::new(expr), args), span);
                }
                Some(Tok::LBracket) => {
                    self.pos += 1;
                    let index = self.expr()?;
                    self.expect(&Tok::RBracket, "`]` closing the index")?;
                    let span = expr.span.join(Span::point(self.prev_end()));
                    expr = Expr::new(ExprKind::Index(Box::new(expr), Box::new(index)), span);
                }
                _ => return Ok(expr),
            }
        }
    }

    fn atom(&mut self) -> PResult<Expr> {
        let span = self.span_here();
        let Some(tok) = self.peek().cloned() else {
            return Err(self.error_here("expected an expression"));
        };
        let simple = |kind| Ok(Expr::new(kind, span));
        match tok {
            Tok::Int(n) => {
                self.pos += 1;
                simple(ExprKind::Int(n))
            }
            Tok::Omega => {
                self.pos += 1;
                simple(ExprKind::Omega)
            }
            Tok::Kw(Keyword::True) => {
                self.pos += 1;
                simple(ExprKind::Bool(true))
            }
            Tok::Kw(Keyword::False) => {
                self.pos += 1;
                simple(ExprKind::Bool(false))
            }
            Tok::Kw(Keyword::Up) => {
                self.pos += 1;
                if self.peek() == Some(&Tok::LParen) {
                    return Err(self
                        .error_here("`up` is a literal, not a function")
                        .with_hint("write the literal `up` without parentheses"));
                }
                simple(ExprKind::Up)
            }
            Tok::Kw(Keyword::Down) => {
                self.pos += 1;
                if self.peek() == Some(&Tok::LParen) {
                    return Err(self
                        .error_here("`down` is a literal, not a function")
                        .with_hint("write the literal `down` without parentheses"));
                }
                simple(ExprKind::Down)
            }
            Tok::Ident(name) => {
                self.pos += 1;
                simple(ExprKind::Var(name))
            }
            Tok::Upper(name) => {
                self.pos += 1;
                simple(ExprKind::Con(name))
            }
            Tok::Star => self.star(),
            Tok::LParen => self.paren(),
            Tok::LBracket => self.list(),
            Tok::LBrace => self.form(),
            Tok::Kw(Keyword::If | Keyword::Match) => Err(self
                .error_here("a conditional is not an operand")
                .with_hint("parenthesize it: `1 + (if c then a else b)`")),
            Tok::Underscore | Tok::DrawAtom => Err(self
                .error_here("a lone draw atom is not an expression")
                .with_hint(
                    "mover-result atoms come in pairs: `‿‿`, `>‿`, …; `_` alone is a pattern",
                )),
            Tok::Outcome(_) | Tok::Lt | Tok::Gt | Tok::Le | Tok::Ge | Tok::Eq | Tok::Fuzzy => {
                Err(self.error_here("expected an expression before the relation"))
            }
            Tok::Bar => Err(self
                .error_here("unexpected `|`")
                .with_hint("game forms are written `{L | R}`")),
            _ => Err(self.error_here("expected an expression")),
        }
    }

    fn star(&mut self) -> PResult<Expr> {
        let start = self.bump().span;
        let index = match self.peek() {
            Some(Tok::Int(n)) => {
                let n = *n;
                self.pos += 1;
                StarIndex::Finite(n)
            }
            Some(Tok::Omega) => {
                self.pos += 1;
                StarIndex::Omega
            }
            Some(Tok::LParen) => {
                self.pos += 1;
                let terms = self.cnf()?;
                self.expect(&Tok::RParen, "`)` closing the star index")?;
                StarIndex::Cnf(terms)
            }
            _ => StarIndex::Finite(1),
        };
        Ok(Expr::new(
            ExprKind::Star(index),
            start.join(Span::point(self.prev_end())),
        ))
    }

    fn cnf(&mut self) -> PResult<Vec<CnfTerm>> {
        let start = self.span_here();
        let mut terms = vec![self.cnf_term()?];
        while self.eat(&Tok::Plus) {
            terms.push(self.cnf_term()?);
        }
        for pair in terms.windows(2) {
            if cnf_exponent_rank(&pair[0]) <= cnf_exponent_rank(&pair[1]) {
                return Err(GrundyError::new(
                    GrundyErrorKind::CnfOrder,
                    start.join(Span::point(self.prev_end())),
                    "Cantor-normal-form exponents must strictly descend",
                )
                .with_hint("CNF indices are structural: `*(ω + 1)`, not `*(1 + ω)`"));
            }
        }
        Ok(terms)
    }

    fn cnf_term(&mut self) -> PResult<CnfTerm> {
        match self.peek() {
            Some(Tok::Int(n)) => {
                let n = *n;
                self.pos += 1;
                Ok(CnfTerm {
                    exponent: None,
                    coefficient: n,
                })
            }
            Some(Tok::Omega) => {
                self.pos += 1;
                let exponent = if self.eat(&Tok::Pow) {
                    match self.peek() {
                        Some(Tok::Int(n)) => {
                            let n = *n;
                            self.pos += 1;
                            CnfExponent::Finite(n)
                        }
                        Some(Tok::Omega) => {
                            self.pos += 1;
                            CnfExponent::Omega
                        }
                        Some(Tok::LParen) => {
                            self.pos += 1;
                            self.enter()?;
                            let inner = self.cnf();
                            self.leave();
                            let inner = inner?;
                            self.expect(&Tok::RParen, "`)` closing the CNF exponent")?;
                            CnfExponent::Cnf(inner)
                        }
                        _ => return Err(self.error_here("expected a CNF exponent")),
                    }
                } else {
                    CnfExponent::Finite(1)
                };
                let coefficient = if self.eat(&Tok::Dot) {
                    match self.peek() {
                        Some(Tok::Int(n)) => {
                            let n = *n;
                            self.pos += 1;
                            n
                        }
                        _ => return Err(self.error_here("expected a CNF coefficient")),
                    }
                } else {
                    1
                };
                Ok(CnfTerm {
                    exponent: Some(exponent),
                    coefficient,
                })
            }
            _ => Err(self.error_here("expected a CNF term (`n`, `ω`, `ω↑e`, `ω↑e⋅c`)")),
        }
    }

    fn paren(&mut self) -> PResult<Expr> {
        let open = self.bump().span;
        if self.peek() == Some(&Tok::RParen) {
            return Err(self.error_here("empty parentheses are not an expression"));
        }
        if self.at_binding() {
            let mut bindings = Vec::new();
            loop {
                if self.at_binding() {
                    bindings.push(self.binding()?);
                    self.expect(&Tok::Semi, "`;` after a binding in a sequence")?;
                    continue;
                }
                let body = self.expr()?;
                if self.peek() == Some(&Tok::Semi) {
                    return Err(self
                        .error_here("only bindings may precede `;`")
                        .with_hint("a discarded value is dead code; bind it with `name := …`"));
                }
                let close = self.expect(&Tok::RParen, "`)` closing the sequence")?;
                return Ok(Expr::new(
                    ExprKind::Block(bindings, Box::new(body)),
                    open.join(close),
                ));
            }
        }
        let first = self.expr()?;
        if self.eat(&Tok::Comma) {
            let mut items = vec![first];
            loop {
                items.push(self.expr()?);
                if self.eat(&Tok::Comma) {
                    continue;
                }
                break;
            }
            let close = self.expect(&Tok::RParen, "`)` closing the tuple")?;
            return Ok(Expr::new(ExprKind::Tuple(items), open.join(close)));
        }
        if self.peek() == Some(&Tok::Semi) {
            return Err(self
                .error_here("only bindings may precede `;`")
                .with_hint("a discarded value is dead code; bind it with `name := …`"));
        }
        let close = self.expect(&Tok::RParen, "`)`")?;
        // The parentheses widen the span, which is how literal-shaped
        // fractions recognize a parenthesized operand.
        Ok(Expr::new(first.kind, open.join(close)))
    }

    fn item(&mut self) -> PResult<Item> {
        if self.eat(&Tok::DotDot) {
            Ok(Item::Splice(self.expr()?))
        } else {
            Ok(Item::One(self.expr()?))
        }
    }

    fn list(&mut self) -> PResult<Expr> {
        let open = self.bump().span;
        if let Some(close) = self
            .tokens
            .get(self.pos)
            .filter(|t| t.kind == Tok::RBracket)
        {
            let close = close.span;
            self.pos += 1;
            return Ok(Expr::new(ExprKind::List(Vec::new()), open.join(close)));
        }
        let first = self.item()?;
        if let (Item::One(head), Some(Tok::Kw(Keyword::For))) = (&first, self.peek()) {
            let head = head.clone();
            let mut clauses = Vec::new();
            loop {
                match self.peek() {
                    Some(Tok::Kw(Keyword::For)) => {
                        self.pos += 1;
                        let pat = self.pattern()?;
                        self.expect(
                            &Tok::Kw(Keyword::In),
                            "`in` after the comprehension pattern",
                        )?;
                        let source = self.or_expr()?;
                        clauses.push(Clause::For(pat, source));
                    }
                    Some(Tok::Kw(Keyword::If)) => {
                        self.pos += 1;
                        let guard = self.or_expr()?;
                        clauses.push(Clause::If(guard));
                    }
                    _ => break,
                }
            }
            let close = self.expect(&Tok::RBracket, "`]` closing the comprehension")?;
            return Ok(Expr::new(
                ExprKind::Comprehension(Box::new(head), clauses),
                open.join(close),
            ));
        }
        let mut items = vec![first];
        while self.eat(&Tok::Comma) {
            items.push(self.item()?);
        }
        let close = self.expect(&Tok::RBracket, "`]` closing the list")?;
        Ok(Expr::new(ExprKind::List(items), open.join(close)))
    }

    fn form(&mut self) -> PResult<Expr> {
        let open = self.bump().span;
        let mut left = Vec::new();
        while !matches!(self.peek(), Some(Tok::Bar) | Some(Tok::RBrace) | None) {
            left.push(self.item()?);
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        if self.peek() == Some(&Tok::Fuzzy) {
            return Err(self
                .error_here("`∥` is not the brace bar")
                .with_hint("game forms are written `{L | R}`"));
        }
        if self.peek() != Some(&Tok::Bar) {
            return Err(self
                .error_here("a game form needs its bar")
                .with_hint("`[a, b]` is the list; braces are game forms `{L | R}`"));
        }
        self.pos += 1;
        let mut right = Vec::new();
        while !matches!(self.peek(), Some(Tok::RBrace) | None) {
            right.push(self.item()?);
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        let close = self.expect(&Tok::RBrace, "`}` closing the game form")?;
        Ok(Expr::new(ExprKind::Form { left, right }, open.join(close)))
    }

    // --------------------------------------------------------------- patterns

    fn pattern(&mut self) -> PResult<Pat> {
        self.enter()?;
        let result = self.pattern_inner();
        self.leave();
        result
    }

    fn pattern_inner(&mut self) -> PResult<Pat> {
        let span = self.span_here();
        let Some(tok) = self.peek().cloned() else {
            return Err(self.error_here("expected a pattern"));
        };
        match tok {
            Tok::Underscore => {
                self.pos += 1;
                Ok(Pat::new(PatKind::Wild, span))
            }
            Tok::Ident(name) => {
                self.pos += 1;
                Ok(Pat::new(PatKind::Var(name), span))
            }
            Tok::Int(n) => {
                self.pos += 1;
                let n = i128::try_from(n).map_err(|_| {
                    GrundyError::new(
                        GrundyErrorKind::Overflow,
                        span,
                        "pattern literal exceeds i128",
                    )
                })?;
                Ok(Pat::new(PatKind::Int(n), span))
            }
            Tok::Minus => {
                self.pos += 1;
                match self.peek() {
                    Some(Tok::Int(n)) => {
                        let n = i128::try_from(*n).map_err(|_| {
                            GrundyError::new(
                                GrundyErrorKind::Overflow,
                                span,
                                "pattern literal exceeds i128",
                            )
                        })?;
                        self.pos += 1;
                        Ok(Pat::new(
                            PatKind::Int(-n),
                            span.join(Span::point(self.prev_end())),
                        ))
                    }
                    _ => Err(self.error_here("expected an integer after `-` in a pattern")),
                }
            }
            Tok::Kw(Keyword::True) => {
                self.pos += 1;
                Ok(Pat::new(PatKind::Bool(true), span))
            }
            Tok::Kw(Keyword::False) => {
                self.pos += 1;
                Ok(Pat::new(PatKind::Bool(false), span))
            }
            Tok::Upper(name) => {
                self.pos += 1;
                let mut args = Vec::new();
                if self.eat(&Tok::LParen) {
                    loop {
                        args.push(self.pattern()?);
                        if self.eat(&Tok::Comma) {
                            continue;
                        }
                        self.expect(&Tok::RParen, "`)` closing the constructor pattern")?;
                        break;
                    }
                }
                Ok(Pat::new(
                    PatKind::Con(name, args),
                    span.join(Span::point(self.prev_end())),
                ))
            }
            Tok::LParen => {
                self.pos += 1;
                let first = self.pattern()?;
                let first = if self.eat(&Tok::Colon) {
                    let ty = self.ty()?;
                    let span = first.span.join(ty.span);
                    Pat::new(PatKind::Annot(Box::new(first), ty), span)
                } else {
                    first
                };
                if self.eat(&Tok::Comma) {
                    let mut items = vec![first];
                    loop {
                        items.push(self.pattern()?);
                        if self.eat(&Tok::Comma) {
                            continue;
                        }
                        break;
                    }
                    self.expect(&Tok::RParen, "`)` closing the tuple pattern")?;
                    return Ok(Pat::new(
                        PatKind::Tuple(items),
                        span.join(Span::point(self.prev_end())),
                    ));
                }
                self.expect(&Tok::RParen, "`)` closing the pattern")?;
                Ok(first)
            }
            Tok::LBracket => {
                self.pos += 1;
                let mut items = Vec::new();
                let mut rest = None;
                if !self.eat(&Tok::RBracket) {
                    loop {
                        if self.eat(&Tok::DotDot) {
                            rest = Some(Box::new(self.pattern()?));
                            break;
                        }
                        items.push(self.pattern()?);
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                    }
                    self.expect(&Tok::RBracket, "`]` closing the list pattern")?;
                }
                Ok(Pat::new(
                    PatKind::List(items, rest),
                    span.join(Span::point(self.prev_end())),
                ))
            }
            _ => Err(self.error_here("expected a pattern")),
        }
    }

    // ------------------------------------------------------------------ types

    fn ty(&mut self) -> PResult<TypeExpr> {
        self.enter()?;
        let result = self.ty_inner();
        self.leave();
        result
    }

    fn ty_inner(&mut self) -> PResult<TypeExpr> {
        let start = self.span_here();
        let (args, tuple_like) = if self.peek() == Some(&Tok::LParen) {
            self.pos += 1;
            let mut args = vec![self.ty()?];
            while self.eat(&Tok::Comma) {
                args.push(self.ty()?);
            }
            self.expect(&Tok::RParen, "`)` in the type")?;
            (args, true)
        } else {
            (vec![self.ty_atom()?], false)
        };
        if self.eat(&Tok::Arrow) {
            let ret = self.ty()?;
            let span = start.join(ret.span);
            return Ok(TypeExpr::new(TypeKind::Fun(args, Box::new(ret)), span));
        }
        let span = start.join(Span::point(self.prev_end()));
        if tuple_like && args.len() > 1 {
            return Ok(TypeExpr::new(TypeKind::Tuple(args), span));
        }
        let mut only = args.into_iter().next().expect("one type");
        if tuple_like {
            only.span = span;
        }
        Ok(only)
    }

    fn ty_atom(&mut self) -> PResult<TypeExpr> {
        let span = self.span_here();
        match self.peek().cloned() {
            Some(Tok::Ident(name)) => {
                self.pos += 1;
                Ok(TypeExpr::new(TypeKind::Var(name), span))
            }
            Some(Tok::Upper(name)) => {
                self.pos += 1;
                match self.peek() {
                    Some(Tok::LBracket) => {
                        self.pos += 1;
                        match self.peek() {
                            Some(Tok::Ident(var)) if var == "t" => self.pos += 1,
                            _ => {
                                return Err(self
                                    .error_here("polynomial rings are written `S[t]`")
                                    .with_hint("the indeterminate is named `t`"))
                            }
                        }
                        self.expect(&Tok::RBracket, "`]` closing the polynomial ring")?;
                        Ok(TypeExpr::new(
                            TypeKind::PolyRing(name),
                            span.join(Span::point(self.prev_end())),
                        ))
                    }
                    Some(Tok::LParen) => {
                        if is_prime_field_name(&name)
                            && matches!(self.peek_at(1), Some(Tok::Ident(var)) if var == "t")
                            && self.peek_at(2) == Some(&Tok::RParen)
                        {
                            self.pos += 3;
                            return Ok(TypeExpr::new(
                                TypeKind::RatField(name),
                                span.join(Span::point(self.prev_end())),
                            ));
                        }
                        self.pos += 1;
                        let mut args = vec![self.ty()?];
                        while self.eat(&Tok::Comma) {
                            args.push(self.ty()?);
                        }
                        self.expect(&Tok::RParen, "`)` closing the type arguments")?;
                        Ok(TypeExpr::new(
                            TypeKind::Named(name, args),
                            span.join(Span::point(self.prev_end())),
                        ))
                    }
                    _ => Ok(TypeExpr::new(TypeKind::Named(name, Vec::new()), span)),
                }
            }
            _ => Err(self.error_here("expected a type")),
        }
    }
}

/// The prime fields whose rational-function fields `S(t)` are spelled specially.
pub fn is_prime_field_name(name: &str) -> bool {
    matches!(name, "F2" | "F3" | "F5" | "F7")
}

fn binary(op: BinaryOp, lhs: Expr, rhs: Expr) -> Expr {
    let span = lhs.span.join(rhs.span);
    Expr::new(ExprKind::Binary(op, Box::new(lhs), Box::new(rhs)), span)
}

fn fraction(num: i128, den: i128) -> Option<ExprKind> {
    let (num, den) = if den < 0 { (-num, -den) } else { (num, den) };
    Some(ExprKind::Frac(num, u128::try_from(den).ok()?))
}

fn relop_of(tok: &Tok) -> Option<RelOp> {
    Some(match tok {
        Tok::Eq => RelOp::Eq,
        Tok::Lt => RelOp::Lt,
        Tok::Gt => RelOp::Gt,
        Tok::Le => RelOp::Le,
        Tok::Ge => RelOp::Ge,
        Tok::Fuzzy => RelOp::Fuzzy,
        Tok::Equiv => RelOp::Equiv,
        Tok::Outcome(cell) => RelOp::Outcome(*cell),
        _ => return None,
    })
}

fn is_relop(tok: &Tok) -> bool {
    relop_of(tok).is_some()
}

/// A sort key for CNF exponent comparison: finite terms rank below every ω-term.
fn cnf_exponent_rank(term: &CnfTerm) -> (u8, CnfRank) {
    match &term.exponent {
        None => (0, CnfRank::Finite(0)),
        Some(exponent) => (1, cnf_rank(exponent)),
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum CnfRank {
    Finite(u128),
    Transfinite(Vec<(CnfTermRank, u128)>),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct CnfTermRank(u8, Box<CnfRank>);

fn cnf_rank(exponent: &CnfExponent) -> CnfRank {
    match exponent {
        CnfExponent::Finite(n) => CnfRank::Finite(*n),
        CnfExponent::Omega => {
            CnfRank::Transfinite(vec![(CnfTermRank(1, Box::new(CnfRank::Finite(1))), 1)])
        }
        CnfExponent::Cnf(terms) => {
            if let [CnfTerm {
                exponent: None,
                coefficient,
            }] = terms.as_slice()
            {
                return CnfRank::Finite(*coefficient);
            }
            CnfRank::Transfinite(
                terms
                    .iter()
                    .map(|term| match &term.exponent {
                        None => (
                            CnfTermRank(0, Box::new(CnfRank::Finite(0))),
                            term.coefficient,
                        ),
                        Some(exponent) => (
                            CnfTermRank(1, Box::new(cnf_rank(exponent))),
                            term.coefficient,
                        ),
                    })
                    .collect(),
            )
        }
    }
}
