use super::ast::OutcomeCell;
use super::error::{GrundyError, GrundyErrorKind, GrundyResult, Span};

#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq)]
pub enum TokenKind {
    Int(u128),
    Ident(String),
    Blade(usize),
    Omega,
    Star,
    Index,
    Power,
    Wedge,
    Dot,
    Slash,
    Percent,
    At,
    Question,
    Colon,
    Arrow,
    If,
    Then,
    Else,
    And,
    Or,
    Not,
    True,
    False,
    Up,
    Down,
    Dim,
    Semicolon,
    Eq,
    Less,
    Greater,
    Pipe,
    // U+2225, the canonical fuzzy relop; `!` is its lexer sugar. `Pipe` is
    // the structural braceform bar only — no relop reading (a relop-tier `|`
    // gets the expect_end hint) — and `Parallel` is refused as the bar in turn.
    Parallel,
    Assign,
    RecursiveAssign,
    Append,
    Equiv,
    Outcome(OutcomeCell),
    DrawAtom,
    Plus,
    Minus,
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Comma,
}

pub fn lex(src: &str) -> GrundyResult<Vec<Token>> {
    let (src, block_depth) = mask_comments(src);
    if block_depth != 0 {
        return Err(GrundyError::new(
            GrundyErrorKind::Parse,
            Span::point(src.len()),
            "unterminated block comment",
        ));
    }
    lex_masked(&src)
}

fn lex_masked(src: &str) -> GrundyResult<Vec<Token>> {
    let chars: Vec<(usize, char)> = src.char_indices().collect();
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < chars.len() {
        let (pos, ch) = chars[i];
        if ch.is_whitespace() {
            i += 1;
            continue;
        }
        if ch.is_ascii_digit() {
            let start = pos;
            let mut end = pos + ch.len_utf8();
            let mut value = 0u128;
            while i < chars.len() {
                let (p, c) = chars[i];
                if !c.is_ascii_digit() {
                    break;
                }
                let digit = u128::from(c as u8 - b'0');
                value = value
                    .checked_mul(10)
                    .and_then(|v| v.checked_add(digit))
                    .ok_or_else(|| {
                        GrundyError::new(
                            GrundyErrorKind::Overflow,
                            Span::new(start, p + c.len_utf8()),
                            "integer literal exceeds u128",
                        )
                    })?;
                end = p + c.len_utf8();
                i += 1;
            }
            out.push(Token {
                kind: TokenKind::Int(value),
                span: Span::new(start, end),
            });
            continue;
        }
        if ch == 'e' && i + 1 < chars.len() && chars[i + 1].1.is_ascii_digit() {
            let start = pos;
            i += 1;
            let mut end = start + 1;
            let mut value = 0usize;
            while i < chars.len() {
                let (p, c) = chars[i];
                if !c.is_ascii_digit() {
                    break;
                }
                let digit = usize::from(c as u8 - b'0');
                value = value
                    .checked_mul(10)
                    .and_then(|v| v.checked_add(digit))
                    .ok_or_else(|| {
                        GrundyError::new(
                            GrundyErrorKind::Overflow,
                            Span::new(start, p + c.len_utf8()),
                            "blade index exceeds usize",
                        )
                    })?;
                end = p + c.len_utf8();
                i += 1;
            }
            out.push(Token {
                kind: TokenKind::Blade(value),
                span: Span::new(start, end),
            });
            continue;
        }
        if ch == 'O' && i + 1 < chars.len() && chars[i + 1].1 == '(' {
            return Err(reserved(Span::new(pos, chars[i + 1].0 + 1)));
        }
        if ch.is_ascii_lowercase() {
            let start = pos;
            let mut s = String::new();
            let mut end = pos + ch.len_utf8();
            while i < chars.len() {
                let (p, c) = chars[i];
                if !(c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_') {
                    break;
                }
                s.push(c);
                end = p + c.len_utf8();
                i += 1;
            }
            let kind = if s == "w" {
                TokenKind::Omega
            } else if s == "if" {
                TokenKind::If
            } else if s == "then" {
                TokenKind::Then
            } else if s == "else" {
                TokenKind::Else
            } else if s == "and" {
                TokenKind::And
            } else if s == "or" {
                TokenKind::Or
            } else if s == "not" {
                TokenKind::Not
            } else if s == "true" {
                TokenKind::True
            } else if s == "false" {
                TokenKind::False
            } else if s == "up" {
                TokenKind::Up
            } else if s == "down" {
                TokenKind::Down
            } else if s == "dim" {
                TokenKind::Dim
            } else if s == "e" {
                return Err(GrundyError::new(
                    GrundyErrorKind::Parse,
                    Span::new(start, end),
                    "`e` needs a blade index, e.g. `e0`",
                ));
            } else {
                TokenKind::Ident(s)
            };
            out.push(Token {
                kind,
                span: Span::new(start, end),
            });
            continue;
        }
        let span = Span::new(pos, pos + ch.len_utf8());
        let kind = match ch {
            'ω' => TokenKind::Omega,
            '*' => TokenKind::Star,
            '#' => TokenKind::Index,
            '^' | '↑' => {
                if i + 1 < chars.len() && matches!(chars[i + 1].1, '^' | '↑') {
                    return Err(reserved(Span::new(
                        pos,
                        chars[i + 1].0 + chars[i + 1].1.len_utf8(),
                    )));
                }
                TokenKind::Power
            }
            '&' | '∧' => TokenKind::Wedge,
            '.' | '⋅' | '·' => TokenKind::Dot,
            '/' => TokenKind::Slash,
            '%' => TokenKind::Percent,
            '@' => TokenKind::At,
            '!' | '∥' => TokenKind::Parallel,
            '?' => TokenKind::Question,
            '=' => {
                if i + 1 < chars.len() && chars[i + 1].1 == ':' {
                    i += 1;
                    out.push(Token {
                        kind: TokenKind::RecursiveAssign,
                        span: Span::new(pos, chars[i].0 + 1),
                    });
                    i += 1;
                    continue;
                }
                if i + 2 < chars.len() && chars[i + 1].1 == '=' && chars[i + 2].1 == '=' {
                    i += 2;
                    out.push(Token {
                        kind: TokenKind::Equiv,
                        span: Span::new(pos, chars[i].0 + 1),
                    });
                    i += 1;
                    continue;
                }
                if i + 1 < chars.len() && chars[i + 1].1 == '=' {
                    i += 1;
                    out.push(Token {
                        kind: TokenKind::Eq,
                        span: Span::new(pos, chars[i].0 + 1),
                    });
                    i += 1;
                    continue;
                }
                TokenKind::Eq
            }
            '<' | '>' | '‿' | '_' => {
                if i + 1 < chars.len() {
                    if let (Some(first), Some(second)) =
                        (mover_atom(ch), mover_atom(chars[i + 1].1))
                    {
                        i += 1;
                        out.push(Token {
                            kind: TokenKind::Outcome(OutcomeCell::from_atoms(first, second)),
                            span: Span::new(pos, chars[i].0 + chars[i].1.len_utf8()),
                        });
                        i += 1;
                        continue;
                    }
                }
                match ch {
                    '<' => TokenKind::Less,
                    '>' => TokenKind::Greater,
                    '‿' | '_' => TokenKind::DrawAtom,
                    _ => unreachable!(),
                }
            }
            '|' => TokenKind::Pipe,
            ':' => {
                if i + 1 < chars.len() && chars[i + 1].1 == '=' {
                    i += 1;
                    out.push(Token {
                        kind: TokenKind::Assign,
                        span: Span::new(pos, chars[i].0 + 1),
                    });
                    i += 1;
                    continue;
                }
                TokenKind::Colon
            }
            '+' => {
                if i + 1 < chars.len() && chars[i + 1].1 == '+' {
                    i += 1;
                    out.push(Token {
                        kind: TokenKind::Append,
                        span: Span::new(pos, chars[i].0 + 1),
                    });
                    i += 1;
                    continue;
                }
                TokenKind::Plus
            }
            '⧺' => TokenKind::Append,
            '≡' => TokenKind::Equiv,
            '-' => TokenKind::Minus,
            ';' => TokenKind::Semicolon,
            '(' => TokenKind::LParen,
            ')' => TokenKind::RParen,
            '[' => TokenKind::LBracket,
            ']' => TokenKind::RBracket,
            '{' => TokenKind::LBrace,
            '}' => TokenKind::RBrace,
            ',' => TokenKind::Comma,
            '↦' | '~' => TokenKind::Arrow,
            _ => {
                return Err(GrundyError::new(
                    GrundyErrorKind::Parse,
                    span,
                    format!("unexpected character `{ch}`"),
                ));
            }
        };
        out.push(Token { kind, span });
        i += 1;
    }
    Ok(out)
}

fn mover_atom(ch: char) -> Option<char> {
    match ch {
        '<' | '>' => Some(ch),
        '‿' | '_' => Some('‿'),
        _ => None,
    }
}

pub fn needs_continuation(src: &str) -> GrundyResult<bool> {
    let (masked, block_depth) = mask_comments(src);
    if block_depth != 0 {
        return Ok(true);
    }
    let mut paren_depth = 0usize;
    let mut bracket_depth = 0usize;
    let mut brace_depth = 0usize;
    let tokens = lex_masked(&masked)?;
    for token in &tokens {
        match token.kind {
            TokenKind::LParen => paren_depth += 1,
            TokenKind::RParen => {
                let Some(depth) = paren_depth.checked_sub(1) else {
                    return Ok(false);
                };
                paren_depth = depth;
            }
            TokenKind::LBracket => bracket_depth += 1,
            TokenKind::RBracket => {
                let Some(depth) = bracket_depth.checked_sub(1) else {
                    return Ok(false);
                };
                bracket_depth = depth;
            }
            TokenKind::LBrace => brace_depth += 1,
            TokenKind::RBrace => {
                let Some(depth) = brace_depth.checked_sub(1) else {
                    return Ok(false);
                };
                brace_depth = depth;
            }
            _ => {}
        }
    }
    if paren_depth > 0 || bracket_depth > 0 || brace_depth > 0 {
        return Ok(true);
    }
    Ok(tokens
        .last()
        .is_some_and(|token| token_requires_continuation(&token.kind)))
}

fn token_requires_continuation(kind: &TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::Arrow
            | TokenKind::Assign
            | TokenKind::RecursiveAssign
            | TokenKind::Semicolon
            | TokenKind::Comma
            | TokenKind::If
            | TokenKind::Then
            | TokenKind::Else
            | TokenKind::And
            | TokenKind::Or
            | TokenKind::Not
            | TokenKind::Power
            | TokenKind::Wedge
            | TokenKind::Dot
            | TokenKind::Slash
            | TokenKind::Percent
            | TokenKind::At
            | TokenKind::Append
            | TokenKind::Plus
            | TokenKind::Minus
            | TokenKind::Eq
            | TokenKind::Less
            | TokenKind::Greater
            | TokenKind::Parallel
            | TokenKind::Equiv
            | TokenKind::Outcome(_)
            | TokenKind::Pipe
            | TokenKind::Star
            | TokenKind::Index
    )
}

pub(crate) fn strip_comments(src: &str) -> GrundyResult<String> {
    let (masked, block_depth) = mask_comments(src);
    if block_depth == 0 {
        Ok(masked)
    } else {
        Err(GrundyError::new(
            GrundyErrorKind::Parse,
            Span::point(src.len()),
            "unterminated block comment",
        ))
    }
}

fn mask_comments(src: &str) -> (String, usize) {
    let mut bytes = src.as_bytes().to_vec();
    let mut depth = 0usize;
    let mut i = 0usize;
    while i < bytes.len() {
        if depth == 0 && bytes[i..].starts_with(b"//") {
            bytes[i] = b' ';
            bytes[i + 1] = b' ';
            i += 2;
            while i < bytes.len() && bytes[i] != b'\n' {
                bytes[i] = b' ';
                i += 1;
            }
            continue;
        }
        if bytes[i..].starts_with(b"/*") {
            depth += 1;
            bytes[i] = b' ';
            bytes[i + 1] = b' ';
            i += 2;
            continue;
        }
        if depth != 0 && bytes[i..].starts_with(b"*/") {
            depth -= 1;
            bytes[i] = b' ';
            bytes[i + 1] = b' ';
            i += 2;
            continue;
        }
        if depth != 0 && bytes[i] != b'\n' {
            bytes[i] = b' ';
        }
        i += 1;
    }
    (
        String::from_utf8(bytes).expect("comment masking preserves UTF-8 as ASCII whitespace"),
        depth,
    )
}

fn reserved(span: Span) -> GrundyError {
    GrundyError::new(GrundyErrorKind::Reserved, span, "reserved syntax")
        .with_hint("reserved for future games/precision/function syntax")
}
