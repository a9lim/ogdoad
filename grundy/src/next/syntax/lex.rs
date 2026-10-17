//! Tokenization, ASCII sugar normalization, and continuation detection.

use super::super::error::{GrundyError, GrundyErrorKind, GrundyResult, Span};
use super::ast::{Mover, OutcomeCell};

/// A normalized token and its source span.
#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    /// Normalized token kind.
    pub kind: Tok,
    /// Byte range in the submitted source.
    pub span: Span,
}

/// Tokens after ASCII sugar is normalized.
#[derive(Clone, Debug, PartialEq)]
pub enum Tok {
    /// Natural-number literal.
    Int(u128),
    /// Lowercase identifier.
    Ident(String),
    /// Uppercase identifier: a type or constructor name.
    Upper(String),
    /// `ω` (sugar `w`).
    Omega,
    /// Star prefix `*`.
    Star,
    /// `↑` (sugar `^`).
    Pow,
    /// `∧` (sugar `&`).
    Wedge,
    /// `⋅` (sugar `.`, `·`).
    Dot,
    /// `/`.
    Slash,
    /// `%`.
    Percent,
    /// `↦` (sugar `~`).
    MapsTo,
    /// `→` (sugar `->`).
    Arrow,
    /// `:` type annotation.
    Colon,
    /// `:=`.
    Assign,
    /// `=:`.
    RecAssign,
    /// `;`.
    Semi,
    /// `,`.
    Comma,
    /// `|`.
    Bar,
    /// `=` (sugar `==`).
    Eq,
    /// `<`.
    Lt,
    /// `>`.
    Gt,
    /// `≤` (sugar `<=`).
    Le,
    /// `≥` (sugar `>=`).
    Ge,
    /// `∥` (sugar `!`).
    Fuzzy,
    /// `≡` (sugar `===`).
    Equiv,
    /// An outcome double.
    Outcome(OutcomeCell),
    /// `⧺` (sugar `++`).
    Concat,
    /// `+`.
    Plus,
    /// `-`.
    Minus,
    /// `..`.
    DotDot,
    /// `..=`.
    DotDotEq,
    /// `_` wildcard, or a lone draw atom outside an outcome double.
    Underscore,
    /// `‿` alone (always an error; atoms come in pairs).
    DrawAtom,
    /// `(`.
    LParen,
    /// `)`.
    RParen,
    /// `[`.
    LBracket,
    /// `]`.
    RBracket,
    /// `{`.
    LBrace,
    /// `}`.
    RBrace,
    /// A keyword.
    Kw(Keyword),
}

/// Reserved words.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Keyword {
    /// `if`
    If,
    /// `then`
    Then,
    /// `else`
    Else,
    /// `and`
    And,
    /// `or`
    Or,
    /// `not`
    Not,
    /// `true`
    True,
    /// `false`
    False,
    /// `up`
    Up,
    /// `down`
    Down,
    /// `for`
    For,
    /// `in`
    In,
    /// `match`
    Match,
    /// `data`
    Data,
}

impl Keyword {
    /// The keyword's spelling.
    pub fn text(self) -> &'static str {
        match self {
            Keyword::If => "if",
            Keyword::Then => "then",
            Keyword::Else => "else",
            Keyword::And => "and",
            Keyword::Or => "or",
            Keyword::Not => "not",
            Keyword::True => "true",
            Keyword::False => "false",
            Keyword::Up => "up",
            Keyword::Down => "down",
            Keyword::For => "for",
            Keyword::In => "in",
            Keyword::Match => "match",
            Keyword::Data => "data",
        }
    }

    fn from_text(text: &str) -> Option<Keyword> {
        Some(match text {
            "if" => Keyword::If,
            "then" => Keyword::Then,
            "else" => Keyword::Else,
            "and" => Keyword::And,
            "or" => Keyword::Or,
            "not" => Keyword::Not,
            "true" => Keyword::True,
            "false" => Keyword::False,
            "up" => Keyword::Up,
            "down" => Keyword::Down,
            "for" => Keyword::For,
            "in" => Keyword::In,
            "match" => Keyword::Match,
            "data" => Keyword::Data,
            _ => return None,
        })
    }
}

/// Every reserved word, including the omega sugar `w`.
pub fn is_reserved_word(text: &str) -> bool {
    text == "w" || Keyword::from_text(text).is_some()
}

/// Tokenize source, masking comments and normalizing ASCII sugar.
pub fn lex(src: &str) -> GrundyResult<Vec<Token>> {
    let masked = strip_comments(src)?;
    lex_masked(&masked)
}

fn lex_masked(src: &str) -> GrundyResult<Vec<Token>> {
    let chars: Vec<(usize, char)> = src.char_indices().collect();
    let end_of = |i: usize| -> usize {
        chars
            .get(i)
            .map_or(src.len(), |&(pos, ch)| pos + ch.len_utf8())
    };
    let at = |i: usize| -> Option<char> { chars.get(i).map(|&(_, ch)| ch) };
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < chars.len() {
        let (pos, ch) = chars[i];
        if ch.is_whitespace() {
            i += 1;
            continue;
        }
        if ch.is_ascii_digit() {
            let mut value = 0u128;
            let mut j = i;
            while let Some(c) = at(j).filter(char::is_ascii_digit) {
                let digit = u128::from(c as u8 - b'0');
                value = value
                    .checked_mul(10)
                    .and_then(|v| v.checked_add(digit))
                    .ok_or_else(|| {
                        GrundyError::new(
                            GrundyErrorKind::Overflow,
                            Span::new(pos, end_of(j)),
                            "integer literal exceeds u128",
                        )
                    })?;
                j += 1;
            }
            out.push(Token {
                kind: Tok::Int(value),
                span: Span::new(pos, end_of(j - 1)),
            });
            i = j;
            continue;
        }
        if ch.is_ascii_alphabetic() {
            let mut j = i;
            let mut text = String::new();
            while let Some(c) = at(j).filter(|c| c.is_ascii_alphanumeric() || *c == '_') {
                text.push(c);
                j += 1;
            }
            let span = Span::new(pos, end_of(j - 1));
            let kind = if ch.is_ascii_uppercase() {
                if text == "O" && at(j) == Some('(') {
                    return Err(reserved(Span::new(pos, end_of(j))));
                }
                Tok::Upper(text)
            } else if text == "w" {
                Tok::Omega
            } else if let Some(keyword) = Keyword::from_text(&text) {
                Tok::Kw(keyword)
            } else {
                Tok::Ident(text)
            };
            out.push(Token { kind, span });
            i = j;
            continue;
        }
        let next = at(i + 1);
        let next2 = at(i + 2);
        let (kind, width) = match ch {
            'ω' => (Tok::Omega, 1),
            '*' => (Tok::Star, 1),
            '^' | '↑' => {
                if matches!(next, Some('^' | '↑')) {
                    return Err(reserved(Span::new(pos, end_of(i + 1))));
                }
                (Tok::Pow, 1)
            }
            '&' | '∧' => (Tok::Wedge, 1),
            '.' => match (next, next2) {
                (Some('.'), Some('=')) => (Tok::DotDotEq, 3),
                (Some('.'), _) => (Tok::DotDot, 2),
                _ => (Tok::Dot, 1),
            },
            '⋅' | '·' => (Tok::Dot, 1),
            '/' => (Tok::Slash, 1),
            '%' => (Tok::Percent, 1),
            '↦' | '~' => (Tok::MapsTo, 1),
            '→' => (Tok::Arrow, 1),
            '!' | '∥' => (Tok::Fuzzy, 1),
            '≡' => (Tok::Equiv, 1),
            '≤' => (Tok::Le, 1),
            '≥' => (Tok::Ge, 1),
            '⧺' => (Tok::Concat, 1),
            ';' => (Tok::Semi, 1),
            ',' => (Tok::Comma, 1),
            '|' => (Tok::Bar, 1),
            '(' => (Tok::LParen, 1),
            ')' => (Tok::RParen, 1),
            '[' => (Tok::LBracket, 1),
            ']' => (Tok::RBracket, 1),
            '{' => (Tok::LBrace, 1),
            '}' => (Tok::RBrace, 1),
            '+' => match next {
                Some('+') => (Tok::Concat, 2),
                _ => (Tok::Plus, 1),
            },
            '-' => match next {
                Some('>') => (Tok::Arrow, 2),
                _ => (Tok::Minus, 1),
            },
            ':' => match next {
                Some('=') => (Tok::Assign, 2),
                _ => (Tok::Colon, 1),
            },
            '=' => match (next, next2) {
                (Some(':'), _) => (Tok::RecAssign, 2),
                (Some('='), Some('=')) => (Tok::Equiv, 3),
                (Some('='), _) => (Tok::Eq, 2),
                _ => (Tok::Eq, 1),
            },
            '<' | '>' | '‿' | '_' => {
                let first = Mover::from_glyph(ch).expect("mover glyph");
                if let Some(second) = next.and_then(Mover::from_glyph) {
                    // An identifier may not start with `_`, so `_x` never
                    // reaches here; `__`, `<_`, `_>` and friends are doubles.
                    (
                        Tok::Outcome(OutcomeCell {
                            left_first: first,
                            right_first: second,
                        }),
                        2,
                    )
                } else if next == Some('=') && ch == '<' {
                    (Tok::Le, 2)
                } else if next == Some('=') && ch == '>' {
                    (Tok::Ge, 2)
                } else {
                    match ch {
                        '<' => (Tok::Lt, 1),
                        '>' => (Tok::Gt, 1),
                        '_' => (Tok::Underscore, 1),
                        _ => (Tok::DrawAtom, 1),
                    }
                }
            }
            _ => {
                return Err(GrundyError::new(
                    GrundyErrorKind::Parse,
                    Span::new(pos, pos + ch.len_utf8()),
                    format!("unexpected character `{ch}`"),
                ));
            }
        };
        out.push(Token {
            kind,
            span: Span::new(pos, end_of(i + width - 1)),
        });
        i += width;
    }
    Ok(out)
}

/// Whether a source fragment needs another input line: an unbalanced
/// delimiter, an open block comment, or a final token that cannot end a
/// statement.
pub fn needs_continuation(src: &str) -> GrundyResult<bool> {
    let (masked, block_depth) = mask_comments(src);
    if block_depth != 0 {
        return Ok(true);
    }
    let tokens = lex_masked(&masked)?;
    let mut depth = 0isize;
    for token in &tokens {
        match token.kind {
            Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
            Tok::RParen | Tok::RBracket | Tok::RBrace => {
                depth -= 1;
                if depth < 0 {
                    return Ok(false);
                }
            }
            _ => {}
        }
    }
    if depth > 0 {
        return Ok(true);
    }
    Ok(tokens.last().is_some_and(|token| {
        matches!(
            token.kind,
            Tok::MapsTo
                | Tok::Arrow
                | Tok::Assign
                | Tok::RecAssign
                | Tok::Semi
                | Tok::Comma
                | Tok::Colon
                | Tok::Bar
                | Tok::Pow
                | Tok::Wedge
                | Tok::Dot
                | Tok::Slash
                | Tok::Percent
                | Tok::Concat
                | Tok::Plus
                | Tok::Minus
                | Tok::DotDot
                | Tok::DotDotEq
                | Tok::Eq
                | Tok::Lt
                | Tok::Gt
                | Tok::Le
                | Tok::Ge
                | Tok::Fuzzy
                | Tok::Equiv
                | Tok::Outcome(_)
                | Tok::Star
                | Tok::Kw(
                    Keyword::If
                        | Keyword::Then
                        | Keyword::Else
                        | Keyword::And
                        | Keyword::Or
                        | Keyword::Not
                        | Keyword::For
                        | Keyword::In
                        | Keyword::Match
                        | Keyword::Data
                )
        )
    }))
}

/// Replace comments by whitespace, preserving byte offsets and newlines.
pub fn strip_comments(src: &str) -> GrundyResult<String> {
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
        String::from_utf8(bytes).expect("comment masking writes ASCII spaces"),
        depth,
    )
}

fn reserved(span: Span) -> GrundyError {
    GrundyError::new(GrundyErrorKind::Reserved, span, "reserved syntax")
        .with_hint("`↑↑` and `O(` are reserved for future precision syntax")
}
