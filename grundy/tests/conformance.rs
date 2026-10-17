//! The conformance corpus: `docs/conformance.txt`, hand-checked vectors.
//!
//! Format, one block per statement:
//!
//! ```text
//! @reset            fresh session (also: @fuel n, @graph n)
//! > input           a statement, exactly as typed (sugar allowed)
//! >> continuation   a continuation line
//! ~ canonical       optional: the canonical echo
//! = display         the displayed value, or:
//! ! E_Kind: text    an error kind and a message substring
//! ? hint text       optional after `!`: a hint substring
//! ```
//!
//! A block with neither `=` nor `!` asserts success with no displayed value.

use grundy::{GrundyError, GrundySession};

#[derive(Default)]
struct Block {
    line: usize,
    input: String,
    canonical: Option<String>,
    value: Option<String>,
    error: Option<(String, String)>,
    hint: Option<String>,
}

fn run(session: &mut GrundySession, block: &Block) {
    let result = session.eval_line(&block.input);
    let where_ = format!("line {}: `{}`", block.line, block.input);
    match (&block.error, result) {
        (
            Some((kind, text)),
            Err(GrundyError {
                kind: actual,
                message,
                hint,
                ..
            }),
        ) => {
            assert_eq!(actual.code(), kind, "{where_}: error kind ({message})");
            assert!(
                message.contains(text.as_str()),
                "{where_}: message `{message}` lacks `{text}`"
            );
            if let Some(want) = &block.hint {
                let hint = hint.unwrap_or_default();
                assert!(
                    hint.contains(want.as_str()),
                    "{where_}: hint `{hint}` lacks `{want}`"
                );
            }
        }
        (Some((kind, _)), Ok(out)) => panic!("{where_}: expected {kind}, got {:?}", out.value),
        (None, Err(err)) => panic!("{where_}: unexpected error {err}"),
        (None, Ok(out)) => {
            if let Some(canonical) = &block.canonical {
                assert_eq!(&out.canonical, canonical, "{where_}: canonical echo");
            }
            assert_eq!(out.value, block.value, "{where_}: value");
        }
    }
}

#[test]
fn conformance_corpus() {
    let corpus = include_str!("../docs/conformance.txt");
    let mut session = GrundySession::new();
    let mut block: Option<Block> = None;
    let mut count = 0;
    let flush = |session: &mut GrundySession, block: &mut Option<Block>, count: &mut usize| {
        if let Some(b) = block.take() {
            run(session, &b);
            *count += 1;
        }
    };
    for (index, raw) in corpus.lines().enumerate() {
        let line_no = index + 1;
        let line = raw.trim_end();
        if line.is_empty() || line.starts_with("//") {
            flush(&mut session, &mut block, &mut count);
            continue;
        }
        if let Some(directive) = line.strip_prefix('@') {
            flush(&mut session, &mut block, &mut count);
            let (name, arg) = directive.split_once(' ').unwrap_or((directive, ""));
            match name {
                "reset" => session = GrundySession::new(),
                "fuel" => session.set_fuel(arg.trim().parse().expect("fuel")),
                "graph" => session.set_graph_budget(arg.trim().parse().expect("graph")),
                other => panic!("line {line_no}: unknown directive @{other}"),
            }
            continue;
        }
        if let Some(input) = line.strip_prefix("> ") {
            flush(&mut session, &mut block, &mut count);
            block = Some(Block {
                line: line_no,
                input: input.to_string(),
                ..Block::default()
            });
            continue;
        }
        let current = block
            .as_mut()
            .unwrap_or_else(|| panic!("line {line_no}: content outside a block"));
        if let Some(rest) = line.strip_prefix(">> ") {
            current.input.push('\n');
            current.input.push_str(rest);
        } else if let Some(rest) = line.strip_prefix("~ ") {
            current.canonical = Some(rest.to_string());
        } else if let Some(rest) = line.strip_prefix("= ") {
            current.value = Some(rest.to_string());
        } else if let Some(rest) = line.strip_prefix("! ") {
            let (kind, text) = rest.split_once(':').unwrap_or((rest, ""));
            current.error = Some((kind.trim().to_string(), text.trim().to_string()));
        } else if let Some(rest) = line.strip_prefix("? ") {
            current.hint = Some(rest.to_string());
        } else {
            panic!("line {line_no}: unrecognized corpus line `{line}`");
        }
    }
    flush(&mut session, &mut block, &mut count);
    assert!(count >= 300, "the corpus has {count} vectors");
}
