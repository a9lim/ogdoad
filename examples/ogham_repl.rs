use ogdoad::ogham::OghamSession;
use std::io::{self, Write};

fn main() {
    let mut session = OghamSession::new("integer 0").expect("default ogham world");
    println!("ogham — {}", session.world_summary());
    let stdin = io::stdin();
    loop {
        print!("og> ");
        io::stdout().flush().expect("flush prompt");
        let mut line = String::new();
        if stdin.read_line(&mut line).expect("read line") == 0 {
            break;
        }
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        match line {
            ":quit" | ":q" => break,
            ":help" => {
                println!(":world <decl>  change world");
                println!(":env           show bindings");
                println!(":quit          exit");
                continue;
            }
            ":env" => {
                println!("{}", session.world_summary());
                for binding in session.env_summary() {
                    println!("{binding}");
                }
                continue;
            }
            _ => {}
        }
        if let Some(rest) = line.strip_prefix(":world ") {
            match session.set_world(rest) {
                Ok(()) => println!("{}", session.world_summary()),
                Err(err) => eprintln!("{err}"),
            }
            continue;
        }
        match session.eval_line(line) {
            Ok(out) => {
                if out.canonical != line {
                    println!("{}", out.canonical);
                }
                if let Some(value) = out.value {
                    println!("{value}");
                }
            }
            Err(err) => eprintln!("{err}"),
        }
    }
}
