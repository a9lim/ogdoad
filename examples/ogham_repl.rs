use ogdoad::ogham::{needs_continuation, OghamSession, OGHAM_VERSION, WORLD_MENU};
use std::io::{self, Write};

const TUTOR_TASKS: &str = concat!(
    "commands:\n",
    "  :world <decl>  :fuel [n]  :graph [n]  :env  :help  :quit\n",
    "try (:world, then expression):\n",
    "  :world nimber 0    | *3 ⋅ *5\n",
    "  :world game        | {1, 2 | 0} > 0        up ∥ *1\n",
    "  :world integer 0   | fact =: n ↦ (n = 0 ? 1 : n⋅fact@(n-1)); fact@5\n",
    "  :world game        | ones =: {1 | ones}; ones ‿‿ ones\n",
    "  :world surreal 0   | ω↑(1/2) + 1/2",
);

fn help_screen() -> String {
    format!("{WORLD_MENU}\n{TUTOR_TASKS}")
}

fn main() {
    let mut session = OghamSession::new("integer 0").expect("default ogham world");
    println!("ogham {OGHAM_VERSION} — {}", session.world_summary());
    let stdin = io::stdin();
    let mut pending = String::new();
    loop {
        if pending.is_empty() {
            print!("og> ");
        } else {
            print!(">> ");
        }
        io::stdout().flush().expect("flush prompt");
        let mut line = String::new();
        if stdin.read_line(&mut line).expect("read line") == 0 {
            break;
        }
        let line = line.trim();
        if pending.is_empty() && line.is_empty() {
            continue;
        }
        if pending.is_empty() {
            match line {
                ":quit" | ":q" => break,
                ":help" => {
                    println!("{}", help_screen());
                    continue;
                }
                ":env" => {
                    println!("{}", session.world_summary());
                    for binding in session.env_summary() {
                        println!("{binding}");
                    }
                    continue;
                }
                ":fuel" => {
                    println!("{}", session.fuel_budget());
                    continue;
                }
                ":graph" => {
                    println!("{}", session.graph_budget());
                    continue;
                }
                _ => {}
            }
        }
        if pending.is_empty() {
            if let Some(rest) = line.strip_prefix(":fuel ") {
                match rest.trim().parse::<u128>() {
                    Ok(budget) => {
                        session.set_fuel_budget(budget);
                        println!("{budget}");
                    }
                    Err(_) => eprintln!("E_Parse: fuel budget must be a u128"),
                }
                continue;
            }
        }
        if pending.is_empty() {
            if let Some(rest) = line.strip_prefix(":graph ") {
                match rest.trim().parse::<u128>() {
                    Ok(budget) => {
                        session.set_graph_budget(budget);
                        println!("{budget}");
                    }
                    Err(_) => eprintln!("E_Parse: graph budget must be a u128"),
                }
                continue;
            }
        }
        if pending.is_empty() {
            if let Some(rest) = line.strip_prefix(":world ") {
                match session.set_world(rest) {
                    Ok(()) => println!("{}", session.world_summary()),
                    Err(err) => eprintln!("{err}"),
                }
                continue;
            }
        }
        if !pending.is_empty() {
            pending.push('\n');
        }
        pending.push_str(line);
        match needs_continuation(&pending) {
            Ok(true) => continue,
            Ok(false) => {}
            Err(err) => {
                eprintln!("{err}");
                pending.clear();
                continue;
            }
        }
        match session.eval_line(&pending) {
            Ok(out) => {
                if !out.canonical.is_empty() && out.canonical != pending {
                    println!("{}", out.canonical);
                }
                if let Some(value) = out.value {
                    println!("{value}");
                }
            }
            Err(err) => eprintln!("{err}"),
        }
        pending.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tutor_is_one_screen_and_covers_commands_and_seed_families() {
        let help = help_screen();
        assert!(help.lines().count() <= 20);
        for command in [":world", ":fuel", ":graph", ":env", ":help", ":quit"] {
            assert!(help.contains(command));
        }
        for seed in ["*3 ⋅ *5", "up ∥ *1", "fact =:", "ones ‿‿ ones", "ω↑(1/2)"] {
            assert!(help.contains(seed));
        }
    }
}
