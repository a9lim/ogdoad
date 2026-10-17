use grundy::{needs_continuation, GrundySession, GRUNDY_VERSION};
use std::io::{self, Write};

const HELP: &str = concat!(
    "commands:  :type e   :env   :fuel [n]   :graph [n]   :help   :quit\n",
    "values:\n",
    "  3 + 4          *3 ⋅ *5          {0 | 1} + *1        ω↑(1/2)\n",
    "  (t↑2 + 1 : F5[t])               (x + 1 : F9)        [k⋅k for k in 0..5]\n",
    "rulesets:\n",
    "  g := impartial(n ↦ [[a, n - a] for a in 1..n if 2⋅a < n])   // Grundy's game\n",
    "  [sg(g, n) for n in 0..20]       value(g, 7)          winning(g, [7, 5], Left)\n",
    "  kayles := octal([7, 7])         periodic(kayles, 71, 12)\n",
    "loopy games:\n",
    "  over =: {0 | over}              over = over          over ‿‿ over\n",
    "  certify(over)                   outcome(graph(g, 9))\n",
    "misère:\n",
    "  sampled(misere_quotient(g, [1, 2, 3, 4], 3, 3))      separate(g, [3], [6], sums([1, 2], 2))\n",
    "algebra:\n",
    "  alg := clifford([*1, *1]); [e0, e1] := basis(alg); (e0 + e1) ⋅ (e0 + e1)",
);

fn main() {
    let mut session = GrundySession::new();
    println!("grundy {GRUNDY_VERSION}");
    let stdin = io::stdin();
    let mut pending = String::new();
    loop {
        print!("{}", if pending.is_empty() { "og> " } else { ">> " });
        io::stdout().flush().expect("flush prompt");
        let mut line = String::new();
        if stdin.read_line(&mut line).expect("read line") == 0 {
            break;
        }
        let line = line.trim();
        if pending.is_empty() {
            if line.is_empty() {
                continue;
            }
            if let Some(command) = line.strip_prefix(':') {
                let (name, arg) = command.split_once(' ').unwrap_or((command, ""));
                let arg = arg.trim();
                match name {
                    "quit" | "q" => break,
                    "help" => println!("{HELP}"),
                    "env" => {
                        for (name, scheme) in session.env() {
                            println!("{name} : {scheme}");
                        }
                    }
                    "type" => match session.type_of(arg) {
                        Ok(ty) => println!("{ty}"),
                        Err(err) => eprintln!("{err}"),
                    },
                    "fuel" if arg.is_empty() => println!("{}", session.fuel()),
                    "fuel" => match arg.parse() {
                        Ok(n) => session.set_fuel(n),
                        Err(_) => eprintln!("E_Parse: the fuel budget is a natural number"),
                    },
                    "graph" if arg.is_empty() => println!("{}", session.graph_budget()),
                    "graph" => match arg.parse() {
                        Ok(n) => session.set_graph_budget(n),
                        Err(_) => eprintln!("E_Parse: the graph budget is a natural number"),
                    },
                    other => eprintln!("unknown command `:{other}`; try `:help`"),
                }
                continue;
            }
        } else {
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
                if out.canonical != pending {
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
    fn help_fits_one_screen_and_names_every_command() {
        assert!(HELP.lines().count() <= 20);
        for command in [":type", ":env", ":fuel", ":graph", ":help", ":quit"] {
            assert!(HELP.contains(command), "{command}");
        }
    }
}
