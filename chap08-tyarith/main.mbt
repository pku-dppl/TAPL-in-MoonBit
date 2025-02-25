///|
let already_imported : Array[String] = []

///|
fn process_command!(cmd : Command) -> Unit {
  match cmd {
    Import(fname) => process_file!(fname)
    Eval(_, t) => {
      let ty = t.derive_type!()
      let t_prime = t.eval()
      println("\{t_prime}\n  : \{ty}")
    }
  }
}

///|
fn process_file!(fname : String) -> Unit {
  if already_imported.contains(fname) {
    ()
  } else {
    already_imported.push(fname)
    let cmds = parse_file!(fname)
    loop cmds {
      Nil => break
      Cons(c, rest) => {
        process_command!(c)
        continue rest
      }
    }
  }
}

///|
fn parse_file!(fname : String) -> @immut/list.T[Command] {
  try {
    let code = @fs.read_file_to_string!(fname)
    let lexer = new_lexer(code)
    reset_lex(fname)
    let tokens = []
    while true {
      let elem = lexer.next_token()
      tokens.push(elem)
      match elem.0 {
        EOF => break
        _ => continue
      }
    }
    let result = toplevel!(tokens)
    if has_lex_error.val {
      error_info!("")
    } else {
      result
    }
  } catch {
    @fs.IOError(_) => error_info!("cannot locate file \"\{fname}\"")
    ErrorWithInfo(_) as e => raise e
    UnexpectedToken(t, (start, end), _) =>
      if has_lex_error.val {
        error_info!("")
      } else {
        error_info!("unexpected token \"\{t}\"", info=FI(start, end))
      }
    _ => panic()
  }
}

///|
fn main {
  let argv = @sys.get_cli_args()[2:]
  try {
    if argv.length() != 1 {
      error_info!("you must specify exactly one input file")
    } else {
      let fname = argv[0]
      process_file!(fname)
    }
  } catch {
    ErrorWithInfo((msg, info)) =>
      if not(msg.is_empty()) {
        println("Error:\{info} \{msg}")
      }
    _ => panic()
  }
}
