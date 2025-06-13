///|
let already_imported : Array[String] = []

///|
fn process_command(ctx : Context, cmd : Command) -> Context raise {
  match cmd {
    Import(fname) => process_file(ctx, fname)
    Eval(_, t) => {
      let ty = t.derive_type(ctx)
      let t_prime = t.eval(ctx)
      println("\{t_prime.to_string(ctx)}\n  : \{ty.to_string(ctx)}")
      ctx
    }
    Bind(info, x, bind) => {
      let bind_checked = bind.derive_type(ctx, info)
      let bind_prime = bind_checked.eval(ctx)
      println("\{x} \{bind_prime.to_string(ctx)}")
      ctx.add_binding(x, bind_prime)
    }
  }
}

///|
fn process_file(ctx : Context, fname : String) -> Context raise {
  if already_imported.contains(fname) {
    ctx
  } else {
    already_imported.push(fname)
    let cmds = parse_file(ctx, fname)
    loop (ctx, cmds) {
      (ctx, Nil) => break ctx
      (ctx, Cons(c, rest)) => continue (process_command(ctx, c), rest)
    }
  }
}

///|
fn parse_file(ctx : Context, fname : String) -> @immut/list.T[Command] raise {
  try {
    let code = @fs.read_file_to_string(fname)
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
    let result = toplevel(tokens)
    if has_lex_error.val {
      error_info("")
    } else {
      result(ctx).0
    }
  } catch {
    @fs.IOError(_) => error_info("cannot locate file \"\{fname}\"")
    ErrorWithInfo(_) as e => raise e
    UnexpectedToken(t, (start, end), _) =>
      if has_lex_error.val {
        error_info("")
      } else {
        error_info("unexpected token \"\{t}\"", info=FI(start, end))
      }
    _ => panic()
  }
}

///|
fn main {
  let argv = @sys.get_cli_args()[2:]
  try {
    if argv.length() != 1 {
      error_info("you must specify exactly one input file")
    } else {
      let fname = argv[0]
      ignore(process_file(Context::empty(), fname))
    }
  } catch {
    ErrorWithInfo((msg, info)) =>
      if not(msg.is_empty()) {
        println("Error:\{info} \{msg}")
      }
    _ => panic()
  }
}
