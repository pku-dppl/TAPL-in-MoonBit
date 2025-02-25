///|
let already_imported : Array[String] = []

///|
fn process_command!(ctx : Context, cmd : Command) -> Context {
  match cmd {
    Import(fname) => process_file!(ctx, fname)
    Eval(_, t) => {
      let ty = t.derive_type!(ctx)
      let t_prime = t.eval(ctx)
      println("\{t_prime.to_string(ctx)}\n  : \{ty.to_string(ctx)}")
      ctx
    }
    Bind(info, x, bind) => {
      let bind_checked = bind.derive_type!(ctx, info)
      let bind_prime = bind_checked.eval(ctx)
      println("\{x} \{bind_prime.to_string(ctx)}")
      ctx.add_binding(x, bind_prime)
    }
    SomeBind(info, x1, x2, t) => {
      let ty = t.derive_type!(ctx)
      match ty.simplify(ctx) {
        Some(_, kd1, ty2) => {
          let t_prime = t.eval(ctx)
          let b = match t_prime {
            Pack(_, _, t2, _) => TmAbb(t2.shift(1), Some(ty2))
            _ => Var(ty2)
          }
          println("\{x1} \{TyVar(kd1).to_string(ctx)}")
          let ctx1 = ctx.add_binding(x1, TyVar(kd1))
          println("\{x2} \{b.to_string(ctx1)}")
          let ctx2 = ctx1.add_binding(x2, b)
          ctx2
        }
        _ => error_info!("existential type expected", info~)
      }
    }
  }
}

///|
fn process_file!(ctx : Context, fname : String) -> Context {
  if already_imported.contains(fname) {
    ctx
  } else {
    already_imported.push(fname)
    let cmds = parse_file!(ctx, fname)
    loop (ctx, cmds) {
      (ctx, Nil) => break ctx
      (ctx, Cons(c, rest)) => continue (process_command!(ctx, c), rest)
    }
  }
}

///|
fn parse_file!(ctx : Context, fname : String) -> @immut/list.T[Command] {
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
      result!(ctx).0
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
      ignore(process_file!(Context::empty(), fname))
    }
  } catch {
    ErrorWithInfo((msg, info)) =>
      if not(msg.is_empty()) {
        println("Error:\{info} \{msg}")
      }
    _ => panic()
  }
}
