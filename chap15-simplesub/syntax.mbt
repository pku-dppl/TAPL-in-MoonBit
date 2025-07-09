///|
enum Type {
  Bool
  Nat
  Arr(Type, Type)
  Record(@immut/list.T[(String, Type)])
  Top
} derive(Eq)

///|
enum Term {
  True(Info)
  False(Info)
  If(Info, Term, Term, Term)
  Zero(Info)
  Succ(Info, Term)
  Pred(Info, Term)
  IsZero(Info, Term)
  Var(Info, Int, Int)
  Abs(Info, String, Type, Term)
  App(Info, Term, Term)
  Record(Info, @immut/list.T[(String, Term)])
  Proj(Info, Term, String)
}

///|
enum Binding {
  Name
  TmAbb(Term, Type?)
  Var(Type)
}

///|
enum Command {
  Import(String)
  Eval(Info, Term)
  Bind(Info, String, Binding)
}

///|
type Context @immut/list.T[(String, Binding)]

///|
fn Context::empty() -> Context {
  Nil
}

///|
fn Context::length(self : Context) -> Int {
  self._.length()
}

///|
fn Context::add_binding(self : Context, x : String, bind : Binding) -> Context {
  Cons((x, bind), self._)
}

///|
fn Context::add_name(self : Context, x : String) -> Context {
  self.add_binding(x, Name)
}

///|
fn Context::name_to_index(self : Context, x : String, info : Info) -> Int raise {
  loop (0, self._) {
    (_, Nil) => error_info("identifier \"\{x}\" is unbound", info~)
    (i, Cons((y, _), rest)) => if y == x { i } else { continue (i + 1, rest) }
  }
}

///|
fn Context::index_to_name(self : Context, x : Int) -> String {
  self._.unsafe_nth(x).0
}

///|
fn Context::is_name_bound(self : Context, x : String) -> Bool {
  self._.any(fn(b) { x == b.0 })
}

///|
fn Context::pick_fresh_name(self : Context, x : String) -> (Context, String) {
  loop x {
    x =>
      if self.is_name_bound(x) {
        continue x + "'"
      } else {
        break (self.add_name(x), x)
      }
  }
}

///|
fn Context::get_binding(self : Context, x : Int) -> Binding {
  self._.unsafe_nth(x).1.shift(x + 1)
}

///|
fn Context::get_type(self : Context, x : Int) -> Type {
  match self.get_binding(x) {
    Name => panic()
    TmAbb(_, Some(ty)) => ty
    TmAbb(_, None) => panic()
    Var(ty) => ty
  }
}

///|
fn Type::to_string(self : Type) -> String {
  let logger = StringBuilder::new()
  self.output(true, logger)
  logger.to_string()
}

///|
fn Type::output(self : Type, outer : Bool, logger : &Logger) -> Unit {
  match self {
    Arr(ty1, ty2) => {
      ty1.output_atom(outer, logger)
      if outer {
        logger.write_string(" ")
      }
      logger.write_string("->")
      if outer {
        logger.write_string(" ")
      }
      ty2.output(outer, logger)
    }
    _ => self.output_atom(outer, logger)
  }
}

///|
fn Type::output_atom(self : Type, outer : Bool, logger : &Logger) -> Unit {
  match self {
    Bool => logger.write_string("Bool")
    Nat => logger.write_string("Nat")
    Record(ltys) => {
      logger.write_string("{")
      loop (ltys, 1) {
        (Nil, _) => break
        (Cons((l, ty), rest), i) => {
          if i > 1 {
            logger.write_string(",")
            if outer {
              logger.write_string(" ")
            }
          }
          if l != i.to_string() {
            logger.write_string("\{l}:")
          }
          ty.output(false, logger)
          continue (rest, i + 1)
        }
      }
      logger.write_string("}")
    }
    Top => logger.write_string("Top")
    _ => {
      logger.write_string("(")
      self.output(outer, logger)
      logger.write_string(")")
    }
  }
}

///|
fn Term::map(
  self : Term,
  onvar : (Info, Int, Int, Int) -> Term,
  c : Int
) -> Term {
  match self {
    True(info) => True(info)
    False(info) => False(info)
    If(info, t1, t2, t3) =>
      If(info, t1.map(onvar, c), t2.map(onvar, c), t3.map(onvar, c))
    Zero(info) => Zero(info)
    Succ(info, t1) => Succ(info, t1.map(onvar, c))
    Pred(info, t1) => Pred(info, t1.map(onvar, c))
    IsZero(info, t1) => IsZero(info, t1.map(onvar, c))
    Var(info, x, n) => onvar(info, c, x, n)
    Abs(info, x, ty1, t2) => Abs(info, x, ty1, t2.map(onvar, c + 1))
    App(info, t1, t2) => App(info, t1.map(onvar, c), t2.map(onvar, c))
    Record(info, lts) =>
      Record(info, lts.map(fn(lt) { (lt.0, lt.1.map(onvar, c)) }))
    Proj(info, t1, l) => Proj(info, t1.map(onvar, c), l)
  }
}

///|
fn Term::shift_above(self : Term, d : Int, c : Int) -> Term {
  self.map(
    fn(info, c, x, n) {
      if x >= c {
        Var(info, x + d, n + d)
      } else {
        Var(info, x, n + d)
      }
    },
    c,
  )
}

///|
fn Term::shift(self : Term, d : Int) -> Term {
  self.shift_above(d, 0)
}

///|
fn Term::subst(self : Term, j : Int, s : Term) -> Term {
  self.map(
    fn(info, c, x, n) { if x == j + c { s.shift(c) } else { Var(info, x, n) } },
    0,
  )
}

///|
fn Term::subst_top(self : Term, s : Term) -> Term {
  self.subst(0, s.shift(1)).shift(-1)
}

///|
fn Term::to_string(self : Term, ctx : Context) -> String {
  let logger = StringBuilder::new()
  self.output(ctx, logger)
  logger.to_string()
}

///|
fn Term::output(self : Term, ctx : Context, logger : &Logger) -> Unit {
  match self {
    If(_, t1, t2, t3) => {
      logger.write_string("if ")
      t1.output(ctx, logger)
      logger.write_string(" then ")
      t2.output(ctx, logger)
      logger.write_string(" else")
      t3.output(ctx, logger)
    }
    Abs(_, x, ty1, t2) => {
      let (ctx1, x1) = ctx.pick_fresh_name(x)
      logger.write_string("lambda \{x1}:")
      ty1.output(false, logger)
      logger.write_string(". ")
      t2.output(ctx1, logger)
    }
    _ => self.output_app(ctx, logger)
  }
}

///|
fn Term::output_app(self : Term, ctx : Context, logger : &Logger) -> Unit {
  match self {
    Pred(_, t1) => {
      logger.write_string("pred ")
      t1.output_path(ctx, logger)
    }
    IsZero(_, t1) => {
      logger.write_string("iszero ")
      t1.output_path(ctx, logger)
    }
    App(_, t1, t2) => {
      t1.output_app(ctx, logger)
      logger.write_string(" ")
      t2.output_path(ctx, logger)
    }
    _ => self.output_path(ctx, logger)
  }
}

///|
fn Term::output_path(self : Term, ctx : Context, logger : &Logger) -> Unit {
  match self {
    Proj(_, t1, l) => {
      t1.output_path(ctx, logger)
      logger.write_string(".\{l}")
    }
    _ => self.output_atom(ctx, logger)
  }
}

///|
fn Term::output_atom(self : Term, ctx : Context, logger : &Logger) -> Unit {
  match self {
    True(_) => logger.write_string("true")
    False(_) => logger.write_string("false")
    Zero(_) => logger.write_string("0")
    Succ(_, t1) =>
      loop (t1, 1) {
        (Zero(_), n) => {
          logger.write_string("\{n}")
          break
        }
        (Succ(_, s), n) => continue (s, n + 1)
        _ => {
          logger.write_string("(succ ")
          t1.output_path(ctx, logger)
          logger.write_string(")")
        }
      }
    Var(_, x, _) => logger.write_string(ctx.index_to_name(x))
    Record(_, lts) => {
      logger.write_string("{")
      loop (lts, 1) {
        (Nil, _) => break
        (Cons((l, t), rest), i) => {
          if i > 1 {
            logger.write_string(", ")
          }
          if l != i.to_string() {
            logger.write_string("\{l}=")
          }
          t.output(ctx, logger)
          continue (rest, i + 1)
        }
      }
      logger.write_string("}")
    }
    _ => {
      logger.write_string("(")
      self.output(ctx, logger)
      logger.write_string(")")
    }
  }
}

///|
fn Binding::shift(self : Binding, d : Int) -> Binding {
  match self {
    Name => Name
    TmAbb(t, ty_opt) => TmAbb(t.shift(d), ty_opt)
    Var(ty) => Var(ty)
  }
}

///|
fn Binding::to_string(self : Binding, ctx : Context) -> String {
  match self {
    Name => "/"
    TmAbb(t, Some(ty)) => "= \{t.to_string(ctx)}\n  : \{ty.to_string()}"
    TmAbb(_, None) => panic()
    Var(ty) => ": \{ty.to_string()}"
  }
}
