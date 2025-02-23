///|
enum Kind {
  Star
  Arr(Kind, Kind)
} derive(Eq)

///|
enum Type {
  Bool
  Nat
  Arr(Type, Type)
  Var(Int, Int)
  Id(String)
  Unit
  Record(@immut/list.T[(String, Type)])
  Variant(@immut/list.T[(String, Type)])
  String
  Double
  All(String, Type, Type)
  Some(String, Type, Type)
  Top
  Abs(String, Kind, Type)
  App(Type, Type)
}

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
  Unit(Info)
  Ascribe(Info, Term, Type)
  Record(Info, @immut/list.T[(String, Term)])
  Proj(Info, Term, String)
  Tag(Info, String, Term, Type)
  Case(Info, Term, @immut/list.T[(String, (String, Term))])
  String(Info, String)
  Double(Info, Double)
  Timesdouble(Info, Term, Term)
  Fix(Info, Term)
  TAbs(Info, String, Type, Term)
  TApp(Info, Term, Type)
  Pack(Info, Type, Term, Type)
  Unpack(Info, String, String, Term, Term)
}

///|
enum Binding {
  Name
  TmAbb(Term, Type?)
  Var(Type)
  TyAbb(Type, Kind?)
  TyVar(Type)
}

///|
enum Command {
  Import(String)
  Eval(Info, Term)
  Bind(Info, String, Binding)
  SomeBind(Info, String, String, Term)
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
fn Context::name_to_index!(self : Context, x : String, info : Info) -> Int {
  loop (0, self._) {
    (_, Nil) => error_info!("identifier \"\{x}\" is unbound", info~)
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
    TyAbb(_) => panic()
    TyVar(_) => panic()
  }
}

///|
fn Context::get_kind!(self : Context, x : Int, info : Info) -> Kind {
  match self.get_binding(x) {
    Name => panic()
    TmAbb(_) => panic()
    Var(_) => panic()
    TyAbb(_, Some(kd)) => kd
    TyAbb(_, None) => panic()
    TyVar(ty) => ty.derive_kind!(self, info)
  }
}

///|
fn Kind::to_string(self : Kind) -> String {
  let logger = StringBuilder::new()
  self.output(true, logger)
  logger.to_string()
}

///|
fn Kind::output(self : Kind, outer : Bool, logger : &Logger) -> Unit {
  match self {
    Arr(kd1, kd2) => {
      kd1.output_atom(outer, logger)
      if outer {
        logger.write_string(" ")
      }
      logger.write_string("=>")
      if outer {
        logger.write_string(" ")
      }
      kd2.output(outer, logger)
    }
    _ => self.output_atom(outer, logger)
  }
}

///|
fn Kind::output_atom(self : Kind, outer : Bool, logger : &Logger) -> Unit {
  match self {
    Star => logger.write_string("*")
    _ => {
      logger.write_string("(")
      self.output(outer, logger)
      logger.write_string(")")
    }
  }
}

///|
fn Type::map(self : Type, onvar : (Int, Int, Int) -> Type, c : Int) -> Type {
  match self {
    Bool => Bool
    Nat => Nat
    Arr(ty1, ty2) => Arr(ty1.map(onvar, c), ty2.map(onvar, c))
    Var(x, n) => onvar(c, x, n)
    Id(b) => Id(b)
    Unit => Unit
    Record(ltys) => Record(ltys.map(fn(lty) { (lty.0, lty.1.map(onvar, c)) }))
    Variant(ltys) => Variant(ltys.map(fn(lty) { (lty.0, lty.1.map(onvar, c)) }))
    String => String
    Double => Double
    All(x, ty1, ty2) => All(x, ty1.map(onvar, c), ty2.map(onvar, c + 1))
    Some(x, ty1, ty2) => Some(x, ty1.map(onvar, c), ty2.map(onvar, c + 1))
    Top => Top
    Abs(x, kd1, ty2) => Abs(x, kd1, ty2.map(onvar, c + 1))
    App(ty1, ty2) => App(ty1.map(onvar, c), ty2.map(onvar, c))
  }
}

///|
fn Type::shift_above(self : Type, d : Int, c : Int) -> Type {
  self.map(
    fn(c, x, n) { if x >= c { Var(x + d, n + d) } else { Var(x, n + d) } },
    c,
  )
}

///|
fn Type::shift(self : Type, d : Int) -> Type {
  self.shift_above(d, 0)
}

///|
fn Type::subst(self : Type, j : Int, s : Type) -> Type {
  self.map(fn(c, x, n) { if x == j + c { s.shift(c) } else { Var(x, n) } }, 0)
}

///|
fn Type::subst_top(self : Type, s : Type) -> Type {
  self.subst(0, s.shift(1)).shift(-1)
}

///|
fn Type::to_string(self : Type, ctx : Context) -> String {
  let logger = StringBuilder::new()
  self.output(ctx, true, logger)
  logger.to_string()
}

///|
fn Type::output(
  self : Type,
  ctx : Context,
  outer : Bool,
  logger : &Logger
) -> Unit {
  match self {
    All(x, ty1, ty2) => {
      let (ctx1, x1) = ctx.pick_fresh_name(x)
      logger.write_string("All \{x1}")
      match ty1 {
        Top => ()
        _ => {
          logger.write_string("<:")
          ty1.output(ctx, false, logger)
        }
      }
      logger.write_string(". ")
      ty2.output(ctx1, outer, logger)
    }
    Abs(x, kd1, ty2) => {
      let (ctx1, x1) = ctx.pick_fresh_name(x)
      logger.write_string("lambda \{x1}")
      if kd1 != Star {
        logger.write_string("::")
        kd1.output(false, logger)
      }
      logger.write_string(". ")
      ty2.output(ctx1, outer, logger)
    }
    _ => self.output_arr(ctx, outer, logger)
  }
}

///|
fn Type::output_arr(
  self : Type,
  ctx : Context,
  outer : Bool,
  logger : &Logger
) -> Unit {
  match self {
    Arr(ty1, ty2) => {
      ty1.output_app(ctx, outer, logger)
      if outer {
        logger.write_string(" ")
      }
      logger.write_string("->")
      if outer {
        logger.write_string(" ")
      }
      ty2.output_arr(ctx, outer, logger)
    }
    _ => self.output_app(ctx, outer, logger)
  }
}

///|
fn Type::output_app(
  self : Type,
  ctx : Context,
  outer : Bool,
  logger : &Logger
) -> Unit {
  match self {
    App(ty1, ty2) => {
      ty1.output_app(ctx, outer, logger)
      logger.write_string(" ")
      ty2.output_atom(ctx, outer, logger)
    }
    _ => self.output_atom(ctx, outer, logger)
  }
}

///|
fn Type::output_atom(
  self : Type,
  ctx : Context,
  outer : Bool,
  logger : &Logger
) -> Unit {
  match self {
    Bool => logger.write_string("Bool")
    Nat => logger.write_string("Nat")
    Var(x, _) => logger.write_string(ctx.index_to_name(x))
    Id(b) => logger.write_string(b)
    Unit => logger.write_string("Unit")
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
          ty.output(ctx, false, logger)
          continue (rest, i + 1)
        }
      }
      logger.write_string("}")
    }
    Variant(ltys) => {
      logger.write_string("<")
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
          ty.output(ctx, false, logger)
          continue (rest, i + 1)
        }
      }
      logger.write_string(">")
    }
    String => logger.write_string("String")
    Double => logger.write_string("Double")
    Some(x, ty1, ty2) => {
      let (ctx1, x1) = ctx.pick_fresh_name(x)
      logger.write_string("{Some \{x1}")
      match ty1 {
        Top => ()
        _ => {
          logger.write_string("<:")
          ty1.output(ctx, false, logger)
        }
      }
      logger.write_string(", ")
      ty2.output(ctx1, false, logger)
      logger.write_string("}")
    }
    Top => logger.write_string("Top")
    _ => {
      logger.write_string("(")
      self.output(ctx, outer, logger)
      logger.write_string(")")
    }
  }
}

///|
fn Term::map(
  self : Term,
  onvar : (Info, Int, Int, Int) -> Term,
  ontype : (Int, Type) -> Type,
  c : Int
) -> Term {
  match self {
    True(info) => True(info)
    False(info) => False(info)
    If(info, t1, t2, t3) =>
      If(
        info,
        t1.map(onvar, ontype, c),
        t2.map(onvar, ontype, c),
        t3.map(onvar, ontype, c),
      )
    Zero(info) => Zero(info)
    Succ(info, t1) => Succ(info, t1.map(onvar, ontype, c))
    Pred(info, t1) => Pred(info, t1.map(onvar, ontype, c))
    IsZero(info, t1) => IsZero(info, t1.map(onvar, ontype, c))
    Var(info, x, n) => onvar(info, c, x, n)
    Abs(info, x, ty1, t2) =>
      Abs(info, x, ontype(c, ty1), t2.map(onvar, ontype, c + 1))
    App(info, t1, t2) =>
      App(info, t1.map(onvar, ontype, c), t2.map(onvar, ontype, c))
    Unit(info) => Unit(info)
    Ascribe(info, t1, ty1) =>
      Ascribe(info, t1.map(onvar, ontype, c), ontype(c, ty1))
    Record(info, lts) =>
      Record(info, lts.map(fn(lt) { (lt.0, lt.1.map(onvar, ontype, c)) }))
    Proj(info, t1, l) => Proj(info, t1.map(onvar, ontype, c), l)
    Tag(info, l, t1, ty) =>
      Tag(info, l, t1.map(onvar, ontype, c), ontype(c, ty))
    Case(info, t1, cases) =>
      Case(
        info,
        t1.map(onvar, ontype, c),
        cases.map(fn(case) {
          (case.0, (case.1.0, case.1.1.map(onvar, ontype, c + 1)))
        }),
      )
    String(info, s) => String(info, s)
    Double(info, d) => Double(info, d)
    Timesdouble(info, t1, t2) =>
      Timesdouble(info, t1.map(onvar, ontype, c), t2.map(onvar, ontype, c))
    Fix(info, t1) => Fix(info, t1.map(onvar, ontype, c))
    TAbs(info, x, ty1, t2) =>
      TAbs(info, x, ontype(c, ty1), t2.map(onvar, ontype, c + 1))
    TApp(info, t1, ty2) => TApp(info, t1.map(onvar, ontype, c), ontype(c, ty2))
    Pack(info, ty1, t2, ty3) =>
      Pack(info, ontype(c, ty1), t2.map(onvar, ontype, c), ontype(c, ty3))
    Unpack(info, x1, x2, t1, t2) =>
      Unpack(
        info,
        x1,
        x2,
        t1.map(onvar, ontype, c),
        t2.map(onvar, ontype, c + 2),
      )
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
    fn(c, ty) { ty.shift_above(d, c) },
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
    fn(_, ty) { ty },
    0,
  )
}

///|
fn Term::subst_top(self : Term, s : Term) -> Term {
  self.subst(0, s.shift(1)).shift(-1)
}

///|
fn Term::subst_ty(self : Term, j : Int, s : Type) -> Term {
  self.map(
    fn(info, _, x, n) { Var(info, x, n) },
    fn(c, ty) { ty.subst(j + c, s) },
    0,
  )
}

///|
fn Term::subst_ty_top(self : Term, s : Type) -> Term {
  self.subst_ty(0, s.shift(1)).shift(-1)
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
      ty1.output(ctx, false, logger)
      logger.write_string(". ")
      t2.output(ctx1, logger)
    }
    Case(_, t1, cases) => {
      logger.write_string("case ")
      t1.output(ctx, logger)
      logger.write_string(" of ")
      loop (cases, 1) {
        (Nil, _) => break
        (Cons((l, (x, t)), rest), i) => {
          if i > 1 {
            logger.write_string(" | ")
          }
          let (ctx1, x1) = ctx.pick_fresh_name(x)
          logger.write_string("<\{l}=\{x1}>==>")
          t.output_app(ctx1, logger)
          continue (rest, i + 1)
        }
      }
    }
    TAbs(_, x, ty1, t2) => {
      let (ctx1, x1) = ctx.pick_fresh_name(x)
      logger.write_string("lambda \{x1}")
      match ty1 {
        Top => ()
        _ => {
          logger.write_string("<:")
          ty1.output(ctx, false, logger)
        }
      }
      logger.write_string(". ")
      t2.output(ctx1, logger)
    }
    Unpack(_, x1, x2, t1, t2) => {
      let (ctx1, x1_prime) = ctx.pick_fresh_name(x1)
      let (ctx2, x2_prime) = ctx1.pick_fresh_name(x2)
      logger.write_string("let {\{x1_prime},\{x2_prime}} = ")
      t1.output(ctx, logger)
      logger.write_string(" in ")
      t2.output(ctx2, logger)
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
    Timesdouble(_, t1, t2) => {
      logger.write_string("timesdouble ")
      t1.output_path(ctx, logger)
      logger.write_string(" ")
      t2.output_path(ctx, logger)
    }
    Fix(_, t1) => {
      logger.write_string("fix ")
      t1.output_path(ctx, logger)
    }
    TApp(_, t1, ty2) => {
      t1.output_app(ctx, logger)
      logger.write_string(" [")
      ty2.output(ctx, false, logger)
      logger.write_string("]")
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
    _ => self.output_ascribe(ctx, logger)
  }
}

///|
fn Term::output_ascribe(self : Term, ctx : Context, logger : &Logger) -> Unit {
  match self {
    Ascribe(_, t1, ty1) => {
      t1.output_atom(ctx, logger)
      logger.write_string(" as ")
      ty1.output(ctx, false, logger)
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
    Unit(_) => logger.write_string("unit")
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
    Tag(_, l, t1, ty) => {
      logger.write_string("<\{l}=")
      t1.output(ctx, logger)
      logger.write_string("> as ")
      ty.output(ctx, false, logger)
    }
    String(_, s) => logger.write_string("\"\{s}\"")
    Double(_, d) => logger.write_string("\{d}")
    Pack(_, ty1, t2, ty3) => {
      logger.write_string("{*")
      ty1.output(ctx, false, logger)
      logger.write_string(", ")
      t2.output(ctx, logger)
      logger.write_string("} as ")
      ty3.output(ctx, false, logger)
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
    TmAbb(t, ty_opt) => TmAbb(t.shift(d), ty_opt.map(fn(ty) { ty.shift(d) }))
    Var(ty) => Var(ty.shift(d))
    TyAbb(ty, kd_opt) => TyAbb(ty.shift(d), kd_opt)
    TyVar(ty) => TyVar(ty.shift(d))
  }
}

///|
fn Binding::to_string(self : Binding, ctx : Context) -> String {
  match self {
    Name => "/"
    TmAbb(t, Some(ty)) => "= \{t.to_string(ctx)}\n  : \{ty.to_string(ctx)}"
    TmAbb(_, None) => panic()
    Var(ty) => ": \{ty.to_string(ctx)}"
    TyAbb(ty, Some(kd)) => "= \{ty.to_string(ctx)}\n  :: \{kd.to_string()}"
    TyAbb(_, None) => panic()
    TyVar(ty) => "<: \{ty.to_string(ctx)}"
  }
}
