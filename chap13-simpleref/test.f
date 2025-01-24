/* Examples for testing */

true;
if false then true else false;

42;
succ (pred 0);
iszero (pred (succ (succ 0)));

x : Bool;
x;

lambda x:Bool. x;
(lambda x:Bool->Bool. if x false then true else false)
  (lambda x:Bool. if x then false else true);

id = lambda x:Bool. x;
id (id ((lambda z:Bool. id z) true));

tru = lambda t:Nat. lambda f:Nat. t;
fls = lambda t:Nat. lambda f:Nat. f;

test = lambda l:Nat->Nat->Nat. lambda m:Nat. lambda n:Nat. l m n;
test tru 33 44;

pair = lambda f:Nat. lambda s:Nat. lambda b:Nat->Nat->Nat. b f s;
fst = lambda p:(Nat->Nat->Nat)->Nat. p tru;
snd = lambda p:(Nat->Nat->Nat)->Nat. p fls;
fst (pair 33 44);

c0 = lambda s:Nat->Nat. lambda z:Nat. z;
c1 = lambda s:Nat->Nat. lambda z:Nat. s z;
c2 = lambda s:Nat->Nat. lambda z:Nat. s (s z);
c3 = lambda s:Nat->Nat. lambda z:Nat. s (s (s z));

scc = lambda n:(Nat->Nat)->Nat->Nat. lambda s:Nat->Nat. lambda z:Nat. s (n s z);
scc c1;

plus = lambda m:(Nat->Nat)->Nat->Nat. lambda n:(Nat->Nat)->Nat->Nat. lambda s:Nat->Nat. lambda z:Nat. m s (n s z);
plus c2 c2;

realnat = lambda m:(Nat->Nat)->Nat->Nat. m (lambda x:Nat. succ x) 0;
realnat c3;
realnat (plus c2 c2);

r = ref 5;
!r;
r := 7;
!r;

(r := succ(!r); !r);
(lambda _:Unit. !r) (r := succ(!r));

(r := succ(!r); r := succ(!r); r := succ(!r); r := succ(!r); !r);

s = r;
s := 82;
!r;

c = ref 0;
incc = lambda x:Unit. (c := succ(!c); !c);
decc = lambda x:Unit. (c := pred(!c); !c);

incc unit;
decc unit;

equal = fix (lambda eq:Nat->Nat->Bool. lambda x:Nat. lambda y:Nat.
    if iszero(x) then
      if iszero(y) then true
      else false
    else
      if iszero(y) then false
      else eq (pred x) (pred y)
  );

newarray = lambda _:Unit. ref (lambda n:Nat. 0);
lookup = lambda a:Ref(Nat->Nat). lambda n:Nat. (!a) n;
update =
  lambda a:Ref(Nat->Nat). lambda m:Nat. lambda v:Nat.
    (lambda oldf:Nat->Nat. a := (lambda n:Nat. if equal m n then v else oldf n)) (!a);

a = newarray unit;
lookup a 0;
lookup a 2;
update a 0 5;
update a 1 4;
update a 2 3;
lookup a 0;
lookup a 1;
lookup a 2;
