/* Examples for testing */

true;
if false then true else false;

42;
succ (pred 0);
iszero (pred (succ (succ 0)));

x/;
x;

lambda x. x;
(lambda x. x) (lambda x. x x);

id = lambda x. x;
id (id (lambda z. id z));

tru = lambda t. lambda f. t;
fls = lambda t. lambda f. f;

test = lambda l. lambda m. lambda n. l m n;
test tru 33 44;

and = lambda b. lambda c. b c fls;
and tru tru;
and tru fls;

pair = lambda f. lambda s. lambda b. b f s;
fst = lambda p. p tru;
snd = lambda p. p fls;
fst (pair 33 44);

c0 = lambda s. lambda z. z;
c1 = lambda s. lambda z. s z;
c2 = lambda s. lambda z. s (s z);
c3 = lambda s. lambda z. s (s (s z));

scc = lambda n. lambda s. lambda z. s (n s z);
scc c1;

plus = lambda m. lambda n. lambda s. lambda z. m s (n s z);

times = lambda m. lambda n. m (plus n) c0;
times c2 c2;

iszro = lambda m. m (lambda _. fls) tru;
iszro c1;
iszro (times c0 c2);

zz = pair c0 c0;
ss = lambda p. pair (snd p) (plus c1 (snd p));
prd = lambda m. fst (m ss zz);

realbool = lambda b. b true false;
realbool tru;

churchbool = lambda b. if b then tru else fls;

realnat = lambda m. m (lambda x. succ x) 0;
realnat c3;
realnat (times c2 c2);

/* omega = (lambda x. x x) (lambda x. x x); */

fix = lambda f. (lambda x. f (lambda y. x x y)) (lambda x. f (lambda y. x x y));

g = lambda fct. lambda n. if realbool(iszro(n)) then c1 else (times n (fct (prd n)));
factorial = fix g;
realnat (factorial c3);
realnat (factorial (scc (scc c3)));
