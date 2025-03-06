.PHONY: test

test:
	moon run chap03-arith chap03-arith/test.f > chap03-arith/test.f.out
	moon run chap05-untyped chap05-untyped/test.f > chap05-untyped/test.f.out
	moon run chap08-tyarith chap08-tyarith/test.f > chap08-tyarith/test.f.out
	moon run chap09-simplebool chap09-simplebool/test.f > chap09-simplebool/test.f.out
	moon run chap11-fullsimple chap11-fullsimple/test.f > chap11-fullsimple/test.f.out
	moon run chap13-simpleref chap13-simpleref/test.f > chap13-simpleref/test.f.out
	moon run chap14-simpleerror chap14-simpleerror/test.f > chap14-simpleerror/test.f.out
	moon run chap15-simplesub chap15-simplesub/test.f > chap15-simplesub/test.f.out
	moon run chap20-fullequirec chap20-fullequirec/test.f > chap20-fullequirec/test.f.out
	moon run chap20-fullisorec chap20-fullisorec/test.f > chap20-fullisorec/test.f.out
	moon run chap22-simplerecon chap22-simplerecon/test.f > chap22-simplerecon/test.f.out
	moon run chap23-fullpoly chap23-fullpoly/test.f > chap23-fullpoly/test.f.out
	moon run chap26-fullfsub chap26-fullfsub/test.f > chap26-fullfsub/test.f.out
	moon run chap29-fullomega chap29-fullomega/test.f > chap29-fullomega/test.f.out
	moon run chap31-fullfomsub chap31-fullfomsub/test.f > chap31-fullfomsub/test.f.out
