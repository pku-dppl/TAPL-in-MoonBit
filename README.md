# TAPL

[MoonBit](https://www.moonbitlang.com/) Port of implementations for Pierce's [Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/).

The port here slightly diverges from the [original implementations](https://www.cis.upenn.edu/~bcpierce/tapl/resources.html#checkers) to better suit the needs of the [Design Principles of Programming Languages](https://pku-dppl.github.io/2025/english.html) course at Peking University.
- [chap03-arith](chap03-arith) for Chapter 3: Untyped Arithmetic Expressions. An untyped calculus with Booleans and natural numbers.
- [chap05-untyped](chap05-untyped) for Chapter 5: The Untyped Lambda-Calculus. An untyped lambda calculus with Booleans and natural numbers.
- [chap08-tyarith](chap08-tyarith) for Chapter 8: Typed Arithmetic Expressions. A typed calculus with Booleans and natural numbers.
- [chap09-simplebool](chap09-simplebool) for Chapter 9: Simply Typed Lambda-Calculus. A simply-typed lambda calculus with Booleans and natural numbers.
- [chap11-fullsimple](chap11-fullsimple) for Chapter 11: Simple Extensions. A simply-typed lambda calculus with Booleans, natural numbers, units, records, variants, strings, and decimal numbers.
- [chap13-simpleref](chap13-simpleref) for Chapter 13: References. A simply-typed lambda calculus with Booleans, natural numbers, and references.
- [chap14-simpleerror](chap14-simpleerror) for Chapter 14: Exceptions. A simply-typed lambda calculus with Booleans, natural numbers, and errors. Note that the implementation uses subtyping and the bottom type to allow polymorphic typing of errors.
- [chap15-simplesub](chap15-simplesub) for Chapter 15: Subtyping. A simply-typed lambda calculus with subtyping, as well as Booleans, natural numbers, and records.
- [chap20-fullequirec](chap20-fullequirec) for Chapter 20: Recursive Types. A simply-typed lambda calculus with equi-recursive types, as well as Booleans, natural numbers, units, records, variants, strings, and decimal numbers.
- [chap20-fullisorec](chap20-fullisorec) for Chapter 20: Recursive Types. A simply-typed lambda calculus with iso-recursive types, as well as Booleans, natural numbers, units, records, variants, strings, and decimal numbers.
- [chap22-simplerecon](chap22-simplerecon) for Chapter 22: Type Reconstruction. A simply-typed lambda calculus with type inference, as well as Booleans and natural numbers.
- [chap23-fullpoly](chap23-fullpoly) for Chapter 23: Universal Types. A System-F calculus with Booleans, natural numbers, units, records, variants, strings, and decimal numbers.
- [chap26-fullfsub](chap26-fullfsub) for Chapter 26: Bounded Quantification. A System-F calculus with subtyping, as well as Booleans, natural numbers, units, records, variants, strings, and decimal numbers.
- [chap29-fullomega](chap29-fullomega) for Chapter 29: Type Operators and Kinding. A System-F calculus with kinding, as well as Booleans, natural numbers, units, records, variants, strings, and decimal numbers.
- [chap31-fullfomsub](chap31-fullfomsub) for Chapter 31: Higher-Order Subtyping. A System-F calculus with kinding and subtyping, as well as Booleans, natural numbers, units, records, variants, strings, and decimal numbers.

## Prerequisites

Follow the instruction [here](https://docs.moonbitlang.com/en/latest/tutorial/tour.html#installation) to install MoonBit's toolchain.
The recommended setup is to install MoonBit's VS Code extension and then perform the 'Install moonbit toolchain' action in VS Code.

## Usage

Go to the root directory and build all the checkers:
```
moon build
```

Run a particular checker on an input file:
```
moon run chap11-fullsimple chap11-fullsimple/test.f
```
