# efci - Effective Curry Interpreter

This repository contains the implementation of `efci`, a Curry interpreter
based on effects and handlers.

## Installation (tested with stack 3.7.1 and cabal 3.16.1.0)

```
git clone https://github.com/nbun/efci
cd efci
git submodules pull --init
stack install
```

## Usage
Run
```
efci [filename]
```
from the directory where `filename.curry` is located. If `efci` is called without an argument, only the `Prelude` module is loaded.
If you have `rlwrap` installed, use `rlwrap efci [filename]` to get an input history for the interpreter.

## Options

* Without an option, the input is interpreted as a Curry expression within the loaded file.
* `:q` exits interpreter.
* `:o` rotates between the available interpretation modes
* `:time` toggles printing time elapsed during interpretation
* `:fcy` toggles printing of the `main` expression generated from the input.

## Run tests

```
stack test effective-curry-interpreter
```

## Run benchmarks

```
stack bench effective-curry-interpreter
```

## Generate documentation

```
stack haddock --open effective-curry-interpreter
```

## Repository structure

* [src](src): implementation of the interpreter(s)
    * [Data.Union](src/Data/Union.hs): open unions used for implementing signatures
    * [Effect](src/Effect/): implementations of (Curry-specific) effects
        * [FlatCurry](src/Effect/FlatCurry/): Curry-specific effects
            * [Constructor](src/Effect/FlatCurry/Constructor.hs): terms and pattern matching effect
            * [Declarations](src/Effect/FlatCurry/Declarations.hs): function declaration effect
            * [Function](src/Effect/FlatCurry/Function.hs): Partial application effect
            * [IO](src/Effect/FlatCurry/IO.hs): input/output effect
            * [Let](src/Effect/FlatCurry/Let.hs): local bindings effect
        * [General](src/Effect/General/): commonly known effects
            * [Error](src/Effect/General/Error.hs): (unexpected) error effect
            * [Memoization](src/Effect/General/Memoization.hs): lazy evaluation effect
            * [ND](src/Effect/General/ND.hs): non-determinism effect
            * [State](src/Effect/General/State.hs): state effect
        * [Transformation](src/Transformation/): transformation functions
            * [AE2Result](src/Transformation/AE2Result.hs): transformation from effects to results
            * [FCY2AE](src/Transformation/FCY2AE.hs): transformation from FlatCurry to effects
        * [App](src/App): REPL logic and front end integration
        * [Debug](src/Debug): flags for toggling debug output
        * [Forwarding](src/Forwarding): forwarding functions and carrier classes
        * [Free](src/Free): effect representations (tree-based, continuation-based, smart views)
        * [InterpFL](src/InterpFL): implementation of [A Monadic Semantics for Core Curry](https://doi.org/10.1016/S1571-0661(04)80691-1)
        * [Pipeline](src/Pipeline): pipelines for different effect representations
        * [Signature](src/Signature): adapters, type operators, and injection functions for signatures
        * [Type](src/Type): auxiliary functions and type definitions
* [tests/Main.hs](tests/Main.hs): test suite runner
* [examples](examples): example programs for the test suite
* [benchmarks](benchmarks): benchmark programs
    * [Main.hs](benchmarks/Main.hs): benchmark runner

## Known issues
* Ambiguous types are not defaulted. For example, `1 + 2` needs to be annotated as `1 + 2 :: Int`.
* Not all external functions are implemented. 

## Historic releases

Haskell'24 paper [Making a Curry Interpreter using Effects and Handlers](https://doi.org/10.1145/3677999.3678279):

* [4db98c2](https://github.com/nbun/efci/tree/4db98c2cd0f80b27fc2d4cac5f15109417e1b7d5) for the original interpreter
* [1421632](https://github.com/nbun/efci/tree/1421632a166990b8369bdd7d12a46c6b8b9663c3) for an extended version featuring unification
* [90dfb99](https://github.com/nbun/efci/tree/90dfb99d4d1b4b9cfa7fed71503f6486237b46ac) for 'fusion all the way'