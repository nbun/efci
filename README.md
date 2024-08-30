# efci - Effective Curry Interpreter

This repository accompanies the Haskell'24 paper [Making a Curry Interpreter using Effects and Handlers](https://doi.org/10.1145/3677999.3678279).

The most recent code might differ from the version shown in the paper. You can check out

* [4db98c2](https://github.com/nbun/efci/tree/4db98c2cd0f80b27fc2d4cac5f15109417e1b7d5) for the original interpreter
* [1421632](https://github.com/nbun/efci/tree/1421632a166990b8369bdd7d12a46c6b8b9663c3) for an extended version featuring unification
* [90dfb99](https://github.com/nbun/efci/tree/90dfb99d4d1b4b9cfa7fed71503f6486237b46ac) for 'fusion all the way'

## Installation

```
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
* `:fcy` toggles printing of the `main` expression generated from the input.

## Run tests

```
stack test effective-curry-interpreter
```

## Run benchmarks

```
stack bench effective-curry-interpreter
```

## Known issues
* Ambiguous types are not defaulted. For example, `1 + 2` needs to be annotated as `1 + 2 :: Int`.
* Not all external functions are implemented. 
