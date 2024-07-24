# efci - Effective Curry Interpreter

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
* `:fcy` prints the `main` expression generated from the input.

## Run tests

```
stack test effective-curry-interpreter
```

## Known issues
* Ambiguous types are not defaulted. For example, `1 + 2` needs to be annotated as `1 + 2 :: Int`.
* Not all external functions are implemented. 