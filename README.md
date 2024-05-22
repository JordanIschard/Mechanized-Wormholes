# Wormholes formalization -- Second step

## Dependencies

The formalization depends on the library `MMaps` available on the coq community [git](https://github.com/coq-community/coq-mmaps) and the library `DeBrLevel`, version `1.2.0`, available at [https://github.com/JordanIschard/DeBrLevel](https://github.com/JordanIschard/DeBrLevel).

## Documentation

It is possible to generate documentation via the command `make coqdoc`. However, it requires to build the project before (`dune build`). The documentation generation uses the `coqdocJs` script available on the coq community [git](https://github.com/coq-community/coqdocjs).

## Introduction

This project is a formalization of a subset of Wormholes, i.e, a language with lambda-calculus terms, pairs, recursion, arrow terms (`arr`, `first` and `(>>>)`) and the `rsf` term. It is a simplification of the main formalization available at the [main branch](https://github.com/JordanIschard/Mechanized-Wormholes/tree/main) of the repository.

## Statistics

Via `coqwc $(find theories/ -name "*.v")`, we have the following statistics:

| spec | proof | comments | file |
|:---:|:---:|:---:|:---|
|   62|   30|    4| [VContext](theories/Environments_Contexts/VContext.v) |
|  152|  492|    6| [RFlows](theories/Environments_Contexts/RFlows.v) |
|   82|   44|    6| [REnvironment](theories/Environments_Contexts/REnvironment.v) |
|   68|   31|    3| [RContext](theories/Environments_Contexts/RContext.v) |
|  108|  249|    7| [WfConEnv](theories/Environments_Contexts/WfConEnv.v) |
|   17|    4|    3| [Var](theories/Syntax/Var.v) |
|   88|   23|    8| [Term](theories/Syntax/Term.v) |
|   84|  101|    0| [RFlow](theories/Syntax/RFlow.v) |
|   52|   37|    6| [Typ](theories/Syntax/Typ.v) |
|   22|    5|    2| [Resource](theories/Syntax/Resource.v) |
|   21|    0|    1| [Resources](theories/Syntax/Resources.v) |
|   47|   20|    9| [Cell](theories/Syntax/Cell.v) |
|   82|  102|   28| [Typing](theories/Typing.v) |
|   35|   43|    5| [Substitution](theories/Substitution.v) |
|   52|  306|   35| [Evaluation](theories/Evaluation.v) |
|   45|  246|  111| [Functional](theories/Functional.v) |
|   40|   44|   18| [Temporal](theories/Temporal.v) |
| 1057| 1777|  252| **total** |

## Authors

- Jordan Ischard