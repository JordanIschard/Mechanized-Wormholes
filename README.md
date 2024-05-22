# Wormholes formalization -- First step

## Dependencies

The formalization depends on the library `MMaps` available on the coq community [git](https://github.com/coq-community/coq-mmaps).

## Introduction

This project is a formalization of a lambda-calculus with pairs, recursion and arrow terms (`arr`, `first` and `(>>>)`). It is a simplification of the main formalization available at the [main branch](https://github.com/JordanIschard/Mechanized-Wormholes) of the repository.

## Statistics

Via `coqwc $(find theories/ -name "*.v")`, we have the following statistics:

| spec | proof | comments | file |
|:---:|:---:|:---:|:---|
|  63  |   30  |        4 | [Context](theories/Environments_Contexts/Context.v) |
|  17  |    4  |        3 | [Var](theories/Syntax/Var.v) |
| 104  |   57  |        8 | [Term](theories/Syntax/Term.v) |
|  53  |   39  |        7 | [Typ](theories/Syntax/Typ.v) |
|  65  |   72  |       22 | [Typing](theories/Typing.v) |
|  34  |   42  |       13 | [Substitution](theories/Substitution.v) |
|  49  |  296  |       50 | [Evaluation](theories/Evaluation.v) |
|  25  |  112  |       44 | [Functional](theories/Functional.v) |
|  34  |   59  |       13 | [Temporal](theories/Temporal.v) |
| 444  |  711  |      164 | **total** |

## Authors

- Jordan Ischard
