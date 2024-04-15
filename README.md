# Wormholes formalization -- Second step

## Task list

- [x] Prove the preservation of the functional transition
- [x] Prove the progress of the functional transition
- [ ] Prove the preservation of the temporal transition
- [ ] Prove the progress of the temporal transition
- [ ] Prove the safety property for the functional transition
- [ ] Prove the safety property for the temporal transition

## Dependencies

The formalization depends on the library `MMaps` findable in the coq community [git](https://github.com/coq-community/coq-mmaps) and the library `DeBrLevel` findable on [git](https://github.com/JordanIschard/DeBrLevel).

## Introduction

This project is a formalization of a subset of Wormholes, i.e, a language with lambda-calculus terms, pairs, recursion, arrow terms (`arr`, `first` and `(>>>)`) and the `rsf` term. It is a simplification of the main formalization findable on the [main branch](https://github.com/JordanIschard/Mechanized-Wormholes/tree/main) of the repository.

## Authors

- Jordan Ischard