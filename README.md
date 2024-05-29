# Wormholes formalization

## Task list

- [x] Safety of the functional transition
- [ ] Safety of the temporal transition
- [x] Update the project with `dune`

## Dependencies

The formalization depends on the library `MMaps` available on the coq community [git](https://github.com/coq-community/coq-mmaps) and the library `DeBrLevel`, version `1.2.0`, available at [https://github.com/JordanIschard/DeBrLevel](https://github.com/JordanIschard/DeBrLevel).

## Documentation

It is possible to generate documentation via the command `make coqdoc`. However, it requires to build the project before (`dune build`). The documentation generation uses the `coqdocJs` script available on the coq community [git](https://github.com/coq-community/coqdocjs).

## The capture avoiding issue

The difficulty to formalize `Wormholes` comes from the naming of resources. Indeed, like in the lambda-calculus the naming of variable can provoke bad behavior in the case of lazy evaluation. In our case, **resources** are evaluated during the functional transition but **never replaced** and can **be moved by a substitution** during a beta-reduction. In order to avoid capture of names during an evaluation we have to cautiously deal with resources.
****
An old representation for dealing with names in lambda calculus uses **De Bruijn indexes**. But this representation is hard to read, and all functions provoke a consequent number of shifts. However, there is its little brother not very common named **De Bruijn levels** that caught our attention (thanks to _Adrien Guatto_).

## De Bruijn level

De Bruijn level is a representation that avoid the capture of variables issue for the lambda-calculus. Like the De Bruijn indices, variables are numbers that are chosen regards of a constraint. For De Bruijn indices, the number associated to the variable is "distance" between the variable and the abstraction. The distance is the number of abstraction between the abstraction and its associated variable. In De Bruijn levels, there is a concept of level or depth in the term, each time we enter an abstraction the depth increase. The best advantage of levels is the simplicity to handle free variables and the fact that all variables are associated to a unique level.

<div align="center">

| Representation | term |
|:--:|:--:|
| basic | $λz.(λx.(λy.(y~z)~x)~z)~~λx.x$ |
| De Bruijn indices | $λ.(λ.(λ.(0~2)~0)~0)~~λ.0$ |
| **De Bruijn levels** | $λ.(λ.(λ.(2~0)~1)~0)~~λ.0$ |

</div>

The De Bruijn level representation is more developed in the following figure.

![Example of the De Bruijn level representation for the lambda calculus](images/level_example_1.svg)

## Statistics

Via `coqwc $(find theories/ -name "*.v")`, we have the following statistic:

| spec | proof | comments | file |
|:---:|:---:|:---:|:---|
|   67|   32|    4| [VContext](Environments_Contexts/VContext.v) |
|   82|   67|    3| [RContext](Environments_Contexts/RContext.v) |
|  128|  272|    8| [REnvironment](Environments_Contexts/REnvironment.v) |
|  135|  243|    9| [ReadStock](Environments_Contexts/ReadStock.v) |
|   51|   58|    4| [WriteStock](Environments_Contexts/WriteStock.v) |
|   68|   91|    7| [Stock](Environments_Contexts/Stock.v) |
|   17|    4|    3| [Var](Syntax/Var.v) |
|   34|   19|    6| [Resource](Syntax/Resource.v) |
|   32|    7|    5| [Resources](Syntax/Resources.v) |
|  130|  133|   26| [Typ](Syntax/Typ.v) |
|  264|  325|   28| [Term](Syntax/Term.v) |
|   96|   77|   24| [Cell](Syntax/Cell.v) |
|  133|  220|   59| [Typing.v](Typing.v) |
|   88|    0|   74| [ET_Definition](Transition/Evaluation/ET_Definition.v) |
|   22|   44|   45| [ET_Preservation](Transition/Evaluation/ET_Preservation.v) |
|  101|  367|   15| [ET_Props](Transition/Evaluation/ET_Props.v) |
|    2|   44|    7| [ET_Progress](Transition/Evaluation/ET_Progress.v) |
|    2|   31|   13| [FT_Safety](Transition/Functional/FT_Safety.v) |
|    2|   42|   14| [FT_Definition](Transition/Functional/FT_Definition.v) |
|   58|  140|    8| [FT_Props](Transition/Functional/FT_Props.v) |
|  105|  713|  154| [FT_Preservation](Transition/Functional/FT_Preservation.v) |
|   17|  322|   20| [FT_Progress](Transition/Functional/FT_Progress.v) |
| 1634| 3251|  536| **total** |

## Authors

- Jordan Ischard

<!--
## Functional Transition

<img src="images/fT_example_1.drawio.svg" alt="MarineGEO circle logo" style="height: 600px;"/>
<img src="images/fT_example_2.drawio.svg" alt="MarineGEO circle logo" style="height: 600px;"/>
<img src="images/fT_example_3.drawio.svg" alt="MarineGEO circle logo" style="height: 600px;"/>
<img src="images/fT_example_4.drawio.svg" alt="MarineGEO circle logo" style="height: 600px;"/>
<img src="images/fT_example_5.drawio.svg" alt="MarineGEO circle logo" style="height: 600px;"/>
<img src="images/fT_example_6.drawio.svg" alt="MarineGEO circle logo" style="height: 600px;"/>

## Functional Transition rules

<img src="images/fT_arr_rule.drawio.svg" alt="MarineGEO circle logo" style="height: 600px;"/>
<img src="images/fT_first_rule.drawio.svg" alt="MarineGEO circle logo" style="height: 600px;"/>
<img src="images/fT_comp_rule.drawio.svg" alt="MarineGEO circle logo" style="height: 600px;"/>
<img src="images/fT_rsf_rule.drawio.svg" alt="MarineGEO circle logo" style="height: 600px;"/>
<img src="images/fT_wh_rule.drawio.svg" alt="MarineGEO circle logo" style="height: 600px;"/>
-->