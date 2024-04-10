# Wormholes formalization

## Task list

- [ ] Finish the formalization
- [x] Update the project with `dune`

## Dependencies

The formalization depends on the library `MMaps` findable in the coq community [git](https://github.com/coq-community/coq-mmaps) and the library `DeBrLevel` findable on [git](https://github.com/JordanIschard/DeBrLevel).

## The capture avoiding issue

The difficulty to formalize `Wormholes` comes from the naming of resources. Indeed, like in the lambda-calculus the naming of variable can provoke bad behavior in the case of lazy evaluation. In our case, **resources** are evaluated during the functional transition but **never replaced** and can **be moved by a substitution** during a beta-reduction. In order to avoid capture of names during an evaluation we have to cautiously deal with resources.

<!--
First versions do not deal with this issue and end up stuck.

Several representations exist to avoid the alpha renaming issue, we tested the **locally nameless** representation, but it also ends up stuck. The trick in this representation is to name the bound variables (_open_) only when we go through an abstraction and remove the name (_close_) when we go out the abstraction. Unfortunately, in the typing system needs to stock used resource names even the bound resources.

We try to brute force the issue with a handmade equivalence property, but it came to be very annoying to work with.  
-->

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