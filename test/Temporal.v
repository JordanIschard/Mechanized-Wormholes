From Coq Require Import Lists.Streams micromega.Lia Relations.Relation_Definitions 
                        Classes.RelationClasses Relations.Relation_Operators.
From Mecha Require Import Resource Resources Term Typ Var Substitution 
               Typing VContext RContext Evaluation REnvironment 
               Functional Stock Cell ReadStock WriteStock.


(**
  tt  ===> (R,P,W) --> (R1,P1,W1)
  mtt ===> (Rl,P,W) -- 0 --> (Rl1,P1,W1)
                ==> tt (nth 0 Rl,P,W) --> (R1,P1,W1)
      ===> (Rl,P,W) -- n+1 --> (Rln+1,Pn+1,Wn+1)
                ==> (Rl,P,W) -- n --> (Rln,Pn,Wn)
                ==> tt (nth n Rln,Pn,Wn) --> (Rn+1,Pn+1,Wn+1)

  R ::= map level (Λ * option Λ)
  R ::= map level (list Λ * list (option Λ))

  EN gros on montre le résultat de la nième itération avec une liste de n éléments d'entrée.
  une simulation à la reactimate en gros

  (Rl,P,W) -- n --> (Rln,Pn,Wn)
  (Rl,P,W) -- n-1 --> (Rln-1,Pn-1,Wn-1) --> (Rln,Pn,Wn)
  (Rl,P,W) -- n-2 --> (Rln-2,Pn-2,Wn-2) --> (Rln-1,Pn-1,Wn-1) --> (Rln,Pn,Wn)
  ...
  (Rl,P,W) -- 0 --> ... --> (Rln,Pn,Wn)
  (Rl,P,W) --> ... --> (Rln,Pn,Wn)
  (grossièrement)
*)