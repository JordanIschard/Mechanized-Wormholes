From Mecha Require Import Resource Term Typ Var ReadStock WriteStock Stock Typing
                          Cell VContext REnvironment RContext ET_Definition FT_Definition
                          Sample Samples.
(**

Definition temporal (S S1 : 𝐒) (P P' : Λ) (W W1 : 𝐖) :=
  forall Vin Vout Wnew _tv,
    (Vin = Stock.init_virtual W (Samples.nexts S))%re /\
                    
    ⪡ Vin ; unit ; P ⪢ ⭆ ⪡ Vout ; _tv ; P' ; Wnew ⪢ /\
                    
    (S1 = Samples.puts Vout S) /\ (W1 = Stock.update Wnew Vout)%sk. 

Notation "'⟦' S ';' W ';' P '⟧' '⟾' '⟦' S1 ';' W1 ';' P1 '⟧'" 
  := (temporal S S1 P P1 W W1) (at level 30, S constr, S1 constr,
                                             P custom wh, P1 custom wh, 
                                             W constr, W1 constr, no associativity).


*)