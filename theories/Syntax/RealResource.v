From Coq Require Import Lists.Streams.
Require Import Term.


Module RealResource.

Import Streams.

Definition t : Type := (Stream Λ * Stream Λ).

Definition next (rr : t) : Λ * t := 
  let (inp,out) := rr in (hd inp, (tl inp,out)).

Definition put (v : Λ) (rr : t) : t :=
  let (inp,out) := rr in (inp,Cons v out).

Definition put_opt (v : option Λ) (rr : t) : t :=
  match v with
    | Some v' => put v' rr
    | _ => rr
  end.


End RealResource.



Module RealResources.

Import List.

Definition t : Type := list RealResource.t.

Definition nexts (fl : t) : list Λ * t :=
  split (map RealResource.next fl).

Definition puts (vl : list (option Λ)) (fl : t) : t :=
  map (fun vf => RealResource.put_opt (fst vf) (snd vf)) (combine vl fl).

End RealResources.