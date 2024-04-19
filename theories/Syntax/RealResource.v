From Coq Require Import Lists.Streams.
From Mecha Require Import Term Evaluation.


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

Definition halts (rr : t) := 
  ForAll (fun st => halts (Streams.hd st)) (fst rr) /\
  ForAll (fun st => halts (Streams.hd st)) (snd rr).

End RealResource.



Module RealResources.

Import List.

Definition t : Type := list RealResource.t.

Definition nexts (fl : t) : list Λ * t :=
  split (map RealResource.next fl).

Definition puts (vl : list (option Λ)) (fl : t) : t :=
  map (fun vf => RealResource.put_opt (fst vf) (snd vf)) (combine vl fl).

Definition halts := List.Forall RealResource.halts.

End RealResources.