From Coq Require Import Lists.Streams.
From Mecha Require Import Term Evaluation.


Module RealResource.

Import Streams.

Definition t : Type := (Stream Λ * Stream Λ).

Definition next (rr : t) : Λ := 
  let (inp,_) := rr in hd inp.

Definition put (v : Λ) (rr : t) : t :=
  let (inp,out) := rr in (tl inp,Cons v out).

Definition put_opt (v : option Λ) (rr : t) : t :=
  match v with
    | Some v' => put v' rr
    | _ => rr
  end.

Definition halts (rr : t) := 
  ForAll (fun st => halts (Streams.hd st)) (fst rr) /\
  ForAll (fun st => halts (Streams.hd st)) (snd rr).

Lemma halts_next t : 
  halts t -> Evaluation.halts (next t).
Proof.
  intros. destruct t; simpl; destruct H; simpl in *.
  destruct s; simpl in *; inversion H; now simpl in *.
Qed.

Lemma halts_put t v :
  halts t -> Evaluation.halts v -> halts (put v t).
Proof.
  intros; unfold put; destruct t; destruct H; split; simpl in *.
  - inversion H; auto.
  - split; simpl; auto.
Qed. 

Lemma halts_put_opt t v :
  halts t -> match v with Some v => Evaluation.halts v | _ => True end -> halts (put_opt v t).
Proof.
  intros. destruct v; auto. unfold put_opt; now apply halts_put.
Qed. 

End RealResource.



Module RealResources.

Import List.

Definition t : Type := list RealResource.t.

Definition nexts (fl : t) : list Λ := map RealResource.next fl.

Definition puts (vl : list (option Λ)) (fl : t) : t :=
  map (fun vf => RealResource.put_opt (fst vf) (snd vf)) (combine vl fl).

Definition halts := List.Forall RealResource.halts.

Lemma halts_nexts t : 
  halts t -> List.Forall Evaluation.halts (nexts t).  
Proof.
  unfold halts; intros; induction H; simpl; auto.
  apply List.Forall_cons_iff; split; auto. now apply RealResource.halts_next.
Qed.

Lemma halts_puts t vl :
  halts t -> 
  List.Forall (fun v => match v with Some v => Evaluation.halts v | _ => True end) vl ->
  halts (puts vl t).
Proof.
  revert vl; induction t; intros; simpl in *.
  - unfold puts, combine; destruct vl; simpl; auto.
  - destruct vl.
    -- unfold puts; simpl; unfold halts; auto.
    -- unfold puts; simpl; unfold halts in *. apply Forall_cons_iff; split.
       + rewrite Forall_cons_iff in *; destruct H,H0.
         apply RealResource.halts_put_opt; auto; destruct o; auto.
       + rewrite Forall_cons_iff in *; destruct H,H0.
         apply IHt; auto.
Qed.

End RealResources.