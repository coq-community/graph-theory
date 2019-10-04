Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect.
Require Export pttdom mgraph2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

Section s.
Variable A: Type.
Notation test := (test (tm_pttdom A)). 
Notation term := (term A).
Notation graph := (graph test term).
Notation graph2 := (graph2 test term).

(* HACK: unluckily, declaring [pttdom_bisetoid] as canonical
   does not make it possible to solve [tm_setoid A = setoid_of_bisetoid _]
   which is needed at a few places.
   we solve this by declaring the following instance as canonical *)
Canonical Structure tm_bisetoid :=
  @BiSetoid (tm_setoid A) (@eqv' (tm_pttdom A))
            (@eqv'_sym (tm_pttdom A))
            (@eqv10 (tm_pttdom A)) (@eqv01 (tm_pttdom A)) (@eqv11 (tm_pttdom A)).
(* we would be happier with the following declaration, but Eval hnf does not simplify enough... *)
(* Canonical Structure tm_bisetoid := Eval hnf in pttdom_bisetoid (tm_pttdom A). *)

(* following command should work 
   Check erefl: tm_setoid A = setoid_of_bisetoid _.  
 *)

(* rewriting system *)

(* Universe S. *)
Inductive step: graph2 -> graph2 -> Prop (* Type@{S} *) :=
  | step_v0: forall G alpha,
      step
        (G ∔ alpha)
        G
  | step_v1: forall (G: graph2) x u alpha,
      step
        (G ∔ alpha ∔ [Some x, u, None])
        (G [tst x <- [dom (u·alpha)]])
  | step_v2: forall G x y u alpha v,
      step
        (G ∔ alpha ∔ [Some x, u, None] ∔ [None, v, Some y])
        (G ∔ [x, u·alpha·v, y])
  | step_e0: forall G x u,
      step
        (G ∔ [x, u, x])
        (G [tst x <- [1∥u]])
  | step_e2: forall G x y u v,
      step
        (G ∔ [x, u, y] ∔ [x, v, y])
        (G ∔ [x, u∥v, y]).

Inductive steps: relation graph2 :=
  | iso_step F G: iso2 F G -> steps F G
  | cons_step F G H H': iso2 F G -> step G H -> steps H H' -> steps F H'.
(* Global Existing Instance iso_step. *)


(* TODO: let reflexivity belong to // again (should work in the two proofs below) *)
Global Instance PreOrder_steps: PreOrder steps.
Proof.
  split. intro. apply iso_step. reflexivity. 
  intros F G H S S'. induction S as [F G I|F G G' G'' I S _ IH].
  - destruct S' as [F' G' I'|F' G' G'' G''' I' S'].
    apply iso_step. etransitivity; eassumption.
    apply cons_step with G' G''=>//. etransitivity; eassumption.
  - apply cons_step with G G'=>//. by apply IH. 
Qed.

Global Instance one_step: subrelation step steps.
Proof. intros F G S. now apply cons_step with F G. Qed.

End s.
