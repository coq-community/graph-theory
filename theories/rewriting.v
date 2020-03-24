Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect.
Require Import pttdom mgraph mgraph2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

Section s.
Variable X: pttdom.
Notation test := (test X).
Notation graph := (graph (pttdom_labels X)).
Notation graph2 := (graph2 (pttdom_labels X)).

(** * Rewrite System on Packaged Graphs *)

(* additive presentation *)

(* Universe S. *)
Inductive step: graph2 -> graph2 -> Prop (* Type@{S} *) :=
  | step_v0: forall G alpha,
      step
        (G ∔ alpha)
        G
  | step_v1: forall (G: graph2) x u alpha,
      step
        (G ∔ alpha ∔ [inl x, u, inr tt])
        (G [tst x <- [dom (u·alpha)]])
  | step_v2: forall G x y u alpha v,
      step
        (G ∔ alpha ∔ [inl x, u, inr tt] ∔ [inr tt, v, inl y])
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

Global Instance PreOrder_steps: PreOrder steps.
Proof.
  split. intro. by apply iso_step. 
  intros F G H S S'. induction S as [F G I|F G G' G'' I S _ IH].
  - destruct S' as [F' G' I'|F' G' G'' G''' I' S'].
    apply iso_step. etransitivity; eassumption.
    apply cons_step with G' G''=>//. etransitivity; eassumption.
  - apply cons_step with G G'=>//. by apply IH. 
Qed.

Global Instance isop_step: subrelation iso2prop steps.
Proof. intros F G [H]. by apply iso_step. Qed. 

Global Instance one_step: subrelation step steps.
Proof. intros F G S. now apply cons_step with F G. Qed.

Lemma steps_refl G: steps G G.
Proof. reflexivity. Qed.

End s.
Hint Resolve steps_refl : core.        (* in order [by] to get it *)
