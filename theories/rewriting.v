Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect.
Require Import setoid_bigop structures pttdom mgraph mgraph2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

Section s.
Variable X: pttdom.
Notation test := (test X).
Notation graph := (graph test X).
Notation graph2 := (graph2 test X).

(** * Rewrite System on Packaged Graphs *)

(** note: 
- we need everything to be finite to get a terminating rewrite system
- elsewhere we don't care that the edge type is a finType, it could certainly just be a Type
- the vertex type has to be an eqType at various places since we regularly compare vertices (e.g., [add_vlabel])
- the vertex type has to be a finType for the [merge] operation, but only in order to express the new vertex labeling function... we could imagine a [finitary_merge] operation that would not impose this restriction
- the vertex type has to be finite also when we go to open graphs (although maybe countable would suffice) *)

(** additive presentation *)

Inductive step: graph2 -> graph2 -> Prop :=
  | step_v0: forall G alpha,
      step
        (G ∔ alpha)
        G
  | step_v1: forall (G: graph2) x u alpha,
      step
        (G ∔ alpha ∔ [inl x, u, inr tt])
        (G [tst x <- [dom (u·elem_of alpha)]])
  | step_v2: forall G x y u alpha v,
      step
        (G ∔ alpha ∔ [inl x, u, inr tt] ∔ [inr tt, v, inl y])
        (G ∔ [x, u·elem_of alpha·v, y])
  | step_e0: forall G x u,
      step
        (G ∔ [x, u, x])
        (G [tst x <- [1%ptt∥u]])
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
