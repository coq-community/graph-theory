From HB Require Import structures.
Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import edone preliminaries setoid_bigop structures pttdom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

(** * 2p algebras, tests, initial algebra of terms *)

(** ** 2p algebras (2pdom algebras with top) *)

(** We define [ptt] as a substructure of [pttdom] where [top] is
interpreted appropriately. We also provide a factory where the laws
for [dom], (i.e., [A13] and [A14]) can be omitted, as they are
derivable *)

HB.mixin Record Ptt_of_Pttdom A of Pttdom A := 
  { A11: forall x: A, x · top ≡ dom x · top;
    A12: forall x y: A, (x∥1) · y ≡ (x∥1)·top ∥ y;
    domE: forall x: A, dom x ≡ 1 ∥ x·top }.
HB.structure Definition Ptt := { A of Ptt_of_Pttdom A & }.
Notation ptt := Ptt.type.

HB.factory Record Ptt_of_Ops A of Ops_of_Type A & Setoid_of_Type A :=
  { dot_eqv: Proper (eqv ==> eqv ==> eqv) (dot : A -> A -> A);
    par_eqv: Proper (eqv ==> eqv ==> eqv) (par : A -> A -> A);
    cnv_eqv: Proper (eqv ==> eqv) (cnv : A -> A);
    domE: forall x: A, dom x ≡ 1 ∥ x·top;
    parA: forall x y z: A, x ∥ (y ∥ z) ≡ (x ∥ y) ∥ z;
    parC: forall x y: A, x ∥ y ≡ y ∥ x;
    dotA: forall x y z: A, x · (y · z) ≡ (x · y) · z;
    dotx1: forall x: A, x · 1 ≡ x;
    cnvI: forall x: A, x°° ≡ x;
    cnvpar: forall x y: A, (x ∥ y)° ≡ x° ∥ y°;
    cnvdot: forall x y: A, (x · y)° ≡ y° · x°;
    par11: 1 ∥ 1 ≡ 1 :> A ;
    A10: forall x y: A, 1 ∥ x·y ≡ dom (x ∥ y°);
    A11: forall x: A, x · top ≡ dom x · top;
    A12: forall x y: A, (x∥1) · y ≡ (x∥1)·top ∥ y
  }.

HB.builders Context A (F : Ptt_of_Ops A).

  Instance ptt_equivalence : Equivalence (@eqv [the setoid of A]).
  Proof. exact: Eqv. Qed.

  Instance ptt_par_eqv : Proper (eqv ==> eqv ==> eqv) (par : A -> A -> A).
  Proof. exact: par_eqv. Qed.

  Instance ptt_dot_eqv : Proper (eqv ==> eqv ==> eqv) (dot : A -> A -> A).
  Proof. exact: dot_eqv. Qed.

  Lemma A13_ (x y: A): dom(x·y) ≡ dom(x·dom y).
  Proof. by rewrite domE -dotA A11 dotA -domE. Qed.

  Lemma A14_ (x y z: A): dom x·(y∥z) ≡ dom x·y ∥ z.
  Proof. by rewrite domE parC A12 (A12 _ y) parA. Qed.

  Lemma dom_eqv_ : Proper (eqv ==> eqv) (dom : A -> A).
  Proof. by move=> x y xy; rewrite !domE xy. Qed.

  HB.instance Definition Pttdom_of_Ops := 
    Pttdom_of_Ops.Build A 
      dot_eqv par_eqv cnv_eqv dom_eqv_ 
      parA parC dotA dotx1 cnvI cnvpar cnvdot par11 A10 A13_ A14_.

  HB.instance Definition Ptt_of_Ops := 
    Ptt_of_Pttdom.Build A A11 A12 domE.

HB.end.

#[export]
Instance ptt_equivalence (A : ptt) : Equivalence (@eqv [the ptt of A]).
Proof. exact: Eqv. Qed.

#[export]
Instance ptt_par_eqv (A : ptt) : Proper (eqv ==> eqv ==> eqv) (par : A -> A -> A).
Proof. exact: par_eqv. Qed.

#[export]
Instance ptt_dot_eqv (A : ptt) : Proper (eqv ==> eqv ==> eqv) (dot : A -> A -> A).
Proof. exact: dot_eqv. Qed.

(** ** basic derivable laws  *)
Section derived.
 Variable X: ptt.
 
 Lemma parxtop (x: X): x ∥ top ≡ x.
 Proof.
   symmetry. generalize (A12 1 x).
   by rewrite par11 2!dot1x parC. 
 Qed.

 Lemma partopx (x: X): top ∥ x ≡ x.
 Proof. by rewrite parC parxtop. Qed.

 Lemma cnvtop: top° ≡ @top X.
 Proof.
  rewrite -(parxtop top°) -{2}(cnvI top).
  by rewrite -cnvpar partopx cnvI.
 Qed.

End derived.

Section terms.
 Variable A: Type.
 Inductive term :=
 | tm_dot: term -> term -> term
 | tm_par: term -> term -> term
 | tm_cnv: term -> term
 | tm_dom: term -> term
 | tm_one: term
 | tm_top: term
 | tm_var: A -> term.
 Section e.
 Variable (X: Ops.type) (f: A -> X).
 Fixpoint eval (u: term): X :=
   match u with
   | tm_dot u v => eval u · eval v
   | tm_par u v => eval u ∥ eval v
   | tm_cnv u => (eval u) °
   | tm_dom u => dom (eval u)
   | tm_one => 1
   | tm_top => top
   | tm_var a => f a
   end.
 End e.
 Definition tm_eqv (u v: term): Prop :=
   forall (X: ptt) (f: A -> X), eval f u ≡ eval f v.

 Hint Unfold tm_eqv : core.
 Lemma tm_eqv_equivalence: Equivalence tm_eqv.
 Proof.
   constructor.
     now intro.
     intros ?? H X f. specialize (H X f). by symmetry. 
     intros ??? H H' X f. specialize (H X f). specialize (H' X f). etransitivity. apply H. apply H'.
 Qed.
 HB.instance Definition tm_setoid := Setoid_of_Type.Build term tm_eqv_equivalence.
 
 HB.instance Definition tm_ops := Ops_of_Type.Build term tm_dot tm_par tm_cnv tm_dom tm_one tm_top.

 Let tm_eqv_eqv (u v: term) (X: ptt) (f: A -> X) : u ≡ v -> eval f u ≡ eval f v. 
 Proof. exact. Qed.
 
 (* quotiented terms indeed form a 2p algebra *)
 Definition tm_ptt : Ptt_of_Ops.axioms_ term tm_ops tm_setoid.
  refine (Ptt_of_Ops.Build term _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    abstract (repeat intro; simpl; by apply: dot_eqv; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply: par_eqv; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply: cnv_eqv; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply: domE; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply: parA; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply: parC; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply: dotA; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply: dotx1; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply: cnvI; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply: cnvpar; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply: cnvdot; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply: par11; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply: A10; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply: A11; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply: A12; apply: tm_eqv_eqv).
 Defined.
 HB.instance Definition _ := tm_ptt.

End terms.
Declare Scope ptt_ops.
Bind Scope ptt_ops with term.
