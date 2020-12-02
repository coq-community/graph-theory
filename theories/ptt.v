Require Import Setoid Morphisms.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries setoid_bigop structures pttdom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

(** * 2p algebras, tests, initial algebra of terms *)

(** ** 2p algebras (2pdom algebras with top) *)

(** TOTHINK: We could also let [ptt] inherit from [pttdom] and turn the record below into a factory *)

(* 2p axioms *)
HB.mixin Record Ptt_of_Ops A of Ops_of_Type A & Setoid_of_Type A := 
  { dot_eqv_: Proper (eqv ==> eqv ==> eqv) (dot : A -> A -> A);
    par_eqv_: Proper (eqv ==> eqv ==> eqv) (par : A -> A -> A);
    cnv_eqv_: Proper (eqv ==> eqv) (cnv : A -> A);
    domE: forall x: A, dom x ≡ 1 ∥ x·top;
    parA_: forall x y z: A, x ∥ (y ∥ z) ≡ (x ∥ y) ∥ z;
    parC_: forall x y: A, x ∥ y ≡ y ∥ x;
    dotA_: forall x y z: A, x · (y · z) ≡ (x · y) · z;
    dotx1_: forall x: A, x · 1 ≡ x;
    cnvI_: forall x: A, x°° ≡ x;
    cnvpar_: forall x y: A, (x ∥ y)° ≡ x° ∥ y°;
    cnvdot_: forall x y: A, (x · y)° ≡ y° · x°;
    par11_: 1 ∥ 1 ≡ 1 :> A ;
    A10_: forall x y: A, 1 ∥ x·y ≡ dom (x ∥ y°);
    A11: forall x: A, x · top ≡ dom x · top;
    A12: forall x y: A, (x∥1) · y ≡ (x∥1)·top ∥ y
  }.
HB.structure Definition Ptt := { A of Ptt_of_Ops A & }.
Notation ptt := Ptt.type.

(** ** basic derivable laws  *)
Section derived.
 Variable X: ptt.
 Existing Instances dot_eqv_ par_eqv_ cnv_eqv_.
  
 Instance dom_eqv_: Proper (eqv ==> eqv) (@dom X).
 Proof. intros ?? H. by rewrite 2!domE H. Qed.
 
 Lemma A13_ (x y: X): dom(x·y) ≡ dom(x·dom y).
 Proof. by rewrite domE -dotA_ A11 dotA_ -domE. Qed.

 Lemma A14_ (x y z: X): dom x·(y∥z) ≡ dom x·y ∥ z.
 Proof. by rewrite domE parC_ A12 (A12 _ y) parA_. Qed.

 HB.instance Definition pttdom_of_ptt := 
   Pttdom_of_Ops.Build (Ptt.sort X)
    (@dot_eqv_ X)
    (@par_eqv_ X)
    (@cnv_eqv_ X)
    (dom_eqv_)
    (@parA_ X)
    (@parC_ X)
    (@dotA_ X)
    (@dotx1_ X)
    (@cnvI_ X)
    (@cnvpar_ X)
    (@cnvdot_ X)
    (@par11_ X)
    (@A10_ X)
    (A13_)
    (A14_).
 
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
 Definition tm_ptt : Ptt_of_Ops.axioms_ tm_setoid tm_ops.
  refine (Ptt_of_Ops.Build term _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    abstract (repeat intro; simpl; by apply dot_eqv_; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply par_eqv_; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply cnv_eqv_; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply domE; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply parA_; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply parC_; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply dotA_; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply dotx1_; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply cnvI_; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply cnvpar_; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply cnvdot_; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply par11_; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply A10_; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply A11; apply: tm_eqv_eqv).
    abstract (repeat intro; simpl; by apply A12; apply: tm_eqv_eqv).
 Defined.
 HB.instance term tm_ptt.

End terms.
Declare Scope ptt_ops.
Bind Scope ptt_ops with term.
