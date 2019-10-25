Require Export Setoid Morphisms.
From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries.
Require Export structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

(** * 2p algebras, tests, initial algebra of terms *)

(** ** 2p algebras (2pdom algebras with top) *)

(* TODO: prove that 2p-algebras are 2pdom algebras to share related definitions and proofs 
   (requires properly setting up structures)
 *)

(* operations are put apart so that the can get notations for them before stating/proving the laws  *)
Structure ops_ :=
  { setoid_of_ops:> setoid;
    dot: setoid_of_ops -> setoid_of_ops -> setoid_of_ops;
    par: setoid_of_ops -> setoid_of_ops -> setoid_of_ops;
    cnv: setoid_of_ops -> setoid_of_ops;
    dom: setoid_of_ops -> setoid_of_ops;
    one: setoid_of_ops;
    top: setoid_of_ops }.

Bind Scope ptt_ops with setoid_of_ops.
Delimit Scope ptt_ops with ptt.
Open Scope ptt_ops.
Notation "x ∥ y" := (par x y) (left associativity, at level 40, format "x ∥ y"): ptt_ops.
Notation "x · y" := (dot x y) (left associativity, at level 25, format "x · y"): ptt_ops.
Notation "x °"  := (cnv x) (left associativity, at level 5, format "x °"): ptt_ops.
Notation "1"  := (one _): ptt_ops.
Arguments top [_].

(* 2p axioms *)
Structure ptt :=
  { ops:> ops_;
    dot_eqv: Proper (eqv ==> eqv ==> eqv) (@dot ops);
    par_eqv: Proper (eqv ==> eqv ==> eqv) (@par ops);
    cnv_eqv: Proper (eqv ==> eqv) (@cnv ops);
    domE: forall x: ops, dom x ≡ 1 ∥ x·top;
    parA: forall x y z: ops, x ∥ (y ∥ z) ≡ (x ∥ y) ∥ z;
    parC: forall x y: ops, x ∥ y ≡ y ∥ x;
    dotA: forall x y z: ops, x · (y · z) ≡ (x · y) · z;
    dotx1: forall x: ops, x · 1 ≡ x;
    cnvI: forall x: ops, x°° ≡ x;
    cnvpar: forall x y: ops, (x ∥ y)° ≡ x° ∥ y°;
    cnvdot: forall x y: ops, (x · y)° ≡ y° · x°;
    par11: 1 ∥ 1 ≡ one ops;
    A10: forall x y: ops, 1 ∥ x·y ≡ dom (x ∥ y°);
    A11: forall x: ops, x · top ≡ dom x · top;
    A12: forall x y: ops, (x∥1) · y ≡ (x∥1)·top ∥ y
  }.
Existing Instances dot_eqv par_eqv cnv_eqv.

(** ** basic derivable laws  *)
Section derived.
 Variable X: ptt.
  
 Global Instance dom_eqv: Proper (eqv ==> eqv) (@dom X).
 Proof. intros ?? H. by rewrite 2!domE H. Qed.

 Lemma cnv1: 1° ≡ @one X.
 Proof.
  rewrite -(dotx1 1°) -{2}(cnvI 1).
  by rewrite -cnvdot dotx1 cnvI.
 Qed.

 Lemma dot1x (x: X): 1·x ≡ x.
 Proof. by rewrite -(cnvI (1·x)) cnvdot cnv1 dotx1 cnvI. Qed.

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

 Lemma cnv_inj (x y: X): x° ≡ y° -> x ≡ y.
 Proof. intro H. by rewrite -(cnvI x) -(cnvI y) H. Qed.

 Lemma dotcnv (x y: X): x·y ≡ (y°·x°)°.
 Proof. apply cnv_inj. by rewrite cnvdot cnvI. Qed.
 
 Lemma A13 (x y: X): dom(x·y) ≡ dom(x·dom y).
 Proof. by rewrite domE -dotA A11 dotA -domE. Qed.

 Lemma A14 (x y z: X): dom x·(y∥z) ≡ dom x·y ∥ z.
 Proof. by rewrite domE parC A12 (A12 _ y) parA. Qed.

 (** ** tests *)
 Definition is_test (x: X) := dom x ≡ x.
 Record test := Test{ elem_of:> X ; testE: is_test elem_of }.

 Lemma is_test_alt (x: X): dom x ≡ x <-> x∥1 ≡ x.
 Proof.
   split=>E.
   - rewrite -{1}E -{1}(dotx1 (dom x)) -A14.
     by rewrite par11 dotx1. 
   - by rewrite -E -{1}cnv1 -A10 dotx1 parC.
 Qed.
 
 Lemma domtst (a : test) : dom a ≡ a. 
 Proof. apply testE. Qed.
 
 Lemma tstpar1 (a : test) : a ∥ 1 ≡ a.
 Proof. apply is_test_alt, domtst. Qed.

 Lemma one_test: is_test 1. 
 Proof. rewrite /is_test. by rewrite -{1}par11 -{2}cnv1 -A10 dotx1 par11. Qed.
 Canonical Structure tst_one := Test one_test. 

 Lemma dom_test x: is_test (dom x). 
 Proof. rewrite /is_test. by rewrite -{1}[dom x]dot1x -A13 dot1x. Qed.
 Canonical Structure tst_dom x := Test (dom_test x).
 
 Lemma par_test (a: test) (u: X): is_test (a∥u).
 Proof.
   rewrite /is_test is_test_alt.
   by rewrite -parA (parC u) parA tstpar1. 
 Qed.
 Canonical Structure tst_par a u := Test (par_test a u).

 Lemma cnvtst (a: test): a° ≡ a.
 Proof.
   rewrite -tstpar1 cnvpar cnv1 -(dot1x (a°)) parC A10 cnvI parC.
   apply domtst.
 Qed.

 Lemma cnv_test (a: test): is_test (a°).
 Proof.
   by rewrite /is_test is_test_alt cnvtst tstpar1. 
 Qed.
 Canonical Structure tst_cnv a := Test (cnv_test a).

 Lemma tstpar (a: test) (x y: X): a·(x∥y) ≡ a·x ∥ y.
 Proof. rewrite -domtst. apply A14. Qed.

 Lemma pardot (a b: test): a ∥ b ≡ a·b.
 Proof.
   by rewrite -{2}(tstpar1 b) (parC _ 1) tstpar dotx1.
 Qed.
 
 Lemma dot_test (a b: test): is_test (a·b).
 Proof. rewrite /is_test -pardot. apply domtst. Qed.
 Canonical Structure tst_dot a b := Test (dot_test a b).
 
 (** automatised inference of tests *)
 Definition infer_test x y (e: elem_of y = x) := y.
 Notation "[ x ]" := (@infer_test x _ erefl).

 (** ** commutative monoid of  tests *)
 Definition eqv_test (a b: test) := a ≡ b.
 Arguments eqv_test _ _ /.
 Lemma eqv_test_equiv: Equivalence eqv_test. 
 Proof. 
   split => [x|x y|x y z]; rewrite /eqv_test /=.
   reflexivity. by symmetry. by transitivity (elem_of y).
 Qed.
 Canonical Structure ptt_test_setoid := Setoid eqv_test_equiv.
 Lemma tst_dot_eqv: Proper (eqv ==> eqv ==> eqv) tst_dot.
 Proof. intros [a] [b] ? [c] [d] ?. by apply dot_eqv. Qed.
 Lemma tst_dotA: forall a b c: test, a·(b·c) ≡ (a·b)·c.
 Proof. intros [a] [b] [c]. apply dotA. Qed.
 Lemma tst_dotC: forall a b: test, a·b ≡ b·a.
 Proof. intros. rewrite -2!pardot. apply parC. Qed.
 Lemma tst_dotU: forall a: test, a·1 ≡ a.
 Proof. intros [a]. apply dotx1. Qed.

 (** ** label structure of a 2pdom algebra (Definition 4.3)  *)
 
 (* dualised equality (to get the [labels] structure below) *)
 Definition eqv' (x y: X) := x ≡ y°.
 Arguments eqv' _ _ /.
 Lemma eqv'_sym: Symmetric eqv'.
 Proof. move=> x y /= H. apply cnv_inj. by rewrite cnvI H. Qed.
 Lemma eqv01 x y z: x ≡ y -> eqv' y z -> eqv' x z.
 Proof. by move=> /= ->. Qed.
 Lemma eqv11 x y z: eqv' x y -> eqv' y z -> x ≡ z.
 Proof. move=> /= -> ->. apply cnvI. Qed.
 
 Canonical Structure ptt_labels: labels :=
   Labels
     tst_dot_eqv tst_dotA tst_dotC tst_dotU
     eqv'_sym eqv01 eqv11.

End derived.
Coercion ptt_labels: ptt >-> labels. 
Notation "[ x ]" := (@infer_test _ x%ptt _ erefl): ptt_ops.

Arguments eqv : simpl never.

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
 Variable (X: ops_) (f: A -> X).
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
 Hint Unfold tm_eqv.
 Lemma tm_eqv_equivalence: Equivalence tm_eqv.
 Proof.
   constructor.
     now intro.
     intros ?? H X f. specialize (H X f). by symmetry. 
     intros ??? H H' X f. specialize (H X f). specialize (H' X f). etransitivity. apply H. apply H'.
 Qed.
 Canonical Structure tm_setoid := Setoid tm_eqv_equivalence. 
 Canonical Structure tm_ops_ :=
   {| setoid_of_ops := tm_setoid;
      dot := tm_dot;
      par := tm_par;
      cnv := tm_cnv;
      dom := tm_dom;
      one := tm_one;
      top := tm_top |}.
 
 (* quotiented terms indeed form a 2p-algebra *)
 Program Definition tm_ptt: ptt := {| ops := tm_ops_ |}.
 Next Obligation. repeat intro; simpl. by apply dot_eqv. Qed.
 Next Obligation. repeat intro; simpl. by apply par_eqv. Qed.
 Next Obligation. repeat intro; simpl. by apply cnv_eqv. Qed.
 Next Obligation. repeat intro; simpl. by apply domE. Qed.
 Next Obligation. repeat intro; simpl. by apply parA. Qed.
 Next Obligation. repeat intro; simpl. by apply parC. Qed.
 Next Obligation. repeat intro; simpl. by apply dotA. Qed.
 Next Obligation. repeat intro; simpl. by apply dotx1. Qed.
 Next Obligation. repeat intro; simpl. by apply cnvI. Qed.
 Next Obligation. repeat intro; simpl. by apply cnvpar. Qed.
 Next Obligation. repeat intro; simpl. by apply cnvdot. Qed.
 Next Obligation. repeat intro; simpl. by apply par11. Qed.
 Next Obligation. repeat intro; simpl. by apply A10. Qed.
 Next Obligation. repeat intro; simpl. by apply A11. Qed.
 Next Obligation. repeat intro; simpl. by apply A12. Qed.
 Canonical tm_ptt. 
 
 Notation test := (test tm_ptt).
End terms.
Bind Scope ptt_ops with term.
