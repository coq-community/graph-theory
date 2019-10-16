Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries.
Require Export structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

(* 2pdom algebra, initial algebra of terms, tests *)

(* TODO: 2p algebra and their links with 2pdom algebra *)

(* operations are put apart so that the can get notations for them before stating/proving the laws  *)
Structure ops_ :=
  { setoid_of_ops:> setoid;
    dot: setoid_of_ops -> setoid_of_ops -> setoid_of_ops;
    par: setoid_of_ops -> setoid_of_ops -> setoid_of_ops;
    cnv: setoid_of_ops -> setoid_of_ops;
    dom: setoid_of_ops -> setoid_of_ops;
    one: setoid_of_ops }.

Bind Scope pttdom_ops with setoid_of_ops.
Delimit Scope pttdom_ops with ptt.
Open Scope pttdom_ops.
Notation "x ∥ y" := (par x y) (left associativity, at level 40, format "x ∥ y"): pttdom_ops.
Notation "x · y" := (dot x y) (left associativity, at level 25, format "x · y"): pttdom_ops.
Notation "x °"  := (cnv x) (left associativity, at level 5, format "x °"): pttdom_ops.
Notation "1"  := (one _): pttdom_ops.

Structure pttdom :=
  { ops:> ops_;
    dot_eqv: Proper (eqv ==> eqv ==> eqv) (@dot ops);
    par_eqv: Proper (eqv ==> eqv ==> eqv) (@par ops);
    cnv_eqv: Proper (eqv ==> eqv) (@cnv ops);
    dom_eqv: Proper (eqv ==> eqv) (@dom ops);
    (* domE: forall x: ops, dom x ≡ 1 ∥ x·top; *)
    parA: forall x y z: ops, x ∥ (y ∥ z) ≡ (x ∥ y) ∥ z;
    parC: forall x y: ops, x ∥ y ≡ y ∥ x;
    dotA: forall x y z: ops, x · (y · z) ≡ (x · y) · z;
    dotx1: forall x: ops, x · 1 ≡ x;
    cnvI: forall x: ops, x°° ≡ x;
    cnvpar: forall x y: ops, (x ∥ y)° ≡ x° ∥ y°;
    cnvdot: forall x y: ops, (x · y)° ≡ y° · x°;
    par11: 1 ∥ 1 ≡ one ops;
    A10: forall x y: ops, 1 ∥ x·y ≡ dom (x ∥ y°);
    (* A11: forall x: ops, x · top ≡ dom x · top; *)
    (* A12: forall x ops: X, (x∥1) · y ≡ (x∥1)·top ∥ y *)
    A13: forall x y: ops, dom(x·y) ≡ dom(x·dom y);
    A14: forall x y z: ops, dom x·(y∥z) ≡ dom x·y ∥ z;
  }.
Existing Instances dot_eqv par_eqv cnv_eqv dom_eqv.

Section derived.

 Variable X: pttdom.

 Lemma cnv1: 1° ≡ one X.
 Proof.
  rewrite <-dotx1. rewrite <-(cnvI 1) at 2.
  by rewrite <-cnvdot, dotx1, cnvI.
 Qed.

 Lemma dot1x (x: X): 1·x ≡ x.
 Proof. by rewrite <-cnvI, cnvdot, cnv1, dotx1, cnvI. Qed.

 Lemma cnv_inj (x y: X): x° ≡ y° -> x ≡ y.
 Proof. intro. rewrite <-(cnvI x), <-(cnvI y). by apply cnv_eqv. Qed.

 Lemma dotcnv (x y: X): x·y ≡ (y°·x°)°.
 Proof. apply cnv_inj. by rewrite cnvdot cnvI. Qed.

 (* tests *)
 Definition is_test (x: X) := dom x ≡ x.
 Record test := Test{ elem_of:> X ; testE: is_test elem_of }.
 Lemma one_test: is_test 1.
 Admitted.
 Canonical Structure tst_one := Test one_test. 
 Lemma dom_test x: is_test (dom x).
 Admitted.
 Canonical Structure tst_dom x := Test (dom_test x).
 Lemma par_test (a: test) (u: X): is_test (a∥u).
 Admitted.
 Canonical Structure tst_par a u := Test (par_test a u). 
 Lemma dot_test (a b: test): is_test (a·b).
 Admitted.
 Canonical Structure tst_dot a b := Test (dot_test a b).
 Lemma cnv_test (a: test): is_test (a°).
 Admitted.
 Canonical Structure tst_cnv a := Test (cnv_test a).
 (* automatised inference of tests *)
 Definition infer_test x y (e: elem_of y = x) := y.
 Notation "[ x ]" := (@infer_test x _ erefl).

 (* commutative monoid of  tests *)
 Definition eqv_test (a b: test) := a ≡ b.
 Arguments eqv_test _ _ /.
 Lemma eqv_test_equiv: Equivalence eqv_test.
 Admitted. 
 Canonical Structure pttdom_test_setoid := Setoid eqv_test_equiv.
 Lemma tst_dot_eqv: Proper (eqv ==> eqv ==> eqv) tst_dot.
 Proof. intros [a] [b] ? [c] [d] ?. by apply dot_eqv. Qed.
 Lemma tst_dotA: forall a b c: test, [a·[b·c]] ≡ [[a·b]·c].
 Proof. intros [a] [b] [c]. apply dotA. Qed.
 Lemma tst_dotC: forall a b: test, [a·b] ≡ [b·a].
 Admitted.
 Lemma tst_dotU: forall a: test, [a·1] ≡ a.
 Proof. intros [a]. apply dotx1. Qed.

 (* dualised equality (to get the [labels] structure below) *)
 Definition eqv' (x y: X) := x ≡ y°.
 Arguments eqv' _ _ /.
 Lemma eqv'_sym: Symmetric eqv'.
 Proof. move=> x y /= H. apply cnv_inj. by rewrite cnvI H. Qed.
 Lemma eqv10 x y z: eqv' x y -> y ≡ z -> eqv' x z.
 Proof. by move=> /= H <-. Qed.
 Lemma eqv01 x y z: x ≡ y -> eqv' y z -> eqv' x z.
 Proof. by move=> /= ->. Qed.
 Lemma eqv11 x y z: eqv' x y -> eqv' y z -> x ≡ z.
 Proof. move=> /= -> ->. apply cnvI. Qed.
 
 Canonical Structure pttdom_labels: labels :=
   Labels
     tst_dot_eqv tst_dotA tst_dotC tst_dotU
     eqv'_sym eqv10 eqv01 eqv11.
 
End derived.
Coercion pttdom_labels: pttdom >-> labels. 
Notation "[ x ]" := (@infer_test _ x%ptt _ erefl): pttdom_ops.


(* initial algebra of terms *)
Section terms.
 Variable A: Type.
 Inductive term :=
 | tm_dot: term -> term -> term
 | tm_par: term -> term -> term
 | tm_cnv: term -> term
 | tm_dom: term -> term
 | tm_one: term
 | tm_var: A -> term.
 Bind Scope pttdom_ops with term.
 Section e.
 Variable (X: ops_) (f: A -> X).
 Fixpoint eval (u: term): X :=
   match u with
   | tm_dot u v => eval u · eval v
   | tm_par u v => eval u ∥ eval v
   | tm_cnv u => (eval u) °
   | tm_dom u => dom (eval u)
   | tm_one => 1
   | tm_var a => f a
   end.
 End e.
 (* axiomatic equality on terms (we do not prove it, but this
    impredicative encoding is equivalent to the inductive defining
    equational reasoning in pttdom) *)
 Definition tm_eqv (u v: term): Prop :=
   forall (X: pttdom) (f: A -> X), eval f u ≡ eval f v.
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
      one := tm_one |}.
 (* quotiented terms indeed form a pttdom *)
 Program Definition tm_pttdom: pttdom := {| ops := tm_ops_ |}.
 Next Obligation. repeat intro; simpl. by apply dot_eqv. Qed.
 Next Obligation. repeat intro; simpl. by apply par_eqv. Qed.
 Next Obligation. repeat intro; simpl. by apply cnv_eqv. Qed.
 Next Obligation. repeat intro; simpl. by apply dom_eqv. Qed.
 Next Obligation. repeat intro; simpl. by apply parA. Qed.
 Next Obligation. repeat intro; simpl. by apply parC. Qed.
 Next Obligation. repeat intro; simpl. by apply dotA. Qed.
 Next Obligation. repeat intro; simpl. by apply dotx1. Qed.
 Next Obligation. repeat intro; simpl. by apply cnvI. Qed.
 Next Obligation. repeat intro; simpl. by apply cnvpar. Qed.
 Next Obligation. repeat intro; simpl. by apply cnvdot. Qed.
 Next Obligation. repeat intro; simpl. by apply par11. Qed.
 Next Obligation. repeat intro; simpl. by apply A10. Qed.
 Next Obligation. repeat intro; simpl. by apply A13. Qed.
 Next Obligation. repeat intro; simpl. by apply A14. Qed.
 Canonical tm_pttdom. 
 
 Notation test := (test tm_pttdom).

 (* TOTHINK: might want to move normalisation to completeness related files *)
 
 (* normal forms for terms *)
 Inductive nterm :=
 | nt_test: test -> nterm
 | nt_conn: test -> term -> test -> nterm.

 Definition term_of_nterm (t: nterm) :=
   match t with
   | nt_test alpha => elem_of alpha (* why do we need to insert the coercion??? *)
   | nt_conn alpha u gamma => alpha · u · gamma
   end.                                         

 (* pttdom algebra on normal forms *)
 Definition nt_one := nt_test [1].
 Definition nt_var a := nt_conn [1] (tm_var a) [1].
 Definition nt_cnv u :=
   match u with
   | nt_test _ => u
   | nt_conn a u b => nt_conn b (u°) a
   end.
 Definition nt_dom u :=
   match u with
   | nt_test _ => u
   | nt_conn a u b => nt_test [a · dom (u·b)]
   end.
 Definition nt_dot u v :=
   match u,v with
   | nt_test a, nt_test b => nt_test [a·b]
   | nt_test a, nt_conn b u c => nt_conn [a·b] u c
   | nt_conn a u b, nt_test c => nt_conn a u [b·c]
   | nt_conn a u b, nt_conn c v d => nt_conn a (u·b·c·v) d
   end.
 Definition nt_par u v :=
   match u,v with
   | nt_test a, nt_test b => nt_test [a·b]
   | nt_test a, nt_conn b u c => nt_test [a ∥ b·u·c]
   | nt_conn a u b, nt_test c => nt_test [c ∥ a·u·b]
   | nt_conn a u b, nt_conn c v d => nt_conn [a·c] (u ∥ v) [b·d]
   end.

 (* normalisation function (could also be defined as an [eval])*)
 Fixpoint nt (u: term): nterm :=
   match u with
   | tm_dot u v => nt_dot (nt u) (nt v)
   | tm_par u v => nt_par (nt u) (nt v)
   | tm_cnv u => nt_cnv (nt u) 
   | tm_var a => nt_var a
   | tm_dom u => nt_dom (nt u)
   | tm_one => nt_one
   end.
 
 Proposition nt_correct (u: term): u ≡ term_of_nterm (nt u).
 Proof.
   induction u=>//=.
   - rewrite {1}IHu1 {1}IHu2.
     case (nt u1)=>[a|a u b];
     case (nt u2)=>[c|c v d]=>//=; 
     rewrite !dotA//.
   - rewrite {1}IHu1 {1}IHu2.
     case (nt u1)=>[a|a u b];
     case (nt u2)=>[c|c v d]=>//=.
     admit.                      (* ok *)
     apply parC.
     admit.                      (* ok *)
   - rewrite {1}IHu.
     case (nt u)=>[a|a v b]=>//=.
     admit.                      (* ok *)
     rewrite 2!cnvdot dotA.
     admit. (* ok *)
   - rewrite {1}IHu.
     case (nt u)=>[a|a v b]=>//=.
     admit.                      (* ok *)
     admit.                      (* ok *)
   - rewrite dotx1.
     admit.                      (* ok *)
 Qed.

End terms.
