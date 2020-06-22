Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries setoid_bigop structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

(** * 2pdom algebra, tests, initial algebra of terms *)

(** ** 2pdom algebra (the top-free fragment of 2p algebra) *)

(* operations are put apart so that the can get notations for them before stating/proving the laws  *)
Structure ops_ :=
  { setoid_of_ops:> setoid;
    dot: setoid_of_ops -> setoid_of_ops -> setoid_of_ops;
    par: setoid_of_ops -> setoid_of_ops -> setoid_of_ops;
    cnv: setoid_of_ops -> setoid_of_ops;
    dom: setoid_of_ops -> setoid_of_ops;
    one: setoid_of_ops;
    top: setoid_of_ops;         (* top is left uninterpreted in 2pdom *)
  }.
Arguments one {_}: simpl never.
Arguments top {_}: simpl never.
Arguments dot: simpl never.
Arguments par: simpl never.
Arguments cnv: simpl never.
Arguments dom: simpl never.

Declare Scope pttdom_ops.
Bind Scope pttdom_ops with setoid_of_ops.
Delimit Scope pttdom_ops with ptt.
Open Scope pttdom_ops.
Notation "x ∥ y" := (par x y) (left associativity, at level 40, format "x ∥ y"): pttdom_ops.
Notation "x · y" := (dot x y) (left associativity, at level 25, format "x · y"): pttdom_ops.
Notation "x °"  := (cnv x) (left associativity, at level 5, format "x °"): pttdom_ops.
Notation "1"  := (one): pttdom_ops.

(* 2pdom axioms *)
Structure pttdom :=
  { ops:> ops_;
    dot_eqv: Proper (eqv ==> eqv ==> eqv) (@dot ops);
    par_eqv: Proper (eqv ==> eqv ==> eqv) (@par ops);
    cnv_eqv: Proper (eqv ==> eqv) (@cnv ops);
    dom_eqv: Proper (eqv ==> eqv) (@dom ops);
    parA: forall x y z: ops, x ∥ (y ∥ z) ≡ (x ∥ y) ∥ z;
    parC: forall x y: ops, x ∥ y ≡ y ∥ x;
    dotA: forall x y z: ops, x · (y · z) ≡ (x · y) · z;
    dotx1: forall x: ops, x · 1 ≡ x;
    cnvI: forall x: ops, x°° ≡ x;
    cnvpar: forall x y: ops, (x ∥ y)° ≡ x° ∥ y°;
    cnvdot: forall x y: ops, (x · y)° ≡ y° · x°;
    par11: 1 ∥ 1 ≡ @one ops;
    A10: forall x y: ops, 1 ∥ x·y ≡ dom (x ∥ y°);
    A13: forall x y: ops, dom(x·y) ≡ dom(x·dom y);
    A14: forall x y z: ops, dom x·(y∥z) ≡ dom x·y ∥ z;
  }.
Existing Instances dot_eqv par_eqv cnv_eqv dom_eqv.

(** ** basic derivable laws  *)
Section derived.

 Variable X: pttdom.
 Implicit Types u v x y z: X.
 
 Lemma cnv1: 1° ≡ @one X.
 Proof.
  rewrite <-dotx1. rewrite <-(cnvI 1) at 2.
  by rewrite <-cnvdot, dotx1, cnvI.
 Qed.

 Lemma dot1x x: 1·x ≡ x.
 Proof. by rewrite <-cnvI, cnvdot, cnv1, dotx1, cnvI. Qed.

 Lemma cnv_inj x y: x° ≡ y° -> x ≡ y.
 Proof. intro. rewrite <-(cnvI x), <-(cnvI y). by apply cnv_eqv. Qed.

 Lemma dotcnv x y: x·y ≡ (y°·x°)°.
 Proof. apply cnv_inj. by rewrite cnvdot cnvI. Qed.

 (** ** tests *)
 Definition is_test x := dom x ≡ x.
 Record test := Test{ elem_of:> X ; testE: is_test elem_of }.

 Implicit Types a b c d: test.
 
 Lemma is_test_alt x: dom x ≡ x <-> x∥1 ≡ x.
 Proof.
   split=>E.
   - rewrite -{1}E -{1}(dotx1 (dom x)) -A14.
     by rewrite par11 dotx1. 
   - by rewrite -E -{1}cnv1 -A10 dotx1 parC.
 Qed.
 
 Lemma domtst a: dom a ≡ a. 
 Proof. apply testE. Qed.
 
 Lemma tstpar1 a: a ∥ 1 ≡ a.
 Proof. apply is_test_alt, domtst. Qed.

 Lemma one_test: is_test 1. 
 Proof. rewrite /is_test. by rewrite -{1}par11 -{2}cnv1 -A10 dotx1 par11. Qed.
 Canonical Structure tst_one := Test one_test. 

 Lemma dom_test x: is_test (dom x). 
 Proof. rewrite /is_test. by rewrite -{1}[dom x]dot1x -A13 dot1x. Qed.
 Canonical Structure tst_dom x := Test (dom_test x).
 
 Lemma par_test a u: is_test (a∥u).
 Proof.
   rewrite /is_test is_test_alt.
   by rewrite -parA (parC u) parA tstpar1. 
 Qed.
 Canonical Structure tst_par a u := Test (par_test a u).

 Lemma cnvtst a: a° ≡ a.
 Proof.
   rewrite -tstpar1 cnvpar cnv1 -(dot1x (a°)) parC A10 cnvI parC.
   apply domtst.
 Qed.

 Lemma cnv_test a: is_test (a°).
 Proof.
   by rewrite /is_test is_test_alt cnvtst tstpar1. 
 Qed.
 Canonical Structure tst_cnv a := Test (cnv_test a).

 Lemma tstpar a x y: a·(x∥y) ≡ a·x ∥ y.
 Proof. rewrite -domtst. apply A14. Qed.

 Lemma pardot a b: a ∥ b ≡ a·b.
 Proof.
   by rewrite -{2}(tstpar1 b) (parC _ 1) tstpar dotx1.
 Qed.
 
 Lemma dot_test a b: is_test (a·b).
 Proof. rewrite /is_test -pardot. apply domtst. Qed.
 Canonical Structure tst_dot a b := Test (dot_test a b).
 
 (** automatised inference of tests *)
 Definition infer_test x b (e: elem_of b = x) := b.
 Notation "[ x ]" := (@infer_test x _ erefl).

 (** ** commutative monoid of  tests *)
 Definition eqv_test a b := a ≡ b.
 Arguments eqv_test _ _ /.
 Lemma eqv_test_equiv: Equivalence eqv_test. 
 Proof. 
   split => [x|x y|x y z]; rewrite /eqv_test /=.
   reflexivity. by symmetry. by transitivity (elem_of y).
 Qed.
 Canonical Structure pttdom_test_setoid := Setoid eqv_test_equiv.
 Lemma tst_dot_eqv: Proper (eqv ==> eqv ==> eqv) tst_dot.
 Proof. intros [a] [b] ? [c] [d] ?. by apply dot_eqv. Qed.
 Lemma tst_dotA: forall a b c, a·(b·c) ≡ (a·b)·c.
 Proof. intros [a] [b] [c]. apply dotA. Qed.
 Lemma tst_dotC: forall a b, a·b ≡ b·a.
 Proof. intros. rewrite -2!pardot. apply parC. Qed.
 Lemma tst_dotU: forall a, a·1 ≡ a.
 Proof. intros [a]. apply dotx1. Qed.

 (** ** label structure of a 2pdom algebra (Definition 4.3)  *)
 
 (* dualised equality (to get the [labels] structure below) *)
 Definition eqv' x y := x ≡ y°.
 Arguments eqv' _ _ /.
 Lemma eqv'_sym: Symmetric eqv'.
 Proof. move=> x y /= H. apply cnv_inj. by rewrite cnvI H. Qed.
 Lemma eqv01 x y z: x ≡ y -> eqv' y z -> eqv' x z.
 Proof. by move=> /= ->. Qed.
 Lemma eqv11 x y z: eqv' x y -> eqv' y z -> x ≡ z.
 Proof. move=> /= -> ->. apply cnvI. Qed.
 
 Canonical Structure pttdom_labels: labels :=
   Labels
     (mkComMonoidLaws tst_dot_eqv tst_dotA tst_dotC tst_dotU)
     eqv'_sym eqv01 eqv11.
 
 (* Lemmas to turn pttdom expressions into (projections of) tests *)
 Lemma par1tst u : 1 ∥ u = [1∥u]. by []. Qed.
 Lemma paratst a u : a ∥ u = [a∥u]. by []. Qed.
 Lemma dom_tst u : dom u = [dom u]. by []. Qed.
 
 (* this allows rewriting an equivalence between tests inside a pttdom expression *)
 Lemma rwT a b: a ≡ b -> elem_of a ≡ elem_of b. by []. Qed.
 
 (** ** other derivable laws used in the completeness proof *)
 
 Lemma partst u v a : (u ∥ v)·a ≡ u ∥ v·a.
 Proof.
   apply cnv_inj. rewrite cnvdot 2!cnvpar cnvdot.
   by rewrite parC tstpar parC.
 Qed.
 
 Lemma par_tst_cnv a u : a ∥ u° ≡ a ∥ u.
 Proof. by rewrite paratst -(@cnvtst [a∥u]) /= cnvpar cnvtst. Qed.
 
 Lemma eqvb_par1 a u v (b : bool) : u ≡[b] v -> a ∥ u ≡ a ∥ v.
 Proof. case: b => [->|-> //]. exact: par_tst_cnv. Qed.
 
 (* used twice in reduce in reduction.v *)
 Lemma reduce_shuffle v a c d : c·(d·a)·[1∥v] ≡ a ∥ c·v·d.
 Proof. 
   rewrite [c·(d·a)]dotA -dotA tstpar dotx1.
   by rewrite -dotA (paratst a v) tst_dotC /= partst parC tstpar parC dotA.
 Qed.
 
 (* lemma for nt_correct *)
 Lemma par_nontest u v a b c d : a·u·b∥c·v·d ≡ a·c·(u∥v)·(b·d).
 Proof. by rewrite -partst -[a·u·b]dotA -tstpar parC -tstpar -partst !dotA parC. Qed.
 
 
 (* used in open.v *)
 Lemma eqvbN u v : u ≡[false] v -> u ≡ v. by []. Qed.
 Lemma eqvbT u v : u ≡[true] v -> u ≡ v°. by []. Qed.
 
 Lemma eqvb_neq u v (b : bool) : u ≡[~~b] v <-> u ≡[b] v°.
 Proof. split; apply: eqvb_transL; by rewrite ?(addbN,addNb) addbb //= cnvI. Qed.
 
 Lemma infer_testE x x' a a' p p' : 
   (@infer_test x a p) ≡ (@infer_test x' a' p') <-> x ≡ x'.
 Proof. rewrite /infer_test. by subst. Qed.

End derived.
Coercion pttdom_labels: pttdom >-> labels. 
Notation "[ x ]" := (@infer_test _ x%ptt _ erefl): pttdom_ops.

(** ** initial algebra of terms *)
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

 (* axiomatic equality on terms *)
 (* (via impredicative encoding to avoid repeating the axioms in an inductive definition)) *)
 Definition tm_eqv (u v: term): Prop :=
   forall (X: pttdom) (f: A -> X), eval f u ≡ eval f v.
(* Do we really want this hint? *)
 Hint Unfold tm_eqv : core. 
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
      top := tm_one;            (* not a typo: top is not used in 2pdom *)
   |}.
 
 (* quotiented terms indeed form a 2pdom algebra *)
 Definition tm_pttdom: pttdom.
  refine (@Build_pttdom tm_ops_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    abstract (repeat intro; simpl; by apply dot_eqv).
    abstract (repeat intro; simpl; by apply par_eqv).
    abstract (repeat intro; simpl; by apply cnv_eqv).
    abstract (repeat intro; simpl; by apply dom_eqv).
    abstract (repeat intro; simpl; by apply parA).
    abstract (repeat intro; simpl; by apply parC).
    abstract (repeat intro; simpl; by apply dotA).
    abstract (repeat intro; simpl; by apply dotx1).
    abstract (repeat intro; simpl; by apply cnvI).
    abstract (repeat intro; simpl; by apply cnvpar).
    abstract (repeat intro; simpl; by apply cnvdot).
    abstract (repeat intro; simpl; by apply par11).
    abstract (repeat intro; simpl; by apply A10).
    abstract (repeat intro; simpl; by apply A13).
    abstract (repeat intro; simpl; by apply A14).
 Defined.
 Canonical tm_pttdom. 
 
 Notation test := (test tm_pttdom).
 
 (** ** normal terms and normalisation function (Section 7)*)

 (* TOTHINK: might want to move normalisation to completeness related files
    also, the normal terms construction actually works in an arbitrary pttdom *)

 (* normal terms *)
 Inductive nterm :=
 | nt_test: test -> nterm
 | nt_conn: test -> term -> test -> nterm.

 (* reading back terms *)
 Definition term_of_nterm (t: nterm) :=
   match t with
   | nt_test alpha => elem_of alpha (* why do we need to insert the coercion??? *)
   | nt_conn alpha u gamma => alpha · u · gamma
   end.                                         

 (* pttdom algebra on normal terms *)
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

 (* normalisation function (Definition 7.1) *)
 (* TODO: define it as an [eval]) *)
 Fixpoint nt (u: term): nterm :=
   match u with
   | tm_dot u v => nt_dot (nt u) (nt v)
   | tm_par u v => nt_par (nt u) (nt v)
   | tm_cnv u => nt_cnv (nt u) 
   | tm_var a => nt_var a
   | tm_dom u => nt_dom (nt u)
   | tm_one => nt_one
   end.

 (* correctness of the normalisation function (Proposition 7.1)  *)
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
     exact: pardot.
     apply parC. 
     exact: par_nontest.
   - rewrite {1}IHu.
     case (nt u)=>[a|a v b]=>//=.
     exact: cnvtst.
     by rewrite 2!cnvdot dotA !cnvtst.
   - rewrite {1}IHu.
     case (nt u)=>[a|a v b]=>//=.
     exact: domtst.
     by rewrite -dotA A13 (dom_tst (v·b)) domtst.
   - by rewrite dotx1 dot1x.
 Qed.

End terms.


(* unused for now
Ltac fold_ops := 
  repeat match goal with 
         | |- context[tm_par ?u ?v] => change (tm_par u v) with (u ∥ v) 
         | |- context[tm_dot ?u ?v] => change (tm_dot u v) with (u · v)
         | |- context[tm_cnv ?u] => change (tm_cnv u) with (u°)
         | |- context[tm_dom ?u] => change (tm_dom u) with (dom u)
         | |- context[tm_one ?A] => change (tm_one A) with (@one (tm_ops_ A))
         | |- tm_eqv ?u ?v => change (u ≡ v)
         end.
 *)
