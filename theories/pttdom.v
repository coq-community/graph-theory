Require Import Setoid Morphisms.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries setoid_bigop structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

(** * 2pdom algebra, tests, initial algebra of terms *)

(** ** 2pdom algebra (the top-free fragment of 2p algebra) *)

(** NOTE: we let Ops inherit from Setoid, to avoid having a
"criss-cross" inheritance pattern that is not (yet) supported by HB *)
HB.mixin Record Ops_of_Type A of Setoid_of_Type A :=
  { dot: A -> A -> A;
    par: A -> A -> A;
    cnv: A -> A;
    dom: A -> A;
    one: A;
    top: A;         (* top is left uninterpreted in 2pdom *)
  }.
HB.structure Definition Ops := { A of Ops_of_Type A & }.

Arguments one {_}: simpl never.
Arguments top {_}: simpl never.
Arguments dot: simpl never.
Arguments par: simpl never.
Arguments cnv: simpl never.
Arguments dom: simpl never.

Declare Scope pttdom_ops.
Bind Scope pttdom_ops with Ops.type.
Delimit Scope pttdom_ops with ptt.
Open Scope pttdom_ops.
Notation "x ∥ y" := (par x y) (left associativity, at level 40, format "x ∥ y"): pttdom_ops.
Notation "x · y" := (dot x y) (left associativity, at level 25, format "x · y"): pttdom_ops.
Notation "x °"  := (cnv x) (left associativity, at level 5, format "x °"): pttdom_ops.
Notation "1"  := (one): pttdom_ops.

(* 2pdom axioms *)

HB.mixin Record Pttdom_of_Ops A of Ops_of_Type A & Setoid_of_Type A := 
  { dot_eqv: Proper (eqv ==> eqv ==> eqv) (dot : A -> A -> A);
    par_eqv: Proper (eqv ==> eqv ==> eqv) (par : A -> A -> A);
    cnv_eqv: Proper (eqv ==> eqv) (cnv : A -> A);
    dom_eqv: Proper (eqv ==> eqv) (dom : A -> A);
    parA: forall x y z: A, x ∥ (y ∥ z) ≡ (x ∥ y) ∥ z;
    parC: forall x y: A, x ∥ y ≡ y ∥ x;
    dotA: forall x y z: A, x · (y · z) ≡ (x · y) · z;
    dotx1: forall x: A, x · 1 ≡ x;
    cnvI: forall x: A, x°° ≡ x;
    cnvpar: forall x y: A, (x ∥ y)° ≡ x° ∥ y°;
    cnvdot: forall x y: A, (x · y)° ≡ y° · x°;
    par11: (1 : A) ∥ 1 ≡ 1;
    A10: forall x y: A, 1 ∥ x·y ≡ dom (x ∥ y°);
    A13: forall x y: A, dom(x·y) ≡ dom(x·dom y);
    A14: forall x y z: A, dom x·(y∥z) ≡ dom x·y ∥ z;
  }.
HB.structure Definition Pttdom := { A of Pttdom_of_Ops A & }.
Notation pttdom := Pttdom.type.
Existing Instances dot_eqv par_eqv cnv_eqv dom_eqv.

Class is_test (X : pttdom) (x : X) := { testE : dom x ≡ x }.

(* Coercion ops_of (X : pttdom) (x : Pttdom.sort X) : Ops.sort X := x. *)
(* Coercion setoid_of (X : Ops) (x : Pttdom.sort X) : Setoid.sort X := x. *)

(** ** basic derivable laws  *)
Section derived.

 Variable X: pttdom.
 Implicit Types u v x y z: X.
 
 Lemma cnv1: 1° ≡ @one X.
 Proof. rewrite -[1°]dotx1 -{2}[1]cnvI. by rewrite -cnvdot dotx1 cnvI. Qed.

 Lemma dot1x x: 1·x ≡ x.
 Proof. by rewrite -[1·x]cnvI cnvdot cnv1 dotx1 cnvI. Qed.

 Lemma cnv_inj x y: x° ≡ y° -> x ≡ y.
 Proof. intro. rewrite <-(cnvI x), <-(cnvI y). by apply cnv_eqv. Qed.

 Lemma dotcnv x y: x·y ≡ (y°·x°)°.
 Proof. apply cnv_inj. by rewrite cnvdot cnvI. Qed.

 (** ** tests *)
 (* Definition is_test x := dom x ≡ x. *)
 Record test := Test{ elem_of :> X ; testP : is_test elem_of }.

 Global Instance test_test (a : test) : is_test (elem_of a).
 Proof. exact: testP. Qed.

 Implicit Types a b c d : X.
 
 Lemma is_test_alt x: dom x ≡ x <-> x∥1 ≡ x.
 Proof.
   split=>E.
   - rewrite -{1}E -{1}(dotx1 (dom x)) -A14.
     by rewrite par11 dotx1. 
   - by rewrite -E -{1}cnv1 -A10 dotx1 parC.
 Qed.

 Lemma domtst a of is_test a : dom a ≡ a. 
 Proof. exact: testE. Qed.

 Lemma tstpar1 a of is_test a :  a ∥ 1 ≡ a.
 Proof. by apply/is_test_alt; rewrite domtst. Qed.

 Lemma one_test: is_test (1:X). 
 Proof. constructor. by rewrite -{1}par11 -{2}cnv1 -A10 dotx1 par11. Qed.
 Global Existing Instance one_test.

 Lemma dom_test x: is_test (dom x). 
 Proof. constructor. by rewrite -{1}[dom x]dot1x -A13 dot1x. Qed.
 Global Existing Instance dom_test.
 
 Lemma par_test a u of is_test a : is_test (a∥u).
 Proof.
   constructor; apply/is_test_alt.
   by rewrite -parA (parC u) parA tstpar1. 
 Qed.
 Global Existing Instance par_test.

 Lemma cnvtst a of is_test a : a° ≡ a.
 Proof. 
   rewrite -[a]tstpar1 cnvpar cnv1 -(dot1x (a°)) parC A10 cnvI parC.
   apply: domtst.
 Qed.

 Lemma cnv_test a of is_test a : is_test (a°).
 Proof. constructor. by rewrite is_test_alt cnvtst tstpar1. Qed.
 Global Existing Instance cnv_test.

 Lemma tstpar a x y of is_test a : a·(x∥y) ≡ a·x ∥ y.
 Proof. rewrite -[a]domtst. apply A14. Qed.

 Lemma tstpar_r a x y of is_test a : a·(x∥y) ≡ x ∥ a·y.
 Proof. by rewrite parC tstpar parC. Qed.

 Lemma pardot a b of is_test a & is_test b : a ∥ b ≡ a·b.
 Proof.
   by rewrite -{2}(@tstpar1 b) (parC _ 1) tstpar dotx1.
 Qed.
 
 Lemma dotC a b of is_test a & is_test b : a·b ≡ b·a.
 Proof. by rewrite -pardot parC pardot. Qed.

 Lemma dot_test a b of is_test a & is_test b : is_test (a·b).
 Proof. constructor. rewrite -pardot. apply: domtst. Qed.
 Global Existing Instance dot_test.
 
 (* (** automatised inference of tests *) *)
 (* Definition infer_test x b (e: elem_of b = x) := b. *)
 (* Notation "[ x ]" := (@infer_test x _ erefl). *)
 Notation "[ x ]" := (@Test x _).

 (** ** commutative monoid of  tests *)
 Definition eqv_test (a b : test) := elem_of a ≡ elem_of b.
 Arguments eqv_test _ _ /.
 Lemma eqv_test_equiv: Equivalence eqv_test. 
 Proof. 
   split => [x|x y|x y z]; rewrite /eqv_test /=.
   reflexivity. by symmetry. by transitivity (elem_of y).
 Qed.
 HB.instance Definition pttdom_test_setoid := 
   Setoid_of_Type.Build test eqv_test_equiv.

 Lemma infer_testE a of is_test a : elem_of [a] ≡ a. 
 Proof. by []. Qed.
 Lemma eqv_testE a b of is_test a & is_test b : [a] ≡ [b] <-> a ≡ b.
 Proof. by []. Qed.

 Section M.
 Definition tst_dot (a b : test) : test := [elem_of a · elem_of b].
 Local Infix "·" := tst_dot.

 Lemma tst_dot_eqv: Proper (eqv ==> eqv ==> eqv) tst_dot.
 Proof. intros [a] [b] ? [c] [d] ?. by apply dot_eqv. Qed.
 Lemma tst_dotA: forall a b c : test, a·(b·c) ≡ (a·b)·c.
 Proof. intros [a] [b] [c]. apply dotA. Qed.
 Lemma tst_dotC: forall a b : test, a·b ≡ b·a.
 Proof. intros. by rewrite /tst_dot eqv_testE -pardot parC pardot. Qed.
 Lemma tst_dotU: forall a : test , a·[1] ≡ a.
 Proof. intros [a]. apply dotx1. Qed.

 Definition pttdom_monoid_laws := 
   mkComMonoidLaws tst_dot_eqv tst_dotA tst_dotC tst_dotU.
 HB.instance Definition pttdom_monoid := 
   ComMonoid_of_Setoid.Build test pttdom_monoid_laws.
 End M.


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

 HB.instance Definition pttdom_elabel := 
   Elabel_of_Setoid.Build (Pttdom.sort X) eqv'_sym eqv01 eqv11.
 
 (* Lemmas to turn pttdom expressions into (projections of) tests *)
 Lemma par1tst u : 1 ∥ u = elem_of [1∥u]. by []. Qed.
 Lemma paratst (a : test) u : elem_of a ∥ u = elem_of [elem_of a∥u]. by []. Qed.
 Lemma dom_tst u : dom u = elem_of [dom u]. by []. Qed.
 
 (* this allows rewriting an equivalence between tests inside a pttdom expression *)
 Lemma rwT (a b: test) : a ≡ b -> elem_of a ≡ elem_of b. by []. Qed.
 
 (** ** other derivable laws used in the completeness proof *)
 
 Lemma partst u v a of is_test a : (u ∥ v)·a ≡ u ∥ v·a.
 Proof.
   apply cnv_inj. rewrite cnvdot 2!cnvpar cnvdot.
   by rewrite parC tstpar parC.
 Qed.
 
 Lemma par_tst_cnv a u of is_test a : a ∥ u° ≡ a ∥ u.
 Proof. by rewrite -[a∥u°]cnvtst cnvpar cnvtst cnvI. Qed.
 
 Lemma eqvb_par1 a u v (b : bool) of is_test a : u ≡[b] v -> a ∥ u ≡ a ∥ v.
 Proof. case: b => [->|-> //]. exact: par_tst_cnv. Qed.
 
 (* used twice in reduce in reduction.v *)
 Lemma reduce_shuffle v a c d of is_test a & is_test c & is_test d :
   c·(d·a)·(1∥v) ≡ a ∥ c·v·d.
 Proof.
   rewrite -!dotA -tstpar_r; apply: dot_eqv => //.
   by rewrite -partst tstpar dotx1 dotC.
 Qed.
 
 (* lemma for nt_correct *)
 Lemma par_nontest u v a b c d of is_test a & is_test b & is_test c & is_test d :
   a·u·b∥c·v·d ≡ (a·c)·(u∥v)·(b·d).
 Proof. by rewrite -partst -[a·u·b]dotA -tstpar parC -tstpar -partst !dotA parC. Qed.
 
 
 (* used in open.v *)
 Lemma eqvbN u v : u ≡[false] v -> u ≡ v. by []. Qed.
 Lemma eqvbT u v : u ≡[true] v -> u ≡ v°. by []. Qed.

 Arguments Elabel.Exports.eqv' _ _ _ /.
 
 Lemma eqvb_neq u v (b : bool) : u ≡[~~b] v <-> u ≡[b] v°.
 Proof. by split; apply: eqvb_transL; rewrite ?(addbN,addNb) addbb //= ?cnvI. Qed.
 
End derived.
(* Coercion pttdom_labels: pttdom >-> labels.  *)

 Notation "[ x ]" := (@Test _ x _).

(* Notation "[ x ]" := (@infer_test _ x%ptt _ erefl): pttdom_ops. *)

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
 Variable (X: Ops.type) (f: A -> X).
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
 HB.instance Definition tm_setoid := Setoid_of_Type.Build term tm_eqv_equivalence.
 
 HB.instance Definition tm_ops := Ops_of_Type.Build term tm_dot tm_par tm_cnv tm_dom tm_one tm_one.

 (* Arguments eqv { _ } _ _ / . *)

 Lemma tm_eqv_eqv (u v: term) (X: pttdom) (f: A -> X) :
   u ≡ v -> eval f u ≡ eval f v. 
 Proof. exact. Qed.

 Definition tm_pttdom : Pttdom_of_Ops.axioms_ tm_setoid tm_ops.
 Proof.
   refine (Pttdom_of_Ops.Build term _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
   abstract (by repeat intro; simpl; apply dot_eqv; apply: tm_eqv_eqv).
   abstract (by repeat intro; simpl; apply par_eqv; apply: tm_eqv_eqv).
   abstract (by repeat intro; simpl; apply cnv_eqv; apply: tm_eqv_eqv).
   abstract (by repeat intro; simpl; apply dom_eqv; apply: tm_eqv_eqv).
   abstract (by repeat intro; simpl; apply parA; apply: tm_eqv_eqv).
   abstract (by repeat intro; simpl; apply parC; apply: tm_eqv_eqv).
   abstract (by repeat intro; simpl; apply dotA; apply: tm_eqv_eqv).
   abstract (by repeat intro; simpl; apply dotx1; apply: tm_eqv_eqv).
   abstract (by repeat intro; simpl; apply cnvI; apply: tm_eqv_eqv).
   abstract (by repeat intro; simpl; apply cnvpar; apply: tm_eqv_eqv).
   abstract (by repeat intro; simpl; apply cnvdot; apply: tm_eqv_eqv).
   abstract (by repeat intro; simpl; apply par11; apply: tm_eqv_eqv).
   abstract (by repeat intro; simpl; apply A10; apply: tm_eqv_eqv).
   abstract (by repeat intro; simpl; apply A13; apply: tm_eqv_eqv).
   abstract (by repeat intro; simpl; apply A14; apply: tm_eqv_eqv).
 Defined.
 HB.instance term tm_pttdom.
 HB.instance term (pttdom_elabel term_is_a_Pttdom).

 Notation test := (test term_is_a_Pttdom).
 
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
   | nt_conn alpha u gamma => elem_of alpha · u · elem_of gamma
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
   | nt_conn a u b => nt_test [elem_of a · dom (u·elem_of b)]
   end.
 Definition nt_dot u v :=
   match u,v with
   | nt_test a, nt_test b => nt_test [elem_of a·elem_of b]
   | nt_test a, nt_conn b u c => nt_conn [elem_of a·elem_of b] u c
   | nt_conn a u b, nt_test c => nt_conn a u [elem_of b·elem_of c]
   | nt_conn a u b, nt_conn c v d => nt_conn a (u·elem_of b·elem_of c·v) d
   end.
 Definition nt_par u v :=
   match u,v with
   | nt_test a, nt_test b => nt_test [elem_of a·elem_of b]
   | nt_test a, nt_conn b u c => nt_test [elem_of a ∥ elem_of b·u·elem_of c]
   | nt_conn a u b, nt_test c => nt_test [elem_of c ∥ elem_of a·u·elem_of b]
   | nt_conn a u b, nt_conn c v d => nt_conn [elem_of a·elem_of c] (u ∥ v) [elem_of b·elem_of d]
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

 (** Induction on terms exposes [tm_*] constructors. The [fold_ops]
 tactic recovers the notations for the term algebra *)
 Ltac fold_ops := 
   repeat match goal with 
          | |- context[tm_par ?u ?v] => change (tm_par u v) with (u ∥ v) 
          | |- context[tm_dot ?u ?v] => change (tm_dot u v) with (u · v)
          | |- context[tm_cnv ?u] => change (tm_cnv u) with (u°)
          | |- context[tm_dom ?u] => change (tm_dom u) with (dom u)
          | |- context[tm_one ?A] => change (tm_one A) with (@one term_is_a_Ops)
          | |- tm_eqv ?u ?v => change (u ≡ v)
         end.


 (* correctness of the normalisation function (Proposition 7.1)  *)
 Proposition nt_correct (u: term): u ≡ term_of_nterm (nt u).
 Proof.
   induction u=>//=; fold_ops.
   - (* rewrite {1}IHu1 {1}IHu2. - coq 8.12 regression *)
     rewrite (dot_eqv _ _ IHu1 _ _ IHu2).
     case (nt u1) =>[a|a u b];
     case (nt u2)=>[c|c v d] //=;
     rewrite !dotA//.
   - (* rewrite {1}IHu1 {1}IHu2. *)
     rewrite (par_eqv _ _ IHu1 _ _ IHu2).
     case (nt u1)=>[a|a u b];
     case (nt u2)=>[c|c v d]=>//=.
     exact: pardot.
     apply: parC. 
     exact: par_nontest.
   - rewrite {1}IHu.
     case (nt u)=>[a|a v b]=>//=.
     exact: cnvtst.
     by rewrite 2!cnvdot dotA !cnvtst.
   - rewrite {1}IHu.
     case (nt u)=>[a|a v b]=>//=.
     exact: domtst.
     by rewrite -dotA A13 domtst.
   - by rewrite dotx1 dot1x.
 Qed.

End terms.
