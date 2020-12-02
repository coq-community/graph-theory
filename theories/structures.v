Require Import RelationClasses Morphisms Relation_Definitions.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries setoid_bigop bij.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Setoids and Label Structures *)

(* Note on Equivalences and Morphisms: This development mixes both
rewriting in Prop (e.g., 2pdom algebras) and rewriting in Type (e.g.,
iso). To facilitate this, we import the Prop versions and introduce
notations for the Type versions. This leads to the follwing usage
patterns: 

- Morphisms and Relation classes should be imported as needed.
- CMorhisms and CRelationClasses should be Required but never imported.
- There are notations CEquivalence and CProper that refer to the Type versions.
- The "_ ==> ..." argumentof CProper is parsed using the respectful from CMorphisms.
*)

Notation CEquivalence := CRelationClasses.Equivalence.
Notation CProper := CMorphisms.Proper.
Declare Scope csignature.
Delimit Scope csignature with C.
Notation "A ==> B" := (@CMorphisms.respectful _ _ (A%C) (B%C)) : csignature.
Arguments CMorphisms.Proper [A] _%C _.

Section CProper.
Variables A B C: Type.
Notation i R := (fun x y => inhabited (R x y)). 
Variable R: A -> A -> Type.
Variable S: B -> B -> Type.
Variable T: C -> C -> Type.
Variable f: A -> B.
Hypothesis Hf: CProper (R ==> S) f.
Lemma CProper1: Proper (i R ==> i S) f.
Proof. intros x y [H]. exists. by apply Hf. Qed.
Variable g: A -> B -> C.
Hypothesis Hg: CProper (R ==> S ==> T) g.
Lemma CProper2: Proper (i R ==> i S ==> i T) g.
Proof. intros x y [E] u v [F]. exists. by apply Hg. Qed.
End CProper.


(** ** label structures (Definition 4.1) *)

(** The original label structure (comment has been split into a commutative monoid (for
the vertex labels) and an "elabel Type" (accounting for possible edge-flipping)
for edge labels. *)

(*
Record labels :=
  Labels {
      lv: setoid;
      mon0: lv;
      mon2: lv -> lv -> lv;
      lv_monoid: comMonoidLaws mon0 mon2;
      le: setoid;
      eqv': relation le;
      Eqv'_sym: Symmetric eqv';
      eqv01: forall x y z, eqv  x y -> eqv' y z -> eqv' x z;
      eqv11: forall x y z, eqv' x y -> eqv' y z -> eqv  x z;
    }.
Global Existing Instance lv_monoid. 
*)

HB.mixin Record ComMonoid_of_Setoid A of Setoid_of_Type A := 
  { cm_id : A;
    cm_op : A -> A -> A;
    cm_laws : comMonoidLaws cm_id cm_op }.
HB.structure Definition ComMonoid := { A of ComMonoid_of_Setoid A & }.
Notation comMonoid := ComMonoid.type.

Existing Instance cm_laws.
Arguments cm_op {_} _ _.
Declare Scope cm_scope.
Delimit Scope cm_scope with CM.
Infix "⊗" := cm_op (left associativity, at level 25) : cm_scope.
Arguments cm_id {_}.
Notation "1" := cm_id : cm_scope.

(** ingredients required to label graphs
    - eqv' x y = eqv x y° (when we have an involution _°)
   - eqv' _ _ = False    (otherwise) *)

HB.mixin Record Elabel_of_Setoid A of Setoid_of_Type A := 
  { eqv': Relation_Definitions.relation A;
    Eqv'_sym: Symmetric eqv';
    eqv01: forall x y z : A, eqv  x y -> eqv' y z -> eqv' x z;
    eqv11: forall x y z : A, eqv' x y -> eqv' y z -> eqv  x z }.
HB.structure Definition Elabel := { A of Elabel_of_Setoid A & }.
Notation elabelType := Elabel.type.
Infix "≡'" := eqv' (at level 79).

Lemma eqv10 (l : elabelType) (x y z : l) : eqv' x y -> eqv  y z -> eqv' x z.
Proof. move => /Eqv'_sym A B. apply: Eqv'_sym. apply: eqv01 A. by symmetry. Qed.

(* switch between [≡] and [≡'] based on a Boolean 
   (useful for defining potentially edge swapping homomorphisms) *)
Definition eqv_ (X: elabelType) (b: bool) (x y: X) := if b then x ≡' y else x ≡ y.
Notation "x ≡[ b ] y" := (eqv_ b x y) (at level 79).
Global Instance eqv_sym {X: elabelType} {b}: Symmetric (@eqv_ X b).
Proof. case b=> x y/=. apply Eqv'_sym. by symmetry. Qed.

Lemma eqvb_trans (X : elabelType) (u v w : X) (b1 b2 : bool) : 
  u ≡[b1] v -> v ≡[b2] w -> u ≡[b1 (+) b2] w.
Proof. 
  case: b1; case: b2 => /=; try solve [exact: eqv01|exact: eqv11|exact: eqv10].
  by transitivity v.
Qed.

(* variants of the above that are more useful for backward chaining *)
Lemma eqvb_transR (X : elabelType) b b' (u v v' : X) : 
  u ≡[b (+) b'] v' ->  v' ≡[b'] v ->  u ≡[b] v.
Proof. move => A B. move:(eqvb_trans A B). by rewrite -addbA addbb addbF. Qed.

Lemma eqvb_transL (X : elabelType) b b' (u u' v : X) : 
  u' ≡[b (+) b'] v ->  u ≡[b'] u' ->  u ≡[b] v.
Proof. move => A B. move:(eqvb_trans B A). by rewrite addbC -addbA addbb addbF. Qed.

Global Instance eqv_morphim (X: elabelType) : 
  Proper (eq ==> eqv ==> eqv ==> iff) (@eqv_ X).
Proof. 
  move => b ? <- x x' xx y y' yy. 
  change (x ≡[false] x') in xx. change (y ≡[false] y') in yy. split => H. 
  - symmetry in xx. apply: eqvb_transR yy. apply: eqvb_transL xx. by rewrite !addbF.
  - symmetry in yy. apply: eqvb_transR yy. apply: eqvb_transL xx. by rewrite !addbF.
Qed.

Lemma eq_unit (a b: unit): a = b.
Proof. by case a; case b. Qed.
Hint Resolve eq_unit: core.

Lemma big_bij_eq (T : comMonoid) (I1 I2 : finType) (F : I1 -> T) (f : bij I1 I2) (y : I2) :
  \big[cm_op/1%CM]_(x | f x == y) F x ≡ F (f^-1 y).
Proof. apply: big_pred1 => x /=. exact: bij_eqLR. Qed.

(* TOTHINK: this is necessary because f^-1 is a bijective function and not a bijection ... *)
Lemma big_bij_eq' (T : comMonoid) (I1 I2 : finType) (F : I1 -> T) (f : bij I2 I1) (y : I2) :
  \big[cm_op/1%CM]_(x | f^-1 x == y) F x ≡ F (f y).
Proof. apply: big_pred1 => x /=. by rewrite eq_sym -bij_eqLR eq_sym. Qed.

(** ** Structure Inference *)

(** On [unit], [eq] is the only equivalence relation. Hence, we can
safely register [unit_setoid] as the canonical setoid for unit *)

Lemma unit_commMonoidLaws : comMonoidLaws tt (fun _ _ => tt).
Proof. by do 2 (split; try done). Qed.

HB.instance Definition unit_commMonoid := 
  ComMonoid_of_Setoid.Build unit unit_commMonoidLaws.

(** Any type can be endowed with a flat edge-label structure over the
equality setoid. However, we cannot declare this canonical for
arbitrary types, because this would take precedence over all other
setoids. Instead, we introduce an alias [flat] and equip it with a
flat edge-label structure. Note that [flat A] is convertible to [A] *)

Section E.
Variable (A : Type).
Let rel := (fun _ _ : A  => False).
Let rel_sym : Symmetric rel. by []. Qed.
Let rel01 (x y z : A) : x = y -> rel y z -> rel x z. by []. Qed.
Let rel11 (x y z : A) : rel x y -> rel y z -> x = z. by []. Qed.

HB.instance Definition flat_elabel_mixin :=
  @Elabel_of_Setoid.Build (flat A) rel rel_sym rel01 rel11.
End E.
