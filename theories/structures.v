Require Import RelationClasses Morphisms Relation_Definitions.
From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries setoid_bigop.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Setoids and Label Structures *)


(*  
TODO: packed classes? (does not seem to be problematic for now)
but we should at least understand the current hack in rewriting.v for setoid_of_bisetoid
*)


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

(*

(** ** label structures (Definition 4.1) *)
(* ingredients required to label graphs
   - eqv' x y = eqv x y° (when we have an involution _°)
   - eqv' _ _ = False    (otherwise)
 *)

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
Arguments mon0 {_}: simpl never.
Arguments mon2 {_}: simpl never.
Arguments eqv' {_}.
Infix "≡'" := eqv' (at level 79).

Lemma eqv10 (l : labels) (x y z : le l) : eqv' x y -> eqv  y z -> eqv' x z.
Proof. move => /Eqv'_sym A B. apply: Eqv'_sym. apply: eqv01 A. by symmetry. Qed.

(* switch between [≡] and [≡'] based on a Boolean (useful for defining potentially edge swapping homomorphisms) *)
Definition eqv_ (X: labels) (b: bool) (x y: le X) := if b then x ≡' y else x ≡ y.
Notation "x ≡[ b ] y" := (eqv_ b x y) (at level 79).
Global Instance eqv_sym {X: labels} {b}: Symmetric (@eqv_ X b).
Proof. case b=> x y/=. apply Eqv'_sym. by symmetry. Qed.

Lemma eqvb_trans (X : labels) (u v w : le X) (b1 b2 : bool) : 
  u ≡[b1] v -> v ≡[b2] w -> u ≡[b1 (+) b2] w.
Proof. 
  case: b1; case: b2 => //=; eauto using eqv10, eqv01, eqv11. 
  by transitivity v.
Qed.

(* variants of the above that are more useful for backward chaining *)
Lemma eqvb_transR (X : labels) b b' (u v v' : le X) : 
  u ≡[b (+) b'] v' ->  v' ≡[b'] v ->  u ≡[b] v.
Proof. move => A B. move:(eqvb_trans A B). by rewrite -addbA addbb addbF. Qed.

Lemma eqvb_transL (X : labels) b b' (u u' v : le X) : 
  u' ≡[b (+) b'] v ->  u ≡[b'] u' ->  u ≡[b] v.
Proof. move => A B. move:(eqvb_trans B A). by rewrite addbC -addbA addbb addbF. Qed.

Global Instance eqv_morphim (X: labels) : 
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

(* label structure for letter-labeled graphs (Definition 4.2) *)
Definition flat_labels (X: Type): labels.
  refine (@Labels (eq_setoid unit) tt (fun _ _ => tt) _ (eq_setoid X) (fun _ _ => False) _ _ _).
  abstract by repeat split.
  all: abstract by []. 
Defined.
*)

Record comMonoid := 
  ComMonoid { cm_car :> setoid ;
              cm_id : cm_car;
              cm_op : cm_car -> cm_car -> cm_car;
              cm_laws : comMonoidLaws cm_id cm_op }.

Existing Instance cm_laws.

Arguments cm_op {_} _ _.
Declare Scope cm_scope.
Delimit Scope cm_scope with CM.
Infix "⊗" := cm_op (left associativity, at level 25) : cm_scope.
Arguments cm_id {_}.
Notation "1" := cm_id : cm_scope.

Record elabelType :=
  ElabelType { el_car :> setoid ;
               eqv': Relation_Definitions.relation el_car;
               Eqv'_sym: Symmetric eqv';
               eqv01: forall x y z, eqv  x y -> eqv' y z -> eqv' x z;
               eqv11: forall x y z, eqv' x y -> eqv' y z -> eqv  x z }.

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
  case: b1; case: b2 => //=; eauto using eqv10, eqv01, eqv11. 
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

(** ** Structure Inference *)

(** On [unit], [eq] is the only equivalence relation. Hence, we can
safely register [unit_setoid] as the canonical setoid for unit *)

Canonical unit_setoid := Eval hnf in eq_setoid unit.

Lemma unit_commMonoidLaws : comMonoidLaws tt (fun _ _ => tt).
Proof. by do 2 (split; try done). Qed.

Canonical unit_comMonoid := Eval hnf in ComMonoid unit_commMonoidLaws.

(** Any type can be endowed with a flat edge-label structure over the
equality setoid. However, we cannot declare this canonical for
arbitrary types, because this would take precedence over all other
setoids. Instead, we introduce an alias [flat] and equip it with a
flat edge-label structure. Note that [flat A] is convertible to [A] *)

Definition flat_elabels (A : Type) : elabelType.
by refine (@ElabelType (eq_setoid A) (fun _ _ => False) _ _ _); done.
Defined.

Definition flat (A : Type) := A.  
Canonical flat_setoid (A : Type) := eq_setoid (flat A). 
Canonical flat_elabelsType (A : Type) := Eval hnf in flat_elabels (flat A).
