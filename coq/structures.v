Require Import RelationClasses Morphisms Relation_Definitions.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.

(* basic structures used for the completeness proof of 2pdom algebra

  TODO: packed classes? (does not seem to be problematic for now)
   but we should at least understand the current hack in rewriting.v for setoid_of_bisetoid
 *)


(* setoids *)
Structure setoid :=
  Setoid {
      car:> Type;
      eqv: relation car;
      Eqv: Equivalence eqv
    }.
Arguments eqv {_}. 
Infix "≡" := eqv (at level 79).
Global Existing Instance Eqv.

Definition eq_setoid (X: Type): setoid := Setoid (@eq_equivalence X).


(* ingredients required to label graphs
   - eqv' x y = eqv x y° (when we have an involution _°)
   - eqv' _ _ = False    (otherwise)
 *)
Structure labels :=
  Labels {
      lv: setoid;
      mon0: lv;
      mon2: lv -> lv -> lv;
      mon_eqv: Proper (eqv ==> eqv ==> eqv) mon2;
      monA: forall x y z, mon2 x (mon2 y z) ≡ mon2 (mon2 x y) z;
      monC: forall x y, mon2 x y ≡ mon2 y x;
      monU: forall x, mon2 x mon0 ≡ x;
                           
      le: setoid;
      eqv': relation le;
      Eqv'_sym: Symmetric eqv';
      eqv10: forall x y z, eqv' x y -> eqv  y z -> eqv' x z;
      eqv01: forall x y z, eqv  x y -> eqv' y z -> eqv' x z;
      eqv11: forall x y z, eqv' x y -> eqv' y z -> eqv  x z;
    }.
Global Existing Instance mon_eqv.
Arguments mon0 {_}.
Arguments mon2 {_}.
Arguments eqv' {_}.
Infix "≡'" := eqv' (at level 79).

(* switch between [≡] and [≡'] based on a Boolean (useful for defining potentially edge swapping homomorphisms) *)
Definition eqv_ (X: labels) (b: bool) (x y: le X) := if b then x ≡' y else x ≡ y.
Notation "x ≡[ b ] y" := (eqv_ b x y) (at level 79).
Global Instance eqv_sym {X: labels} {b}: Symmetric (@eqv_ X b).
Proof. case b=> x y/=. apply Eqv'_sym. by symmetry. Qed.

Global Instance eqv_morphim (X: labels) : 
  Proper (eq ==> eqv ==> eqv ==> iff) (@eqv_ X).
Proof. move => b ? <- x x' xx y y' yy. Admitted.


Program Definition flat_labels (X: Type) :=
  {| lv := eq_setoid unit; mon0:=tt; mon2 _ _ :=tt;
     le := eq_setoid X; eqv' _ _ := False |}.
Next Obligation. by case x. Qed.
Next Obligation. tauto. Qed.

(* notations for vertex labels *)
Bind Scope labels with lv.
Delimit Scope labels with lbl.
Infix "⊗" := mon2 (left associativity, at level 25): labels.
Notation "1" := mon0: labels.

