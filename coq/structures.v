Require Import Setoid Morphisms.
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

(* setoids with an second notion of equality: 
   - eqv' x y = eqv x y° (when we have an involution _°)
   - eqv' _ _ = False    (otherwise)
 *)
Structure bisetoid :=
  BiSetoid {
      setoid_of_bisetoid:> setoid;
      eqv': relation setoid_of_bisetoid;
      Eqv'_sym: Symmetric eqv';
      eqv10: forall x y z, eqv' x y -> eqv  y z -> eqv' x z;
      eqv01: forall x y z, eqv  x y -> eqv' y z -> eqv' x z;
      eqv11: forall x y z, eqv' x y -> eqv' y z -> eqv  x z;
    }.
Arguments eqv' {_}.
Infix "≡'" := eqv' (at level 79).

(* switch between [≡] and [≡'] based on a Boolean (useful for defining potentially edge swapping homomorphisms) *)
Definition eqv_ (X: bisetoid) (b: bool) (x y: X) := if b then x ≡' y else x ≡ y.
Notation "x ≡[ b ] y" := (eqv_ b x y) (at level 79).
Global Instance eqv_sym {X: bisetoid} {b}: Symmetric (@eqv_ X b).
Proof. case b=> x y/=. apply Eqv'_sym. by symmetry. Qed.

Program Definition trivial_bisetoid (X: Type) := {| setoid_of_bisetoid := {| eqv := @eq X |}; eqv' (_ _: X) := False |}.
Next Obligation. eauto with typeclass_instances. Qed.
Next Obligation. tauto. Qed.

(* (commutative) monoids 
   for labelling graph vertices
 *)
Structure monoid :=
  Monoid {
      setoid_of_monoid:> setoid;
      mon0: setoid_of_monoid;
      mon2: setoid_of_monoid -> setoid_of_monoid -> setoid_of_monoid;
      mon_eqv: Proper (@eqv _ ==> @eqv _ ==> @eqv _) mon2;
      monA: forall x y z, mon2 x (mon2 y z) ≡ mon2 (mon2 x y) z;
      monC: forall x y, mon2 x y ≡ mon2 y x;
      monU: forall x, mon2 x mon0 ≡ x
    }.
Global Existing Instance mon_eqv.
Arguments mon0 {_}.
Arguments mon2 {_}.
