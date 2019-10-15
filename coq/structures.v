Require Import RelationClasses Morphisms Relation_Definitions.
From mathcomp Require Import all_ssreflect.
Require Import edone.

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

Section Theory.
Variable L : labels.
Local Open Scope labels.

Lemma monUl (x : lv L) : 1 ⊗ x ≡ x. by rewrite monC monU. Qed.

Lemma big_mkcond (I : eqType) (r : seq I) (P : pred I) (F : I -> lv L) :
  \big[mon2/1]_(i <- r | P i) F i ≡ \big[mon2/1]_(i <- r) (if P i then F i else 1).
Proof. rewrite unlock. elim: r => //= i r H. by case P; rewrite H ?monUl. Qed.

Lemma big_cat (I : eqType) (r1 r2 : seq I) (P : pred I) (F : I -> lv L) :
      \big[mon2/1]_(i <- (r1 ++ r2) | P i) F i ≡
      (\big[mon2/1]_(i <- r1 | P i) F i) ⊗ (\big[mon2/1]_(i <- r2 | P i) F i).
Proof.
rewrite !(big_mkcond _ P). elim: r1 => /= [|i r1 IH]; first by rewrite big_nil monUl.
by rewrite !big_cons IH monA.
Qed.

Lemma perm_big (I : eqType) r1 r2 (P : pred I) (F : I -> lv L) :
  perm_eq r1 r2 ->
  \big[mon2/1]_(i <- r1 | P i) F i ≡ \big[mon2/1]_(i <- r2 | P i) F i.
Proof.
move/permP; rewrite !(big_mkcond _ P).
elim: r1 r2 => [|i r1 IHr1] r2 eq_r12.
  by case: r2 eq_r12 => // i r2; move/(_ (pred1 i)); rewrite /= eqxx.
have r2i: i \in r2 by rewrite -has_pred1 has_count -eq_r12 /= eqxx.
case/splitPr: r2 / r2i => [r3 r4] in eq_r12 *. rewrite big_cat /= !big_cons.
rewrite monA [_ ⊗ if _ then _ else _]monC -monA. rewrite -big_cat. 
rewrite (IHr1 (r3 ++ r4)) //.  move => a. move/(_ a) : eq_r12. 
rewrite !count_cat /= addnCA. apply: addnI.
Qed.

Lemma eqv_map (I1 I2 : finType) (r1 : seq I1) (P1 : pred I1) (P2 : pred I2) 
  (f : I1 -> I2) (F1 : I1 -> lv L) (F2 : I2 -> lv L) :
   (forall x, P1 x = P2 (f x)) -> (forall i : I1, P1 i -> F1 i ≡ F2 (f i)) -> 
   \big[mon2/1]_(i <- r1 | P1 i) F1 i ≡ \big[mon2/1]_(i <- map f r1 | P2 i) F2 i.
Proof.
  
  move => HP HF. elim r1 => [|k r2 IH]; first by rewrite !big_nil.
  rewrite /= !big_cons -HP. case: (boolP (P1 k)) => [Pk|_]; by rewrite -?HF ?IH.
Qed.

Lemma eqv_big_bij (I1 I2 : finType) (f : I1 -> I2) 
   (r1 : seq I1) (r2 : seq I2) (P1 : pred I1) (P2 : pred I2) (F1 : I1 -> lv L) (F2 : I2 -> lv L) :
   perm_eq r2 (map f r1) -> (forall x, P1 x = P2 (f x)) -> (forall i : I1, P1 i -> F1 i ≡ F2 (f i)) -> 
   \big[mon2/1]_(i <- r1 | P1 i) F1 i ≡ \big[mon2/1]_(i <- r2 | P2 i) F2 i.
Proof. move => pr HP HF. rewrite (perm_big _ _ pr). exact: eqv_map. Qed.


End Theory.
