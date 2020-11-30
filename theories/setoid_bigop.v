Require Import RelationClasses Morphisms Relation_Definitions.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Bigops over Setoids *)

(** This file generalizes various lemmas from
[mathcomp.ssreflect.bigop] to the setting where monoid laws only hold
up to the equivalence of some setoid. *)

(** ** setoids *)

From HB Require Import structures.

HB.mixin Record Setoid_of_Type A := 
  { eqv : relation A; Eqv : Equivalence eqv }.

HB.structure Definition Setoid := { A of Setoid_of_Type A }.
Notation setoid := Setoid.type.

Declare Scope setoid_scope.
Open Scope setoid_scope.
Infix "≡" := eqv (at level 79) : setoid_scope.
Notation "x ≡ y :> X" := ((x : X) ≡ (y : X)) 
  (at level 79, y at next level, only parsing) : setoid_scope.
Global Existing Instance Eqv.

Definition flat (A : Type) := A.
Definition flat_setoid_mixin (A : Type) := 
  Setoid_of_Type.Build A (@eq_equivalence A).
Section A.

(** TODO: Remove the section wrapper once HB supports this *)
Variable (A : Type).
HB.instance (flat A) (flat_setoid_mixin A).
End A.
HB.instance unit (flat_setoid_mixin unit).

Lemma eqvxx (X : setoid) (x : X) : x ≡ x. reflexivity. Qed.
Arguments eqvxx {X x}.

(** This allows [trivia] (and hence [done]) to solve [x ≡ x]. *)
Hint Extern 0 => reflexivity : core.

Class monoidLaws {X : setoid} (mon0 : X) (mon2 : X -> X -> X) :=
  MonoidLaws {
      mon_eqv: Proper (eqv ==> eqv ==> eqv) mon2;
      monA: forall x y z, mon2 x (mon2 y z) ≡ mon2 (mon2 x y) z;
      monU: forall x, mon2 x mon0 ≡ x;
      monUl: forall x, mon2 mon0 x ≡ x
    }.
Global Existing Instance mon_eqv.

Class comMonoidLaws {X:setoid} (mon0 : X) (mon2 : X -> X -> X) :=
  ComMonoidLaws { 
      mon_of_com :> monoidLaws mon0 mon2;
      monC : forall x y, mon2 x y ≡ mon2 y x 
    }.

Section SetoidTheory.
Variables (X : setoid) (mon0 : X) (mon2 : X -> X -> X).
Local Notation "1" := mon0.
Local Notation "*%M" := mon2 (at level 0).
Notation "x ⊗ y" := (mon2 x y) (left associativity, at level 25).

Lemma monUl_of_com : 
  (forall x, mon2 x mon0 ≡ x) -> (forall x y, mon2 x y ≡ mon2 y x) -> forall x, mon2 mon0 x ≡ x.
Proof. move => monU monC x. by rewrite monC monU. Qed.

Definition mkComMonoidLaws
  (mon_eqv: Proper (eqv ==> eqv ==> eqv) mon2)
  (monA: forall x y z, mon2 x (mon2 y z) ≡ mon2 (mon2 x y) z)
  (monC : forall x y, mon2 x y ≡ mon2 y x)
  (monU: forall x, mon2 x mon0 ≡ x) :=
  ComMonoidLaws (MonoidLaws mon_eqv monA monU (monUl_of_com monU monC)) monC.

Section MonoidTheory.
Context {X_monoid : monoidLaws mon0 mon2}.

(* TOTHINK: The initial lemmas only require the Proper instance: introduce another class? *)
Lemma eqv_bigr (I : Type) (r : seq I) (P : pred I) (F1 F2 : I -> X) :
    (forall i : I, P i -> F1 i ≡ F2 i) -> \big[*%M/1]_(i <- r | P i) F1 i ≡ \big[*%M/1]_(i <- r | P i) F2 i.
Proof. elim/big_rec2 : _ => // i x y Pi H1 H2. by rewrite H2 ?H1. Qed.

Lemma eqv_bigl I r (P1 P2 : pred I) (F : I -> X) :
  P1 =1 P2 ->
  \big[*%M/1]_(i <- r | P1 i) F i ≡ \big[*%M/1]_(i <- r | P2 i) F i.
Proof. by move=> eqP12; rewrite -!(big_filter r) (eq_filter eqP12). Qed.

Lemma eqv_big I (r:seq I) (P1 P2 : pred I) (F1 F2 : I -> X) :
  P1 =1 P2 -> (forall i, P1 i -> F1 i ≡ F2 i) ->
  \big[*%M/1]_(i <- r | P1 i) F1 i ≡ \big[*%M/1]_(i <- r | P2 i) F2 i.
Proof. by move/eqv_bigl <-; move/eqv_bigr->. Qed.

Lemma big_mkcond (I : eqType) (r : seq I) (P : pred I) (F : I -> X) :
  \big[*%M/1]_(i <- r | P i) F i ≡ \big[*%M/1]_(i <- r) (if P i then F i else 1).
Proof. rewrite unlock. elim: r => //= i r H. by case P; rewrite H ?monUl. Qed.

Lemma big_cat (I : eqType) (r1 r2 : seq I) (P : pred I) (F : I -> X) :
      \big[*%M/1]_(i <- (r1 ++ r2) | P i) F i ≡
      (\big[*%M/1]_(i <- r1 | P i) F i) ⊗ (\big[*%M/1]_(i <- r2 | P i) F i).
Proof.
rewrite !(big_mkcond _ P). elim: r1 => /= [|i r1 IH]; first by rewrite big_nil monUl.
by rewrite !big_cons IH monA.
Qed.

Lemma big_seq1 (I : Type) (i : I) (F : I -> X) : \big[*%M/1]_(j <- [:: i]) F j ≡ F i.
Proof. by rewrite big_cons big_nil monU. Qed.

Lemma big_pred1_eq (I : finType) (i : I) (F : I -> X) :
  \big[*%M/1]_(j | j == i) F j ≡ F i.
Proof. 
  rewrite -big_filter filter_pred1_uniq //; first by rewrite big_seq1.
  solve [by rewrite /index_enum -?enumT ?enum_uniq (* mathcomp-1.9.0 *)
        |exact: index_enum_uniq].                  (* mathcomp-1.10.0 *)
Qed.

Lemma big_pred1 (I : finType) i (P : pred I) (F : I -> X) :
  P =1 pred1 i -> \big[*%M/1]_(j | P j) F j ≡ F i.
Proof.  move/(eq_bigl _ _)->; apply: big_pred1_eq. Qed.

Lemma eqv_map (I1 I2 : finType) (r1 : seq I1) (P1 : pred I1) (P2 : pred I2) 
  (f : I1 -> I2) (F1 : I1 -> X) (F2 : I2 -> X) :
   (forall x, P1 x = P2 (f x)) -> (forall i : I1, P1 i -> F1 i ≡ F2 (f i)) -> 
   \big[*%M/1]_(i <- r1 | P1 i) F1 i ≡ \big[*%M/1]_(i <- map f r1 | P2 i) F2 i.
Proof.
  move => HP HF. elim r1 => [|k r2 IH]; first by rewrite !big_nil.
  rewrite /= !big_cons -HP. case: (boolP (P1 k)) => [Pk|_]; by rewrite -?HF ?IH.
Qed.

End MonoidTheory.

Section ComMonoidTheory.
Context {X_comMonoid : comMonoidLaws mon0 mon2}.

Local Notation "1" := mon0.
Local Notation "*%M" := mon2 (at level 0).
Notation "x ⊗ y" := (mon2 x y) (left associativity, at level 25).

Lemma big_split I r (P : pred I) (F1 F2 : I -> X) :
  \big[*%M/1]_(i <- r | P i) (F1 i ⊗ F2 i) ≡
  (\big[*%M/1]_(i <- r | P i) F1 i) ⊗ \big[*%M/1]_(i <- r | P i) F2 i.
Proof.
  elim/big_rec3 : _ => [|i x y z Pi ->]; rewrite ?monU //.
  rewrite -!monA. apply: mon_eqv => //. by rewrite monA [_ ⊗ y]monC monA.
Qed.

Lemma perm_big (I : eqType) r1 r2 (P : pred I) (F : I -> X) :
  perm_eq r1 r2 ->
  \big[*%M/1]_(i <- r1 | P i) F i ≡ \big[*%M/1]_(i <- r2 | P i) F i.
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

Lemma bigID (I:eqType) r (a P : pred I) (F : I -> X) :
  \big[*%M/1]_(i <- r | P i) F i ≡
  (\big[*%M/1]_(i <- r | P i && a i) F i) ⊗ \big[*%M/1]_(i <- r | P i && ~~ a i) F i.
Proof.
  rewrite !(@big_mkcond _ I r _ F) -big_split. 
  apply: eqv_bigr => i; case: (a i); by rewrite /= ?andbT ?andbF ?monU ?monUl.
Qed.
Arguments bigID [I r] a P F.


Lemma bigD1 (I : finType) j (P : pred I) (F : I -> X) : 
  P j -> \big[*%M/1]_(i | P i) F i ≡ F j ⊗ \big[*%M/1]_(i | P i && (i != j)) F i.
Proof.
  move=> Pj; rewrite (bigID (pred1 j)); apply mon_eqv => //.
  apply: big_pred1 => i /=. by rewrite /= andbC; case: eqP => // ->.
Qed.
Arguments bigD1 [I] j [P F].

Lemma reindex_onto (I J : finType) (h : J -> I) h' (P : pred I) (F : I -> X) :
   (forall i, P i -> h (h' i) = i) ->
  \big[*%M/1]_(i | P i) F i ≡
  \big[*%M/1]_(j | P (h j) && (h' (h j) == j)) F (h j).
Proof.
move=> h'K; elim: {P}_.+1 {-3}P h'K (ltnSn #|P|) => //= n IHn P h'K.
case: (pickP P) => [i Pi | P0 _]; last first.
  by rewrite !big_pred0 // => j; rewrite P0.
rewrite ltnS (cardD1x Pi); move/IHn {n IHn} => IH.
rewrite (bigD1 i Pi) (bigD1 (h' i)) h'K ?Pi ?eq_refl //=. apply: mon_eqv => //.
rewrite {}IH => [|j]; [apply: eqv_bigl => j | by case/andP; auto].
rewrite andbC -andbA (andbCA (P _)); case: eqP => //= hK; congr (_ && ~~ _).
by apply/eqP/eqP=> [<-|->] //; rewrite h'K.
Qed.
Arguments reindex_onto [I J] h h' [P F].

Lemma reindex (I J : finType) (h : J -> I) (P : pred I) (F : I -> X) :
    {on [pred i | P i], bijective h} ->
  \big[*%M/1]_(i | P i) F i ≡ \big[*%M/1]_(j | P (h j)) F (h j).
Proof.
case=> h' hK h'K; rewrite (reindex_onto h h' h'K).
by apply eqv_bigl => j; rewrite !inE; case Pi: (P _); rewrite //= hK ?eqxx.
Qed.
Arguments reindex [I J] h P F.

Lemma partition_big (I J : finType) (P : pred I) p (Q : pred J) (F : I -> X) :
    (forall i, P i -> Q (p i)) ->
      \big[*%M/1]_(i | P i) F i ≡
         \big[*%M/1]_(j | Q j) \big[*%M/1]_(i | P i && (p i == j)) F i.
Proof.
move=> Qp; transitivity (\big[*%M/1]_(i | P i && Q (p i)) F i).
  by apply: eqv_bigl => i; case Pi: (P i); rewrite // Qp.
elim: {Q Qp}_.+1 {-2}Q (ltnSn #|Q|) => // n IHn Q.
case: (pickP Q) => [j Qj | Q0 _]; last first.
  by rewrite !big_pred0 // => i; rewrite Q0 andbF.
rewrite ltnS (cardD1x Qj) (bigD1 j) //; move/IHn=> {n IHn} <-.
rewrite (bigID (fun i => p i == j)) => /=. apply: mon_eqv; apply: eqv_bigl => i.
  case: eqP => [-> | _] ; by rewrite ?(Qj) ?andbT ?andbF. 
by rewrite andbA.
Qed.

Lemma big_sumType (I1 I2 : finType) (P : pred (I1 + I2)) (F : (I1 + I2) -> X) : 
  \big[*%M/1]_(x | P x) F x ≡ 
  (\big[*%M/1]_(x | P (inl x)) F (inl x)) ⊗ (\big[*%M/1]_(x | P (inr x)) F (inr x)).
Proof. by rewrite ![index_enum _]unlock [@Finite.enum in X in X ≡ _]unlock big_cat !big_map. Qed.
Arguments big_sumType [I1 I2] P F.

Lemma big_unitType (P : pred unit) (F : unit -> X) : 
  \big[*%M/1]_(x | P x) F x ≡ if P tt then F tt else 1.
Proof. by rewrite ![index_enum _]unlock [@Finite.enum]unlock big_mkcond big_seq1. Qed.

(** in conjunction with [bij_perm_enum] *)
Lemma eqv_big_bij (I1 I2 : finType) (f : I1 -> I2) 
   (r1 : seq I1) (r2 : seq I2) (P1 : pred I1) (P2 : pred I2) (F1 : I1 -> X) (F2 : I2 -> X) :
   perm_eq r2 (map f r1) -> (forall x, P1 x = P2 (f x)) -> (forall i : I1, P1 i -> F1 i ≡ F2 (f i)) -> 
   \big[*%M/1]_(i <- r1 | P1 i) F1 i ≡ \big[*%M/1]_(i <- r2 | P2 i) F2 i.
Proof. move => pr HP HF. rewrite (perm_big _ _ pr). exact: eqv_map. Qed.

Lemma big_inj2_eq (I1 I2 : finType) (F : I1 -> X) (f : I1 -> I2) (y : I1) :
  injective f -> \big[*%M/mon0]_(x | f x == f y) F x ≡ F y.
Proof. move => inj_f; rewrite (@big_pred1 _ _ y) //= => x; exact: inj_eq. Qed.

End ComMonoidTheory.
End SetoidTheory.

Arguments reindex_onto [X mon0 mon2 _ I J] h h' [P F].
Arguments reindex [X mon0 mon2 _ I J] h [P F].
Arguments bigD1 [X mon0 mon2 _ I] j [P F].
Arguments partition_big [X mon0 mon2 _ I J P] p Q [F].
Arguments big_pred1 [X mon0 mon2 _ I] i P F.
