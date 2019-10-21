Require Import RelationClasses Morphisms Relation_Definitions.
From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Setoids and Label Structures *)

(*  
TODO: packed classes? (does not seem to be problematic for now)
but we should at least understand the current hack in rewriting.v for setoid_of_bisetoid
*)

(** ** Structures *)

(** setoids *)
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

Lemma eqvxx (X : setoid) (x : X) : x ≡ x. reflexivity. Qed.
Arguments eqvxx [X x].

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

(** switch between [≡] and [≡'] based on a Boolean (useful for defining potentially edge swapping homomorphisms) *)
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

(** variants of the above that are more useful for backward chaining *)
Lemma eqvb_transR (X : labels) b b' (u v v' : le X) : 
  u ≡[b (+) b'] v' ->  v' ≡[b'] v ->  u ≡[b] v.
Proof. move => A B. move:(eqvb_trans A B). by rewrite -addbA addbxx addbF. Qed.

Lemma eqvb_transL (X : labels) b b' (u u' v : le X) : 
  u' ≡[b (+) b'] v ->  u ≡[b'] u' ->  u ≡[b] v.
Proof. move => A B. move:(eqvb_trans B A). by rewrite addbC -addbA addbxx addbF. Qed.

Global Instance eqv_morphim (X: labels) : 
  Proper (eq ==> eqv ==> eqv ==> iff) (@eqv_ X).
Proof. 
  move => b ? <- x x' xx y y' yy. 
  change (x ≡[false] x') in xx. change (y ≡[false] y') in yy. split => H. 
  - symmetry in xx. apply: eqvb_transR yy. apply: eqvb_transL xx. by rewrite !addbF.
  - symmetry in yy. apply: eqvb_transR yy. apply: eqvb_transL xx. by rewrite !addbF.
Qed.

Program Definition flat_labels (X: Type) :=
  {| lv := eq_setoid unit; mon0:=tt; mon2 _ _ :=tt;
     le := eq_setoid X; eqv' _ _ := False |}.
Next Obligation. by case x. Qed.
Next Obligation. tauto. Qed.

(** notations for vertex labels *)
Bind Scope labels with lv.
Delimit Scope labels with lbl.
Infix "⊗" := mon2 (left associativity, at level 25): labels.
Notation "1" := mon0: labels.

(** ** BigOps over the label monoid *)

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

Lemma big_split I r (P : pred I) (F1 F2 : I -> lv L) :
  \big[mon2/1]_(i <- r | P i) (F1 i ⊗ F2 i) ≡
  (\big[mon2/1]_(i <- r | P i) F1 i) ⊗ \big[mon2/1]_(i <- r | P i) F2 i.
Proof.
  elim/big_rec3 : _ => [|i x y z Pi ->]; rewrite ?monU //.
  rewrite -!monA. apply: mon_eqv => //. by rewrite monA [_ ⊗ y]monC monA.
Qed.

Lemma eqv_bigr (I : Type) (r : seq I) (P : pred I) (F1 F2 : I -> lv L) :
    (forall i : I, P i -> F1 i ≡ F2 i) -> \big[mon2/1]_(i <- r | P i) F1 i ≡ \big[mon2/1]_(i <- r | P i) F2 i.
Proof. elim/big_rec2 : _ => // i x y Pi H1 H2. by rewrite H2 ?H1. Qed.

Lemma eqv_bigl I r (P1 P2 : pred I) (F : I -> lv L) :
  P1 =1 P2 ->
  \big[mon2/1]_(i <- r | P1 i) F i ≡ \big[mon2/1]_(i <- r | P2 i) F i.
Proof. by move=> eqP12; rewrite -!(big_filter r) (eq_filter eqP12). Qed.

Lemma bigID (I:eqType) r (a P : pred I) (F : I -> lv L) :
  \big[mon2/1]_(i <- r | P i) F i ≡
  (\big[mon2/1]_(i <- r | P i && a i) F i) ⊗ \big[mon2/1]_(i <- r | P i && ~~ a i) F i.
Proof.
  rewrite !(@big_mkcond I r _ F) -big_split. 
  apply: eqv_bigr => i; case: (a i); by rewrite /= ?andbT ?andbF ?monU ?monUl.
Qed.
Arguments bigID [I r] a P F.

Lemma big_pred1_eq (I : finType) (i : I) (F : I -> lv L) :
  \big[mon2/1]_(j | j == i) F j ≡ F i.
Proof. rewrite -big_filter filter_index_enum enum1. (* big_seq1. *) by rewrite big_cons big_nil monU. Qed.

Lemma big_pred1 (I : finType) i (P : pred I) (F : I -> lv L) :
  P =1 pred1 i -> \big[mon2/1]_(j | P j) F j ≡ F i.
Proof.  move/(eq_bigl _ _)->; apply: big_pred1_eq. Qed.

Lemma bigD1 (I : finType) j (P : pred I) (F : I -> lv L) : 
  P j -> \big[mon2/1]_(i | P i) F i ≡ F j ⊗ \big[mon2/1]_(i | P i && (i != j)) F i.
Proof.
  move=> Pj; rewrite (bigID (pred1 j)); apply mon_eqv => //.
  apply: big_pred1 => i /=. by rewrite /= andbC; case: eqP => // ->.
Qed.
Arguments bigD1 [I] j [P F].

Lemma reindex_onto (I J : finType) (h : J -> I) h' (P : pred I) (F : I -> lv L) :
   (forall i, P i -> h (h' i) = i) ->
  \big[mon2/1]_(i | P i) F i ≡
  \big[mon2/1]_(j | P (h j) && (h' (h j) == j)) F (h j).
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


Lemma reindex (I J : finType) (h : J -> I) (P : pred I) (F : I -> lv L) :
    {on [pred i | P i], bijective h} ->
  \big[mon2/1]_(i | P i) F i ≡ \big[mon2/1]_(j | P (h j)) F (h j).
Proof.
case=> h' hK h'K; rewrite (reindex_onto h h' h'K).
by apply eqv_bigl => j; rewrite !inE; case Pi: (P _); rewrite //= hK ?eqxx.
Qed.
Arguments reindex [I J] h P F.

Lemma eqv_big I (r:seq I) (P1 P2 : pred I) (F1 F2 : I -> lv L) :
  P1 =1 P2 -> (forall i, P1 i -> F1 i ≡ F2 i) ->
  \big[mon2/1]_(i <- r | P1 i) F1 i ≡ \big[mon2/1]_(i <- r | P2 i) F2 i.
Proof. by move/eqv_bigl <-; move/eqv_bigr->. Qed.

Lemma partition_big (I J : finType) (P : pred I) p (Q : pred J) (F : I -> lv L) :
    (forall i, P i -> Q (p i)) ->
      \big[mon2/1]_(i | P i) F i ≡
         \big[mon2/1]_(j | Q j) \big[mon2/1]_(i | P i && (p i == j)) F i.
Proof.
move=> Qp; transitivity (\big[mon2/1]_(i | P i && Q (p i)) F i).
  by apply: eqv_bigl => i; case Pi: (P i); rewrite // Qp.
elim: {Q Qp}_.+1 {-2}Q (ltnSn #|Q|) => // n IHn Q.
case: (pickP Q) => [j Qj | Q0 _]; last first.
  by rewrite !big_pred0 // => i; rewrite Q0 andbF.
rewrite ltnS (cardD1x Qj) (bigD1 j) //; move/IHn=> {n IHn} <-.
rewrite (bigID (fun i => p i == j)) => /=. apply: mon_eqv; apply: eqv_bigl => i.
  case: eqP => [-> | _] ; by rewrite ?(Qj). 
by rewrite andbA.
Qed.


(* TODO: eliminate [i1] and [i2], which are only used as defaults for reindexing *)
Lemma big_sum (I1 I2 : finType) (i1 : I1) (i2 : I2) (P : pred (I1 + I2)) (F : (I1 + I2) -> lv L) : 
  \big[mon2/1]_(x | P x) F x ≡ 
  (\big[mon2/1]_(x | P (inl x)) F (inl x)) ⊗ (\big[mon2/1]_(x | P (inr x)) F (inr x)).
Proof.
  rewrite (bigID is_inl). apply: mon_eqv. 
  - rewrite (reindex inl). exact: eqv_bigl. 
    exists (fun x => if x is inl x then x else i1) => //. move => [x|x] //. by rewrite inE /= andbF.
  - rewrite (reindex inr). exact: eqv_bigl. 
    exists (fun x => if x is inr x then x else i2) => //. move => [x|x] //. by rewrite inE /= andbF.
Qed.
Arguments big_sum [I1 I2] i1 i2 P F.

Lemma big_seq1 I (i : I) (F : I -> lv L) : \big[mon2/1]_(j <- [:: i]) F j ≡ F i.
Proof. by rewrite unlock /= monU. Qed.

End Theory.
Arguments reindex_onto [L I J] h h' [P F].
Arguments reindex [L I J] h [P F].
Arguments bigD1 [L I] j [P F].
Arguments partition_big [L I J P] p Q [F].
Arguments big_pred1 [L I] i P F.
