From mathcomp Require Import all_ssreflect.
Require Export mathcomp.finmap.finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

Open Scope fset_scope.

Lemma fsval_eqF (T:choiceType) (E : {fset T}) (e : E) x : x \notin E -> val e == x = false.
Proof. apply: contraNF => /eqP <-. exact: fsvalP. Qed.

Lemma fsetDDD (T : choiceType) (A B C : {fset T}) : A `\` B `\` (C `\` B) = A `\` (B `|` C).
Proof. apply/fsetP => z. rewrite !inE. by case (z \in B). Qed.

Lemma in_imfsetT (aT : finType) (rT : choiceType) (f : aT -> rT) (x : aT) : 
  f x \in [fset f x | x in aT].
Proof. by rewrite in_imfset. Qed.

Lemma fsetDEl (T : choiceType) (A B : {fset T}) (x : A `\` B) : val x \in A.
Proof. by case/fsetDP : (valP x). Qed.

Lemma fset1UE (T : choiceType) (x a : T) (A : {fset T}) : 
 x \in a |` A ->  (x = a) + (x != a) * (x \in A).
Proof. rewrite !inE. case: (altP (x =P a)) => /=; [by left|by right;split]. Qed.

Lemma fsvalK (T : choiceType) (A : {fset T}) (x : A) (p : fsval x \in A) : Sub (fsval x) p = x.
Proof. exact: val_inj. Qed.

Lemma fsetUDU (T : choiceType) (A B C : {fset T}) : 
  [disjoint A & B] -> (A `|` B) `\` (A `|` C) = B `\` C.
Proof. 
  move => disAC. apply/fsetP => x. rewrite !inE. case Hx : (x \in A) => //=. 
  by rewrite -[x \in B]negbK (fdisjointP disAC) //= andbF. 
Qed.

Lemma cardsDsub (T : choiceType) (A B : {fset T}) : 
  #|` A `\` B | == 0 -> A `<=` B.
Proof. by rewrite -fsetD_eq0 cardfs_eq0. Qed.

Lemma cardsIsub (T : choiceType) (A B : {fset T}) :
  #|`A `&` B| = #|`B| -> B `<=` A.
Proof. move => H. by rewrite cardsDsub // cardfsD fsetIC H subnn. Qed.

Lemma fset1U0 (T : choiceType) (x : T) (A : {fset T}) : x |` A != fset0.
Proof. apply: contraFneq (in_fset0 x) => <-. by rewrite !inE eqxx. Qed.

Lemma imfset0 (aT rT : choiceType) (f : aT -> rT) : [fset f x | x in fset0] = fset0.
Proof. apply/fsetP => z. rewrite inE. apply: contraTF isT. by case/imfsetP. Qed.

Arguments fset1Ur [K x a B].
Arguments fset1U1 [K x B].
Arguments fset1U1 [K x B].

(** Things that also depend on preliminaries.v *)
Require Import Coq.Relations.Relation_Definitions.
Require Import edone preliminaries.

(** uses Sigma *)
Lemma fset2_cases (T : choiceType) (x y x' y' : T) : x != y -> x' != y' ->
  let A := [fset x;y] in 
  let B := [fset x';y'] in 
  (A = B) + [disjoint A & B] + (Σ z : T, A `&` B = [fset z]).
Proof.
  move => D D' A B.
  have [CA CB] : #|` A| = 2 /\ #|` B| = 2. 
  { by  rewrite !cardfs2 ?(negbTE D) ?(negbTE D'). }
  move C : (#|` A `&` B|) => n. case: n C => [|[|[|]]] => C.
  - left;right. by rewrite -fsetI_eq0 (cardfs0_eq C).
  - right.
    have E : exists z : T, A `&` B == [fset z].
    { setoid_rewrite <- (rwP eqP). apply/cardfs1P. exact/eqP. }
    exists (xchoose E). apply/eqP. exact: (xchooseP E). 
  - left;left. apply/eqP. 
    by rewrite eqEfsubset !cardsIsub // ?CA ?CB ?[_ `&` A]fsetIC.
  - move/eqP. rewrite eqn_leq [C.+3 <= _]negbTE ?andbF // -leqNgt -addn2.
    apply: leq_trans (leq_addl _ _). rewrite -CA. 
    apply: fsubset_leq_card. exact: fsubsetIl.
Qed.

Lemma imfset_inv (aT : finType) (rT : choiceType) (f : aT -> rT) (y : [fset f x | x in aT]) : 
  Σ x : aT, f x = val y.
Proof. 
  suff E : exists x, f x == val y by exists (xchoose E); rewrite (eqP (xchooseP E)).
  case/imfsetP : (valP y) => /= x _ ->. by exists x.
Qed.

(** uses maxnP *)

Lemma mem_maxn n m (A : {fset nat}) : n \notin A -> m \notin A -> maxn n m \notin A.
Proof. by case: maxnP. Qed.

Lemma maxn_fset2 n m : maxn n m \in [fset n; m].
Proof. case: maxnP; by rewrite !in_fset2 eqxx. Qed.
  
Lemma maxn_fsetD n m (A : {fset nat}) : maxn n m \notin A `\` [fset n; m]. 
Proof. by rewrite inE negb_and negbK maxn_fset2. Qed.

Lemma fset2_maxn_neq n m x : x \notin [fset n; m] -> x != maxn n m.
Proof. apply: contraNneq => ->. exact: maxn_fset2. Qed.


(** depends on update *)
Lemma in_eqv_update (aT : choiceType) (rT : Type) (f g : aT -> rT) (E : relation rT) 
  (z : aT) (u v : rT) (A : {fset aT}) : 
  {in A, forall x : aT, E (f x) (g x)} -> E u v -> 
  {in z |` A, forall x : aT, E (f[upd z := u] x) (g[upd z := v] x)}.
Proof.
  move => H Euv k. rewrite !inE. 
  case: (altP (k =P z)) => [-> _|? /= inA]; rewrite !updateE //. exact: H.
Qed.

Lemma eqv_update (aT : eqType) (rT : Type) (f g : aT -> rT) (E : relation rT) z u v : 
  (forall x, E (f x) (g x)) -> E u v -> forall x, E (f[upd z := u] x) (g[upd z := v] x).
Proof. move => H Euv k. case: (altP (k =P z)) => [->|?]; by rewrite !updateE. Qed.


(** Bijections between finite sets *)
Require Import bij.

(** TOTHINK: how to have simpl keep the [h/h^-1] notation unless the functions actually reduce? *)
Section Bij.
Variable (G : finType) (T : choiceType) (g : G -> T).
Hypothesis g_inj : injective g.
Let vset := [fset g x | x in G].
Definition imfset_bij_fwd (x : G) : vset := Sub (g x) (in_imfsetT g x).
Definition imfset_bij_bwd (x : vset) : G := tag (imfset_inv x).

Lemma can_vset : cancel imfset_bij_fwd imfset_bij_bwd.
Proof. 
  move => x. rewrite /imfset_bij_fwd /imfset_bij_bwd /=. set S := Sub _ _. 
  apply: g_inj. by rewrite (tagged (imfset_inv S)).
Qed.

Lemma can_vset' : cancel imfset_bij_bwd imfset_bij_fwd.
Proof.
  move => [x Hx]. rewrite /imfset_bij_fwd /imfset_bij_bwd. apply: val_inj => /=.
  by rewrite (tagged (imfset_inv [` Hx])).
Qed.

Definition imfset_bij := Bij can_vset can_vset'.

Lemma imfset_bij_bwdE x p : imfset_bij_bwd (Sub (g x) p) = x.
Proof. 
  rewrite /imfset_bij_bwd. set t := imfset_inv _. 
  by move/g_inj : (tagged t).
Qed.

End Bij.

Lemma fresh_bij (T : finType) (E : {fset nat}) (f : bij T E) e (He : e \notin E) : 
  bij (option T) (e |` E).
Proof.
  pose g (x : option T) :  e |` E := 
    if x is Some z then Sub (val (f z)) (fset1Ur (valP (f z))) else Sub e fset1U1.
  pose g_inv  (x : e |` E) : option T := 
    match fsetULVR (valP x) with inl _ => None | inr p => Some (f^-1 (Sub (val x) p)) end.
  have can_g : cancel g g_inv.
  { move => [x|]; rewrite /g/g_inv/=; case: (fsetULVR _) => [|p] //=. 
    - by rewrite inE fsval_eqF.
    - by rewrite valK' bijK.
    -  exfalso. by rewrite p in He. }
  have can_g_inv : cancel g_inv g.
  { move => [x Hx]; rewrite /g/g_inv/=. case: (fsetULVR _) => [|p] //=. 
    - rewrite !inE => A. apply: val_inj => /=. by rewrite (eqP A).
    - apply: val_inj => //=. by rewrite bijK'. }
  apply: (Bij can_g can_g_inv).
Defined.

Lemma fresh_bijE (T : finType) (E : {fset nat}) (f : bij T E) x (Hx : x \notin E) : 
  (forall x, fresh_bij f Hx (Some x) = Sub (val (f x)) (fset1Ur (valP (f x))))*
  (fresh_bij f Hx None = Sub x fset1U1).
Proof. done. Qed.

(** not acutally used *)
Definition bij_setD (aT : finType) (C : choiceType) (rT : {fset C}) (A : {set aT}) (f : bij aT rT) : 
  bij { x | x \in ~: A} (rT `\` [fset val (f x) | x in A]).
Proof.
  set aT' := ({ x | _ }). set rT' := _ `\` _.
  have g_proof (x : aT') : val (f (val x)) \in rT'.
  { rewrite !inE (valP (f (val x))) andbT. apply: contraTN (valP x).
    case/imfsetP => /= x0 inA /val_inj /(@bij_injective _ _ f) ->. by rewrite inE negbK. }
  pose g (x : aT') : rT' := Sub (val (f (val x))) (g_proof x).
  have g_inv_proof (x : rT') :  f^-1 (Sub (fsval x) (fsetDEl x)) \in ~: A.
  { rewrite inE. case/fsetDP: (valP x) => ?. apply: contraNN => X. apply/imfsetP.
    exists (f^-1 (Sub (fsval x) (fsetDEl x))) => //. by rewrite bijK'. }
  pose g_inv (x : rT') : aT' := Sub (f^-1 (Sub (val x) (fsetDEl x))) (g_inv_proof x). 
  have can1 : cancel g g_inv.
  { move => [x Hx]. rewrite /g/g_inv. apply: val_inj => /=. apply: (@bij_injective _ _ f).
    rewrite bijK'. exact: val_inj. }
  have can2 : cancel g_inv g.
  { move => [x Hx]. rewrite /g/g_inv. apply: val_inj => /=. by rewrite bijK'. }
  apply: Bij can1 can2.
Defined.

Section BijCast.
Variables (T : choiceType) (A A' : {fset T}) (eqA : A = A').
Definition bij_cast : bij A A'.
Proof. case eqA. exact bij_id. Defined.

Lemma cast_proof x : x \in A -> x \in A'. case eqA. exact id. Qed.

Lemma bij_castE x (Hx : x \in A) : bij_cast [` Hx] = [` cast_proof Hx].
Proof. 
  rewrite /bij_cast. move: (cast_proof _). case eqA => Hx'. exact: val_inj.
Qed.
End BijCast.
