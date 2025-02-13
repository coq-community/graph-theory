From Coq Require Import RelationClasses Setoid Morphisms List.
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import preliminaries bij finite_quotient.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs". 



Lemma equiv_of_class (T : finType) (e : rel T) : equiv_class_of (equiv_of e).
Proof. constructor; auto using equiv_of_refl, equiv_of_sym, equiv_of_trans. Qed.

Canonical equiv_of_equivalence (T : finType) (e : rel T) := EquivRelPack (equiv_of_class e).

Lemma equiv_ofE (T1 T2 : finType) (e1 : rel T1) (e2 : equiv_rel T2) (f : T1 -> T2) x y :
  (forall u v : T1, e1 u v -> e2 (f u) (f v)) -> equiv_of e1 x y -> e2 (f x) (f y).
Proof.
  move => H. case/connectP => p. elim: p x => /= [x _ -> //|z p IH x /andP [xz] pth_p lst_p].
  apply: equiv_trans (IH _ pth_p lst_p). 
  case/orP : xz; [exact: H|rewrite equiv_sym; exact: H].
Qed.

Lemma equiv_of_transfer (T1 T2 : finType) (e1 : rel T1) (e2 : rel T2) (f : T1 -> T2) x y :
  (forall u v : T1, e1 u v -> equiv_of e2 (f u) (f v)) ->
  equiv_of e1 x y -> equiv_of e2 (f x) (f y).
Proof. exact: equiv_ofE. Qed.

Definition pairs A := seq (A*A).
Definition map_pairs A B (f: A -> B): pairs A -> pairs B := map (fun x => (f x.1,f x.2)). 


Definition rel_of_pairs (A : eqType) (l : pairs A) : rel A := [rel x y | (x,y) \in l].
Definition eqv_clot (T : finType) (l : pairs T) : equiv_rel T :=
  (* equiv_of_equivalence (rel_of_pairs l). *)
  locked [equiv_rel of equiv_of (rel_of_pairs l)].

Lemma eqv_clotE (T : finType) (l : pairs T) x y : 
  eqv_clot l x y = equiv_of (rel_of_pairs l) x y.
Proof. by rewrite /eqv_clot -lock. Qed.

(* move to equiv.v *)
Lemma eqv_clot_pair (A : finType) (h : pairs A) x y : (x, y) \in h -> eqv_clot h x y.
Proof. move => H. rewrite eqv_clotE. exact: sub_equiv_of. Qed.

Lemma rel_of_pairs_mono (T : finType) (l l' : pairs T) :
  {subset l <= l'} -> subrel (rel_of_pairs l) (rel_of_pairs l').
Proof. move => sub_l x y. exact: sub_l. Qed.

Lemma eqv_clot_subset (T : finType) (l1 l2 : pairs T) : 
  {subset l1 <= l2} -> subrel (eqv_clot l1) (eqv_clot l2).
Proof. 
  move => H x y. rewrite !eqv_clotE. apply: equiv_of_transfer => u v.
  move => R. apply: sub_equiv_of. exact: rel_of_pairs_mono R.
Qed.
Arguments eqv_clot_subset [T] l1 [l2].

Lemma subset_catL (T : eqType) (h k : seq T) : {subset h <= h ++ k}.
Proof. move => x H. by rewrite mem_cat H. Qed.
Lemma subset_catR (T : eqType) (h k : seq T) : {subset k <= h ++ k}.
Proof. move => x H. by rewrite mem_cat H orbT. Qed.
#[export]
Hint Resolve subset_catL subset_catR : core.
Lemma subset_tl (T : eqType) z (l : seq T) : {subset l <= z :: l}.
Proof. move => x y. exact: mem_tail. Qed. 
#[export]
Hint Resolve subset_tl : core.

(* this should be eqv_clot_map, the other lemma should use the _inj suffix *)
Lemma eqv_clot_map' (aT rT : finType) (f : aT -> rT) (l : pairs aT) x y : 
  eqv_clot l x y -> eqv_clot (map_pairs f l) (f x) (f y).
Proof.
  rewrite eqv_clotE /=. apply: equiv_ofE => {x y} x y H.
  apply: eqv_clot_pair. by apply/mapP; exists (x,y).
Qed.

Lemma eqv_clot_iso (A B: finType) (h: bij A B) (l: pairs A):
  map_equiv h^-1 (eqv_clot l) =2 eqv_clot (map_pairs h l).
Proof.
  move => x y. rewrite /map_equiv/map_equiv_rel/=. apply/idP/idP.
  - move/(eqv_clot_map' h). by rewrite !bijK'.
  - move/(eqv_clot_map' h^-1). rewrite /map_pairs -map_comp map_id_in //. 
    move => {x y} x y /=. by rewrite !bijK -surjective_pairing.
Qed.

(* TOTHINK: eliminate? *)
Lemma equiv_of_sub (T : finType) (e1 e2 : rel T) :
  subrel e1 e2 -> reflexive e2 -> symmetric e2 -> transitive e2 -> subrel (equiv_of e1) e2.
Proof. 
  move => sub2 refl2 sym2 trans2 x y. case/connectP => p. 
  elim: p x => [x _ -> //|a p IHp x] /= /andP [/orP H] pth lst.
  apply: trans2 _ (IHp _ pth lst). case: H; last rewrite sym2; exact: sub2.
Qed.

Lemma equiv_of_sub' (T : finType) (e1 : rel T) (e2 : equiv_rel T) :
  subrel e1 e2 -> subrel (equiv_of e1) e2.
Proof. move => sub. apply: equiv_of_sub => //; auto using equiv_sym, equiv_trans. Qed.

(* TODO: preliminaries *)
Lemma eq_equiv (T : finType) (e : equiv_rel T) x y : x = y -> e x y.
Proof. by move->. Qed.

Lemma eqv_clot_trans (T: finType) (z x y: T) (l: pairs T): 
  eqv_clot l x z -> eqv_clot l z y -> eqv_clot l x y.
Proof. exact: equiv_trans. Qed.

#[export]
Instance equiv_rel_Equivalence T (e : equiv_rel T) : Equivalence [eta e].
Proof. split => // [x y|x y z]; by [rewrite equiv_sym | apply: equiv_trans]. Qed.
  
Lemma eqv_clot_hd (T: finType) (x y: T) (l: pairs T): eqv_clot ((x,y)::l) x y.
Proof. apply: eqv_clot_pair. exact: mem_head. Qed.

Lemma eqv_clot_hd' (T: finType) (x y: T) (l: pairs T): eqv_clot ((x,y)::l) y x.
Proof. symmetry. apply eqv_clot_hd. Qed.

Lemma eqv_clot_tl (T: finType) (x y: T) z (l: pairs T):
  eqv_clot l x y ->
  eqv_clot (z::l) x y.
Proof. exact: eqv_clot_subset. Qed.

Lemma ForallE (T : eqType) (P : T -> Prop) (s : list T) : 
  List.Forall P s <-> (forall x, x \in s -> P x).
Proof. 
  split. 
  - elim => //= {s} x s Px _ H. exact/all_cons.
  - elim: s => // x s IH /all_cons [Px Ps]. by constructor; auto.
Qed.

Lemma eqv_clot_subrel (T: finType) (h k: pairs T):
  List.Forall (fun p => eqv_clot k p.1 p.2) h ->
  subrel (eqv_clot h) (eqv_clot k).
Proof. rewrite ForallE=>H x y. rewrite eqv_clotE. apply equiv_of_sub'=> u v. exact (H (u,v)). Qed.

(* Better formulation ? *)
Lemma eqv_clot_eq (T: finType) (h k: pairs T):
  List.Forall (fun p => eqv_clot k p.1 p.2) h ->
  List.Forall (fun p => eqv_clot h p.1 p.2) k ->
  eqv_clot h =2 eqv_clot k.
Proof. move=> A B x y. by apply/idP/idP; apply eqv_clot_subrel. Qed.

Lemma kernel_eqv_clot {A: finType} {B:eqType} (l: pairs A) (f: A -> B):
  List.Forall (fun p => f p.1 = f p.2) l ->
  (forall x y, f x = f y -> eqv_clot l x y) ->
  (forall x y, reflect (kernel f x y) (eqv_clot l x y)).
Proof.
  move => /ForallE H1 H2 x y. apply: (iffP idP); last exact: H2.
  move => E. apply/kernelP. 
  suff: subrel (eqv_clot l) (EquivRelPack (kernel_equivalence f)) by apply.
  rewrite /eqv_clot -lock. apply equiv_of_sub'.
  by move => {E x y} x y /= /H1/eqP.
Qed.

Lemma eq_equiv_class (T : eqType) : equiv_class_of (@eq_op T). 
Proof. split => //. exact: eq_op_trans. Qed.
Canonical eqv_equiv (T : eqType) := EquivRelPack (@eq_equiv_class T).

Lemma eqv_clot_nothing (T : finType) (h : pairs T) :
  List.Forall (fun p => p.1 = p.2) h -> eqv_clot h =2 eq_op.
Proof.
  move => /ForallE H x y. rewrite eqv_clotE /= in H *. 
  apply/idP/idP; last by move/eqP->.
  by apply: equiv_ofE => /= u v /H /= ->.
Qed.

Lemma eqv_clot_nothing' (T : finType) (h : pairs T) :
  List.Forall (fun p => p.1 = p.2) h -> forall x y, eqv_clot h x y -> x=y.
Proof.
  intro H. apply eqv_clot_nothing in H.
  intros x y. rewrite H. apply /eqP. 
Qed.


(* TODO: move to preliminaries *)
Section eqv_inj.
  Variables (T1 T2 : finType) (e1 : rel T1) (e2 : rel T2) (f : T1 -> T2).
  Hypothesis eq_e : forall u v, e1 u v = e2 (f u) (f v).
  Hypothesis eq2E : forall u' v', e2 u' v' -> exists u v, u' = f u /\ v' = f v.
  Hypothesis f_inj : injective f. 

  Lemma equiv_of_ff x y : equiv_of e2 (f x) (f y) = equiv_of e1 x y.
  Proof.
    apply/idP/idP. 
    - case/connectP => p. elim: p x => /= [|u' p IH] x. 
      + by move => _ /f_inj ->. 
      + case/andP => A B C. case/orP : A => A.
        * move/eq2E : (A) => [?] [v] [_ ?]. subst. 
          apply: connect_trans (connect1 _) (IH _ B C). by rewrite /= !eq_e A.
        * move/eq2E : (A) => [v] [?] [? _]. subst. 
          apply: connect_trans (connect1 _) (IH _ B C). by rewrite /= !eq_e A orbT.
    - apply: equiv_of_transfer => {x y} u v H. apply: sub_equiv_of. by rewrite -eq_e.
  Qed.
  
  Lemma equiv_of_nn x y : x \notin codom f -> equiv_of e2 x y -> x = y.
  Proof.
    move => xf. case/connectP => p. elim: p x xf => /=; auto.
    move => z p _ x xf /andP[E _] _. apply: contraNeq xf => _.
    case/orP : E => /eq2E [?] [?] [? ?]; subst; exact: codom_f.
  Qed.

  Lemma equiv_of_fn x y : y \notin codom f -> equiv_of e2 (f x) y = false.
  Proof.
    move => yf. apply: contraNF (yf). rewrite equiv_sym/=. 
    move/equiv_of_nn -> => //. exact: codom_f.
  Qed.
End eqv_inj.

Lemma rel_of_pairs_map_eq (H G : eqType) (l : pairs G) (f : G -> H) :
  injective f ->
  forall u v, rel_of_pairs l u v = rel_of_pairs (map_pairs f l) (f u) (f v).
Proof.
  move => f_inj u v. rewrite /rel_of_pairs/= /map_pairs.
  apply/idP/mapP => [uv_l|[[u' v'] uv_l]]; first by exists (u,v).
  case. by do 2 move/f_inj ->.
Qed.

Lemma rel_of_pairs_mapE (H G : eqType) (l : pairs G) (f : G -> H) (u' v' : H) :
    rel_of_pairs (map_pairs f l) u' v' -> exists u v : G, u' = f u /\ v' = f v.
Proof.
  rewrite /rel_of_pairs/= /map_pairs. case/mapP => [[u v]] /= ? [? ?]. by exists u; exists v.
Qed.

Lemma eqv_clot_map (H G : finType) (x y : G) (l : pairs G) (f : G -> H) : 
  injective f ->
  eqv_clot (map_pairs f l) (f x) (f y) = eqv_clot l x y.
Proof.
  move => inj_f. rewrite /eqv_clot -!lock /=. apply: equiv_of_ff => //.
  exact: rel_of_pairs_map_eq.
  exact: rel_of_pairs_mapE.
Qed.
  
Lemma eqv_clot_mapF (H G : finType) (x : G) (y : H) (l : pairs G) (f : G -> H) : 
  injective f -> y \notin codom f ->
  eqv_clot (map_pairs f l) (f x) y = false.
Proof.
  move => inj_f. rewrite /eqv_clot -!lock /=. apply: equiv_of_fn => //.
  exact: rel_of_pairs_mapE.
Qed.

Lemma eqv_clot_map_eq (H G : finType) (x y : H) (l : pairs G) (f : G -> H) : 
  x \notin codom f ->  
  eqv_clot (map_pairs f l) x y = (x == y).
Proof.
  move => cd_x. apply/idP/eqP; last by move => ->.
  rewrite /eqv_clot -!lock /=. apply: equiv_of_nn cd_x => //.
  exact: rel_of_pairs_mapE.
Qed.

Lemma eqv_clot_cat (A: finType) (h k: pairs A):
  equiv_comp (eqv_clot (map_pairs (pi (eqv_clot h)) k)) =2 eqv_clot (h++k).
Proof.
  move => x y. symmetry. rewrite /equiv_comp map_equivE/= !eqv_clotE /=. 
  set e1 := rel_of_pairs _. set e2 := rel_of_pairs _. apply/idP/idP. 
  - apply: equiv_of_transfer => {x y} u v. 
    rewrite /e1/rel_of_pairs/= mem_cat. case/orP => H.
    + apply: eq_equiv. apply/eqquotP. rewrite eqv_clotE. exact: sub_equiv_of.
    + apply: sub_equiv_of. apply/mapP. by exists (u,v).
  - suff S (u v : quot (eqv_clot h)):
      equiv_of e2 u v -> equiv_of e1 (repr u) (repr v).
    { move/S => H.  
      apply: equiv_trans (equiv_trans _ _). 2: exact: H.
      rewrite /= -eqv_clotE. exact: (eqv_clot_subset h) (piK' _ _). 
      rewrite /= -eqv_clotE equiv_sym. exact: (eqv_clot_subset h) (piK' _ _). }
    apply: equiv_of_transfer => {u v} u v /mapP [[u0 v0] H0] [-> ->].
    apply: equiv_trans (equiv_trans _ _). 
    2:{ rewrite /= -eqv_clotE. apply: (eqv_clot_subset k) _. done. 
        rewrite eqv_clotE. apply: sub_equiv_of. exact: H0. }
    rewrite equiv_sym. all: rewrite /= -eqv_clotE; exact: (eqv_clot_subset h) (piK' _ _).
Qed.

(* Inversion lemmas for a single pair *)

Lemma eqv_clot1E (T : finType) (u v x y : T) : 
 eqv_clot [:: (u, v)] x y -> [\/ x = y, x = u /\ y = v | x = v /\ y = u].
Proof.
  rewrite eqv_clotE.  case/connectP => p. elim: p x => //=.
  - firstorder.
  - move => a p IHp x /andP[]. rewrite /rel_of_pairs/= !inE !xpair_eqE => A pth lst.
    move: (IHp _ pth lst). case/orP : A => /andP [] /eqP ? /eqP ?; subst; firstorder.
Qed.

Lemma eqv_clot_injL (T1 T2 : finType) (x y : T1) o i :
      inl T2 x = inl y %[mod eqv_clot [:: (inl o,inr i)]] -> x = y. 
Proof. move/eqquotP. by case/eqv_clot1E => [[]|[//]|[//]]. Qed.

Lemma eqv_clot_injR (T1 T2 : finType) (x y : T2) o i :
      inr T1 x = inr y %[mod eqv_clot [:: (inl o,inr i)]] -> x = y. 
Proof. move/eqquotP. by case/eqv_clot1E => [[]|[//]|[//]]. Qed. 

Lemma eqv_clot_LR (T1 T2 : finType) (x : T1) (y : T2) o i :
      inl T2 x = inr T1 y %[mod eqv_clot [:: (inl o,inr i)]] -> x = o /\ y = i. 
Proof. move/eqquotP. by case/eqv_clot1E => [//|[[->][->]]|[//]]. Qed.

(* TODO: provide inversion lemmas for the case of two pairs (at least
for the case of inl/inr pairs as used in [par2] *)

(** Tactics for showing that some concrete equivalence closure
contains a given pair (list of pairs) *)

Ltac eqv := lazymatch goal with
            | |- is_true (equiv (eqv_clot ((?x,?y)::_)) ?x' ?y') =>
              reflexivity
              || (unify x x' ; unify y y'; apply: eqv_clot_hd)
              || (unify x y' ; unify y x'; apply: eqv_clot_hd')
              || apply: eqv_clot_tl; eqv
            end.
Ltac leqv := solve [apply List.Forall_cons;[eqv|leqv] | apply List.Forall_nil].

Global Opaque eqv_clot.
