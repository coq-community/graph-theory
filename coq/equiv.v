Require Import RelationClasses Setoid Morphisms.

From mathcomp Require Import all_ssreflect.
Require Import finite_quotient preliminaries.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 


Lemma eq_piK (T : choiceType) (e : equiv_rel T) z : e z (repr (\pi_({eq_quot e}) z)).
Proof. by case: piP => /= y /eqquotP. Qed.

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

Section equiv_comp.
  Variables (T: choiceType) (e: equiv_rel T) (e': equiv_rel {eq_quot e}).
  Definition equiv_comp: simpl_rel T := [rel x y | e' (\pi x) (\pi y)].
  Lemma equiv_comp_class: equiv_class_of equiv_comp.
  Proof. split => [x|x y|x y z]. apply: equiv_refl. apply: equiv_sym. apply: equiv_trans. Qed.
  Canonical Structure equiv_comp_rel := EquivRelPack equiv_comp_class.
  Lemma equiv_comp_pi (x: T):
    x = repr (repr (\pi_{eq_quot e'} (\pi_{eq_quot e} x)))
             %[mod_eq equiv_comp_rel]. 
  Proof. apply/eqquotP. rewrite /equiv_comp_rel/= reprK. exact: eq_piK. Qed.
End equiv_comp.


Notation "\pie x" := (\pi_{eq_quot _} x) (at level 30). 


Definition pairs A := seq (A*A).
Definition map_pairs A B (f: A -> B): pairs A -> pairs B := map (fun x => (f x.1,f x.2)). 


Definition rel_of_pairs (A : eqType) (l : pairs A) : rel A := [rel x y | (x,y) \in l].
Definition eqv_clot (T : finType) (l : pairs T) : equiv_rel T :=
  (* equiv_of_equivalence (rel_of_pairs l). *)
  locked [equiv_rel of equiv_of (rel_of_pairs l)].

Lemma eqv_clotE (T : finType) (l : pairs T) x y : 
  eqv_clot l x y = equiv_of (rel_of_pairs l) x y.
Proof. by rewrite /eqv_clot -lock. Qed.

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

Lemma eq_equiv (T : finType) (e : equiv_rel T) x y : x = y -> e x y.
Proof. by move->. Qed.


Lemma eqv_clot_trans (T: finType) (z x y: T) (l: pairs T): eqv_clot l x z -> eqv_clot l z y -> eqv_clot l x y.
Proof. exact: equiv_trans. Qed.

Instance equiv_rel_Equivalence T (e : equiv_rel T) : Equivalence [eta e].
Proof. split => // [x y|x y z]; by [rewrite equiv_sym | apply: equiv_trans]. Qed.
  
Lemma eqv_clot_hd (T: finType) (x y: T) (l: pairs T): eqv_clot ((x,y)::l) x y.
Proof. 
  rewrite eqv_clotE. apply: sub_equiv_of. by rewrite /rel_of_pairs //= mem_head. 
Qed.

Lemma eqv_clot_hd' (T: finType) (x y: T) (l: pairs T): eqv_clot ((x,y)::l) y x.
Proof. symmetry. apply eqv_clot_hd. Qed.

Lemma rel_of_pairs_mono (T : finType) (l l' : pairs T) :
  {subset l <= l'} -> subrel (rel_of_pairs l) (rel_of_pairs l').
Proof. move => sub_l x y. exact: sub_l. Qed.

Lemma subset_tl (T : eqType) z (l : seq T) : {subset l <= z :: l}.
Proof. move => x y. exact: mem_tail. Qed. 
Hint Resolve subset_tl.

Lemma eqv_clot_tl (T: finType) (x y: T) z (l: pairs T):
  eqv_clot l x y ->
  eqv_clot (z::l) x y.
Proof. 
  rewrite !eqv_clotE. apply: equiv_of_sub' => /=. 
  exact: sub_trans (rel_of_pairs_mono _) (@sub_equiv_of _ _).
Qed.

Lemma ForallE (T : eqType) (P : T -> Prop) (s : list T) : 
  List.Forall P s <-> (forall x, x \in s -> P x).
Proof. 
  split. 
  - elim => //= {s} x s Px _ H. exact/all_cons.
  - elim: s => // x s IH /all_cons [Px Ps]. by constructor; auto.
Qed.

(* Better formulation ? *)
Lemma eqv_clot_eq (T: finType) (h k: pairs T):
  List.Forall (fun p => eqv_clot k p.1 p.2) h ->
  List.Forall (fun p => eqv_clot h p.1 p.2) k ->
  eqv_clot h =2 eqv_clot k.
Proof.
  rewrite !ForallE /= => A B x y. apply/idP/idP; rewrite eqv_clotE. 
  all: apply: equiv_of_sub' => u v; solve [exact: (A (u,v))|exact:(B (u,v))].
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


(* Ltac eqv := solve [reflexivity|apply: eqv_clot_hd|apply: eqv_clot_hd'|apply: eqv_clot_tl; eqv]. *)
Ltac eqv := lazymatch goal with
            | |- is_true (equiv (eqv_clot ((?x,?y)::_)) ?x' ?y') =>
              reflexivity
              || (unify x x' ; unify y y'; apply: eqv_clot_hd)
              || (unify x y' ; unify y x'; apply: eqv_clot_hd')
              || apply: eqv_clot_tl; eqv
            end.
Ltac leqv := solve [apply List.Forall_cons;[eqv|leqv] | apply List.Forall_nil].

Opaque eqv_clot.

Lemma mod_exchange (T : choiceType) (e1 e2 : equiv_rel T) x y : 
  e1 =2 e2 -> x = y %[mod_eq e2] -> x = y %[mod_eq e1].
Proof. move => E M1. apply/eqquotP. rewrite E. apply/eqquotP. exact: M1. Qed.


