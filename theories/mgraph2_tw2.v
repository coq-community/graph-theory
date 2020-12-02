Require Import RelationClasses Setoid.
From mathcomp Require Import all_ssreflect.
Require Import edone set_tac finite_quotient preliminaries digraph sgraph treewidth minor equiv.
Require Import setoid_bigop structures mgraph pttdom ptt mgraph2 skeleton.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

Section Subalgebra.
Variable (Lv : comMonoid) (Le : elabelType).
Notation graph := (graph Lv Le).
Notation graph2 := (graph2 Lv Le).

Implicit Types (G H : graph) (U : sgraph) (T : forest).

Open Scope implicit_scope.

(** * Subalgebra of Tree-Width 2 Graphs *)

Arguments sdecomp T G B : clear implicits.

Definition compatible (T : forest) (G : graph2) (B : T -> {set G}) := 
  exists t, (input \in B t) && (output \in B t).

Lemma sdecomp_sskel (T : forest) (G : graph2) (B : T -> {set G}) :
  sdecomp T (sskeleton G) B <-> (sdecomp T G B /\ compatible B).
Proof.
  split. 
  - case => [D1 D2 D3]. split. split => //. 
    + move => x y /= xy. apply: D2. by rewrite /edge_rel/= xy. 
    + case: (altP (input =P output :> skeleton G)) => E. 
      * case: (D1 input) => t Ht. exists t. by rewrite -E !Ht.
      * suff: (input : sskeleton G) -- output by apply: D2. by rewrite /edge_rel/= E !eqxx.
  - move => [[D1 D2 D3] C]. split => //= x y. case/or3P; first exact: D2.
    + case/and3P => ? /eqP E1 /eqP E2. by subst. 
    + case/and3P => ? /eqP E1 /eqP E2. subst. 
      case: C => t. rewrite andbC. by exists t.
Qed.

Lemma hom_eqL (V : finType) (e1 e2 : rel V) (G : sgraph) (h : V -> G) 
      (e1_sym : symmetric e1) (e1_irrefl : irreflexive e1) 
      (e2_sym : symmetric e2) (e2_irrefl : irreflexive e2):
  e1 =2 e2 ->
  @hom_s (SGraph e1_sym e1_irrefl) G h -> 
  @hom_s (SGraph e2_sym e2_irrefl) G h.
Proof. move => E hom_h x y. rewrite /edge_rel/= -E. exact: hom_h. Qed.


Lemma skel_union_join (G1 G2 : graph) : @sk_rel _ _ (union G1 G2) =2 @join_rel G1 G2.
Proof.
  move => [x|x] [y|y] /=. 
  - rewrite /edge_rel/=/sk_rel sum_eqE. 
    case: (boolP (x == y)) => //= E. apply/existsP/existsP. 
    + move => [[e|e]]; rewrite !inE //= !sum_eqE. by exists e; rewrite !inE.
    + move => [e] H. exists (inl e). by rewrite !inE /= !sum_eqE in H *. 
  - apply: contraTF isT => /existsP [[e|e]]; by rewrite !inE //= andbC.
  - apply: contraTF isT => /existsP [[e|e]]; by rewrite !inE //= andbC.
  - rewrite /edge_rel/=/sk_rel sum_eqE. 
    case: (boolP (x == y)) => //= E. apply/existsP/existsP. 
    + move => [[e|e]]; rewrite !inE //= !sum_eqE. by exists e; rewrite !inE.
    + move => [e] H. exists (inr e). by rewrite !inE /= !sum_eqE in H *. 
Qed.

Section Quotients. 
  Variables (G1 G2 : graph2).
  
  Let P : {set union G1 G2} := [set unl input; unl output; unr input; unr output].

  Definition admissible (eqv : rel (union G1 G2)) := 
    forall x y, eqv x y -> x = y \/ [set x;y] \subset P.

  Lemma admissible_eqv_clot (l: pairs (union G1 G2)):
    (forall p, p \in l -> p.1 \in P /\ p.2 \in P) -> admissible (eqv_clot l).
  Proof.
    move => H x y. rewrite eqv_clotE. case/connectP => p.
    have relE u v : rel_of_pairs l u v -> ((u \in P) * (v \in P)) %type. 
    { by move /H => /= [-> ->]. }
    elim: p x => /= [x _ -> //|z p IH x /andP [E pth_p] lst_p]; first by left.
    right. rewrite subUset !sub1set. case: (IH _ pth_p lst_p) => [Z|S]; subst. 
    - rewrite -Z. case/orP : E => E; by rewrite !(relE _ _ E).
    - case/orP: E => E; rewrite (relE _ _ E) /=; by abstract (set_tac).
  Qed.
 
  Lemma decomp_quot (T1 T2 : forest) D1 D2 (e : equiv_rel (union G1 G2)): 
    sdecomp T1 (sskeleton G1) D1 -> sdecomp T2 (sskeleton G2) D2 -> 
    width D1 <= 3 -> width D2 <= 3 ->
    admissible e -> #|[set pi e x | x in P]| <= 3 ->
    exists T D, [/\ sdecomp T (skeleton (merge _ e)) D, 
              width D <= 3 & exists t, 
              D t = [set \pi x | x in P]].
  Proof using. 
    move => /sdecomp_sskel [dec1 comp1] /sdecomp_sskel [dec2 comp2] W1 W2 adm_e collapse_P.
    move: comp1 comp2 => [t1 /andP[t1_in t1_out]] [t2 /andP[t2_in t2_out]].
    pose T := tjoin T1 T2.
    pose D : tjoin T1 T2 -> {set sjoin G1 G2}:= decompU D1 D2.
    have dec_D: sdecomp T (sjoin G1 G2) D by exact: join_decomp. 
    have dis_t1_t2 : ~~ connect (@sedge T)(inl t1) (inr t2) by rewrite join_disc.
    have dis_T12 : {in [set inl t1;inr t2] &, forall x y, x != y -> ~~ connect (@sedge T) x y}.
    { move => [?|?] [?|?] /setUP[] /set1P-> /setUP[]/set1P ->. 
      all: by rewrite ?eqxx // => _; rewrite sconnect_sym. }
    pose T' := @tlink T _ dis_T12.
    pose D' := decompL D P : _ -> {set sjoin G1 G2}.
    have dec_D' : sdecomp T' (sjoin G1 G2) D'.
    { apply: decomp_link => //.
      apply/subsetP => x.
      rewrite !inE -!orbA => /or4P [] /eqP->.
      all: apply/bigcupP; solve 
        [ by exists (inl t1) => //; rewrite ?inE ?mem_imset ?eqxx 
        | by exists (inr t2) => //; rewrite ?inE ?mem_imset ?eqxx]. }
    pose h := pi e : skeleton (union G1 G2) -> skeleton (merge _ e).
    exists T'. exists (rename D' h); split; last by exists None.
    - apply: rename_decomp => //. 
      + apply: hom_eqL (pi_hom (e := e)). exact: skel_union_join.
      + exact: pi_surj.
      + move => x y. move/sk_rel_mergeE => [? [x0] [y0] /= [? ? ?]]. 
        exists x0;exists y0. split => //. by rewrite /edge_rel/= -skel_union_join.
      + move => x y. move/eqquotP => /=. case/adm_e => [<-|A].
        * case: (sbag_cover dec_D' x) => t Ht. left. exists t. by rewrite Ht.
        * left. exists None. by rewrite /= -!sub1set -subUset. 
    - rewrite /width (bigop.bigID (pred1 None)).
      rewrite bigop.big_pred1_eq. rewrite geq_max. apply/andP;split => //.
      + rewrite (bigop.reindex Some) /=.
        * apply: (@leq_trans (maxn (width D1) (width D2))); last by rewrite geq_max W1 W2.
          apply: leq_trans (join_width _ _). 
          apply: bigmax_leq_pointwise => t _. exact: leq_imset_card.
        * apply: subon_bij; last by (apply bij_on_codom => //; exact: (inl t1)). 
          by move => [x|]; rewrite !in_simpl // codom_f. 
  Qed.
  
  Lemma decomp_par2 (T1 T2 : forest) D1 D2 : 
    sdecomp T1 (sskeleton G1) D1 -> sdecomp T2 (sskeleton G2) D2 -> 
    width D1 <= 3 -> width D2 <= 3 ->
    exists T D, [/\ sdecomp T (sskeleton (G1 ∥ G2)) D & width D <= 3].
  Proof using.
    move => dec1 dec2 W1 W2.
    case: (decomp_quot (e:=eqv_clot [:: (unl input, unr input); (unl output, unr output)])
                       dec1 dec2 W1 W2 _ _).
    - apply admissible_eqv_clot. case => u v. 
      rewrite !inE /= !xpair_eqE => /orP [] /andP [/eqP -> /eqP->]; by rewrite !eqxx.
    - pose P' : {set union G1 G2} := [set unl input; unl output].
      apply: (@leq_trans #|P'|); last by rewrite cards2; by case (_ != _).
      apply: (@leq_trans #|[set (\pi x : G1 ∥ G2) | x in P']|); last exact: leq_imset_card.
      apply: subset_leq_card.
      apply/subsetP => ? /imsetP [x H1 ->]. case/setUP : H1 => H1; first case/setUP : H1 => H1.
      * by rewrite mem_imset.
      * move/set1P : H1 => ->. apply/imsetP. exists (unl input); first by rewrite !inE eqxx ?orbT.
        apply/eqquotP. eqv. 
      * move/set1P : H1 => ->. apply/imsetP. exists (unl output); first by rewrite !inE eqxx ?orbT.
        apply/eqquotP. eqv. 
    - move => T [D] [A B [t C]]. exists T. exists D. split => //. 
      apply/sdecomp_sskel. split => //. 
      exists t. by rewrite C !mem_imset // !inE ?eqxx ?orbT.
  Qed.

  Lemma decomp_dot2 (T1 T2 : forest) D1 D2 : 
    sdecomp T1 (sskeleton G1) D1 -> sdecomp T2 (sskeleton G2) D2 -> 
    width D1 <= 3 -> width D2 <= 3 ->
    exists T D, [/\ sdecomp T (sskeleton (G1 · G2)) D & width D <= 3].
  Proof using.
    move => dec1 dec2 W1 W2.
    case: (decomp_quot (e:=eqv_clot [:: (unl output, unr input)]) dec1 dec2 W1 W2 _ _).
    - apply admissible_eqv_clot. case => u v.
      rewrite !inE /= !xpair_eqE => /andP [/eqP -> /eqP->]; by rewrite !eqxx.
    - pose P' : {set union G1 G2} := [set unl input; unl output; unr output].
      apply: (@leq_trans #|P'|); last apply cards3.
      apply: (@leq_trans #|[set (\pi x : G1 · G2) | x in P']|); last exact: leq_imset_card.
      apply: subset_leq_card.
      apply/subsetP => ? /imsetP [x H1 ->]. move: H1. 
      rewrite /P -!setUA [[set _;_]]setUC !setUA. case/setUP => H1.
      * by rewrite mem_imset.
      * move/set1P : H1 => ->. apply/imsetP. exists (unl output); first by rewrite !inE eqxx ?orbT.
        apply/eqquotP. eqv. 
    - move => T [D] [A B [t C]]. exists T. exists D. split => //. 
      apply/sdecomp_sskel. split => //. 
      exists t. by rewrite C !mem_imset // !inE ?eqxx ?orbT.
  Qed.

End Quotients.

Lemma decomp_cnv (G : graph2) T D : 
  sdecomp T (sskeleton G) D -> sdecomp T (sskeleton (G°)) D.
Proof. 
  move/sdecomp_sskel => [dec cmp]. apply/sdecomp_sskel; split => //. 
  move: cmp => [t] H. exists t => /=. by rewrite andbC.
Qed.

Lemma decomp_dom (G : graph2) T D : 
  sdecomp T (sskeleton G) D -> sdecomp T (sskeleton (dom G)) D.
Proof. 
  move/sdecomp_sskel => [dec cmp]. apply/sdecomp_sskel; split => //. 
  move: cmp => [t] /andP [H _]. exists t => /=. by rewrite !H. 
Qed.

Theorem eval_TW2 A (f: A -> graph2):
  (forall a, exists T D, [/\ sdecomp T (sskeleton (f a)) D & width D <= 3]) ->
  forall u, exists T D, [/\ sdecomp T (sskeleton (eval f u)) D & width D <= 3].
Proof.
  move => Hf. elim => [u IHu v IHv | u IHu v IHv | u IHu | u IHu | | | a].
  - move: IHu IHv => [T1] [D1] [? ?] [T2] [D2] [? ?].
    exact: (decomp_dot2 (D1 := D1) (D2 := D2)).
  - move: IHu IHv => [T1] [D1] [? ?] [T2] [D2] [? ?].
    exact: (decomp_par2 (D1 := D1) (D2 := D2)).
  - move: IHu => [T] [D] [D1 D2]. exists T. exists D. split => //. 
    exact: decomp_cnv. 
  - move: IHu => [T] [D] [D1 D2]. exists T. exists D. split => //. 
    exact: decomp_dom. 
  - apply: decomp_small. by rewrite card_unit.
  - apply: decomp_small. by rewrite card_sum card_unit.
  - apply Hf. 
Qed.

End Subalgebra.

Section s.
Variable A: Type.
Let graph_of_term: term A -> graph2 unit (flat A) := eval (fun a : flat A => g2_var _ a). 

Theorem graph_of_TW2 (u : term A) : 
  exists T D, [/\ @sdecomp T (sskeleton (graph_of_term u)) D & width D <= 3].
Proof.
  apply eval_TW2 => a.
  apply: decomp_small. by rewrite card_sum card_unit.  
Qed.

Lemma sskel_K4_free (u : term A) : K4_free (sskeleton (graph_of_term u)).
Proof.
  case: (graph_of_TW2 u) => T [B] [B1 B2]. 
  exact: TW2_K4_free B1 B2.
Qed.

Lemma skel_K4_free (u : term A) : K4_free (skeleton (graph_of_term u)).
Proof.
  apply: minor_K4_free (@sskel_K4_free u).
  exact: sub_minor (skel_sub _).
Qed.

(* TODO: define the subalgebra as a ptt_algebra? (with sigma types) *)

End s.
