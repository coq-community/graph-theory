From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries sgraph minor multigraph skeleton.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 

Implicit Types (G H : graph) (U : sgraph) (T : forest).

(** * Subalgebra of Tree-Width 2 Graphs *)

(** ** Closure Properties for operations *)

Arguments sdecomp T G B : clear implicits.

Definition compatible (T : forest) (G : graph2) (B : T -> {set G}) := 
  exists t, (g_in \in B t) && (g_out \in B t).

Lemma sdecomp_sskel (T : forest) (G : graph2) (B : T -> {set G}) :
  sdecomp T (sskeleton G) B <-> (sdecomp T G B /\ compatible B).
Proof.
  split. 
  - case => [D1 D2 D3]. split. split => //. 
    + move => x y /= xy. apply: D2. by rewrite /= xy. 
    + case: (altP (g_in =P g_out :> skeleton G)) => E. 
      * case: (D1 g_in) => t Ht. exists t. by rewrite -E !Ht.
      * suff: (g_in : sskeleton G) -- g_out by apply: D2. by rewrite /= E !eqxx.
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
Proof. move => E hom_h x y. rewrite /= -E. exact: hom_h. Qed.


Lemma skel_union_join (G1 G2 : graph) : sk_rel (union G1 G2) =2 @join_rel G1 G2.
Proof.
  move => [x|x] [y|y] /=. 
  - rewrite /sk_rel sum_eqE. 
    case: (boolP (x == y)) => //= E. apply/existsP/existsP. 
    + move => [[e|e]]; rewrite !inE //= !sum_eqE. by exists e; rewrite !inE.
    + move => [e] H. exists (inl e). by rewrite !inE /= !sum_eqE in H *. 
  - apply: contraTF isT => /andP [_ /existsP [[e|e]]]; by rewrite !inE //= andbC.
  - apply: contraTF isT => /andP [_ /existsP [[e|e]]]; by rewrite !inE //= andbC.
  - rewrite /sk_rel sum_eqE. 
    case: (boolP (x == y)) => //= E. apply/existsP/existsP. 
    + move => [[e|e]]; rewrite !inE //= !sum_eqE. by exists e; rewrite !inE.
    + move => [e] H. exists (inr e). by rewrite !inE /= !sum_eqE in H *. 
Qed.

Section Quotients. 
  Variables (G1 G2 : graph2).
  
  Let P : {set union G1 G2} := [set inl g_in; inl g_out; inr g_in; inr g_out].

  Definition admissible (eqv : rel (union G1 G2)) := 
    forall x y, eqv x y -> x = y \/ [set x;y] \subset P. 
 
  Lemma decomp_quot (T1 T2 : forest) D1 D2 (e : equiv_rel (union G1 G2)): 
    sdecomp T1 (sskeleton G1) D1 -> sdecomp T2 (sskeleton G2) D2 -> 
    width D1 <= 3 -> width D2 <= 3 ->
    admissible e -> #|[set \pi_{eq_quot e} x | x in P]| <= 3 ->
    exists T D, [/\ sdecomp T (skeleton (merge_def _ e)) D, 
              width D <= 3 & exists t, 
              D t = [set \pi_{eq_quot e} x | x in P]].
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
    pose h := \pi_{eq_quot e} : skeleton (union G1 G2) -> skeleton (merge_def _ e).
    exists T'. exists (rename D' h); split; last by exists None.
    - apply: rename_decomp => //. 
      + apply: hom_eqL (pi_hom e). exact: skel_union_join.
      + exact: emb_surj.
      + move => x y. move/sk_rel_mergeE => [? [x0] [y0] /= [? ? ?]]. 
        exists x0;exists y0. split => //. by rewrite -skel_union_join.
      + move => x y. move/eqmodP => /=. case/adm_e => [<-|A].
        * case: (sbag_cover dec_D' x) => t Ht. exists t. by rewrite Ht.
        * exists None. rewrite /= -!sub1set -subUset. done.
    - rewrite /width (bigID (pred1 None)).
      rewrite big_pred1_eq. rewrite geq_max. apply/andP;split => //.
      + rewrite (reindex Some) /=.
        * apply: (@leq_trans (maxn (width D1) (width D2))); last by rewrite geq_max W1 W2.
          apply: leq_trans (join_width _ _). 
          apply: max_mono => t. exact: leq_imset_card.
        * apply: subon_bij; last by (apply bij_on_codom => //; exact: (inl t1)). 
          by move => [x|]; rewrite !in_simpl // codom_f. 
  Qed.

  Definition par2_eqv : rel (union G1 G2) :=
    fun x y => (x == y) ||
      if (g_in != g_out :> G1) && (g_in != g_out :> G2)
      then [set x; y] \in [set [set inl g_in; inr g_in]; [set inl g_out; inr g_out]]
      else [set x; y] \subset [set inl g_in; inl g_out; inr g_in; inr g_out].

  Definition par2_eqv_refl : reflexive par2_eqv.
  Proof. by move=> ?; rewrite /par2_eqv eqxx. Qed.

  Lemma par2_eqv_sym : symmetric par2_eqv.
  Proof. move=> x y. by rewrite /par2_eqv [[set y; x]]setUC [y == x]eq_sym. Qed.

  Definition par2_eqv_trans : transitive par2_eqv.
  Proof using.
    move=> y x z. rewrite /par2_eqv.
    case/altP: (x =P y) => [<-//|xNy/=]. case/altP: (y =P z) => [<-->//|yNz/=].
    case/boolP: ((g_in != g_out :> G1) && (g_in != g_out :> G2)).
    - rewrite !inE -(implyNb (x == z)).
      case/andP=> /negbTE iNo1 /negbTE iNo2 Hxy Hyz. apply/implyP=> xNz.
      move: Hxy xNy. rewrite 2!eqEcard 2!subUset 4!sub1set !inE.
      case/orP => /andP[]/andP[] /orP[]/eqP ? /orP[]/eqP ? _; subst=> // _.
      all: move: Hyz xNz yNz; rewrite 2!eqEcard 2!subUset 4!sub1set !inE.
      all: rewrite ?eqxx ?sum_eqE ?[g_out == g_in]eq_sym ?iNo1 ?iNo2 ?orbT ?orbF /=.
      all: case/andP => /orP[]/eqP-> _; by rewrite !eqxx.
    - rewrite -implyNb => _ Hxy Hyz. apply/implyP=> xNz.
      rewrite subUset !sub1set. apply/andP; split.
      + apply: (subsetP Hxy). by rewrite !inE eqxx.
      + apply: (subsetP Hyz). by rewrite !inE eqxx.
  Qed.

  Canonical par2_eqv_equivalence :=
    EquivRel par2_eqv par2_eqv_refl par2_eqv_sym par2_eqv_trans.

  Lemma par2_eqv_io :
    (par2_eqv (inl g_in) (inr g_in)) * (par2_eqv (inl g_out) (inr g_out)).
  Proof.
    rewrite /par2_eqv/=. case: ifP => _.
    - by rewrite !inE !eqxx.
    - by rewrite !subUset !sub1set !inE !eqxx.
  Qed.

  Definition par2_eq (x y : union G1 G2) :=
    match x,y with
    | inl x, inr y => (x == g_in) && (y == g_in) || (x == g_out) && (y == g_out)
    | _,_ => false
    end.

  Lemma par2_equiv_of : par2_eqv =2 equiv_of par2_eq.
  Proof using.
    move=> x y. apply/idP/idP.
    - rewrite /par2_eqv. case/altP: (x =P y) => [<- _|xNy]/=; first exact: connect0.
      case: ifP => [_|/negbT].
      + rewrite !inE 2!eqEcard 2!subUset 4!sub1set !inE => H.
        case/orP: H xNy => /andP[]/andP[]/orP[]/eqP->/orP[]/eqP-> _.
        all: rewrite ?eqxx // ?[equiv_of _ (inr _) _]equiv_of_sym => _.
        all: apply: sub_equiv_of; by rewrite /par2_eq 2!eqxx.
      + rewrite negb_and 2!negbK. case/orP=> [/eqP Eio1|/eqP Eio2].
        * rewrite -Eio1 setUid => Exy.
          have Rio2 : equiv_of par2_eq (inr g_out) (inr g_in).
          { apply: (@equiv_of_trans _ _ (inl g_in)); first rewrite equiv_of_sym Eio1;
            by apply: sub_equiv_of; rewrite /par2_eq !eqxx. }
          move: Exy xNy; rewrite subUset 2!sub1set !inE -2!orbA.
          case/andP=> /or3P[]/eqP-> /or3P[]/eqP->.
          all: rewrite ?eqxx // ?[equiv_of _ _ (inl _)]equiv_of_sym => _.
          all: try solve [apply: (@sub_equiv_of _ _ (inl _));
                          by rewrite /par2_eq -?Eio1 !eqxx].
          by rewrite equiv_of_sym.
        * rewrite -setUA -Eio2 setUid => Exy.
          have Rio2 : equiv_of par2_eq (inl g_out) (inl g_in).
          { apply: (@equiv_of_trans _ _ (inr g_out)); last rewrite equiv_of_sym -Eio2;
            by apply: sub_equiv_of; rewrite /par2_eq !eqxx. }
          move: Exy xNy; rewrite subUset 2!sub1set !inE -2!orbA.
          case/andP=> /or3P[]/eqP-> /or3P[]/eqP->.
          all: rewrite ?eqxx // ?[equiv_of _ (inr _) _]equiv_of_sym => _.
          all: try solve [apply: (@sub_equiv_of _ _ (inl _));
                          by rewrite /par2_eq -?Eio2 !eqxx].
          by rewrite equiv_of_sym.
    - case/connectP=> p. elim: p x; first by [move=> x _ ->; exact: par2_eqv_refl].
      move=> /= a p IH x /andP[x_a p_path p_last].
      have {p_path p_last} : par2_eqv a y by exact: IH. apply: par2_eqv_trans.
      move: x a x_a => [x|x] [a|a] //=; first rewrite orbF.
      all: case/orP=> /andP[/eqP-> /eqP->].
      all: by rewrite ?par2_eqv_io // par2_eqv_sym par2_eqv_io.
  Qed.

  Lemma par2_eqv_ii x y : 
    x = g_in :> G1 -> y = g_in :> G2 ->
    par2_eqv (inl x) (inr y).
  Proof.
    move => -> ->. rewrite par2_equiv_of. apply: sub_equiv_of.
      by rewrite /par2_eq !eqxx. 
  Qed.
  
  Lemma par2_eqv_oo x y : 
    x = g_out :> G1 -> y = g_out :> G2 ->
    par2_eqv (inl x) (inr y).
  Proof.
    move => -> ->. rewrite par2_equiv_of. apply: sub_equiv_of.
      by rewrite /par2_eq !eqxx. 
  Qed.

  Definition par2 := 
    {| graph_of := merge (union G1 G2) par2_eqv ;
       g_in := \pi_{eq_quot par2_eqv} (inl g_in);
       g_out := \pi_{eq_quot par2_eqv} (inl g_out) |}.

  Lemma par2_eqvP : admissible par2_eqv.
  Proof using. 
    move=> x y. case/orP=> [/eqP|]; first by left. case: ifP; last by right.
    rewrite !inE => _ /orP[]/eqP->; by right; rewrite subUset !sub1set !inE !eqxx.
  Qed.

  Lemma decomp_par2 (T1 T2 : forest) D1 D2 : 
    sdecomp T1 (sskeleton G1) D1 -> sdecomp T2 (sskeleton G2) D2 -> 
    width D1 <= 3 -> width D2 <= 3 ->
    exists T D, [/\ sdecomp T (sskeleton (par2)) D & width D <= 3].
  Proof using.
    move => dec1 dec2 W1 W2.
    case: (decomp_quot (e:= [equiv_rel of par2_eqv]) dec1 dec2 W1 W2 _ _).
    - exact: par2_eqvP.
    - pose P' : {set union G1 G2} := [set inl g_in; inl g_out].
      apply: (@leq_trans #|P'|); last by rewrite cards2; by case (_ != _).
      apply: (@leq_trans #|[set (\pi x : par2) | x in P']|); last exact: leq_imset_card.
      apply: subset_leq_card.
      apply/subsetP => ? /imsetP [x H1 ->]. case/setUP : H1 => H1; first case/setUP : H1 => H1.
      * by rewrite mem_imset.
      * move/set1P : H1 => ->. apply/imsetP. exists (inl g_in); first by rewrite !inE eqxx ?orbT.
        apply/eqmodP. by rewrite equiv_sym /= par2_eqv_io.
      * move/set1P : H1 => ->. apply/imsetP. exists (inl g_out); first by rewrite !inE eqxx ?orbT.
        apply/eqmodP. by rewrite equiv_sym /= par2_eqv_io.
    - move => T [D] [A B [t C]]. exists T. exists D. split => //. 
      apply/sdecomp_sskel. split => //. 
      exists t. by rewrite C !mem_imset // !inE ?eqxx ?orbT.
  Qed.

  Definition seq2_eqv : rel (union G1 G2) :=
    fun x y => (x == y) || ([set x; y] == [set inl g_out; inr g_in]).

  Definition seq2_eqv_refl : reflexive seq2_eqv.
  Proof. by move=> ?; rewrite /seq2_eqv eqxx. Qed.

  Lemma seq2_eqv_sym : symmetric seq2_eqv.
  Proof. move=> x y. by rewrite /seq2_eqv [[set y; x]]setUC [y == x]eq_sym. Qed.

  Definition seq2_eqv_trans : transitive seq2_eqv.
  Proof using.
    move=> y x z. rewrite /seq2_eqv.
    case/altP: (x =P y) => [<-//|/= xNy Exy].
    case/altP: (y =P z) => [<-|/= yNz Eyz]; first by rewrite Exy.
    case/altP: (x =P z) => //= xNz.
    have := eq_refl #|[set inl (@g_out G1); inr (@g_in G2)]|.
    rewrite -{1}(setUid [set _; _]) -{1}(eqP Exy) -{1}(eqP Eyz).
    rewrite set2C -setUUr (cardsU1 y) !cards2 !inE.
    by rewrite (eq_sym y x) negb_or xNy yNz xNz.
  Qed.

  Canonical seq2_eqv_equivalence :=
    EquivRel seq2_eqv seq2_eqv_refl seq2_eqv_sym seq2_eqv_trans.

  Lemma seq2_eqv_io : seq2_eqv (inl g_out) (inr g_in).
  Proof. by rewrite /seq2_eqv/=. Qed.

  Definition seq2_eq : rel (union G1 G2) :=
    [rel a b | (a == inl g_out) && (b == inr g_in)].

  Lemma seq2_equiv_of : seq2_eqv =2 equiv_of seq2_eq.
  Proof using.
    move=> x y. apply/idP/idP.
    - case/altP: (x =P y) => [<- _|xNy]; first exact: connect0.
      rewrite /seq2_eqv (negbTE xNy) /= eqEcard subUset !sub1set !inE => /andP[H _].
      case/andP: H xNy => /orP[]/eqP-> /orP[]/eqP->; rewrite ?eqxx // => _.
      + apply: sub_equiv_of. by rewrite /seq2_eq/= !eqxx.
      + rewrite equiv_of_sym. apply: sub_equiv_of. by rewrite /seq2_eq/= !eqxx.
    - case/connectP=> p. elim: p x; first by [move=> x _ ->; exact: seq2_eqv_refl].
      move=> /= a p IH x /andP[x_a p_path p_last].
      have {p_path p_last} : seq2_eqv a y by exact: IH. apply: seq2_eqv_trans.
      case/orP: x_a => /andP[/eqP-> /eqP->];
      last rewrite seq2_eqv_sym; exact: seq2_eqv_io.
  Qed.

  Definition seq2 :=
    {| graph_of := merge (union G1 G2) seq2_eqv ;
       g_in := \pi_{eq_quot seq2_eqv} (inl g_in);
       g_out := \pi_{eq_quot seq2_eqv} (inr g_out) |}.

  Lemma seq2_eqvP : admissible seq2_eqv.
  Proof. 
    move=> x y. case/orP => /eqP->; [by left | right].
    by rewrite subUset !sub1set !inE !eqxx.
  Qed.

  Lemma decomp_seq2 (T1 T2 : forest) D1 D2 : 
    sdecomp T1 (sskeleton G1) D1 -> sdecomp T2 (sskeleton G2) D2 -> 
    width D1 <= 3 -> width D2 <= 3 ->
    exists T D, [/\ sdecomp T (sskeleton seq2) D & width D <= 3].
  Proof using.
    move => dec1 dec2 W1 W2.
    case: (decomp_quot (e:= [equiv_rel of seq2_eqv]) dec1 dec2 W1 W2 _ _).
    - exact: seq2_eqvP.
    - pose P' : {set union G1 G2} := [set inl g_in; inl g_out; inr g_out].
      apply: (@leq_trans #|P'|); last apply cards3.
      apply: (@leq_trans #|[set (\pi x : seq2) | x in P']|); last exact: leq_imset_card.
      apply: subset_leq_card.
      apply/subsetP => ? /imsetP [x H1 ->]. move: H1. 
      rewrite /P -!setUA [[set _;_]]setUC !setUA. case/setUP => H1.
      * by rewrite mem_imset.
      * move/set1P : H1 => ->. apply/imsetP. exists (inl g_out); first by rewrite !inE eqxx ?orbT.
        apply/eqmodP. by rewrite equiv_sym /= seq2_eqv_io.
    - move => T [D] [A B [t C]]. exists T. exists D. split => //. 
      apply/sdecomp_sskel. split => //. 
      exists t. by rewrite C !mem_imset // !inE ?eqxx ?orbT.
  Qed.

End Quotients.

Definition cnv2 (G : graph2) :=
  {| graph_of := G; g_in := g_out; g_out := g_in |}.

Lemma decomp_cnv (G : graph2) T D : 
  sdecomp T (sskeleton G) D -> sdecomp T (sskeleton (cnv2 G)) D.
Proof. 
  move/sdecomp_sskel => [dec cmp]. apply/sdecomp_sskel; split => //. 
  move: cmp => [t] H. exists t => /=. by rewrite andbC.
Qed.

Definition dom2 (G : graph2) := 
  {| graph_of := G; g_in := g_in; g_out := g_in |}.

Lemma decomp_dom (G : graph2) T D : 
  sdecomp T (sskeleton G) D -> sdecomp T (sskeleton (dom2 G)) D.
Proof. 
  move/sdecomp_sskel => [dec cmp]. apply/sdecomp_sskel; split => //. 
  move: cmp => [t] /andP [H _]. exists t => /=. by rewrite !H. 
Qed.

Definition triv_decomp (G : sgraph) :
  sdecomp tunit G (fun _ => [set: G]).
Proof. 
  split => [x|e|x [] [] _ _]; try by exists tt; rewrite !inE.
  exact: connect0.
Qed.

Notation vfun := (fun x : void => match x with end).  
Definition unit_graph := @Graph [finType of unit] _ vfun vfun vfun.

Definition one2 := {| graph_of := unit_graph; g_in := tt; g_out := tt |}.

Definition two_graph := @Graph [finType of bool] _ vfun vfun vfun.

Definition top2 := {| graph_of := two_graph; g_in := false; g_out := true |}.

Definition edge_graph (a : sym) := 
  Graph (fun _ : unit => false) (fun _ => true) (fun _ => a).                           

Definition sym2 a := {| graph_of := edge_graph a; g_in := false; g_out := true |}.

Lemma decomp_small (G : graph2) : #|G| <= 3 -> 
  exists T D, [/\ sdecomp T (sskeleton G) D & width D <= 3].
Proof. 
  exists tunit; exists (fun => setT). split.
  - exact: triv_decomp.
  - by rewrite /width (big_pred1 tt _) // cardsT. 
Qed.

(** ** Terms and tree-width 2 property *)

Inductive term := 
| tmA of sym
| tm1 
| tmT 
| tmC of term
| tmS of term & term
| tmI of term & term
| tmD of term
.

Fixpoint graph_of_term (u:term) {struct u} : graph2 := 
  match u with
  | tmA a => sym2 a
  | tm1 => one2
  | tmT => top2
  | tmC u => cnv2 (graph_of_term u)
  | tmS u v => seq2 (graph_of_term u) (graph_of_term v)
  | tmI u v => par2 (graph_of_term u) (graph_of_term v)
  | tmD u => dom2 (graph_of_term u)
  end.

Theorem graph_of_TW2 (u : term) : 
  exists T D, [/\ sdecomp T (sskeleton (graph_of_term u)) D & width D <= 3].
Proof.
  elim: u => [a| | | u IHu | u IHu v IHv | u IHu v IHv | u IHu ].
  - apply: decomp_small. by rewrite card_bool.
  - apply: decomp_small. by rewrite card_unit.
  - apply: decomp_small. by rewrite card_bool.
  - move: IHu => [T] [D] [D1 D2]. exists T. exists D. split => //. 
    exact: decomp_cnv. 
  - move: IHu IHv => [T1] [D1] [? ?] [T2] [D2] [? ?].
    simpl graph_of_term. exact: (decomp_seq2 (D1 := D1) (D2 := D2)).
  - move: IHu IHv => [T1] [D1] [? ?] [T2] [D2] [? ?].
    simpl graph_of_term. exact: (decomp_par2 (D1 := D1) (D2 := D2)).
  - move: IHu => [T] [D] [D1 D2]. exists T. exists D. split => //. 
    exact: decomp_dom. 
Qed.

Lemma sskel_K4_free (u : term) : K4_free (sskeleton (graph_of_term u)).
Proof.
  case: (graph_of_TW2 u) => T [B] [B1 B2]. 
  exact: TW2_K4_free B1 B2.
Qed.

Lemma skel_K4_free (u : term) : K4_free (skeleton (graph_of_term u)).
Proof.
  apply: minor_K4_free (@sskel_K4_free u).
  exact: sub_minor (skel_sub _).
Qed.
