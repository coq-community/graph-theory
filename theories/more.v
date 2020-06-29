
(* Definitions of degree, removal of an edge and their properties *)

From mathcomp Require Import all_ssreflect.
Require Import preliminaries digraph sgraph connectivity dom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


(**********************************************************************************)
(** * Minimum and maximum (weighted and unweighted) degrees of a graph *)

Section Weighted_degree.

Variable G : sgraph.
Variable weight : G -> nat.
Hypothesis positive_weights : forall v : G, weight v > 0.

Let W := weight_set weight.

Definition deg_w (v : G) := W N(v).

Lemma ltn_deg_w_subwsetT1 (v : G) : deg_w v <= W setT - 1.
Proof.
  suff: deg_w v < W setT by move=> H ; rewrite (pred_Sn (deg_w v)) -subn1 (leq_sub2r 1 H).
  rewrite /deg_w ; apply: (ltnwset positive_weights).
  rewrite properT ; apply/negP => /eqP H1.
  move: (in_setT v) ; rewrite -H1 ; move/negP: (v_notin_opneigh v) ; contradiction.
Qed.

(* Minimum and maximum weighted degree of a graph. *)

(* x is a vertex of G (i.e. G is a non-empty graph) *)
Hypothesis x : G.

Let some_vertex_with_neighborhood (S : {set G}) := [exists v, S == N(v)].

Local Fact Nx_is_neighborhood_x : some_vertex_with_neighborhood N(x).
Proof. by rewrite /some_vertex_with_neighborhood ; apply/existsP ; exists x. Qed.

Definition delta_w := W (arg_min N(x) some_vertex_with_neighborhood W).

Fact delta_min (v : G) : delta_w <= deg_w v.
Proof.
  rewrite /delta_w ; case: (arg_minP W Nx_is_neighborhood_x) => A _ ; apply.
  by rewrite /some_vertex_with_neighborhood ; apply/existsP ; exists v.
Qed.

Fact delta_witness : exists v, deg_w v = delta_w.
Proof.
  rewrite /delta_w ; case: (arg_minP W Nx_is_neighborhood_x) => S exS _.
  move/existsP: exS => [u] /eqP SeqNu ; exists u ; by rewrite /deg_w SeqNu.
Qed.

Definition Delta_w := W (arg_max N(x) some_vertex_with_neighborhood W).

Fact Delta_max (v : G) : deg_w v <= Delta_w.
Proof.
  rewrite /Delta_w ; case: (arg_maxP W Nx_is_neighborhood_x) => A _ ; apply.
  by rewrite /some_vertex_with_neighborhood ; apply/existsP ; exists v.
Qed.

Fact Delta_witness : exists v, deg_w v = Delta_w.
Proof.
  rewrite /Delta_w ; case: (arg_maxP W Nx_is_neighborhood_x) => S exS _.
  move/existsP: exS => [u] /eqP SeqNu ; exists u ; by rewrite /deg_w SeqNu.
Qed.

End Weighted_degree.

Section Degree_of_vertices.

Variable G : sgraph.

Definition deg (v : G) := #|N(v)|.

Fact eq_deg_deg1 (v : G) : deg v = deg_w (@ones G) v.
Proof. by rewrite /deg /deg_w -cardwset1. Qed.

Lemma ltn_deg_subn1 (v : G) : deg v <= #|G| - 1.
Proof. by rewrite eq_deg_deg1 -cardsT (cardwset1 setT) ; exact: ltn_deg_w_subwsetT1. Qed.

(* Minimum and maximum weighted degree of a graph. *)

(* x is a vertex of G (i.e. G is a non-empty graph) *)
Hypothesis x : G.

Let some_vertex_with_degree (n : nat) := [exists v, deg v == n].

Local Fact degx_has_deg_x : exists (n : nat), some_vertex_with_degree n.
Proof. by rewrite /some_vertex_with_degree ; exists (deg x) ; apply/existsP ; exists x. Qed.

Local Fact ltn_someu_degu_subn1 (n : nat) : some_vertex_with_degree n -> n <= #|G| - 1.
Proof.
  rewrite /some_vertex_with_degree ; move/existsP => [u].
  move/eqP<- ; exact: ltn_deg_subn1.
Qed.

Definition delta := ex_minn degx_has_deg_x.

Lemma eq_delta_delta1 : delta = delta_w (@ones G) x.
Proof.
  rewrite /delta.
  have [n some_n n_min] := ex_minnP.
  apply/eqP ; rewrite eqn_leq ; apply/andP ; split.
  - apply: n_min ; rewrite /some_vertex_with_degree.
    apply/existsP ; elim: (delta_witness (@ones G) x) => u.
    move<- ; exists u ; apply/eqP.
    exact: eq_deg_deg1.
  - move: some_n.
    rewrite /some_vertex_with_degree.
    move/existsP => [u] /eqP <-.
    rewrite eq_deg_deg1.
    exact: delta_min.
Qed.

Definition Delta := ex_maxn degx_has_deg_x ltn_someu_degu_subn1.

Lemma eq_Delta_Delta1 : Delta = Delta_w (@ones G) x.
Proof.
  rewrite /Delta.
  have [n some_n n_max] := ex_maxnP.
  apply/eqP ; rewrite eqn_leq ; apply/andP ; split.
  - move: some_n.
    rewrite /some_vertex_with_degree.
    move/existsP => [u] /eqP <-.
    rewrite eq_deg_deg1.
    exact: Delta_max.
  - apply: n_max ; rewrite /some_vertex_with_degree.
    apply/existsP ; elim: (Delta_witness (@ones G) x) => u.
    move<- ; exists u ; apply/eqP.
    exact: eq_deg_deg1.
Qed.

End Degree_of_vertices.

Arguments deg_w : clear implicits.
Arguments delta_w : clear implicits.
Arguments Delta_w : clear implicits.
Arguments deg : clear implicits.
Arguments delta : clear implicits.
Arguments Delta : clear implicits.


(**********************************************************************************)
(** * A classic result of Graph Theory: the sum of degrees equals the cardinal of the edge set *)

Section EdgelessGraph.
  Variable G : sgraph.
  Hypothesis edgeless : E(G) = set0.

  Lemma sg_edgeless (u v : G) : u -- v = false.
  Proof.
    apply: negbTE ; move/eqP: edgeless ; apply: contraLR.
    rewrite negbK => adjuv.
    apply/set0Pn ; exists [set u; v] ; apply/edgesP.
    by exists u ; exists v ; split=> //.
  Qed.

  Lemma deg_edgeless (v : G) : deg G v = 0.
  Proof.
    rewrite /deg opn_edges ; apply/eqP ; rewrite cards_eq0.
    move/eqP: edgeless ; apply: contraLR ; move/set0Pn => [u].
    rewrite in_set => vuinEG.
    by apply/set0Pn ; exists [set v; u].
  Qed.

End EdgelessGraph.

Section RemoveEdge.
  Variable G : sgraph.
  Variables u v : G.
  Hypothesis adjuv : u -- v.

  Definition remove_edge_rel (x y : G) := if ([set u; v] == [set x; y]) then false else x -- y.

  Lemma remove_edge_sym : symmetric remove_edge_rel.
  Proof.
    rewrite /symmetric /remove_edge_rel => x y.
    case: ifP ; case: ifP => //.
    - move=> /eqP H1 /eqP H2 ; move: H1 ; rewrite H2 doubleton_eq_iff.
      have: (x = y /\ y = x \/ x = x /\ y = y) by apply: or_intror => //.
      contradiction.
    - move/eqP-> ; move/eqP ; rewrite doubleton_eq_iff.
      have: (y = x /\ x = y \/ y = y /\ x = x) by apply: or_intror => //.
      contradiction.
    - by rewrite sg_sym.
  Qed.

  Lemma remove_edge_irrefl : irreflexive remove_edge_rel.
  Proof.
    rewrite /irreflexive /remove_edge_rel => ?.
    case: ifP => // ; by rewrite sg_irrefl.
  Qed.

  Definition remove_edge := SGraph remove_edge_sym remove_edge_irrefl.

  Fact remove_edge_rel_false : remove_edge_rel u v = false.
  Proof. by rewrite /remove_edge_rel eqxx. Qed.

  Fact remove_edge_rel_sg (x y : G) : [set u; v] != [set x; y] -> remove_edge_rel x y = (x -- y).
  Proof. by rewrite /remove_edge_rel ; apply: ifN. Qed.

  Fact remove_edge_implies_sg (x y : G) : remove_edge_rel x y -> x -- y.
  Proof.
    rewrite /remove_edge_rel ; case: ifP ; last by [].
    move: not_false_is_true ; contradiction.
  Qed.

  Proposition remove_edge_set : E(remove_edge) = E(G) :\ [set u; v].
  Proof.
    apply/eqP ; rewrite eqEsubset ; apply/andP ; split.
    - apply/subsetP => e einEG'.
      rewrite in_setD1 ; apply/andP ; split.
      + have : exists x y : remove_edge, e = [set x; y] /\ remove_edge_rel x y.
        by move/edgesP : einEG'.
        (* note: can't use the previous line directly because it generates the adjacency
           relation from G, not from remove_edge :S *)
        move=> [x [y [eeqxy]]].
        move: eeqxy->.
        apply: contraL.
        move/eqP ; rewrite doubleton_eq_iff ; case.
        * by elim ; move-> ; move-> ; rewrite remove_edge_rel_false.
        * by elim ; move-> ; move-> ; rewrite remove_edge_sym remove_edge_rel_false.
      + move/edgesP: einEG'=> [x [y [eisxy adjxy]]].
        suff : e \in E(G) by simpl.
        (* same weird thing happens here, can't apply directly edgesP, probably because
           x, y is from remove_edge instead of G because of the coercion :S *)
        apply/edgesP ; exists x ; exists y ; split => //.
        apply: remove_edge_implies_sg.
        exact: adjxy.
    - apply/subsetP => e.
      rewrite in_setD1 => /andP [enequv ?].
      have einEG : e \in E(G) by simpl. (* again! *)
      move/edgesP: einEG => [x [y [eisxy adjxy]]].
      rewrite eisxy in_edges.
      suff: remove_edge_rel x y by simpl.
      rewrite eisxy eq_sym in enequv.
      by rewrite (remove_edge_rel_sg enequv).
  Qed.

  Lemma opn_remove_edgew (w : G) : w \notin [set u; v] -> N(G; w) = N(remove_edge; w).
  Proof.
    move=> wnotuv ; rewrite !opn_edges remove_edge_set.
    apply/eqP ; rewrite eqEsubset ; apply/andP ; split ; last first.
    - by apply/subsetP=> z ; rewrite !in_set in_edges => /andP [_ ?].
    - apply/subsetP=> z.
      rewrite in_set in_edges => adjwz.
      rewrite in_set in_setD1 ; apply/andP ; split ; last by rewrite (in_edges w z).
      move: wnotuv ; apply: contra ; move/eqP.
      rewrite doubleton_eq_iff in_set2 ; case.
      + by elim ; move-> ; rewrite eqxx orTb.
      + by elim ; move-> ; rewrite eqxx orbT.
  Qed.

  Lemma opn_remove_edgeu : N(G; u) = N(remove_edge; u) :|: [set v].
  Proof.
    rewrite !opn_edges remove_edge_set.
    apply/eqP ; rewrite eqEsubset ; apply/andP ; split.
    - apply/subsetP=> z.
      rewrite in_setU in_set1 !in_set !in_edges => adjuz.
      rewrite adjuz andbT -implybE ; apply/implyP ; move/eqP.
      rewrite doubleton_eq_left. by move->.
    - apply/subsetP=> z.
      rewrite in_setU in_set1 !in_set.
      move/orP ; case ; first by move/andP ; elim.
      by move/eqP-> ; rewrite in_edges.
  Qed.

  Lemma opn_remove_edgev : N(G; v) = N(remove_edge; v) :|: [set u].
  Proof.
    rewrite !opn_edges remove_edge_set.
    apply/eqP ; rewrite eqEsubset ; apply/andP ; split.
    - apply/subsetP=> z.
      rewrite in_setU in_set1 !in_set !in_edges => adjuz.
      rewrite adjuz andbT -implybE setUC ; apply/implyP ; move/eqP.
      rewrite doubleton_eq_right. by move->.
    - apply/subsetP=> z.
      rewrite in_setU in_set1 !in_set.
      move/orP ; case ; first by move/andP ; elim.
      by move/eqP-> ; rewrite in_edges sgP.
  Qed.

  Proposition deg_remove_edgew (w : G) : w \notin [set u; v] -> deg G w = deg remove_edge w.
  Proof.
    move=> wnotuv ; rewrite /deg ; apply: eq_card.
    by rewrite (opn_remove_edgew wnotuv).
  Qed.

  Proposition deg_remove_edgeu : deg G u = (deg remove_edge u).+1.
  Proof.
    rewrite /deg opn_remove_edgeu cardsU cards1 addn1. 
    suff: N(remove_edge; u) :&: [set v] = set0 by move-> ; rewrite cards0 subn0.
    apply/eqP ; rewrite setI_eq0 ; apply/disjointP => x.
    rewrite in_opn in_set1 => adjux /eqP xisv.
    have: remove_edge_rel u v by move: adjux ; rewrite xisv.
    by rewrite remove_edge_rel_false.
  Qed.

  Proposition deg_remove_edgev : deg G v = (deg remove_edge v).+1.
  Proof.
    rewrite /deg opn_remove_edgev cardsU cards1 addn1. 
    suff: N(remove_edge; v) :&: [set u] = set0 by move-> ; rewrite cards0 subn0.
    apply/eqP ; rewrite setI_eq0 ; apply/disjointP => x.
    rewrite in_opn in_set1 => adjvx /eqP xisu.
    have: remove_edge_rel v u by move: adjvx ; rewrite xisu.
    by rewrite remove_edge_sym remove_edge_rel_false.
  Qed.

End RemoveEdge.


Theorem edges_sum_degrees : forall G : sgraph, 2 * #|E(G)| = \sum_(w in G) deg G w.
Proof.
  (* first, we shape the statement *)
  suff: forall (n : nat) (G : sgraph), #|E(G)| = n -> 2 * n = \sum_(w in [set: G]) deg G w.
  { by move=> H1 G ; move: (H1 #|E(G)| G erefl)-> ; under eq_bigl => ? do rewrite in_setT. }
  move=> n ; elim/nat_ind: n => [G | m IH].
  (* base case *)
  - move=> /cards0_eq edgeless.
  under eq_bigr => w do rewrite deg_edgeless //.
  by rewrite sum_nat_const !muln0.
  (* inductive case *)
  - move=> G Emplus1.
    rewrite mulnC mulSn mulnC.
    (* we first obtain an edge {u,v} from G *)
    move: (ltn0Sn m).
    rewrite -Emplus1 card_gt0.
    move/set0Pn => [e einEG].
    move/edgesP: (einEG) => [u [v [eisuv adjuv]]].
    (* we now split the summation, and do the same for the inductive hypothesis *)
    rewrite (big_setID [set u; v]) (setIidPr (subsetT [set u; v])) /=.

    set G' := @remove_edge G u v.
    have IH' : #|E(G')| = m ->
         2 * m = \sum_(i in [set (u : G'); (v : G')]) deg G' i
               + \sum_(i in [set: G'] :\: [set (u : G'); (v : G')]) deg G' i.
    { move=> EG'm.
      rewrite -[in X in _ = X + _](setIidPr (subsetT [set (u : G'); (v : G')])).
      by rewrite -(big_setID [set u; v]) (IH G' EG'm). }

    have uvinEG : [set [set u; v]] \subset E(G).
    { by rewrite sub1set -eisuv einEG. }

    have EG'm : #|E(G')| = m.
    { by rewrite remove_edge_set cardsD Emplus1 (setIidPr uvinEG) cards1 subn1 /=. }

    (* now, we apply the inductive hypothesis *)
    rewrite (IH' EG'm) addnA.

    under [in X in _ + _ = _ + X]eq_bigr => w.
      rewrite setTD in_setC => wnequv.
      rewrite (deg_remove_edgew wnequv) -/G'.
    over.
    have H3 : [set: G'] :\: [set u; v] = [set: svertex G] :\: [set u; v] by auto.
    under [in X in _ + _ + X = _ + _]eq_bigl => w do rewrite H3.

    apply/eqP ; rewrite eqn_add2r ; apply/eqP.

    have usubuv : [set u] \subset [set u; v] by rewrite sub1set set21.
    have uvdifv : [set u; v] :\: [set u] = [set v].
    { by rewrite setU1K // in_set1 (sg_edgeNeq adjuv). }

    rewrite (big_setID [set u]) (setIidPr usubuv) big_set1 /=.
    rewrite [in X in _ = X](big_setID [set u]) (setIidPr usubuv) big_set1 /=.
    rewrite !uvdifv !big_set1.
    rewrite (@deg_remove_edgeu G u v adjuv) -/G'.
    rewrite (@deg_remove_edgev G u v adjuv) -/G'.
    by rewrite [in X in _ = X]addSn [in X in _ = X]addnS !addSnnS add0n.
Qed.


