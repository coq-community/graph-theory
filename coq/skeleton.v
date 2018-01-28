Require Import RelationClasses.

From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries sgraph minor checkpoint.
Require Import multigraph subalgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 

(** * Skeletons *)

Definition sk_rel (G : graph) : rel G := 
  sc [rel x y | (x != y) && [exists e, (source e == x) && (target e == y)]].

Arguments sk_rel G _ _ : clear implicits.

Lemma sk_rel_sym (G : graph) : symmetric (sk_rel G).
Proof. move => x y. by rewrite /sk_rel /sc /= orbC. Qed.

Lemma sk_rel_irrefl (G : graph) : irreflexive (sk_rel G).
Proof. move => x. by rewrite /sk_rel /sc /= !eqxx. Qed.

Definition skeleton (G : graph) := 
  SGraph (@sk_rel_sym G) (@sk_rel_irrefl G).

Lemma skelP (G : graph) (P : G -> G -> Prop) : 
  Symmetric P -> 
  (forall e : edge G, P (source e) (target e)) -> 
  (forall x y : G,  sk_rel _ x y -> P x y).
Proof. 
  move => S H x y. 
  case/orP => /= /andP [_] /existsP [e] /andP [/eqP<- /eqP <-] //.
  exact: S.
Qed.

Lemma decomp_skeleton (G : graph) (T : tree) (D : T -> {set G}) :
  decomp T G D -> sdecomp T (skeleton G) D.
Proof. 
  case => D1 D2 D3. split => //. apply skelP => // x y. 
  move => [t] A. exists t. by rewrite andbC.
Qed.

Definition ssk_rel (G : graph2) := 
  relU (sk_rel G) (sc [rel x y | [&& x != y, x == g_in & y == g_out]]).

Definition add_edge_rel (G:sgraph) (i o : G) := 
  relU (@sedge G) (sc [rel x y | [&& x != y, x == i & y == o]]).

Lemma add_edge_sym (G:sgraph) (i o : G) : symmetric (add_edge_rel i o).
Proof. apply: relU_sym'. exact: sg_sym. exact: sc_sym. Qed.

Lemma add_edge_irrefl (G:sgraph) (i o : G) : irreflexive (add_edge_rel i o).
Proof. move => x /=. by rewrite sg_irrefl eqxx. Qed.

Definition add_edge (G:sgraph) (i o : G) :=
  {| svertex := G;
     sedge := add_edge_rel i o;
     sg_sym := add_edge_sym i o;
     sg_irrefl := add_edge_irrefl i o |}.

Lemma add_edge_Path (G : sgraph) (i o x y : G) (p : @Path G x y) :
  exists q : @Path (add_edge i o) x y, nodes q = nodes p.
Proof.
  case: p => p p_pth.
  have p_iopth : @spath (add_edge i o) x y p.
  { case/andP: p_pth => p_path p_last. apply/andP; split=> //.
    apply: sub_path p_path. by move=> u v /=->. }
  by exists (Sub (p : seq (add_edge i o)) p_iopth).
Qed.

Lemma add_edge_connected (G : sgraph) (i o : G) (U : {set G}) :
  @connected G U -> @connected (add_edge i o) U.
Proof.
  move=> U_conn x y x_U y_U; move/(_ x y x_U y_U): U_conn.
  case: (boolP (x == y :> G)); first by move=>/eqP-> _; rewrite connect0.
  move=> xNy /(uPathRP xNy)[p _ /subsetP pU].
  case: (add_edge_Path i o p) => [q eq_q].
  apply: (@connectRI _ _ x y q) => z.
  rewrite in_collective eq_q; exact: pU.
Qed.

Definition sskeleton (G : graph2) := @add_edge (skeleton G) g_in g_out.

(* Lemma ssk_sym (G : graph2) : symmetric (ssk_rel G). *)
(* Proof. apply: relU_sym' (@sk_rel_sym _) _. exact: sc_sym. Qed. *)

(* Lemma ssk_irrefl (G : graph2) : irreflexive (ssk_rel G). *)
(* Proof. move => x /=. by rewrite sk_rel_irrefl eqxx. Qed. *)

(* Definition sskeleton (G : graph2) := SGraph (@ssk_sym G) (@ssk_irrefl G). *)

Lemma sskelP (G : graph2) (P : G -> G -> Prop) : 
  Symmetric P -> 
  (forall e : edge G, P (source e) (target e)) -> 
  (g_in != g_out :> G -> P g_in g_out) ->
  (forall x y : sskeleton G, x -- y -> P x y).
Proof. 
  move => S H IO x y. case/orP. exact: skelP. 
  case/orP => /= /and3P [A /eqP ? /eqP ?];subst; first exact: IO.
  apply: S. exact: IO.
Qed.

Lemma decomp_sskeleton (G : graph2) (T : tree) (D : T -> {set G}) :
  decomp T G D -> compatible D -> sdecomp T (sskeleton G) D.
Proof. 
  case => D1 D2 D3 C. split => //. apply sskelP  => // x y. 
  move => [t] A. exists t. by rewrite andbC.
Qed.

Lemma sskel_K4_free (u : term) : K4_free (sskeleton (graph_of_term u)).
Proof.
  case: (graph_of_TW2 u) => T [B] [B1 B2 B3].
  exact: TW2_K4_free (decomp_sskeleton B1 B2) _.
Qed.

Lemma skel_sub (G : graph2) : sgraph.subgraph (skeleton G) (sskeleton G).
Proof.
  (* Note: This is really obsucre due to the abbiguity of [x -- y] *)
  exists id => //= x y H. right. exact: subrelUl. 
Qed.

Lemma skel_K4_free (u : term) : K4_free (skeleton (graph_of_term u)).
Proof. 
  apply: minor_K4_free (@sskel_K4_free u).
  exact: sub_minor (skel_sub _).  
Qed.

(** Bridging Lemmas *)

Definition edges (G : graph) (x y : G) := 
  [set e : edge G | (source e == x) && (target e == y)].

Definition adjacent (G : graph) (x y : G) := 
  [exists e, e \in edges x y] || [exists e, e \in edges y x].

Lemma adjacentE (G : graph) (x y : skeleton G) : 
  (x != y) && adjacent x y = x -- y.
Proof.
  apply/andP/idP.
  - move=> /= [Hxy]. rewrite /sk_rel /= Hxy eq_sym Hxy /= /adjacent.
    case/orP => /existsP[e]; rewrite inE => ?; apply/orP; [left|right];
    by apply/existsP; exists e.
  - move=> xy; split; first by rewrite sg_edgeNeq.
    move: xy; rewrite /=/sk_rel/adjacent/=.
    case/orP=> /andP[_] /existsP[e He]; apply/orP; [left|right];
    by apply/existsP; exists e; rewrite inE.
Qed.

(* TODO: simplify edge_set, edges, adjacent, ... *)
Lemma edge_set_adj (G : graph2) : 
  @edge_set G [set g_in; g_out] == set0 -> ~~ @adjacent G g_in g_out. 
Proof. 
  apply: contraTN => /orP[] /existsP [e He]. 
  all: rewrite !inE in He; case/andP: He => He1 He2. 
  all: apply/set0Pn; exists e; by rewrite !inE ?He1 ?He2. 
Qed.

Lemma edge_set1 (G : graph) (x : G) : edge_set [set x] = edges x x.
Proof. apply/setP=> e. by rewrite !inE. Qed.

Lemma sskeleton_subgraph_for (G : graph2) (V : {set G}) (E : {set edge G})
  (con : consistent V E) (i o : sig [eta mem V]) : val i = g_in -> val o = g_out ->
  sgraph.subgraph (sskeleton (point (subgraph_for con) i o)) (sskeleton G).
Proof.
  rewrite /sskeleton/= => <- <-.
  (* TODO: Factor out some lemma about [add_edge] and [sgraph.subgraph]. *)
  exists val; first exact: val_inj.
  move=> x y /=; rewrite -!(inj_eq val_inj) /=.
  case/or3P=> [xy|->|->]; right=> //. apply/orP; left.
  move: xy; rewrite /sk_rel/= -!(inj_eq val_inj).
  case/orP=> /andP[->] /= /existsP[e];
  rewrite -!(inj_eq val_inj) /= => He; apply/orP; [left|right];
  apply/existsP; by exists (val e).
Qed.



(** ** Intervals and Petals *)

(** TOTHINK: define intervals and petals on graph or sgraph, i.e.,
where to add theskeleton casts? *)

Fact intervalL (G : sgraph) (x y : G) : 
  x \in interval x y.
Proof. by rewrite !inE eqxx. Qed.

Fact intervalR (G : sgraph) (x y : G) : 
  y \in interval x y.
Proof. by rewrite !inE eqxx !orbT. Qed.

Definition remove_edges (G : graph) (E : {set edge G}) := 
  {| vertex := G;
     edge := [finType of { e : edge G | e \notin E }];
     source e := source (val e);
     target e := target (val e);
     label e := label (val e) |}.

Coercion skeleton : graph >-> sgraph.

Definition interval_edges (G : graph) (x y : G) :=
  edge_set (@interval G x y) :\: (edges x x :|: edges y y).

Lemma interval_edges_sym (G : graph) (x y : G) :
  interval_edges x y = interval_edges y x.
Proof. by rewrite /interval_edges interval_sym setUC. Qed.

Lemma igraph_proof (G : graph) (x y : skeleton G) :
  consistent (interval x y) (interval_edges x y).
Proof. move=> e. rewrite inE =>/andP[_]. by rewrite inE =>/andP. Qed.

Definition igraph (G : graph) (x y : skeleton G) :=
  @point (subgraph_for (@igraph_proof G x y))
         (Sub x (intervalL x y))
         (Sub y (intervalR x y)).

Definition pgraph (G : graph) (U : {set G}) (x:G) :=
  @point (induced (@petal (skeleton G) U x))
         (Sub x (@petal_id (skeleton G) U x))
         (Sub x (@petal_id (skeleton G) U x)).

Lemma pgraph_eq_io (G : graph) (U : {set G}) (x : G) : g_in = g_out :> @pgraph G U x.
Proof. by []. Qed.

Lemma interval_petal_edges_disj (G : graph) (U : {set G}) (x y : G) :
  connected [set: skeleton G] -> x \in @CP G U -> y \in @CP G U ->
  [disjoint edge_set (@petal G U x) & @interval_edges G x y].
Proof.
  move=> G_conn x_cp y_cp. rewrite -setI_eq0 -subset0. apply/subsetP => e.
  rewrite 3!inE => /and3P[]/andP[src_p tgt_p].
  rewrite 4!inE ![_ \in @interval G _ _]inE (lock sinterval) !inE -lock.
  rewrite negb_or !negb_and -!orbA => /andP[eNx eNy].
  case/andP=> /or3P[src_x|src_y|src_sI] /or3P[tgt_x|tgt_y|tgt_sI].
  all: move: eNx eNy; rewrite ?src_x ?src_y ?tgt_x ?tgt_y ?orbF //= => eNx eNy.
  - move: eNx. by rewrite (eqP tgt_y) -(@petal_cp G _ U) // -(eqP tgt_y) tgt_p.
  - by case: (disjointE (@interval_petal_disj G U x y y_cp) tgt_p tgt_sI).
  - move: eNx. by rewrite (eqP src_y) -(@petal_cp G _ U) // -(eqP src_y) src_p.
  - by case: (disjointE (@interval_petal_disj G U x y y_cp) tgt_p tgt_sI).
  - by case: (disjointE (@interval_petal_disj G U x y y_cp) src_p src_sI).
  - by case: (disjointE (@interval_petal_disj G U x y y_cp) src_p src_sI).
  - by case: (disjointE (@interval_petal_disj G U x y y_cp) src_p src_sI).
Qed.

Lemma petal_edges_disj (G : graph) (U : {set G}) (x y : G) :
  connected [set: skeleton G] -> x \in @CP G U -> y \in @CP G U -> x != y ->
  [disjoint edge_set (@petal G U x) & edge_set (@petal G U y)].
Proof.
  move=> G_conn x_cp y_cp xNy. rewrite -setI_eq0 -subset0. apply/subsetP => e.
  rewrite 3!inE. case/andP=> /andP[src_x tgt_x] /andP[src_y tgt_y].
  by case: (disjointE (@petal_disj G _ U x y _ _ _) src_x src_y).
Qed.

Lemma interval_edges_disj_cp (G : graph) (x y z : G) :
  z \in @cp G x y -> [disjoint interval_edges x z & interval_edges z y].
Proof.
  move=> z_cpxy. rewrite -setI_eq0 -subset0. apply/subsetP => e.
  rewrite 6!inE negb_or !negb_and. case/andP=> /and3P[_ src_Ixz tgt_Ixz].
  rewrite 5!inE negb_or !negb_and. case/and3P=> /andP[e_z _] src_Izy tgt_Izy.
  move: e_z.
  have : source e \in [set z] by rewrite -(intervalI_cp z_cpxy) inE src_Ixz src_Izy.
  rewrite inE =>->/=.
  have : target e \in [set z] by rewrite -(intervalI_cp z_cpxy) inE tgt_Ixz tgt_Izy.
  by rewrite inE =>->.
Qed.

Lemma interval_petal_edge_partition (G : graph) (x y : G) :
  connected [set: skeleton G] -> x != y ->
  pe_partition [set edge_set (@petal G [set x; y] x);
                    edge_set (@petal G [set x; y] y);
                    @interval_edges G x y]
               [set: edge G].
Proof.
  move=> G_conn xNy. apply/andP. split.
  - rewrite -subTset. apply/subsetP=> e _.
    case/andP: (sinterval_petal_partition G_conn xNy) => /eqP compU _.
    move: compU; rewrite /cover !bigcup_setU !bigcup_set1 2!inE setUC => /esym compU.
    have : target e \in [set: G] by []. have : source e \in [set: G] by [].
    rewrite !{}compU !in_setU.
    case: (boolP (source e \in @sinterval G x y)) => [Hsrc _|Nsrc /= Hsrc].
    + case: (boolP (target e \in @sinterval G x y)) => [Htgt _|Ntgt /= Htgt].
      { rewrite ![e \in _]inE ![_ \in @interval G _ _]inE Hsrc Htgt.
        rewrite !orbT negb_or !negb_and. move: Hsrc.
        by rewrite 5!inE negb_or => /andP[]/andP[->->]. }
      wlog Htgt : x y xNy Hsrc Ntgt {Htgt} / target e \in @petal G [set x; y] x.
      { move=> Hyp. case/orP: Htgt; first exact: Hyp.
        rewrite setUC [(e \in _) || (e \in _)]orbC interval_edges_sym.
        apply: Hyp; rewrite 1?sinterval_sym //. by rewrite eq_sym. }
      have Nsrc : source e \notin @petal G [set x; y] x.
      { rewrite (disjointFl (@interval_petal_disj G _ x y _) Hsrc) //.
        apply: CP_extensive. by rewrite !inE eqxx. }
      have src_tgt : @sedge G (target e) (source e).
      { apply/orP; right. apply/andP. split; first by apply: contraNneq Ntgt =><-.
        apply/'exists_andP. by exists e; split. }
      have : target e = x := petal_exit_edge G_conn _ Htgt Nsrc src_tgt.
      move/(_ (CP_extensive _)). rewrite 3!inE eqxx => /(_ _)/Wrap[]// tgt_x.
      rewrite ![e \in _]inE tgt_x (@intervalL G) [_ \in @interval G _ _]inE Hsrc.
      rewrite orbT !andbT negb_or !negb_and.
      suff [->->] : source e != x /\ source e != y by [].
      by split; apply: contraTneq Hsrc =>->; rewrite (@sinterval_bounds G).
    + wlog Hsrc : x y xNy {Nsrc Hsrc} / source e \in @petal G [set x; y] x.
      { move=> Hyp. case/orP: Hsrc; first exact: Hyp.
        rewrite setUC sinterval_sym interval_edges_sym [(e \in _) || (e \in _)]orbC.
        rewrite [(target e \in _) || (target e \in _)]orbC.
        by apply: Hyp; rewrite eq_sym. }
      case: (boolP (target e \in @petal G [set x; y] x)) => Ntgt /=.
        by rewrite [e \in _]inE Hsrc Ntgt.
      have src_tgt : @sedge G (source e) (target e).
      { apply/orP; left. apply/andP. split; first by apply: contraNneq Ntgt =><-.
        apply/'exists_andP. by exists e; split. }
      have : source e = x := petal_exit_edge G_conn _ Hsrc Ntgt src_tgt.
      move/(_ (CP_extensive _)). rewrite 3!inE eqxx => /(_ _)/Wrap[]// src_x.
      case/orP=> Htgt.
      * rewrite ![e \in _]inE src_x (@intervalL G) (negbTE xNy) orbF eqxx/=.
        have -> : target e != x.
        { apply: contraTneq Htgt =>->. by rewrite (@sinterval_bounds G). }
        by have -> : target e \in @interval G x y by rewrite inE Htgt.
      * have Nsrc : source e \notin @petal G [set x; y] y.
        { have yNx : y != x by rewrite eq_sym.
          rewrite (disjointFl (petal_disj G_conn _ _ yNx) Hsrc) //;
          by apply: CP_extensive; rewrite !inE eqxx. }
        have := petal_exit_edge G_conn (CP_extensive _) Htgt Nsrc _.
        rewrite sg_sym 3!inE eqxx => /(_ _ src_tgt)/Wrap[]// tgt_y.
        rewrite ![e \in _]inE src_x tgt_y (@intervalL G) (@intervalR G).
        by rewrite !eqxx eq_sym (negbTE xNy).
  - have [x_cp y_cp] : x \in @CP G [set x; y] /\ y \in @CP G [set x; y]
      by split; apply: CP_extensive; rewrite !inE eqxx.
    apply: trivIset3; first exact: petal_edges_disj; first rewrite interval_edges_sym;
    exact: interval_petal_edges_disj.
Qed.

(** ** Connecting Multigraphs and their Skeletons *)

Lemma has_edge (G : graph) (x y : G) : 
  connected [set: skeleton G] -> x != y -> 0 < #|edge G|.
Proof.
  move/connectedTE/(_ x y). case/uPathP => p _ xy. 
  case: (splitL p xy) => x' [/= xx'] _. 
  apply/card_gt0P. rewrite /sk_rel /= in xx'. 
  case/orP : xx' => /andP [_ /existsP [e _]]; by exists e. 
Qed.

Lemma consistent_setD (G : graph) V E E' : 
  @consistent G V E -> consistent V (E :\: E').
Proof. move => con_E e /setDP [? _]. exact: con_E. Qed.

(* Is this the most general type? *)
Lemma card_val (T : finType) (P : pred T) (s : subFinType P) (A : pred s) : 
  #|val @: A| = #|A|.
Proof. rewrite card_imset //. exact: val_inj. Qed.

(* lifting connectedness from the skeleton *)
Lemma connected_skeleton' (G : graph) V E (con : @consistent G V E) :
  forall U : {set subgraph_for con}, @connected (skeleton G) (val @: U) ->
  (forall e, e \in edge_set (val @: U) -> source e != target e ->
             let x := source e in let y := target e in
             exists2 e, e \in E & (e \in edges x y) || (e \in edges y x)) ->
  @connected (skeleton (subgraph_for con)) U.
Proof.
  move => U conn_U all_edges.
  move => x y x_U y_U. (* move: (conn_U _ _ x_U y_U). *)
  (* ... *)
Admitted.

Lemma connected_skeleton (G : graph) V E (con : @consistent G V E) :
  forall U : {set subgraph_for con}, @connected (skeleton G) (val @: U) ->
  (forall e, e \in edge_set (val @: U) -> source e != target e -> e \in E) ->
  @connected (skeleton (subgraph_for con)) U.
Proof.
  move=> U conn_U all_edges. apply: connected_skeleton' conn_U _.
  move=> e E1 E2; exists e; rewrite ?inE ?eqxx //. exact: all_edges.
Qed.

Lemma connected_pgraph (G : graph2) (U : {set G}) (x : G) : 
  connected [set: skeleton G] -> x \in @CP (skeleton G) U -> 
  connected [set: skeleton (pgraph U x)].
Proof.
  move => conn_G cp_x.
  apply: connected_skeleton; rewrite imset_valT memKset //. exact: connected_petal.
Qed.

Lemma connected_igraph (G : graph2) (x y: G) : 
  connected [set: skeleton G] -> 
  connected [set: skeleton (igraph x y)].
Proof.
  move=> conn_G. apply: connected_skeleton; rewrite imset_valT memKset.
  + exact: connected_interval.
  + move => e E1 E2. rewrite 4!inE E1 andbT negb_or. apply/andP;split.
    * apply: contraNN E2 => /andP [/eqP -> /eqP ->]; by rewrite eqxx.
    * apply: contraNN E2 => /andP [/eqP -> /eqP ->]; by rewrite eqxx.
Qed.

Lemma iso_pointxx (G : graph) (x : G) :
  sg_iso (sskeleton (point _ x x)) (skeleton G).
Proof.
  exists (id : skeleton G -> sskeleton (point G x x)) id => // u v /=;
  first by move=>->. case/or3P => // /and3P[uNv /eqP eq1 /eqP eq2];
  move: uNv; by rewrite eq1 eq2 eqxx.
Qed.

Lemma sub_pointxx (G : graph) (x:G) :
  sgraph.subgraph (sskeleton (point _ x x))
                  (skeleton G).
Proof. apply: iso_subgraph; exact: iso_pointxx. Qed.

(* The subgraph relation lifts to skeletons *)
Lemma sub_sub (G H : graph) : 
  subgraph G H -> sgraph.subgraph G H.
Proof.
  move => [[hv he]] [/= hom_h lab_h] [/= inj_hv inj_he]. 
  exists hv => // x y. rewrite -!adjacentE => /andP[E adj]. right.
  apply/andP;split; first by apply: contraNN E => /eqP/inj_hv->.
  case/orP : adj => /existsP[e]. 
  - rewrite inE => /andP[/eqP<- /eqP<-]. rewrite !hom_h.
    apply/orP; left. apply/existsP; exists (he e). by rewrite !inE !eqxx.
  - rewrite inE => /andP[/eqP<- /eqP<-]. rewrite !hom_h.
    apply/orP; right. apply/existsP; exists (he e). by rewrite !inE !eqxx.
Qed.

Definition flesh_out_graph (G : sgraph) (z : G) : graph2 :=
  {| graph_of :=
       {| vertex := G ; edge := [finType of { p : G * G | p.1 -- p.2 }];
          source := fst \o val; target := snd \o val; label := fun _ => sym0 |} ;
     g_in := z; g_out := z |}.

Lemma flesh_out (G : sgraph) (z : G) :
  exists G', sg_iso (sskeleton G') G /\ sg_iso (skeleton G') G.
Proof.
  pose G' := flesh_out_graph z. exists G'.
  suff iso : sg_iso (skeleton G') G.
  { split=> //. apply: sg_iso_trans iso. exact: iso_pointxx. }
  exists (id : G -> skeleton G') id; move=> //= x y; rewrite /sk_rel/=.
  - move=> xy. apply/orP; left. rewrite sg_edgeNeq //=.
    apply/existsP; exists (Sub (x, y) xy); by rewrite /= !eqxx.
  - case/orP=> /andP[_] /existsP[][/=][u v /=] ? /andP[/eqP<- /eqP<-] //.
    by rewrite sg_sym.
Qed.
