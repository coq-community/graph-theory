Require Import RelationClasses.

From mathcomp Require Import all_ssreflect.
Require Import finite_quotient preliminaries sgraph minor checkpoint.
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

Lemma relU_sym' (T : Type) (e e' : rel T) :
  symmetric e -> symmetric e' -> symmetric (relU e e').
Proof. move => sym_e sym_e' x y /=. by rewrite sym_e sym_e'. Qed.

Lemma sc_sym (T : Type) (e : rel T) : symmetric (sc e).
Proof. move => x y /=. by rewrite orbC. Qed.

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
Admitted.

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
  - move => /= [Hxy]. rewrite /sk_rel /= Hxy eq_sym Hxy /=.
    rewrite /adjacent. 
Admitted.



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

Lemma igraph_proof (G : graph) (x y : skeleton G) :
  consistent (interval x y) 
             (edge_set (interval x y) :\: (edges x x :|: edges y y)).
Admitted.

Definition igraph (G : graph) (x y : skeleton G) :=
  @point (subgraph_for (@igraph_proof G x y))
         (Sub x (intervalL x y))
         (Sub y (intervalR x y)).

Definition pgraph (G : graph) (U : {set G}) (x:G) :=
  @point (induced (@petal (skeleton G) U x))
         (Sub x (@petal_id (skeleton G) U x))
         (Sub x (@petal_id (skeleton G) U x)).

Lemma edge_part (G : graph) (U : {set skeleton G}) (x y z : skeleton G) :
  x \in CP U -> y \in CP U -> z \in CP U -> checkpoint.link_rel _ x y ->
  [disjoint val @: [set: edge (pgraph U z)] & 
            val @: [set: edge (igraph x y)]].
Proof.
  move => cp_x cp_y cp_z xy.
  (* Assume e is some edge in G[x,y] and G[z]. Then, both [source e]
     and [target e] are in [[x,y]] ∩ [[z]]_U. Thus z is either x or y
     and e is either an xx-edge or an yy-edge. This contradicts that e
     is an G[x,y] edge. *)
Admitted.

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
Lemma connected_skeleton (G : graph) V E (con : @consistent G V E) : 
  @connected (skeleton G) V -> 
  (forall e, e \in edge_set V -> source e != target e -> e \in E) ->
  connected [set: skeleton (subgraph_for con)].
Proof.
  move => conn_V all_edges. 
  move => x y xV yV. move: (conn_V _ _ (valP x) (valP y)). 
  (* ... *)
Admitted.

Lemma connected_pgraph (G : graph2) (U : {set G}) (x : G) : 
  connected [set: skeleton G] -> x \in @CP (skeleton G) U -> 
  connected [set: skeleton (pgraph U x)].
Proof.
  move => conn_G cp_x.
  apply: connected_skeleton => //. exact: connected_petal.
Qed.

Lemma connected_igraph (G : graph2) (x y: G) : 
  connected [set: skeleton G] -> 
  connected [set: skeleton (igraph x y)].
Proof.
  move => conn_G. apply: connected_skeleton.
  + exact: connected_interval.
  + move => e E1 E2. rewrite 4!inE E1 andbT negb_or. apply/andP;split.
    * apply: contraNN E2 => /andP [/eqP -> /eqP ->]; by rewrite eqxx.
    * apply: contraNN E2 => /andP [/eqP -> /eqP ->]; by rewrite eqxx.
Qed.

Lemma sub_pointxx (G : graph) (x:G) :
  sgraph.subgraph (sskeleton (point _ x x))
                  (skeleton G).
Proof.
  exists id => // u v /=. 
  case/or3P; solve [by right| by case/and3P => _ /eqP-> /eqP->; left].
Qed.

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

Lemma flesh_out (G : sgraph) : 
  exists G', sg_iso (sskeleton G') G /\ sg_iso (skeleton G') G.
Proof. (* for evert pair x -- y in G add a 0-edge *) Admitted.


