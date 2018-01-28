Require Import RelationClasses Morphisms Setoid Omega.

From mathcomp Require Import all_ssreflect.

Require Import edone finite_quotient preliminaries.
Require Import sgraph minor checkpoint cp_minor. 
Require Import multigraph subalgebra tm_iso skeleton bounded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs". 


(* TODO: resolve this name clash *)
Local Notation link_rel := checkpoint.link_rel.


Lemma consistentT (G : graph) (E : {set edge G}) : consistent setT E.
Proof. by []. Qed.
Arguments consistentT [G] E.

(** * Term Extraction *)

(** ** Termination Metric *)

Definition term_of_measure (G : graph2) :=
  (g_in == g_out :> G) + 2*#|edge G|.

Local Notation measure G := (term_of_measure G).

Ltac normH := match goal 
  with 
  | [ H : is_true (_ <= _) |- _] => move/leP : H 
  | [ H : is_true (_ == _) |- _] => move/eqP : H 
  end.
Ltac elim_ops := rewrite -multE -plusE -!(rwP leP).
Ltac somega := repeat normH; elim_ops; intros; omega.

Lemma measure_card (G' G : graph2) : 
  #|edge G'| < #|edge G| -> measure G' < measure G.
Proof. 
  rewrite /term_of_measure. 
  do 2 case: (g_in == g_out) => /=; somega.
Qed.

Lemma measure_io (G' G : graph2) : 
  (g_in == g_out :> G) -> (g_in != g_out :> G') -> #|edge G'| <= #|edge G| -> 
  measure G' < measure G.
Proof. 
  rewrite /term_of_measure. 
  do 2 case: (g_in == g_out) => //=; somega.
Qed.

Lemma measure_subgraph (G : graph2) V E (con : @consistent G V E) x y e : 
  e \notin E -> measure (@point (subgraph_for con) x y) < measure G.
Proof. 
  move => He. apply: measure_card. rewrite card_sig. 
  apply: proper_card. apply/properP. split; by [exact/subsetP| exists e].
Qed.

Lemma measure_node (G : graph2) V E (con : @consistent G V E) v x y : 
  connected [set: skeleton G] -> 
  v \notin V -> measure (@point (subgraph_for con) x y) < measure G.
Proof.
  move => /connectedTE conn_G Hv. 
  case/uPathP : (conn_G v (val x)) => p _. 
  have vx: v != val x. { apply: contraNN Hv => /eqP->. exact: valP. }
  case: (splitL p vx) => u [vu] _ {p vx}. rewrite -adjacentE in vu.
  case/andP: vu => _ /orP[] [/existsP [e He]].
  - refine (@measure_subgraph _ _ _ _ _ _ e _). 
    apply: contraNN Hv. move/con => [Hs Ht]. 
    move: He. by rewrite inE => /andP[/eqP<- _].
  - refine (@measure_subgraph _ _ _ _ _ _ e _). 
    apply: contraNN Hv. move/con => [Hs Ht]. 
    move: He. by rewrite inE => /andP[_ /eqP<-].
Qed.

(** ** Subroutines *)

Notation IO := ([set g_in; g_out]).
Notation "u :||: v" := (tmI u v) (at level 35, right associativity).
Notation "u :o: v" := (tmS u v) (at level 33, right associativity).

Definition lens (G : graph2) := 
  [&& edge_set (@petal G IO g_in)  == set0 ,
      edge_set (@petal G IO g_out) == set0 &
      @link_rel (skeleton G) g_in g_out].

Lemma get_edge (G : graph) (U : {set G}) (x y : skeleton G) : 
  x \in U -> y \in U -> x -- y -> exists e : edge G, e \in edge_set U.
Proof.
  move => Hx Hy. rewrite -adjacentE => /andP [_] /orP [A|A].
  all: case/existsP : A => e; rewrite !inE => /andP[/eqP S /eqP T].
  all: exists e; by rewrite inE S T Hx Hy.
Qed.

Lemma edgeless_petal (G : graph) (U : {set G}) x : 
  connected [set: skeleton G] -> x \in @CP G U ->
  edge_set (@petal G U x)  == set0 -> @petal G U x == [set x].
Proof.
  move => con_G cp_x.
  apply: contraTT => /petal_nontrivial [y Y1 Y2]. rewrite eq_sym in Y2.
  have con_Px := connected_petal con_G cp_x.
  have [||z Pz xz] := connected_card_gt1 con_Px _ _ Y2.
    exact: petal_id. done. 
  apply/set0Pn. apply: get_edge xz => //. exact: petal_id.
Qed.

Lemma lens_sinterval (G : graph2) :
  connected [set: skeleton G] -> lens G ->
  (@sinterval G g_in g_out = ~: IO).
Proof.
  move=> G_conn /and3P[] /edgeless_petal/eqP-/(_ G_conn (CP_extensive _)).
  rewrite !inE -setTD eqxx =>/(_ isT) petal_i.
  move=> /edgeless_petal/eqP-/(_ G_conn (CP_extensive _)).
  rewrite !inE eqxx orbT =>/(_ isT) petal_o /andP[iNo _].
  case/andP: (sinterval_petal_partition G_conn iNo) => /eqP<- _.
  rewrite petal_i petal_o /cover !bigcup_setU !bigcup_set1.
  rewrite setDUl setDv set0U setDE. apply: esym; apply/setIidPl.
  apply/subsetP=> x x_sI. rewrite !inE negb_or.
  apply/andP; split; apply: contraTneq x_sI =>->; by rewrite sinterval_bounds.
Qed.

Arguments cp : clear implicits.
Arguments Path : clear implicits.

Definition CK4F (G : graph2) := 
  connected [set: skeleton G] /\ K4_free (sskeleton G).

(** If G is a lens with non non-adjacent input and output, then it has
at least two parallel components *)
Lemma split_K4_nontrivial (G : graph2) : 
  g_in != g_out :> G -> 
  lens G -> 
  ~~ @adjacent G g_in g_out -> 
  CK4F G ->
  1 < #|components (@sinterval (skeleton G) g_in g_out)|.
Proof.
  move => A B C [D E]. 
  apply/equivalence_partition_gt1P.
  - move => x y z _ _ _. exact: (sedge_in_equiv (G := skeleton G)).
  - set H := sinterval _ _. apply: ssplit_K4_nontrivial (E) _ (D).
    + by rewrite -adjacentE A.
    + by case/and3P : B.
    + apply/eqP. apply: edgeless_petal => //=. 
      * apply: (@CP_extensive G); by rewrite !inE eqxx.
      * by case/and3P : B => ? _ _.
Qed.

Fixpoint pairs (T : Type) (s : seq T) {struct s} : seq (T * T) := 
  if s isn't x::s' then [::] 
  else if s' is y :: s'' then (x,y):: pairs s' else [::].

Lemma pairs_cons (T : Type) a b (s : seq T) : 
  pairs [:: a, b & s] = (a,b) :: pairs (b :: s).
Proof. done. Qed.

(* TOTHINK: this does not look easy to used *)
Lemma pairs_cat (T : Type) a1 a2 (s1 s2 : seq T) : 
  pairs (rcons s1 a1 ++ a2 :: s2) = 
  pairs (rcons s1 a1) ++ (a1,a2) :: pairs (a2 :: s2).
Admitted.

(** BEGIN: Temporary simplification: binary sequential split *)

Definition simple_check_point_term (g : graph2 -> term) (G : graph2) : term := 
  let (i,o) := (g_in : G, g_out : G) in 
  if  (edge_set (@petal G IO i) != set0) || (edge_set (@petal G IO o) != set0)
  then g (pgraph IO i) :o: g (igraph i o) :o: g (pgraph IO o)
  else if [pick z in @cp G i o :\: IO] isn't Some z then tm1 (* never happens *)
       else g (igraph i z) :o: g(pgraph IO z) :o: g(igraph z o).

(** END: Temporary simplification: binary sequential split *)


(** list of checkpoint bewteen x and y (excluding x) *)
(* NOTE: see insub in eqtype.v *)
(* TOTHINK: this actually does include both x and y *)
Definition checkpoint_seq (G : graph) (x y : G) := 
  if @idP (connect (@sedge (skeleton G)) x y) isn't ReflectT con_xy then [::]
  else sort (cpo con_xy) (enum (@cp (skeleton G) x y)).

Definition check_point_term (t : graph2 -> term) (G : graph2) :=
  let (i,o) := (g_in : G, g_out : G) in
  let c := checkpoint_seq i o in
  t (pgraph IO i) :o: 
  \big[tmS/tm1]_(p <- pairs c) (t(igraph p.1 p.2) :o: t(pgraph IO p.2)).

Fact redirect_proof1 (T : finType) x (A : {set T}) : x \in x |: A. 
Proof. by rewrite !inE eqxx. Qed.
Arguments redirect_proof1 [T x A].

(** subgraph induced by [i |: H] without i-selfloops and with output set
to [o] *)
Lemma redirect_consistent (G : graph2) (H : {set G}) (o : G) : 
  let H' := g_in |: (o |: H) in 
  consistent H' (edge_set H' :\: edges g_in g_in).
Proof. apply: consistent_setD. exact: induced_proof. Qed.

Fact redirect_output_proof (T : finType) x y (B : {set T}) : x \in y |: (x |: B). 
Proof. by rewrite !inE eqxx. Qed.
Arguments redirect_output_proof [T x y B].

Definition redirect_to (G : graph2) (H : {set G}) (o:G) :=
  @point (subgraph_for (@redirect_consistent G H o))
         (Sub g_in (setU11 _ _))
         (Sub o redirect_output_proof).

(** subgraph induced by [i |: H] without i-selfloops and with [o] set
to some neighbor of [i] in H *)
Definition redirect (G : graph2) (H : {set G}) : graph2 :=
  if [pick z in H | adjacent g_in z] isn't Some z then one2 
  else redirect_to H z.


Definition component (G : graph2) (H : {set G}) : graph2 := 
  @point (induced (g_in |: (g_out |: H)))
         (Sub g_in (setU11 _ _))
         (Sub g_out (setU1r _ (setU11 _ _))).

(** Possibly empty sequence of (trivial) terms corresponding to direct
i-o edges. Yields nonempty parallel composition when concatenated with
the terms for the i-o components *)
Definition tm_ (G : graph2) (e : edge G) := 
  if e \in edges g_in g_out then tmA (label e) else tmC (tmA (label e)).

Definition tmEs (G : graph2) : seq term := [seq tm_ e | e in @edge_set G IO].

(* NOTE: we assume the input graph to be connected and K4-free *)
Definition term_of_rec (term_of : graph2 -> term) (G : graph2) := 
  if g_in == g_out :> G
  then (* input equals output *)
    let E := @edge_set G IO in
    if E == set0 then
      if [pick C in @components G [set~ g_in]] is Some C then
        tmD (term_of (redirect C)) :||: term_of (induced2 (~: C))
      else tm1
    else (\big[tmI/tmT]_(e in @edge_set G IO) tm_ e) :||:
         term_of (point (remove_edges E) g_in g_out)
  else (* distinct input and output *)
    if lens G
    then (* no checkpoints and no petals on i and o *)
      let P := components (@sinterval (skeleton G) g_in g_out) in
      let E := @edge_set G IO in
      if E == set0 
      then 
        if [pick C in P] isn't Some C then tmT 
        else term_of (component C) :||: term_of (induced2 (~: C))
      else if P == set0 
           then \big[tmI/tmT]_(e in @edge_set G IO) tm_ e
           else  (\big[tmI/tmT]_(e in @edge_set G IO) tm_ e) :||: 
                 term_of (point (remove_edges E) g_in g_out) 
    else (* at least one nontrivial petal or checkpoint *)
      @simple_check_point_term term_of G.

Definition term_of := Fix tmT term_of_measure term_of_rec.

Lemma mem_pairs_sort (T : eqType) e x y (s : seq T) : 
  uniq s -> total e -> (x,y) \in pairs (sort e s) -> 
  [/\ x \in s, y \in s, x != y, e x y & forall z, z \in s -> e z x || e y z].
Admitted.

(** All pairs in the checkpoint sequence are adjacent in CP({i,o}) *)
Lemma cp_pairs_edge (G : graph) (i o x y : G) : 
  connected [set: skeleton G] ->
  (x,y) \in pairs (checkpoint_seq i o) -> 
  exists (px : x \in @CP G [set i;o]) (py : y \in @CP G [set i;o]), 
    (Sub x px : @CP_ G [set i;o]) -- (Sub y py).
Proof.
  move => conn_G. move/(_ i o) : (conn_G) => conn_io'.
  rewrite /checkpoint_seq. case: {-}_ / idP => [conn_io|].
  - move/mem_pairs_sort. case/(_ _ _)/Wrap => [||[P1 P2 P3 P4 P5]].
    + exact: enum_uniq. 
    + exact: (@cpo_total (skeleton G)).
    + rewrite !mem_enum in P1,P2.
      suff S: cp G x y \subset [set x; y].
      { have px: x \in @CP G [set i;o]. 
        { apply/bigcupP. exists (i,o); by rewrite // !inE !eqxx. }
        have py: y \in @CP G [set i;o].
        { apply/bigcupP. exists (i,o); by rewrite // !inE !eqxx. }
        exists px. exists py. by rewrite /= P3. }
      apply/subsetP => z Hz. move: (P5 z). rewrite mem_enum.
      have Hz': z \in cp G i o. { apply: cp_widen Hz => //. }
      move/(_ Hz'). move: Hz. 
      rewrite (cpo_cp P1 P2 P4) // !inE => /and3P[_ H1 H2].
      case/orP => H3. 
      * have H: cpo conn_io x z && cpo conn_io z x by rewrite H3.
        by rewrite (cpo_antisym _ _ H) // eqxx.
      * have H: cpo conn_io y z && cpo conn_io z y by rewrite H3.
        by rewrite (cpo_antisym _ _ H) // eqxx.        
  - rewrite restrictE // in conn_io'. by move => u;rewrite !inE.
Qed.

Notation sigraph := cp_minor.igraph.
Lemma sskeleton_add (G : graph) (x y : G) : 
  sgraph.subgraph (sskeleton (igraph x y))
                  (add_edge (sigraph G x y) istart iend).
Proof.
  rewrite /igraph /sigraph /sskeleton -/istart -/iend. 
Admitted.

Lemma CK4F_igraph (G : graph2) (x y : G) : 
  x \in cp G g_in g_out -> y \in cp G g_in g_out ->
  CK4F G -> x != y -> CK4F (igraph x y).
Proof.
  move => Hx Hy [conn_G K4F_G] xy. 
  split; first exact: connected_igraph.
  apply: subgraph_K4_free (sskeleton_add _ _) _.
  exact: igraph_K4F K4F_G.
Qed.

Lemma measure_igraph (G : graph2) :
    connected [set: skeleton G] ->
    (edge_set (@petal G IO g_in) != set0) || (edge_set (@petal G IO g_out) != set0) ->
    measure (@igraph G g_in g_out) < measure G.
Proof.
  move=> G_conn A.
Admitted.

Lemma skeleton_induced_edge (G : graph) (V : {set skeleton G}) u v : 
  ((val u : skeleton G) -- val v) = ((u : skeleton (induced V)) -- v).
Proof.
  rewrite /= /sk_rel. apply: sc_eq => {u v} u v /=.
  rewrite val_eqE. case E : (_ != _) => //=. 
  apply/existsP/existsP.
  - case => e e_uv. 
    have He: e \in edge_set V. 
    { case/andP : e_uv => E1 E2. rewrite inE (eqP E1) (eqP E2).
      apply/andP;split; exact: valP. }
    exists (Sub e He). by rewrite -!val_eqE.
  - case => e. rewrite -!val_eqE /= => e_uv. by exists (val e).
Qed.

(* TOTHINK: how to align induced subgraphs for simple graphs and
induced subgraphs for multigraphs *)
Lemma connected_induced (G : graph) (V : {set skeleton G}) : 
  connected V -> connected [set: skeleton (induced V)].
Proof. 
  move => conV. apply: connectedTI => u v. 
  move: (conV (val u) (val v) (valP u) (valP v)). 
  case/upathPR => p /upathW.
  elim: p u => [?|a p IH u]. 
  - move/spath_nil/val_inj ->. exact: connect0.
  - rewrite spath_cons /= -!andbA => /and4P [A B C D]. 
    apply: (connect_trans (y := Sub a B)); last exact: IH.
    apply: connect1. change (u -- (Sub a B)). 
    by rewrite -skeleton_induced_edge.
Qed.

Lemma induced_K4_free (G : graph2) (V : {set G}) : 
  K4_free (sskeleton G) -> K4_free (induced V).
Proof.
  apply: minor_K4_free. 
  apply: (minor_trans (y := skeleton G)).
  apply: sub_minor. apply: skel_sub. 
  (* NOTE: this is a relation on the respecive skeletons *)
  apply: sub_minor. apply: sub_sub. exact: induced_sub.
Qed.

Lemma CK4F_sub (G : graph2) (V : {set G})  x : 
  @connected G V -> CK4F G -> CK4F (point (induced V) x x).
Proof. 
  move => conV CK4F_G. split. 
  - exact: connected_induced.
  - apply: subgraph_K4_free (sub_pointxx _) _.
    apply: induced_K4_free. apply CK4F_G.
Qed.

Lemma CK4F_induced2 (G : graph2) (V : {set G}) :
    @connected G V -> CK4F G -> CK4F (induced2 V).
Proof.
  move=> V_conn G_CK4F. rewrite /induced2.
  case: {-}_ / idP => // i_V. case: {-}_ / idP => // o_V.
  split; first exact: connected_induced.
  case: G_CK4F => _. apply: subgraph_K4_free.
  exists val; first exact: val_inj.
  move=> x y xy. right. move: xy. rewrite /= -!(inj_eq val_inj) /=.
  case/or3P=> [xy|->|->] //. apply/orP. left.
  have /negbT : x == y = false := @sg_edgeNeq (induced V) x y xy.
  pattern x, y. revert x y xy.
  apply skelP; first by move=> x y xy; rewrite eq_sym sk_rel_sym.
  move=> e. rewrite /sk_rel/= -!(inj_eq val_inj)/= => -> /=.
  apply/orP. left. apply/'exists_andP. by exists (sval e).
Qed.


Lemma rec_petal (G : graph2) (x : G) : 
  CK4F G -> x \in @CP (skeleton G) IO -> g_in != g_out :> G ->
  CK4F (pgraph IO x) /\ measure (pgraph IO x) < measure G.
Proof.
  move => [conn_G K4F_G] cp_x Dio. split. 
  - apply: CK4F_sub => //. exact: connected_petal.
  - suff: (g_in \notin @petal G IO x) || (g_out \notin @petal G IO x).
    { by case/orP; exact: measure_node. }
    rewrite -negb_and. apply:contraNN Dio => /andP[].
    rewrite !(petal_cp conn_G) // => [/eqP-> /eqP-> //||]; 
      by apply CP_extensive; rewrite !inE eqxx.
Qed.  

Lemma cp_pairs_measure (G : graph2) x y :
  CK4F G -> ~~ lens G -> (x,y) \in pairs (@checkpoint_seq G g_in g_out) ->
  measure (igraph x y) < measure G.
Proof. 
  move => CK4F_G no_lens pair_xy. 
  rewrite /lens in no_lens. 
Admitted.

Lemma cp_pairs_CK4G (G : graph2) (x y : G) :
  CK4F G -> ~~ lens G -> (x,y) \in pairs (@checkpoint_seq G g_in g_out) ->
  CK4F (igraph x y).
Proof.
  move => [G_conn G_K4F] ? Hxy.
  move/cp_pairs_edge : (Hxy) => /(_ G_conn) [px] [py] link_xy. 
  apply: CK4F_igraph; admit.
Admitted.
                           
Definition check_point_wf (f g : graph2 -> term) (G : graph2) : 
  CK4F G -> 
  g_in != g_out :> G ->
  ~~ lens G -> 
  (forall H : graph2, CK4F H -> measure H < measure G -> f H = g H) -> 
  check_point_term f G = check_point_term g G.
Proof. 
  move => [G_conn G_K4F] Dio not_lens Efg.
  congr tmS. 
  - apply: Efg; apply rec_petal => // ; apply: CP_extensive; by rewrite !inE eqxx.
  - apply: eq_big_seq => [[x y] Hxy /=]. congr tmS. 
    + apply: Efg; by [apply: cp_pairs_CK4G|apply: cp_pairs_measure].
    + move/cp_pairs_edge : Hxy => /(_ G_conn) [px] [py] _. 
      by apply: Efg; apply rec_petal.
Qed.

Lemma CK4F_remove_component (G : graph2) (C : {set G}) :
  g_in == g_out :> G -> @edge_set G IO == set0 -> C \in @components G [set~ g_in] ->
  CK4F G -> CK4F (induced2 (~: C)).
Proof.
  move=> Eio _ C_comp G_CK4F. apply: CK4F_induced2 (G_CK4F).
Admitted.

Lemma measure_remove_component (G : graph2) (C : {set G}) :
  CK4F G -> C \in @components G (~: IO) -> measure (induced2 (~: C)) < measure G.
Proof.
  move=> [G_conn _] C_comp.
  case/and3P: (@partition_components G (~: IO)) => /eqP compU _ compN0.
  have /set0Pn[x x_C] : C != set0 by apply: contraTneq C_comp =>->.
  have {x_C} : x \notin ~: C by rewrite inE negbK.
  have : (g_in  : G) \notin ~: IO by rewrite !inE negbK eqxx.
  have : (g_out : G) \notin ~: IO by rewrite !inE negbK eqxx.
  rewrite -compU.
  move/bigcupP/(_ (ex_intro2 _ _ C C_comp _))=> /negP oNC.
  move/bigcupP/(_ (ex_intro2 _ _ C C_comp _))=> /negP iNC.
  have {iNC oNC} [iNC oNC] : g_in \in ~: C /\ g_out \in ~: C by rewrite !inE.
  rewrite induced2_induced. exact: measure_node.
Qed.

Lemma CK4F_redirect (G : graph2) C : 
  CK4F G -> g_in == g_out :> G -> C \in @components G [set~ g_in] ->
  CK4F (redirect C).
Proof.
  rewrite /redirect. case: pickP. 
  - (* moving the output along an edge does not change the (strong) skeleton *)
Admitted. 

Lemma measure_redirect (G : graph2) C : 
  CK4F G -> g_in == g_out :> G -> C \in @components G [set~ g_in] ->
  measure (redirect C) < measure G.
Proof.
  (* Since G is connected and C nonempty, there must be a neighbor of i.
  Hence, [redirect C] has distinct input an ouutput and no more edges than G. *)
Admitted. 

Lemma CK4F_lens (G : graph2) C : 
  CK4F G -> lens G -> C \in components (@sinterval (skeleton G) g_in g_out) -> 
  CK4F (component C).
Proof.
  set sI := sinterval _ _. move=> [G_conn G_K4F] G_lens C_comp.
  split; last by apply: subgraph_K4_free G_K4F; exact: sskeleton_subgraph_for.
  apply: connected_induced.
  case: (sinterval_components C_comp) => -[u] u_C iu [v] v_C ov.
  apply: connectedU_edge iu _ _; rewrite 3?inE ?eqxx ?u_C //;
  first exact: connected1.
  apply: connectedU_edge ov _ _; rewrite 1?inE ?eqxx ?v_C //;
  first exact: connected1.
  exact: connected_in_components C_comp.
Qed.

Lemma measure_lens (G : graph2) C :
  CK4F G -> lens G -> @edge_set G IO == set0 ->
  C \in components (@sinterval (skeleton G) g_in g_out) ->
  measure (component C) < measure G.
Proof.
  set sI := sinterval _ _. case/and3P: (partition_components sI).
  set P := components _.
  move=> /eqP compU compI comp0 [G_conn G_K4F] G_lens Eio0 C_comp.
  have iNo : g_in != g_out :> G
    by case/and3P: G_lens => _ _ /(@sg_edgeNeq (link_graph G))->.
  have Nio : ~~ @adjacent G g_in g_out.
  { apply: contraTN Eio0 => io. apply/set0Pn.
    case/orP: io => /existsP[e]; rewrite inE => /andP[/eqP src_e /eqP tgt_e].
    all: by exists e; rewrite !inE src_e tgt_e !eqxx //. }
  have : 1 < #|P| by exact: split_K4_nontrivial.
  rewrite (cardD1 C) C_comp add1n ltnS => /card_gt0P[/= D].
  rewrite !inE => /andP[DNC] D_comp.
  have /set0Pn[x x_D] : D != set0 by apply: contraTneq D_comp =>->.
  move/trivIsetP: compI => /(_ D C D_comp C_comp DNC)/disjointFr/(_ x_D) xNC.
  suff : x \notin g_in |: (g_out |: C) by exact: measure_node.
  have : x \in sI by rewrite -compU; apply/bigcupP; exists D.
  rewrite ![in ~~ _]inE xNC orbF.
  apply: contraTN =>/orP[]/eqP->; by rewrite (@sinterval_bounds G).
Qed.


Section SplitCP.
Variables (G : graph2).
Hypothesis CK4F_G : CK4F G.
Hypothesis Hio : g_in != g_out :> G.


(* g_out not in left side, g_in not in right side *)
(* neither g_in nor g_out is in the central petal *)

Lemma CK4F_split_cpL z :
 z \in cp G g_in g_out :\: IO -> CK4F (igraph g_in z).
Proof.
  move => Hz.
  apply: CK4F_igraph => //; first exact: (@mem_cpl G).
  - move: z Hz. apply/subsetP. exact: subsetDl.
  - apply: contraTN Hz => C. by rewrite !inE !negb_or (eqP C) eqxx.
Qed.

Lemma CK4F_split_cpR z :
 z \in cp G g_in g_out :\: IO -> CK4F (igraph z g_out).
Admitted.

Lemma CK4F_split_cpM z :
 z \in cp G g_in g_out :\: IO -> CK4F (@pgraph G IO z).
Admitted.

Lemma measure_split_cpL z :
 z \in cp G g_in g_out :\: IO -> measure (igraph g_in z) < measure G.
Proof.
  move => Hz. apply: (measure_node (v := g_out)); first apply CK4F_G.
  admit.
Admitted.

Lemma measure_split_cpR z :
 z \in cp G g_in g_out :\: IO -> measure (igraph z g_out) < measure G.
Admitted.

Lemma measure_split_cpM z :
 z \in cp G g_in g_out :\: IO -> measure (@pgraph G IO z) < measure G.
Admitted.

End SplitCP.

Definition simple_check_point_wf (f g : graph2 -> term) (G : graph2) : 
  CK4F G -> 
  g_in != g_out :> G ->
  ~~ lens G -> 
  (forall H : graph2, CK4F H -> measure H < measure G -> f H = g H) -> 
  simple_check_point_term f G = simple_check_point_term g G.
Proof.
  move => CK4F_G Eio nlens_G Efg.
  rewrite /simple_check_point_term.
  case: ifP => [A|A].
  - (* g_out not in left petal, e notin interval, g_in not in right petal *)
    rewrite ![f (pgraph _ _)]Efg; 
      try (apply rec_petal => //; apply: CP_extensive; by rewrite !inE eqxx).
    do 2 f_equal. rewrite Efg //. 
    * apply: CK4F_igraph => //=; last rewrite cp_sym; exact: (@mem_cpl G). 
    * apply: measure_igraph => //; by case: CK4F_G.
  - case: pickP => [z Hz|//]; repeat congr tmS.
    + rewrite Efg //. exact: CK4F_split_cpL. exact: measure_split_cpL.
    + have {Hz} Hz : z \in @CP G IO by move: Hz; rewrite inE CP_set2 => /andP[_ ->].
      by rewrite Efg //; apply rec_petal => //.
    + rewrite Efg //. exact: CK4F_split_cpR. exact: measure_split_cpR.
Qed.

Lemma CK4F_remove_edges (G : graph2) : 
  CK4F G -> g_in != g_out :> G -> lens G ->
  @edge_set G IO != set0 -> components (@sinterval G g_in g_out) != set0 -> 
  CK4F (point (remove_edges (@edge_set G IO)) g_in g_out).
Proof.
  move => CK4F_G Hio lens_G Es Ps. split.
  - (* if there is at least one component, then this component connects g_in and g_out *)
    admit.
  - apply: subgraph_K4_free (proj2 CK4F_G). 
    admit.
Admitted.

Lemma measure_remove_edges (G : graph2) (E : {set edge G}) (i o : G) :
  E != set0 -> measure (point (remove_edges E) i o) < measure G.
Proof.
  case/set0Pn => e inIO. apply: measure_card => /=. rewrite card_sig.
  apply: (card_ltnT (x := e)). by rewrite /= negbK.
Qed.

Lemma CK4F_remove_loops (G : graph2) :
  CK4F G -> g_in == g_out :> G ->
  CK4F (point (remove_edges (@edge_set G IO)) g_in g_out).
Admitted.

Lemma CK4F_lens_rest (G : graph2) C : 
  CK4F G -> g_in != g_out :> G -> lens G -> @edge_set G IO == set0 -> 
  C \in @components G (@sinterval G g_in g_out) -> CK4F (induced2 (~: C)).
Admitted.

Lemma measure_lens_rest (G : graph2) C : 
  CK4F G -> lens G -> C \in @components G (@sinterval G g_in g_out) ->
  measure (induced2 (~: C)) < measure G.
Proof.
  move=> G_CK4F G_lens. rewrite lens_sinterval //; last by case: G_CK4F.
  exact: measure_remove_component.
Qed.

Lemma term_of_eq (G : graph2) : 
  CK4F G -> term_of G = term_of_rec term_of G.
Proof.
  apply: Fix_eq => // {G} f g G CK4F_G Efg. rewrite /term_of_rec. 
  case: (boolP (@g_in G == g_out)) => Hio.
  - case (boolP (@edge_set G IO == set0)) => Es.
    + case: pickP => //= C HC. rewrite !Efg //.
      * exact: CK4F_remove_component.
      * move: HC. rewrite -[set1 g_in]setUid {2}(eqP Hio).
        exact: measure_remove_component.
      * exact: CK4F_redirect.
      * exact: measure_redirect.
    + congr tmI. rewrite Efg //.
      * exact: CK4F_remove_loops.
      * exact: measure_remove_edges.
  - case: (boolP (lens G)) => [deg_G|ndeg_G].
    + case: (boolP (_ == _)) => Es.
      * case: pickP => [C HC|//]. congr tmI.
        -- apply: Efg. exact: CK4F_lens. exact: measure_lens.
        -- apply: Efg. exact: CK4F_lens_rest. exact: measure_lens_rest.
      * case: (boolP (_ == _)) => Ps //. 
        rewrite Efg //. 
        -- exact: CK4F_remove_edges. 
        -- exact: measure_remove_edges.
    + exact: simple_check_point_wf.
Qed.

(** * Isomorphim Properties *)

Local Open Scope quotient_scope.
Local Notation "\pi x" := (\pi_(_) x) (at level 4).

Lemma comp_exit (G : graph2) (C : {set G}) : 
  connected [set: skeleton G] ->
  g_in == g_out :> G -> C \in @components G [set~ g_in] ->
  exists2 z : skeleton G, z \in C & z -- g_in.
Proof.
  move=> G_conn Eio C_comp.
  case/and3P: (@partition_components G [set~ g_in]) => /eqP compU compI comp0.
  have /card_gt0P[a a_C] : 0 < #|C|.
  { rewrite card_gt0. by apply: contraTneq C_comp =>->. }
  have aNi : a \in [set~ g_in]. { rewrite -compU. by apply/bigcupP; exists C. }
  rewrite -{C C_comp a_C}(def_pblock compI C_comp a_C).
  case/uPathP: (connectedTE G_conn a g_in) => p.
  move: (aNi); rewrite !inE. case/(splitR p) => [z][q][zi] {p}->.
  rewrite irred_cat'. case/and3P=> _ _ /eqP/setP/(_ g_in).
  rewrite !inE eq_sym sg_edgeNeq // nodes_end andbT => /negbT iNq.
  exists z => //.
  rewrite pblock_equivalence_partition // ?inE ?(sg_edgeNeq zi) //.
  + apply: (connectRI (p := q)) => x. rewrite !inE. by apply: contraTneq =>->.
  + exact: sedge_equiv_in.
Qed.

Lemma comp_dom2_redirect (G : graph2) (C : {set G}) : 
  connected [set: skeleton G] -> g_in == g_out :> G ->
  @edge_set G IO == set0 -> C \in @components G [set~ g_in] ->
  component C ≈ dom2 (redirect C).
Proof.
  move => G_conn Eio no_loops HC.
  rewrite /redirect. case: pickP => [x /andP [inC adj_x] |].
  - apply: subgraph_for_iso => //.
    + by rewrite (eqP Eio) setUA setUid [x |: C](setUidPr _) // sub1set. 
    + move: no_loops. rewrite -(eqP Eio) setUA setUid edge_set1 => /eqP->.
      by rewrite setD0 [x |: C](setUidPr _) // ?sub1set.
    + by rewrite /= (eqP Eio).
  - case: (comp_exit G_conn Eio HC) => z Z1 Z2.
    rewrite sg_sym -adjacentE in Z2. case/andP : Z2 => [A B].
    move/(_ z). by rewrite Z1 B. 
Qed.

Lemma componentless_one (G : graph2) :
  g_in == g_out :> G -> @edge_set G IO == set0 ->
  @components G [set~ g_in] == set0 -> G ≈ one2.
Admitted.

Lemma split_component (G : graph2) (C : {set G}) :
  @edge_set G IO == set0 -> C \in @components G (~: IO) ->
  G ≈ par2 (component C) (induced2 (~: C)).
Admitted.

Lemma split_cp (G : graph2) (u : skeleton G) :
  connected [set: skeleton G] -> u \in @cp G g_in g_out :\: IO ->
  edge_set (@petal G IO g_in) == set0 -> 
  edge_set (@petal G IO g_out) == set0 ->
  G ≈ seq2 (@igraph G g_in u) (seq2 (@pgraph G IO u) (@igraph G u g_out)).
Proof.
  move=> G_conn u_cpio pi_e0 po_e0. apply: iso2_sym. set G' := seq2 _ _.
  have [i_cp o_cp] : g_in \in @CP G IO /\ g_out \in @CP G IO.
  { by split; apply: CP_extensive; rewrite !inE eqxx. }
  have u_cp : u \in @CP G IO.
  { apply/bigcupP; exists (g_in, g_out) => /=; first by rewrite !inE !eqxx.
    by move: u_cpio; rewrite inE => /andP[_]. }
  have [uNi uNo] : u != g_in /\ u != g_out.
  { by move: u_cpio; rewrite 4!inE negb_or => /andP[]/andP[]. }
  have iNo : g_in != g_out :> G.
  { apply: contraTneq u_cpio => <-. by rewrite setUid cpxx !inE andNb. }
  have G_intv : [set: skeleton G] = @interval G g_in g_out.
  { case/andP: (sinterval_petal_partition G_conn iNo) => /eqP<- _.
    rewrite (eqP (edgeless_petal _ (CP_extensive _) pi_e0)) ?inE ?eqxx //.
    rewrite (eqP (edgeless_petal _ (CP_extensive _) po_e0)) ?inE ?eqxx //.
    by rewrite /cover !bigcup_setU !bigcup_set1. }
  pose f (x : G') : G :=
    match repr x with
    | inl x => val x
    | inr x => match repr x with
               | inl x => val x
               | inr x => val x
               end
    end.
  pose h (e : edge G') : edge G :=
    match e with
    | inl e => val e
    | inr e => match e with
               | inl e => val e
               | inr e => val e
               end
    end.

  pose valE := f_equal val. pose injL := seq2_injL. pose injR := seq2_injR.
  pose inLR := seq2_LR. pose inRL := fun e => seq2_LR (esym e).
  exists (f, h); split; first split; first apply: hom_gI => e.
  all: rewrite -?[(f, h).1]/f -?[(f, h).2]/h.

  - case: e => [e|[e|e]]; rewrite /h; split; rewrite // /f.
    + case: piP => -[y /injL<-//|y /inLR[/valE]]. rewrite [val (source e)]/= =>->{y}->.
      by case: piP => -[y /injL<-|y /inLR[_ ->]].
    + case: piP => -[y /injL<-//|y /inLR[/valE]]. rewrite [val (target e)]/= =>->{y}->.
      by case: piP => -[y /injL<-|y /inLR[_ ->]].
    + case: piP => -[y /inRL[->]/injL/valE//|y /injR<-{y}].
      by case: piP => -[y /injL<-|y /inLR[/valE?->]].
    + case: piP => -[y /inRL[->]/injL/valE//|y /injR<-{y}].
      by case: piP => -[y /injL<-|y /inLR[/valE?->]].
    + case: piP => -[y /inRL[->]/inRL[_]/valE//|y /injR<-{y}].
      by case: piP => -[y /inRL[->]/valE|y /injR<-].
    + case: piP => -[y /inRL[->]/inRL[_]/valE//|y /injR<-{y}].
      by case: piP => -[y /inRL[->]/valE|y /injR<-].

  - rewrite /f. case: piP => -[y /injL<-//|y /inLR[/valE H {y}->]].
    rewrite /= in H. by case: piP => -[y /injL<-|y /inLR[/valE?->]].
  - rewrite /f. case: piP => -[y /inRL[->]/inRL[_]/valE//|y /injR<-{y}].
    by case: piP => -[y /inRL[->]/valE|y /injR<-].

  - case/andP: (sinterval_cp_partition G_conn u_cpio) => /eqP compU _.
    have petal_node (x : G) : x \notin (g_in  |: @sinterval G g_in u) ->
                              x \notin (g_out |: @sinterval G u g_out) ->
                              x \in @petal G IO u.
    { rewrite ![x \in _ |: _]inE ![x \in set1 _]inE !negb_or.
      move=> /andP[/negbTE xNi /negbTE xNl] /andP[/negbTE xNo /negbTE xNr].
      have : x \in [set : skeleton G] by [].
      rewrite G_intv 4!inE xNi xNo -compU =>/bigcupP[?].
      rewrite 5!inE -orbA => /or3P[]/eqP->; by rewrite ?xNl ?xNr. }
    have intvL_node (x : G) : x \in g_in |: @sinterval G g_in u ->
                              x \in @interval G g_in u.
    { by rewrite [_ \in @interval G _ _]inE (lock sinterval) !inE -lock orbAC =>->. }
    have intvR_node (x : G) : x \in g_out |: @sinterval G u g_out ->
                              x \in @interval G u g_out.
    { by rewrite [_ \in @interval G _ _]inE (lock sinterval) !inE -lock -orbA =>->. }
    pose g (x : G) : G' :=
      match boolP (x \in g_in |: @sinterval G g_in u) with
      | AltTrue xL => \pi (inl (Sub x (intvL_node x xL)))
      | AltFalse xNl => match boolP (x \in g_out |: @sinterval G u g_out) with
                        | AltTrue xR => \pi (inr (\pi (inr (Sub x (intvR_node x xR)))))
                        | AltFalse xNr => \pi (inr (\pi (inl (Sub x (petal_node x xNl xNr)))))
                        end
      end.
    exists g => x.

    + rewrite /f.
      case Ex: (repr x) => [y|y]; last case Ey: (repr y) => [z|z]; rewrite /g.
      * have yL : val y \in @interval G g_in u := valP y. case: {-}_ / boolP => H1.
        { rewrite -[x]reprK Ex; congr \pi (inl _); exact: val_inj. }
        have Ey : val y = u.
        { move: H1 yL. rewrite [_ \in @interval G _ _]inE (lock sinterval) !inE -lock.
          rewrite negb_or => /andP[/negbTE-> /negbTE->]. by rewrite orbF => /eqP. }
        case: {-}_ / boolP => H2.
        { have := H2; rewrite {1}Ey 2!inE (@sinterval_bounds G).
          by move: u_cpio; rewrite 4!inE negb_or => /andP[]/andP[_]/negbTE->. }
        rewrite -[x]reprK Ex. apply/eqmodP.
        rewrite /equiv/equiv_pack/seq2_eqv -[_ == inl y]/false.
        rewrite eqEcard subUset !sub1set !inE !sum_eqE !cards2.
        rewrite -![inl _ == inr _]/false -![inr _ == inl _]/false.
        rewrite -(inj_eq val_inj) [_ && (_ || _)]andbC {1}Ey eqxx andbT.
        apply/eqP. apply/eqmodP. rewrite /equiv/equiv_pack/seq2_eqv sum_eqE.
        by rewrite -(inj_eq val_inj) SubK {1}Ey eqxx.
      * have z_petal : val z \in @petal G IO u := valP z.
        have /negbTE zNl : val z \notin g_in |: @sinterval G g_in u.
        { rewrite 2!inE negb_or sinterval_sym. apply/andP; split.
          - by apply: contraTneq z_petal =>->; rewrite (petal_cp G_conn) 1?eq_sym.
          - by rewrite (disjointFr (interval_petal_disj u _) z_petal). }
        have /negbTE zNr : val z \notin g_out |: @sinterval G u g_out.
        { rewrite 2!inE negb_or. apply/andP; split.
          - by apply: contraTneq z_petal =>->; rewrite (petal_cp G_conn) 1?eq_sym.
          - by rewrite (disjointFr (interval_petal_disj u _) z_petal). }
        case: {-}_ / boolP => H1; first by have := H1; rewrite zNl.
        case: {-}_ / boolP => H2; first by have := H2; rewrite zNr.
        rewrite -[x]reprK Ex -[y]reprK Ey. congr \pi (inr (\pi (inl _))).
        exact: val_inj.
      * have zR : val z \in @interval G u g_out := valP z.
        have /negbTE zNl : val z \notin g_in |: @sinterval G g_in u.
        { rewrite 2!inE negb_or. move: zR. rewrite 4!inE -orbA.
          case/or3P=> [/eqP->|/eqP->|zR]; apply/andP; split=> //.
          - by rewrite (@sinterval_bounds G).
          - by rewrite eq_sym.
          - rewrite (@sintervalP G) negb_and !negbK.
            by move: u_cpio; rewrite inE cp_sym => /andP[_]->.
          - apply: contraTneq zR => ->. rewrite (@sintervalP G) negb_and !negbK.
            by move: u_cpio; rewrite inE => /andP[_]->.
          - rewrite (disjointFl (@sinterval_disj_cp G g_in g_out u _) zR) //.
            by move: u_cpio; rewrite inE => /andP[_]. }
        case: {-}_ / boolP => H1; first by have := H1; rewrite zNl.
        case: {-}_ / boolP => H2.
        { rewrite -[x]reprK Ex -[y]reprK Ey. congr \pi (inr (\pi (inr _))).
          exact: val_inj. }
        move: zR; rewrite 4!inE. have := H2; rewrite 2!inE negb_or.
        case/andP=> /negbTE-> /negbTE->; rewrite !orbF => /eqP y_u.
        rewrite -[x]reprK Ex -[y]reprK Ey. congr \pi (inr _). apply/eqmodP.
        rewrite /equiv/equiv_pack/seq2_eqv -[_ == inr z]/false.
        rewrite eqEcard subUset !sub1set !inE !sum_eqE !cards2.
        rewrite -![inl _ == inr _]/false -![inr _ == inl _]/false.
        by rewrite -!(inj_eq val_inj) SubK y_u eqxx.

    + rewrite /f/g. case: {-}_ / boolP => H1; last case: {-}_ / boolP => H2.
      * case: piP => -[y /injL/valE//|y /inLR[/valE?{y}->]].
        by case: piP => -[y /injL<-|y /inLR[_]->].
      * case: piP => -[y /inRL[->]/inRL[_]/valE//|y /injR<-{y}].
        by case: piP => -[y /inRL[->]/valE|y /injR<-].
      * case: piP => -[y /inRL[->]/injL/valE//|y /injR<-{y}].
        by case: piP => -[y /injL<-|y /inLR[/valE?->]].
Admitted.

Definition sym2_ (G : graph2) (e : edge G) :=
  if e \in edges g_in g_out then sym2 (label e) else cnv2 (sym2 (label e)).

Lemma split_par_top (G : graph2) : 
  g_in != g_out :> G -> @components G (~: IO) == set0 -> @edge_set G IO == set0 ->
  G ≈ top2.
Admitted.

(** (a,true) -> io-edge / (a,false) -> oi-edge *)
Definition sym2b (a : sym) (b : bool) : graph2 :=
  if b then sym2 a else cnv2 (sym2 a).

Definition sym2b' (a : sym) (b : bool) : graph2 :=
  point (edge_graph a) (~~b) (b). 

Lemma sym_eqv (a : sym) (b : bool) : sym2b a b = sym2b' a b.
Proof. by case: b. Qed.

(** "false" is the input and "true" is the output *)
Definition edges2_graph (As : seq (sym * bool)) : graph := 
  {| vertex := [finType of bool];
     edge := [finType of 'I_(size As)];
     label e := (tnth (in_tuple As) e).1;
     source e := ~~ (tnth (in_tuple As) e).2;
     target e := (tnth (in_tuple As) e).2 |}.

Definition edges2 (As : seq (sym * bool)) : graph2 := 
  point (edges2_graph As) false true.

Lemma edges2_nil : edges2 nil ≈ top2.
Admitted.

Lemma ord_0Vp n (o : 'I_n.+1) : (o = ord0) + ({o' : 'I_n | o'.+1 = o :> nat}).
Proof.
  case: (unliftP ord0 o); last by left.
  move => o' A. right. exists o'. by rewrite A.
Qed.

Lemma edges2_cons (a : sym) (b : bool) (Ar : seq (sym * bool)) : 
  edges2 ((a, b) :: Ar) ≈ par2 (sym2b a b) (edges2 Ar).
Proof.
  rewrite sym_eqv. (* this makes h actually typecheck *)
  set E1 := edges2 _.
  set E2 := par2 _ _.
  pose f (x : E1) : E2 := \pi (inr x).
    (* if x == g_in then \pi (inr g_in) else \pi (inr g_out). *) 
  pose g (x : E2) : E1 :=
    match repr x with 
    | inl x => if x == g_in then g_in else g_out
    | inr x => x end.
  pose h (x : edge E1) : edge E2 := 
    match ord_0Vp x with 
    | inl e => inl tt
    | inr (exist o H) => inr o
    end.
  exists (f,h); repeat split.
  - move => e. 
    rewrite [source]lock /= -lock. rewrite /h /=.
    case: (ord_0Vp e) => [E|[o' Ho']].
    + rewrite E /f /=. destruct b eqn: def_b.
      all: symmetry; apply/eqmodP => //=.
      exact: par2_eqv_ii.
      exact: par2_eqv_oo.
    + rewrite (tnth_cons Ho'). case: (tnth _ _) => a' b' /=.
      rewrite /f /=. by case: b'.
  - move => e. 
    rewrite [target]lock /= -lock. rewrite /h /=.
    case: (ord_0Vp e) => [E|[o' Ho']].
    + rewrite E /f /=. destruct b eqn: def_b.
      all: symmetry; apply/eqmodP => //=.
      exact: par2_eqv_oo.
      exact: par2_eqv_ii.
    + rewrite (tnth_cons Ho'). case: (tnth _ _) => a' b' /=.
      rewrite /f /=. by case: b'.
  - move => e. rewrite /= /h. case: (ord_0Vp e) => [-> //|[o' Ho']].
    by rewrite (tnth_cons Ho'). 
  - rewrite /f /=. symmetry. apply/eqmodP => //=. exact: par2_eqv_ii.
  - rewrite /f /=. symmetry. apply/eqmodP => //=. exact: par2_eqv_oo.
  - apply: (Bijective (g := g)) => /= x. 
    + rewrite /f /g /=. case: piP => [] [y|y] /= /esym Hy.
      * move/(@par2_LR (sym2b' a b) (edges2 Ar)) : Hy.
        case => [[-> ->]|[-> ->]]; by destruct b.
      * move/(@par2_injR (sym2b' a b) (edges2 Ar)) : Hy. apply. 
        by destruct b.
    + rewrite /f /g /=. case Rx : (repr x) => [y|y]; last by rewrite -Rx reprK.
      rewrite -[x]reprK Rx => {x Rx}. symmetry. apply/eqmodP => /=. 
      destruct b;destruct y => //=;
      solve [exact: par2_eqv_oo|exact: par2_eqv_ii].
  - pose h' (e : edge E2) : edge E1 := 
      match e with inl tt => ord0 | inr i => lift ord0 i end.
    apply: (Bijective (g := h')) => /= x.
    + rewrite /h /h'. case: (ord_0Vp x) => [-> //|[o' Ho']].
      apply: ord_inj. by rewrite lift0.
    + rewrite /h /h'. case: x => [[]|x]. 
      by case: (ord_0Vp ord0) => [|[o' Ho']].
      case: (ord_0Vp _) => [|[o']]. 
      * move/(f_equal (@nat_of_ord _)). by rewrite lift0.
      * move/eqP. rewrite lift0 eqSS => /eqP E. 
        congr inr. exact: ord_inj.
Qed.

Lemma edges2_big (As : seq (sym * bool)) : 
  edges2 As ≈ \big[par2/top2]_(x <- As) sym2b x.1 x.2.
Proof.
  elim: As => [|[a b] Ar IH].
  - by rewrite big_nil edges2_nil.
  - by rewrite big_cons /= -IH edges2_cons.
Qed. 

Definition strip (G : graph2) (e : edge G) := 
  if e \in edges g_in g_out then (label e,true) else (label e,false).

Lemma edges_st (G : graph2) (x y : G) (e : edge G) : 
  e \in edges x y -> (source e = x) * (target e = y).
Proof. by rewrite inE => /andP[/eqP -> /eqP ->]. Qed.


Lemma split_io_edges (G : graph2) : 
  let E : {set edge G} := edges g_in g_out :|: edges g_out g_in in
  G ≈ par2 (edges2 [seq strip e | e in E]) (point (remove_edges E) g_in g_out).
Proof.
  move => E.
  set G' := par2 _ _.
  pose S := [seq strip e | e in E].
  pose n := size S.
  (* have e0 : edge (edges2 [seq strip e | e in E]). admit. *)
  pose f (x : G) : G' := \pi (inr x).
  pose g (x : G') : G := 
    match repr x with 
    | inl x => if x then g_out else g_in
    | inr x => x
    end.
  have h_proof e : e \in E -> index e (enum E) < n. 
  { move => A. by rewrite /n /S size_map index_mem mem_enum. }
  pose h (e : edge G) : edge G' :=
    match boolP (e \in E) with 
    | AltTrue p => inl (Ordinal (h_proof e p))
    | AltFalse p => inr (Sub e p)
    end.
  exists (f,h); repeat split. 
  - move => e /=. rewrite /h. case: {-}_ / boolP => p //.
    symmetry. apply/eqmodP => /=. move: (h_proof _ _) => He. 
    rewrite tnth_map_in ?mem_enum //. 
    move: p. rewrite inE /strip. case: ifP => /= [A _|A B].
    + apply: par2_eqv_ii => //. by rewrite (edges_st A).
    + apply: par2_eqv_oo => //. by rewrite (edges_st B).
  - move => e /=. rewrite /h. case: {-}_ / boolP => p //.
    symmetry. apply/eqmodP => /=. move: (h_proof _ _) => He. 
    rewrite tnth_map_in ?mem_enum //. 
    move: p. rewrite inE /strip. case: ifP => /= [A _|A B].
    + apply: par2_eqv_oo => //. by rewrite (edges_st A).
    + apply: par2_eqv_ii => //. by rewrite (edges_st B).
  - move => e /=. rewrite /h. case: {-}_ / boolP => p //.
    rewrite tnth_map_in ?mem_enum // /strip. by case: ifP.
  - rewrite /= /f. symmetry. apply/eqmodP => /=. 
    exact: par2_eqv_ii.
  - rewrite /= /f. symmetry. apply/eqmodP => /=. 
    exact: par2_eqv_oo.
  - apply: (Bijective (g := g)) => x /=.
    + rewrite /f /g. case: piP => /= [[y|y]] /esym Hy.
      * move/(@par2_LR (edges2 [seq strip e | e in E]) 
                       (point (remove_edges E) g_in g_out)) : Hy.
        by case => [][-> ->]. 
      * exact: (@par2_injR (edges2 [seq strip e | e in E]) 
                           (point (remove_edges E) g_in g_out)).
    + rewrite /f /g. case def_y : (repr x) => [y|y].
      * rewrite -[x]reprK def_y. symmetry. apply/eqmodP => /=. 
        destruct y => //=; solve [exact: par2_eqv_oo|exact: par2_eqv_ii].
      * by rewrite -def_y reprK. 
  - rewrite /=. 
    have cast: size [seq strip e | e in E] = size (enum E).
    { by rewrite size_map. }
    pose h' (e : edge G') := 
      match e with 
      | inl i => (tnth (in_tuple (enum E)) (cast_ord cast i))
      | inr e => val e
      end.
    apply: (Bijective (g := h')) => e.
    + rewrite /h /h'. case: {-}_ / boolP => p //. 
      by rewrite /cast_ord /tnth nth_index //= ?mem_enum.
    + rewrite /h'. case: e => [i|e]. 
      * rewrite /h. case: {-}_/ boolP => p //.
        -- move: (h_proof _ _) => A. 
           congr inl. apply: val_inj => /=. 
           rewrite /tnth index_uniq //. exact: enum_uniq.
        -- case: notF. by rewrite -mem_enum mem_tnth in p. 
      * rewrite /h. case: {-}_/ boolP => p //.
        -- case:notF. by rewrite (negbTE (valP e)) in p.
        -- congr inr. exact: val_inj.
Qed.

Lemma remove0 (G : graph2) : 
  point (@remove_edges G set0) g_in g_out ≈ G.
Admitted.

Lemma split_pip (G : graph2) : 
  connected [set: skeleton G] -> g_in != g_out :> G ->
  G ≈ seq2 (@pgraph G IO g_in) (seq2 (@igraph G g_in g_out) (@pgraph G IO g_out)).
Proof.
  move=> G_conn Eio. apply: iso2_sym. set G' := seq2 _ _.
  pose f (x : G') : G :=
    match repr x with
    | inl x => val x
    | inr x => match repr x with
               | inl x => val x
               | inr x => val x
               end
    end.
  pose h (x : edge G') : edge G :=
    match x with
    | inl x => val x
    | inr (inl x) => val x
    | inr (inr x) => val x
    end.

  pose valE := f_equal val. pose injL := seq2_injL. pose injR := seq2_injR.
  pose inLR := seq2_LR. pose inRL := fun e => seq2_LR (esym e).
  exists (f, h); split; first split; first apply: hom_gI => e.
  all: rewrite -?[(f, h).1]/f -?[(f, h).2]/h.

  - case: e => [e|[e|e]]; rewrite /h; split=> //.
    + rewrite /f. case: piP => -[x /injL<-//|x /inLR[He {x}->]].
      move: He => /valE. rewrite [val (source e)]/= =>->.
      by case: piP=> -[x /injL<-|x /inLR[/valE? {x}->]].
    + rewrite /f. case: piP => -[x /injL<-//|x /inLR[He {x}->]].
      move: He => /valE. rewrite [val (target e)]/= =>->.
      by case: piP=> -[x /injL<-|x /inLR[/valE? {x}->]].
    + rewrite /f. case: piP => -[x /inRL[->]/injL/valE//|x /injR<-{x}].
      by case: piP => -[x /injL<-|x /inLR[/valE/=->->]].
    + rewrite /f. case: piP => -[x /inRL[->]/injL/valE//|x /injR<-{x}].
      by case: piP => -[x /injL<-|x /inLR[/valE/=->->]].
    + rewrite /f. case: piP => -[x|x /injR<-{x}].
        by move=> /inRL[->]/inRL[]/valE/=?/valE/=->.
      by case: piP => -[x /inRL[->]/valE/=->|x /injR<-].
    + rewrite /f. case: piP => -[x|x /injR<-{x}].
        by move=> /inRL[->]/inRL[]/valE/=?/valE/=->.
      by case: piP => -[x /inRL[->]/valE/=->|x /injR<-].

  - rewrite /f. case: piP => -[x /injL<-//|x /inLR[_{x}->]].
    by case: piP => -[x /injL<-|x /inLR[/valE/=?->]].
  - rewrite /f. case: piP => -[x /inRL[->]/inRL[/valE? _]//|x /injR<-{x}].
    by case: piP => -[x /inRL[->]|x /injR<-].

  - case/andP: (sinterval_petal_partition G_conn Eio) => /eqP nodeU nodeI.
    have sintv_node (x : G) : x \notin @petal G IO g_in ->
                              x \notin @petal G IO g_out ->
                              x \in @sinterval G g_in g_out.
    { move=> /negbTE Npi /negbTE Npo. have : x \in [set: G] by [].
      by rewrite -nodeU /cover !bigcup_setU !bigcup_set1 2!inE Npi Npo. }
    have intv_node (x : G) : x \in @sinterval G g_in g_out ->
                             x \in  @interval G g_in g_out.
    { by rewrite [x \in @interval G _ _]inE => ->. }
    pose g (x : G) : G' :=
      match boolP (x \in @petal G IO g_in), boolP (x \in @petal G IO g_out) with
      | AltTrue pi, _ => \pi (inl (Sub x pi))
      | _, AltTrue po => \pi (inr (\pi (inr (Sub x po))))
      | AltFalse Npi, AltFalse Npo =>
        let pintv := intv_node x (sintv_node x Npi Npo) in
        \pi (inr (\pi (inl (Sub x pintv))))
      end.
    exists g => x.

    + rewrite /f. case Ex: (repr x) => [y|y]; last case Ey: (repr y) => [z|z].
      * have y_pi : val y \in @petal G IO g_in := valP y.
        rewrite /g. case: {-}_ / boolP => [?|H]; last by have := H; rewrite {1}y_pi.
        rewrite -[x]reprK Ex. congr \pi (inl _). exact: val_inj.
      * have : val z \in @interval G g_in g_out := valP z.
        rewrite 4!inE -orbA => /or3P[/eqP|/eqP|] Hz.
        -- rewrite Hz /g. case: {-}_ / boolP=> H; last first.
             by have := H; rewrite ?{1}(@petal_id G IO g_in).
           rewrite -[x]reprK Ex. apply/eqmodP.
           rewrite /equiv/equiv_pack/seq2_eqv -[_ == inr y]/false.
           rewrite eqEcard subUset !sub1set !inE sum_eqE !cards2.
           rewrite -![inl _ == inr _]/false -![inr _ == inl _]/false.
           rewrite -(inj_eq val_inj) eqxx sum_eqE andbT -[y]reprK Ey.
           apply/eqP. apply/eqmodP.
           by rewrite /equiv/equiv_pack/seq2_eqv sum_eqE -(inj_eq val_inj) Hz eqxx.
        -- rewrite Hz /g. have : g_out \in @petal G IO g_out by exact: petal_id.
           move=> /(disjointFl(petal_disj G_conn(CP_extensive _)(CP_extensive _)Eio)).
           rewrite 6!inE 2!eqxx orbT => /(_ _ _)/Wrap[]// o_pi.
           case: {-}_ / boolP=> Hi; first by have := Hi; rewrite {1}o_pi.
           case: {-}_ / boolP=> Ho; last first.
             by have := Ho; rewrite ?{1}(@petal_id G IO g_out).
           rewrite -[x]reprK Ex -[y]reprK Ey. congr \pi (inr _). apply/eqmodP.
           rewrite /equiv/equiv_pack/seq2_eqv -[_ == inl z]/false.
           rewrite eqEcard subUset !sub1set !inE sum_eqE !cards2.
           rewrite -![inl _ == inr _]/false -![inr _ == inl _]/false.
           rewrite -(inj_eq val_inj) eqxx sum_eqE andbT orbF.
           apply/eqP. exact: val_inj.
        -- rewrite /g.
           have piF : val z \in @petal G IO g_in = false.
           { apply: disjointFl Hz. apply: interval_petal_disj.
             apply: CP_extensive. by rewrite !inE eqxx. }
           case: {-}_ / boolP => pi; first by have := pi; rewrite {1}piF.
           have poF : val z \in @petal G IO g_out = false.
           { apply: disjointFl Hz. rewrite sinterval_sym. apply: interval_petal_disj.
             apply: CP_extensive. by rewrite !inE eqxx. }
           case: {-}_ / boolP => po; first by have := po; rewrite {1}poF.
           rewrite -[x]reprK Ex -[y]reprK Ey. congr \pi (inr (\pi (inl _))).
           exact: val_inj.
      * have y_po : val z \in @petal G IO g_out := valP z.
        have := disjointFl(petal_disj G_conn(CP_extensive _)(CP_extensive _)Eio)y_po.
        rewrite !inE !eqxx orbT => /(_ _ _)/Wrap[]// y_pi.
        rewrite /g. case: {-}_ / boolP => H1; first by have := H1; rewrite {1}y_pi.
        case: {-}_ / boolP => H2; last by have := H2; rewrite {1}y_po.
        rewrite -[x]reprK Ex -[y]reprK Ey. congr \pi (inr (\pi (inr _))).
        exact: val_inj.

    + rewrite /f/g. case: {-}_ / boolP => H1; last case: {-}_ / boolP => H2.
      * case: piP => -[y /injL/valE<-//|y /inLR[/valE]].
        rewrite SubK =>->{y}->. by case: piP => -[y /injL<-|y /inLR[/valE?->]].
      * case: piP => -[y /inRL[->]/inRL[/valE?/valE/=->]//|y /injR<-{y}].
        by case: piP => -[y /inRL[->]/valE|y /injR<-].
      * case: piP => -[y /inRL[->]/injL/valE//|y /injR<-{y}].
        by case: piP => -[y /injL<-|y /inLR[/valE?->]].

  - case/andP: (interval_petal_edge_partition G_conn Eio) => /eqP edgeU edgeI.
    have intv_edge (e : edge G) :
      e \notin edge_set (@petal G IO g_in) -> e \notin edge_set (@petal G IO g_out) ->
      e \in @interval_edges G g_in g_out.
    { move=> /negbTE Npi /negbTE Npo. have : e \in [set: edge G] by [].
        by rewrite -edgeU /cover !bigcup_setU !bigcup_set1 2!inE Npi Npo. }
    pose k (e : edge G) : edge G' :=
      match boolP (e \in edge_set (@petal G IO g_in)),
            boolP (e \in edge_set (@petal G IO g_out)) with
      | AltTrue pi, _ => inl (Sub e pi)
      | _, AltTrue po => inr (inr (Sub e po))
      | AltFalse Npi, AltFalse Npo =>
        let pintv := intv_edge e Npi Npo in inr (inl (Sub e pintv))
    end.
    exists k => e; rewrite /h/k; last by repeat case: {-}_ / boolP => ?.
    case: e => [e|[e|e]].

    + have He : val e \in edge_set (@petal G IO g_in) := valP e.
      case: {-}_ / boolP => H1; last by have := H1; rewrite {1}He.
      congr inl. exact: val_inj.
    + have He : val e \in @interval_edges G g_in g_out := valP e.
      case: {-}_ / boolP => H1.
      { case: (disjointE (interval_petal_edges_disj _ _ _) H1 He) => //;
        by apply: CP_extensive; rewrite !inE eqxx. }
      rewrite {4}interval_edges_sym in He.
      case: {-}_ / boolP => H2.
      { case: (disjointE (interval_petal_edges_disj _ _ _) H2 He) => //;
        by apply: CP_extensive; rewrite !inE eqxx. }
      congr (inr (inl _)). exact: val_inj.
    + have He : val e \in edge_set (@petal G IO g_out) := valP e.
      case: {-}_ / boolP => H1.
      { case: (disjointE (petal_edges_disj _ _ _ Eio) H1 He) => //;
        by apply: CP_extensive; rewrite !inE eqxx. }
      case: {-}_ / boolP => H2; last by have := H2; rewrite {1}He.
      congr (inr (inr _)). exact: val_inj.
Qed.

Lemma componentless_top (G : graph2) : 
  g_in != g_out :> G -> @components G (~: IO) == set0 -> 
  point (@remove_edges G (edge_set IO)) g_in g_out ≈ top2.
Admitted.

Lemma lens_io_set (G : graph2) : 
  lens G -> @edge_set G IO = edges g_in g_out :|: edges g_out g_in.
Admitted.

Lemma edges2_graph_of (G : graph2) : 
  edges2 [seq strip e | e in @edges G g_in g_out :|: edges g_out g_in] ≈ 
  graph_of_term (\big[tmI/tmT]_(e in (@edges G g_in g_out :|: edges g_out g_in)) tm_ e).
Proof.
  rewrite edges2_big // big_map.
  rewrite graph_of_big_tmIs //. rewrite -big_enum_in.
  set s := enum _. 
  apply: big_par2_congr'.
  move => e. rewrite mem_enum /tm_ /strip inE. by case: (e \in edges g_in _). 
Qed.

Theorem term_of_iso (G : graph2) : 
  CK4F G -> iso2 G (graph_of_term (term_of G)).
Proof.
  elim: (wf_leq term_of_measure G) => {G} G _ IH CK4F_G.
  rewrite term_of_eq // /term_of_rec. 
  case: ifP => [C1|/negbT C1].
  - (* selfloops / io-redirect *)
    case: ifP => [C2|/negbT C2] /=.
    + case: pickP => [C HC|/(_ _) HC] /=.
      * rewrite {1}[G](@split_component _ C) // -?(eqP C1) ?setUid //.
        have G_conn : connected [set: skeleton G] by case: CK4F_G.
        apply: par2_congr; rewrite -IH ?comp_dom2_redirect //.
        -- exact: measure_redirect.
        -- exact: CK4F_redirect.
        -- move: HC. rewrite -[set1 g_in]setUid {2}(eqP C1).
           exact: measure_remove_component.
        -- exact: CK4F_remove_component.
      * have : @components G [set~ g_in] == set0.
        { rewrite -subset0. apply/subsetP => C. by rewrite HC. }
        exact: componentless_one.
    + rewrite {1}[G]split_io_edges. set E := edges _ _ :|: edges _ _.
      have Eio : E = edge_set IO. by rewrite /E (eqP C1) !setUid edge_set1.
      rewrite -{1}Eio {2}Eio. apply: par2_congr; first exact: edges2_graph_of.
      apply: IH; [exact: measure_remove_edges | exact: CK4F_remove_loops].
  - case: ifP => [C2|/negbT C2].
    + (* parallel split *)
      have EC := lens_sinterval (proj1 CK4F_G) C2.
      case: (boolP (_ == set0)) => C3.
      * case: pickP => [C HC|]. 
        -- rewrite EC in HC. rewrite {1}[G](split_component _ HC) //=.  
           apply: par2_congr. 
           ++ rewrite -IH //; rewrite -EC in HC.
              exact: measure_lens. exact: CK4F_lens.
           ++ rewrite -IH //; rewrite -EC in HC. 
              exact: measure_lens_rest. exact: CK4F_lens_rest.
        -- have := split_K4_nontrivial C1 C2 _ CK4F_G. 
           rewrite edge_set_adj // => /(_ isT)/ltnW. 
           case/card_gt0P => C HC /(_ C). by rewrite HC.
      * rewrite EC.
        case: (boolP (_ == set0)) => C4 /=.
        -- rewrite {1}[G]split_io_edges -{2}lens_io_set //.
           rewrite componentless_top // par2_idR lens_io_set //.
           exact: edges2_graph_of.
        -- rewrite {1}[G]split_io_edges /=. 
           apply: par2_congr. 
           ++ rewrite lens_io_set //. exact: edges2_graph_of.
           ++ rewrite -IH lens_io_set // -lens_io_set //. 
              exact: measure_remove_edges.
              rewrite -EC in C4. exact: CK4F_remove_edges.
    + (* petal/sequential split *) 
      rewrite /simple_check_point_term. 
      case: ifP => [A|/negbT A].
      * rewrite /=. (* TODO: clean this up *)
        rewrite -IH; first last. 
          apply rec_petal => //; apply: CP_extensive; by rewrite !inE eqxx.
          apply rec_petal => //; apply: CP_extensive; by rewrite !inE eqxx.
        rewrite -IH; first last.
          apply: CK4F_igraph => //; last rewrite cp_sym; exact: mem_cpl.
          apply: measure_igraph => //; by case: CK4F_G.
        rewrite -IH; first last. 
          apply rec_petal => //; apply: CP_extensive; by rewrite !inE eqxx.
          apply rec_petal => //; apply: CP_extensive; by rewrite !inE eqxx.
          case: CK4F_G => G_conn _; exact: split_pip.
      * move: A. rewrite negb_or !negbK. case/andP => A B.
        rewrite /lens !negb_and A B (negbTE C1) /= in C2.
        case: pickP => [z Hz|C]; last first.
        { case:notF. apply: contraNT C2 => _. rewrite -setD_eq0. 
          apply/eqP. apply/setP => x. by rewrite C inE. }
        rewrite /=. 
        rewrite {1}[G](split_cp (proj1 CK4F_G) Hz) //. repeat apply: seq2_congr.
        -- rewrite -IH //. exact: measure_split_cpL. exact: CK4F_split_cpL.
        -- suff ? : z \in @CP G IO. { rewrite -IH //; by apply rec_petal. }
           case/setDP : Hz => Hz _. apply/bigcupP; exists (g_in,g_out) => //. 
           by rewrite !inE !eqxx.
        -- rewrite -IH //. exact: measure_split_cpR. exact: CK4F_split_cpR.
Qed.

(** * Minor Exclusion Corollaries *)

Corollary minor_exclusion_2p (G : graph2) :
  connected [set: skeleton G] -> 
  K4_free (sskeleton G) <-> 
  exists (T:tree) (B : T -> {set G}), [/\ decomp T G B, width B <= 3 & compatible B].
Proof.
  move => conn_G. split => [K4F_G|[T [B [B1 B2 B3]]]].
  - have [T [B] [B1 B2 B3]] := (graph_of_TW2 (term_of G)).
    have [i hom_i bij_i] := term_of_iso (conj conn_G K4F_G).
    exists T. exists (fun t => [set x | i.1 x \in B t]). 
    (* lift decomposition along isomorphim *) 
    admit.
  - apply: (TW2_K4_free (G := sskeleton G)) B2.
    exact: decomp_sskeleton.
Admitted.


Corollary sminor_exclusion (G : sgraph) :
  connected [set: G] -> 
  K4_free G <-> 
  exists (T:tree) (B : T -> {set G}), sdecomp T G B /\ width B <= 3.
Proof.
  move => conn_G. split=> [K4F_G | [T][B][]]; last exact: TW2_K4_free.
  case: (posnP #|G|) =>[G_empty | /card_gt0P[x _]].
  { exists tunit; exists (fun _ => [set: G]). split; first exact: triv_sdecomp.
    apply: leq_trans (width_bound _) _. by rewrite G_empty. }
  have [G' [iso_Gs iso_G]] := flesh_out x.
  have conn_G' : connected [set: skeleton G'].
  { admit. (* lift along iso *) }
  have M := minor_exclusion_2p conn_G'.  
  have/M [T [B [B1 B2 B3]]] : K4_free (sskeleton G').
  { admit. (* lift along iso *) }
  exists T.
  have: sdecomp T (sskeleton G') B by exact: decomp_sskeleton.
  admit. (* lift along iso *)
Admitted.
