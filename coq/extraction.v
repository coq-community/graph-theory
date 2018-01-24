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
  (@sinterval G g_in g_out = [set: G] :\: IO).
Proof.
  move=> G_conn /and3P[] /edgeless_petal/eqP-/(_ G_conn (CP_extensive _)).
  rewrite !inE eqxx =>/(_ isT) petal_i.
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
    if [pick e in @edges G g_in g_in] is Some e
    then (* e is a self-loop on the input *)
      (tm1 :||: tmA (label e)) :o:
      term_of (point (remove_edges [set e]) g_in g_in)
    else (* the input has no self-loops *)
      let P := @components G [set~ g_in] in
      (\big[tmS/tm1]_(C in P) tmD (term_of (redirect C)))
  else (* distinct input and output *)
    if lens G
    then (* no checkpoints and no petals on i and o *)
      let P := components (@sinterval (skeleton G) g_in g_out) in
      let E := @edge_set G IO in
      if E == set0 then big_tmI [seq term_of (component C) | C in P]
      else if P == set0 then big_tmI (tmEs G) 
           else let t0 := term_of (point (remove_edges E) g_in g_out) in
                \big[tmI/t0]_(e in @edge_set G IO) tm_ e
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

Lemma CK4F_remove_loop (G : graph2) (e : edge G) :
  CK4F G -> g_in == g_out :> G -> e \in @edges G g_in g_in ->
  CK4F (point (remove_edges [set e]) g_in g_in).
Admitted.

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

Definition igraph_edges (G : graph) x y := 
  (edge_set (@interval G x y) :\: (edges x x :|: edges y y)).

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
  have {A} [e He] : exists e : edge G, e \notin igraph_edges g_in g_out.
  { admit. }
  - (* g_out not in left petal, e notin interval, g_in not in right petal *)
    rewrite ![f (pgraph _ _)]Efg; 
      try (apply rec_petal => //; apply: CP_extensive; by rewrite !inE eqxx).
    do 2 f_equal. rewrite Efg //. 
    * apply: CK4F_igraph => //=; last rewrite cp_sym; exact: (@mem_cpl G). 
    * exact: measure_subgraph He. 
  - case: pickP => [z Hz|//]; repeat congr tmS.
    + rewrite Efg //. exact: CK4F_split_cpL. exact: measure_split_cpL.
    + rewrite Efg //; apply rec_petal => //. admit. (* align assumptions *) admit.
    + rewrite Efg //. exact: CK4F_split_cpR. exact: measure_split_cpR.
Admitted.

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

Lemma term_of_eq (G : graph2) : 
  CK4F G -> term_of G = term_of_rec term_of G.
Proof.
  apply: Fix_eq => // {G} f g G CK4F_G Efg. rewrite /term_of_rec. 
  case: (boolP (@g_in G == g_out)) => Hio.
  - case: pickP => [e e_loop|].
    + congr tmS. rewrite Efg //.
        * exact: CK4F_remove_loop.
        * apply: measure_remove_edges. by rewrite -cards_eq0 cards1.
    + move=> /(_ _)/negbT no_loops.
      apply: eq_big => // C HC. rewrite Efg //.
      * exact: CK4F_redirect.
      * exact: measure_redirect.
  - case: (boolP (lens G)) => [deg_G|ndeg_G].
    + case: (boolP (_ == _)) => Es.
      * congr big_tmI. apply eq_in_map => C. 
      rewrite mem_enum => HC. apply: Efg.
        -- exact: CK4F_lens.
        -- exact: measure_lens. 
      * case: (boolP (_ == _)) => Ps //. 
        rewrite Efg //. 
        -- exact: CK4F_remove_edges. 
        -- exact: measure_remove_edges.
    + exact: simple_check_point_wf.
Qed.

(** * Isomorphim Properties *)


Lemma setU22 (T:finType) (x y :T) : y \in [set x;y].
Proof. by rewrite !inE eqxx. Qed.


Section SplitPetals.
  Variable (G : graph2).
  Hypothesis G_io : g_in == g_out :> G.
  Let E := @edges G g_in g_out.
  Let P := @components G [set~ g_in].
  
  Definition G_edge' (e : edge G) := par2 one2 (sym2 (label e)).
  Definition G_edges' := big_seq2 [seq G_edge' e | e in E].
  Definition G_rest' := big_seq2 [seq component C | C in P].

  (* can we prove this without associativity? *)
  Lemma split_i : G ≈ seq2 G_rest' G_edges'.
  Admitted.

End SplitPetals.

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
  @edges G g_in g_in = set0 -> C \in @components G [set~ g_in] ->
  component C ≈ dom2 (redirect C).
Proof.
  move => G_conn Eio no_iloops HC.
  rewrite /redirect. case: pickP => [x /andP [inC adj_x] |].
  - apply: subgraph_for_iso => //.
    + by rewrite (eqP Eio) setUA setUid [x |: C](setUidPr _) // sub1set. 
    + by rewrite -(eqP Eio) setUA setUid [x |: C](setUidPr _) ?sub1set // no_iloops setD0.
    + by rewrite /= (eqP Eio).
  - case: (comp_exit G_conn Eio HC) => z Z1 Z2.
    rewrite sg_sym -adjacentE in Z2. case/andP : Z2 => [A B].
    move/(_ z). by rewrite Z1 B. 
Qed.

Lemma split_cp (G : graph2) (z : skeleton G) : 
  z \in @cp G g_in g_out :\: IO ->  g_in != g_out :> G -> 
  edge_set (@petal G IO g_in) == set0 -> 
  edge_set (@petal G IO g_out) == set0 ->
  G ≈ seq2 (@igraph G g_in z) (seq2 (@pgraph G IO z) (@igraph G z g_out)).
Admitted.

Lemma split_par_components (G : graph2): 
  CK4F G -> g_in != g_out :> G -> lens G -> @edge_set G IO == set0 -> 
  G ≈ big_par2 [seq component C | C in @components G (~: IO)].
Admitted.

Definition sym2_ (G : graph2) (e : edge G) :=
  if e \in edges g_in g_out then sym2 (label e) else cnv2 (sym2 (label e)).

Lemma split_par_top (G : graph2) : 
  g_in != g_out :> G -> @components G (~: IO) == set0 -> @edge_set G IO == set0 ->
  G ≈ top2.
Admitted.

Lemma split_par_edges_rest (G : graph2) :
  g_in != g_out :> G -> 
  let G' := point (remove_edges (@edge_set G IO)) g_in g_out in 
  G ≈ \big[par2/G']_(e in @edge_set G IO) sym2_ e .
Proof.
Admitted.

Lemma remove0 (G : graph2) : 
  point (@remove_edges G set0) g_in g_out ≈ G.
Admitted.

Lemma split_par_edges (G : graph2) :
  g_in != g_out :> G -> 
  @components G (~: IO) == set0 -> 
  G ≈ big_par2 [seq sym2_ e | e in @edge_set G IO].
Proof.
  move => Eio com0. rewrite {1}[G]split_par_edges_rest //. 
  rewrite /big_par2. 
  (* TODO: proper inductive proof *)
  case: (set_0Vmem (@edge_set G IO)) => [H|].
  - rewrite H. 
    rewrite big_pred0; last by move => x; rewrite ?inE.
    rewrite /image_mem enum_set0 big_nil.
    rewrite remove0. apply: split_par_top => //. exact/eqP.
  - admit.
Admitted.

Lemma graph_of_bigI_nested (T : finType) (r : seq T) F u : 
  (graph_of_term (\big[tmI/u]_(e <- r) F e)) = 
  \big[par2/graph_of_term u]_(e <- r) graph_of_term (F e).
Proof. 
  elim: r => [|a r IH]; first by rewrite !big_nil.
  by rewrite !big_cons /= IH.
Qed.

Lemma graph_of_bigIs_nested (T : finType) (r : {set T}) F u : 
  (graph_of_term (\big[tmI/u]_(e in r) F e)) = 
  \big[par2/graph_of_term u]_(e in r) graph_of_term (F e).
Admitted.

Lemma big_par2_iso_cps (G G' : graph2) (T : finType) (A : {set T}) F F' : 
  G ≈ G' -> (forall e, e \in A -> F e ≈ F' e) -> 
  \big[par2/G]_(e in A) F e ≈ \big[par2/G']_(e in A) F' e.
Admitted.

Lemma split_pip (G : graph2) : 
  CK4F G -> g_in != g_out :> G -> (* needed ? *)
  G ≈ seq2 (@pgraph G IO g_in) (seq2 (@igraph G g_in g_out) (@pgraph G IO g_out)).
Proof.
  move => CK4F_G Eio.
Admitted.
  
Theorem term_of_iso (G : graph2) : 
  CK4F G -> iso2 G (graph_of_term (term_of G)).
Proof.
  elim: (wf_leq term_of_measure G) => {G} G _ IH CK4F_G.
  rewrite term_of_eq // /term_of_rec. 
  case: ifP => [C1|/negbT C1].
  - (* selfloops / io-redirect *)
    case: pickP => [e e_loop|no_loops]; admit.
    (* Old proof was: *)
    (* rewrite {1}[G]split_i //=. apply: seq2_congr. *)
    (* + rewrite /G_rest' -big_seq2_maps. apply: big_seq2_congrs. *)
    (*   have G_conn : connected [set: skeleton G] by case: CK4F_G. *)
    (*   move => C HC. rewrite /= -IH ?comp_dom2_redirect //. *)
    (*   * exact: measure_redirect. *)
    (*   * exact: CK4F_redirect. *)
    (* + rewrite /G_edges' -big_seq2_maps -(eqP C1).  *)
    (*   apply: big_seq2_congrs => e He. done. *)
  - case: ifP => [C2|/negbT C2].
    + (* parallel split *)
      have EC: @sinterval G g_in g_out = ~: IO. { admit. }
      case: (boolP (_ == set0)) => C3.
      * rewrite -big_par2_map; last first.
        { admit. }
        rewrite -map_comp {1}[G]split_par_components // EC. 
        apply: big_par2_congr => C HC. rewrite mem_enum in HC.
        rewrite -IH //; rewrite -EC in HC. exact: measure_lens. exact: CK4F_lens.
      * rewrite EC.
        case: (boolP (_ == set0)) => C4 /=.
        -- rewrite {1}[G]split_par_edges // -big_par2_map.
           ++ rewrite /tmEs -map_comp. apply: big_par2_congr.
              move => e _. rewrite /tm_ /sym2_. by case: ifP.
           ++ apply: contraNN C3. rewrite /tmEs /nilp size_map. admit.
        -- rewrite {1}[G]split_par_edges_rest //.
           rewrite graph_of_bigIs_nested /=. 
           apply: big_par2_iso_cps.
           ++ rewrite -IH //. 
              exact: measure_remove_edges.
              rewrite -EC in C4. exact: CK4F_remove_edges. 
           ++ move => e. rewrite /tm_ /sym2_. by case: ifP.
    + (* petal/sequential split *) 
      rewrite /simple_check_point_term. 
      case: ifP => [A|/negbT A].
      * rewrite /=. (* TODO: clean this up *)
        rewrite -IH; first last. 
          apply rec_petal => //; apply: CP_extensive; by rewrite !inE eqxx.
          apply rec_petal => //; apply: CP_extensive; by rewrite !inE eqxx.
        rewrite -IH; first last.
          apply: CK4F_igraph => //. admit. admit.
          admit.
        rewrite -IH; first last. 
          apply rec_petal => //; apply: CP_extensive; by rewrite !inE eqxx.
          apply rec_petal => //; apply: CP_extensive; by rewrite !inE eqxx.
          exact: split_pip.
      * move: A. rewrite negb_or !negbK. case/andP => A B.
        rewrite /lens !negb_and A B (negbTE C1) /= in C2.
        case: pickP => [z Hz|C]; last first.
        { case:notF. apply: contraNT C2 => _. rewrite -setD_eq0. 
          apply/eqP. apply/setP => x. by rewrite C inE. }
        rewrite /=. 
        rewrite {1}[G](split_cp Hz) //. repeat apply: seq2_congr. 
        -- rewrite -IH //. exact: measure_split_cpL. exact: CK4F_split_cpL.
        -- suff ? : z \in @CP G IO. { rewrite -IH //; by apply rec_petal. }
           case/setDP : Hz => Hz _. apply/bigcupP; exists (g_in,g_out) => //. 
           by rewrite !inE !eqxx.
        -- rewrite -IH //. exact: measure_split_cpR. exact: CK4F_split_cpR.
Admitted.

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
