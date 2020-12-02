Require Import RelationClasses Morphisms Setoid Omega.

From mathcomp Require Import all_ssreflect.

Require Import edone finite_quotient preliminaries.
Require Import digraph sgraph minor checkpoint cp_minor. 
Require Import setoid_bigop structures pttdom ptt mgraph mgraph2 skeleton bounded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

Arguments edge_set [Lv Le] G _,[Lv Le G] _.

Section ExtractionDef.
Variable sym : Type.
Notation graph := (graph unit (flat sym)).
Notation graph2 := (graph2 unit (flat sym)).

(* TODO: resolve this name clash *)
Local Notation link_rel := checkpoint.link_rel.

(* same as in mgraph2_tw2.v, but different from [reduction.graph_of_term] 
   (the latter start from a 2pdom term rather than a 2p term) *)
Definition graph_of_term: term sym -> graph2 := eval (fun a : flat sym => @g2_var _ _ a).

(** * Term Extraction Function *)

(** ** Termination Metric *)

Definition term_of_measure (G : graph2) :=
  (input == output :> G) + 2*#|edge G|.

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
  do 2 case: (input == output) => /=; somega.
Qed.

Lemma measure_io (G' G : graph2) : 
  (input == output :> G) -> (input != output :> G') -> #|edge G'| <= #|edge G| -> 
  measure G' < measure G.
Proof. 
  rewrite /term_of_measure. 
  do 2 case: (input == output) => //=; somega.
Qed.

Lemma measure_subgraph (G : graph2) V E (con : @consistent _ _ G V E) x y e : 
  e \notin E -> measure (@point (subgraph_for con) x y) < measure G.
Proof. 
  move => He. apply: measure_card. rewrite card_sig. 
  apply: proper_card. apply/properP. split; by [exact/subsetP| exists e].
Qed.

Lemma measure_node (G : graph2) V E (con : @consistent _ _ G V E) v x y : 
  connected [set: skeleton G] -> 
  v \notin V -> measure (@point (subgraph_for con) x y) < measure G.
Proof.
  move => /connectedTE conn_G Hv. 
  case/connect_irredP : (conn_G v (val x)) => p _. 
  have vx: v != val x. { apply: contraNN Hv => /eqP->. exact: valP. }
  case: (splitL p vx) => u [vu] _ {p vx}. move: vu.
  rewrite /=/sk_rel. case/andP=> _ /existsP[e He].
  refine (@measure_subgraph _ _ _ _ _ _ e _).
  apply: contraNN Hv. move/con =>H.
  move: He. by rewrite !inE => /orP[/andP[/eqP<- _]|/andP[_ /eqP<-]].
Qed.

(** ** Subroutines *)

Definition lens (G : graph2) := 
  [&& edge_set G (@bag G IO input)  == set0 ,
      edge_set G (@bag G IO output) == set0 &
      @link_rel (skeleton G) input output].

Lemma get_edge (G : graph) (U : {set G}) (x y : skeleton G) : 
  x \in U -> y \in U -> x -- y -> exists e : edge G, e \in edge_set U.
Proof.
  move => Hx Hy. rewrite /=/sk_rel => /andP[_].
  case/existsP=> e He. exists e. move: He.
  by rewrite !inE => /orP[]/andP[/eqP-> /eqP->]; rewrite Hx Hy.
Qed.

Lemma edgeless_bag (G : graph) (U : {set G}) (x : skeleton G) : 
  connected [set: skeleton G] -> x \in @CP G U ->
  edge_set (@bag G U x)  == set0 -> @bag G U x == [set x].
Proof.
  move => con_G cp_x.
  apply: contraTT => /bag_nontrivial [y Y1 Y2]. rewrite eq_sym in Y2.
  have con_Px := connected_bag con_G cp_x.
  have [||z Pz xz] := connected_card_gt1 con_Px _ _ Y2.
    exact: bag_id. done. 
  apply/set0Pn. apply: get_edge xz => //. exact: bag_id.
Qed.

Lemma lens_io_set (G : graph2) : 
  lens G -> @edge_set _ _ G IO = edges input output :|: edges output input.
Proof.
  move => /and3P [A B _]. apply/setP => e. apply/idP/idP.
  - rewrite !inE. 
    (repeat let H := fresh in case: (boolP (_ == _)) => H) => //= _.
    + apply: contraTT A => _. apply/set0Pn; exists e. 
      by rewrite inE (eqP H) (eqP H1) (@bag_id G). 
    + apply: contraTT B => _. apply/set0Pn; exists e. 
      by rewrite inE (eqP H0) (eqP H2) (@bag_id G). 
  - by case/setUP ; apply: edge_in_set; rewrite !inE eqxx.
Qed.

Lemma lens_sinterval (G : graph2) :
  connected [set: skeleton G] -> lens G ->
  (@sinterval G input output = ~: IO).
Proof.
  move=> G_conn /and3P[] /edgeless_bag/eqP-/(_ G_conn (CP_extensive _)).
  rewrite !inE -setTD eqxx =>/(_ isT) bag_i.
  move=> /edgeless_bag/eqP-/(_ G_conn (CP_extensive _)).
  rewrite !inE eqxx orbT =>/(_ isT) bag_o /andP[iNo _].
  rewrite (sinterval_bag_cover G_conn iNo) bag_i bag_o setUAC.
  rewrite setDUl setDv set0U setDE. apply: esym; apply/setIidPl.
  apply/subsetP=> x x_sI. rewrite !inE negb_or.
  apply/andP; split; apply: contraTneq x_sI =>->; by rewrite sinterval_bounds.
Qed.

Arguments cp : clear implicits.
Arguments Path : clear implicits.



Definition CK4F (G : graph2) := connected [set: skeleton G] /\ K4_free (sskeleton G).

(** If G is a lens with non non-adjacent input and output, then it has
at least two parallel components *)
Lemma split_K4_nontrivial (G : graph2) : 
  input != output :> G -> 
  lens G -> 
  ~~ @adjacent _ _ G input output -> 
  CK4F G ->
  1 < #|components (@sinterval (skeleton G) input output)|.
Proof.
  move => A B C [D E]. 
  apply/equivalence_partition_gt1P.
  - move => x y z _ _ _. exact: (sedge_in_equiv (G := skeleton G)).
  - set H := sinterval _ _. apply: ssplit_K4_nontrivial (E) (D).
    + by rewrite /edge_rel/=/sk_rel A.
    + by case/and3P : B.
Qed.


Fact redirect_proof1 (T : finType) x (A : {set T}) : x \in x |: A. 
Proof. by rewrite !inE eqxx. Qed.
Arguments redirect_proof1 {T x A}.

(** subgraph induced by [i |: H] without i-selfloops and with output set
to [o] *)
Lemma redirect_consistent (G : graph2) (H : {set G}) (o : G) : 
  let H' := input |: (o |: H) in 
  consistent H' (edge_set H' :\: edges input input).
Proof. apply: consistent_setD. exact: induced_proof. Qed.

Fact redirect_output_proof (T : finType) x y (B : {set T}) : x \in y |: (x |: B). 
Proof. by rewrite !inE eqxx. Qed.
Arguments redirect_output_proof {T x y B}.

Definition redirect_to (G : graph2) (H : {set G}) (o:G) := 
  @point (induced (input |: (o |: H))) 
         (Sub input (setU11 _ _))
         (Sub o redirect_output_proof).

(** subgraph induced by [i |: H] without i-selfloops and with [o] set
to some neighbor of [i] in H *)
Definition redirect (G : graph2) (H : {set G}) : graph2 :=
  if [pick z in H | adjacent input z] isn't Some z then 1 (* unit_graph2 tt *)
  else redirect_to H z.


Definition component (G : graph2) (H : {set G}) : graph2 := 
  @point (induced (input |: (output |: H)))
         (Sub input (setU11 _ _))
         (Sub output (setU1r _ (setU11 _ _))).

Definition induced2 (G : graph2) (V :{set G}) := 
  match @idP (input \in V), @idP (output \in V) with 
  | ReflectT p, ReflectT q => point (induced V) (Sub input p) (Sub output q)
  | _,_ => G
  end.

Lemma induced2_induced (G : graph2) (V :{set G}) (iV : input \in V) (oV :output \in V) : 
  induced2 V = point (induced V) (Sub input iV) (Sub output oV).
Proof.
  rewrite /induced2. 
  case: {-}_ / idP; last by rewrite iV.
  case: {-}_ / idP; last by rewrite oV.
  move => p q. by rewrite (bool_irrelevance p oV) (bool_irrelevance q iV).
Qed.


Open Scope ptt_ops.

(** Possibly empty sequence of (trivial) terms corresponding to direct
i-o edges. Yields nonempty parallel composition when concatenated with
the terms for the i-o components *)
Definition tm_ (G : graph2) (e : edge G): term sym := 
  if e \in edges input output then tm_var (elabel e) else (tm_var (elabel e))°.

Definition tmEs (G : graph2) : seq (term sym) := [seq tm_ e | e in edge_set G IO].

(** ** The Extraction Functional *)

(** Here we define the extraction function. The case distinctions are chosen
such that we can make use of induced subgraphs (rather than the more generic
[subgraph_for] construction) as much as possible. *)

Definition simple_check_point_term (g : graph2 -> term sym) (G : graph2) : term sym := 
  let (i,o) := (input : G, output : G) in 
  if  (edge_set (@bag G IO i) != set0) || (edge_set (@bag G IO o) != set0)
  then g (bgraph IO i) · g (igraph i o) · g (bgraph IO o)
  else if [pick z in @cp G i o :\: IO] isn't Some z then 1 (* never happens *)
       else g (igraph i z) · g(bgraph IO z) · g(igraph z o).

(** NOTE: we assume the input graph to be connected and K4-free *)
Definition term_of_rec (term_of : graph2 -> term sym) (G : graph2) := 
  if input == output :> G
  then (* input equals output *)
    let E := edge_set G IO in
    if [pick e in E] isn't Some e then
      if [pick C in @components G [set~ input]] is Some C then
        dom (term_of (redirect C)) ∥ term_of (induced2 (~: C))
      else 1
    else tm_ e ∥ term_of (point (remove_edges [set e]) input output)
  else (* distinct input and output *)
    if lens G
    then (* no checkpoints and no bags on i and o *)
      let P := components (@sinterval (skeleton G) input output) in
      let E := edge_set G IO in
      if [pick e in E] isn't Some e 
      then 
        if [pick C in P] isn't Some C then 1 (* never happens *)
        else term_of (component C) ∥ term_of (induced2 (~: C))
      else if (P == set0) && (E :\ e == set0)
           then  tm_ e
           else  tm_ e ∥ term_of (point (remove_edges [set e]) input output)
    else (* at least one nontrivial bag or checkpoint *)
      @simple_check_point_term term_of G.

Definition term_of := Fix top term_of_measure term_of_rec.

(** ** Termination Argument *)


Notation sigraph := cp_minor.igraph.
Lemma sskeleton_add (G : graph) (x y : G) : 
  sgraph.subgraph (sskeleton (igraph x y))
                  (sgraph.add_edge (sigraph G x y) istart iend).
Proof.
  exists id => // u v uv _; move: u v uv. apply sskelP.
  - move=> u v. by rewrite sg_sym.
  - move=> e sNt. rewrite /edge_rel /= -!val_eqE /=. apply/orP; left.
    by rewrite /edge_rel/=/sk_rel/edge_rel/=/sk_rel sNt adjacent_edge.
  - by rewrite /edge_rel/= -!val_eqE /= !eqxx => ->.
Qed.

Lemma CK4F_igraph (G : graph2) (x y : G) : 
  x \in cp G input output -> y \in cp G input output ->
  CK4F G -> x != y -> CK4F (igraph x y).
Proof.
  move => Hx Hy [conn_G K4F_G] xy. 
  split; first exact: connected_igraph.
  apply: subgraph_K4_free (sskeleton_add _ _) _.
  exact: igraph_K4F K4F_G.
Qed.

Lemma measure_igraph (G : graph2) :
    connected [set: skeleton G] ->
    (edge_set (@bag G IO input) != set0) || (edge_set (@bag G IO output) != set0) ->
    measure (@igraph _ _ G input output) < measure G.
Proof.
  move=> G_conn A.
  suff [e] : exists e, e \notin @interval_edges _ _ G input output
    by exact: measure_subgraph.
  have [i_cp o_cp] : input \in @CP G IO /\ output \in @CP G IO
    by split; apply: CP_extensive; rewrite !inE eqxx.
  case/orP: A => /set0Pn[e He]; exists e; last rewrite interval_edges_sym.
  all: by rewrite (disjointFr (interval_bag_edges_disj G_conn _ _) He).
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
  - move/pathp_nil/val_inj ->. exact: connect0.
  - rewrite pathp_cons /= -!andbA => /and5P [A B C D E].
    apply: (connect_trans (y := Sub a B)); last exact: IH.
    apply: connect1. move: C. rewrite /sk_rel -val_eqE.
    by rewrite adjacent_induced.
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
  move=> x y xy _. move: xy. rewrite /edge_rel/= -!(inj_eq val_inj) /=.
  case/or3P=> [xy|->|->] //. apply/orP. left.
  pattern x, y. revert x y xy.
  apply skelP; first by move=> x y xy; rewrite sgP.
  move=> e. rewrite /edge_rel/=/sk_rel -!(inj_eq val_inj)/= => -> /=.
  exact: adjacent_edge.
Qed.


Lemma rec_bag (G : graph2) (x : G) : 
  CK4F G -> x \in @CP (skeleton G) IO -> input != output :> G ->
  CK4F (bgraph IO x) /\ measure (bgraph IO x) < measure G.
Proof.
  move => [conn_G K4F_G] cp_x Dio. split. 
  - apply: CK4F_sub => //. exact: connected_bag.
  - suff: (input \notin @bag G IO x) || (output \notin @bag G IO x).
    { by case/orP; exact: measure_node. }
    rewrite -negb_and. apply:contraNN Dio => /andP[].
    rewrite !(bag_cp conn_G) // => [/eqP-> /eqP-> //||]; 
      by apply CP_extensive; rewrite !inE eqxx.
Qed.  

                           

Lemma CK4F_remove_component (G : graph2) (C : {set G}) :
  C \in @components G [set~ input] -> CK4F G -> CK4F (induced2 (~: C)).
Proof.
  move=> C_comp G_CK4F. apply: CK4F_induced2 (G_CK4F). case: G_CK4F => G_conn _.
  have Hi : (@input _ _ G)\notin[set~ input] by rewrite !inE negbK.
  apply: (@remove_component G) Hi C_comp G_conn _. rewrite setCK. exact: connected1.
Qed.

Lemma measure_remove_component (G : graph2) (C : {set G}) :
  CK4F G -> C \in @components G (~: IO) -> measure (induced2 (~: C)) < measure G.
Proof.
  move=> [G_conn _] C_comp.
  case/and3P: (@partition_components G (~: IO)) => /eqP compU _ compN0.
  have /set0Pn[x x_C] : C != set0 by apply: contraTneq C_comp =>->.
  have {x_C} : x \notin ~: C by rewrite inE negbK.
  have : (input  : G) \notin ~: IO by rewrite !inE negbK eqxx.
  have : (output : G) \notin ~: IO by rewrite !inE negbK eqxx.
  rewrite -compU.
  move/bigcupP/(_ (ex_intro2 _ _ C C_comp _))=> /negP oNC.
  move/bigcupP/(_ (ex_intro2 _ _ C C_comp _))=> /negP iNC.
  have {iNC oNC} [iNC oNC] : input \in ~: C /\ output \in ~: C by rewrite !inE.
  rewrite induced2_induced. exact: measure_node.
Qed.

Lemma CK4F_one : CK4F 1.
Proof. 
  split. move => [] [] _ _. exact: connect0.
  apply small_K_free. by rewrite card_unit.
Qed.

Lemma CK4F_redirect (G : graph2) C : 
  CK4F G -> input == output :> G -> C \in @components G [set~ input] ->
  CK4F (redirect C).
Proof.
  move => CK4F_G Eio HC.
  have D := @partition_components G [set~ input].
  have Csub: C \subset [set~ input].
  { rewrite -(cover_partition D). apply/subsetP => z Hz. 
    exact: mem_cover HC _. }
  rewrite /redirect. 
  case: pickP => [z /andP [Z1 Z2]|_]; last exact: CK4F_one.
  have conn_iC : @connected G (input |: C).
  { apply: (@connectedU_edge G _ _ input z) => //.
    - by rewrite set11.
    - rewrite /edge_rel/=/sk_rel Z2 andbT.
      move/(subsetP Csub) in Z1. by rewrite !inE eq_sym in Z1. 
    - apply: connected1.
    - apply: connected_in_components HC.  }
  split.
  - apply: connected_induced. by rewrite [z |: C]setU1_mem.
  - have: K4_free (induced (input |: C)). 
    { apply: induced_K4_free. by apply CK4F_G. }
    apply: iso_K4_free.
    setoid_rewrite <-sskeleton_adjacent. 
    by rewrite (setU1_mem Z1). 
    by rewrite adjacent_induced.
Qed.

Lemma measure_redirect (G : graph2) C : 
  CK4F G -> input == output :> G -> C \in @components G [set~ input] ->
  measure (redirect C) < measure G.
Proof.
  move => CK4F_G Eio HC.
  have D := @partition_components G [set~ input].
  have Csub: C \subset [set~ input].
  { rewrite -(cover_partition D). apply/subsetP => z Hz. 
    exact: mem_cover HC _. }
  rewrite /redirect. case: pickP => [x /andP [Hx1 Hx2]|]. 
  - apply: measure_io => //=. 
    + rewrite -val_eqE /=. apply: contraTN Hx1 => /eqP<-. 
      apply: contraTN Csub => A. apply/subsetPn. exists input => //. by rewrite setC11. 
    + rewrite card_sig. exact: max_card. 
  - move => _. apply: measure_card => /=. rewrite card_void.
    have/set0Pn [x Hx] : C != set0. 
    { case/and3P : D => _ _. by apply: contraNN => /eqP <-. }
    have: x != input. move/(subsetP Csub) in Hx. by rewrite !inE in Hx.    
    apply: has_edge. by apply CK4F_G.
Qed.

Lemma connected_component_set (G : graph2) C : 
  CK4F G -> lens G -> C \in components (@sinterval (skeleton G) input output) ->
  @connected G (input |: (output |: C)).
Proof.
  set sI := sinterval _ _. move=> [G_conn G_K4F] G_lens C_comp.
  case: (sinterval_components C_comp) => -[u] u_C iu [v] v_C ov.
  apply: connectedU_edge iu _ _; rewrite 3?inE ?eqxx ?u_C //;
  first exact: connected1.
  apply: connectedU_edge ov _ _; rewrite 1?inE ?eqxx ?v_C //;
  first exact: connected1.
  exact: connected_in_components C_comp.
Qed.

Lemma CK4F_lens (G : graph2) C : 
  CK4F G -> lens G -> C \in components (@sinterval (skeleton G) input output) -> 
  CK4F (component C).
Proof.
  set sI := sinterval _ _. move=> [G_conn G_K4F] G_lens C_comp.
  split; last by apply: subgraph_K4_free G_K4F; exact: sskeleton_subgraph_for.
  apply: connected_induced. exact: connected_component_set.
Qed.

Lemma lens_components (G : graph2) C :
  CK4F G -> lens G -> edge_set G IO == set0 ->
  C \in components (@sinterval G input output) ->
  exists2 D, D \in components (@sinterval G input output) & D != C.
Proof.
  set sI := sinterval _ _. case/and3P: (partition_components sI).
  set P := components _.
  move=> /eqP compU compI comp0 [G_conn G_K4F] G_lens Eio0 C_comp.
  have iNo : input != output :> G
    by case/and3P: G_lens => _ _ /(@sg_edgeNeq (link_graph G))->.
  have Nio : ~~ @adjacent _ _ G input output.
  { apply: contraTN Eio0 => io. apply/set0Pn.
    case/existsP: io => e. rewrite inE => He. exists e.
    by case/orP: He; apply: edge_in_set; rewrite in_set2 eqxx. }
  have : 1 < #|P| by exact: split_K4_nontrivial.
  rewrite (cardD1 C) C_comp add1n ltnS => /card_gt0P[/= D].
  rewrite !inE => /andP[DNC] D_comp. by exists D.
Qed.

Lemma measure_lens (G : graph2) C :
  CK4F G -> lens G -> edge_set G IO == set0 ->
  C \in components (@sinterval (skeleton G) input output) ->
  measure (component C) < measure G.
Proof.
  set sI := sinterval _ _. case/and3P: (partition_components sI).
  set P := components _.
  move=> /eqP compU compI comp0 G_CK4F G_lens Eio0 C_comp.
  case: (lens_components G_CK4F G_lens Eio0 C_comp) => [D] D_comp DNC.
  have /set0Pn[x x_D] : D != set0 by apply: contraTneq D_comp =>->.
  move/trivIsetP: compI => /(_ D C D_comp C_comp DNC)/disjointFr/(_ x_D) xNC.
  have G_conn : connected [set: skeleton G] by case: G_CK4F.
  suff : x \notin input |: (output |: C) by exact: measure_node.
  have : x \in sI by rewrite -compU; apply/bigcupP; exists D.
  rewrite ![in ~~ _]inE xNC orbF.
  apply: contraTN =>/orP[]/eqP->; by rewrite (@sinterval_bounds G).
Qed.


Section SplitCP.
Variables (G : graph2).
Hypothesis CK4F_G : CK4F G.
Hypothesis Hio : input != output :> G.
Variable (z : G).
Hypothesis Hz : z \in cp G input output :\: IO.

Let Hz' : z \in cp G input output.
Proof. by case/setDP: (Hz). Qed.       

Let Zi : z != input. 
Proof. move: Hz. rewrite !inE negb_or -andbA. by case/and3P. Qed.

Let Zo : z != output. 
Proof. move: Hz. rewrite !inE negb_or -andbA. by case/and3P. Qed.

(* output not in left side, input not in right side *)
(* neither input nor output is in the central bag *)

Lemma CK4F_split_cpL : CK4F (igraph input z).
Proof.
  apply: CK4F_igraph => //; first exact: (@mem_cpl G). by rewrite eq_sym.
Qed.

Lemma CK4F_split_cpR : CK4F (igraph z output).
Proof.
  apply: CK4F_igraph => //. rewrite cp_sym. exact: mem_cpl. 
Qed.

Lemma CK4F_split_cpM : CK4F (@bgraph _ _ G IO z).
Proof. 
  apply rec_bag => //. 
  apply/bigcupP. exists (input,output) => //. by rewrite !inE /= !eqxx.
Qed.

Lemma measure_split_cpL : measure (igraph input z) < measure G.
Proof.
  apply: (measure_node (v := output)); first apply CK4F_G.
  have Ho: output \in @interval G z output. exact: intervalR.
  apply: contraNN Zo => C. 
  by rewrite eq_sym -in_set1 -(intervalI_cp Hz') inE C. 
Qed.

Lemma measure_split_cpR : measure (igraph z output) < measure G.
Proof.
  apply: (measure_node (v := input)); first apply CK4F_G.
  have Hi := @intervalL G input z.
  apply: contraNN Zi => C. 
  by rewrite eq_sym -in_set1 -(intervalI_cp Hz') inE C.
Qed.

Lemma measure_split_cpM : measure (@bgraph _ _ G IO z) < measure G.
Proof.
  apply: (measure_node (v := input)); first apply CK4F_G.
  rewrite (@bag_cp G) 1?eq_sym //; first apply CK4F_G.
  - apply: CP_extensive. by rewrite !inE eqxx.
  - apply/bigcupP. exists (input,output) => //. by rewrite !inE /= !eqxx.
Qed.

End SplitCP.

Definition simple_check_point_wf (f g : graph2 -> term sym) (G : graph2) : 
  CK4F G -> 
  input != output :> G ->
  ~~ lens G -> 
  (forall H : graph2, CK4F H -> measure H < measure G -> f H = g H) -> 
  simple_check_point_term f G = simple_check_point_term g G.
Proof.
  move => CK4F_G Eio nlens_G Efg.
  rewrite /simple_check_point_term.
  case: ifP => [A|A].
  - (* output not in left bag, e notin interval, input not in right bag *)
    rewrite ![f (bgraph _ _)]Efg; 
      try (apply rec_bag => //; apply: CP_extensive; by rewrite !inE eqxx).
    do 2 f_equal. rewrite Efg //. 
    * apply: CK4F_igraph => //=; last rewrite cp_sym; exact: (@mem_cpl G). 
    * apply: measure_igraph => //; by case: CK4F_G.
  - case: pickP => [z Hz|//]; repeat congr tm_dot.
    + rewrite Efg //. exact: CK4F_split_cpL. exact: measure_split_cpL.
    + have {Hz} Hz : z \in @CP G IO by move: Hz; rewrite inE CP_set2 => /andP[_ ->].
      by rewrite Efg //; apply rec_bag => //.
    + rewrite Efg //. exact: CK4F_split_cpR. exact: measure_split_cpR.
Qed.

Lemma CK4F_remove_edges (G : graph2) (E : {set edge G}) :
  CK4F G -> input != output :> G -> lens G ->
  components (@sinterval G input output) != set0 \/ edge_set IO :\: E != set0 ->
  E \subset edge_set IO ->
  CK4F (point (remove_edges E) input output).
Proof.
  move => CK4F_G Hio lens_G Ps E_sub_IO. 
  split; last by case: CK4F_G => _; apply: iso_K4_free; exact: sskeleton_remove_io. 
  case: CK4F_G => G_conn _. apply: remove_edges_connected G_conn.
  suff io_conn : connect (@sk_rel _ _ (remove_edges E)) input output.
  { move=> e /(subsetP E_sub_IO). rewrite !inE. case/andP=> /orP[]/eqP-> /orP[]/eqP-> //.
    rewrite connect_symI //. exact: sk_rel_sym. }
  move: Ps. set sI := sinterval _ _. case. 
  - case/set0Pn=> /= C C_comp.
    case/and3P: (partition_components sI) => /eqP compU compI comp0.
    have C_sub : C \subset sI by rewrite -compU; exact: bigcup_sup.
    case: (@sinterval_components G C _ _ C_comp) => -[u u_C iu][v v_C ov].
    have [uNio vNio] : u \notin IO /\ v \notin IO.
    { have [u_sI v_sI] := (subsetP C_sub u u_C, subsetP C_sub v v_C).
      rewrite !in_set2. split; [move: u_sI | move: v_sI];
      apply: contraTN => /orP[]/eqP->; by rewrite (@sinterval_bounds G). }
    have /connect1 iu_conn := remove_edges_cross (E_sub_IO) iu uNio.
    apply: connect_trans iu_conn _.
    have := remove_edges_cross (E_sub_IO) ov vNio. rewrite sk_rel_sym.
    move/connect1. apply: connect_trans.
    apply: remove_edges_restrict (E_sub_IO) _.
    have := @connected_in_components G sI C C_comp u v u_C v_C.
    apply: connect_mono. apply: restrict_mono => z /= Hz.
    have {Hz} Hz : z \in sI by rewrite -compU; apply/bigcupP; exists C.
    rewrite !inE negb_or. apply/andP.
    by split; apply: contraTneq Hz => ->; rewrite /sI (@sinterval_bounds G).
  - case/set0Pn => e /setDP [E1 E2]. apply: connect1.
    rewrite /sk_rel/= Hio /=. rewrite lens_io_set // in E1. case/setUP : E1 => E1.
    + apply: adjacentI. instantiate (1 := Sub e E2). by rewrite !inE /= in E1 *.
    + rewrite adjacent_sym. apply: adjacentI. instantiate (1 := Sub e E2). by rewrite !inE /= in E1 *.
Qed.

Lemma measure_remove_edges (G : graph2) (E : {set edge G}) (i o : G) :
  E != set0 -> measure (point (remove_edges E) i o) < measure G.
Proof.
  case/set0Pn => e inIO. apply: measure_card => /=. rewrite card_sig.
  apply: (card_ltnT (x := e)). by rewrite /= negbK.
Qed.

Lemma CK4F_remove_loops (G : graph2) (E : {set edge G}) : 
  CK4F G -> input == output :> G -> E \subset edge_set IO ->
  CK4F (point (remove_edges E) input output).
Proof.
  move=> [G_conn G_CK4F] /eqP Eio E_sub_IO. rewrite -Eio.
  have loopP : {in E, forall e, source e = target e}. 
  { move => e /(subsetP E_sub_IO). rewrite !inE. 
    case/andP. by do 2 case/orP=> [/eqP->|/eqP->]. }
 split.
  - apply: iso_connected G_conn. symmetry. exact: remove_loops.
  - apply: iso_K4_free G_CK4F. apply: diso_comp (iso_pointxx _) _.
    case: G {G_conn E_sub_IO} E Eio loopP => G i o E /= <- loopP. symmetry. 
    apply: diso_comp (iso_pointxx _) _. exact: remove_loops.
Qed.

Lemma CK4F_lens_rest (G : graph2) C : 
  CK4F G -> lens G -> edge_set G IO == set0 -> 
  C \in @components G (@sinterval G input output) -> CK4F (induced2 (~: C)).
Proof.
  set sI := sinterval _ _. case/and3P: (partition_components sI).
  set P := components _.
  move=> /eqP compU /trivIsetP compI comp0 G_CK4F G_lens Eio0 C_comp.
  apply: CK4F_induced2 (G_CK4F). have [G_conn _] := G_CK4F.
  have : C \subset cover P := bigcup_sup _ C_comp.
  rewrite compU /sI lens_sinterval // subsetC subUset !sub1set => /andP[Gi Go].
  apply: connected_center (Gi) => x Hx.
  have [D [D_comp DNC x_ioD]] :
    exists D, [/\ D \in P, D != C & x \in input |: (output |: D)].
  { case: (lens_components G_CK4F G_lens Eio0 C_comp) => D D_comp DNC.
    case: (altP (x =P input))  => [->|Di]; last case: (altP (x =P output)) => [->|Do].
    - exists D; split => //. exact: setU11.
    - exists D; split => //. exact: (setU1r _ (setU11 _ _)).
    - have x_cover : x \in cover P
        by rewrite compU /sI lens_sinterval // !inE negb_or Di Do.
      exists (pblock P x). split; first exact: pblock_mem.
      + rewrite inE in Hx. apply: contraNneq Hx => <-. by rewrite mem_pblock.
      + by rewrite !in_setU mem_pblock x_cover. }
  have : connect (restrict (input |: (output |: D)) (@sedge G)) input x.
  { apply: connected_component_set => //. exact: setU11. }
  apply connect_mono. apply: restrict_mono => z /=. rewrite !in_setU1.
  case/or3P=> [/eqP->//|/eqP->//|Hz].
  by rewrite inE (disjointFr (compI D C D_comp C_comp DNC) Hz).
Qed.

Lemma measure_lens_rest (G : graph2) C : 
  CK4F G -> lens G -> C \in @components G (@sinterval G input output) ->
  measure (induced2 (~: C)) < measure G.
Proof.
  move=> G_CK4F G_lens. rewrite lens_sinterval //; last by case: G_CK4F.
  exact: measure_remove_component.
Qed.

Lemma term_of_rec_eq (f g : graph2 -> term sym) (G : graph2) :
  CK4F G -> (forall H : graph2, CK4F H -> measure H < measure G -> f H = g H) ->
  term_of_rec f G = term_of_rec g G.
Proof.
  move=> CK4F_G Efg. rewrite /term_of_rec.
  case: (boolP (@input _ _ G == output)) => Hio.
  - case: pickP => [e Eio|Es]; last first.
    + case: pickP => //= C HC. rewrite !Efg //.
      * exact: CK4F_remove_component.
      * move: HC. rewrite -[set1 input]setUid {2}(eqP Hio).
        exact: measure_remove_component.
      * exact: CK4F_redirect.
      * exact: measure_redirect.
    + congr tm_par. rewrite Efg //.
      * apply CK4F_remove_loops => //. by rewrite sub1set.
      * apply: measure_remove_edges. exact: set10.
  - case: (boolP (lens G)) => [deg_G|ndeg_G].
    + case: picksP => [e Eio|/eqP Es]; last first. 
      * case: pickP => [C HC|//]. congr tm_par.
        -- apply: Efg. exact: CK4F_lens. exact: measure_lens.
        -- apply: Efg. exact: CK4F_lens_rest. exact: measure_lens_rest.
      * case: (boolP (_ && _)) => Ps //. rewrite Efg //. 
        -- apply: CK4F_remove_edges => //.
           ++ rewrite negb_and in Ps. exact/orP.
           ++ by rewrite sub1set.
        -- apply: measure_remove_edges. exact: set10.
    + exact: simple_check_point_wf.
Qed.

Lemma term_of_eq : forall (G : graph2), CK4F G -> term_of G = term_of_rec term_of G.
Proof. apply: Fix_eq term_of_rec_eq. Qed.

End ExtractionDef.
