Require Import RelationClasses Morphisms Setoid Omega.

From mathcomp Require Import all_ssreflect.

Require Import edone finite_quotient preliminaries bij set_tac.
Require Import digraph sgraph minor checkpoint.
Require Import setoid_bigop structures pttdom mgraph mgraph2 skeleton.
Require Import bounded equiv extraction_def.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 


Section ExtractionIso.
Variable sym : Type.
Notation graph := (graph unit (flat sym)).
Notation graph2 := (graph2 unit (flat sym)).

Notation g2_top := (g2_top : graph2).
Notation g2_one := (g2_one : graph2).

(** * Isomorphim Theorem *)

(** In this file we prove correctness of the extraction function. This
mainly amounts to establishing a variety of isomorphisms corresponding
to the way the extraction function decomposes graphs. *)


(* lemmas for recognizing [top] and [one] *)
Lemma iso_top (G : graph2) :
  input != output :> G -> 
  (forall x : G, x \in IO) -> 
  (forall e : edge G, False) -> G ≃2 top.
Proof.
  move => Dio A B. 
  pose f (x : G) : g2_top := 
    if x == input then input else output.
  pose f' (x : g2_top) : G := 
    if x == input then input else output.
  pose g (e : edge G) : edge g2_top := 
    match (B e) with end.
  pose g' (e : edge g2_top) : edge G := 
    match e with inl e |inr e => vfun e end.
  unshelve Iso2 (@Iso _ _ _ _ (@Bij _ _ f f' _ _) (@Bij _ _ g g' _ _) xpred0 _)=>/=.
  - rewrite /f/f'/= => x.
    case: (boolP (x == input)) => [/eqP <-|/=]//. 
    move: (A x). case/setUP => /set1P => -> //. by rewrite eqxx.
  - rewrite /f/f'/= => x.
    case: (boolP (x == inl tt)) => [/eqP <-|/=]//. by rewrite eqxx.
    case: x => // [[]] _. by rewrite eq_sym (negbTE Dio).
  - by [].
  - by case=>[[]|[]]. 
  - by split.
  - by rewrite /f  eqxx. 
  - by rewrite /f eq_sym (negbTE Dio). 
Qed.

Lemma iso_one (G : graph2) :
  input == output :> G -> 
  (forall x : G, x \in IO) -> 
  (forall e : edge G, False) -> G ≃2 1.
Proof.
  move => Dio A B. 
  pose f (x : G) : g2_one := input.
  pose f' (x : g2_one) : G := input.
  pose g (e : edge G) : edge g2_one := 
    match (B e) with end.
  pose g' (e : edge g2_one) : edge G := 
    match e with end.
  unshelve Iso2 (@Iso _ _ _ _ (@Bij _ _ f f' _ _) (@Bij _ _ g g' _ _) xpred0 _)=>/=.
  - rewrite /f/f'/= => x.
    move: (A x). rewrite !inE -(eqP Dio) => /orP. by case => /eqP->.
  - by move => [].
  - by [].
  - by [].
  - by split.
Qed.


Lemma comp_exit (G : graph2) (C : {set G}) : 
  connected [set: skeleton G] ->
  input == output :> G -> C \in @components G [set~ input] ->
  exists2 z : skeleton G, z \in C & z -- input.
Proof.
  move=> G_conn Eio C_comp.
  case/and3P: (@partition_components G [set~ input]) => /eqP compU compI comp0.
  have /card_gt0P[a a_C] : 0 < #|C|.
  { rewrite card_gt0. by apply: contraTneq C_comp =>->. }
  have aNi : a \in [set~ input]. { rewrite -compU. by apply/bigcupP; exists C. }
  rewrite -{C C_comp a_C}(def_pblock compI C_comp a_C).
  case/connect_irredP: (connectedTE G_conn a input) => p.
  move: (aNi); rewrite !inE. case/(splitR p) => [z][q][zi] {p}->.
  rewrite irred_cat. case/and3P=> _ _ /eqP/setP/(_ input).
  rewrite !inE eq_sym sg_edgeNeq // andbT => /negbT iNq.
  exists z => //.
  rewrite pblock_equivalence_partition // ?inE ?(sg_edgeNeq zi) //.
  + apply: (connectRI q) => x. rewrite !inE. by apply: contraTneq =>->.
  + exact: sedge_equiv_in.
Qed.

Lemma merge_subgraph_dot (G : graph) (V1 V2 : {set G}) (E1 E2 : {set edge G}) 
  (con1 : consistent V1 E1) (con2 : consistent V2 E2) i1 i2 o1 o2 :
  val o1 = val i2 -> [disjoint E1 & E2] -> (forall x, x \in V1 -> x \in V2 -> x = val o1) ->
  point (subgraph_for con1) i1 o1 · point (subgraph_for con2) i2 o2 ≃2
  point (subgraph_for (consistentU con1 con2))
        (Sub (val i1) (union_bij_proofL _ (valP i1))) 
        (Sub (val o2) (union_bij_proofR _ (valP o2))).
Proof.
  move => Eoi disE12 cap12. rewrite /dot/=/g2_dot.
  set G12 := (point _ _ _ ⊎ point _ _ _)%G.
  have eqvI (x : G) (inV1 : x \in V1) (inV2 : x \in V2)  :
    inl (Sub x inV1) = inr (Sub x inV2) %[mod @eqv_clot G12 [:: (unl output, unr input)]].
  { move: (inV1) (inV2). rewrite (cap12 _ inV1 inV2) {2 4}Eoi /= =>  ? ?. 
    rewrite !valK'. apply/eqquotP. exact: eqv_clot_hd. }
  set x0 := Sub (sval i1) (union_bij_proofL V2 (valP i1)).
  rewrite /x0 /G12. 
  apply: iso2_comp. apply: (iso_iso2 (merge_subgraph_iso eqvI disE12)).
  rewrite !(merge_subgraph_isoE eqvI disE12 x0).
  rewrite -> merge_nothing. 2: repeat constructor; exact: val_inj.  
  apply: (iso_iso2' (h := iso_id)); apply: val_inj => /=; by rewrite val_insubd inE ?(valP i1) ?(valP o2).
Qed.

Lemma merge_subgraph_par (G : graph) (V1 V2 : {set G}) (E1 E2 : {set edge G}) 
  (con1 : consistent V1 E1) (con2 : consistent V2 E2) (i1 o1 : subgraph_for con1) (i2 o2 : subgraph_for con2) :
  val i2 = val i1 -> val o2 = val o1 ->
  [disjoint E1 & E2] -> (forall x, x \in V1 -> x \in V2 -> x \in [set val i1; val o1]) ->
  point (subgraph_for con1) i1 o1 ∥ point (subgraph_for con2) i2 o2 ≃2
  point (subgraph_for (consistentU con1 con2))
        (Sub (val i1) (union_bij_proofL _ (valP i1))) 
        (Sub (val o2) (union_bij_proofR _ (valP o2))).
Proof.
  move => Ei Eo disE12 cap12. rewrite /par/=/g2_par. 
  set G12 := (point _ _ _ ⊎ point _ _ _)%G.
  have eqvI (x : G) (inV1 : x \in V1) (inV2 : x \in V2)  :
    inl (Sub x inV1) = inr (Sub x inV2) 
      %[mod @eqv_clot G12 [:: (unl input, unr input); (unl output, unr output)]].
  { case/set2P : (cap12 _ inV1 inV2) => ?; subst x; rewrite !valK' !/input !/output.
    rewrite -Ei in inV1 inV2 *. rewrite valK'. apply/eqquotP. by eqv.
    rewrite -Eo in inV1 inV2 *. rewrite valK'. apply/eqquotP. by eqv. }
  set x0 := Sub (sval i1) (union_bij_proofL V2 (valP i1)).
  rewrite /x0 /G12. 
  apply: iso2_comp. apply: (iso_iso2 (merge_subgraph_iso eqvI disE12)).
  rewrite !(merge_subgraph_isoE eqvI disE12 x0).
  rewrite -> merge_nothing. 2: repeat constructor; exact: val_inj.  
  apply: (iso_iso2' (h := iso_id)); apply: val_inj => /=; by rewrite val_insubd inE ?(valP i1) ?(valP o2).
Qed.

(** These two lemmas make use of [merge_subgraph_dot], drastically
simplifying their proofs (compared to the proofs underlying the ITP
2018 paper) *)

Lemma split_pip (G : graph2) : 
  connected [set: skeleton G] -> input != output :> G ->
  G ≃2 @bgraph _ _ G IO input · (@igraph _ _ G input output · @bgraph _ _ G IO output).
Proof.
  move => conn_G Dio. symmetry.
  have [Hi Ho] : input \in @CP (skeleton G) IO /\ output \in @CP (skeleton G) IO
    by split; apply: CP_extensive; rewrite !inE eqxx.
  rewrite-> dot2A. rewrite /= {1}/bgraph /igraph /induced.
  setoid_rewrite merge_subgraph_dot=>//=.
  2: exact: interval_bag_edges_disj.
  2: move => x; exact: (@bag_interval_cap G).
  rewrite /bgraph/induced.
  setoid_rewrite-> merge_subgraph_dot => //=.
  move: (union_bij_proofL _ _) => Pi.
  move: (union_bij_proofR _ _) => Po.
  move: (consistentU _ _) => con1.
  apply iso2_subgraph_forT => //=. 
  move => x. move: (sinterval_bag_cover conn_G Dio). 
    have: x \in [set: G] by []. rewrite /interval; set_tac.
  move => e. by rewrite -(interval_bag_edge_cover).  
  apply: disjointsU. exact: bag_edges_disj. 
  rewrite disjoint_sym interval_edges_sym. exact: interval_bag_edges_disj.
  move => x A B. rewrite inE (disjointFl (bag_disj conn_G _ _ Dio)) //= interval_sym in A.
    exact: (@bag_interval_cap G) B A. 
Qed.

Lemma split_cp (G : graph2) (u : skeleton G) :
  connected [set: skeleton G] -> u \in @cp G input output :\: IO ->
  edge_set (@bag G IO input) == set0 -> 
  edge_set (@bag G IO output) == set0 ->
  G ≃2 @igraph _ _ G input u · (@bgraph _ _ G IO u · @igraph _ _ G u output).
Proof.
  move => conn_G proper_u Ei0 Eo0. symmetry.
  have Dio: input != output :> G. 
  { apply: contraTneq proper_u => <-. by rewrite setUid cpxx setDv inE. }
  have [? ? ?] : [/\ input \in @CP G IO, output \in @CP G IO & u \in @CP G IO].
  { split; rewrite CP_set2 ?(@mem_cpl G) //; by [rewrite cp_sym (@mem_cpl G)|set_tac]. }
  rewrite-> dot2A. rewrite /= {1}/igraph /bgraph /induced.
  setoid_rewrite-> merge_subgraph_dot=>//. 
  2: by rewrite disjoint_sym interval_edges_sym interval_bag_edges_disj. 
  2: move => x A B; rewrite interval_sym in A; exact: (@bag_interval_cap G) B A.
  move: (union_bij_proofL _ _) => Pi.
  move: (union_bij_proofR _ _) => Po.
  move: (consistentU _ _) => con1.
  rewrite /igraph. setoid_rewrite merge_subgraph_dot=>//.
  apply iso2_subgraph_forT=>//.
  - move => x. 
    have: x \in @interval G input output. 
    { move: (sinterval_bag_cover conn_G Dio). 
      rewrite (eqP (edgeless_bag _ _ _)) // (eqP (edgeless_bag _ _ _)) //.
      rewrite setUC setUA [[set _;_]]setUC -/(@interval G _ _) => <- //. }
    rewrite (interval_cp_cover conn_G proper_u) /interval. by set_tac.
  - move => e.
    have: e \in interval_edges input output.
    { move: (interval_bag_edge_cover conn_G Dio).
      by rewrite (eqP Ei0) (eqP Eo0) set0U setU0 => <-. }
    by rewrite (interval_cp_edge_cover conn_G proper_u). 
  - apply: disjointsU. apply: interval_edges_disj_cp. by set_tac.
    apply: interval_bag_edges_disj => //. 
  - move => x. case/setUP. apply: (@interval_interval_cap G). by set_tac.
    exact: (@bag_interval_cap G).
Qed.


Lemma iso_split_par2 (G : graph2) (C D : {set G}) 
  (Ci : input \in C) (Co : output \in C) (Di : input \in D) (Do : output \in D) :
  C :&: D \subset IO -> C :|: D = setT -> 
  edge_set C :&: edge_set D = set0 -> edge_set C :|: edge_set D = setT ->
  G ≃2 point (induced C) (Sub input Ci) (Sub output Co)
     ∥ point (induced D) (Sub input Di) (Sub output Do).
Proof.
  move => subIO fullCD disjE fullE. symmetry. 
  apply: iso2_comp. apply: (merge_subgraph_par _ _ _ _) => //=.
    abstract by rewrite -setI_eq0 disjE //.
    abstract by move => x inC inD; apply: (subsetP subIO); exact/setIP.
  by apply: iso2_subgraph_forT => //=; rewrite ?fullCD ?fullE.
Qed.


Lemma comp_dom2_redirect (G : graph2) (C : {set G}) : 
  connected [set: skeleton G] -> input == output :> G ->
  edge_set G IO == set0 -> C \in @components G [set~ input] ->
  component C ≃2 dom (redirect C).
Proof.
  move => G_conn Eio no_loops HC.
  rewrite /redirect. case: pickP => [x /andP [inC adj_x] |].
  have E :  input |: (output |: C) = input |: (x |: C).
  { by rewrite (eqP Eio) [x |: C]setU1_mem // setUA setUid. }
  - apply: subgraph_for_iso => //; by rewrite ?E //= (eqP Eio).
  - case: (sig2W (comp_exit G_conn Eio HC)) => z Z1.
    rewrite sg_sym /=/sk_rel => /andP[_ B] /(_ z). by rewrite Z1 B.
Qed.

Lemma componentless_one (G : graph2) :
  input == output :> G -> edge_set G IO == set0 ->
  @components G [set~ input] == set0 -> G ≃2 1.
Proof.
  move => Eio E com0. 
  have A (x : G) : x = input. 
  { set C := pblock (@components G [set~ input]) x.
    apply: contraTeq com0 => Hx. apply/set0Pn. exists C. apply: pblock_mem.
    by rewrite (cover_partition (partition_components _)) !inE. }
  apply: iso_one => // [x|e]; first by rewrite !inE [x]A eqxx. 
  move/eqP/setP/(_ e) : E.  
  by rewrite !inE [source e]A [target e]A !eqxx.
Qed.

Lemma split_component (G : graph2) (C : {set G}) :
  edge_set G IO == set0 -> C \in @components G (~: IO) ->
  G ≃2 component C ∥ induced2 (~: C).
Proof.
  move=> NEio C_comp.
  case/and3P: (@partition_components G (~: IO)) => /eqP compU compI comp0n.
  have : C \subset ~: IO by rewrite -compU; apply/subsetP => x; exact: mem_cover.
  rewrite subsetC subUset !sub1set => /andP[iNC oNC]. rewrite induced2_induced.
  apply: iso_split_par2.
  - rewrite setUA setIUl setICr setU0. exact: subsetIl.
  - by rewrite -!setUA setUCr !setUT.
  - rewrite -(eqP NEio). apply/setP=> e; rewrite !inE.
    rewrite andbACA !orbA andb_orl andbN orbF.
    rewrite [_ && (target e \notin C)]andb_orl andbN orbF andbACA.
    apply/idP/idP => [/andP[->]//|He]. rewrite He /=.
    rewrite !inE in iNC oNC.
    case/andP: He => /orP[]/eqP-> /orP[]/eqP->; by rewrite ?iNC ?oNC.
  - apply/eqP. rewrite eqEsubset subsetT /=. apply/subsetP=> e _.
    rewrite !inE. case: (altP (source e =P target e)) => [<-|He].
      by rewrite !andbb -!orbA orbN.
    rewrite -negb_or orbC -implybE. apply/implyP.
    have {He} : @sedge G (source e) (target e) by rewrite /=/sk_rel He adjacent_edge.
    move: {e} (source e) (target e).
    suff Hyp (x y : G) : @sedge G x y -> x \in C ->
                         [|| y == input, y == output | y \in C].
    { move=> x y xy /orP[]H; rewrite H !orbT /= ?andbT; first exact: Hyp xy H.
      move: H. have : @sedge G y x by rewrite sg_sym. exact: Hyp. }
    move=> xy Hx. have := component_exit xy C_comp Hx. by rewrite !inE negbK orbA.
Qed.

Lemma componentless_top (G : graph2) : 
  input != output :> G -> @components G (~: IO) == set0 -> 
  point (@remove_edges _ _ G (edge_set IO)) input output ≃2 top.
Proof.
  move => Dio com0.
  have A (x: G) : x \in IO. 
  { set C := pblock (@components G (~: IO)) x.
    apply: contraTT com0 => Hx. apply/set0Pn. exists C. apply: pblock_mem. 
    by rewrite (cover_partition (partition_components _)) inE. }
  apply: iso_top => //.
  move => [e He]. rewrite inE negb_and in He. 
  case/orP: He; by rewrite A.
Qed.  

Lemma split_io_edge_aux (G : graph2) (e : edge G) :
  e \in edges input output -> point (remove_edges [set e] ∔ [input, elabel e, output]) input output ≃2 G.
Proof.
  rewrite inE => /andP [/eqP Es /eqP Et]. rewrite -{1}Es -{1}Et.
  apply: iso2_comp. apply: iso_iso2. apply: remove_edge_add. by case: G e {Es Et}.
Qed.

Lemma split_io_edge (G : graph2) (e : edge G) : 
  e \in edges input output -> 
  G ≃2 edge_graph2 1%CM (elabel e) 1%CM ∥ point (remove_edges [set e]) input output.
Proof.
  move => e_io. symmetry. 
  rewrite /par/=/g2_par/=. 
  apply: iso2_comp. apply: merge_iso2. apply: union_add_edge_l. rewrite /=.
  apply: iso2_comp. apply: iso_iso2. apply: merge_add_edge. rewrite !merge_add_edgeE.
  apply: iso2_comp. apply: iso_iso2. apply: add_edge_iso. apply: merge_iso. 
    apply: union_C. rewrite !merge_isoE /=. 
  pose k (x : @two_graph _ (flat sym) tt tt) : remove_edges [set e] := 
    match x with inl tt => input | inr tt => output end.
  eapply iso2_comp. apply: iso_iso2. apply: add_edge_iso. apply (merge_union_K (k := k)).
  - done.
  - abstract (case => [[]|[]] /=; apply/eqquotP; eqv).
  - abstract (repeat case).
  - rewrite /= !merge_union_KE /= {}/k. 
    apply: iso2_comp. apply: iso_iso2. apply: iso_sym. apply: merge_add_edge. 
    Unshelve. (* why? *)
    rewrite !(@merge_add_edgeE _ _ _ _ input (elabel e) output _).
    apply: iso2_comp. apply: @merge_nothing. 
    + abstract (repeat constructor).
    + exact: split_io_edge_aux.
Qed.

Lemma split_io_edge_lens (G : graph2) (e : edge G) : 
  e \in edge_set IO -> lens G -> G ≃2 graph_of_term (tm_ e) ∥ point (remove_edges [set e]) input output.
Proof.
  move => e_io lens_G. rewrite lens_io_set // inE in e_io. 
  rewrite /tm_. case: ifP e_io => //= [e_io _|eNio e_oi]; first exact: split_io_edge.
  rewrite <- cnv2I. 
  have e_io : e \in @edges _ _ (g2_cnv G) input output by [].
  rewrite -> (split_io_edge e_io) at 1. by rewrite -> cnv2par. 
Qed.

Lemma split_io_loop (G : graph2) (e : edge G) : 
  e \in edge_set IO -> input == output :> G -> G ≃2 graph_of_term (tm_ e) ∥ point (remove_edges [set e]) input output.
Proof.
  move => e_io /eqP Eio. rewrite inE -Eio setUid !inE in e_io. 
  rewrite /tm_ inE -Eio e_io {2}Eio /=. apply: split_io_edge. by rewrite inE -Eio.
Qed.

Theorem term_of_iso (G : graph2) : 
  CK4F G -> G ≃2 graph_of_term (term_of G).
Proof.
  elim/(size_ind (@term_of_measure sym)) : G => G IH CK4F_G.
  rewrite term_of_eq // /term_of_rec. 
  case: ifP => [C1|/negbT C1].
  - (* selfloops / io-redirect *)
    case: picksP => [e e_io|/eqP C2]; last first.
    + case: pickP => [C HC|/(_ _) HC] /=.
      * setoid_rewrite (@split_component _ C) at 1 =>//.
        rewrite -?(eqP C1) ?setUid.
        have G_conn : connected [set: skeleton G] by case: CK4F_G.
        setoid_rewrite <-IH=>//.
        setoid_rewrite comp_dom2_redirect=>//. 
        -- exact: measure_redirect.
        -- exact: CK4F_redirect.
        -- move: HC. rewrite -[set1 input]setUid {2}(eqP C1).
           exact: measure_remove_component.
        -- exact: CK4F_remove_component.
        -- by rewrite -?(eqP C1) ?setUid.
      * have : @components G [set~ input] == set0.
        { rewrite -subset0. apply/subsetP => C. by rewrite HC. }
        exact: componentless_one.
    + rewrite -> (split_io_loop e_io C1) at 1. simpl. rewrite <- IH => //.
      * apply: measure_remove_edges. exact: set10.
      * apply: CK4F_remove_loops => //. by rewrite sub1set.
  - case: ifP => [C2|/negbT C2].
    + (* parallel split *)
      have EC := lens_sinterval (proj1 CK4F_G) C2.
      case: picksP => [e e_io|/eqP C3]; last first.
      * case: pickP => [C HC|]. 
        -- rewrite EC in HC. setoid_rewrite (split_component _ HC) at 1=> //=.  
           apply: par_iso2. 
           ++ apply IH; rewrite -EC in HC.
              exact: measure_lens. exact: CK4F_lens.
           ++ apply IH; rewrite -EC in HC. 
              exact: measure_lens_rest. exact: CK4F_lens_rest.
        -- have := split_K4_nontrivial C1 C2 _ CK4F_G. 
           rewrite edge_set_adj // => /(_ isT)/ltnW.
           move=>H H'. exfalso. move: H H'.  
           case/card_gt0P => C HC /(_ C). by rewrite HC.
      * rewrite EC. case: (boolP (_ && _)) => C4 /=. 
        -- case/andP : C4 => C4 E4.  
           rewrite -> (split_io_edge_lens e_io C2) at 1.
           have -> : [set e] = edge_set IO. 
           { apply/eqP. by rewrite eqEsubset sub1set e_io -setD_eq0. }
           by rewrite -> componentless_top, par2top.
        -- setoid_rewrite (split_io_edge_lens e_io C2) at 1. apply: par_iso2 => //.
           rewrite negb_and -EC in C4. move/orP in C4.
           apply: IH. 
           ++ apply: measure_remove_edges. exact: set10.
           ++ apply: CK4F_remove_edges => //=. by rewrite sub1set.
    + (* bag/sequential split *) 
      rewrite /simple_check_point_term. 
      case: ifP => [A|/negbT A].
      * rewrite /=. (* TODO: clean this up *)
        setoid_rewrite <-IH; first last. 
          apply rec_bag => //; apply: CP_extensive; by rewrite !inE eqxx.
          apply rec_bag => //; apply: CP_extensive; by rewrite !inE eqxx.
          apply: CK4F_igraph => //; last rewrite cp_sym; exact: mem_cpl.
          apply: measure_igraph => //; by case: CK4F_G.
          apply rec_bag => //; apply: CP_extensive; by rewrite !inE eqxx.
          apply rec_bag => //; apply: CP_extensive; by rewrite !inE eqxx.
        case: CK4F_G => G_conn _. setoid_rewrite <-dot2A. exact: split_pip.
      * move: A. rewrite negb_or !negbK. case/andP => A B.
        rewrite /lens !negb_and A B (negbTE C1) /= in C2.
        case: pickP => [z Hz|C]; last first.
        { case:notF. apply: contraNT C2 => _. rewrite -setD_eq0. 
          apply/eqP. apply/setP => x. by rewrite C inE. }
        rewrite /=. 
        setoid_rewrite (split_cp (proj1 CK4F_G) Hz) at 1 => //.
        setoid_rewrite dot2A. repeat apply: dot_iso2.
        -- apply IH=> //. exact: measure_split_cpL. exact: CK4F_split_cpL.
        -- suff ? : z \in @CP G IO. { apply IH => //; by apply rec_bag. }
           case/setDP : Hz => Hz _. apply/bigcupP; exists (input,output) => //. 
           by rewrite !inE !eqxx.
        -- apply IH=> //. exact: measure_split_cpR. exact: CK4F_split_cpR.
Qed.
End ExtractionIso.
