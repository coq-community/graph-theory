Require Import RelationClasses Morphisms Setoid Omega.

From mathcomp Require Import all_ssreflect.

Require Import edone finite_quotient preliminaries.
Require Import digraph sgraph minor checkpoint.
Require Import multigraph ptt_algebra equiv ptt_graph skeleton.
Require Import bounded extraction_def.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 


(** * Isomorphim Theorem *)

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
  rewrite irred_cat. case/and3P=> _ _ /eqP/setP/(_ g_in).
  rewrite !inE eq_sym sg_edgeNeq // andbT => /negbT iNq.
  exists z => //.
  rewrite pblock_equivalence_partition // ?inE ?(sg_edgeNeq zi) //.
  + apply: (connectRI (p := q)) => x. rewrite !inE. by apply: contraTneq =>->.
  + exact: sedge_equiv_in.
Qed.

(* TOMOVE to ptt_graph? *)
Lemma subgraph_for_iso (G : graph2) V1 V2 E1 E2 i1 i2 o1 o2
  (C1 : @consistent G V1 E1) (C2: consistent V2 E2) :
  V1 = V2 -> E1 = E2 -> val i1 = val i2 -> val o1 = val o2 ->
  point (subgraph_for C1) i1 o1 ≈ point (subgraph_for C2) i2 o2.
Proof.
  move => eq_V eq_E eq_i eq_o. subst.
  move/val_inj : eq_i => ->. move/val_inj : eq_o => ->.
  apply (@Iso2 (point (subgraph_for C1) i2 o2) (point (subgraph_for C2) i2 o2) bij_id bij_id).
  split=>//. split=>//=e.
    * by rewrite (bool_irrelevance (source_proof C1 e) (source_proof C2 e)).
    * by rewrite (bool_irrelevance (target_proof C1 e) (target_proof C2 e)).
Qed.

Lemma iso_top (G : graph2) :
  g_in != g_out :> G -> 
  (forall x : G, x \in IO) -> 
  (forall e : edge G, False) -> G ≈ top2.
Proof.
  move => Dio A B. 
  pose f (x : G) : top2 := 
    if x == g_in then g_in else g_out.
  pose f' (x : top2) : G := 
    if x == g_in then g_in else g_out.
  pose g (e : edge G) : edge top2 := 
    match (B e) with end.
  pose g' (e : edge top2) : edge G := 
    match e with end.
  unshelve refine (@Iso2 _ _ (@Bij _ _ f f' _ _) (@Bij _ _ g g' _ _) _)=>/=.
  - rewrite /f/f'/= => x.
    case: (boolP (x == g_in)) => [/eqP <-|/=]; first by rewrite eqxx.
    move: (A x). case/setUP => /set1P => -> //. by rewrite eqxx.
  - rewrite /f/f'/= => x.
    case: (boolP (x == false)) => [/eqP <-|/=]; first by rewrite eqxx.
    case: x => // _. by rewrite eq_sym (negbTE Dio).
  - by [].
  - by [].
  - split=>//. by rewrite /f eqxx. by rewrite /f eq_sym (negbTE Dio).
Qed.

Lemma iso_one (G : graph2) :
  g_in == g_out :> G -> 
  (forall x : G, x \in IO) -> 
  (forall e : edge G, False) -> G ≈ one2.
Proof.
  move => Dio A B. 
  pose f (x : G) : one2 := g_in.
  pose f' (x : one2) : G := g_in.
  pose g (e : edge G) : edge one2 := 
    match (B e) with end.
  pose g' (e : edge one2) : edge G := 
    match e with end.
  unshelve refine (@Iso2 _ _ (@Bij _ _ f f' _ _) (@Bij _ _ g g' _ _) _)=>/=.
  - rewrite /f/f'/= => x.
    move: (A x). rewrite !inE -(eqP Dio) => /orP. by case => /eqP->.
  - by move => [].
  - by [].
  - by [].
  - split=>//.
Qed.
  
Lemma iso_split_par2 (G : graph2) (C D : {set G}) 
  (Ci : g_in \in C) (Co : g_out \in C) (Di : g_in \in D) (Do : g_out \in D) :
  C :&: D \subset IO -> C :|: D = setT -> 
  edge_set C :&: edge_set D = set0 -> edge_set C :|: edge_set D = setT ->
  G ≈ (par2 (point (induced C) (Sub g_in Ci) (Sub g_out Co)) 
            (point (induced D) (Sub g_in Di) (Sub g_out Do))).
Proof.
  move => subIO fullCD disjE fullE. symmetry. setoid_rewrite par2_alt.
  set G1 := point _ _ _. set G2 := point _ _ _. set G' := par2' _ _.

  have injL (x y : G1) : inl x = inl y %[mod @par2_eqv_equivalence G1 G2] -> x = y.
  { move=> /eqquotP/=. rewrite /par2_eqv sum_eqE -!(inj_eq val_inj) !SubK andbb.
    case/orP=> [/eqP|]; first exact: val_inj.
    case: ifPn; rewrite ?negbK ?in_set2 => Eio; first case/orP.
    all: rewrite 1?eqEcard subUset !sub1set !in_setU !in_set1 !sum_eqE !orbF.
    - by case/andP=> /andP[]/eqP->/eqP->.
    - by case/andP=> /andP[]/eqP->/eqP->.
    - by case/andP=> /orP[]/eqP-> /orP[]/eqP->; apply: val_inj => //=; rewrite -(eqP Eio). }
  have injR (x y : G2) : inr x = inr y %[mod @par2_eqv_equivalence G1 G2] -> x = y.
  { move=> /eqquotP/=. rewrite /par2_eqv sum_eqE -!(inj_eq val_inj) !SubK andbb.
    case/orP=> [/eqP|]; first exact: val_inj.
    case: ifPn; rewrite ?negbK ?in_set2 => Eio; first case/orP.
    all: rewrite 1?eqEcard subUset !sub1set !in_setU !in_set1 !sum_eqE.
    - by case/andP=> /andP[]/eqP->/eqP->.
    - by case/andP=> /andP[]/eqP->/eqP->.
    - by case/andP=> /orP[]/eqP-> /orP[]/eqP->; apply: val_inj => //=; rewrite -(eqP Eio). }
  pose valE := f_equal val. 
  pose inLR := par2_LR.
  pose inRL := fun e => par2_LR (esym e).

  pose f (x : G') : G := match repr x with inl x => val x | inr x => val x end.
  pose h (e : edge G') : edge G := match e with inl e => val e | inr e => val e end.
  have decV (v : G) : ((v \in C) + (v \in D))%type.
  { have : v \in [set: G] by []. rewrite -fullCD in_setU.
    case: (boolP (v \in C)) => HC /= HD; by [left|right]. }
  pose g (x : G) : G' :=
    match decV x with
    | inl p => \pi inl (Sub x p)
    | inr p => \pi inr (Sub x p)
    end.
  have decE (e : edge G) : ((e \in edge_set C) + (e \in edge_set D))%type.
  { have : e \in [set: edge G] by []. rewrite -fullE in_setU.
    case: (boolP (e \in edge_set C)) => HC /= HD; by [left|right]. }
  pose k (e : edge G) : edge G' :=
    match decE e with
    | inl p => inl (Sub e p)
    | inr p => inr (Sub e p)
    end.
  apply Iso2'' with f g h k. 
  - rewrite /f/g=>x.
    case Ex: (repr x) => [y|y]; have Hy : val y \in _ := valP y; case: (decV _) => H.
      * rewrite -[x]reprK Ex. congr (\pi (inl _)). exact: val_inj.
      * have {Hy} /(subsetP subIO) Hy : val y \in C :&: D by rewrite in_setI Hy H.
        rewrite in_set2 in Hy. rewrite -[x]reprK Ex. apply/eqquotP.
        rewrite /=/par2_eqv. case: ifPn => _; last first.
        { rewrite subUset !sub1set !in_setU !in_set1.
          by rewrite !sum_eqE -!(inj_eq val_inj) !SubK !Hy. }
        rewrite in_set2 2!eqEcard !cards2 2!subUset 4!sub1set.
        rewrite 4!in_set2 !sum_eqE -!(inj_eq val_inj) !SubK.
        by rewrite /= !orbF !andbT !andbb.
      * have {Hy} /(subsetP subIO) Hy : val y \in C :&: D by rewrite in_setI Hy H.
        rewrite in_set2 in Hy. rewrite -[x]reprK Ex. apply/eqquotP.
        rewrite /=/par2_eqv. case: ifPn => _; last first.
        { rewrite subUset !sub1set !in_setU !in_set1.
          by rewrite !sum_eqE -!(inj_eq val_inj) !SubK !Hy. }
        rewrite in_set2 2!eqEcard !cards2 2!subUset 4!sub1set.
        rewrite 4!in_set2 !sum_eqE -!(inj_eq val_inj) !SubK.
        by rewrite /= !orbF !andbT !andbb.
      * rewrite -[x]reprK Ex. congr (\pi (inr _)). exact: val_inj.
  - rewrite /f/g=>x. case: (decV x) => Hx; case: piP => -[]y.
      * by move=> /injL<-.
      * by case/inLR=> -[]/valE/=->->.
      * by case/inRL=> -[->]/valE/=->.
      * by move=> /injR<-.
  - rewrite /h/k=>e. case:e=> [e|e].
    + have He : val e \in edge_set C := valP e.
      case: (decE _) => H; first by congr inl; exact: val_inj.
      suff : val e \in edge_set C :&: edge_set D by rewrite disjE inE.
      by rewrite in_setI He H.
    + have He : val e \in edge_set D := valP e.
      case: (decE _) => H; last by congr inr; exact: val_inj.
      suff : val e \in edge_set C :&: edge_set D by rewrite disjE inE.
      by rewrite in_setI He H.
  - rewrite /h/k=>e. by case: (decE e).
  - case => [e|e]; split => //.
    + rewrite /f/h. case: piP => [[y|y]] /=. 
      * by move/injL <-. 
      * by move/(@par2_LR G1 G2) => [[/valE/= -> ->]|[/valE/= -> ->]].
    + rewrite /f/h. case: piP => [[y|y]] /=. 
      * by move/injL <-. 
      * by move/(@par2_LR G1 G2) => [[/valE/= -> ->]|[/valE/= -> ->]].
    + rewrite /f/h. case: piP => [[y|y]] /=. 
      * by move/esym/(@par2_LR G1 G2) => [[-> /valE/= ->]|[-> /valE/= ->]].
      * by move/injR <-. 
    + rewrite /f/h. case: piP => [[y|y]] /=. 
      * by move/esym/(@par2_LR G1 G2) => [[-> /valE/= ->]|[-> /valE/= ->]].
      * by move/injR <-. 
  - rewrite /f. case: piP => [[y|y]] /=. 
    + by move/injL<-.
    + by move/(@par2_LR G1 G2) => [[_ ->]|[/valE/= -> ->]]. 
  - rewrite /f. case: piP => [[y|y]] /=. 
    + by move/injL<-.
    + by move/(@par2_LR G1 G2) => [[/valE/= -> ->]|[_ ->]].
Qed.

Lemma comp_dom2_redirect (G : graph2) (C : {set G}) : 
  connected [set: skeleton G] -> g_in == g_out :> G ->
  @edge_set G IO == set0 -> C \in @components G [set~ g_in] ->
  component C ≈ dom2 (redirect C).
Proof.
  move => G_conn Eio no_loops HC.
  rewrite /redirect. case: pickP => [x /andP [inC adj_x] |].
  have E :  g_in |: (g_out |: C) = g_in |: (x |: C).
  { by rewrite (eqP Eio) [x |: C]setU1_mem // setUA setUid. }
  - apply: subgraph_for_iso => //; by rewrite ?E //= (eqP Eio).
  - case: (sig2W (comp_exit G_conn Eio HC)) => z Z1.
    rewrite sg_sym /=/sk_rel => /andP[_ B] /(_ z). by rewrite Z1 B.
Qed.

Lemma componentless_one (G : graph2) :
  g_in == g_out :> G -> @edge_set G IO == set0 ->
  @components G [set~ g_in] == set0 -> G ≈ one2.
Proof.
  move => Eio E com0. 
  have A (x : G) : x = g_in. 
  { set C := pblock (@components G [set~ g_in]) x.
    apply: contraTeq com0 => Hx. apply/set0Pn. exists C. apply: pblock_mem.
    by rewrite (cover_partition (partition_components _)) !inE. }
  apply: iso_one => // [x|e]; first by rewrite !inE [x]A eqxx. 
  move/eqP/setP/(_ e) : E.  
  by rewrite !inE [source e]A [target e]A !eqxx.
Qed.

Lemma split_component (G : graph2) (C : {set G}) :
  @edge_set G IO == set0 -> C \in @components G (~: IO) ->
  G ≈ par2 (component C) (induced2 (~: C)).
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
                         [|| y == g_in, y == g_out | y \in C].
    { move=> x y xy /orP[]H; rewrite H !orbT /= ?andbT; first exact: Hyp xy H.
      move: H. have : @sedge G y x by rewrite sg_sym. exact: Hyp. }
    move=> xy Hx. have := component_exit xy C_comp Hx. by rewrite !inE negbK orbA.
Qed.

Lemma split_cp (G : graph2) (u : skeleton G) :
  connected [set: skeleton G] -> u \in @cp G g_in g_out :\: IO ->
  edge_set (@bag G IO g_in) == set0 -> 
  edge_set (@bag G IO g_out) == set0 ->
  G ≈ @igraph G g_in u · (@bgraph G IO u · @igraph G u g_out).
Proof.
  move=> G_conn u_cpio pi_e0 po_e0. symmetry.
  setoid_rewrite (dot2_alt (bgraph IO u)).
  setoid_rewrite dot2_alt. set G' := dot2' _ _.
  have [i_cp o_cp] : g_in \in @CP G IO /\ g_out \in @CP G IO.
  { by split; apply: CP_extensive; rewrite !inE eqxx. }
  have u_cp : u \in @CP G IO.
  { apply/bigcupP; exists (g_in, g_out) => /=; first by rewrite !inE !eqxx.
    by move: u_cpio; rewrite inE => /andP[_]. }
  have [uNi uNo] : u != g_in /\ u != g_out.
  { by move: u_cpio; rewrite 4!inE negb_or => /andP[]/andP[]. }
  have iNo : g_in != g_out :> G.
  { apply: contraTneq u_cpio => <-. by rewrite setUid cpxx !inE andNb. }
  have intvL_node (x : G) : x \in g_in |: @sinterval G g_in u ->
                                  x \in @interval G g_in u.
  { by rewrite [_ \in @interval G _ _]inE (lock sinterval) !inE -lock orbAC =>->. }
  have intvR_node (x : G) : x \in g_out |: @sinterval G u g_out ->
                                  x \in @interval G u g_out.
  { by rewrite [_ \in @interval G _ _]inE (lock sinterval) !inE -lock -orbA =>->. }
  have bag_node (x : G) : x \notin (g_in  |: @sinterval G g_in u) ->
                          x \notin (g_out |: @sinterval G u g_out) ->
                          x \in @bag G IO u.
  { rewrite ![x \in _ |: _]inE ![x \in set1 _]inE !negb_or.
    move=> /andP[/negbTE xNi /negbTE xNl] /andP[/negbTE xNo /negbTE xNr].
    have : x \in [set : skeleton G] by [].
    rewrite (sinterval_bag_cover G_conn iNo).
    rewrite (eqP (edgeless_bag _ (CP_extensive _) pi_e0)) ?in_set2 ?eqxx //.
    rewrite (eqP (edgeless_bag _ (CP_extensive _) po_e0)) ?in_set2 ?eqxx //.
    rewrite !in_setU !in_set1 xNi xNo orbF /=.
      by rewrite (sinterval_cp_cover G_conn u_cpio) !in_setU -orbA xNl xNr orbF. }
  have bag_edge (e : edge G) : e \notin @interval_edges G g_in u ->
                                   e \notin @interval_edges G u g_out ->
                                   e \in edge_set (@bag G IO u).
  { move=> /negbTE eNl /negbTE eNr. have : e \in [set: edge G] by [].
    rewrite (interval_bag_edge_cover G_conn iNo).
    rewrite (eqP pi_e0) (eqP po_e0) set0U setU0.
      by rewrite (interval_cp_edge_cover G_conn u_cpio) !in_setU eNl eNr orbF. }
  pose f (x : G') : G :=
    match repr x with
    | inl x => val x
    | inr x => match repr x with
               | inl x => val x
               | inr x => val x
               end
    end.
  pose g (x : G) : G' :=
      match boolP (x \in g_in |: @sinterval G g_in u) with
      | AltTrue xL => \pi (inl (Sub x (intvL_node x xL)))
      | AltFalse xNl => match boolP (x \in g_out |: @sinterval G u g_out) with
                        | AltTrue xR => \pi (inr (\pi (inr (Sub x (intvR_node x xR)))))
                        | AltFalse xNr => \pi (inr (\pi (inl (Sub x (bag_node x xNl xNr)))))
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
  pose k (e : edge G) : edge G' :=
    match boolP (e \in @interval_edges G g_in u) with
    | AltTrue eL => inl (Sub e eL)
    | AltFalse eNl => match boolP (e \in @interval_edges G u g_out) with
                      | AltTrue eR => inr (inr (Sub e eR))
                      | AltFalse eNr => inr (inl (Sub e (bag_edge e eNl eNr)))
                      end
    end.
    
  pose valE := f_equal val. pose injL := dot2_injL. pose injR := dot2_injR.
  pose inLR := dot2_LR. pose inRL := fun e => dot2_LR (esym e).
  apply Iso2'' with f g h k.
  - rewrite /f/g=>x.
    case Ex: (repr x) => [y|y]; last case Ey: (repr y) => [z|z]. 
    * have yL : val y \in @interval G g_in u := valP y. case: {-}_ / boolP => H1.
      { rewrite -[x]reprK Ex; congr (\pi (inl _)); exact: val_inj. }
      have Ey : val y = u.
      { move: H1 yL. rewrite [_ \in @interval G _ _]inE (lock sinterval) !inE -lock.
        rewrite negb_or => /andP[/negbTE-> /negbTE->]. by rewrite orbF => /eqP. }
      case: {-}_ / boolP => H2.
      { have := H2; rewrite {1}Ey 2!inE (@sinterval_bounds G).
        by move: u_cpio; rewrite 4!inE negb_or => /andP[]/andP[_]/negbTE->. }
      rewrite -[x]reprK Ex. apply/eqquotP.
      rewrite /=/dot2_eqv -[_ == inl y]/false.
      rewrite eqEcard subUset !sub1set !inE !sum_eqE !cards2.
      rewrite -![inl _ == inr _]/false -![inr _ == inl _]/false.
      rewrite -(inj_eq val_inj) [_ && (_ || _)]andbC {1}Ey eqxx andbT.
      apply/eqP. apply/eqquotP. rewrite /=/dot2_eqv sum_eqE.
      by rewrite -(inj_eq val_inj) SubK {1}Ey eqxx.
    * have z_bag : val z \in @bag G IO u := valP z.
      have /negbTE zNl : val z \notin g_in |: @sinterval G g_in u.
      { rewrite 2!inE negb_or sinterval_sym. apply/andP; split.
        - by apply: contraTneq z_bag =>->; rewrite (bag_cp G_conn) 1?eq_sym.
        - by rewrite (disjointFr (interval_bag_disj u _) z_bag). }
      have /negbTE zNr : val z \notin g_out |: @sinterval G u g_out.
      { rewrite 2!inE negb_or. apply/andP; split.
        - by apply: contraTneq z_bag =>->; rewrite (bag_cp G_conn) 1?eq_sym.
        - by rewrite (disjointFr (interval_bag_disj u _) z_bag). }
      case: {-}_ / boolP => H1; first by have := H1; rewrite zNl.
      case: {-}_ / boolP => H2; first by have := H2; rewrite zNr.
      rewrite -[x]reprK Ex -[y]reprK Ey. congr (\pi (inr (\pi (inl _)))).
      exact: val_inj.
    * have zR : val z \in @interval G u g_out := valP z.
      have /negbTE zNl : val z \notin g_in |: @sinterval G g_in u.
      { rewrite 2!inE negb_or. move: zR. rewrite 4!inE -orbA.
        case/or3P=> [/eqP->|/eqP->|zR]; apply/andP; split=> //.
        - by rewrite (@sinterval_bounds G).
        - by rewrite eq_sym.
        - rewrite inE negb_and !negbK.
          by move: u_cpio; rewrite inE cp_sym => /andP[_]->.
        - apply: contraTneq zR => ->. rewrite inE negb_and !negbK.
          by move: u_cpio; rewrite inE => /andP[_]->.
        - rewrite (disjointFl (@sinterval_disj_cp G g_in g_out u _) zR) //.
          by move: u_cpio; rewrite inE => /andP[_]. }
      case: {-}_ / boolP => H1; first by have := H1; rewrite zNl.
      case: {-}_ / boolP => H2.
      { rewrite -[x]reprK Ex -[y]reprK Ey. congr (\pi (inr (\pi (inr _)))).
        exact: val_inj. }
      move: zR; rewrite 4!inE. have := H2; rewrite 2!inE negb_or.
      case/andP=> /negbTE-> /negbTE->; rewrite !orbF => /eqP y_u.
      rewrite -[x]reprK Ex -[y]reprK Ey. congr (\pi (inr _)). apply/eqquotP.
      rewrite /=/dot2_eqv -[_ == inr z]/false.
      rewrite eqEcard subUset !sub1set !inE !sum_eqE !cards2.
      rewrite -![inl _ == inr _]/false -![inr _ == inl _]/false.
      by rewrite -!(inj_eq val_inj) SubK/= y_u eqxx /=.

  - rewrite /f/g=>x. case: {-}_ / boolP => H1; last case: {-}_ / boolP => H2.
    * case: piP => -[y /injL/valE//|y /inLR[/valE?{y}->]].
      by case: piP => -[y /injL<-|y /inLR[_]->].
    * case: piP => -[y /inRL[->]/inRL[_]/valE//|y /injR<-{y}].
      by case: piP => -[y /inRL[->]/valE|y /injR<-].
    * case: piP => -[y /inRL[->]/injL/valE//|y /injR<-{y}].
      by case: piP => -[y /injL<-|y /inLR[/valE?->]].

  - rewrite /h/k=>e. case: e => [e|[e|e]].
    + have eL : val e \in @interval_edges G g_in u := valP e.
      case: {-}_ / boolP => H1; last by have := H1; rewrite eL.
      congr inl; exact: val_inj.
    + have e_bag : val e \in edge_set (@bag G IO u) := valP e.
      case: {-}_ / boolP => H1; first (have := H1; rewrite {1}interval_edges_sym).
        by rewrite (disjointFr (interval_bag_edges_disj G_conn _ _) e_bag).
      case: {-}_ / boolP => H2; first have := H2.
        by rewrite (disjointFr (interval_bag_edges_disj G_conn _ _) e_bag).
      congr (inr (inl _)); exact: val_inj.
    + have eR : val e \in @interval_edges G u g_out := valP e.
      case: {-}_ / boolP => H1; first have := H1.
      { rewrite (disjointFl (@interval_edges_disj_cp G g_in g_out u _) eR) //.
        by move: u_cpio; rewrite inE => /andP[_]. }
      case: {-}_ / boolP => H2; last by have := H2; rewrite eR.
      congr (inr (inr _)); exact: val_inj.
  - rewrite /h/k=>e; by repeat case: {-}_ / boolP => ?.

  - case=> [e|[e|e]]; rewrite /h; split; rewrite // /f.
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
Qed.

Definition sym2_ (G : graph2) (e : edge G) :=
  if e \in edges g_in g_out then sym2 (label e) else cnv2 (sym2 (label e)).

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
Proof. 
  apply: iso_top => //; last by case. 
  move => x. rewrite !inE. by case: x.
Qed.

Lemma ord_0Vp n (o : 'I_n.+1) : (o = ord0) + ({o' : 'I_n | o'.+1 = o :> nat}).
Proof.
  case: (unliftP ord0 o); last by left.
  move => o' A. right. exists o'. by rewrite A.
Qed.

Lemma edges2_cons (a : sym) (b : bool) (Ar : seq (sym * bool)) : 
  edges2 ((a, b) :: Ar) ≈ par2 (sym2b a b) (edges2 Ar).
Proof.
  setoid_rewrite par2_alt.
  rewrite sym_eqv. (* this makes h actually typecheck *)
  set E1 := edges2 _.
  set E2 := par2' _ _.
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
  pose k (e : edge E2) : edge E1 := 
    match e with inl tt => ord0 | inr i => lift ord0 i end.
  apply Iso2'' with f g h k.
  - rewrite /f/g=>x.
    case: piP => [] [y|y] /= /esym Hy.
    * move/(@par2_LR (sym2b' a b) (edges2 Ar)) : Hy.
      case => [[-> ->]|[-> ->]]; by destruct b.
    * move/(@par2_injR (sym2b' a b) (edges2 Ar)) : Hy. apply. 
        by destruct b.
  - rewrite /f/g=>x. case Rx : (repr x) => [y|y]; last by rewrite -Rx reprK.
      rewrite -[x]reprK Rx => {x Rx}. symmetry. apply/eqquotP => /=. 
      destruct b;destruct y => //=;
      solve [exact: par2_eqv_oo|exact: par2_eqv_ii].
  - rewrite /h/k=>x. case: (ord_0Vp x) => [-> //|[o' Ho']].
      apply: ord_inj. by rewrite lift0.
  - rewrite /h/k. case=> [[]|x]. 
      by case: (ord_0Vp ord0) => [|[o' Ho']].
      case: (ord_0Vp _) => [|[o']]. 
    * move/(f_equal (@nat_of_ord _)). by rewrite lift0.
    * move/eqP. rewrite lift0 eqSS => /eqP E. 
      congr inr. exact: ord_inj.
  - move => e. split.
    * rewrite [source]lock /= -lock. rewrite /h /=.
      case: (ord_0Vp e) => [E|[o' Ho']].
      + rewrite E /f /=. destruct b eqn: def_b.
        all: symmetry; apply/eqquotP => //=.
        exact: par2_eqv_ii.
        exact: par2_eqv_oo.
      + rewrite /=(tnth_cons Ho'). by case: (tnth _ _) => a' b'.
    * rewrite [target]lock /= -lock. rewrite /h /=.
      case: (ord_0Vp e) => [E|[o' Ho']].
      + rewrite E /f /=. destruct b eqn: def_b.
        all: symmetry; apply/eqquotP => //=.
        exact: par2_eqv_oo.
        exact: par2_eqv_ii.
      + rewrite /=(tnth_cons Ho'). by case: (tnth _ _) => a' b'.
    * rewrite /h/=. case: (ord_0Vp e) => [-> //|[o' Ho']].
        by rewrite (tnth_cons Ho'). 
  - rewrite /f /=. symmetry. apply/eqquotP => //=. exact: par2_eqv_ii.
  - rewrite /f /=. symmetry. apply/eqquotP => //=. exact: par2_eqv_oo.
Qed.

Lemma edges2_big (As : seq (sym * bool)) : 
  edges2 As ≈ \big[par2/top2]_(x <- As) sym2b x.1 x.2.
Proof.
  elim: As => [|[a b] Ar IH].
  - setoid_rewrite big_nil. apply edges2_nil.
  - setoid_rewrite big_cons. setoid_rewrite <-IH. apply edges2_cons.
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
  move => E. setoid_rewrite par2_alt.
  set G' := par2' _ _.
  pose S := [seq strip e | e in E].
  pose n := size S.
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
  have cast: size [seq strip e | e in E] = size (enum E).
  { by rewrite size_map. }
  pose k (e : edge G') := 
    match e with 
    | inl i => (tnth (in_tuple (enum E)) (cast_ord cast i))
    | inr e => val e
    end.
  apply Iso2'' with f g h k.
  - rewrite /f/g=>x/=.
    case: piP => /= [[y|y]] /esym Hy.
    * move/(@par2_LR (edges2 [seq strip e | e in E]) 
                     (point (remove_edges E) g_in g_out)) : Hy.
        by case => [][-> ->]. 
    * exact: (@par2_injR (edges2 [seq strip e | e in E]) 
                         (point (remove_edges E) g_in g_out)).
  - rewrite /f/g=>x/=. case def_y : (repr x) => [y|y].
    * rewrite -[x]reprK def_y. symmetry. apply/eqquotP => /=. 
      destruct y => //=; solve [exact: par2_eqv_oo|exact: par2_eqv_ii].
    * by rewrite -def_y reprK. 
  - rewrite /h/k=>e/=. 
    case: {-}_ / boolP => p //. 
      by rewrite /cast_ord /tnth nth_index //= ?mem_enum.
  - rewrite /h/k. case => [i|e]/=. 
    * case: {-}_/ boolP => p //.
      -- move: (h_proof _ _) => A. 
         congr inl. apply: val_inj => /=. 
         rewrite /tnth index_uniq //. exact: enum_uniq.
      -- case: notF. by rewrite -mem_enum mem_tnth in p. 
    * rewrite /h. case: {-}_/ boolP => p //.
      -- case:notF. by rewrite (negbTE (valP e)) in p.
      -- congr inr. exact: val_inj.
  - move => e /=. rewrite /h. case: {-}_ / boolP => p //. split. 
    * symmetry. apply/eqquotP => /=. move: (h_proof _ _) => He. 
      rewrite tnth_map_in ?mem_enum //. 
      move: p. rewrite inE /strip. case: ifP => /= [A _|A B].
      + apply: par2_eqv_ii => //. by rewrite (edges_st A). 
      + apply: par2_eqv_oo => //. by rewrite (edges_st B).
    * symmetry. apply/eqquotP => /=. move: (h_proof _ _) => He. 
      rewrite tnth_map_in ?mem_enum //. 
      move: p. rewrite inE /strip. case: ifP => /= [A _|A B].
      + apply: par2_eqv_oo => //. by rewrite (edges_st A). 
      + apply: par2_eqv_ii => //. by rewrite (edges_st B).
    * rewrite tnth_map_in ?mem_enum // /strip. by case: ifP.
  - rewrite /= /f. symmetry. apply/eqquotP => /=. 
    exact: par2_eqv_ii.
  - rewrite /= /f. symmetry. apply/eqquotP => /=. 
    exact: par2_eqv_oo.
Qed.

Lemma split_pip (G : graph2) : 
  connected [set: skeleton G] -> g_in != g_out :> G ->
  G ≈ @bgraph G IO g_in · (@igraph G g_in g_out · @bgraph G IO g_out).
Proof.
  move=> G_conn Eio. symmetry.
  setoid_rewrite (dot2_alt (igraph g_in g_out)).
  setoid_rewrite dot2_alt. set G' := dot2' _ _.
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
  have sintv_node (x : G) : x \notin @bag G IO g_in ->
                              x \notin @bag G IO g_out ->
                              x \in @sinterval G g_in g_out.
  { move=> /negbTE Npi /negbTE Npo. have : x \in [set: G] by [].
      by rewrite (sinterval_bag_cover G_conn Eio) !in_setU Npi Npo orbF. }
  have intv_node (x : G) : x \in @sinterval G g_in g_out ->
                                 x \in  @interval G g_in g_out.
  { by rewrite [x \in @interval G _ _]inE => ->. }
  pose g (x : G) : G' :=
    match boolP (x \in @bag G IO g_in), boolP (x \in @bag G IO g_out) with
    | AltTrue pi, _ => \pi (inl (Sub x pi))
    | _, AltTrue po => \pi (inr (\pi (inr (Sub x po))))
    | AltFalse Npi, AltFalse Npo =>
      let pintv := intv_node x (sintv_node x Npi Npo) in
      \pi (inr (\pi (inl (Sub x pintv))))
    end.

  have intv_edge (e : edge G) :
    e \notin edge_set (@bag G IO g_in) -> e \notin edge_set (@bag G IO g_out) ->
    e \in @interval_edges G g_in g_out.
  { move=> /negbTE Npi /negbTE Npo. have : e \in [set: edge G] by [].
      by rewrite (interval_bag_edge_cover G_conn Eio) !in_setU Npi Npo orbF. }
  pose k (e : edge G) : edge G' :=
    match boolP (e \in edge_set (@bag G IO g_in)),
          boolP (e \in edge_set (@bag G IO g_out)) with
    | AltTrue pi, _ => inl (Sub e pi)
    | _, AltTrue po => inr (inr (Sub e po))
    | AltFalse Npi, AltFalse Npo =>
      let pintv := intv_edge e Npi Npo in inr (inl (Sub e pintv))
    end.
      
  pose valE := f_equal val. pose injL := dot2_injL. pose injR := dot2_injR.
  pose inLR := dot2_LR. pose inRL := fun e => dot2_LR (esym e).

  apply Iso2'' with f g h k. 

  - rewrite /f/g => x.
    case Ex: (repr x) => [y|y]; last case Ey: (repr y) => [z|z].
    * have y_pi : val y \in @bag G IO g_in := valP y.
      rewrite /g. case: {-}_ / boolP => [?|H]; last by have := H; rewrite {1}y_pi.
      rewrite -[x]reprK Ex. congr (\pi (inl _)). exact: val_inj.
    * have : val z \in @interval G g_in g_out := valP z.
      rewrite 4!inE -orbA => /or3P[/eqP|/eqP|] Hz.
      -- rewrite Hz /g. case: {-}_ / boolP=> H; last first.
           by have := H; rewrite ?{1}(@bag_id G IO g_in).
         rewrite -[x]reprK Ex. apply/eqquotP.
         rewrite /=/dot2_eqv -[_ == inr y]/false.
         rewrite eqEcard subUset !sub1set !inE sum_eqE !cards2.
         rewrite -![inl _ == inr _]/false -![inr _ == inl _]/false.
         rewrite -(inj_eq val_inj) eqxx sum_eqE andbT -[y]reprK Ey.
         apply/eqP. apply/eqquotP.
         by rewrite /=/dot2_eqv sum_eqE -(inj_eq val_inj) Hz eqxx.
      -- rewrite Hz /g. have : g_out \in @bag G IO g_out by exact: bag_id.
         move=> /(disjointFl(bag_disj G_conn(CP_extensive _)(CP_extensive _)Eio)).
         rewrite 6!inE 2!eqxx orbT => /(_ _ _)/Wrap[]// o_pi.
         case: {-}_ / boolP=> Hi; first by have := Hi; rewrite {1}o_pi.
         case: {-}_ / boolP=> Ho; last first.
           by have := Ho; rewrite ?{1}(@bag_id G IO g_out).
         rewrite -[x]reprK Ex -[y]reprK Ey. congr (\pi (inr _)). apply/eqquotP.
         rewrite /=/dot2_eqv -[_ == inl z]/false.
         rewrite eqEcard subUset !sub1set !inE sum_eqE !cards2.
         rewrite -![inl _ == inr _]/false -![inr _ == inl _]/false.
         rewrite -(inj_eq val_inj) eqxx sum_eqE andbT orbF.
         apply/eqP. exact: val_inj.
      -- rewrite /g.
         have piF : val z \in @bag G IO g_in = false.
         { apply: disjointFl Hz. apply: interval_bag_disj.
           apply: CP_extensive. by rewrite !inE eqxx. }
         case: {-}_ / boolP => pi; first by have := pi; rewrite {1}piF.
         have poF : val z \in @bag G IO g_out = false.
         { apply: disjointFl Hz. rewrite sinterval_sym. apply: interval_bag_disj.
           apply: CP_extensive. by rewrite !inE eqxx. }
         case: {-}_ / boolP => po; first by have := po; rewrite {1}poF.
         rewrite -[x]reprK Ex -[y]reprK Ey. congr (\pi (inr (\pi (inl _)))).
         exact: val_inj.
    * have y_po : val z \in @bag G IO g_out := valP z.
      have := disjointFl(bag_disj G_conn(CP_extensive _)(CP_extensive _)Eio)y_po.
      rewrite !inE !eqxx orbT => /(_ _ _)/Wrap[]// y_pi.
      rewrite /g. case: {-}_ / boolP => H1; first by have := H1; rewrite {1}y_pi.
      case: {-}_ / boolP => H2; last by have := H2; rewrite {1}y_po.
      rewrite -[x]reprK Ex -[y]reprK Ey. congr (\pi (inr (\pi (inr _)))).
      exact: val_inj.

  - rewrite /f/g=>x. case: {-}_ / boolP => H1; last case: {-}_ / boolP => H2.
    * case: piP => -[y /injL/valE<-//|y /inLR[/valE]].
      rewrite SubK =>->{y}->. by case: piP => -[y /injL<-|y /inLR[/valE?->]].
    * case: piP => -[y /inRL[->]/inRL[/valE?/valE/=->]//|y /injR<-{y}].
        by case: piP => -[y /inRL[->]/valE|y /injR<-].
    * case: piP => -[y /inRL[->]/injL/valE//|y /injR<-{y}].
        by case: piP => -[y /injL<-|y /inLR[/valE?->]].

  - rewrite /h/k. case => [e|[e|e]].
    + have He : val e \in edge_set (@bag G IO g_in) := valP e.
      case: {-}_ / boolP => H1; last by have := H1; rewrite {1}He.
      congr inl. exact: val_inj.
    + have He : val e \in @interval_edges G g_in g_out := valP e.
      case: {-}_ / boolP => H1.
      { case: (disjointE (interval_bag_edges_disj _ _ _) H1 He) => //;
        by apply: CP_extensive; rewrite !inE eqxx. }
      rewrite {4}interval_edges_sym in He.
      case: {-}_ / boolP => H2.
      { case: (disjointE (interval_bag_edges_disj _ _ _) H2 He) => //;
        by apply: CP_extensive; rewrite !inE eqxx. }
      congr (inr (inl _)). exact: val_inj.
    + have He : val e \in edge_set (@bag G IO g_out) := valP e.
      case: {-}_ / boolP => H1.
      { case: (disjointE (bag_edges_disj _ _ _ Eio) H1 He) => //;
        by apply: CP_extensive; rewrite !inE eqxx. }
      case: {-}_ / boolP => H2; last by have := H2; rewrite {1}He.
      congr (inr (inr _)). exact: val_inj.
  - rewrite /h/k=>e. by repeat case: {-}_ / boolP => ?.

  - case=> [e|[e|e]]; rewrite /h; split=> //.
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
Qed.


Lemma componentless_top (G : graph2) : 
  g_in != g_out :> G -> @components G (~: IO) == set0 -> 
  point (@remove_edges G (edge_set IO)) g_in g_out ≈ top2.
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



Lemma edges2_graph_of (G : graph2) : 
  edges2 [seq strip e | e in @edges G g_in g_out :|: edges g_out g_in] ≈ 
  graph_of_term (\big[@tm_par _/@tm_top _]_(e in (@edges G g_in g_out :|: edges g_out g_in)) tm_ e).
Proof.
  setoid_rewrite edges2_big. rewrite big_map.
  setoid_rewrite graph_of_big_pars. rewrite -big_enum_in.
  set s := enum _. 
  apply: big_par_iso2.
  move => e. rewrite mem_enum /tm_ /strip inE. by case: (e \in edges g_in _). 
Qed.

Theorem term_of_iso (G : graph2) : 
  CK4F G -> G ≈ (graph_of_term (term_of G)).
Proof.
  elim: (wf_leq term_of_measure G) => {G} G _ IH CK4F_G.
  rewrite term_of_eq // /term_of_rec. 
  case: ifP => [C1|/negbT C1].
  - (* selfloops / io-redirect *)
    case: ifP => [C2|/negbT C2] /=.
    + case: pickP => [C HC|/(_ _) HC] /=.
      * setoid_rewrite (@split_component _ C) at 1 =>//.
        rewrite -?(eqP C1) ?setUid.
        have G_conn : connected [set: skeleton G] by case: CK4F_G.
        setoid_rewrite <-IH=>//.
        setoid_rewrite comp_dom2_redirect=>//. 
        -- exact: measure_redirect.
        -- exact: CK4F_redirect.
        -- move: HC. rewrite -[set1 g_in]setUid {2}(eqP C1).
           exact: measure_remove_component.
        -- exact: CK4F_remove_component.
        -- by rewrite -?(eqP C1) ?setUid.
      * have : @components G [set~ g_in] == set0.
        { rewrite -subset0. apply/subsetP => C. by rewrite HC. }
        exact: componentless_one.
    + setoid_rewrite split_io_edges at 1. set E := edges _ _ :|: edges _ _.
      have Eio : E = edge_set IO. by rewrite /E (eqP C1) !setUid edge_set1.
      rewrite -{1}Eio {2}Eio. apply: par2_iso2; first exact: edges2_graph_of.
      apply: IH; [exact: measure_remove_edges | exact: CK4F_remove_loops].
  - case: ifP => [C2|/negbT C2].
    + (* parallel split *)
      have EC := lens_sinterval (proj1 CK4F_G) C2.
      case: (boolP (_ == set0)) => C3.
      * case: pickP => [C HC|]. 
        -- rewrite EC in HC. setoid_rewrite (split_component _ HC) at 1=> //=.  
           apply: par2_iso2. 
           ++ apply IH; rewrite -EC in HC.
              exact: measure_lens. exact: CK4F_lens.
           ++ apply IH; rewrite -EC in HC. 
              exact: measure_lens_rest. exact: CK4F_lens_rest.
        -- have := split_K4_nontrivial C1 C2 _ CK4F_G. 
           rewrite edge_set_adj // => /(_ isT)/ltnW.
           move=>H H'. exfalso. move: H H'.  
           case/card_gt0P => C HC /(_ C). by rewrite HC.
      * rewrite EC.
        case: (boolP (_ == set0)) => C4 /=.
        -- setoid_rewrite split_io_edges at 1; rewrite -{2}lens_io_set //.
           setoid_rewrite componentless_top =>//.
           setoid_rewrite par2top=>//.
           rewrite lens_io_set//.
           exact: edges2_graph_of. 
        -- setoid_rewrite split_io_edges at 1. apply: par2_iso2. 
           ++ rewrite lens_io_set //. exact: edges2_graph_of.
           ++ setoid_rewrite <-IH; rewrite lens_io_set // -lens_io_set //. 
              exact: measure_remove_edges.
              rewrite -EC in C4. exact: CK4F_remove_edges.
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
        setoid_rewrite dot2A. repeat apply: dot2_iso2.
        -- apply IH=> //. exact: measure_split_cpL. exact: CK4F_split_cpL.
        -- suff ? : z \in @CP G IO. { apply IH => //; by apply rec_bag. }
           case/setDP : Hz => Hz _. apply/bigcupP; exists (g_in,g_out) => //. 
           by rewrite !inE !eqxx.
        -- apply IH=> //. exact: measure_split_cpR. exact: CK4F_split_cpR.
Qed.


Require Import subalgebra.

Corollary minor_exclusion_2p (G : graph2) :
  connected [set: skeleton G] -> 
  K4_free (sskeleton G) <-> 
  exists (T : forest) (B : T -> {set G}), [/\ sdecomp T (sskeleton G) B & width B <= 3].
Proof.
  move => conn_G. split => [K4F_G|[T [B [B1 B2 B3]]]].
  - have [T [B] [B1 B2]] := (graph_of_TW2 (term_of G)).
    have I := term_of_iso (conj conn_G K4F_G). symmetry in I. apply sskel_iso2 in I.
    have [D D1 D2] := decomp_iso B1 I.
    exists T. exists D. by rewrite D2.
  - exact: TW2_K4_free B1 B2 B3. 
Qed.

(** ** Graph Minor Theorem for TW2 *)

(** Remark: contrary to the textbook definition, we do not substract 1
in the definition of treewidth. Consequently, [width <= 3] means
treewidth two. *) 

Theorem graph_minor_TW2 (G : sgraph) :
  K4_free G <-> 
  exists (T : forest) (B : T -> {set G}), sdecomp T G B /\ width B <= 3.
Proof.
  split=> [| [T][B][]]; last exact: TW2_K4_free.
  move: G. apply: (nat_size_ind (f := fun G : sgraph => #|G|)).
  move => G IH K4F_G. 
  case: (boolP (connectedb [set: G])) => /connectedP conn_G.
  - case: (posnP #|G|) =>[G_empty | /card_gt0P[x _]].
    { exists tunit; exists (fun _ => [set: G]). split; first exact: triv_sdecomp.
      apply: leq_trans (width_bound _) _. by rewrite G_empty. }
    have [G' [iso_Gs iso_G]] := flesh_out x.
    have conn_G' : connected [set: skeleton G'].
    { exact: iso_connected conn_G. }
    have M := minor_exclusion_2p conn_G'.  
    have K4F_G' : K4_free (sskeleton G').
    { exact: iso_K4_free K4F_G. }
    case/M : K4F_G' => T [B] [B1 B2]. 
    case: (decomp_iso B1 iso_Gs) => D D1 D2. exists T. exists D. by rewrite D2.
  - case/disconnectedE : conn_G => x [y] [_ _]. 
    rewrite restrictE; last by move => ?;rewrite !inE. move => Hxy.
    pose V := [set z | connect sedge x z].
    pose G1 := sgraph.induced V.
    pose G2 := sgraph.induced (~:V).
    have G_iso : diso (sjoin G1 G2) G.
    { apply: ssplit_disconnected => a b. rewrite !inE => H1. apply: contraNN => H2.
      apply: connect_trans H1 _. exact: connect1. }
    have [T1 [B1 [dec1 W1]]] : 
      exists (T : forest) (B : T -> {set G1}), sdecomp T G1 B /\ width B <= 3.
    { apply: IH. 
      - rewrite card_sig. apply: (card_ltnT (x := y)) => /=. by rewrite inE.
      - apply: subgraph_K4_free K4F_G. exact: sgraph.induced_sub. }
    have [T2 [B2 [dec2 W2]]] : 
      exists (T : forest) (B : T -> {set G2}), sdecomp T G2 B /\ width B <= 3.
    { apply: IH. 
      - rewrite card_sig. apply: (card_ltnT (x := x)) => /=. 
        by rewrite !inE negbK connect0.
      - apply: subgraph_K4_free K4F_G. exact: sgraph.induced_sub. }
    exists (tjoin T1 T2). 
    pose B' := (decompU B1 B2).
    have dec' := join_decomp dec1 dec2.
    have [B dec W] := decomp_iso dec' G_iso.
    exists B. rewrite W. split => //. 
    apply: leq_trans (join_width _ _) _. by rewrite geq_max W1 W2.
Qed.

Print Assumptions graph_minor_TW2.
