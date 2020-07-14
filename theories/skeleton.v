Require Import Setoid Morphisms.

From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient bij preliminaries digraph sgraph treewidth minor checkpoint.
Require Import setoid_bigop structures mgraph mgraph2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 

(** * Skeletons *)

Section Skeleton.
Variables Lv Le : Type.
Notation graph := (graph Lv Le).

Definition adjacent (G : graph) (x y : G) :=
  [exists e, e \in edges x y :|: edges y x].

Lemma adjacent_sym (G : graph) : symmetric (@adjacent G).
Proof. move=> x y. by rewrite /adjacent setUC. Qed.

Lemma adjacentI (G : graph) (x y : G) (e : edge G) : e \in edges x y -> adjacent x y.
Proof. move=> He. apply/existsP. exists e. by rewrite inE He. Qed.

Arguments adjacentI [G x y] e _.

Lemma adjacent_edge (G : graph) (e : edge G) : adjacent (source e) (target e).
Proof. apply: (adjacentI e). by rewrite !inE. Qed.

(** The following lemma avoids the need for without loss of generality
reasoning (regarding the direction of the edge) when analyzing
[adjacent x y] *)
Lemma adjacentP (G : graph) (P : G -> G -> Prop) :
  Symmetric P ->
  (forall e : edge G, P (source e) (target e)) ->
  (forall x y : G,  adjacent x y -> P x y).
Proof.
  move=> S H x y. case/existsP=> e. rewrite !inE.
  case/orP=> /andP[/eqP<- /eqP<-] //. exact: S.
Qed.

Definition sk_rel (G : graph) := fun x y : G => (x != y) && adjacent x y.

Lemma sk_rel_sym (G : graph) : symmetric (@sk_rel G).
Proof. move=> x y. by rewrite /sk_rel/= eq_sym adjacent_sym. Qed.

Lemma sk_rel_irrefl (G : graph) : irreflexive (@sk_rel G).
Proof. move=> x. by rewrite /sk_rel/= eqxx. Qed.

Definition skeleton (G : graph) := 
  SGraph (@sk_rel_sym G) (@sk_rel_irrefl G).

Lemma skelP (G : graph) (P : G -> G -> Prop) : 
  Symmetric P -> 
  (forall e : edge G, source e != target e -> P (source e) (target e)) ->
  (forall x y : G,  sk_rel x y -> P x y).
Proof. 
  move => S H x y. case/andP=> xNy. case/existsP=> e He. move: He xNy. rewrite !inE.
  case/orP=> /andP[/eqP<- /eqP<-]; last rewrite eq_sym; move=> /H//. exact: S.
Qed.

End Skeleton.

Coercion skeleton : graph >-> sgraph.

Section SSkeleton.
Variables (Lv : comMonoid) (Le : elabelType).
Notation graph := (graph Lv Le).
Notation graph2 := (graph2 Lv Le).

(** Edges of skeletons of quotients *)
Lemma sk_rel_mergeE (G : graph) (e : equiv_rel G) x y :
  @sk_rel _ _ (merge G e) x y <-> 
  x != y /\ exists x0 y0 : skeleton G, [/\ \pi x0 = x, \pi y0 = y & x0 -- y0].
Proof.
  rewrite /= /sk_rel. 
  case: (boolP (x != y)) => //=; last by move => _; split => [|[]]. 
  move => xy; split.
  - move => A. split => //. move: xy. pattern x, y. apply adjacentP => //.
    + move => {x y A} x y H xy. 
      case: H => [|x0 [y0] [? ? /andP [E A]]]; first by rewrite eq_sym.
      exists y0; exists x0. by rewrite /edge_rel/=/sk_rel eq_sym adjacent_sym A E. 
    + move => e0. exists (@endpoint _ _ G false e0). exists (@endpoint _ _ G true e0).
      split => // ; last apply/andP;split => //. 
      * apply: contraNN xy => /eqP H. by rewrite eqmodE H.
      * apply/existsP; exists e0. by rewrite !inE !eqxx.
  - case => _ [x0] [y0] [Px Py /andP [Dxy0]]. case/existsP => [e0 E].
    wlog E : x0 y0 x y Dxy0 Px Py {xy E} / e0 \in edges x0 y0.
    { move => W. case/setUP : E; first exact: W. 
      rewrite adjacent_sym. apply: W => //. by rewrite eq_sym. }
    rewrite inE in E. case/andP : E => [E1 E2]. 
    apply/existsP; exists e0. by rewrite !inE /= (eqP E1) (eqP E2) Px Py !eqxx.
Qed.


Lemma hom_skel (G1 G2 : graph) (h: iso G1 G2) :
  forall x y, @edge_rel (skeleton G1) x y -> @edge_rel (skeleton G2) (h x) (h y).
Proof.
  apply skelP. 
  - move => x y. by rewrite sgP.
  - move => e He. rewrite /edge_rel/=/sk_rel. 
    rewrite bij_eq ?He //=. apply/existsP; exists (h.e e). 
    rewrite !inE !endpoint_iso /=.
    case (h.d e)=>/=; by rewrite !eqxx. 
Qed.

Instance skel_iso: CProper (iso ==> diso) (@skeleton Lv Le).
Proof.
  intros F G h. exists (iso_v h). apply: hom_skel. apply: (hom_skel (iso_sym h)).
Defined.
  
Lemma pi_hom (G : graph) (e : equiv_rel G) : 
  hom_s (pi e : skeleton G -> skeleton (merge G e)).
Proof.
  move => x y xy Dxy. apply/sk_rel_mergeE. split => //. by exists x; exists y.
Qed.
Arguments pi_hom [G] e.

(** ** Strong skeletons *)


Definition sskeleton (G : graph2) := @sgraph.add_edge (skeleton G) input output.

Lemma sskelP (G : graph2) (P : G -> G -> Prop) : 
  Symmetric P -> 
  (forall e : edge G, source e != target e -> P (source e) (target e)) ->
  (input != output :> G -> P input output) ->
  (forall x y : sskeleton G, x -- y -> P x y).
Proof. 
  move => S H IO x y. case/orP. exact: skelP. 
  case/orP => /= /and3P [A /eqP ? /eqP ?];subst; first exact: IO.
  apply: S. exact: IO.
Qed.

(* Note: The proof below is a bit obsucre due to the abbiguity of [x -- y] *)
Lemma skel_sub (G : graph2) : sgraph.subgraph (skeleton G) (sskeleton G).
Proof. exists id => //= x y H _. exact: subrelUl. Qed.


(** Isomorphim Lemmas *)

Lemma hom2_sskel (G1 G2 : graph2) (h: iso2 G1 G2) :
  forall x y, @edge_rel (sskeleton G1) x y -> @edge_rel (sskeleton G2) (h x) (h y).
Proof.
  (* TODO: reuse [hom_skel] above? *)
  apply sskelP.
  - move => x y. by rewrite sgP.
  - move => e He. rewrite /edge_rel /=  [_ -- _](_ : _ = true) /= /edge_rel //=. 
    rewrite /sk_rel /= bij_eq ?He //=. apply/existsP; exists (h.e e).
    rewrite !inE !endpoint_iso.
    case (h.d e)=>/=; by rewrite !eqxx. 
  - move => H. by rewrite /edge_rel /= bij_eq // H iso2_input iso2_output !eqxx.
Qed.

Instance sskel_iso2: CProper (iso2 ==> diso) sskeleton.
Proof.
  intros F G h. exists (iso_v h). exact: hom2_sskel. exact:(hom2_sskel (iso2_sym h)).
Defined.

Lemma decomp_iso2 (G1 G2 : graph2) (T : forest) B1 : 
  @sdecomp T (sskeleton G1) B1 -> G1 ≃2 G2 -> 
  exists2 B2, @sdecomp T (sskeleton G2) B2 & width B2 = width B1.
Proof.
  move => dec iso. apply: decomp_iso dec _. exact: sskel_iso2. 
Qed.


(** Bridging Lemmas *)

Lemma adjacent_induced (G : graph) (V : {set G}) (x y : induced V) :
  adjacent x y = adjacent (val x) (val y).
Proof.
  apply/existsP/existsP => -[e]; rewrite ?inE => He.
  - exists (val e). move: He. by rewrite !inE -!val_eqE.
  - suff eV : e \in edge_set V by exists (Sub e eV); rewrite !inE -!val_eqE.
    rewrite inE. case/orP: He => /andP[/eqP-> /eqP->]; apply/andP; split; exact: valP.
Qed.

Lemma edge_set_adj (G : graph2) (x y : G) : 
  @edge_set _ _ G [set x; y] == set0 -> ~~ @adjacent _ _ G x y. 
Proof. 
  apply: contraTN => /existsP[e]. rewrite !inE => He.
  apply/set0Pn. exists e. rewrite !inE.
  by case/orP: He => /andP[->->]; rewrite orbT.
Qed.

Lemma sskeleton_subgraph_for (G : graph2) (V : {set G}) (E : {set edge G})
  (con : consistent V E) (i o : sig [eta mem V]) : val i = input -> val o = output ->
  sgraph.subgraph (sskeleton (point (subgraph_for con) i o)) (sskeleton G).
Proof.
  rewrite {2}/sskeleton/= => <- <-.
  exists val; first exact: val_inj. 
  rewrite /hom_s. move => x y xy _. move: x y xy. apply sskelP.
  - move=> x y. by rewrite sg_sym.
  - move=> e sNt. apply/orP; left. apply/andP. split=> //. exact: adjacent_edge.
  - move=> /= iNo. by rewrite /edge_rel /= iNo !eqxx.
Qed.

Lemma sskeleton_adjacent (G : graph) (i o : G) :
  adjacent i o -> diso G (sskeleton (point G i o)).
Proof.
  move=> Aio.
  exists (bij_id: bij G (sskeleton (point G i o))) => /=. 
  by move=>x y; rewrite {2}/edge_rel/= => ->.
  rewrite /is_dhom. apply sskelP.
  - move=> x y. by rewrite sg_sym.
  - rewrite /edge_rel/=/sk_rel => e ->. exact: adjacent_edge.
  - by rewrite /edge_rel/=/sk_rel => ->.
Qed.

Lemma remove_edge_add (G : graph) (e : edge G) : 
  remove_edges [set e] ∔ [source e, elabel e, target e] ≃ G.
Proof.
  Iso bij_id (bijD1 e) xpred0. constructor => //.
  - by case => [f b|[|]].
  - by case => [f|] /=.
Defined.

Lemma remove_loops (G : graph) (E : {set edge G}) :
  {in E, forall e, source e = target e} ->
  diso G (remove_edges E).
Proof.
  move=> Eloops.
  have Esame x y : x != y -> @edges _ _ (remove_edges E) x y = val @^-1: @edges _ _ G x y.
  { move=> xNy. apply/setP=> e. by rewrite !inE. }
  exists (bij_id: bij G (remove_edges E)) => //= x y; rewrite /=/sk_rel => /andP[xNy].
  all: rewrite /edge_rel/=/sk_rel.
  all: rewrite xNy /adjacent/= !Esame // 1?eq_sym // -preimsetU.
  - case/existsP=> e He.
    suff H : e \notin E by apply/existsP; exists (Sub e H); rewrite inE.
    apply: contraNN xNy => /Eloops eq_e. move: He. rewrite !inE -eq_e.
    by case/orP=> /andP[/eqP<- /eqP<-].
  - case/existsP=> e. rewrite inE => He. apply/existsP. by exists (val e).
Qed.

Lemma remove_edges_connected (G : graph) (E : {set edge G}) :
  {in E, forall e : edge G, connect (@sk_rel _ _ (remove_edges E)) (source e) (target e)} ->
  connected [set: skeleton G] -> connected [set: skeleton (remove_edges E)].
Proof.
  move=> E_conn G_conn. apply: connectedTI => x y. have := connectedTE G_conn x y.
  apply: connect_sub x y. move=> /=. apply skelP.
  - by move=> x y; rewrite connect_symI //; exact: sk_rel_sym (remove_edges E).
  - move=> e sNt. case: (boolP (e \in E)) => [/E_conn//|He].
    apply: connect1. rewrite /sk_rel/= sNt /=.
    by apply/existsP; exists (Sub e He); rewrite !inE !eqxx.
Qed.

Lemma remove_edges_cross (G : graph) (V : {set G}) (E : {set edge G}) (x y : G) :
  E \subset edge_set V -> sk_rel x y -> y \notin V -> @sk_rel _ _ (remove_edges E) x y.
Proof.
  move=> E_subV xy yNV.
  have {yNV} : (x \notin V) || (y \notin V) by rewrite yNV.
  pattern x, y. revert x y xy.
  apply skelP ; first by move=> x y; rewrite orbC sk_rel_sym.
  move=> e sNt stNV. rewrite /sk_rel sNt /=.
  case: (boolP (e \in E)) => He; last first.
  - apply/existsP; exists (Sub e He); by rewrite !inE !eqxx.
  - move: He stNV => /(subsetP E_subV). rewrite inE. by case/andP=> -> ->.
Qed.

Lemma remove_edges_restrict (G : graph) (V : {set G}) (E : {set edge G}) (x y : G) :
  E \subset edge_set V -> connect (restrict (~: V) (@sk_rel _ _ G)) x y ->
  connect (@sk_rel _ _ (remove_edges E)) x y.
Proof.
  move=> E_subV. apply: connect_mono x y => x y /=. rewrite !inE -andbA.
  case/and3P=> xNV yNV xy. exact: remove_edges_cross xy yNV.
Qed.

Lemma sskeleton_remove_io (G : graph2) (E : {set edge G}) :
  E \subset @edge_set _ _ G IO ->
  diso (sskeleton (point (remove_edges E) input output)) (sskeleton G).
Proof.
  move=> E_subIO. 
  exists (bij_id: bij (sskeleton (point (remove_edges E) input output)) (sskeleton G)) => //.  
  all: rewrite /is_dhom; apply sskelP.
  - move=> x y. by rewrite sg_sym.
  - move=> e sNt. apply/orP; left. rewrite /edge_rel/=/sk_rel sNt /=. exact: adjacent_edge.
  - rewrite /edge_rel /= => ->. by rewrite !eqxx.
  - move=> x y. by rewrite sg_sym.
  - move=> e sNt /=. case: (boolP (e \in E)) => Ee; last first.
    + apply/orP; left. rewrite /edge_rel/=/sk_rel sNt /=. apply/existsP; exists (Sub e Ee).
      by rewrite !inE !eqxx.
    + move: Ee sNt => /(subsetP E_subIO). rewrite !inE /edge_rel/=.
      by case/andP=> /orP[]/eqP-> /orP[]/eqP->; rewrite !eqxx // eq_sym => ->.
  - rewrite /edge_rel/= => ->. by rewrite !eqxx.
Qed.

(** ** Interval and Bag Graphs *)

(** NOTE: for interval graphs, we need to remove self loops on the
ends, because these edges will be edges of the bag graph for the end
nodes. *)
Definition interval_edges (G : graph) (x y : G) :=
  edge_set (@interval G x y) :\: (edges x x :|: edges y y).

Lemma interval_edges_sym (G : graph) (x y : G) :
  interval_edges x y = interval_edges y x.
Proof. by rewrite /interval_edges interval_sym setUC. Qed.

Lemma igraph_proof (G : graph) (x y : skeleton G) :
  consistent (interval x y) (interval_edges x y).
Proof.
  move=> e. rewrite inE =>[b]. rewrite inE =>/andP [_ H].
  rewrite /edge_set in_set in H. move: H=>/andP[? ?]. by case b. 
Qed.

Definition igraph (G : graph) (x y : skeleton G) :=
  @point (subgraph_for (@igraph_proof G x y))
         (Sub x (intervalL x y))
         (Sub y (intervalR x y)).

Definition bgraph (G : graph) (U : {set G}) (x:G) :=
  @point (induced (@bag G U x))
         (Sub x (@bag_id G U x))
         (Sub x (@bag_id G U x)).

Lemma bgraph_eq_io (G : graph) (U : {set G}) (x : G) : input = output :> @bgraph G U x.
Proof. by []. Qed.

Lemma interval_bag_edges_disj (G : graph) (U : {set G}) (x y : G) :
  connected [set: skeleton G] -> x \in @CP (skeleton G) U -> y \in @CP (skeleton G) U ->
  [disjoint edge_set (@bag G U x) & @interval_edges G x y].
Proof.
  move=> G_conn x_cp y_cp. rewrite -setI_eq0 -subset0. apply/subsetP => e.
  rewrite 3!inE => /and3P[]/andP[src_p tgt_p].
  rewrite 4!inE ![_ \in @interval G _ _]inE (lock sinterval) !inE -lock.
  rewrite negb_or !negb_and -!orbA => /andP[eNx eNy].
  case/andP=> /or3P[src_x|src_y|src_sI] /or3P[tgt_x|tgt_y|tgt_sI].
  all: move: eNx eNy; rewrite ?src_x ?src_y ?tgt_x ?tgt_y ?orbF //= => eNx eNy.
  - move: eNx. by rewrite (eqP tgt_y) -(@bag_cp G _ U) // -(eqP tgt_y) tgt_p.
  - by case: (disjointE (@interval_bag_disj G U x y y_cp) tgt_p tgt_sI).
  - move: eNx. by rewrite (eqP src_y) -(@bag_cp G _ U) // -(eqP src_y) src_p.
  - by case: (disjointE (@interval_bag_disj G U x y y_cp) tgt_p tgt_sI).
  - by case: (disjointE (@interval_bag_disj G U x y y_cp) src_p src_sI).
  - by case: (disjointE (@interval_bag_disj G U x y y_cp) src_p src_sI).
  - by case: (disjointE (@interval_bag_disj G U x y y_cp) src_p src_sI).
Qed.

Lemma bag_edges_disj (G : graph) (U : {set G}) (x y : G) :
  connected [set: skeleton G] -> x \in @CP G U -> y \in @CP G U -> x != y ->
  [disjoint edge_set (@bag G U x) & edge_set (@bag G U y)].
Proof.
  move=> G_conn x_cp y_cp xNy. rewrite -setI_eq0 -subset0. apply/subsetP => e.
  rewrite 3!inE. case/andP=> /andP[src_x tgt_x] /andP[src_y tgt_y].
  by case: (disjointE (@bag_disj G _ U x y _ _ _) src_x src_y).
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

Lemma interval_bag_edge_cover (G : graph) (x y : G) :
  connected [set: skeleton G] -> x != y ->
  [set: edge G] = edge_set (@bag G [set x; y] x) :|: 
                  @interval_edges G x y :|: 
                  edge_set (@bag G [set x; y] y).
Proof.
  move=> G_conn xNy. apply/eqP. rewrite eq_sym -subTset. apply/subsetP=> e _.
  move: (sinterval_bag_cover G_conn xNy) => compU.
  have : target e \in [set: G] by []. have : source e \in [set: G] by [].
  rewrite !{}compU !in_setU -!orbA.
  case: (boolP (source e \in @sinterval G x y)) => [Hsrc _|Nsrc /= Hsrc].
  + case: (boolP (target e \in @sinterval G x y)) => [Htgt _|Ntgt /= Htgt].
    { rewrite ![e \in _]inE ![_ \in @interval G _ _]inE Hsrc Htgt.
      rewrite !orbT negb_or !negb_and.
      suff [-> ->] : source e != x /\ source e != y by [].
      by split; apply: contraTneq Hsrc => ->; rewrite (@sinterval_bounds G). }
    wlog Htgt : x y xNy Hsrc Ntgt {Htgt} / target e \in @bag G [set x; y] x.
    { move=> Hyp. case/orP: Htgt; first exact: Hyp.
      rewrite setUC orbC orbAC orbC interval_edges_sym.
      apply: Hyp; rewrite 1?sinterval_sym //. by rewrite eq_sym. }
    have Nsrc : source e \notin @bag G [set x; y] x.
    { rewrite (disjointFl (@interval_bag_disj G _ x y _) Hsrc) //.
      apply: CP_extensive. by rewrite !inE eqxx. }
    have src_tgt : @sedge G (target e) (source e).
    { rewrite /=/sk_rel adjacent_sym adjacent_edge andbT.
      by apply: contraNneq Ntgt =>->. }
    have : target e = x := bag_exit_edge G_conn _ Htgt Nsrc src_tgt.
    move/(_ (CP_extensive _)). rewrite 3!inE eqxx => /(_ _)/Wrap[]// tgt_x.
    rewrite ![e \in _]inE tgt_x (@intervalL G) [_ \in @interval G _ _]inE Hsrc.
    rewrite orbT !andbT negb_or !negb_and.
    suff [->->] : source e != x /\ source e != y by [].
    by split; apply: contraTneq Hsrc =>->; rewrite (@sinterval_bounds G).
  + wlog Hsrc : x y xNy {Nsrc Hsrc} / source e \in @bag G [set x; y] x.
    { move=> Hyp. case/orP: Hsrc; first exact: Hyp.
      rewrite setUC sinterval_sym interval_edges_sym orbC orbAC orbC.
      rewrite [(e \in _) || _]orbC orbAC [_ || (e \in _)]orbC.
      by apply: Hyp; rewrite eq_sym. }
    case: (boolP (target e \in @bag G [set x; y] x)) => Ntgt /=.
      by rewrite [e \in _]inE Hsrc Ntgt.
    have src_tgt : @sedge G (source e) (target e).
    { rewrite /=/sk_rel adjacent_edge andbT. by apply: contraNneq Ntgt =><-. }
    have : source e = x := bag_exit_edge G_conn _ Hsrc Ntgt src_tgt.
    move/(_ (CP_extensive _)). rewrite 3!inE eqxx => /(_ _)/Wrap[]// src_x.
    case/orP=> Htgt.
    * rewrite ![e \in _]inE src_x (@intervalL G) (negbTE xNy) orbF eqxx/=.
      have -> : target e != x.
      { apply: contraTneq Htgt =>->. by rewrite (@sinterval_bounds G). }
      by have -> : target e \in @interval G x y by rewrite inE Htgt.
    * have Nsrc : source e \notin @bag G [set x; y] y.
      { have yNx : y != x by rewrite eq_sym.
        rewrite (disjointFl (bag_disj G_conn _ _ yNx) Hsrc) //;
        by apply: CP_extensive; rewrite !inE eqxx. }
      have := bag_exit_edge G_conn (CP_extensive _) Htgt Nsrc _.
      rewrite sg_sym 3!inE eqxx => /(_ _ src_tgt)/Wrap[]// tgt_y.
      rewrite ![e \in _]inE src_x tgt_y (@intervalL G) (@intervalR G).
      by rewrite !eqxx eq_sym (negbTE xNy).
Qed.

Lemma interval_cp_edge_cover (G : graph) (x y z : G) :
  connected [set: skeleton G] -> z \in @cp G x y :\: [set x; y] ->
  @interval_edges G x y = @interval_edges G x z :|: 
                          edge_set (@bag G [set x; y] z) :|: 
                          @interval_edges G z y.
Proof.
  move=> G_conn zPcpxy.
  have z_cpxy : z \in @cp G x y by move: z zPcpxy; apply/subsetP; exact: subsetDl.
  have z_cp : z \in @CP G [set x; y].
  { apply/bigcupP; exists (x, y); by [rewrite in_setX !in_set2 !eqxx |]. }
  have [x_cp y_cp] : x \in @CP G [set x; y] /\ y \in @CP G [set x; y]
    by split; apply: CP_extensive; rewrite !inE eqxx.
  apply/eqP. rewrite eqEsubset andbC !subUset [(_ \subset _) && _ && _]andbAC.
  apply/andP; split; first (apply/andP; split).
  - wlog suff : x y z zPcpxy {z_cpxy x_cp y_cp z_cp} /
                  interval_edges x z \subset interval_edges x y.
    { move=> Hyp. rewrite (Hyp x y z zPcpxy) /=.
      by rewrite interval_edges_sym (interval_edges_sym x) Hyp 1?cp_sym 1?setUC. }
    move: zPcpxy. rewrite in_setD in_set2 negb_or => /andP[]/andP[zNx zNy] z_cpxy.
    apply/subsetP=> e. rewrite ![e \in _]inE !negb_or.
    case/and3P=> /andP[eNx eNz] Hsrc Htgt. rewrite eNx /=.
    have -> : source e \in @interval G x y.
    { move: Hsrc. rewrite !in_setU !in_set1 -orbA.
      case/or3P=> [->//|/eqP->|/(subsetP (sinterval_sub G_conn z_cpxy))->//].
      move: z_cpxy => /(subsetP (cp_sub_interval G_conn _ _)).
      by rewrite !in_setU !in_set1. }
    have -> : target e \in @interval G x y.
    { move: Htgt. rewrite !in_setU !in_set1 -orbA.
      case/or3P=> [->//|/eqP->|/(subsetP (sinterval_sub G_conn z_cpxy))->//].
      move: z_cpxy => /(subsetP (cp_sub_interval G_conn _ _)).
      by rewrite !in_setU !in_set1. }
    rewrite /= andbT.
    suff : y \notin @interval G x z by apply: contraNN => /andP[/eqP<-].
    rewrite in_setU in_set2 [_ == z]eq_sym (negbTE zNy) orbF negb_or.
    apply/andP; split; first by apply: contraTneq z_cpxy =>->; rewrite cpxx inE.
    by rewrite inE negb_and !negbK (@cp_sym G y x) z_cpxy.
  - apply/subsetP=> e. rewrite ![e \in _]inE negb_or.
    have /subsetP PsubI := bag_sub_sinterval G_conn x_cp y_cp zPcpxy.
    case/andP=> /PsubI Hsrc /PsubI Htgt.
    rewrite ![_ \in @interval G x y]inE Hsrc Htgt !orbT /= andbT.
    apply/andP; split; apply: contraTN Hsrc => /andP[/eqP<-];
    by rewrite sinterval_bounds.
  - apply/subsetP=> e.
    rewrite in_setD andbC !in_setU inE (interval_cp_cover G_conn zPcpxy).
    rewrite negb_or 2!in_setU 2!(in_setU (target e)) => /andP[]/andP[].
    rewrite [(_ \in _) || _]orbC -2!orbA. case/orP=> Hsrc Htgt.
    + wlog Htgt : x y z zPcpxy Hsrc x_cp y_cp z_cp {z_cpxy Htgt} /
          (target e \in @bag G [set x; y] z) || (target e \in x |: @sinterval G x z).
      { case/or3P: Htgt => /= Htgt Hyp.
        * apply: Hyp => //; by rewrite Htgt.
        * apply: Hyp => //; by rewrite Htgt.
        * rewrite andbC orbC orbCA orbC setUC (interval_edges_sym x)interval_edges_sym.
          by apply: Hyp; rewrite setUC 1?cp_sym // sinterval_sym Htgt. }
      case/orP: Htgt => Htgt _; first by rewrite ![e \in _]inE Hsrc Htgt.
      case: (altP (source e =P target e)) => He.
        by rewrite ![e \in _]inE -He Hsrc.
      have src_tgt : @sedge G (source e) (target e).
      { by rewrite /=/sk_rel He adjacent_edge. }
      have zNx : z != x by move: zPcpxy; rewrite !inE negb_or -andbA => /and3P[].
      have Ntgt : target e \notin @bag G [set x; y] z.
      { move: Htgt; rewrite sinterval_sym in_setU1.
        case/orP=> [/eqP->|Htgt]; last first.
          by rewrite (disjointFl (interval_bag_disj _ x_cp) Htgt).
        apply/bagPn. exists x; by [|rewrite cpxx inE]. }
      move/cpP/(_ (edgep src_tgt)): (bag_exit G_conn z_cp Hsrc Ntgt).
      rewrite mem_edgep orbC. have /negbTE->/= : z != target e
        by apply: contraNneq Ntgt =><-; rewrite (@bag_id G).
      move=> /eqP Esrc. rewrite ![e \in _]inE -Esrc eqxx (negbTE zNx) /=.
      rewrite {1}Esrc eq_sym He (@intervalR G) in_setU in_set2.
      by move: Htgt; rewrite in_setU1; case/orP=>->.
    + wlog Hsrc : x y z zPcpxy x_cp y_cp z_cp Htgt z_cpxy {Hsrc} /
          source e \in x |: @sinterval G x z.
      { case/orP: Hsrc => /= Hsrc; first by [apply]; move=> Hyp.
        rewrite andbC orbC orbCA orbC setUC (interval_edges_sym x) interval_edges_sym.
        apply: Hyp; rewrite 1?[_ |: set1 _]setUC 1?cp_sym //.
        * by rewrite orbC orbAC orbC (@sinterval_sym G y) sinterval_sym.
        * by rewrite sinterval_sym. }
      case/or3P: Htgt => Htgt.
      * case/andP=> eNx _. rewrite 2!inE negb_or eNx 2!inE negb_and.
        have ->/= : source e != z.
        { apply: contraTneq Hsrc => ->.
          rewrite in_setU1 (@sinterval_bounds G) orbF.
          move: zPcpxy; rewrite in_setD in_set2 negb_or; by case/andP=> /andP[]. }
        have -> : source e \in @interval G x z.
        { by move: Hsrc; rewrite !in_setU !in_set1 => /orP[]->. }
        suff -> : target e \in @interval G x z by [].
        by move: Htgt; rewrite !in_setU !in_set1 => /orP[]->.
      * case: (altP (source e =P target e)) => He _.
          by rewrite ![e \in _]inE He Htgt.
        have tgt_src : @sedge G (target e) (source e).
        { by rewrite /=/sk_rel eq_sym He adjacent_sym adjacent_edge. }
        have zNx : z != x by move: zPcpxy; rewrite !inE negb_or -andbA => /and3P[].
        have Nsrc : source e \notin @bag G [set x; y] z.
        { move: Hsrc; rewrite sinterval_sym in_setU1.
          case/orP=> [/eqP->|Hsrc]; last first.
            by rewrite (disjointFl (interval_bag_disj _ x_cp) Hsrc).
          apply/bagPn. exists x; by [|rewrite cpxx inE]. }
        move/cpP/(_ (edgep tgt_src)): (bag_exit G_conn z_cp Htgt Nsrc).
        rewrite mem_edgep orbC. have /negbTE->/= : z != source e
          by apply: contraNneq Nsrc =><-; rewrite (@bag_id G).
        move=> /eqP Etgt. rewrite ![e \in _]inE -Etgt eqxx (negbTE zNx) andbF andbT /=.
        rewrite {1}Etgt He (@intervalR G) in_setU in_set2.
        by move: Hsrc; rewrite in_setU1; case/orP=>->.
      * case: (altP (source e =P target e)) Hsrc Htgt => [<-|He Hsrc Htgt].
        { rewrite !in_setU1; case/orP=> [/eqP->|Hsrc].
          - rewrite inE z_cpxy /= orbF => /eqP Exy.
            move: zPcpxy. by rewrite -Exy cpxx setUid setDv inE.
          - rewrite (disjointFr (sinterval_disj_cp z_cpxy) Hsrc) orbF => /eqP Htgt.
            move: Hsrc. by rewrite Htgt inE (@cp_sym G y x) z_cpxy andbF. }
        have {He} He : @sedge G (source e) (target e).
        { by rewrite /=/sk_rel He adjacent_edge. }
        have [/negbTE srcNz /negbTE tgtNz] : source e != z /\ target e != z.
        { split; [apply: contraTneq Hsrc|apply: contraTneq Htgt]=>->.
          all: rewrite in_setU1 negb_or inE mem_cpl ?andbF andbT.
          all: move: zPcpxy; by rewrite !inE negb_or -andbA =>/and3P[]. }
        have {Hsrc} Hsrc : source e \in @interval G x z.
        { move: Hsrc; rewrite /interval !in_setU !in_set1 => /orP[/eqP->|->//].
          by rewrite eqxx. }
        have {Htgt} Htgt : target e \in @interval G z y.
        { move: Htgt; rewrite /interval !in_setU !in_set1 => /orP[/eqP->|->//].
          by rewrite eqxx. }
        have := interval_edge_cp z_cpxy He Hsrc Htgt. by rewrite srcNz tgtNz.
Qed.

Lemma has_edge (G : graph) (x y : G) : 
  connected [set: skeleton G] -> x != y -> 0 < #|edge G|.
Proof.
  move/connectedTE/(_ x y). case/connect_irredP => p _ xy. 
  case: (splitL p xy) => x' [/= xx'] _. apply/card_gt0P.
  case/andP: xx' => _. case/existsP=> e _. by exists e.
Qed.

(* Is this the most general type? *)
Lemma card_val (T : finType) (P : pred T) (s : subFinType P) (A : pred s) : 
  #|val @: A| = #|A|.
Proof. rewrite card_imset //. exact: val_inj. Qed.

(* lifting connectedness from the skeleton *)
Lemma connected_skeleton' (G : graph) V E (con : @consistent _ _ G V E) :
  forall U : {set subgraph_for con}, @connected (skeleton G) (val @: U) ->
  (forall e, e \in edge_set (val @: U) -> source e != target e ->
             let x := source e in let y := target e in
             exists2 e, e \in E & (e \in edges x y) || (e \in edges y x)) ->
  @connected (skeleton (subgraph_for con)) U.
Proof.
  move => U. set U' := val @: U => conn_U all_edges x y x_U y_U.
  case/connectP: (conn_U _ _ (mem_imset val x_U) (mem_imset val y_U)) => p.
  elim: p x x_U => [|a p IH] x x_U; first by move=> _ /val_inj <-; exact: connect0.
  rewrite (lock edge_rel) /= -!andbA -lock. case/and4P=> _ a_U' xa.
  have Ha : a \in V by case/imsetP: a_U' => b _ ->; exact: valP.
  set b : subgraph_for con := Sub a Ha. rewrite -[a]/(val b) => p_path p_last.
  have b_U : b \in U by rewrite -(inj_imset _  _ val_inj).
  apply: connect_trans (IH b b_U p_path p_last). apply: connect1 => /=.
  apply/andP; split; first by apply/andP; split. move: xa.

  rewrite -[a]/(val b).
  move: b x b_U x_U {p_last p_path a_U' IH p} => {a Ha} b x b_U x_U.
  rewrite /edge_rel/=/sk_rel -val_eqE. case/andP=> xNb. rewrite xNb /= => adjv_xb.
  wlog [e0] : b x b_U x_U xNb {adjv_xb} / exists e, e \in edges (val x) (val b).
  { move=> Hyp. case/existsP: adjv_xb => e. rewrite inE => /orP[]He.
    - by apply: Hyp => //; exists e.
    - rewrite adjacent_sym. apply: Hyp => //; by [rewrite eq_sym | exists e]. }
  rewrite inE. case/andP=> /eqP Hsrc /eqP Htgt.
  have Ne0 : source e0 != target e0 by rewrite Hsrc Htgt.
  have : e0 \in edge_set U' by rewrite inE Hsrc Htgt !mem_imset.
  case/all_edges=> [//|] e' Ee'. rewrite Hsrc Htgt => He'.
  set e : edge (subgraph_for con) := Sub e' Ee'.
  have He : e \in edges x b :|: edges b x.
  { move: He'. by rewrite !inE -[e']/(val e) -!(inj_eq val_inj). }
  apply/existsP. by exists e.
Qed.

Lemma connected_skeleton (G : graph) V E (con : @consistent _ _ G V E) :
  forall U : {set subgraph_for con}, @connected (skeleton G) (val @: U) ->
  (forall e, e \in edge_set (val @: U) -> source e != target e -> e \in E) ->
  @connected (skeleton (subgraph_for con)) U.
Proof.
  move=> U conn_U all_edges. apply: connected_skeleton' conn_U _.
  move=> e E1 E2; exists e; rewrite ?inE ?eqxx //. exact: all_edges.
Qed.

Lemma connected_bgraph (G : graph2) (U : {set G}) (x : G) : 
  connected [set: skeleton G] -> x \in @CP (skeleton G) U -> 
  connected [set: skeleton (bgraph U x)].
Proof.
  move => conn_G cp_x.
  apply: connected_skeleton; rewrite imset_valT memKset //. exact: connected_bag.
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
  diso (sskeleton (point _ x x)) (skeleton G).
Proof.
  exists (bij_id : bij (sskeleton (point G x x)) (skeleton G)) => u v /=.
  - case/or3P => // /and3P[uNv /eqP eq1 /eqP eq2];
    move: uNv; by rewrite eq1 eq2 eqxx.
  - by rewrite {2}/edge_rel/= => ->.
Qed.

Lemma sub_pointxx (G : graph) (x:G) :
  sgraph.subgraph (sskeleton (point _ x x))
                  (skeleton G).
Proof. apply: iso_subgraph; exact: iso_pointxx. Qed.

(* The subgraph relation lifts to skeletons *)
Lemma sub_sub (G H : graph) : 
  subgraph G H -> sgraph.subgraph G H.
Proof.
  case => hv [he] [hd] [hom] [inj_hv inj_he].
  exists hv => // x y xy _. move: x y xy. 
  apply skelP; first by move=> x y; rewrite sg_sym.
  move=> e sNt. (* by *) rewrite /edge_rel/=/sk_rel (inj_eq inj_hv) sNt.
  generalize (endpoint_ihom (is_ihom:=hom) e false).
  generalize (endpoint_ihom (is_ihom:=hom) e true).
  case (hd e)=>/= <- <-.
  by rewrite adjacent_sym adjacent_edge. 
  by apply adjacent_edge. 
Qed.

Definition flesh_out_graph (G : sgraph) sym0 tt (z : G) : graph2 :=
  {| graph_of :=
       {| vertex := G ; edge := [finType of { p : G * G | p.1 -- p.2 }];(* TODO: avoid clones? *)
          endpoint b e := if b then snd (val e) else (val e).1;
          vlabel _ := tt;
          elabel := fun _ => sym0 |} ;
     input := z; output := z |}.

Lemma flesh_out (G : sgraph) (sym0 : Le) (tt: Lv) (z : G) :
  { G' & (diso (sskeleton G') G * diso (skeleton G') G)%type}.
Proof.
  pose G' := flesh_out_graph sym0 tt z. exists G'.
  suff iso : diso (skeleton G') G.
  { split=> //. rewrite <-iso. exact: iso_pointxx. }
  exists (bij_id : bij (skeleton G') G) => x y; rewrite /sk_rel.
  - case/andP=> _ /existsP[][/=][u v /=] uv. rewrite !inE /=.
    case/orP=> /andP[/eqP<- /eqP<-] //; by rewrite sg_sym.
  - move=> xy. rewrite /edge_rel/=/sk_rel sg_edgeNeq //=.
    apply/existsP; exists (Sub (x, y) xy). by rewrite !inE !eqxx.
Qed.


(** ** Disjoint Union of a connected component and the remainder of the graph *)

Lemma edge_component (G : graph) (e : edge G) :
  @component_of G (source e) = @component_of G (target e).
Proof. 
  case: (altP (source e =P target e)) => [->//|sDt].
  apply: same_pblock => //. apply/components_pblockP.
  have st : (source e : skeleton G) -- (target e) . 
  { by rewrite /edge_rel/=/sk_rel sDt adjacent_edge. }
  by exists (prev (edgep st)). 
Qed.
Opaque merge.

Arguments unl [Lv Le G H] x : simpl never.
Arguments unr [Lv Le G H] x : simpl never.

Lemma edge_set_component (G : graph) (C : {set skeleton G}) (e : edge G) : 
  C \in @components G [set: G] -> (source e \in C) = (target e \in C).
Proof.
  move => comp_C. apply/idP/idP.
  - move => inC. rewrite (mem_component comp_C inC). 
    by rewrite edge_component (@in_component_of G).
  - move => inC. rewrite (mem_component comp_C inC). 
    by rewrite -edge_component (@in_component_of G).
Qed.
Arguments edge_set_component [G C e].

(* if C is a component, this becomes an equivalence *)
Lemma edge_setN (G : graph) (C : {set G}) (e : edge G):
  e \in edge_set C -> e \notin edge_set (~: C).
Proof. rewrite !inE. by case/andP => -> ->. Qed.

Lemma edge_comp (G : graph) (C : {set G}) (e : edge G):
  C \in components [set: skeleton G] ->
  (e \in edge_set C) + (e \in edge_set (~: C))%type.
Proof. 
  move => comp_C. case: (boolP (source e \in C)) => p; [left|right].
  - by rewrite inE -(edge_set_component comp_C) p.
  - by rewrite !inE -(edge_set_component comp_C) p.
Qed.

Section IsoComponents.
Variables (G : graph) (C : {set G}).
(* TODO: suffices that there is no edge between [C] and [~:C] *)
Hypothesis comp_C : C \in components [set: skeleton G].
Let G1 := induced C.
Let G2 := induced (~: C).

Lemma decC z : (z \in C) + (z \in ~: C)%type. 
Proof. case: (boolP (z \in C)) => p; [by left|right]. by rewrite inE p. Qed.

Lemma decE (e : edge G) : (e \in edge_set C) + (e \in edge_set (~: C)).
Proof. exact: edge_comp. Qed.

Definition component_v (x : union G1 G2) := match x with inl x => val x | inr x => val x end.
Definition component_v' (z : G) : union G1 G2 := 
    match decC z with inl p => inl (Sub z p) | inr p => inr (Sub z p) end.

Definition component_e (e : edge (union G1 G2)) := match e with inl e => val e | inr e => val e end.
Definition component_e' (e : edge G) : edge (union G1 G2) := 
    match decE e with inl p => inl (Sub e p) | inr p => inr (Sub e p) end.

Lemma component_can_v : cancel component_v component_v'.
Proof.
  case => a; rewrite /component_v/component_v'; case: (decC _) => p. 
  - congr inl. exact: val_inj.
  - exfalso. move: (valP a) => /= X. by rewrite inE X in p.
  - exfalso. move: (valP a) => /=. by rewrite inE p.
  - congr inr. exact: val_inj.
Qed.

Lemma component_can_v' : cancel component_v' component_v.
Proof. by move => x; rewrite /component_v/component_v'; case: (decC x). Qed.

Lemma component_can_e : cancel component_e component_e'.
Proof. 
  case => e; rewrite /component_e/component_e'; case: (decE _) => p.
  - congr inl. exact: val_inj.
  - exfalso. move: (valP e) => /= /edge_setN X. by contrab.
  - exfalso. move: (valP e) => /= X. move/edge_setN in p. by rewrite X in p.
  - congr inr. exact: val_inj. 
Qed.

Lemma component_can_e' : cancel component_e' component_e.
Proof. move => x; rewrite /component_e/component_e'; by case (decE _). Qed.

Lemma component_hom : is_ihom component_v component_e xpred0.
Proof. repeat split; by case. Qed.

Definition iso_component : iso (union (induced C) (induced (~: C))) G := 
  Eval hnf in Iso' component_can_v component_can_v' component_can_e component_can_e' component_hom.

End IsoComponents.

End SSkeleton.
