Require Import RelationClasses.

From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries digraph sgraph minor checkpoint.
Require Import multigraph ptt_graph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 

(** * Skeletons *)

(** ** Adjacency *)

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

Definition sk_rel (G : graph) : rel G := fun x y => (x != y) && adjacent x y.

Arguments sk_rel G _ _ / : clear implicits.

Lemma sk_rel_sym (G : graph) : symmetric (sk_rel G).
Proof. move=> x y. by rewrite /sk_rel/= eq_sym adjacent_sym. Qed.

Lemma sk_rel_irrefl (G : graph) : irreflexive (sk_rel G).
Proof. move=> x. by rewrite /sk_rel/= eqxx. Qed.

Definition skeleton (G : graph) := 
  SGraph (@sk_rel_sym G) (@sk_rel_irrefl G).

Lemma skelP (G : graph) (P : G -> G -> Prop) : 
  Symmetric P -> 
  (forall e : edge G, source e != target e -> P (source e) (target e)) ->
  (forall x y : G,  sk_rel _ x y -> P x y).
Proof. 
  move => S H x y. case/andP=> xNy. case/existsP=> e He. move: He xNy. rewrite !inE.
  case/orP=> /andP[/eqP<- /eqP<-]; last rewrite eq_sym; move=> /H//. exact: S.
Qed.

(** Edges of skeletons of quotients *)
Lemma sk_rel_mergeE (G : graph) (e : equiv_rel G) x y :
  sk_rel (merge_def G e) x y <-> 
  x != y /\ exists x0 y0 : skeleton G, [/\ \pi x0 = x, \pi y0 = y & x0 -- y0].
Proof.
  rewrite /= /sk_rel. 
  case: (boolP (x != y)) => //=; last by move => _; split => [|[]]. 
  move => xy; split.
  - move => A. split => //. move: xy. pattern x, y. apply adjacentP => //.
    + move => {x y A} x y H xy. 
      case: H => [|x0 [y0] [? ? /andP [E A]]]; first by rewrite eq_sym.
      exists y0; exists x0. by rewrite /edge_rel/= eq_sym adjacent_sym A E. 
    + move => e0. exists (@source G e0). exists (@target G e0).
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


(* Lemma skel_iso_g (G1 G2 : graph) h : @iso_g G1 G2 h -> sg_iso_g (skeleton G1) (skeleton G2). *)

Lemma skel_iso (G1 G2 : graph) : iso G1 G2 -> sg_iso (skeleton G1) (skeleton G2).
Abort.
  
Lemma pi_hom (G : graph) (e : equiv_rel G) : 
  hom_s (\pi_{eq_quot e} : skeleton G -> skeleton (merge_def G e)).
Proof.
  move => x y xy Dxy. apply/sk_rel_mergeE. split => //. by exists x; exists y.
Qed.
Arguments pi_hom [G] e.


Coercion skeleton : graph >-> sgraph.


(** * Strong skeletons *)

Definition sskeleton (G : graph2) := @add_edge (skeleton G) g_in g_out.

Lemma sskelP (G : graph2) (P : G -> G -> Prop) : 
  Symmetric P -> 
  (forall e : edge G, source e != target e -> P (source e) (target e)) ->
  (g_in != g_out :> G -> P g_in g_out) ->
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

Lemma hom2_sskel (G1 G2 : graph2) h :
  @hom_g G1 G2 h -> h.1 g_in = g_in -> h.1 g_out = g_out -> bijective h.1 -> 
  forall x y, @edge_rel (sskeleton G1) x y -> @edge_rel (sskeleton G2) (h.1 x) (h.1 y).
Proof.
  move => hom_h h_in h_out bij. apply sskelP. 
  - move => x y. by rewrite sgP.
  - move => e He. rewrite /edge_rel /=  [_ -- _](_ : _ = true) /edge_rel //=.
    rewrite bij_eq ?He //=. apply/existsP; exists (h.2 e). 
    by rewrite !inE !hom_h !eqxx.
  - move => H. by rewrite /edge_rel /= bij_eq // H h_in h_out !eqxx. 
Qed.

Lemma iso_inv (F G: graph) h:
  @iso_g F G h ->
  exists k, @hom_g G F k
            /\ cancel h.1 k.1 /\ cancel k.1 h.1
            /\ cancel h.2 k.2 /\ cancel k.2 h.2.
Proof.
  case => H [[k1 H1 H1'] [k2 H2 H2']]. exists (k1,k2). split =>//.
  (repeat split)=>e/=.
Admitted.

Lemma iso2_sskel (G1 G2 : graph2) : G1 ≈ G2 -> sg_iso (sskeleton G1) (sskeleton G2).
Proof.
  case => h [[iso_h hin] hout].
  destruct (iso_inv iso_h) as (k&hom_k&hk1&kh1&hk2&kh2).
  apply: SgIso. apply kh1. apply hk1.
  - apply: (hom2_sskel hom_k). by rewrite -(hk1 g_in) hin. by rewrite -(hk1 g_out) hout. exact: Bijective.
  - apply: (hom2_sskel iso_h.1) =>//. exact: Bijective.
Qed.

Lemma iso2_decomp (G1 G2 : graph2) (T : forest) B1 : 
  @sdecomp T (sskeleton G1) B1 -> G1 ≈ G2 -> 
  exists2 B2, @sdecomp T (sskeleton G2) B2 & width B2 = width B1.
Proof.
  move => dec iso. apply: sg_iso_decomp dec _. exact: iso2_sskel. 
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
  @edge_set G [set x; y] == set0 -> ~~ @adjacent G x y. 
Proof. 
  apply: contraTN => /existsP[e]. rewrite !inE => He.
  apply/set0Pn. exists e. rewrite !inE.
  by case/orP: He => /andP[->->]; rewrite orbT.
Qed.

Lemma sskeleton_subgraph_for (G : graph2) (V : {set G}) (E : {set edge G})
  (con : consistent V E) (i o : sig [eta mem V]) : val i = g_in -> val o = g_out ->
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
  adjacent i o -> sg_iso (skeleton G) (sskeleton (point G i o)).
Proof.
  move=> Aio. pose id_G := id : vertex G -> vertex G.
  exists id_G id_G => // x y; last by rewrite {2}/edge_rel/= => ->.
  move: x y. apply sskelP.
  - move=> x y. by rewrite sg_sym.
  - rewrite /edge_rel/= => e -> /=. exact: adjacent_edge.
  - by rewrite /edge_rel/= => ->.
Qed.

(** We treat [remove_edges] separately from [subgraph_for] since
removing only edges allows us to avoid the sigma-type on for the
vertices *)
Definition remove_edges (G : graph) (E : {set edge G}) := 
  {| vertex := G;
     edge := [finType of { e : edge G | e \notin E }];
     source e := source (val e);
     target e := target (val e);
     label e := label (val e) |}.

Lemma remove_loops (G : graph) (E : {set edge G}) :
  {in E, forall e, source e = target e} ->
  sg_iso (skeleton G) (skeleton (remove_edges E)).
Proof.
  move=> Eloops. pose id_G := id : vertex G -> vertex G.
  have Esame x y : x != y -> @edges (remove_edges E) x y = val @^-1: @edges G x y.
  { move=> xNy. apply/setP=> e. by rewrite !inE. }
  exists id_G id_G => // x y; rewrite /id_G /=/sk_rel => /andP[xNy].
  all: rewrite /edge_rel/=.
  all: rewrite xNy /adjacent/= !Esame // 1?eq_sym // -preimsetU.
  - case/existsP=> e. rewrite inE => He. apply/existsP. by exists (val e).
  - case/existsP=> e He.
    suff H : e \notin E by apply/existsP; exists (Sub e H); rewrite inE.
    apply: contraNN xNy => /Eloops eq_e. move: He. rewrite !inE -eq_e.
    by case/orP=> /andP[/eqP<- /eqP<-].
Qed.

Lemma remove_edges_connected (G : graph) (E : {set edge G}) :
  {in E, forall e : edge G, connect (sk_rel (remove_edges E)) (source e) (target e)} ->
  connected [set: skeleton G] -> connected [set: skeleton (remove_edges E)].
Proof.
  move=> E_conn G_conn. apply: connectedTI => x y. have := connectedTE G_conn x y.
  apply: connect_sub x y. move=> /=. apply skelP.
  - by move=> x y; rewrite connect_symI //; exact: sk_rel_sym (remove_edges E).
  - move=> e sNt. case: (boolP (e \in E)) => [/E_conn//|He].
    apply: connect1. rewrite /sk_rel sNt /=.
    by apply/existsP; exists (Sub e He); rewrite !inE !eqxx.
Qed.

Lemma remove_edges_cross (G : graph) (V : {set G}) (E : {set edge G}) (x y : G) :
  E \subset edge_set V -> sk_rel G x y -> y \notin V -> sk_rel (remove_edges E) x y.
Proof.
  move=> E_subV xy yNV.
  have {yNV} : (x \notin V) || (y \notin V) by rewrite yNV.
  pattern x, y. revert x y xy.
  apply skelP; first by move=> x y; rewrite orbC sk_rel_sym.
  move=> e sNt stNV. rewrite /sk_rel sNt /=.
  case: (boolP (e \in E)) => He; last first.
  - apply/existsP; exists (Sub e He); by rewrite !inE !eqxx.
  - move: He stNV => /(subsetP E_subV). rewrite inE. by case/andP=> -> ->.
Qed.

Lemma remove_edges_restrict (G : graph) (V : {set G}) (E : {set edge G}) (x y : G) :
  E \subset edge_set V -> connect (restrict (mem (~: V)) (sk_rel G)) x y ->
  connect (sk_rel (remove_edges E)) x y.
Proof.
  move=> E_subV. apply: connect_mono x y => x y /=. rewrite !inE -andbA.
  case/and3P=> xNV yNV xy. exact: remove_edges_cross xy yNV.
Qed.

Lemma sskeleton_remove_io (G : graph2) (E : {set edge G}) :
  E \subset @edge_set G [set g_in; g_out] ->
  sg_iso (sskeleton (point (remove_edges E) g_in g_out)) (sskeleton G).
Proof.
  move=> E_subIO. pose id_G := id : vertex G -> vertex G.
  exists id_G id_G; move=> //; rewrite {}/id_G; apply sskelP.
  - move=> x y. by rewrite sg_sym.
  - move=> e sNt /=. case: (boolP (e \in E)) => Ee; last first.
    + apply/orP; left. rewrite /edge_rel/= sNt /=. apply/existsP; exists (Sub e Ee).
      by rewrite !inE !eqxx.
    + move: Ee sNt => /(subsetP E_subIO). rewrite !inE /edge_rel/=.
      by case/andP=> /orP[]/eqP-> /orP[]/eqP->; rewrite !eqxx // eq_sym => ->.
  - rewrite /edge_rel/= => ->. by rewrite !eqxx.
  - move=> x y. by rewrite sg_sym.
  - move=> e sNt. apply/orP; left. rewrite /edge_rel/= sNt /=. exact: adjacent_edge.
  - rewrite /edge_rel /= => ->. by rewrite !eqxx.
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
Proof. move=> e. rewrite inE =>/andP[_]. by rewrite inE =>/andP. Qed.

Definition igraph (G : graph) (x y : skeleton G) :=
  @point (subgraph_for (@igraph_proof G x y))
         (Sub x (intervalL x y))
         (Sub y (intervalR x y)).

Definition bgraph (G : graph) (U : {set G}) (x:G) :=
  @point (induced (@bag (skeleton G) U x))
         (Sub x (@bag_id (skeleton G) U x))
         (Sub x (@bag_id (skeleton G) U x)).

Lemma bgraph_eq_io (G : graph) (U : {set G}) (x : G) : g_in = g_out :> @bgraph G U x.
Proof. by []. Qed.

Lemma interval_bag_edges_disj (G : graph) (U : {set G}) (x y : G) :
  connected [set: skeleton G] -> x \in @CP G U -> y \in @CP G U ->
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
  move/connectedTE/(_ x y). case/uPathP => p _ xy. 
  case: (splitL p xy) => x' [/= xx'] _. apply/card_gt0P.
  case/andP: xx' => _. case/existsP=> e _. by exists e.
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
  rewrite /edge_rel/= -val_eqE. case/andP=> xNb. rewrite xNb /= => adjv_xb.
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

Lemma connected_skeleton (G : graph) V E (con : @consistent G V E) :
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
  sg_iso (sskeleton (point _ x x)) (skeleton G).
Proof.
  exists (id : skeleton G -> sskeleton (point G x x)) id => // u v /=.
  - by rewrite {2}/edge_rel/= => ->.
  - case/or3P => // /and3P[uNv /eqP eq1 /eqP eq2];
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
  exists hv => // x y xy _. move: x y xy. 
  apply skelP; first by move=> x y; rewrite sg_sym.
  move=> e sNt. by rewrite /edge_rel/= (inj_eq inj_hv) sNt !hom_h adjacent_edge.
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
  exists (id : G -> skeleton G') id; move=> //= x y; rewrite /sk_rel.
  - move=> xy. rewrite /edge_rel /= sg_edgeNeq //=.
    apply/existsP; exists (Sub (x, y) xy). by rewrite !inE !eqxx.
  - case/andP=> _ /existsP[][/=][u v /=] uv. rewrite !inE /=.
    case/orP=> /andP[/eqP<- /eqP<-] //; by rewrite sg_sym.
Qed.
