Require Import RelationClasses Morphisms Setoid Omega.

From mathcomp Require Import all_ssreflect.

Require Import edone finite_quotient preliminaries bij set_tac.
Require Import digraph sgraph minor checkpoint.
Require Import mgraph_jar ptt equiv mgraph2_jar skeleton.
Require Import bounded extraction_def.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

Section ExtractionIso.
Variable sym : eqType.
Notation graph := (@graph sym).
Notation graph2 := (@graph2 sym).
Open Scope ptt_ops.

(** * Isomorphim Theorem *)

(** In this file we prove correctness of the extraction function. This
mainly amounts to establishing a variety of isomorphisms corresponding
to the way the extraction function decomposes graphs. *)

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

(** These two lemmas make use of [merge_subgraph_dot], drastically
simplifying their proofs (comparted to the proofs underlying the ITP
2018 paper) *)

Lemma split_pip (G : graph2) : 
  connected [set: skeleton G] -> g_in != g_out :> G ->
  G ≈ @bgraph _ G IO g_in · (@igraph _ G g_in g_out · @bgraph _ G IO g_out).
Proof.
  move => conn_G Dio. symmetry.
  rewrite -> dotA. 
  rewrite /= {1}/bgraph /igraph /induced. 
  rewrite -> merge_subgraph_dot => //=. 
  move: (union_bij_proofL _ _) => Pi.
  move: (union_bij_proofR _ _) => Po.
  move: (consistentU _ _) => con1.
  rewrite /bgraph/induced. rewrite -> merge_subgraph_dot => //=.
  rewrite -> iso2_subgraph_forT => //=. 
  all: have [? ?] : g_in \in @CP (skeleton G) IO /\ g_out \in @CP (skeleton G) IO
    by split; apply: CP_extensive; rewrite !inE eqxx.
  - move => x. move: (sinterval_bag_cover conn_G Dio). 
    have: x \in [set: G] by []. rewrite /interval; set_tac.
  - move => e. by rewrite -(interval_bag_edge_cover).
  - apply: disjointsU. exact: bag_edges_disj. 
    rewrite disjoint_sym interval_edges_sym. exact: interval_bag_edges_disj.
  - move => x A B. rewrite inE (disjointFl (bag_disj conn_G _ _ Dio)) //= interval_sym in A.
    exact: (@bag_interval_cap G) B A. 
  - exact: interval_bag_edges_disj.
  - move => x. exact: (@bag_interval_cap G).
Qed.

Lemma split_cp (G : graph2) (u : skeleton G) :
  connected [set: skeleton G] -> u \in @cp G g_in g_out :\: IO ->
  edge_set (@bag G IO g_in) == set0 -> 
  edge_set (@bag G IO g_out) == set0 ->
  G ≈ @igraph _ G g_in u · (@bgraph _ G IO u · @igraph _ G u g_out).
Proof.
  move => conn_G proper_u Ei0 Eo0. symmetry.
  have Dio: g_in != g_out :> G. 
  { apply: contraTneq proper_u => <-. by rewrite setUid cpxx setDv inE. }
  have [? ? ?] : [/\ g_in \in @CP G IO, g_out \in @CP G IO & u \in @CP G IO].
  { split; rewrite CP_set2 ?(@mem_cpl G) //; by [rewrite cp_sym (@mem_cpl G)|set_tac]. }
  rewrite -> dotA. rewrite /= {1}/igraph /bgraph /induced.
  rewrite -> merge_subgraph_dot => //=. 
  move: (union_bij_proofL _ _) => Pi.
  move: (union_bij_proofR _ _) => Po.
  move: (consistentU _ _) => con1.
  rewrite /igraph. rewrite -> merge_subgraph_dot => //=.
  rewrite -> iso2_subgraph_forT => //=.
  - move => x. 
    have: x \in @interval G g_in g_out. 
    { move: (sinterval_bag_cover conn_G Dio). 
      rewrite (eqP (edgeless_bag _ _ _)) // (eqP (edgeless_bag _ _ _)) //.
      rewrite setUC setUA [[set _;_]]setUC -/(@interval G _ _) => <- //. }
    rewrite (interval_cp_cover conn_G proper_u) /interval. by set_tac.
  - move => e.
    have: e \in interval_edges g_in g_out.
    { move: (interval_bag_edge_cover conn_G Dio).
      by rewrite (eqP Ei0) (eqP Eo0) set0U setU0 => <-. }
    by rewrite (interval_cp_edge_cover conn_G proper_u). 
  - apply: disjointsU. apply: interval_edges_disj_cp. by set_tac.
    apply: interval_bag_edges_disj => //. 
  - move => x. case/setUP. apply: (@interval_interval_cap G). by set_tac.
    exact: (@bag_interval_cap G).
  - by rewrite disjoint_sym interval_edges_sym interval_bag_edges_disj. 
  - move => x A B. rewrite interval_sym in A. exact: (@bag_interval_cap G) B A.
Qed.

(* TODO: prove a lemma corresponding to [merge_subgraph_dot] for
[par2] and simplify the proofs below *)
  
Lemma iso_split_par2 (G : graph2) (C D : {set G}) 
  (Ci : g_in \in C) (Co : g_out \in C) (Di : g_in \in D) (Do : g_out \in D) :
  C :&: D \subset IO -> C :|: D = setT -> 
  edge_set C :&: edge_set D = set0 -> edge_set C :|: edge_set D = setT ->
  G ≈ (par2 (point (induced C) (Sub g_in Ci) (Sub g_out Co)) 
            (point (induced D) (Sub g_in Di) (Sub g_out Do))).
Proof.
  move => subIO fullCD disjE fullE. symmetry. setoid_rewrite par2_alt.
  set G1 := point _ _ _. set G2 := point _ _ _. set G' := par2' _ _.

  have injL (x y : G1) : inl x = inl y %[mod @par2_eqv_equivalence _ G1 G2] -> x = y.
  { move=> /eqquotP/=. rewrite /par2_eqv sum_eqE -!(inj_eq val_inj) !SubK andbb.
    case/orP=> [/eqP|]; first exact: val_inj.
    case: ifPn; rewrite ?negbK ?in_set2 => Eio; first case/orP.
    all: rewrite 1?eqEcard subUset !sub1set !in_setU !in_set1 !sum_eqE !orbF.
    - by case/andP=> /andP[]/eqP->/eqP->.
    - by case/andP=> /andP[]/eqP->/eqP->.
    - by case/andP=> /orP[]/eqP-> /orP[]/eqP->; apply: val_inj => //=; rewrite -(eqP Eio). }
  have injR (x y : G2) : inr x = inr y %[mod @par2_eqv_equivalence _ G1 G2] -> x = y.
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
      * by move/(@par2_LR _ G1 G2) => [[/valE/= -> ->]|[/valE/= -> ->]].
    + rewrite /f/h. case: piP => [[y|y]] /=. 
      * by move/injL <-. 
      * by move/(@par2_LR _ G1 G2) => [[/valE/= -> ->]|[/valE/= -> ->]].
    + rewrite /f/h. case: piP => [[y|y]] /=. 
      * by move/esym/(@par2_LR _ G1 G2) => [[-> /valE/= ->]|[-> /valE/= ->]].
      * by move/injR <-. 
    + rewrite /f/h. case: piP => [[y|y]] /=. 
      * by move/esym/(@par2_LR _ G1 G2) => [[-> /valE/= ->]|[-> /valE/= ->]].
      * by move/injR <-. 
  - rewrite /f. case: piP => [[y|y]] /=. 
    + by move/injL<-.
    + by move/(@par2_LR _ G1 G2) => [[_ ->]|[/valE/= -> ->]]. 
  - rewrite /f. case: piP => [[y|y]] /=. 
    + by move/injL<-.
    + by move/(@par2_LR _ G1 G2) => [[/valE/= -> ->]|[_ ->]].
Qed.

Lemma comp_dom2_redirect (G : graph2) (C : {set G}) : 
  connected [set: skeleton G] -> g_in == g_out :> G ->
  edge_set G IO == set0 -> C \in @components G [set~ g_in] ->
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
  g_in == g_out :> G -> edge_set G IO == set0 ->
  @components G [set~ g_in] == set0 -> G ≈ one2 _.
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
  edge_set G IO == set0 -> C \in @components G (~: IO) ->
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

Lemma edges2_nil : edges2 nil ≈ @top2 _.
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
    * move/(@par2_LR _ (sym2b' a b) (edges2 Ar)) : Hy.
      case => [[-> ->]|[-> ->]]; by destruct b.
    * move/(@par2_injR _ (sym2b' a b) (edges2 Ar)) : Hy. apply. 
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
  edges2 As ≈ \big[@par2 sym/@top2 _]_(x <- As) sym2b x.1 x.2.
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
    * move/(@par2_LR _ (edges2 [seq strip e | e in E]) 
                     (point (remove_edges E) g_in g_out)) : Hy.
        by case => [][-> ->]. 
    * exact: (@par2_injR _ (edges2 [seq strip e | e in E]) 
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


Lemma componentless_top (G : graph2) : 
  g_in != g_out :> G -> @components G (~: IO) == set0 -> 
  point (@remove_edges _ G (edge_set IO)) g_in g_out ≈ @top2 _.
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

Set Printing Universes.

Lemma edges2_graph_of (G : graph2) : 
  edges2 [seq strip e | e in @edges _ G g_in g_out :|: edges g_out g_in] ≈ 
  graph_of_term (\big[@tm_par _/@tm_top _]_(e in (@edges _ G g_in g_out :|: edges g_out g_in)) tm_ e).
Proof.
  setoid_rewrite edges2_big. rewrite big_map.
  (* setoid_rewrite graph_of_big_pars. -- breaks with u+v<=k constraint error *)
  etransitivity. 2: eapply iso2_sym. 2: eapply graph_of_big_pars.  
  rewrite -big_enum_in.
  set s := enum _. 
  apply: big_par_iso2.
  move => e. rewrite mem_enum /tm_ /strip inE. by case: (e \in edges g_in _). 
Qed.

Theorem term_of_iso (G : graph2) : 
  CK4F G -> G ≈ (graph_of_term (term_of G)).
Proof.
  elim: (wf_leq (@term_of_measure sym) G) => {G} G _ IH CK4F_G.
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

End ExtractionIso.

