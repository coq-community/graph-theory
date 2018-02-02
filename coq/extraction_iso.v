Require Import RelationClasses Morphisms Setoid Omega.

From mathcomp Require Import all_ssreflect.

Require Import edone finite_quotient preliminaries.
Require Import sgraph minor checkpoint.
Require Import multigraph subalgebra tm_iso skeleton.
Require Import bounded extraction_def.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs". 


(** * Isomorphim Theorem *)

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
  have E :  g_in |: (g_out |: C) = g_in |: (x |: C).
  { by rewrite (eqP Eio) [x |: C]setU1_mem // setUA setUid. }
  - apply: subgraph_for_iso => //; by rewrite ?E //= (eqP Eio).
  - case: (comp_exit G_conn Eio HC) => z Z1 Z2.
    rewrite sg_sym -adjacentE in Z2. case/andP : Z2 => [A B].
    move/(_ z). by rewrite Z1 B. 
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
    have {He} : @sedge G (source e) (target e).
    { rewrite -adjacentE He. apply/orP; left; apply/existsP; exists e.
      by rewrite !inE !eqxx. }
    move: {e} (source e) (target e).
    suff Hyp (x y : G) : @sedge G x y -> x \in C ->
                         [|| y == g_in, y == g_out | y \in C].
    { move=> x y xy /orP[]H; rewrite H !orbT /= ?andbT; first exact: Hyp xy H.
      move: H. have : @sedge G y x by rewrite sg_sym. exact: Hyp. }
    move=> xy Hx. have := component_exit xy C_comp Hx. by rewrite !inE negbK orbA.
Qed.

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

  - have petal_node (x : G) : x \notin (g_in  |: @sinterval G g_in u) ->
                              x \notin (g_out |: @sinterval G u g_out) ->
                              x \in @petal G IO u.
    { rewrite ![x \in _ |: _]inE ![x \in set1 _]inE !negb_or.
      move=> /andP[/negbTE xNi /negbTE xNl] /andP[/negbTE xNo /negbTE xNr].
      have : x \in [set : skeleton G] by [].
      rewrite (sinterval_petal_cover G_conn iNo).
      rewrite (eqP (edgeless_petal _ (CP_extensive _) pi_e0)) ?in_set2 ?eqxx //.
      rewrite (eqP (edgeless_petal _ (CP_extensive _) po_e0)) ?in_set2 ?eqxx //.
      rewrite !in_setU !in_set1 xNi xNo orbF /=.
      by rewrite (sinterval_cp_cover G_conn u_cpio) !in_setU -orbA xNl xNr orbF. }
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

  - have petal_edge (e : edge G) : e \notin @interval_edges G g_in u ->
                                   e \notin @interval_edges G u g_out ->
                                   e \in edge_set (@petal G IO u).
    { move=> /negbTE eNl /negbTE eNr. have : e \in [set: edge G] by [].
      rewrite (interval_petal_edge_cover G_conn iNo).
      rewrite (eqP pi_e0) (eqP po_e0) set0U setU0.
      by rewrite (interval_cp_edge_cover G_conn u_cpio) !in_setU eNl eNr orbF. }
    pose k (e : edge G) : edge G' :=
      match boolP (e \in @interval_edges G g_in u) with
      | AltTrue eL => inl (Sub e eL)
      | AltFalse eNl => match boolP (e \in @interval_edges G u g_out) with
                        | AltTrue eR => inr (inr (Sub e eR))
                        | AltFalse eNr => inr (inl (Sub e (petal_edge e eNl eNr)))
                        end
      end.
    exists k => e; rewrite /h/k; last by repeat case: {-}_ / boolP => ?.
    case: e => [e|[e|e]].

    + have eL : val e \in @interval_edges G g_in u := valP e.
      case: {-}_ / boolP => H1; last by have := H1; rewrite eL.
      congr inl; exact: val_inj.
    + have e_petal : val e \in edge_set (@petal G IO u) := valP e.
      case: {-}_ / boolP => H1; first (have := H1; rewrite {1}interval_edges_sym).
        by rewrite (disjointFr (interval_petal_edges_disj G_conn _ _) e_petal).
      case: {-}_ / boolP => H2; first have := H2.
        by rewrite (disjointFr (interval_petal_edges_disj G_conn _ _) e_petal).
      congr (inr (inl _)); exact: val_inj.
    + have eR : val e \in @interval_edges G u g_out := valP e.
      case: {-}_ / boolP => H1; first have := H1.
      { rewrite (disjointFl (@interval_edges_disj_cp G g_in g_out u _) eR) //.
        by move: u_cpio; rewrite inE => /andP[_]. }
      case: {-}_ / boolP => H2; last by have := H2; rewrite eR.
      congr (inr (inr _)); exact: val_inj.
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

  - have sintv_node (x : G) : x \notin @petal G IO g_in ->
                              x \notin @petal G IO g_out ->
                              x \in @sinterval G g_in g_out.
    { move=> /negbTE Npi /negbTE Npo. have : x \in [set: G] by [].
      by rewrite (sinterval_petal_cover G_conn Eio) !in_setU Npi Npo orbF. }
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

  - have intv_edge (e : edge G) :
      e \notin edge_set (@petal G IO g_in) -> e \notin edge_set (@petal G IO g_out) ->
      e \in @interval_edges G g_in g_out.
    { move=> /negbTE Npi /negbTE Npo. have : e \in [set: edge G] by [].
      by rewrite (interval_petal_edge_cover G_conn Eio) !in_setU Npi Npo orbF. }
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

Corollary minor_exclusion_2p (G : graph2) :
  connected [set: skeleton G] -> 
  K4_free (sskeleton G) <-> 
  exists (T : forest) (B : T -> {set G}), [/\ decomp T G B, width B <= 3 & compatible B].
Proof.
  move => conn_G. split => [K4F_G|[T [B [B1 B2 B3]]]].
  - have [T [B] [B1 B2 B3]] := (graph_of_TW2' (term_of G)).
    have I := term_of_iso (conj conn_G K4F_G).
    have [D [D1 D2 D3]] := iso2_decomp B1 B2 (iso2_sym I).
    exists T. exists D. by rewrite D2.
  - apply: (TW2_K4_free (G := sskeleton G)) B2.
    exact: decomp_sskeleton.
Qed.

(** ** Graph Minor Theorem for TW2 *)

(** Remark: contrary to the textbook definition, we do not substract 1
in the definition of treewidth. Consequently, [width <= 3] means
treewidth two. *) 

Theorem graph_minor_TW2 (G : sgraph) :
  connected [set: G] -> 
  K4_free G <-> 
  exists (T : forest) (B : T -> {set G}), sdecomp T G B /\ width B <= 3.
Proof.
  move => conn_G. split=> [K4F_G | [T][B][]]; last exact: TW2_K4_free.
  case: (posnP #|G|) =>[G_empty | /card_gt0P[x _]].
  { exists tunit; exists (fun _ => [set: G]). split; first exact: triv_sdecomp.
    apply: leq_trans (width_bound _) _. by rewrite G_empty. }
  have [G' [iso_Gs iso_G]] := flesh_out x.
  have conn_G' : connected [set: skeleton G'].
  { exact: iso_connected conn_G. }
  have M := minor_exclusion_2p conn_G'.  
  have/M [T [B [B1 B2 B3]]] : K4_free (sskeleton G').
  { exact: iso_K4_free K4F_G. }
  have decB : sdecomp T (sskeleton G') B by exact: decomp_sskeleton.
  have [D D1 D2] := sg_iso_decomp decB iso_Gs.
  exists T. exists D. by rewrite D2.
Qed.

Print Assumptions graph_minor_TW2.
