From mathcomp Require Import all_ssreflect.

Require Import edone finite_quotient preliminaries digraph sgraph minor checkpoint.
Require Import menger separators set_tac.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs". 

(** * Combined Minor and Checkpoint Properties *)

(** This file is where we combine the theory of checkpoints and the theory of
minors and prove the lemmas underlying the correctness arguments for the term
extraction function. *)

Section CheckpointsAndMinors.
Variables (G : sgraph).
Hypothesis (conn_G : connected [set: G]).

(** ** Collapsing Bags *)

Lemma collapse_bags (U : {set G}) u0' (inU : u0' \in U) :
  let T := U :|: ~: \bigcup_(x in U) bag U x in 
  let G' := sgraph.induced T in 
  exists phi : G -> G',
    [/\ total_minor_map phi,
     (forall u : G', val u \in T :\: U -> phi @^-1 u = [set val u]) &
     (forall u : G', val u \in U -> phi @^-1 u = bag U (val u))].
Proof.
  move => T G'.
  have inT0 : u0' \in T by rewrite !inE inU.
  pose u0 : G' := Sub u0' inT0.  
  pose phi u := if [pick x in U | u \in bag U x] is Some x 
                then insubd u0 x else insubd u0 u.
  exists phi.
  have phiU (u : G') : val u \in U -> phi @^-1 u = bag U (val u).
  { move => uU. apply/setP => z. rewrite !inE /phi.
    case: pickP => [x /andP [X1 X2]|H]. 
    - rewrite -val_eqE insubdK ?inE ?X1 //. apply/eqP/idP => [<-//|].
      apply: contraTeq => C. 
      suff S: [disjoint bag U x & bag U (val u)] by rewrite (disjointFr S).
      apply: bag_disj => //; exact: CP_extensive. 
    - move: (H (val u)). rewrite uU /= => ->. 
      have zU : z \notin U. { move: (H z). by rewrite bag_id andbT => ->. }
      have zT : z \in T.
      { rewrite !inE (negbTE zU) /=. apply/negP => /bigcupP [x xU xP].
        move: (H x). by rewrite xU xP. }
      rewrite -val_eqE insubdK //. by apply: contraNF zU => /eqP->. }
  have phiT (u : G') : val u \in T :\: U -> phi @^-1 u = [set val u].
  { move/setDP => [uT uU]. apply/setP => z. rewrite !inE /phi. 
    case: pickP => [x /andP [xU xP]|H]. 
    - rewrite -val_eqE insubdK ?inE ?xU // (_ : z == val u = false). 
      + by apply: contraNF uU => /eqP <-.
      + apply: contraTF uT => /eqP ?. subst. 
        rewrite inE (negbTE uU) /= inE negbK. by apply/bigcupP; exists x. 
    - have zU : z \notin U. { move: (H z). by rewrite bag_id andbT => ->. }
      have zT : z \in T.
      { rewrite !inE (negbTE zU) /=. apply/negP => /bigcupP [x xU xP].
        move: (H x). by rewrite xU xP. }
      by rewrite -val_eqE insubdK. }
  have preim_G' (u : G') : val u \in phi @^-1 u.
  { case: (boolP (val u \in U)) => H; first by rewrite phiU // bag_id. 
    rewrite phiT ?set11 // inE H. exact: valP. }
  split => //.
  - split. 
    + move => y. exists (val y). apply/eqP. case: (boolP (val y \in U)) => x_inU. 
      * by rewrite mem_preim phiU // bag_id. 
      * rewrite mem_preim phiT inE // x_inU. exact: valP.
    + move => y. case: (boolP (val y \in U)) => xU.
      * rewrite phiU //. apply: connected_bag => //. exact: CP_extensive.
      * rewrite phiT; first exact: connected1. rewrite inE xU. exact: valP.
    + move => x y xy. exists (val x); exists (val y). by rewrite !preim_G'. 
Qed.

End CheckpointsAndMinors.
Arguments collapse_bags [G] conn_G U u0' _.

(** Neighbor Tree Lemma *)

Definition neighbours (G : sgraph) (x : G) := [set y | x -- y].

(** Proposition 21(ii) *)
Definition igraph (G : sgraph) (x y : G) : sgraph     := induced (interval  x y).
Definition istart (G : sgraph) (x y : G) : igraph x y := Sub  x  (intervalL x y).
Definition iend   (G : sgraph) (x y : G) : igraph x y := Sub  y  (intervalR x y).

Arguments add_edge : clear implicits.
Arguments igraph : clear implicits.
Arguments istart {G x y}.
Arguments iend {G x y}.

(* TOTHINK: This lemma can have a more general statement.
 * add_edge preserves sg_iso when the nodes are applied to the actual iso. *)
Lemma add_edge_induced_iso (G : sgraph) (S T : {set G})
      (u v : induced S) (x y : induced T) :
  S = T -> val u = val x -> val v = val y ->
  diso (add_edge (induced S) u v) (add_edge (induced T) x y).
Proof.
  move=> eq_ST eq_ux eq_vy.
  have SofT z : z \in T -> z \in S by rewrite eq_ST.
  have TofS z : z \in S -> z \in T by rewrite eq_ST.
  set g : induced T -> induced S := fun z => Sub (val z) (SofT (val z) (valP z)).
  set f : induced S -> induced T := fun z => Sub (val z) (TofS (val z) (valP z)).
  apply (@Diso'' (add_edge (induced S) _ _) (add_edge (induced T) _ _) f g); rewrite {}/f {}/g.
  - move => ?. exact: val_inj.
  - move => ?. exact: val_inj.
  - move => a b; rewrite /edge_rel /= /edge_rel /=.
    rewrite -!(inj_eq val_inj) /=. by rewrite eq_ux eq_vy.
  - move => a b. rewrite /edge_rel /= /edge_rel /=.
    rewrite -!(inj_eq val_inj) /=. by rewrite eq_ux eq_vy.
Qed.

(** ** K4-freenes of Intervals *)

Lemma igraph_K4F (G : sgraph) (i o x y : G) :
  connected [set: G] -> 
  x \in cp i o -> y \in cp i o -> x != y ->
  K4_free (add_edge G i o) ->
  K4_free (add_edge (igraph G x y) istart iend).
Proof.
  set H := add_edge G i o.
  set I := add_edge _ _ _.
  move=> G_conn x_cpio y_cpio xNy; apply: minor_K4_free.
  have iNo : i != o.
  { apply: contra_neq xNy => x_y. move: x_cpio y_cpio.
    by rewrite -{}x_y cpxx !inE =>/eqP->/eqP->. }

  have conn_io : connect sedge i o := connectedTE G_conn i o.
  wlog x_le_y : x y @I x_cpio y_cpio xNy / cpo conn_io x y.
  { move=> Hyp. case/orP: (cpo_total conn_io x y); first exact: Hyp.
    move=> ?; suff : minor (add_edge (igraph G y x) istart iend) I.
    { by apply: minor_trans; apply: Hyp; rewrite // 1?sg_sym 1?eq_sym. }
    apply: strict_is_minor; apply: iso_strict_minor.
    setoid_rewrite add_edge_sym. 
    by apply: add_edge_induced_iso; first exact: interval_sym. }

  pose U2 := [set x; y].
  (* As a consequence, i (resp. o) is the the bag of x (resp. y) with
   * respect to {x, y}. *)
  have [i_Px o_Py] : i \in bag U2 x /\ o \in bag U2 y.
  { split; apply/bagP=> z; rewrite CP_set2 (cpo_cp x_cpio y_cpio x_le_y);
    move=> /andP[z_cpio] /andP[x_le_z z_le_y].
    + rewrite (cpo_cp (mem_cpl i o) z_cpio);
      repeat (apply/andP; split) => //; exact: cpo_min.
    + have o_cpio : o \in cp i o by rewrite cp_sym mem_cpl.
      rewrite cp_sym (cpo_cp z_cpio o_cpio);
      repeat (apply/andP; split) => //; exact: cpo_max. }

  case: (collapse_bags G_conn U2 x _); first by rewrite !inE eqxx.
  set T := U2 :|: _. have {T}-> : T = interval x y.
  { rewrite {}/T {-3}/U2 /interval bigcup_setU !bigcup_set1.
    congr ([set x; y] :|: _).
    rewrite -setTD (sinterval_bag_cover G_conn xNy).
    rewrite setUAC setDUl setDv set0U; apply/setDidPl.
    rewrite disjoint_sym disjoints_subset subUset -!disjoints_subset.
    by rewrite {2}sinterval_sym !interval_bag_disj //;
    apply: CP_extensive; rewrite !inE eqxx. }
  rewrite -[induced _]/(igraph G x y). set Gxy := igraph G x y in I *.

  move=> phi [[phi_surj preim_phi_conn phi_edge] preim_phi preim_phixy].
  apply: strict_is_minor. exists phi; split; first exact: phi_surj.
  + move=> u; have u_I : val u \in interval x y := valP u.
    case: (boolP (val u \in U2)) => u_xy.
    - rewrite preim_phixy //. apply: add_edge_connected.
      apply: (@connected_bag G G_conn (val u) U2).
      exact: CP_extensive.
    - rewrite preim_phi; first exact: connected1.
      by rewrite inE u_xy u_I.
  + move=> u v /orP[].
    - move/phi_edge => [u'] [v'] [? ? uv'].
      by exists u'; exists v'; split; rewrite /edge_rel //= uv'.
    - wlog [-> -> _] : u v / u = istart /\ v = iend.
      { case/(_ istart iend); [ by split | by rewrite /= !eqxx xNy | ].
        move=> u' [v'] [? ? ?]. have ? : v' -- u' by rewrite sg_sym.
        case/orP=> /andP[_]/andP[/eqP->/eqP->];
          [ by exists u'; exists v' | by exists v'; exists u' ]. }
      rewrite 2?preim_phixy ?inE ?eqxx // ![val _]/=.
      by exists i; exists o; split; rewrite /edge_rel //= iNo !eqxx.
Qed.

Lemma igraph_K4F_add_node (G : sgraph) (U : {set G}) :
  connected [set: G] -> forall x y, x \in CP U -> y \in CP U -> x != y ->
  K4_free (add_node G U) -> K4_free (add_edge (igraph G x y) istart iend).
Proof.
  set H := add_node G U => G_conn x y x_cp y_cp xy H_K4F.
  set I := add_edge _ _ _.

  case: (CP_base x_cp y_cp) => [i] [o] [i_U o_U].
  rewrite subUset !sub1set =>/andP[x_cpio y_cpio].
  suff : K4_free (add_edge G i o) by exact: igraph_K4F => //.
  set K := add_edge G i o.
  apply: minor_K4_free H_K4F. apply: strict_is_minor.

  set phi : H -> K := odflt i.
  have preim_phi u :
    phi @^-1 u = Some u |: if u == i then [set None] else set0.
  { by apply/setP=> v; case: ifP => u_i; rewrite -mem_preim !inE ?orbF;
    case: v => [v|] //=; rewrite eq_sym. }
  have preim_phixx u : Some u \in phi @^-1 u by rewrite -mem_preim.

  exists phi; split.
  + by move=> /= u; exists (Some u).
  + move=> /= u; rewrite preim_phi.
    case: ifP => [/eqP{u}->|_]; first exact: connected2.
    by rewrite setU0; exact: connected1.
  + move=> u v /orP[]; first by [ exists (Some u); exists (Some v); split ].
    move=> /orP[]/andP[_]/andP[/eqP->/eqP->];
    [ exists None; exists (Some o) | exists (Some o); exists None ];
    by split; rewrite // -mem_preim.
Qed.

(** ** Parallel Split Lemma *)

Lemma sepatates_cp (G : sgraph) (x y z : G) : separates x y [set z] -> z \in cp x y :\: [set x; y].
Proof.
  case. rewrite !inE ![z == _]eq_sym => /negbTE-> /negbTE-> /= H.
  apply/cpP => p. by case: (H p) => z' Hz /set1P <-.
Qed.

(** TOTHINK: Make this the definition of the link relation? Is the
link relation realiy needed in the first place ? *)
Lemma link_rel_sep2 (G : sgraph) (x y : G) :
  connected [set: G] -> ~~ x -- y -> link_rel G x y -> 
  x != y /\ forall S, separates x y S -> 2 <= #|S|.
Proof.
  move => con_G xNy /andP [xDy cp_sub]. split => // S sep_xy. 
  case E : #|S| => [|[|//]].
  - move/cards0_eq : E => E. subst S. move/connectedTE : con_G => /(_ x y).
    apply: contraTT => _. exact/separates0P.
  - move/eqP/cards1P : E => [z Hz]. subst. move/sepatates_cp in sep_xy. by set_tac.
Qed.


Lemma set_pred0 (T : finType) : @set0 T =i pred0. 
Proof. move => z. by rewrite !inE. Qed.
Hint Resolve set_pred0.

Lemma irred_in_sinterval (G : sgraph) (i o : G) (p : Path i o) : 
  irred p -> {subset interior p <= sinterval i o}.
Proof.
  move => Ip u. rewrite 5!inE negb_or -andbA => /and3P [U1 U2 U3].
  case/(isplitP Ip) : U3 => {p Ip} p1 p2 Ip1 Ip2 I. apply/sintervalP2. split.
  - exists (prev p1); rewrite ?irred_rev // inE. apply: contraNN U2 => in_p. by rewrite [o]I.
  - exists p2 => //. apply: contraNN U1 => in_p. by rewrite [i]I.
Qed.

Open Scope implicit_scope.

Lemma ssplit_K4_nontrivial (G : sgraph) (i o : G) : 
  ~~ i -- o -> link_rel G i o -> K4_free (add_edge G i o) -> 
  (* bag [set i;o] i = [set i] -> *)
  connected [set: G] -> disconnected (sinterval i o).
Proof.
  move => io1 L K4F conn_G. case: (link_rel_sep2 conn_G io1 L) => io2 io3 {L}.
  case: (theta io1 io2 io3) => p indep_p. 
  case: (theta_vertices p io2 io1) => x in_p.
  apply/disconnectedE => conn_io.
  have in_io j : x j \in sinterval i o. 
  { apply: irred_in_sinterval (in_p _). exact: valP. }
  case: (path_in_connected conn_io (in_io ord0) (in_io ord1)) => q' Iq /subsetP sub_io. 
  case: (split_at_first (A := mem (interior (p ord1))) (p := q') (k := x ord1)).
    all: try by [exact: in_p|]. 
  move => x2 [q1'] [q2] [E Q1 Q2].
  have Iq1 : irred q1'. move: Iq. rewrite E. by case/irred_catE.
  apply: K4F.
  case: (add_edge_Path i o (p ord0)) => p0 N0.
  case: (add_edge_Path i o (p ord1)) => p1 N1.
  case: (add_edge_Path i o q1') => q Nq.
  have io : i -- o :> add_edge G i o by rewrite /edge_rel/= io2 !eqxx.
  pose p2 := edgep io.    
  apply (@K4_of_paths (add_edge G i o)) with i o (x ord0) x2 p0 p1 p2 q => //.
  - rewrite (independent_nodes N0 N1). exact: indep_p.
  - by rewrite /independent interior_edgep disjoint_sym eq_disjoint0. 
  - by rewrite /independent interior_edgep disjoint_sym eq_disjoint0.
  - by rewrite (interior_eq_nodes N0). 
  - by rewrite (interior_eq_nodes N1).
  - rewrite (irred_eq_nodes N0). exact: valP.
  - rewrite (irred_eq_nodes N1). exact: valP.
  - exact: irred_edge.
  - by rewrite (irred_eq_nodes Nq).
  - apply/disjointP => z. rewrite (mem_eq_nodes Nq) => z_q1'. case/set2P => [?|?]; subst.
    + move: (sub_io i). by rewrite sinterval_bounds !inE z_q1' => /(_ isT).
    + move: (sub_io o). by rewrite sinterval_bounds !inE z_q1' => /(_ isT).
  - move => z. rewrite (interior_edgep) inE /= in_set0 orbF (mem_eq_nodes Nq). 
    rewrite (interior_eq_nodes N1). exact: Q2.
Qed.

Close Scope implicit_scope.
