From mathcomp Require Import all_ssreflect.

Require Import edone finite_quotient preliminaries sgraph minor checkpoint skeleton. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs". 

(** * Combined Minor and Checkpoint Properties *)

(* Lemma edgeNeq (G : sgraph) (x y : G) : x -- y -> x != y. *)
(* Proof. apply: contraTN => /eqP->. by rewrite sgP. Qed. *)

Lemma linkNeq (G : sgraph) (x y : link_graph G) : x -- y -> x != y.
Proof. move => A. by rewrite sg_edgeNeq. Qed.

Lemma idx_end (G : sgraph) (x y : G) (p : Path x y) z : 
  irred p -> z \in p -> idx p z <= idx p y.
Proof.
  case: p => p pth_p. rewrite /idx /irred in_collective nodesE SubK.
  elim: p x pth_p  => [|a p IH] x.
  - rewrite inE. by move/spath_nil => -> _ /eqP->.
  - admit.
Admitted.

Arguments Path G x y : clear implicits.

Section CheckpointsAndMinors.
Variables (G : sgraph).
Hypothesis (conn_G : forall x y :G, connect sedge x y).


Lemma ins (T : finType) (A : pred T) x : x \in A -> x \in [set z in A].
Proof. by rewrite inE. Qed.

Lemma C3_of_triangle (x y z : link_graph G) : 
  x -- y -> y -- z -> z -- x -> exists2 phi : G -> option C3, 
  minor_map phi & [/\ phi x = Some ord0, phi y = Some ord1 & phi z = Some ord2].
Proof.
  move => xy yz zx.
  have/cpPn' [p irr_p av_z] : (z:G) \notin @cp G x y. 
  { apply: link_cpN => //; apply: linkNeq => //. by rewrite sg_sym. }
  have/cpPn' [q irr_q av_x] : (x:G) \notin @cp G z y.
  { apply: link_cpN => //; first (by rewrite sg_sym) ;apply: linkNeq => //. 
    by rewrite sg_sym. }
  have [Yq Yp] : y \in q /\ y \in p by split;apply: nodes_end.
  case: (split_at_first (G := G) (A := mem p) Yp Yq) => n1 [q1] [q2] [def_q Q1 Q2]. 
  have Hn : n1 != x.
  { apply: contraNN av_x => /eqP<-. by rewrite def_q mem_pcat nodes_end. }
  have {q irr_q av_x Yq def_q q2 Yp} irr_q1 : irred q1.
  { move:irr_q. rewrite def_q irred_cat. by case/and3P. }
  have/cpPn' [q irr_q av_n1] : n1 \notin @cp G z x. 
  { apply link_cpN => //. apply: contraNN av_z => /eqP?. by subst n1. }
  have [Xq Xp] : x \in q /\ x \in p by split; rewrite /= ?nodes_end ?nodes_start. 
  case: (split_at_first (G := G) (A := mem p) Xp Xq) => n2 [q2] [q2'] [def_q Q3 Q4].
  have N : n1 != n2. 
  { apply: contraNN av_n1 => /eqP->. by rewrite def_q mem_pcat nodes_end. }
  have {q irr_q av_n1 Xp Xq q2' def_q} irr_q2 : irred q2.
  { move:irr_q. rewrite def_q irred_cat. by case/and3P. }
  wlog before: n1 n2 q1 q2 irr_q1 irr_q2 Q1 Q2 Q3 Q4 N {Hn} / idx p n1 < idx p n2. 
  { move => W. 
    case: (ltngtP (idx p n1) (idx p n2)) => H.
    - by apply: (W n1 n2 q1 q2).
    - apply: (W n2 n1 q2 q1) => //. by rewrite eq_sym.
    - case:notF. apply: contraNT N => _. apply/eqP. exact: idx_inj H. }
  case: (splitR q1 _) => [|z1 [q1' [zn1 def_q1]]].
  { by apply: contraNN av_z => /eqP->. }
  case: (splitR q2 _) => [|z2 [q2' [zn2 def_q2]]].
  { by apply: contraNN av_z => /eqP->. }
  gen have D,D1 : z1 n1 q1 q1' zn1 irr_q1 def_q1  Q2 {Q1 N before} / 
     [disjoint p & q1'].
  { have A : n1 \notin q1'. 
    { move: irr_q1. rewrite def_q1 irred_cat /= => /and3P[_ _ A].
      by rewrite (disjointFl A _). }
    rewrite disjoint_subset; apply/subsetP => z' Hz'. rewrite !inE.
    apply: contraNN A => A. 
    by rewrite -[n1](Q2 _ Hz' _) // def_q1 mem_pcat A. }
  have {D} D2 : [disjoint p & q2'] by apply: (D z2 n2 q2 q2' zn2).
  case/(isplitP irr_p) def_p : p / Q1 => [p1 p2 _ irr_p2 D3].
  have N2 : n2 \in tail p2. { subst p. by rewrite -idxR in before. }
  have N1 : n1 != y. 
  { apply: contraTN before => /eqP->. by rewrite -leqNgt idx_end. }
  case: (splitL p2 N1) => n1' [n_edge] [p2'] [def_p2 tail_p2].
  have N2' : n2 \in p2' by rewrite tail_p2.
  
  pose pz := pcat (prev q1') q2'.
  pose phi u : option C3 := 
         if u \in p1  then Some ord0
    else if u \in p2' then Some ord1
    else if u \in pz  then Some ord2
                    else None.
  have D_aux : [disjoint p & pz].
  { (* ugly: exposes in_nodes *)
    rewrite ![[disjoint p & _]]disjoint_sym in D1 D2 *. 
    rewrite (eq_disjoint (A2 := [predU q1' & q2'])) ?disjointU ?D1 //.
    move => u. by rewrite !inE mem_pcat mem_prev. }
  have {D_aux} D : [disjoint3 p1 & p2' & pz].
  { subst p; apply/and3P. split.
    - apply: disjoint_transR D3. apply/subsetP => u. by rewrite tail_p2. 
    - apply: disjoint_transL D_aux. apply/subsetP => u. 
      by rewrite mem_pcatT tail_p2 => ->.
    - rewrite disjoint_sym. apply: disjoint_transL D_aux. apply/subsetP => u. 
      by rewrite mem_pcat => ->. }
  (* clean up assumptions that are no longer needed *)
  move => {Q2 Q3 Q4 av_z irr_p before D2 D1 D3 irr_q1 irr_q2 xy yz zx}.
  move => {def_q1 def_q2 N1 N2 def_p2 tail_p2 p def_p N q1 q2}.

  have [Px Py Pz] : [/\ x \in p1, y \in p2' & z \in pz]. 
  { by rewrite /= mem_pcat ?nodes_start ?nodes_end. }
  have phi_x : phi x = Some ord0. 
  { rewrite /phi. by case: (disjoint3P x D) Px. }
  have phi_y : phi y = Some ord1. 
  { rewrite /phi. by case: (disjoint3P y D) Py. }
  have phi_z : phi z = Some ord2. 
  { rewrite /phi. by case: (disjoint3P z D) Pz. }
  exists phi => //. split. 
    + case. move => [|[|[|//]]] Hc; [exists x|exists y|exists z]; 
        rewrite ?phi_x ?phi_y ?phi_z;exact/eqP.
    + move => c u v. rewrite !inE => /eqP E1 /eqP E2; move: E1 E2. 
      rewrite {1 2}/phi. 
      case: (disjoint3P u D) => [Hu|Hu|Hu|? ? ?];
      case: (disjoint3P v D) => [Hv|Hv|Hv|? ? ?] // <- // _.      
      * move: (connected_path (p := p1) (ins Hu) (ins Hv)).
        apply: connect_mono. apply: restrict_mono => {u v Hu Hv} u.
        rewrite !inE /phi. by case: (disjoint3P u D).
      * move: (connected_path (p := p2') (ins Hu) (ins Hv)).
        apply: connect_mono. apply: restrict_mono => {u v Hu Hv} u.
        rewrite !inE /phi. by case: (disjoint3P u D).
      * move: (connected_path (p := pz) (ins Hu) (ins Hv)).
        apply: connect_mono. apply: restrict_mono => {u v Hu Hv} u.
        rewrite !inE /phi. by case: (disjoint3P u D).
    + move => c1 c2.
      wlog: c1 c2 / c1 < c2.
      { move => W. case: (ltngtP c1 c2) => [|A B|A B]; first exact: W.
        - case: (W _ _ A _) => [|y0 [x0] [? ? ?]]; first by rewrite sgP. 
          exists x0; exists y0. by rewrite sgP.
        - case/ord_inj : A => ?. subst. by rewrite sgP in B. }
      case: c1 => [[|[|[|//]]]]; case: c2 => [[|[|[|//]]]] //= Hc2 Hc1 _ _. 
      * exists n1. exists n1'. rewrite !inE n_edge. split => //.
        -- rewrite /phi. by case: (disjoint3P n1 D) (nodes_end p1). 
        -- rewrite /phi. by case: (disjoint3P n1' D) (nodes_start p2'). 
      * exists n1. exists z1. rewrite !inE sg_sym zn1. split => //.
        -- rewrite /phi. by case: (disjoint3P n1 D) (nodes_end p1). 
        -- rewrite /phi. by case: (disjoint3P z1 D) (nodes_start pz). 
      * exists n2. exists z2. rewrite !inE sg_sym zn2. split => //.
        -- rewrite /phi. by case: (disjoint3P n2 D) N2'.
        -- rewrite /phi. by case: (disjoint3P z2 D) (nodes_end pz). 
Qed.


Lemma K4_of_triangle (x y z : link_graph G) : 
  x -- y -> y -- z -> z -- x -> minor (add_node G [set x;y;z]) K4.
Proof.
  move => xy yz zx.
  (* Rewrite K4 to match the conclusion of the [minor_with] lemma. *)
  apply: (@minor_trans _ (add_node C3 setT)); last first.
    by apply: strict_is_minor; apply: iso_strict_minor; exact: add_node_complete.
  (* By [C3_of_triangle], there is a minor map [phi : G -> option C3]. *)
  case: (C3_of_triangle xy yz zx) => phi mm_phi [phi_x phi_y phi_z].
  (* Precomposing [phi] with [val] makes it a minor map from [induced _] to C3
   * so that it fits the premiss of [minor_with]. *)
  have := minor_map_comp (@minor_induced_add_node G [set x; y; z]) mm_phi.
  apply: (minor_with (i := None : add_node _ _)); first by rewrite !inE.
  move=> u _.
  (* Rewrite the conclusion of [C3_of_triangle] in a more uniform way. *)
  (* TODO? change the statement of that lemma? *)
  have : exists2 v, phi v = Some u & v \in [set x; y; z].
    case: u; case=> [| [| [| // ] ] ] lt3;
    [exists x | exists y | exists z];
    rewrite ?phi_x ?phi_y ?phi_z ?inE ?eqxx // /ord0 /ord1 /ord2;
    do 2 f_equal; exact: bool_irrelevance.
  (* The remaining side-condition of [minor_with] then follows. *)
  case=> v eq_v v_in3.
  have sv_in : Some v \in [set~ None] by rewrite !inE.
  exists (Sub (Some v) sv_in) => //.
  by rewrite -mem_preim /= eq_v.
Qed.

Lemma collapse_petals (U : {set G}) u0' (inU : u0' \in U) :
  let T := U :|: ~: \bigcup_(x in U) petal U x in 
  let G' := sgraph.induced T in 
  exists phi : G -> G',
    [/\ total_minor_map phi,
     (forall u : G', val u \in T :\: U -> phi @^-1 u = [set val u]) &
     (forall u : G', val u \in U -> phi @^-1 u = petal U (val u))].
Proof.
  move => T G'.
  have inT0 : u0' \in T by rewrite !inE inU.
  pose u0 : G' := Sub u0' inT0.  
  pose phi u := if [pick x in U | u \in petal U x] is Some x 
                then insubd u0 x else insubd u0 u.
  exists phi.
  have phiU (u : G') : val u \in U -> phi @^-1 u = petal U (val u).
  { move => uU. apply/setP => z. rewrite !inE /phi.
    case: pickP => [x /andP [X1 X2]|H]. 
    - rewrite -val_eqE insubdK ?inE ?X1 //. apply/eqP/idP => [<-//|].
      apply: contraTeq => C. 
      suff S: [disjoint petal U x & petal U (val u)] by rewrite (disjointFr S).
      apply: petal_disj => //; exact: CP_extensive. 
    - move: (H (val u)). rewrite uU /= => ->. 
      have zU : z \notin U. { move: (H z). by rewrite petal_id andbT => ->. }
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
    - have zU : z \notin U. { move: (H z). by rewrite petal_id andbT => ->. }
      have zT : z \in T.
      { rewrite !inE (negbTE zU) /=. apply/negP => /bigcupP [x xU xP].
        move: (H x). by rewrite xU xP. }
      by rewrite -val_eqE insubdK. }
  have preim_G' (u : G') : val u \in phi @^-1 u.
  { case: (boolP (val u \in U)) => H; first by rewrite phiU // petal_id. 
    rewrite phiT ?set11 // inE H. exact: valP. }
  split => //.
  - split. 
    + move => y. exists (val y). apply/eqP. case: (boolP (val y \in U)) => x_inU. 
      * by rewrite mem_preim phiU // petal_id. 
      * rewrite mem_preim phiT inE // x_inU. exact: valP.
    + move => y. case: (boolP (val y \in U)) => xU.
      * rewrite phiU //. apply: connected_petal => //. exact: CP_extensive.
      * rewrite phiT; first exact: connected1. rewrite inE xU. exact: valP.
    + move => x y xy. exists (val x); exists (val y). by rewrite !preim_G'. 
Qed.

End CheckpointsAndMinors.
Arguments collapse_petals [G] conn_G U u0' _.

Definition neighbours (G : sgraph) (x : G) := [set y | x -- y].

(** Proposition 21(i) *)
(* TOTHINK: Is this statement better than the one below? *)
Lemma CP_tree (G : sgraph) (U : {set G}) (G_conn : forall x y : G, connect sedge x y) :
  forall H, minor H (add_node G U) -> K4_free H -> is_tree (CP_ U).
Proof.
  move=> H H_min_GU H_K4F.
  have {H H_min_GU H_K4F} : K4_free (add_node G U).
    by exact: minor_K4_free H_K4F.
  set H := add_node G U => H_K4_free.
Abort.

(** TOTHINK: [[set val x | x in U] = neighbours i] corresponds to what
    is written in the paper. Is there a better way to phrase this? *)
Lemma CP_tree (H : sgraph) (i : H) (U : {set sgraph.induced [set~ i] }) :
  (forall x y : sgraph.induced [set~ i], connect sedge x y) -> 
  K4_free H -> [set val x | x in U] = neighbours i :> {set H} ->
  is_tree (CP_ U).
Proof.
  set G := sgraph.induced _ in U *.
  move => G_conn H_K4_free UisN. 
  suff: ~ exists x y z : CP_ U, [/\ x -- y, y -- z & z -- x] by apply CP_treeI.
  move => [x] [y] [z] [xy yz zx]. apply: H_K4_free. 
  move: (CP_triangle_petals G_conn xy yz zx) => 
    [x'] [y'] [z'] [[x_inU y_inU z_inU] [xX' yY' zZ']].
  set U3 : {set G} := [set val x; val y; val z] in xX' yY' zZ'. 
  pose X := petal U3 (val x). 
  pose Y := petal U3 (val y).
  pose Z := petal U3 (val z).
  have xX : val x \in X by apply: (@petal_id G).  
  have yY : val y \in Y by apply: (@petal_id G).
  have zZ : val z \in Z by apply: (@petal_id G).
  move def_T: (~: (X :|: Y :|: Z)) => T.
  
  pose T' : {set G} := U3 :|: T.
  pose G' := @sgraph.induced G T'.
  
  have xH' : val x \in T' by rewrite !inE eqxx. 
  have yH' : val y \in T' by rewrite !inE eqxx. 
  have zH' : val z \in T' by rewrite !inE eqxx. 

  have def_T' : T' = U3 :|: ~: (\bigcup_(v in U3) petal U3 v).
  { by rewrite {2}/U3 !bigcup_setU !bigcup_set1 /T' -def_T. }

  case: (collapse_petals _ U3 (val x) _) => //.
  { by rewrite !inE eqxx. }
  rewrite -def_T' -/G' => phi [mm_phi P1 P2].

  have irred_inT u v (p : Path G u v) : 
      u \in T' -> v \in T' -> irred p -> {subset p <= T'}.
  { rewrite def_T'. exact: petals_in_out. }
 
  have G'_conn : forall x y : G', connect sedge x y. 
  { apply: connectedTE. apply: connected_induced. 
    move => u v Hu Hv. case/uPathP : (G_conn u v) => p irr_p. 
    apply: (connectRI (p := p)). exact: irred_inT irr_p. }

  have cp_lift u v w : 
    w \in @cp G' u v -> val w \in @cp G (val u) (val v).
  { apply: contraTT => /cpPn' [p] /irred_inT. move/(_ (valP u) (valP v)).
    case/Path_to_induced => q /(_ w) <-. exact: cpNI'. }

  pose x0 : G' := Sub (val x) xH'.
  pose y0 : G' := Sub (val y) yH'.
  pose z0 : G' := Sub (val z) zH'.
  pose H' := @add_node G' [set x0;y0;z0].  

  have link_xy : @link_rel G' x0 y0.
  { rewrite /= -val_eqE /= val_eqE (sg_edgeNeq xy) /=. apply/subsetP.
    move => w /cp_lift. case/andP : (xy) => _ /subsetP S /S. 
    by rewrite !inE !sub_val_eq. }
  have link_yz : @link_rel G' y0 z0.
  { rewrite /= -val_eqE /= val_eqE (sg_edgeNeq yz) /=. apply/subsetP.
    move => w /cp_lift. case/andP : (yz) => _ /subsetP S /S. 
    by rewrite !inE !sub_val_eq. }
  have link_zx : @link_rel G' z0 x0.
  { rewrite /= -val_eqE /= val_eqE (sg_edgeNeq zx) /=. apply/subsetP.
    move => w /cp_lift. case/andP : (zx) => _ /subsetP S /S. 
    by rewrite !inE !sub_val_eq. }

  apply: minor_trans (K4_of_triangle link_xy link_yz link_zx).
  idtac => {link_xy link_yz link_zx}.
  move/map_of_total in mm_phi.
  apply: (minor_with (i := i)) mm_phi; first by rewrite !inE eqxx.
  move => b. rewrite !inE -orbA. case/or3P => /eqP ?; subst b.
  - exists x'. 
    + rewrite !inE Some_eqE mem_preim P2 //; by rewrite !inE eqxx.
    + move/setP/(_ (val x')) : UisN. by rewrite !inE mem_imset // sg_sym. 
  - exists y'. 
    + rewrite !inE Some_eqE mem_preim P2 //; by rewrite !inE eqxx.
    + move/setP/(_ (val y')) : UisN. by rewrite !inE mem_imset // sg_sym.
  - exists z'. 
    + rewrite !inE Some_eqE mem_preim P2 //; by rewrite !inE eqxx.
    + move/setP/(_ (val z')) : UisN. by rewrite !inE mem_imset // sg_sym.
Qed.


Lemma connected2 (G : sgraph) (D : {set G}) : 
  (~ connected D) <-> 
  exists x y, [/\ x \in D, y \in D & ~~ connect (restrict (mem D) sedge) x y].
Admitted.


Lemma ssplit_K4_nontrivial (G : sgraph) (i o : G) : 
  ~~ i -- o -> link_rel G i o -> K4_free (add_edge i o) -> 
  connected [set: G] -> ~ connected (sinterval i o).
Proof.
  move => /= io1 /andP [io2 io3] K4F conn_G. 
  pose G' := @sgraph.induced (add_edge i o) [set~ i].
  set H := add_edge i o in K4F *.
  set U := o |: neighbours i.
  have Ho : o \in [set~ i] by rewrite !inE eq_sym.
  pose o' : G' := Sub o Ho.
  set U' : {set G'} := [set insubd o' x | x in U].
  have tree_CPU' : is_tree (CP_ U').
  { apply: CP_tree K4F _. 
    + (* connectivity *) admit.
    + (* neighbour condition *) admit. }
  have o'_in_U' : o' \in CP U'. 
  { admit. }
  pose N := @neighbours (CP_ U') (Sub o' o'_in_U').
  have Ngt1: 1 < #|N|.
  { suff: 0 < #|N| /\ #|N| != 1. admit.
    split.
    - admit.
    - apply/negP. case/cards1P => z E. 
      (* need that the unique oi-path in CP(U) passes through {z}. Hence, z is a checkpoint *)
      admit.
  }
  case/card_gt1P : Ngt1 => x [y] [Nx Ny xy]. 
  (* TOTHINK: can we avoid nested vals using a proper lemma? *)
  apply/connected2. exists (val (val x)). exists (val (val y)). split.
  - admit. (* whats the argument that the neighbours are in ]]i;o[[ *)
  - admit.
  - admit. (* argue that o, which is not in ]]i;o[[, is a checkpoint beween x an y *)
Admitted.
