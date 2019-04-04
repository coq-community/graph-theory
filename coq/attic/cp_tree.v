From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries digraph sgraph checkpoint minor cp_minor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** This file contains the proof that in a K4-free graph the checkpoint graph of
the set of neighbors of a single node forms a tree. This property was formerly
used to establish the parallel split lemma for term extraction. This proof now
uses Menger's theorem. *)

Section CheckPoints.
  Variables (G : sgraph).
  Implicit Types (x y z : G) (U : {set G}).

  Notation link_graph := (link_graph G).

  Lemma link_cpN (x y z : G) : 
    (x : link_graph) -- y -> z != x -> z != y -> z \notin cp x y.
  Proof using.
    move => /= /andP [_ /subsetP A] B C. apply/negP => /A. 
    by rewrite !inE (negbTE B) (negbTE C).
  Qed.

  Hypothesis G_conn' : connected [set: G].
  Let G_conn : forall x y:G, connect sedge x y.
  Proof using G_conn'. exact: connectedTE. Qed.

  (* Lemma 10 *)
  Lemma link_cycle (p : seq link_graph) : ucycle sedge p -> clique [set x in p].
  Proof using. 
    move => cycle_p x y. rewrite !inE /= => xp yp xy. rewrite /edge_rel/= xy /=.
    case/andP : cycle_p => C1 C2. 
    case: (rot_to_arc C2 xp yp xy) => i p1 p2 _ _ I. 
    have {C1} C1 : cycle sedge (x :: p1 ++ y :: p2) by rewrite -I rot_cycle. 
    have {C2} C2 : uniq (x :: p1 ++ y :: p2) by rewrite -I rot_uniq.
    rewrite /cycle -cat_rcons rcons_cat cat_path last_rcons !rcons_pathp in C1. 
    case/andP : C1 => P1 /pathp_rev P2. 
    move/link_seq_cp in P1. move/link_seq_cp in P2.
    have D: [disjoint p1 & p2].
    { move: C2 => /= /andP [_]. rewrite cat_uniq -disjoint_has disjoint_cons disjoint_sym.
      by case/and3P => _ /andP [_ ?] _. }
    apply: contraTT D. case/subsetPn => z. rewrite !inE negb_or => A /andP [B C].
    move: (subsetP P1 _ A) (subsetP P2 _ A).
    rewrite /srev belast_rcons !(inE,mem_rev,mem_rcons) (negbTE B) (negbTE C) /=.
    exact: disjointNI.
  Qed.

  Lemma cycle_clique (x y : link_graph) (p : Path x y) : 
    irred p -> x -- y -> clique [set x in p].
  Proof using. 
    have -> : [set x in p] = [set x in nodes p].
    { apply/setP => u. by rewrite inE. }
    case: p => p pth_p Ip xy. rewrite irredE nodesE /= in Ip *.
    apply: link_cycle. rewrite /ucycle /= Ip andbT.
    case/andP : pth_p => pth_p /eqP last_p. 
    by rewrite rcons_path pth_p last_p link_sym.
  Qed.


  Lemma CP_clique U : @clique link_graph U -> CP U = U.
  Proof using.
    move => clique_U. apply/setP => x. apply/bigcupP/idP. 
    - case => [[x1 x2]]. rewrite !inE /= => /andP [U1 U2]. 
      move: (clique_U x1 x2 U1 U2). case: (boolP (x1 == x2)) => A B.
      + rewrite (eqP A) cpxx inE. by move/eqP->.
      + case/andP: (B erefl) => _ /subsetP => S /S. by case/setUP => /set1P->.
    - move => inU. by exists (x,x); rewrite ?inE /= ?inU // cpxx inE. 
  Qed.

  Lemma CP_connected (U : {set G}) : connected (CP U).
  Proof using G_conn.
    move=> x y x_cp y_cp.
    have /uPathP[p /(CP_path G_conn' x_cp y_cp)[q] [? q_cp _]] := G_conn x y.
    move/subsetP: q_cp. exact: connectRI.
  Qed.

  Lemma bag_in_out (U : {set G}) x u v (p : Path u v) :
    x \in CP U -> u \in x |: ~: bag U x -> v \in x |: ~: bag U x -> irred p -> 
                                           p \subset x |: ~: bag U x.
  Proof using G_conn.
    move => Ux Pu Pv. apply: contraTT => /subsetPn [w]. 
    rewrite !inE negb_or negbK => in_p /andP [W1 W2]. 
    case/psplitP def_p : _ / in_p => [p1 p2]. subst. 
    rewrite irred_cat !negb_and (_ : _ != _ = true) //.
    apply: contraNN W1 => /eqP/setP/(_ x). rewrite !inE eq_sym => <-.
    gen have H,-> : u p1 Pu / x \in p1. apply/cpP. rewrite cp_sym. exact: bag_exit' Pu.
    by rewrite -mem_prev H. 
  Qed.

  (** This is a bit bespoke, as it only only mentions bags rooted at
elements of [U] rather than [CP U]. At the point where we use it, U is
a clique, so [CP U] is [U]. *)
  Lemma bags_in_out (U : {set G}) u v (p : Path u v) :
    let T' := U :|: (~: \bigcup_(z in U) bag U z) in 
    u \in T' -> v \in T' -> irred p -> {subset p <= T'}.
  Proof using G_conn. 
    move => T' uT vT irr_p. apply/subsetP/negPn/negP.  
    case/subsetPn => z zp. rewrite !inE negb_or negbK => /andP [zU].
    case/bigcupP => x xU zPx. 
    suff HT': {subset T' <= x |: ~: bag U x}. 
    { move/HT' in uT. move/HT' in vT. 
      move/subsetP : (bag_in_out (CP_extensive xU) uT vT irr_p) => sub.
      move/sub : zp. rewrite !inE zPx /= orbF => /eqP ?. by subst z;contrab. }
    move => w. case/setUP => [wU|H].
    + case: (altP (x =P w)) => [->|E]; rewrite !inE ?eqxx // 1?eq_sym.
      rewrite (negbTE E) /=. apply/bagPn; exists w; first exact: CP_extensive.
        by rewrite cpxx inE. 
    + apply/setUP;right. rewrite !inE in H *. apply: contraNN H => wP. 
      apply/bigcupP. by exists x.
  Qed.

  Arguments bagP [G U x z].

  Lemma bag_extension (U : {set G}) x y : 
    x \in CP U -> y \notin bag U x -> bag U x = bag (y |: U) x.
  Proof using G_conn.
    move => CPx Hy. apply/setP => u. apply/idP/bagP.
    - move => A z. 
      have cp_x : x \in cp u y by apply: bag_exit Hy.
      case: (boolP (x == z)) => [/eqP ? _|zx]; first by subst z; apply: (bagP A).
      case/bigcupP => [[v0 v1]] /setXP /= []. 
      have E v : v \in U -> z \in cp y v -> x \in cp u z.
      { move => Hv Hz. case: (cp_mid G_conn' zx Hz) => p1 [p2] [/cpNI|/cpNI] C.
        * apply: contraTT cp_x => ?. exact: cpN_trans C.
        * apply: contraTT A => ?. apply/bagPn. 
          exists v; [exact: CP_extensive|exact: cpN_trans C]. }
      do 2 (case/setU1P => [->|?]). 
      + by rewrite cpxx inE => /eqP->. 
      + exact: E. 
      + rewrite cp_sym. exact: E.
      + move => Hz. apply: (bagP A). apply/bigcupP; exists (v0,v1) => //. exact/setXP.
    - move => A. apply/bagP => z Hz. apply: A. move: z Hz. apply/subsetP. 
      apply: CP_mono. exact: subsetUr.
  Qed.



  Lemma CP_bags {U x y} : link_rel G x y -> x \in CP U -> y \in CP U -> 
    exists x' y', [/\ x' \in U, y' \in U, x' \in bag [set x; y] x & y' \in bag [set x;y] y].
  Proof using G_conn.
    move => xy xU yU. case: (CP_base xU yU) => x' [y'] [Hx' Hy' CPxy].
    case/uPathP : (G_conn x' y') => p irr_p. 
    have [Hx Hy] : x \in p /\ y \in p. 
    { by split; apply: cpP; apply: (subsetP CPxy); rewrite !inE eqxx. }
    rewrite subUset !sub1set in CPxy. case/andP: CPxy => CPx CPy.
    wlog x_before_y : x y Hx Hy xy xU yU CPx CPy / x <[p] y.
    { move => W. 
      case: (ltngtP (idx p x) (idx p y)) => A; first exact: W.
      - case: (W y x) => //; first by rewrite link_sym.
        move => x0 [y0]. rewrite setUC. move => [? ? ? ?]. by exists y0; exists x0.
      - move/idx_inj : A. move/(_ Hx) => ?. subst y. by rewrite /link_rel /= eqxx in xy. }
    case: (three_way_split irr_p Hx Hy x_before_y) => p1 [p2] [p3] [? P1 P3].
    have H2 : CP [set x;y] = [set x;y]. { apply: CP_clique. exact: clique2. }
    exists x';exists y'; split => //. 
    - apply/bagP => ?. rewrite H2. case/set2P=>->; first by rewrite cp_sym mem_cpl.
      apply: contraTT CPx => C. 
      apply: cpN_trans C _. exact: (cpNI (p := p3)).
    - apply/bagP => ?. rewrite H2. case/set2P=>->; last by rewrite cp_sym mem_cpl.
      apply: contraTT CPy => C. rewrite cp_sym in C. 
      apply: cpN_trans C. exact: (cpNI (p := p1)).
  Qed.
  
  Lemma CP_triangle_bags U (x y z : link_graph) : 
    x \in CP U -> y \in CP U -> z \in CP U ->
    x -- y -> y -- z -> z -- x -> 
    let U3 : {set G} := [set x; y; z] in
    exists x' y' z' : G, 
      [/\ x' \in U, y' \in U & z' \in U] /\ 
      [/\ x' \in @bag G U3 x, y' \in @bag G U3 y & z' \in @bag G U3 z].
  Proof with try (apply: CP_extensive; rewrite ?inE ?eqxx //).
    move => x_cp y_cp z_cp xy yz zx.
    gen have T,_ : x y z x_cp y_cp z_cp xy yz zx / z \notin @cp G x y.
    { case/andP : xy => _ /subsetP S. apply/negP => /S. 
      case/set2P=> ?; subst; by rewrite sg_irrefl in zx yz. }
    move => U3.
    case: (CP_bags xy x_cp y_cp) => x' [y'] [xU yU Px Py].
    case: (CP_bags yz y_cp z_cp) => _ [z'] [_ zU _ Pz].
    have zPx : z \notin @bag G [set x; y] x.
    { apply/(@bagPn G). exists y...  apply T => //; by rewrite sg_sym. }
    have zPy : z \notin @bag G [set x; y] y.
    { apply/(@bagPn G). exists x... apply T => //; by rewrite sg_sym. }
    have xPz : x \notin @bag G [set y; z] z.
    { apply/(@bagPn G). exists y... exact: T. }
    exists x';exists y';exists z'. split => //. split.
    - rewrite /U3 setUC -bag_extension //... 
    - rewrite /U3 setUC -bag_extension //... 
    - rewrite /U3 -setUA -bag_extension //...
  Qed.

End CheckPoints.

Arguments ncp0 [G] G_conn [U] x p : rename.
 
Lemma CP_treeI (G : sgraph) (U : {set G}) : connected [set: G] ->
  {in CP U & &, forall x y z, x -- y -> y -- z -> z -- x -> False} ->
  is_tree (CP U).
Proof.
  move=> G_conn noCPtri. split; last exact: CP_connected.
  move=> x y p1 p2 [Ip1 p1_cp] [Ip2 p2_cp].
  case: (altP (p1 =P p2)) => // pN12. exfalso.
  (* W.l.o.g. p1 and p2 differ already at their second vertex. *)
  wlog : x p1 p2 Ip1 Ip2 p1_cp p2_cp pN12 /
        exists z1 z2 (xz1 : x -- z1) (xz2 : x -- z2) q1 q2,
        [/\ z1 != z2, p1 = pcat (edgep xz1) q1 & p2 = pcat (edgep xz2) q2].
  { move=> Hyp. move: p1_cp p2 Ip2 p2_cp pN12. pattern x, y, p1.
    revert x p1 Ip1. apply irred_ind; first by move=> _ p2 /irredxx->.
    move=> x z1 q1 xz1 Iq1 xNq1 IH p1_cp p2 Ip2 p2_cp pN12.
    case: (altP (x =P y)) xNq1 => [->|xNy xNq1]; first by rewrite path_end.
    case: (splitL p2 xNy) Ip2 p2_cp pN12 => [z2] [xz2] [q2] [-> _].
    case: (altP (z1 =P z2)) xz2 q2 => [<-|zN12] xz2 q2 Ip2 p2_cp pN12.
    - apply: (IH _ q2).
      + by apply/subsetP=> u u_q1; apply: (subsetP p1_cp); rewrite mem_pcat u_q1.
      + by move: Ip2; rewrite irred_cat; case/and3P.
      + by apply/subsetP=> u u_q2; apply: (subsetP p2_cp); rewrite mem_pcat u_q2.
      + apply: contraNneq pN12 =>->.
        by have -> : xz1 = xz2 by exact: bool_irrelevance.
    - apply: (Hyp x (pcat (edgep xz1) q1) (pcat (edgep xz2) q2)) => //.
      + rewrite irred_cat irred_edge Iq1. apply/eqP/setP=> u.
        rewrite inE in_set1 mem_edgep.
        apply/andP/eqP=> [|->]; last by rewrite eqxx path_begin.
        case; case/orP=> /eqP-> //. by rewrite (negbTE xNq1).
      + by repeat eexists. }
  move=> [z1] [z2] [xz1] [xz2] [q1] [q2] [zN12 eq_p1 eq_p2].
  have x_cp : x \in CP U by apply: (subsetP p1_cp); rewrite path_begin.
  have [z1_cp z2_cp] : z1 \in CP U /\ z2 \in CP U.
  { split; [move: eq_p1 p1_cp | move: eq_p2 p2_cp]=> -> /subsetP; apply;
    by rewrite mem_pcat path_begin. }
  (* The vertices of the triangle are z1, z2 and x. Two of the edges are obvious... *)
  apply: (noCPtri x z1 z2) => //; last by rewrite sg_sym.
  (* ... and for the third edge we construct an irredundant cycle *)
  have [p Ip xNp] : exists2 p : Path z1 z2, irred p & x \notin p.
  { case: (uncycle (pcat q1 (prev q2))) => p p_sub Ip. exists p => //.
    apply/negP=> /p_sub. rewrite mem_pcat mem_prev.
    move: Ip1 Ip2. rewrite eq_p1 eq_p2 !irred_edgeL.
    by do 2 case/andP=> /negbTE-> _. }
  have /cycle_clique : irred (pcat (edgep xz1) p) by rewrite irred_edgeL xNp Ip.
  by apply=> //; rewrite inE mem_pcat ?path_begin ?path_end.
Qed.

(** ** K4 of link triangle *)

Lemma linkNeq (G : sgraph) (x y : link_graph G) : x -- y -> x != y.
Proof. move => A. by rewrite sg_edgeNeq. Qed.

Lemma ins (T : finType) (A : pred T) x : x \in A -> x \in [set z in A].
Proof. by rewrite inE. Qed.

Section CheckpointsAndMinors.
Variables (G : sgraph).
Hypothesis (conn_G : connected [set: G]).

Lemma C3_of_triangle (x y z : link_graph G) : 
  x -- y -> y -- z -> z -- x -> exists2 phi : G -> option C3, 
  minor_map phi & [/\ phi x = Some ord0, phi y = Some ord1 & phi z = Some ord2].
Proof.
  move => xy yz zx.
  have/cpPn [p irr_p av_z] : (z:G) \notin @cp G x y. 
  { apply: link_cpN => //; apply: linkNeq => //. by rewrite sg_sym. }
  have/cpPn [q irr_q av_x] : (x:G) \notin @cp G z y.
  { apply: link_cpN => //; first (by rewrite sg_sym) ;apply: linkNeq => //. 
    by rewrite sg_sym. }
  have [Yq Yp] : y \in q /\ y \in p by split;apply: path_end.
  case: (split_at_first (D := G) (A := mem p) Yp Yq) => n1 [q1] [q2] [def_q Q1 Q2]. 
  have Hn : n1 != x.
  { apply: contraNN av_x => /eqP<-. by rewrite def_q mem_pcat path_end. }
  have {q irr_q av_x Yq def_q q2 Yp} irr_q1 : irred q1 by subst; case/irred_catE :irr_q.
  have/cpPn [q irr_q av_n1] : n1 \notin @cp G z x. 
  { apply link_cpN => //. apply: contraNN av_z => /eqP?. by subst n1. }
  have [Xq Xp] : x \in q /\ x \in p by split; rewrite /= ?path_end ?path_begin. 
  case: (split_at_first (D := G) (A := mem p) Xp Xq) => n2 [q2] [q2'] [def_q Q3 Q4].
  have N : n1 != n2. 
  { apply: contraNN av_n1 => /eqP->. by rewrite def_q mem_pcat path_end. }
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
    { move: irr_q1. rewrite def_q1 irred_edgeR. by case (_ \in _). }
    rewrite disjoint_subset; apply/subsetP => z' Hz'. rewrite !inE.
    apply: contraNN A => A. 
    by rewrite -[n1](Q2 _ Hz' _) // def_q1 mem_pcat A. }
  have {D} D2 : [disjoint p & q2'] by apply: (D z2 n2 q2 q2' zn2).
  case/(isplitP irr_p) def_p : p / Q1 => [p1 p2 _ irr_p2 D3'].
  have N2 : n2 \in tail p2. { subst p. by rewrite -idxR in before. }
  have N1 : n1 != y. 
  { apply: contraTN before => /eqP->. by rewrite -leqNgt idx_end // idx_mem. }
  case: (splitL p2 N1) => n1' [n_edge] [p2'] [def_p2 tail_p2].
  have N2' : n2 \in p2' by rewrite tail_p2.
  (* TODO: This is a local fix to accomodate change in isplitP *)
  have {D3'} D3 : [disjoint p1 & tail p2].
  { rewrite disjoint_subset. apply/subsetP => k K1. apply/negP => /= K2.
    move: (D3' _ K1 (tailW K2)) => X. subst k. subst p2.
    by rewrite irred_edgeL tail_p2 K2 in irr_p2. }  
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
    move => u. by rewrite !inE (* mem_pcat mem_prev. *). }
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
  { by rewrite /= mem_pcat ?path_begin ?path_end. }
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
        rewrite [pz]lock !inE -lock /phi. by case: (disjoint3P u D).
    + move => c1 c2.
      wlog: c1 c2 / c1 < c2.
      { move => W. case: (ltngtP c1 c2) => [|A B|A B]; first exact: W.
        - case: (W _ _ A _) => [|y0 [x0] [? ? ?]]; first by rewrite sgP. 
          exists x0; exists y0. by rewrite sgP.
        - move/ord_inj : A => ?. subst. by rewrite sgP in B. }
      case: c1 => [[|[|[|//]]]]; case: c2 => [[|[|[|//]]]] //= Hc2 Hc1 _ _. 
      * exists n1. exists n1'. rewrite !inE n_edge. split => //.
        -- rewrite /phi. by case: (disjoint3P n1 D) (path_end p1). 
        -- rewrite /phi. by case: (disjoint3P n1' D) (path_begin p2'). 
      * exists n1. exists z1. rewrite !inE sg_sym zn1. split => //.
        -- rewrite /phi. by case: (disjoint3P n1 D) (path_end p1). 
        -- rewrite /phi. by case: (disjoint3P z1 D) (path_begin pz). 
      * exists n2. exists z2. rewrite !inE sg_sym zn2. split => //.
        -- rewrite /phi. by case: (disjoint3P n2 D) N2'.
        -- rewrite /phi. by case: (disjoint3P z2 D) (path_end pz). 
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

End CheckpointsAndMinors. 

Lemma CP_tree (G : sgraph) (U : {set G}) :
  connected [set: G] -> K4_free (add_node G U) -> is_tree (CP U).
Proof.
  set H := add_node G U.
  move => G_conn H_K4_free.
  apply: CP_treeI => // x y z x_cp y_cp z_cp xy yz zx.
  apply: H_K4_free.
  move: (CP_triangle_bags G_conn x_cp y_cp z_cp xy yz zx) =>
    [x'] [y'] [z'] [[x_inU y_inU z_inU] [xX' yY' zZ']].
  set U3 : {set G} := [set x; y; z] in xX' yY' zZ'.
  pose X := bag U3 x.
  pose Y := bag U3 y.
  pose Z := bag U3 z.
  have xX : x \in X by apply: (@bag_id G).
  have yY : y \in Y by apply: (@bag_id G).
  have zZ : z \in Z by apply: (@bag_id G).
  move def_T: (~: (X :|: Y :|: Z)) => T.
  pose T' : {set G} := U3 :|: T.
  pose G' := @sgraph.induced G T'.
  
  have xH' : x \in T' by rewrite !inE eqxx.
  have yH' : y \in T' by rewrite !inE eqxx.
  have zH' : z \in T' by rewrite !inE eqxx.

  have def_T' : T' = U3 :|: ~: (\bigcup_(v in U3) bag U3 v).
  { by rewrite {2}/U3 !bigcup_setU !bigcup_set1 /T' -def_T. }

  case: (collapse_bags _ U3 x _) => //.
  { by rewrite !inE eqxx. }
  rewrite -def_T' -/G' => phi [mm_phi P1 P2].

  have irred_inT u v (p : Path u v) : 
      u \in T' -> v \in T' -> irred p -> {subset p <= T'}.
  { rewrite def_T'. exact: bags_in_out. }
 
  have G'_conn : forall x y : G', connect sedge x y. 
  { apply: connectedTE. apply: connected_induced. 
    move => u v Hu Hv. case/uPathP : (connectedTE G_conn u v) => p irr_p. 
    apply: (connectRI (p := p)). exact: irred_inT irr_p. }

  have cp_lift u v w : 
    w \in @cp G' u v -> val w \in @cp G (val u) (val v).
  { apply: contraTT => /cpPn [p] /irred_inT. move/(_ (valP u) (valP v)).
    case/Path_to_induced => q eq_nodes.
    rewrite in_collective -eq_nodes (mem_map val_inj).
    exact: cpNI. }

  pose x0 : G' := Sub x xH'.
  pose y0 : G' := Sub y yH'.
  pose z0 : G' := Sub z zH'.
  (* pose H' := @add_node G' [set x0;y0;z0]. *)

  have link_xy : @link_rel G' x0 y0.
  { rewrite /= -val_eqE (sg_edgeNeq xy) /=. apply/subsetP.
    move => w /cp_lift. case/andP : (xy) => _ /subsetP S /S. 
    by rewrite !inE !sub_val_eq. }
  have link_yz : @link_rel G' y0 z0.
  { rewrite /= -val_eqE (sg_edgeNeq yz) /=. apply/subsetP.
    move => w /cp_lift. case/andP : (yz) => _ /subsetP S /S. 
    by rewrite !inE !sub_val_eq. }
  have link_zx : @link_rel G' z0 x0.
  { rewrite /= -val_eqE (sg_edgeNeq zx) /=. apply/subsetP.
    move => w /cp_lift. case/andP : (zx) => _ /subsetP S /S. 
    by rewrite !inE !sub_val_eq. }

  apply: minor_trans (K4_of_triangle link_xy link_yz link_zx).
  idtac => {link_xy link_yz link_zx}.
  rewrite /H. apply: add_node_minor mm_phi.
  move => b. rewrite !inE -orbA. case/or3P => /eqP ?; subst b.
  - exists x' => //. apply/eqP. rewrite mem_preim P2 //. by rewrite !inE eqxx.
  - exists y' => //. apply/eqP. rewrite mem_preim P2 //. by rewrite !inE eqxx.
  - exists z' => //. apply/eqP. rewrite mem_preim P2 //. by rewrite !inE eqxx.  
Qed.
