From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries digraph sgraph connectivity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 

(** * Checkpoints *)

Section CheckPoints.
  Variables (G : sgraph).
  Implicit Types (x y z : G) (U : {set G}).

  Definition cp x y := locked [set z | separatorb G [set x] [set y] [set z]].

  Lemma cpPn x y z : reflect (exists2 p : Path x y, irred p & z \notin p) (z \notin cp x y).
  Proof. 
    rewrite /cp -lock inE. apply: (iffP (separatorPn _ _ _)).
    - move => [x0] [y0] [p] [/set1P ? /set1P ?]; subst x0 y0.
      rewrite disjoint_sym disjoints1. by exists p.
    - move => [p Ip zNp]. exists x; exists y; exists (Build_IPath Ip). 
      by rewrite disjoint_sym disjoints1 !inE !eqxx. 
  Qed.

  Lemma cpNI x y (p : Path x y) z : z \notin p -> z \notin cp x y.
  Proof using. 
    case: (uncycle p) => p' S irr_p' av_z. apply/cpPn. exists p' => //.
    apply: contraNN av_z. exact: S.
  Qed.
  
  Lemma cpP x y z : reflect (forall p : Path x y, z \in p) (z \in cp x y).
  Proof using. 
    apply: introP. 
    - move => cp_z p. apply: contraTT cp_z. exact: cpNI.
    - case/cpPn => p _ av_z /(_ p). exact/negP.
  Qed.
  Arguments cpP {x y z}.

  Lemma cpTI x y z : (forall p : Path x y, irred p -> z \in p) -> z \in cp x y.
  Proof using. move => H. by apply/cpPn => [[p] /H ->]. Qed.  

  Hypothesis G_conn' : connected [set: G].
  Let G_conn : forall x y:G, connect sedge x y.
  Proof using G_conn'. exact: connectedTE. Qed.

  Lemma cp_sym x y : cp x y = cp y x.
  Proof using.
    wlog suff S : x y / cp x y \subset cp y x. 
    { apply/eqP. by rewrite eqEsubset !S. }
    apply/subsetP => z /cpP H. apply/cpP => p. 
    move: (H (prev p)). by rewrite mem_prev.
  Qed.

  Lemma mem_cpl x y : x \in cp x y.
  Proof. apply/cpP => p. by rewrite path_begin. Qed.

  Lemma subcp x y : [set x;y] \subset cp x y.
  Proof. by rewrite subUset !sub1set {2}cp_sym !mem_cpl. Qed.

  Lemma cpxx x : cp x x = [set x].
  Proof using. 
    apply/eqP. rewrite eqEsubset sub1set mem_cpl andbT.
    apply/subsetP => z /cpP /(_ (idp x)). by rewrite !inE mem_idp.
  Qed.

  Lemma cp_triangle z {x y} : cp x y \subset cp x z :|: cp z y.
  Proof using.
    apply/subsetP => u /cpP => A. apply: contraT. 
    rewrite !inE negb_or => /andP[/cpPn [p1 _ up1]] /cpPn [p2 _ up2]. 
    move: (A (pcat p1 p2)). by rewrite mem_pcat (negbTE up1) (negbTE up2).
  Qed.
  
  Lemma cpN_trans a x z y : a \notin cp x z -> a \notin cp z y -> a \notin cp x y.
  Proof using. 
    move => /negbTE A /negbTE B. apply/negP. move/(subsetP (cp_triangle z)). 
    by rewrite !inE A B.
  Qed.

  Lemma cp_mid (z x y t : G) : t != z -> z \in cp x y ->
   exists (p1 : Path z x) (p2 : Path z y), t \notin p1 \/ t \notin p2.
  Proof using G_conn. 
    move => tNz cp_z.
    case/connect_irredP : (G_conn x y) => p irr_p.
    move/cpP/(_ p) : cp_z. case/(isplitP irr_p) => p1 p2 A B C.
    exists (prev p1). exists p2. rewrite mem_prev. apply/orP. 
    case E : (t \in p1) => //=. 
    apply: contraNN tNz => F. by rewrite [t]C.
  Qed.

  Lemma cp_widenR (x y u v : G) :
    u \in cp x y -> v \in cp x u -> v \in cp x y.
  Abort.

  Lemma cp_widen (i o x y z : G) :
    x \in cp i o -> y \in cp i o -> z \in cp x y -> z \in cp i o.
  Proof using.
    move=> x_cpio y_cpio z_cpxy. apply: cpTI => p Ip.
    move: x_cpio y_cpio => /cpP/(_ p) x_p /cpP/(_ p) y_p.
    wlog : x y z_cpxy p Ip x_p y_p / x <[p] y.
    { move=> Hyp. case: (ltngtP (idx p x) (idx p y)); first exact: Hyp.
      - by apply: Hyp; first rewrite cp_sym.
      - move=>/(idx_inj x_p) x_y.
        by move: z_cpxy; rewrite -{1}x_y cpxx inE =>/eqP->. }
    case/(three_way_split Ip x_p y_p) => [p1][p2][p3][-> _ _].
    rewrite !mem_pcat. by move: z_cpxy => /cpP/(_ p2)->.
  Qed.

  Lemma cp_tightenR (x y z u : G) : z \in cp x y -> x \in cp u y -> x \in cp u z.
  Proof using G_conn.
    move=> z_cpxy x_cpuy. apply/cpP => pi.
    case/connect_irredP: (G_conn z y) => pi_o irred_o.
    move/cpP/(_ (pcat pi pi_o)): x_cpuy.
    rewrite mem_pcatT => /orP[//|x_tail]; exfalso.
    case: (altP (z =P y)). (* TODO: worth a lemma *)
    { move=> eq_z; move: pi_o irred_o x_tail.
      by rewrite -eq_z => pi_o /irredxx->. }
    case/(splitL pi_o) => [v] [zv] [pi'] [eq_pio eq_tail].
    rewrite -{}eq_tail in x_tail.
    move: irred_o. rewrite eq_pio irred_edgeL => /andP[zNpi' Ipi'].
    move: zNpi'; apply/idP.
    case: (isplitP Ipi' x_tail) z_cpxy => [p1 p2 _ _ _] /cpP/(_ p2).
    by rewrite mem_pcat =>->.
  Qed.

  (* The two-sided version of the previous lemma, not used. *)
  Lemma cp_tighten (i o p x y : G) :
    i \in cp x p -> o \in cp p y -> p \in cp x y -> p \in cp i o.
  (* Proof sketch:
   * Let [pi : Path i o]. By connectedness, there are irredundant paths
   * [pi_i : Path x i] and [pi_o : Path o y]. Then [p] must be in the
   * concatenation [pi_i ++ pi ++ pi_o]. It cannot be in the tail of [pi_o]
   * because [o \in cp p z] but [pi_o] is assumed to be irredundant. A
   * symmetrical reasoning for [pi_i] shows that [p \in pi].             Qed. *)
  Abort.
  
  Lemma cp_neighbours (x y : G) z : x != y ->
    (forall x' (p : Path x' y), x -- x' -> irred p -> x \notin p -> z \in p) ->
    z \in cp x y.
  Proof using.
    move=> xNy H. apply: cpTI => p.
    case: (splitL p xNy) => [x'] [xx'] [p'] [-> _].
    rewrite irred_edgeL => /andP[xNp' Ip]. by rewrite mem_pcat H.
  Qed.

  Lemma connected_cp_closed (x y : G) (V : {set G}) :
    connected V -> [set x; y] \subset V -> cp x y \subset V.
  Proof using.
    move=> V_conn. rewrite subUset !sub1set. case/andP=> Hx Hy.
    case: (altP (x =P y)) => [<-|xNy]; first by rewrite cpxx sub1set.
    have[p _ /subsetP pV] := connect_irredRP xNy (V_conn x y Hx Hy).
    by apply/subsetP=> u /cpP/(_ p)/pV.
  Qed.

  (** ** Link Graph *)

  Definition link_rel := [rel x y | (x != y) && (cp x y \subset [set x; y])].

  Lemma link_sym : symmetric link_rel.
  Proof. move => x y. by rewrite /= eq_sym cp_sym set2C. Qed.

  Lemma link_irrefl : irreflexive link_rel.
  Proof. move => x /=. by rewrite eqxx. Qed.

  Definition link_graph := SGraph link_sym link_irrefl.

  Local Notation "x ⋄ y" := (@sedge link_graph x y) (at level 30).


  Lemma link_avoid (x y z : G) : 
    z \notin [set x; y] -> link_rel x y -> exists2 p, pathp x y p & z \notin (x::p).
  Abort. (* not acutally used *)

  Lemma link_seq_cp (y x : G) p :
    @pathp link_graph x y p -> cp x y \subset x :: p.
  Proof using.
    elim: p x => [|z p IH] x /=.
    - move/pathp_nil->. rewrite cpxx. apply/subsetP => z. by rewrite !inE.
    - rewrite pathp_cons => /andP [/= /andP [A B] /IH C]. 
      apply: subset_trans (cp_triangle z) _.
      rewrite subset_seqR. apply/subUsetP; split. 
      + apply: subset_trans B _. by rewrite !set_cons setUA subsetUl.
      + apply: subset_trans C _. by rewrite set_cons subset_seqL subsetUr.
  Qed.

  Lemma link_path_cp (x y : G) (p : @Path link_graph x y) : 
    {subset cp x y <= p}.
  Proof using. 
    apply/subsetP. rewrite /in_nodes nodesE. apply: link_seq_cp.
    exact: (valP p). 
  Qed.



  (** ** CP Closure Operator *)

  (* NOTE: The nodes of G and its link graph are the same, but CP U usually makes
   * more sense as a subgraph of the link graph (e.g. for is_tree). *)
  Definition CP (U : {set G}) : {set link_graph} := \bigcup_(xy in setX U U) cp xy.1 xy.2.
  
  Unset Printing Implicit Defensive.

  Lemma CP_set2 (x y : G) : CP [set x; y] = cp x y.
  Proof using.
    apply/setP => z. apply/bigcupP/idP => /=.
    + case=> -[a b] /=/setXP[].
      rewrite !inE =>/orP[]/eqP->; last rewrite (cp_sym x y);
      move=>/orP[]/eqP->//; rewrite cpxx inE => /eqP->; by rewrite mem_cpl.
    + move=> Hz. exists (x, y) => //. by apply/setXP; rewrite !inE !eqxx.
  Qed.
  
  Lemma CP_extensive (U : {set G}) : {subset U <= CP U}.
  Proof using.
    move => x inU. apply/bigcupP; exists (x,x); by rewrite ?inE /= ?inU // cpxx inE.
  Qed.

  (** was only used in the CP_tree lemma, but we keep it here *)
  Lemma CP_mono (U U' : {set G}) : U \subset U' -> CP U \subset CP U'.
  Proof using. 
    move/subsetP => A. apply/bigcupsP => [[x y] /setXP [/A Hx /A Hy] /=].
    apply/subsetP => z Hz. apply/bigcupP; exists (x,y) => //. exact/setXP.
  Qed.
  
  Lemma CP_closed U x y : 
    x \in CP U -> y \in CP U -> cp x y \subset CP U.
  Proof using G_conn.
    case/bigcupP => [[x1 x2] /= /setXP [x1U x2U] x_cp]. 
    case/bigcupP => [[y1 y2] /= /setXP [y1U y2U] y_cp]. 
    apply/subsetP => t t_cp. 
    case (boolP (t == y)) => [/eqP-> //|T2].
    { apply/bigcupP. exists (y1,y2); by [exact/setXP|]. }
    case (boolP (t == x)) => [/eqP-> //|T1].
    { apply/bigcupP. exists (x1,x2); by [exact/setXP|]. }
    move: (cp_mid T1 x_cp) => [p1] [p2] H.
    wlog P1 : x1 x2 p1 p2 x1U x2U x_cp H / t \notin p1 => [W|{H}].
    { case: H => H. 
      - by apply : (W _ _ p1 p2) => //; tauto.
      - rewrite cp_sym in x_cp. apply : (W _ _ p2 p1) => //; tauto. }
    move: (cp_mid T2 y_cp) => [q1] [q2] H.
    wlog P2 : y1 y2 q1 q2 y1U y2U y_cp H / t \notin q1 => [W|{H}].
    { case: H => H. 
      - by apply : (W _ _ q1 q2) => //; tauto.
      - rewrite cp_sym in y_cp. apply : (W _ _ q2 q1) => //; tauto. }
    apply/bigcupP; exists (x1,y1) => /= ; first exact/setXP. 
    apply: contraTT t_cp => /cpPn [s _ Hs]. 
    suff: t \notin (pcat p1 (pcat s (prev q1))) by apply: cpNI.
    by rewrite !mem_pcat !mem_prev (negbTE P1) (negbTE P2) (negbTE Hs).
  Qed.

  Lemma connected_CP_closed (U V : {set G}) :
    connected V -> U \subset V -> CP U \subset V.
  Proof using.
    move=> V_conn /subsetP UV. apply/bigcupsP. case=> x y /=. rewrite in_setX.
    case/andP=> /UV Hx /UV Hy. apply: connected_cp_closed => //.
    by rewrite subUset !sub1set.
  Qed.

  (* Lemma 16 *)
  Lemma CP_base U x y : x \in CP U -> y \in CP U ->
    exists x' y':G, [/\ x' \in U, y' \in U & [set x;y] \subset cp x' y'].
  Proof using.
    move => U1 U2. case/bigcupP : U1 => [[x1 x2]]. case/bigcupP : U2 => [[y1 y2]] /=.
    rewrite !inE /= => /andP[Uy1 Uy2] cp_y /andP[Ux1 Ux2] cp_x.
    case: (boolP (x \in cp y1 y2)) => [C|Wx]; first by exists y1; exists y2; rewrite subUset !sub1set C.
    case: (boolP (y \in cp x1 x2)) => [C|Wy]; first by exists x1; exists x2; rewrite subUset !sub1set C.
    gen have H,A: x x1 x2 y1 y2 {Ux1 Ux2 Uy1 Uy2 Wy cp_y} Wx cp_x /
      (x \in cp x1 y1) || (x \in cp x2 y2).
    { (* TODO: use transitivity *)
      case/cpPn : Wx => p irr_p av_x. 
      apply: contraTT cp_x. rewrite negb_or => /andP[/cpPn [s s1 s2] /cpPn [t t1 t2]].
      apply (cpNI (p := pcat s (pcat p (prev t)))). 
      by rewrite !mem_pcat !mem_prev (negbTE av_x) (negbTE s2) (negbTE t2). }
    have {H} B : (y \in cp x1 y1) || (y \in cp x2 y2).
    { rewrite -(cp_sym y1 x1) -(cp_sym y2 x2). exact: H. }
    wlog {A} /andP [Hx Hy] : x1 x2 y1 y2 A B cp_x cp_y Ux1 Ux2 Uy1 Uy2 Wx Wy
        / (x \in cp x1 y1) && (y \notin cp x1 y1).
    { case: (boolP (y \in cp x1 y1)) A B => A; case: (boolP (x \in cp x1 y1)) => /= B C D W. 
      - by exists x1; exists y1; rewrite subUset !sub1set B. 
      - (* TOTHINK: why the second case anlysis in this case? *)
        case: (boolP (y \in cp x2 y2)) => E. 
        + exists x2; exists y2; by rewrite subUset !sub1set C.
        + move: (W x2 x1 y2 y1). rewrite (cp_sym x2 x1) (cp_sym y2 y1) A C /= orbT. exact.
      - apply: (W x1 x2 y1 y2) => //. by rewrite B. by rewrite D.
      - exists x2; exists y2; by rewrite subUset !sub1set C D. }
    rewrite (negbTE Hy) /= in B.
    case: (boolP (x \in cp x2 y2)) => [C|Wx']; first by exists x2; exists y2; rewrite subUset !sub1set C.
    exists x1. exists y2. rewrite subUset !sub1set. split => //. apply/andP; split.
    - apply: contraTT cp_x => C. apply: cpN_trans C _. by rewrite cp_sym.
    - apply: contraTT cp_y. apply: cpN_trans. by rewrite cp_sym.
  Qed.


  (** *** Checkpoint graph *)

  Arguments Path : clear implicits.
  Arguments pathp : clear implicits.

  (* Lemma 14 *)
  Lemma CP_path (U : {set G}) (x y : G) (p : Path G x y) :
    x \in CP U -> y \in CP U -> irred p ->
    exists q : Path link_graph x y, [/\ irred q, q \subset CP U & q \subset p].
  Proof using G_conn.
    (* The proof goes by strong induction on the size of p. *)
    move: {2}#|p|.+1 (ltnSn #|p|) => n.
    elim: n x y p => [//|n IHn] x y p.
    rewrite ltnS leq_eqVlt => /orP[/eqP size_p x_cp y_cp Ip|]; last exact: IHn.
    case: (x =P y) => [x_y | /eqP xNy].
    { (* When x = y, the empty path works. (Actually, p is empty too.) *)
      move: x_y p size_p Ip => {y y_cp}<- p _ _.
      exists (@idp link_graph x); split; first exact: irred_idp;
        apply/subsetP=> z; rewrite mem_idp => /eqP-> //=.
      by rewrite path_end. }
    (* When x != y, split the path and apply the induction hypothesis. To avoid
     * getting a useless decomposition, x is excluded from the predicate. *)
    pose C := CP U :\ x.
    (* Use y as a witness of the existence of a splitting point. *)
    have {xNy} : y \in C by rewrite in_setD1 eq_sym xNy y_cp.
    (* Let z be the first element in CP(U) after x on p. Call p1 and p2 the
     * parts of p respectively before and after z. *)
    case/split_at_first/(_ (path_end p)) => [z][p1][p2] [eq_p z_C z_1st].
    move: z_C Ip. rewrite in_setD1 eq_p irred_cat => /andP[zNx z_cp] /and3P[Ip1 Ip2].
    move/eqP/setP/(_ x). rewrite inE in_set1 path_begin/= eq_sym (negbTE zNx) => /negbT xNp2.
    (* Apply the induction hypothesis to get an irreducible path q using only
     * vertices in p2. *)
    have /IHn /(_ z_cp y_cp Ip2) [q[] Iq q_cp qSp2] : #|p2| < n. {
      (* The size decreases because x cannot be a splitting point. *)
      rewrite -size_p. apply: proper_card. apply/properP.
      split; last exists x => //; last exact: path_begin.
      by apply/subsetP => a; rewrite eq_p mem_pcat => ->.
    }
    (* All checkpoints for (x, z) are in p1 (by definition of a checkpoint) and
     * in CP(U) (by closure). Finally, z is by definition the only vertex on p1
     * and in CP(U) that isn't x. *)
    have xz : @sedge link_graph x z.
    { rewrite /= eq_sym zNx. apply/subsetP => u u_cpxz. rewrite !in_set2 -implyNb.
      apply/implyP=> uNx. apply/eqP. have /cpP/(_ p1) := u_cpxz. apply: z_1st.
      rewrite in_setD1 {}uNx /=. move: u u_cpxz. apply/subsetP. exact: CP_closed. }
    (* Thus there is an x -- z edge in CP(U) that can be prepended to q.
     * That's the path that was looked for. *)
    exists (pcat (edgep xz) q); split.
    - rewrite irred_cat irred_edge Iq /=. apply/eqP/setP=> u.
      rewrite inE in_set1 (@mem_edgep link_graph).
      apply/andP/eqP; [ case; case/orP=>/eqP->// | move=>->; by rewrite eqxx (path_begin q) ].
      move/(subsetP qSp2). by rewrite (negbTE xNp2).
    - apply/subsetP=> u. rewrite (@mem_pcat link_graph) mem_edgep -orbA.
      case/or3P=> [/eqP->|/eqP->|/(subsetP q_cp)->] //.
    - apply/subsetP=> u. rewrite (@mem_pcat link_graph) mem_pcat mem_edgep -orbA.
      case/or3P=> [/eqP->|/eqP->|/(subsetP qSp2)->//];
        by [ rewrite path_begin | rewrite path_end ].
  Qed.


  (**: If [CP_ U] is a tree, the uniqe irredundant path bewteen any
  two nodes contains exactly the checkpoints bewteen these nodes *)
  Lemma CP_tree_paths (U : {set G}) (x y : G) (p : Path link_graph x y) : 
    is_tree (CP U) -> p \subset CP U -> irred p ->
    {in CP U, p =i cp x y}.
  Proof using G_conn.
    move=> [CPU_tree _] p_cp Ip z z_cp. apply/idP/idP; last exact: link_path_cp.
    have [x_cp y_cp] : x \in CP U /\ y \in CP U.
    { split; apply: (subsetP p_cp); by rewrite ?path_begin ?path_end. }
    move=> z_p. apply: cpTI => q0 /(CP_path x_cp y_cp)[q] [Iq q_cp /subsetP q_sub].
    apply: q_sub. by have -> : q = p by exact: CPU_tree.
  Qed.

  Arguments Path : default implicits.
  Arguments pathp : default implicits.

  (** ** Intervals and bags *)

  (** *** Strict intervals *)

  Definition sinterval x y := [set u | (x \notin cp u y) && (y \notin cp u x)].

  Lemma sinterval_sym x y : sinterval x y = sinterval y x.
  Proof. apply/setP => p. by rewrite !inE andbC. Qed.

  Lemma sinterval_bounds x y : (x \in sinterval x y = false) * 
                               (y \in sinterval x y = false).
  Proof. by rewrite !inE !mem_cpl andbF. Qed.

  Lemma sintervalP2 x y u :
    reflect ((exists2 p : Path u x, irred p & y \notin p) /\
             (exists2 q : Path u y, irred q & x \notin q)) (u \in sinterval x y).
  Proof using.
    apply/(iffP idP).
    + rewrite !inE => /andP[/cpPn ? /cpPn ?] //.
    + case=>- [p] Ip yNp [q] Iq xNq. rewrite !inE. 
      apply/andP;split; [exact: cpNI xNq|exact: cpNI yNp].
  Qed.

  Lemma sinterval_sub x y z : z \in cp x y -> sinterval x z \subset sinterval x y.
  Proof using G_conn.
    move=> z_cpxy. apply/subsetP=> u. rewrite !inE. case/andP=> xNcpuz zNcpux.
    apply/andP; split.
    - apply: contraNN xNcpuz => x_cpuy. exact: cp_tightenR z_cpxy x_cpuy.
    - apply: contraNN zNcpux => y_cpux. apply: cp_widen y_cpux z_cpxy.
      by rewrite cp_sym mem_cpl.
  Qed.

  Lemma sinterval_exit x y u v : u \notin sinterval x y -> v \in sinterval x y ->
    x \in cp u v \/ y \in cp u v.
  Proof using. 
    rewrite !inE negb_and !negbK => H.
    wlog: x y {H} / x \in cp u y.
    { move => W. case/orP : H; first exact: W. 
      rewrite andbC => A B. move: (W _ _ A B). tauto. }
    move => Hu /andP[Hv1 Hv2]. left. 
    apply: contraTT Hu => C. exact: cpN_trans Hv1. 
  Qed.

  Lemma sinterval_outside x y u : u \notin sinterval x y ->
    forall (p : Path u x), irred p -> y \notin p -> [disjoint p & sinterval x y].
  Proof using.
    move=> uNIxy p Ip yNp.
    rewrite disjoint_subset; apply/subsetP => v.
    rewrite inE /= -[mem (in_nodes p)]/(mem p) => v_p.
    apply/negP => v_Ixy.
    case/(isplitP Ip) eq_p : {-}p / v_p => [p1 p2 _ _ D]. 
    case: (sinterval_exit uNIxy v_Ixy) => /cpP/(_ p1); last first.
    + apply/negP; apply: contraNN yNp.
      by rewrite eq_p mem_pcat => ->.
    + move => A. by rewrite -(D x) ?sinterval_bounds ?path_end in v_Ixy.
  Qed.

  Lemma sinterval_disj_cp (x y z : G) :
    z \in cp x y -> [disjoint sinterval x z & sinterval z y].
  Proof using.
    move=> z_cpxy. rewrite -setI_eq0 -subset0. apply/subsetP=> u. rewrite inE.
    case/andP=> /sintervalP2[][p _ /negbTE zNp] _ /sintervalP2[_][q _ /negbTE zNq].
    rewrite !inE. apply: contraTT z_cpxy => _. apply/cpP => /(_ (pcat (prev p) q)).
    by rewrite mem_pcat mem_prev zNp zNq.
  Qed.

  Lemma sinterval_noedge_cp (x y z u v : G) :
    u -- v -> u \in sinterval x z -> v \in sinterval z y -> z \notin cp x y.
  Proof using.
    move=> uv /sintervalP2[][p _ /negbTE zNp] _ /sintervalP2[_][q _ /negbTE zNq].
    apply/cpP => /(_ (pcat (prev p) (pcat (edgep uv) q))).
    rewrite !mem_pcat mem_prev mem_edgep zNp zNq orbF /=.
    apply/negP. rewrite negb_or. apply/andP. split.
    - apply: contraFneq zNp =>->. exact: path_begin.
    - apply: contraFneq zNq =>->. exact: path_begin.
  Qed.

  Lemma sinterval_connectL (x y z : G) : z \in sinterval x y ->
    exists2 u, x -- u & connect (restrict (sinterval x y) sedge) z u.
  Proof using.
    case: (altP (z =P x)) => [->|zNx]; first by rewrite sinterval_bounds.
    case/sintervalP2=> -[p']. case: (splitR p' zNx) => [u] [p] [ux] {p'}->.
    rewrite irred_cat => /and3P[? _] /eqP/setP/(_ x).
    rewrite in_set1 in_set mem_edgep eqxx orbT andbT eq_sym (sg_edgeNeq ux).
    move=> xNp yNp' [q'] Iq' xNq'. exists u; first by rewrite sgP.
    apply: connectRI (p) _ => v in_p. case/psplitP eq_p : _ / in_p => [p1 p2].
    rewrite inE. apply/andP. split.
    - apply: (@cpNI v y (pcat (prev p1) q')).
      rewrite mem_pcat mem_prev negb_or xNq' andbT.
      apply: contraFN xNp. by rewrite eq_p mem_pcat => ->.
    - apply: (@cpNI v x (pcat p2 (edgep ux))).
      apply: contraNN yNp'. by rewrite eq_p !mem_pcat -orbA => ->.
  Qed.

  Lemma sinterval_connectedL (x y : G) : connected (x |: sinterval x y).
  Proof using.
    apply: connected_center (setU11 _ _) => z Hx. have := Hx. rewrite in_setU1.
    case/orP=> [/eqP->|/sinterval_connectL]; first exact: connect0.
    case=> u xu /connect_restrict_case[z_u|].
    - rewrite z_u. apply: connectRI (edgep xu) _ => v.
      rewrite mem_edgep. case/orP=> /eqP->; by [exact: setU11 | rewrite -z_u].
    - case=> zNu _ Hu /(connect_irredRP zNu)[p _ /subsetP p_sub].
      apply: connectRI (pcat (edgep xu) (prev p)) _ => v.
      rewrite mem_pcat mem_edgep mem_prev in_setU1 -orbA.
      case/or3P=> [->|/eqP->|/p_sub->] //. by rewrite Hu.
  Qed.

  Lemma sinterval_components (C : {set G}) x y :
    C \in components (sinterval x y) ->
    (exists2 u, u \in C & x -- u) /\ (exists2 v, v \in C & y -- v).
  Proof using.
    move=> C_comp. wlog suff Hyp : x y C_comp / exists2 u : G, u \in C & x -- u.
    { split; move: C_comp; last rewrite sinterval_sym; exact: Hyp. }
    case/and3P: (partition_components (sinterval x y)).
    move=> /eqP compU compI comp0.
    have /card_gt0P[a a_C] : 0 < #|C|.
    { rewrite card_gt0. by apply: contraTneq C_comp =>->. }
    have a_sI : a \in sinterval x y. { rewrite -compU. by apply/bigcupP; exists C. }
    rewrite -{C C_comp a_C}(def_pblock compI C_comp a_C).
    case: (sinterval_connectL a_sI) => u xu u_a. exists u => //.
    have u_sI : u \in sinterval x y by case/connect_restrict_case: u_a => [<-|[]].
    rewrite pblock_equivalence_partition //. exact: sedge_equiv_in.
  Qed.

  (** *** Intervals *)

  Definition interval x y := [set x;y] :|: sinterval x y.

  Fact intervalL (x y : G) : x \in interval x y.
  Proof. by rewrite !inE eqxx. Qed.

  Fact intervalR (x y : G) : y \in interval x y.
  Proof. by rewrite !inE eqxx !orbT. Qed.

  Lemma interval_sym x y : interval x y = interval y x.
  Proof. by rewrite /interval [[set x; y]]setUC sinterval_sym. Qed.

  Lemma cp_sub_interval x y : cp x y \subset interval x y.
  Proof using G_conn.
    apply/subsetP=> z z_cpxy. rewrite !in_setU !in_set1 inE -implyNb negb_or.
    apply/implyP=> /andP[zNx zNy]. apply/andP; split.
    - apply: contraNN zNx => /(cp_tightenR z_cpxy). by rewrite cpxx !inE eq_sym.
    - rewrite cp_sym in z_cpxy. apply: contraNN zNy => /(cp_tightenR z_cpxy).
      by rewrite cpxx !inE eq_sym.
  Qed.

  Lemma intervalI_cp (x y z : G) :
    z \in cp x y -> interval x z :&: interval z y = [set z].
  Proof using.
    move=> z_cpxy. apply/setP=> u.
    rewrite inE ![_ \in interval _ _]inE (lock sinterval) !inE -lock -!orbA.
    apply/idP/idP; last by move=>->.
    case/andP=> /or3P[/eqP->|->//|u_sIxz] /or3P[->//|/eqP u_y|u_sIzy].
    - move: z_cpxy. by rewrite -u_y cpxx inE eq_sym.
    - move: u_sIzy. by rewrite inE z_cpxy.
    - move: u_sIxz. by rewrite u_y inE (cp_sym y x) z_cpxy andbF.
    - by case: (disjointE (sinterval_disj_cp z_cpxy) u_sIxz u_sIzy).
  Qed.

  Lemma connected_interval (x y : G) : 
    connected (interval x y).
  Proof using G_conn.
    apply: connected_center (intervalL x y) => z.
    rewrite {1}/interval set2C -setUA in_setU1 orbC.
    case/orP=> [/(sinterval_connectedL (setU11 _ _))|/eqP{z}->].
    { apply: connect_mono => {z}. apply: restrict_mono => z /=.
      by rewrite /interval set2C -setUA (in_setU1 z y) => ->. }
    case/connect_irredP: (G_conn x y) => p Ip. apply: connectRI (p) _ => z z_p.
    rewrite inE -implyNb in_set2 negb_or inE. apply/implyP.
    wlog suff Hyp : x y p Ip z_p / z != x -> x \notin cp z y.
    { have Ip' : irred (prev p) by rewrite irred_rev.
      have z_p' : z \in prev p by rewrite mem_prev.
      case/andP=> zNx zNy. apply/andP; split.
      - exact: Hyp Ip z_p zNx.
      - exact: Hyp Ip' z_p' zNy. }
    case/(isplitP Ip) _ : _ / z_p => p1 p2 _ _ I zNx.
    apply: (cpNI (p := p2)). apply: contraNN zNx => H. by rewrite [x]I.
  Qed.

  (** *** Bags *)

  Definition bag (U : {set G}) x :=
    locked [set z | [forall y in CP U, x \in cp z y]].

  Lemma bag_id (U : {set G}) x : x \in bag U x.
  Proof. rewrite /bag -lock inE. apply/forall_inP => y _. exact: mem_cpl. Qed.

  Lemma bag_nontrivial (U : {set G}) x : 
    bag U x != [set x] -> exists2 y, y \in bag U x & y != x.
  Proof. apply: setN01E. apply/set0Pn. exists x. by rewrite bag_id. Qed.

  Lemma bagP (U : {set G}) x z : 
    reflect (forall y, y \in CP U -> x \in cp z y) (z \in bag U x).
  Proof. rewrite /bag -lock inE. exact: (iffP forall_inP). Qed.
  Arguments bagP {U x z}.

  (** was only used in the CP_tree lemma, but we keep it here *)
  Lemma bagPn (U : {set G}) x z : 
    reflect (exists2 y, y \in CP U & x \notin cp z y) (z \notin bag U x).
  Proof using.
    rewrite /bag -lock inE negb_forall. apply: (iffP existsP) => [[y]|[y] A B].
    - rewrite negb_imply => /andP[? ?]. by exists y.
    - exists y. by rewrite A.
  Qed.

  Lemma bag_sub_sinterval (U : {set G}) x y z :
    x \in CP U -> y \in CP U -> z \in cp x y :\: [set x; y] ->
    bag U z \subset sinterval x y.
  Proof using G_conn.
    rewrite in_setD in_set2 negb_or => x_cp y_cp /andP[]/andP[zNx zNy] z_cpxy.
    apply/subsetP=> u /bagP u_bag.
    move: x_cp y_cp => /u_bag z_cpux /u_bag z_cpuy.
    rewrite inE. apply/andP; split.
    - apply: contraNN zNx => x_cpuy.
      suff : x \in cp z z by rewrite cpxx in_set1 eq_sym.
      suff : x \in cp z u by apply: cp_tightenR; rewrite cp_sym.
      rewrite cp_sym; exact: cp_tightenR z_cpxy x_cpuy.
    - apply: contraNN zNy => y_cpux.
      suff : y \in cp z z by rewrite cpxx in_set1 eq_sym.
      suff : y \in cp z u by apply: cp_tightenR; rewrite cp_sym.
      rewrite cp_sym; apply: cp_tightenR y_cpux; by rewrite cp_sym.
  Qed.


  (** ** Neighouring Checkpoints *)

  Definition ncp (U : {set G}) (p : G) : {set G} := 
    locked [set x in CP U | 
            connect (restrict [pred z:G | (z \in CP U) ==> (z == x)] sedge) p x].

  (* TOTHINK: Do we also want to require [irred q] *)
  Lemma ncpP (U : {set G}) (p : G) x : 
    reflect (x \in CP U /\ exists q : Path p x, forall y, y \in CP U -> y \in q -> y = x) 
            (x \in ncp U p).
  Proof using.
    rewrite /ncp -lock inE. 
    apply: (iffP andP) => [[cp_x A]|[cp_x [q Hq]]]; split => //.
    - case: (boolP (p == x)) => [/eqP ?|px]. 
      + subst p. exists (idp x) => y _ . by rewrite mem_idp => /eqP.
      + case/(connect_irredRP px) : A => q irr_q /subsetP sub_q. 
        exists q => y CPy /sub_q. by rewrite !inE CPy => /eqP.
    - apply: (connectRI q) => y y_in_q.
      rewrite inE. apply/implyP => A. by rewrite [y]Hq.
  Qed.
  
  Lemma ncp_CP (U : {set G}) (u : G) :
    u \in CP U -> ncp U u = [set u].
  Proof using. 
    move => Hu.
    apply/setP => x. rewrite [_ \in [set _]]inE. apply/ncpP/eqP.
    - move => [Hx [q Hq]]. by rewrite [u]Hq.
    - move => ->. split => //. exists (idp u) => y _. by  rewrite mem_idp => /eqP.
  Qed.

  Lemma ncp_bag (U : {set G}) (p : G) x :
    x \in CP U -> (p \in bag U x) = (ncp U p == [set x]).
  Proof using G_conn.
    move => Ux. apply/bagP/eq_set1P.
    - move => A. split.
      + apply/ncpP; split => //.
        case/connect_irredP : (G_conn p x) => q irr_q. 
        case: (boolP [exists y in CP U, y \in [predD1 q & x]]).
        * case/exists_inP => y /= B. rewrite inE eq_sym => /= /andP [C D]. 
          case:notF. apply: contraTT (A _ B) => _. apply/cpPn.
          case/(isplitP irr_q) def_q : q / D => [q1 q2 irr_q1 irr_q2 D12].
          exists q1 => //. apply: contraNN C => C. by rewrite [x]D12 // path_end.
        * rewrite negb_exists_in => /forall_inP B.
          exists q => y /B => C D. apply/eqP. apply: contraNT C => C. 
          by rewrite inE C.
      + move => y /ncpP [Uy [q Hq]]. 
        have Hx : x \in q. { apply/cpP. exact: A. }
        apply: esym. exact: Hq. 
    - case => A B y Hy. apply/cpP => q.
      have qy : y \in q by rewrite path_end.
      move: (split_at_first Hy qy) => [x'] [q1] [q2] [def_q cp_x' Hq1]. 
      suff ?: x' = x. { subst x'. by rewrite def_q mem_pcat path_end. }
      apply: B. apply/ncpP. split => //. exists q1 => z' H1 H2. exact: Hq1.
  Qed.

  Lemma ncp0 (U : {set G}) x p : 
    x \in CP U -> ncp U p == set0 = false.
  Proof using G_conn. 
    case/connect_irredP : (G_conn p x) => q irr_q Ux.  
    case: (split_at_first Ux (path_end q)) => y [q1] [q2] [def_q CPy Hy].
    suff: y \in ncp U p. { apply: contraTF => /eqP->. by rewrite inE. }
    apply/ncpP. split => //. by exists q1. 
  Qed.
  Arguments ncp0 [U] x p.
  
  Lemma ncp_interval U (x y p : G) : 
    x != y -> [set x; y] \subset ncp U p -> p \in sinterval x y.
  Proof using.
    rewrite subUset !sub1set inE => xy /andP[Nx Ny]. 
    wlog suff: x y xy Nx Ny / x \notin cp p y.
    { move => W. by rewrite !W // eq_sym. }
    have cp_x : x \in CP U. by case/ncpP : Nx. 
    case/ncpP : Ny => cp_y [q /(_ _ cp_x) H]. 
    apply: (cpNI (p := q)). by apply: contraNN xy => /H->.
  Qed.

  (** *** Application to bags *)

  (** the root of a bag is a checkpoint separating the bag from
  the rest of the graph *)
  Lemma bag_exit (U : {set G}) x u v : 
    x \in CP U -> u \in bag U x -> v \notin bag U x -> x \in cp u v.
  Proof using G_conn.
    move => cp_x. rewrite [v \in _]ncp_bag // => N1 N2.
    have [y [Y1 Y2 Y3]] : exists y, [/\ y \in CP U, x != y & y \in ncp U v].
    { case: (setN01E _ N2); first by rewrite (ncp0 x).
      move => y Y1 Y2. exists y; split => //; by [rewrite eq_sym|case/ncpP : Y1]. }
    move/bagP : N1 => /(_ _ Y1). 
    apply: contraTT => /cpPn [p] irr_p av_x. 
    case/ncpP : Y3 => _ [q] /(_ _ cp_x) A. 
    have {A} Hq : x \notin q. { apply/negP => /A ?. subst. by rewrite eqxx in Y2. }
    apply: (cpNI (p := pcat p q)). by rewrite mem_pcat negb_or av_x.
  Qed.

  Lemma bag_exit' (U : {set G}) x u v : 
    x \in CP U -> u \in bag U x -> v \in x |: ~: bag U x -> x \in cp u v.
  Proof using G_conn. 
    move => cp_x Hu. case/setU1P => [->|]; first by rewrite cp_sym mem_cpl.
    rewrite inE. exact: bag_exit Hu.
  Qed.

  Lemma bag_exit_edge (U : {set G}) x u v :
    x \in CP U -> u \in bag U x -> v \notin bag U x -> u -- v -> u = x.
  Proof using G_conn.
    move=> x_cp u_bag vNbag uv.
    move/cpP/(_ (edgep uv)): (bag_exit x_cp u_bag vNbag).
    rewrite mem_edgep. case/orP=> /eqP// Exv.
    move: vNbag. by rewrite -Exv bag_id.
  Qed.


  Lemma connected_bag x (U : {set G}) : x \in CP U -> connected (bag U x).
  Proof using G_conn.
    move => cp_x.
    suff S z : z \in bag U x -> connect (restrict (bag U x) sedge) x z.
    { move => u v Hu Hv. apply: connect_trans (S _ Hv). 
      rewrite srestrict_sym. exact: S. }
    move => Hz. case/connect_irredP : (G_conn z x) => p irr_p. 
    suff/subsetP sP : p \subset bag U x.
    { rewrite srestrict_sym. exact: (connectRI p). }
    apply/negPn/negP. move/subsetPn => [z' in_p N]. 
    case/(isplitP irr_p): _ / in_p => [p1 p2 _ _ D].
    suff ?: x \in p1 by rewrite -(D x) ?bag_id ?path_end // in N.
    apply/cpP. exact: bag_exit N.
  Qed.



  (** ** Partitioning with intervals, bags and checkpoints *)

  (** *** Disjointness statements *)

  (** A small part of Proposition 20. *)
  Lemma CP_tree_sinterval (U : {set G}) (x y : G) :
    is_tree (CP U) -> x \in CP U -> y \in CP U -> x ⋄ y -> [disjoint CP U & sinterval x y].
  Proof using G_conn.
    move => CP_tree x_cp y_cp xy.
    rewrite -setI_eq0 -subset0; apply/subsetP => u.
    rewrite inE [u \in set0]inE =>/andP[u_cp].
    case/sintervalP2=> -[p] Ip yNp [q] Iq xNq.
    case: (CP_path u_cp x_cp Ip) => p_ [] Ip_ p_cp /subsetP/(_ y) p_p.
    case: (CP_path u_cp y_cp Iq) => q_ [] Iq_ q_cp /subsetP/(_ x) q_q.
    have {p Ip yNp p_p} yNp_ : y \notin p_ by exact: contraNN yNp.
    have {q Iq xNq q_q} xNq_ : x \notin q_ by exact: contraNN xNq.
    have Ip_xy : irred (pcat p_ (edgep xy)).
    { rewrite irred_cat Ip_ irred_edge. apply/eqP/setP=> z. rewrite inE in_set1 mem_edgep.
      apply/andP/eqP=> [[z_p]/orP[]/eqP//z_y|->]; last by rewrite path_end eqxx.
      exfalso. move: z_y z_p =>->. by apply/negP. }
    have eq_ : q_ = pcat p_ (edgep xy).
    { apply CP_tree =>//. split=>//. apply/subsetP=> z. rewrite mem_pcat mem_edgep.
      by case/or3P=> [/(subsetP p_cp)|/eqP->|/eqP->]. }
    apply: contraNT xNq_ => _.
    by rewrite eq_ (@mem_pcat link_graph) mem_edgep eqxx.
  Qed.
  
  Lemma bag_disj (U : {set G}) x y :
    x \in CP U -> y \in CP U -> x != y -> [disjoint bag U x & bag U y].
  Proof using G_conn.
    move => Ux Uy xy. apply/pred0P => p /=. apply:contraNF xy => /andP[].
    rewrite !ncp_bag //. by move => /eqP-> /eqP/set1_inj->.
  Qed.

  Lemma bag_cp (U : {set G}) x y : 
    x \in CP U -> y \in CP U -> x \in bag U y = (x == y).
  Proof using G_conn. 
    move => cp_x cp_y. 
    apply/idP/idP => [|/eqP <-]; last exact: bag_id.
    apply: contraTT => xy. 
    have D: [disjoint bag U x & bag U y] by apply : bag_disj.
      by rewrite (disjointFr D) // bag_id.
  Qed.
  
  (** NOTE: This looks fairly specific, but it also has a fairly
  straightforward proof *)
  Lemma interval_bag_disj U (x y : G) :
    y \in CP U -> [disjoint bag U x & sinterval x y].
  Proof using.
    move => Uy. rewrite disjoint_sym disjoints_subset. apply/subsetP => z.
    rewrite !inE => /andP[A1 A2]. 
    apply: contraTN A1 => /bagP/(_ _ Uy). by rewrite negbK.
  Qed.

  (** *** Covering statements *)

  Lemma sinterval_bag_cover x y : x != y ->
    [set: G] = bag [set x; y] x :|: sinterval x y :|: bag [set x; y] y.
  Proof using G_conn.
    move=> xNy. apply/eqP. rewrite eqEsubset subsetT andbT. apply/subsetP => p _.
    rewrite setUAC setUC !in_setU inE -negb_or -implybE. apply/implyP.
    wlog suff Hyp : x y {xNy} / x \in cp p y -> p \in bag [set x; y] x.
    { by case/orP => /Hyp; last rewrite setUC; move=>->. }
    move=> x_cppy; apply/bagP => z. rewrite CP_set2 => z_cpxy.
    exact: cp_tightenR z_cpxy x_cppy.
  Qed.

  Lemma sinterval_cp_cover x y z : z \in cp x y :\: [set x; y] ->
    sinterval x y = sinterval x z :|: bag [set x; y] z :|: sinterval z y.
  Proof using G_conn.
    rewrite 4!inE negb_or => /andP[]/andP[zNx zNy] z_cpxy. apply/eqP.
    have [x_CP y_CP] : x \in CP [set x; y] /\ y \in CP [set x; y].
    { by split; apply: CP_extensive; rewrite !inE eqxx. }
    rewrite eqEsubset !subUset sinterval_sub //=.
    rewrite {3}(sinterval_sym x y) {2}(sinterval_sym z y) sinterval_sub 1?cp_sym //.
    rewrite bag_sub_sinterval /= ?andbT //;
      last by rewrite in_setD in_set2 negb_or zNx zNy.
    apply/subsetP=> u u_sIxy. rewrite !in_setU.
    have [uNx uNy] : u != x /\ u != y.
    { by split; apply: contraTneq u_sIxy => ->; rewrite sinterval_bounds. }
    move: u_sIxy; rewrite inE. case/andP=> xNcpuy yNcpux.
    case: (boolP (z \in cp u x)) => Hx; case: (boolP (z \in cp u y)) => Hy.
    + suff -> : u \in bag [set x; y] z by []. apply/bagP=> c.
      rewrite CP_set2 => /(subsetP (cp_triangle z)). rewrite in_setU cp_sym.
      case/orP=> c_cp; exact: cp_tightenR c_cp _.
    + suff -> : u \in sinterval z y by []. rewrite inE Hy /=.
      apply: cpN_trans yNcpux _. apply: contraNN zNy => y_cpxz.
      suff : z \in cp y y by rewrite cpxx in_set1 eq_sym.
      move: y_cpxz z_cpxy. rewrite [cp x z]cp_sym [cp x y]cp_sym.
      exact: cp_tightenR.
    + suff -> : u \in sinterval x z by []. rewrite inE Hx andbT.
      apply: cpN_trans xNcpuy _. apply: contraNN zNx => x_cpyz.
      suff : z \in cp x x by rewrite cpxx in_set1 eq_sym.
      move: x_cpyz z_cpxy. rewrite [cp y z]cp_sym.
      exact: cp_tightenR.
    + rewrite cp_sym in Hx. have : z \notin cp x y := cpN_trans Hx Hy.
      by rewrite z_cpxy.
  Qed.

  Lemma interval_cp_cover x y z : z \in cp x y :\: [set x; y] ->
    interval x y = (x |: sinterval x z) :|: bag [set x; y] z :|: (y |: sinterval z y).
  Proof using G_conn.
    rewrite /interval => /sinterval_cp_cover->.
    by rewrite setUAC -setUA [_ :|: set1 y]setUAC !setUA.
  Qed.

  Lemma interval_edge_cp (x y z u v : G) : z \in cp x y -> u -- v ->
    u \in interval x z -> v \in interval z y -> (u == z) || (v == z).
  Proof using.
    move=> z_cpxy uv u_xz v_zy.
    wlog [Hu Evy] : x y u v z_cpxy uv {u_xz v_zy} / u \in sinterval x z /\ v = y.
    { move=> Hyp. move: u_xz v_zy. rewrite !in_setU !in_set1 -!orbA.
      case/or3P=> [/eqP Eux|->//|Hu]; case/or3P=> [->//|/eqP Evy|Hv].
      - move: uv; rewrite Eux Evy => xy. move/cpP/(_ (edgep xy)): z_cpxy.
        by rewrite mem_edgep ![z == _]eq_sym.
      - rewrite orbC. move: (conj Hv Eux). rewrite sinterval_sym.
        apply: Hyp; by rewrite 1?cp_sym 1?sg_sym.
      - by apply: Hyp (conj Hu Evy).
      - move: (sinterval_noedge_cp uv Hu Hv). by rewrite z_cpxy. }
    move: uv Hu; rewrite {}Evy inE => uy /andP[_]/cpPn[p _ zNp].
    move/cpP/(_ (pcat (prev p) (edgep uy))): z_cpxy.
    by rewrite mem_pcat mem_prev mem_edgep (negbTE zNp) /= ![z == _]eq_sym.
  Qed.

  (** Variants of the lemmas above that go together with quotient graphs *)
  Lemma bag_interval_cap (x y z: G) (U : {set G}) :
    connected [set: G] -> x \in CP U -> y \in CP U -> 
    z \in bag U x -> z \in interval x y -> z = x.
  Proof. 
    move => conn_G xU yU Hz. 
    rewrite /interval inE (disjointFr (interval_bag_disj _ _) Hz) // orbF.
    case/setUP => /set1P // ?. subst z. apply/eqP. by rewrite -(@bag_cp U).
  Qed.

  Lemma interval_interval_cap (x y u z: G) :
    u \in cp x y ->
    z \in interval x u -> z \in interval u y -> z = u.
  Proof. 
    move => cp_u Z1 Z2. move: (intervalI_cp cp_u). 
    move/setP/(_ z)/esym. by rewrite 2!inE Z1 Z2 => /eqP.
  Qed.
 
End CheckPoints.

Notation "x ⋄ y" := (@sedge (link_graph _) x y) (at level 30).

(** ** Checkpoint Order *)

Section CheckpointOrder.

  Variables (G : sgraph) (i o : G).
  Hypothesis conn_io : connect sedge i o.
  Implicit Types x y : G.

  Lemma the_uPath_proof : exists p : Path i o, irred p.
  Proof. case/connect_irredP: conn_io => p Ip. by exists p. Qed.
                                                                
  Definition the_uPath := xchoose (the_uPath_proof).

  Lemma the_connect_irredP : irred (the_uPath).
  Proof. exact: xchooseP. Qed.

  Definition cpo x y := let p := the_uPath in idx p x <= idx p y.

  Lemma cpo_refl : reflexive cpo.
  Proof. move => ?. exact: leqnn. Qed.

  Lemma cpo_trans : transitive cpo.
  Proof. move => ? ? ?. exact: leq_trans. Qed.

  Lemma cpo_total : total cpo.
  Proof. move => ? ?. exact: leq_total. Qed.

  Lemma cpo_antisym : {in cp i o&,antisymmetric cpo}.
  Proof using. 
    move => x y /cpP/(_ the_uPath) Hx _.
    rewrite /cpo -eqn_leq =>/eqP. exact: idx_inj.
  Qed.

  (** All paths visist all checkpoints in the same order as the canonical upath *)
  (* TOTHINK: Is this really the formulation that is needed in the proofs? *)
  Lemma cpo_order (x y : G) (p : Path i o) :
    x \in cp i o -> y \in cp i o -> irred p -> cpo x y = (idx p x <= idx p y).
  Proof using.
    move => /cpP cp_x /cpP cp_y Ip. rewrite /cpo.
    wlog suff Hyp : p Ip / x <[p] y -> forall q : Path i o, irred q -> ~ y <[q] x.
    { apply/idP/idP; rewrite leq_eqVlt; case/orP=> [/eqP|x_lt_y].
      + by move=> /(idx_inj (cp_x the_uPath))->.
      + by rewrite leqNgt; apply/negP; apply: Hyp the_connect_irredP _ _ _.
      + by move=> /(idx_inj (cp_x p))->.
      + by rewrite leqNgt; apply/negP; apply: Hyp x_lt_y _ the_connect_irredP.
    }
    case/(three_way_split Ip (cp_x p) (cp_y p)) => [p1][_][p3][_ xNp3 yNp1].
    move=> q Iq.
    case/(three_way_split Iq (cp_y q) (cp_x q)) => [q1][_][q3][_ yNq3 xNq1].
    have := cp_x (pcat q1 p3); apply/negP.
    by rewrite mem_pcat negb_or; apply/andP.
  Qed.

  Lemma cpo_min x : cpo i x.
  Proof. by rewrite /cpo idx_start. Qed.

  Lemma cpo_max x : x \in cp i o -> cpo x o.
  Proof using.
    move=> /cpP/(_ the_uPath) x_path.
    rewrite /cpo idx_end; [ exact: idx_mem | exact: the_connect_irredP ].
  Qed.

  Lemma cpo_cp x y : x \in cp i o -> y \in cp i o -> cpo x y ->
    forall z, z \in cp x y = [&& (z \in cp i o), cpo x z & cpo z y].
  Proof using.
    move=> x_cpio y_cpio.
    have [x_path y_path] : x \in the_uPath /\ y \in the_uPath.
    { by split; move: the_uPath; apply/cpP. }
    rewrite {1}/cpo leq_eqVlt =>/orP[/eqP/(idx_inj x_path)<- z | x_lt_y].
    { rewrite cpxx inE eq_sym.
      apply/eqP/andP; last by case; exact: cpo_antisym.
      by move=><-; split; last rewrite /cpo. }
    case: (three_way_split the_connect_irredP x_path y_path x_lt_y)
      => [p1] [p2] [p3] [eq_path xNp3 yNp1].
    move: the_connect_irredP. rewrite eq_path. 
    case/irred_catE => Ip1 /irred_catE [Ip2 Ip3 D23] D123.
    move=> z; apply/idP/andP.
    + move=> z_cpxy. have z_cpio := cp_widen x_cpio y_cpio z_cpxy.
      split=>//. move: z_cpio => /cpP/(_ the_uPath) z_path.
      move: z_cpxy => /cpP/(_ p2) z_p2. rewrite /cpo.
      case: (altP (z =P x)) => [->|zNx]; first by rewrite leqnn (ltnW x_lt_y).
      apply/andP; split; last first.
      - rewrite eq_path idx_catR ?idx_catL ?path_end ?idx_end ?idx_mem //.
        apply: contraNN zNx => ?. by rewrite [z]D123 // mem_pcat z_p2.
      - rewrite eq_path leq_eqVlt. apply/orP; right.
        rewrite -idxR -?eq_path ?the_connect_irredP //. apply: in_tail zNx _.
        by rewrite mem_pcat z_p2.
    + case=> z_cpio /andP[x_le_z z_le_y]. apply/cpP => p.
      have /cpP/(_ (pcat p1 (pcat p p3))) := z_cpio.
      case (altP (z =P x)) => [-> _ | zNx]; first exact: path_begin.
      case (altP (z =P y)) => [-> _ | zNy]; first exact: path_end.
      have zNp1 : z \notin p1.
      { apply: contraNN zNx => z_p1. apply/eqP; apply: cpo_antisym => //.
        rewrite x_le_z andbT /cpo eq_path idx_catL ?path_end // idx_end //.
        exact: idx_mem. }
      rewrite mem_pcat -implyNb => /implyP/(_ zNp1).
      rewrite mem_pcat => /orP[// | /(in_tail zNy) z_p3].
      exfalso; have := zNy; apply/negP; rewrite negbK.
      apply/eqP; apply: cpo_antisym => //.
      rewrite z_le_y /=/cpo eq_path idx_catR // leq_eqVlt.
      rewrite -idxR ?z_p3 // ?irred_cat ?mem_pcat ?(tailW z_p3) ?Ip2 ?Ip3//=.
      apply/eqP/setP => k. rewrite !inE. apply/andP/eqP => [[]|-> //]. exact: D23. 
  Qed.

End CheckpointOrder.


