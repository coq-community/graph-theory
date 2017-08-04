(** * Proofs using unpackaged paths *)

  (* could provide upaths if needed *)
  Lemma cp_mid z x y t : z \in cp x y -> 
    exists p1 p2, [/\ spath z x p1, spath z y p2 & t \notin p1 \/ t \notin p2].
  Proof.
    case/upathP : (G_conn x y) => p /andP [p1 p2] /cpP cp_z.
    move/(_ _ p2) : cp_z => H. 
    case: (ssplitP H p2) p1 => {p p2 H} pl pr Pl Pr U. 
    exists (srev x pl). exists pr. split => //. 
    - exact: spath_rev.
    - apply/orP. rewrite -negb_and !mem_rev. apply/negP => /andP[/mem_belast E F].
      rewrite -cat_cons cat_uniq in U. case/and3P : U => _ /hasPn /= B _.
      by rewrite (negbTE (B _ F)) in E.
  Qed.

  (* Lemma 13 *)
  Lemma CP_closed U x y : 
    x \in CP U -> y \in CP U -> cp x y \subset CP U.
  Proof.
    case/bigcupP => [[x1 x2] /= /setXP [x1U x2U] x_cp]. 
    case/bigcupP => [[y1 y2] /= /setXP [y1U y2U] y_cp]. 
    apply/subsetP => t t_cp. 
    case (boolP (t == y)) => [/eqP-> //|T2].
    { apply/bigcupP. exists (y1,y2); by [exact/setXP|]. }
    case (boolP (t == x)) => [/eqP-> //|T1].
    { apply/bigcupP. exists (x1,x2); by [exact/setXP|]. }
    move: (cp_mid t x_cp) => [p1] [p2] [u1 u2] H.
    wlog P1 : p1 p2 x1 x2 u1 u2 H x1U x2U x_cp / t \notin p1 => [W|{H}].
    (* FIXME: This [done] takes to long *)
    { case: H => H; [apply: (W p1 p2 x1 x2)|apply: (W p2 p1 x2 x1)] => //; try tauto. 
      by rewrite cp_sym. }
    move: (cp_mid t y_cp) => [q1] [q2] [v1 v2] H.
    wlog P2 : q1 q2 y1 y2 v1 v2 H y1U y2U y_cp / t \notin q1 => [W|{H}].
    { case: H => H; [apply: (W q1 q2 y1 y2)|apply: (W q2 q1 y2 y1)] => //; try tauto. 
      by rewrite cp_sym. }
    apply/bigcupP; exists (x1,y1) => /= ; first exact/setXP. 
    apply: contraTT t_cp => /cpPn [s] [/upathW s1 /notin_tail s2].
    apply: (cpNI (p := p1++s++srev y q1)). 
    - apply: spath_concat u1 _. apply: spath_concat s1 _. exact: spath_rev. 
    - rewrite !inE !mem_cat !negb_or mem_rev T1 P1 s2 /=.  
      apply/negP. move/mem_belast. by rewrite !inE (negbTE T2) (negbTE P2).
  Qed.


  Lemma notin_srev z x p : z \notin x::p -> z \notin srev x p.
  Proof. apply: contraNN. rewrite /srev mem_rev. exact: mem_belast. Qed.


  Lemma CP_base' x y : x \in CP U -> y \in CP U ->
    exists x' y':G, [/\ x' \in U, y' \in U & [set x;y] \subset cp x' y'].
  Proof.
    move => U1 U2. case/bigcupP : U1 => [[x1 x2]]. case/bigcupP : U2 => [[y1 y2]] /=.
    rewrite !inE /= => /andP[Uy1 Uy2] cp_y /andP[Ux1 Ux2] cp_x.
    case: (boolP (x \in cp y1 y2)) => [C|Wx]; first by exists y1; exists y2; rewrite subUset !sub1set C.
    case: (boolP (y \in cp x1 x2)) => [C|Wy]; first by exists x1; exists x2; rewrite subUset !sub1set C.
    gen have H,A: x x1 x2 y1 y2 {Ux1 Ux2 Uy1 Uy2 Wy cp_y} Wx cp_x /
      (x \in cp x1 y1) || (x \in cp x2 y2).
    { case/cpPn : Wx => p pth_p av_x.
      apply: contraTT cp_x. rewrite negb_or => /andP[/cpPn [s s1 s2] /cpPn [t t1 t2]].
      apply: (cpNI (p := s++p++srev x2 t)); first by spath_tac.
      by rewrite -cat_cons !mem_cat /= 2!negb_or s2 (notin_tail av_x) notin_srev. }
    move: (H _ _ _ _ _ Wy cp_y) => B {H}. rewrite (cp_sym y1 x1) (cp_sym y2 x2) in B. 
    wlog {A} /andP [Hx Hy] : x1 x2 y1 y2 A B cp_x cp_y Ux1 Ux2 Uy1 Uy2 Wx Wy
        / (x \in cp x1 y1) && (y \notin cp x1 y1).
    { case: (boolP (y \in cp x1 y1)) A B => A; case: (boolP (x \in cp x1 y1)) => /= B C D W. 
      - by exists x1; exists y1; rewrite subUset !sub1set B. 
      - case: (boolP (y \in cp x2 y2)) => E. (* TOTHINK: why the second case anlysis in this case? *)
        + exists x2; exists y2; by rewrite subUset !sub1set C.
        + move: (W x2 x1 y2 y1). rewrite (cp_sym x2 x1) (cp_sym y2 y1) A C /= orbT. exact.
      - apply: (W x1 x2 y1 y2) => //. by rewrite B. by rewrite D. (* exact/andP. *)
      - exists x2; exists y2; by rewrite subUset !sub1set C D. }
    rewrite (negbTE Hy) /= in B.
    case: (boolP (x \in cp x2 y2)) => [C|Wx']; first by exists x2; exists y2; rewrite subUset !sub1set C.
    exists x1. exists y2. rewrite subUset !sub1set. split => //. apply/andP; split.
    - apply: contraTT cp_x => C. apply: cpN_cat C _. by rewrite cp_sym.
    - apply: contraTT cp_y. apply: cpN_cat. by rewrite cp_sym.
  Qed.


  Lemma CP_triangle_avoid' x' y' (x y z: link_graph) : 
    x -- y -> y -- z -> z -- x -> x \in cp x' y' -> y \in cp x' y' -> z \notin cp x' y'.
  Proof.
    move => xy yz zx Cx Cy. apply/negP => Cz.
    case/upathP : (G_conn x' y') => p pth_p. 
    gen have Hp,x_in_p: x Cx {xy yz zx} / x \in x'::p.
    { apply/cpP. apply: Cx. by spath_tac. }
    move: (Hp _ Cy) (Hp _ Cz) => y_in_p z_in_p.
    pose I (x: link_graph) := index (x) (x'::p).
    have D (x1 x2 : link_graph) : x1 -- x2 -> x1 \in x'::p -> I x1 <> I x2.
    { move => H in_p. move/index_uniq_inj. case/(_ _ )/Wrap => //.
      move => ?. subst. by rewrite sgP in H. }
    wlog /andP [x_lt_y y_lt_z] : x y z xy yz zx x_in_p y_in_p z_in_p Cy {Cx  Cz D Hp}
         / I x < I y < I z.
    { move => W. 
      wlog x_lt_y : x y xy yz zx Cx Cy x_in_p y_in_p z_in_p / I x < I y => [W2|].
      { case: (ltngtP (I x) (I y)); [exact: W2|apply:W2; by rewrite // sg_sym |exact: D]. }
      case: (ltngtP (I y) (I z)) => [Hyz|Hyz|]; last exact: D. 
      - exact: (W x y z).
      - case: (ltngtP (I z) (I x)) => [Hzx|Hzx|]; last exact: D. 
        + exact: (W z x y).
        + apply: (W x z y); by rewrite // sg_sym. }
    case/(usplitP (G := G) x_in_p) def_p : {1}p / pth_p => [p1 p2 pth1 pth2 D]. subst.
    gen have Gy, Hy : y x_lt_y {xy yz y_in_p Cy y_lt_z} / y \notin x' :: p1.
    { apply: contraTN (x_lt_y) => X. 
      rewrite -leqNgt /I -cat_cons !index_cat (spath_end (upathW pth1)) X. 
      rewrite -(spath_last _ _ _ (upathW pth1)) index_last; last exact: upath_uniq pth1.
      by rewrite -ltnS index_mem. }
    have {Gy} Hz : z \notin x' :: p1 by apply: Gy; exact: ltn_trans y_lt_z. 
    rewrite -!cat_cons !(mem_catD D)  (negbTE Hy) (negbTE Hz) /= in y_in_p z_in_p.
    move/(mem_tail (x)) : z_in_p => C. (* this looses information that needs to be recovered *)
    case/(usplitP (G:=G) C) def_p1 : {1}p2 / pth2 => [p21 p22 pth21 pth22 D2]. subst.
    have Hy': y \notin p22. 
    { move: D2. rewrite disjoint_cons => /andP [? D2].
      apply: contraTN y_lt_z => X. 
      rewrite -leqNgt /I -!cat_cons !index_cat (negbTE Hy) (negbTE Hz) leq_add2l.
      have -> : y \in p21 = false. 
      { apply/negP. apply: disjointE X. by rewrite disjoint_sym. }
      have Y : z \in p21. 
      { rewrite (spath_endD (upathW pth21)) //. by rewrite eq_sym; apply: contraTN zx => /= ->. }
      apply: leq_trans (leq_addr _ _). rewrite Y. apply: ltnW. by rewrite index_mem. }
    move: Cy. apply/negP. 
    have: (y) \notin cp (x) (z). 
    { case/andP : zx => _ sub. apply/negP. rewrite cp_sym. move/(subsetP sub). 
      rewrite !inE. by case/orP => /eqP ?;subst; rewrite sg_irrefl in xy yz. }
    case/cpPn => q pth_q /notin_tail Hq. 
    apply: (cpNI (p := p1++q++p22)); first by spath_tac.
    rewrite -cat_cons !mem_cat (negbTE Hy) (negbTE Hq) //=.
  Qed.
