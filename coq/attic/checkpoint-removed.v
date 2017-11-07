  Lemma CP_triangle_avoid x' y' (x y z: link_graph) : 
    x -- y -> y -- z -> z -- x -> x \in cp x' y' -> y \in cp x' y' -> z \notin cp x' y'.
  Proof.
    move => xy yz zx Cx Cy. apply/negP => Cz.
    case/uPathP : (G_conn x' y') => p irr_p.
    move: (cpP' Cx p) (cpP' Cy p) (cpP' Cz p) => x_in_p y_in_p z_in_p.
    pose I := idx p. 
    have D (x1 x2 : link_graph) : x1 -- x2 -> x1 \in nodes p -> I x1 <> I x2.
    { move => H in_p. move/idx_inj. case/(_ _ )/Wrap => //. 
      move => ?. subst. by rewrite sgP in H. }
    wlog /andP [x_lt_y y_lt_z] : x y z xy yz zx x_in_p y_in_p z_in_p Cy {Cx Cz D}
      / I x < I y < I z => [W|].
    { wlog x_lt_y : x y xy yz zx Cx Cy x_in_p y_in_p z_in_p / I x < I y => [W2|].
      { case: (ltngtP (I x) (I y)); [exact: W2|apply:W2; by rewrite // sg_sym |exact: D]. }
      case: (ltngtP (I y) (I z)) => [Hyz|Hyz|]; last exact: D. 
      - exact: (W x y z).
      - case: (ltngtP (I z) (I x)) => [Hzx|Hzx|]; last exact: D. 
        + exact: (W z x y).
        + apply: (W x z y); by rewrite // sg_sym. }
    suff: y \notin cp x' y' by rewrite Cy.
    case/(isplitP (G := G) irr_p) def_p : {1}p / (x_in_p) => [p1 p2 irr_p1 irr_p2 D]. subst.
    case: (idx_nLR irr_p y_in_p) => // Y1 Y2.
    (case: (idx_nLR irr_p z_in_p); first by apply: ltn_trans y_lt_z) => Z1 Z2.
    case/(isplitP (G:=G) irr_p2) def_p1 : {1}p2 / (tailW Z2) => [p21 p22 irr21 irr22 D2]. subst.
    have Hy' : y \notin tail p22.
    { rewrite (idxR irr_p2) ?tailW //. rewrite -(idx_catL irr_p Z2 Y2). by rewrite -leqNgt ltnW. }
    have/cpPn' [q q1 q2] : y \notin cp x z. 
    { case/andP : zx => _ sub. apply/negP. rewrite cp_sym. move/(subsetP sub). 
      rewrite !inE. by case/orP => /eqP ?;subst; rewrite sg_irrefl in xy yz. }
    apply: (cpNI' (p := pcat p1 (pcat q p22))). 
    by rewrite mem_pcat mem_pcatT (negbTE Hy') (negbTE Y1) (negbTE q2).
  Qed.

  
  Lemma CP_triangle U (x y z: CP_ U) : 
    x -- y -> y -- z -> z -- x -> 
    exists x' y' z':G, 
      [/\ x' \in U, y' \in U & z' \in U] /\
      [/\ [set val x;val y] \subset cp x' y',
         [set val y;val z] \subset cp y' z'&
         [set val z;val x] \subset cp z' x'].
  Proof.
    move => xy yz zx.
    move: (CP_base_ x y) => [x'] [y'] [Ux Uy]. 
    rewrite subUset !sub1set => /andP[cp_x cp_y].
    have ncp_z : val z \notin cp x' y' by apply: CP_triangle_avoid cp_x cp_y. 
    case/cpPn' : ncp_z => p irr_p av_z. 
    have x_in_p : val x \in p by apply/cpP'.
    have y_in_p : val y \in p by apply/cpP'.
  
    wlog x_before_y : x' y' Ux Uy cp_x cp_y p irr_p av_z x_in_p y_in_p / 
      idx p (val x) < idx p (val y). 
    { move => W. case: (ltngtP (idx p (val x)) (idx p (val y))) => H.
      - exact: (W x' y' _ _ _ _ p). 
      - apply: (W y' x' _ _ _ _ (prev p)); rewrite 1?cp_sym //. 
        + exact: prev_irred.
        + by rewrite mem_prev.
        + rewrite /=. (* FIXME: why is this needed *) by rewrite mem_prev.
        + by rewrite /= mem_prev.
        + exact: idx_swap H. 
      - move/idx_inj : H. move/(_ x_in_p)/val_inj => ?. subst y. by rewrite sgP in xy. }
    
    move: (CP_base_ x z) => [x''] [z'] [Ux' Uz]. 
    rewrite subUset !sub1set => /andP[cp_x' cp_z].
    have ncp_z : val y \notin cp x'' z' by apply: CP_triangle_avoid cp_x' cp_z; by rewrite sgP.
    case/cpPn' : ncp_z => q irr_q av_y.
    have x_in_q : val x \in q by apply/cpP'.
    have z_in_q : val z \in q by apply/cpP'.

    wlog x_before_z : x'' z' Ux' Uz cp_x' cp_z q irr_q av_y x_in_q z_in_q / 
      idx q (val x) < idx q (val z).
    { move => W. case: (ltngtP (idx q (val x)) (idx q (val z))) => H.
      - exact: (W x'' z' _ _ _ _ q).
      - apply: (W z' x'' _ _ _ _ (prev q)); try rewrite 1?cp_sym /= ?mem_prev //. 
        + exact: prev_irred.
        + exact: idx_swap H. 
      - move/idx_inj : H. move/(_ x_in_q)/val_inj => ?. subst z. by rewrite sgP in zx. }

    case: (three_way_split irr_p x_in_p y_in_p x_before_y) => p1 [p2] [p3] [? ? ?]. subst p.
    rewrite !mem_pcat 2!negb_or in av_z. case/and3P : av_z => p1_z p2_z p3_z. 
    case: (three_way_split irr_q x_in_q z_in_q x_before_z) => q1 [q2] [q3] [? ? ?]. subst q.
    rewrite !mem_pcat 2!negb_or in av_y. case/and3P : av_y => q1_y q2_y q3_y.

    (* have _ : (val x) \in cp x' (val y).  *)
    clear x_before_y y_in_p x_in_p x_before_z z_in_q x_in_q irr_p irr_q.

    exists x'. exists y'. exists z'. split; split; rewrite // subUset !sub1set; apply/andP;split.
    - done.
    - done.
    - apply: contraTT cp_y. case/cpPn' => r _ Hr. 
      apply: (cpNI' (p := pcat p1 (pcat q2 (pcat q3 (prev r))))).
      rewrite /= !mem_pcat !mem_prev 3!negb_or. exact/and4P.
    - apply: contraTT cp_z. case/cpPn' => r _ Hr. 
      apply: (cpNI' (p := pcat q1 (pcat p2 (pcat p3 r)))).
      rewrite /= !mem_pcat 3!negb_or. exact/and4P.
    - rewrite cp_sym. 
      apply: contraTT cp_z. case/cpPn' => r _ Hr. 
      apply: (cpNI' (p := pcat q1 (pcat (prev p1) r))).
      rewrite /= !mem_pcat mem_prev 2!negb_or. exact/and3P.
    - rewrite cp_sym. 
      have: val x \notin cp (val y) (val z).
      { apply/negP. move: yz => /= /andP [_ B] /(subsetP B).
        rewrite !inE => /orP[]/eqP/val_inj=>?; subst x. 
        by rewrite sgP in xy. by rewrite sgP in zx. }
      case/cpPn' => s _ Hs. 
      apply: contraTT cp_x. case/cpPn' => r _ Hr. 
      apply: (cpNI' (p := pcat r (pcat (prev q3) (pcat (prev s) p3)))).
      rewrite /= !mem_pcat !mem_prev 3!negb_or. exact/and4P.
  Qed.

