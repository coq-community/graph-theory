From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries sgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 

(** ** Checkpoints *)

Section CheckPoints.
  Variables (G : sgraph).
  Implicit Types x y z : G.

  Let avoids z x y (p : seq G) := upath x y p && (z \notin x::p).
  Definition avoidable z x y := [exists n : 'I_#|G|, exists p : n.-tuple G, avoids z x y p].

  Definition cp x y := locked [set z | ~~ avoidable z x y].

  Lemma cpPn {z x y} : reflect (exists2 p, upath x y p & z \notin x::p) (z \notin cp x y).
  Proof.
    rewrite /cp -lock inE negbK. apply: (iffP existsP) => [[n] /exists_inP|[p]].
    - case => p ? ?. by exists p.
    - case/andP => U S I.
      have size_p : size p < #|G|.
      { by rewrite -[(size p).+1]/(size (x::p)) -(card_uniqP U) max_card. }
      exists (Ordinal size_p). by apply/exists_inP; exists (in_tuple p).
  Qed.

  Lemma cpNI z x y p : spath x y p -> z \notin x::p -> z \notin cp x y.
  Proof.
    case/andP. case/shortenP => p' ? ? sub_p ? E. apply/cpPn. exists p' => //.
    apply: contraNN E. rewrite !inE. case: (_ == _) => //=. exact: sub_p.
  Qed.
  
  Definition checkpoint x y z := forall p, spath x y p -> z \in x :: p.

  Lemma cpP {x y z} : reflect (checkpoint x y z) (z \in cp x y).
  Proof.
    apply: introP.
    - move => H p pth_p. apply: contraTT H. exact: cpNI.
    - case/cpPn => p /upathW pth_p mem_p /(_ p pth_p). by rewrite (negbTE mem_p).
  Qed.

  (** wrapped versions of the checkpoint/path lemmas *)
  
  Lemma cpP' x y z : reflect (forall p : Path x y, z \in p) (z \in cp x y).
  Proof. 
    apply: (iffP cpP) => [H p|H p Hp]. 
    + rewrite in_collective nodesE. apply: H. exact: valP. 
    + move: (H (Sub p Hp)). by rewrite in_collective nodesE. 
  Qed.
  Arguments cpP' [x y z].

  Lemma cpPn' x y z : reflect (exists2 p : Path x y, irred p & z \notin p) (z \notin cp x y).
  Proof. 
    apply: (iffP cpPn) => [[p /andP [I Hp] N]|[p U N]]. 
    + exists (Sub p Hp); by rewrite /irred ?in_collective nodesE. 
    + rewrite /irred ?in_collective nodesE in U N.
      exists (val p) => //. apply/andP. split => //. exact: valP. 
  Qed.

  Lemma cpNI' x y (p : Path x y) z : z \notin p -> z \notin cp x y.
  Proof. by apply: contraNN => /cpP'. Qed.

  Hypothesis G_conn : forall x y:G, connect sedge x y.

  Lemma cp_sym x y : cp x y = cp y x.
  Proof.
    wlog suff S : x y / cp x y \subset cp y x. 
    { apply/eqP. by rewrite eqEsubset !S. }
    apply/subsetP => z /cpP H. apply/cpP => p p_pth. 
    rewrite (srev_nodes p_pth). apply: H. exact: spath_rev.
  Qed.

  Lemma mem_cpl x y : x \in cp x y.
  Proof. apply/cpP => p. by rewrite mem_head. Qed.

  Lemma subcp x y : [set x;y] \subset cp x y.
  Proof. by rewrite subUset !sub1set {2}cp_sym !mem_cpl. Qed.

  Lemma cpxx x : cp x x = [set x].
  Proof. 
    apply/setP => z; rewrite !inE. 
    apply/idP/idP; last by move/eqP ->; rewrite mem_cpl.
    move/cpP/(_ [::] (spathxx _)). by rewrite inE.
  Qed.

  Lemma cp_triangle z {x y} : cp x y \subset cp x z :|: cp z y.
  Proof.
    apply/subsetP => u /cpP' => A. apply: contraT. 
    rewrite !inE negb_or => /andP[/cpPn' [p1 _ up1]] /cpPn' [p2 _ up2]. 
    move: (A (pcat p1 p2)). by rewrite mem_pcat (negbTE up1) (negbTE up2).
  Qed.
  
  Lemma cpN_cat a x z y : a \notin cp x z -> a \notin cp z y -> a \notin cp x y.
  Proof. 
    move => /negbTE A /negbTE B. apply/negP. move/(subsetP (cp_triangle z)). 
    by rewrite !inE A B.
  Qed.

  Definition CP (U : {set G}) := \bigcup_(xy in setX U U) cp xy.1 xy.2.
  
  Unset Printing Implicit Defensive.

  Lemma cp_mid (z x y t : G) : t != z -> z \in cp x y ->
   exists (p1 : Path z x) (p2 : Path z y), t \notin p1 \/ t \notin p2.
  Proof. 
    move => tNz cp_z.
    case/uPathP : (G_conn x y) => p irr_p.
    move/cpP'/(_ p) : cp_z. case/(isplitP irr_p) => p1 p2 A B C.
    exists (prev p1). exists p2. rewrite mem_prev. apply/orP. 
    case E : (t \in p1) => //=. 
    by rewrite mem_path !inE (negbTE tNz) (disjointFr C E).
  Qed.
  
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
    apply: contraTT t_cp => /cpPn' [s _ Hs]. 
    suff: t \notin (pcat p1 (pcat s (prev q1))) by apply: cpNI'.
    by rewrite !mem_pcat !mem_prev (negbTE P1) (negbTE P2) (negbTE Hs).
  Qed.

  (** Definition of the link graph *)

  Definition link_rel := [rel x y | (x != y) && (cp x y \subset [set x; y])].

  Lemma link_sym : symmetric link_rel.
  Proof. move => x y. by rewrite /= eq_sym cp_sym set2C. Qed.

  Lemma link_irrefl : irreflexive link_rel.
  Proof. move => x /=. by rewrite eqxx. Qed.

  Definition link_graph := SGraph link_sym link_irrefl.

  Lemma link_avoid (x y z : G) : 
    z \notin [set x; y] -> link_rel x y -> exists2 p, spath x y p & z \notin (x::p).
  Abort. (* not acutally used *)

  Lemma link_seq_cp (y x : G) p :
    @spath link_graph x y p -> cp x y \subset x :: p.
  Proof.
    elim: p x => [|z p IH] x /=.
    - move/spath_nil->. rewrite cpxx. apply/subsetP => z. by rewrite !inE.
    - rewrite spath_cons => /andP [/= /andP [A B] /IH C]. 
      apply: subset_trans (cp_triangle z) _.
      rewrite subset_seqR. apply/subUsetP; split. 
      + apply: subset_trans B _. by rewrite !set_cons setUA subsetUl.
      + apply: subset_trans C _. by rewrite set_cons subset_seqL subsetUr.
  Qed.

  (* Lemma 10 *)
  Lemma link_cycle (p : seq link_graph) : ucycle sedge p -> clique [set x in p].
  Proof. 
    move => cycle_p x y. rewrite !inE /= => xp yp xy. rewrite xy /=.
    case/andP : cycle_p => C1 C2. 
    case: (rot_to_arc C2 xp yp xy) => i p1 p2 _ _ I. 
    have {C1} C1 : cycle sedge (x :: p1 ++ y :: p2) by rewrite -I rot_cycle. 
    have {C2} C2 : uniq (x :: p1 ++ y :: p2) by rewrite -I rot_uniq.
    rewrite /cycle -cat_rcons rcons_cat cat_path last_rcons in C1. 
    case/andP : C1 => /rcons_spath P1 /rcons_spath /spath_rev P2. 
    rewrite srev_rcons in P2. 
    move/link_seq_cp in P1. move/link_seq_cp in P2.
    have D: [disjoint p1 & p2].
    { move: C2 => /= /andP [_]. rewrite cat_uniq -disjoint_has disjoint_cons disjoint_sym.
      by case/and3P => _ /andP [_ ?] _. }
    apply: contraTT D. case/subsetPn => z. rewrite !inE negb_or => A /andP [B C].
    move: (subsetP P1 _ A) (subsetP P2 _ A). 
    rewrite !(inE,mem_rcons,negbTE B,negbTE C,mem_rev) /=. 
    exact: disjointNI.
  Qed.

  Variable (U : {set G}).

  (* Lemma 16 *)
  Lemma CP_base x y : x \in CP U -> y \in CP U ->
    exists x' y':G, [/\ x' \in U, y' \in U & [set x;y] \subset cp x' y'].
  Proof.
    move => U1 U2. case/bigcupP : U1 => [[x1 x2]]. case/bigcupP : U2 => [[y1 y2]] /=.
    rewrite !inE /= => /andP[Uy1 Uy2] cp_y /andP[Ux1 Ux2] cp_x.
    case: (boolP (x \in cp y1 y2)) => [C|Wx]; first by exists y1; exists y2; rewrite subUset !sub1set C.
    case: (boolP (y \in cp x1 x2)) => [C|Wy]; first by exists x1; exists x2; rewrite subUset !sub1set C.
    gen have H,A: x x1 x2 y1 y2 {Ux1 Ux2 Uy1 Uy2 Wy cp_y} Wx cp_x /
      (x \in cp x1 y1) || (x \in cp x2 y2).
    { case/cpPn' : Wx => p irr_p av_x. 
      apply: contraTT cp_x. rewrite negb_or => /andP[/cpPn' [s s1 s2] /cpPn' [t t1 t2]].
      apply (cpNI' (p := pcat s (pcat p (prev t)))). 
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
    - apply: contraTT cp_x => C. apply: cpN_cat C _. by rewrite cp_sym.
    - apply: contraTT cp_y. apply: cpN_cat. by rewrite cp_sym.
  Qed.

  (* TOTHINK: Is it really worthwile to have this as a graph in addition to the set [CP U]? *)
  Definition CP_ := @induced link_graph (CP U).

  Lemma index_uniq_inj (T:eqType) (s : seq T) : 
    {in s, injective (index^~ s)}. 
  Proof. 
    move => x in_s y E. 
    have A : y \in s by rewrite -index_mem -E index_mem.
    by rewrite -(nth_index x in_s) E nth_index.
  Qed.

  Lemma CP_base_ (x y : CP_) : 
    exists x' y':G, [/\ x' \in U, y' \in U & [set val x;val y] \subset cp x' y'].
  Proof. exact: CP_base  (svalP x) (svalP y). Qed.

  
  Definition idx x y (p : Path x y) u := index u (nodes p).

  (* TOTHINK: This only parses if the level is at most 10, why? *)
  Notation "x '<[' p ] y" := (idx p x < idx p y) (at level 10, format "x  <[ p ]  y").
  (* (at level 70, p at level 200, y at next level, format "x  <[ p ]  y"). *)


  Lemma idx_end x y (p : Path x y) : 
    irred p -> idx p y = size (tail p).
  Proof.
    rewrite /irred nodesE => irr_p. 
    by rewrite /idx nodesE -[in index _](path_last p) index_last.
  Qed.

  Section IDX.
    Variables (x z y : G) (p : Path x z) (q : Path z y).
    Implicit Types u v : G.

    Lemma idx_inj : {in nodes p, injective (idx p) }.
    Proof.
      move => u in_s v E. rewrite /idx in E.
      have A : v \in nodes p. by rewrite -index_mem -E index_mem.
      by rewrite -(nth_index x in_s) E nth_index.
    Qed.

    Hypothesis irr_pq : irred (pcat p q).
    
    Let dis_pq : [disjoint nodes p & tail q].
    Proof. move: irr_pq. by rewrite irred_cat => /and3P[]. Qed.

    Let irr_p : irred p.
    Proof. move: irr_pq. by rewrite irred_cat => /and3P[]. Qed.

    Let irr_q : irred q.
    Proof. move: irr_pq. by rewrite irred_cat => /and3P[]. Qed.

    Lemma idxR u : u \in nodes (pcat p q) -> 
      (u \in tail q) = z <[pcat p q] u.
    Proof.
      move => A. symmetry. rewrite /idx /pcat nodesE -cat_cons index_cat -nodesE nodes_end.
      rewrite index_cat mem_pcatT in A *. case/orP: A => A.
      - rewrite A (disjointFr dis_pq A). apply/negbTE. 
        rewrite -leqNgt -!/(idx _ _) (idx_end irr_p) -ltnS. 
        rewrite -index_mem in A. apply: leq_trans A _. by rewrite nodesE.
      - rewrite A (disjointFl dis_pq A) -!/(idx _ _) (idx_end irr_p).
        by rewrite nodesE /= addSn ltnS leq_addr. 
    Qed.

    Lemma idx_catL u v : u \in tail q -> v \in tail q -> u <[pcat p q] v = u <[q] v.
    Proof.
      move => A B. rewrite /idx nodesE -!cat_cons !index_cat -nodesE.
      have C : (u \notin nodes p). 
      { apply/negP. apply: disjointE A. by rewrite disjoint_sym dis_pq. }
      have D : (v \notin nodes p). 
      { apply/negP. apply: disjointE B. by rewrite disjoint_sym dis_pq. }
      rewrite (negbTE C) (negbTE D) ltn_add2l nodesE /=.
      have -> : z == u = false. apply: contraTF C => /eqP<-. by rewrite negbK nodes_end.
      have -> : z == v = false. apply: contraTF D => /eqP<-. by rewrite negbK nodes_end.
      by rewrite ltnS.
    Qed.

    Lemma idx_nLR u : u \in nodes (pcat p q) -> 
      idx (pcat p q) z < idx (pcat p q) u -> u \notin nodes p /\ u \in tail q.
    Proof. move => A B. rewrite -idxR // in B. by rewrite (disjointFl dis_pq B). Qed.
  
  End IDX.

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

  Lemma index_rcons (T : eqType) a b (s : seq T):
    a \in b::s -> uniq (b :: s) ->
    index a (rcons s b) = if a == b then size s else index a s.
  Proof.
    case: (boolP (a == b)) => [/eqP<- _|]. 
    - elim: s a {b} => //= [|b s IH] a; first by rewrite eqxx. 
      rewrite !inE negb_or -andbA => /and4P[A B C D].
      rewrite eq_sym (negbTE A) IH //. 
    - elim: s a b => //. 
      + move => a b. by rewrite inE => /negbTE->. 
      + move => c s IH a b A. rewrite inE (negbTE A) /=. 
        rewrite inE eq_sym. case: (boolP (c == a)) => //= B C D. 
        rewrite IH //. 
        * by rewrite inE C.
        * case/and3P:D => D1 D2 D3. rewrite /= D3 andbT. exact: notin_tail D1.
  Qed.

  Lemma index_rev (T : eqType) a (s : seq T) : 
    a \in s -> uniq s -> index a (rev s) = (size s).-1 - index a s.
  Proof.
    elim: s => // b s IH. rewrite in_cons [uniq _]/=. 
    case/predU1P => [?|A] /andP [B uniq_s].
    - subst b. rewrite rev_cons index_rcons. 
      + by rewrite eqxx index_head subn0 size_rev.
      + by rewrite mem_head.
      + by rewrite /= rev_uniq mem_rev B.
    - have D : b == a = false. { by apply: contraNF B => /eqP->. }
      rewrite rev_cons index_rcons. 
      + rewrite eq_sym D IH //= D. by case s.
      + by rewrite inE mem_rev A. 
      + by rewrite /= rev_uniq mem_rev B.
  Qed.
    
  Lemma idx_srev a x y (p : Path x y) : 
    a \in p -> irred p -> idx (prev p) a = size (pval p) - idx p a.
  Proof. 
    move => A B. rewrite /idx /prev !nodesE SubK /srev. 
    case/andP: (valP p) => p1 /eqP p2. 
    by rewrite -rev_rcons -[X in rcons _ X]p2 -lastI index_rev // -?nodesE -?irredE. 
  Qed.
                                              
  Lemma idx_swap a b x y (p : Path x y) : a \in p -> b \in p -> irred p ->
    idx p a < idx p b -> idx (prev p) b < idx (prev p) a.
  Proof.
    move => aP bP ip A. 
    have H : a != b. { apply: contraTN A => /eqP->. by rewrite ltnn. }
    rewrite !idx_srev //. apply: ltn_sub2l => //. 
    apply: (@leq_trans (idx p b)) => //. 
    rewrite -ltnS -[X in _ < X]/(size (x :: pval p)).
    by rewrite -nodesE index_mem.
  Qed. 

  Lemma three_way_split x y (p : Path x y) a b :
    irred p -> a \in p -> b \in p -> a <[p] b -> 
    exists (p1 : Path x a) (p2 : Path a b) p3, 
      [/\ p = pcat p1 (pcat p2 p3), a \notin p3 & b \notin p1].
  Proof.
    move => irr_p a_in_p b_in_p a_before_b.
    case/(isplitP irr_p) def_p : {1}p / (a_in_p) => [p1 p2' irr_p1 irr_p2' D1]. subst p.
    case: (idx_nLR irr_p b_in_p) => // Y1 Y2.
    case/(isplitP irr_p2') def_p1' : {1}p2' / (tailW Y2) => [p2 p3 irr_p2 irr_p3 D2]. subst p2'.
    exists p1. exists p2. exists p3. split => //. 
    have A: a != b. { apply: contraTN a_before_b => /eqP=>?. subst b. by rewrite ltnn. }
    by rewrite mem_path inE (negbTE A) (disjointFr D2 (nodes_start p2)).
  Qed.

  Lemma CP_triangle (x y z: CP_) : 
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

    
End CheckPoints.

Notation "x ⋄ y" := (@sedge (link_graph _) x y) (at level 30).
Notation "x ⋄ y" := (@sedge (CP_ _) x y) (at level 30).

Section CheckpointOrder.

  Variables (G : sgraph) (i o : G).
  Hypothesis conn_io : connect sedge i o.
  Implicit Types x y : G.

  (* TODO: This uses upath in a nontrivial way. *)

  Lemma the_upath_proof : exists p, upath i o p.
  Proof. case/upathP : conn_io => p Hp. by exists p. Qed.
                                                                
  Definition the_upath := xchoose (the_upath_proof).

  Lemma the_upathP x y : upath i o (the_upath).
  Proof. exact: xchooseP. Qed.

  Definition cpo x y := let p := the_upath in 
                        index x (i::p) <= index y (i::p).

  Lemma cpo_trans : transitive cpo.
  Proof. move => ? ? ?. exact: leq_trans. Qed.

  Lemma cpo_total : total cpo.
  Proof. move => ? ?. exact: leq_total. Qed.

  Lemma cpo_antisym : {in cp i o&,antisymmetric cpo}.
  Proof. 
    move => x y Cx Cy. rewrite /cpo -eqn_leq. 
    have Hx: x \in i :: the_upath. 
    { move/cpP : Cx => /(_ (the_upath)). 
      apply. apply upathW. exact: the_upathP. }
    have Hy: y \in i :: the_upath.
    { move/cpP : Cy => /(_ (the_upath)). 
      apply. apply upathW. exact: the_upathP. }
    by rewrite -{2}[x](nth_index i Hx) -{2}[y](nth_index i Hy) => /eqP->.
  Qed.

  (** All paths visist all checkpoints in the same order as the canonical upath *)
  (* TOTHINK: Is this really the formulation that is needed in the proofs? *)
  Lemma cpo_order (x y : G) p : x \in cp i o -> y \in cp i o -> upath i o p -> 
    cpo x y = (index x (i::p) <= index y (i::p)).
    move => cp_x cp_y pth_p. rewrite /cpo. 
  Admitted.

End CheckpointOrder.


Lemma CP_treeI (G : sgraph) (U : {set G}) :
  (~ exists x y z : CP_ U, [/\ x -- y, y -- z & z -- x]) -> is_tree (CP_ U).
Proof.
(* - is_tree is decidable, so we can prove the contraposition
   - if [CP_ U] isn't a tree it contains an irredundant cycle of size at least 3
   - this cycle is a clique by [link_cycle] *)
Admitted.