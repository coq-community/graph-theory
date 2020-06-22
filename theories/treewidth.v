Require Import RelationClasses.

From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries digraph sgraph connectivity.
Require Import set_tac.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 

(** * Tree Decompositions and treewidth *)

(** Covering is not really required, but makes the renaming theorem
easier to state *)

Record sdecomp (T : forest) (G : sgraph) (B : T -> {set G}) := SDecomp
  { sbag_cover x : exists t, x \in B t; 
    sbag_edge x y : x -- y -> exists t, (x \in B t) && (y \in B t);
    sbag_conn x t1 t2  : x \in B t1 -> x \in B t2 ->
      connect (restrict [pred t | x \in B t] sedge) t1 t2}.

Arguments sdecomp T G B : clear implicits.

Lemma sdecomp_subrel (V : finType) (e1 e2 : rel V) (T:forest) (D : T -> {set V}) 
      (e1_sym : symmetric e1) (e1_irrefl : irreflexive e1) 
      (e2_sym : symmetric e2) (e2_irrefl : irreflexive e2):
  subrel e2 e1 -> 
  sdecomp T (SGraph e1_sym e1_irrefl) D -> 
  sdecomp T (SGraph e2_sym e2_irrefl) D.
Proof.
  move => E [D1 D2 D3]. split => //=.
  move => x y /= xy. apply: D2 => /=. exact: E xy.
Qed.

Lemma sdecomp_tree_subrel 
      (G:sgraph) (V : finType) (D : V -> {set G}) (e1 e2 : rel V) 
      (e1_sym : symmetric e1) (e1_irrefl : irreflexive e1)
      (e2_sym : symmetric e2) (e2_irrefl : irreflexive e2)
      (e1_forest : is_forest [set: SGraph e1_sym e1_irrefl])
      (e2_forest : is_forest [set: SGraph e2_sym e2_irrefl]):
  subrel e1 e2 -> 
  sdecomp (Forest e1_forest) G D -> sdecomp (Forest e2_forest) G D.
Proof.
  move => sub12 [D1 D2 D3]. split => // x t1 t2 X1 X2.
  move: (D3 x _ _ X1 X2). apply: connect_mono. 
  move => u v /=. rewrite -!andbA => /and3P [-> -> /=]. exact: sub12.
Qed.

Definition triv_sdecomp (G : sgraph) :
  sdecomp tunit G (fun _ => [set: G]).
Proof.
  split => [x|e|x [] [] _ _]; try by exists tt; rewrite !inE.
  exact: connect0.
Qed.

Lemma decomp_iso (G1 G2 : sgraph) (T : forest) B1 : 
  sdecomp T G1 B1 -> diso G1 G2 -> 
  exists2 B2, sdecomp T G2 B2 & width B2 = width B1.
Proof.
  (* TODO: update proof to abstract against concrete implem of [diso] *)
  case => D1 D2 D3 [[g f can_g can_f] /= hom_g hom_f]. 
  exists (fun t => [set g x | x in B1 t]). 
  - split.
    + move => x. case: (D1 (f x)) => t Ht. exists t. 
      apply/imsetP. by exists (f x).
    + move => x y /hom_f /D2 [t] /andP [t1 t2]. 
      exists t. by rewrite -[x]can_f -[y]can_f !mem_imset. 
    + move => x t1 t2 /imsetP [x1] X1 ? /imsetP [x2] X2 P. subst.
      have ?: x1 = x2 by rewrite -[x1]can_g P can_g. subst => {P}.
      have := D3 _ _ _ X1 X2. 
      apply: connect_mono => t t' /=. 
      rewrite !inE -andbA => /and3P [A B ->]. by rewrite !mem_imset.
  - rewrite /width. apply: eq_bigr => i _. rewrite card_imset //.
    apply: can_inj can_g.
Qed.

Definition triv_decomp (G : sgraph) :
  sdecomp tunit G (fun _ => [set: G]).
Proof. 
  split => [x|e|x [] [] _ _]; try by exists tt; rewrite !inE.
  exact: connect0.
Qed.

Lemma decomp_small (G : sgraph) k : #|G| <= k -> 
  exists T D, [/\ sdecomp T G D & width D <= k].
Proof. 
  exists tunit; exists (fun => setT). split.
  - exact: triv_decomp.
  - by rewrite /width (big_pred1 tt _) // cardsT. 
Qed.

(** ** Renaming *)

Lemma rename_decomp (T : forest) (G H : sgraph) D (dec_D : sdecomp T G D) (h : G -> H) : 
  hom_s h -> 
  surjective h -> 
  (forall x y : H, x -- y -> exists x0 y0, [/\ h x0 = x, h y0 = y & x0 -- y0]) ->
  (forall x y, h x = h y -> 
    (exists t, (x \in D t) && (y \in D t)) \/ (exists t1 t2, [/\ t1 -- t2, x \in D t1 & y \in D t2])) ->
  @sdecomp T _ (rename D h).
Proof.
  move => hom_h sur_h sur_e comp_h. 
  split. 
  - move => x. pose x0 := iinv (sur_h x). case: (sbag_cover dec_D x0) => t Ht.
    exists t. apply/imsetP. by exists x0; rewrite // f_iinv.
  - move => x y xy. case: (sur_e _ _ xy) => x0 [y0] [hx0 hy0 e0].
    case: (sbag_edge dec_D e0) => t /andP [t1 t2]. 
    exists t. apply/andP;split;apply/imsetP;by [exists x0|exists y0].
  - move => x t0 t1 bg1 bg2. 
    case/imsetP : bg1 bg2 => x0 A B /imsetP [x1 C E]. subst.
    have connT x t t' : x \in D t -> x \in D t' -> 
      connect (restrict [pred t | h x \in (rename D h) t] sedge) t t'.
    { move => Ht Ht'. 
      apply: connect_mono (sbag_conn dec_D Ht Ht') => u v /= /andP [/andP [X Y] Z].
      rewrite Z andbT. apply/andP;split; by apply/imsetP;exists x. }
    case: (comp_h _ _ E).
    + case => t /andP [F I]. 
      apply: (connect_trans (y := t)); [exact: connT|rewrite E;exact:connT].
    + move => [t0'] [t1'] [t0t1 H0 H1].
      apply: connect_trans (connT _ _ _ A H0) _.
      rewrite E. apply: connect_trans (connect1 _) (connT _ _ _ H1 C).
      by rewrite /= t0t1 !inE -{1}E !mem_imset.
Qed.

Lemma rename_width (T : forest) (G : sgraph) (D : T -> {set G}) (G' : finType) (h : G -> G') :
  width (rename D h) <= width D.
Proof. apply: bigmax_leq_pointwise => t _. exact: leq_imset_card. Qed.

(** ** Disjoint Union *)

Section JoinT.
  Variables (T1 T2 : forest).

  Lemma sub_inl (a b : T1) (p : @Path (sjoin T1 T2) (inl a) (inl b)) :
    {subset p <= codom inl}.
  Proof. 
    apply: path_closed; first by rewrite codom_f. 
    do 2 case => ? //; rewrite ?codom_f //. by case/codomP => ?.
  Qed.

  Lemma sub_inr (a b : T2) (p : @Path (sjoin T1 T2) (inr a) (inr b)) :
    {subset p <= codom inr}.
  Proof. 
    apply: path_closed; first by rewrite codom_f. 
    do 2 case => ? //; rewrite ?codom_f //. by case/codomP => ?.
  Qed.

  Arguments inl_inj [A B].
  Prenex Implicits inl_inj.

  Lemma join_is_forest : is_forest [set: sjoin T1 T2].
  Proof with try solve [exact: inl_inj|exact: inr_inj
                       |exact: sub_inl|exact: sub_inr].
    move => [a|a] [b|b] p q [Ip _] [Iq _].
    - case: (lift_Path (p' := p)) => //...
      case: (lift_Path (p' := q)) => //...
      move => p' Np I q' Nq I'. 
      have E : p' = q'. { apply: forestP; by rewrite ?I ?I'. }
      apply/eqP. by rewrite -nodes_eqE -Nq -E Np.
    - move: (Path_connect p). by rewrite join_disc.
    - move: (Path_connect p). by rewrite sconnect_sym join_disc.
    - case: (lift_Path (p' := p)) => //...
      case: (lift_Path (p' := q)) => //...
      move => p' Np I q' Nq I'. 
      have E : p' = q'. { apply: forestP; by rewrite ?I ?I'. }
      apply/eqP. by rewrite -nodes_eqE -Nq -E Np.
  Qed.
      
  Definition tjoin := @Forest (sjoin T1 T2) join_is_forest.

  Definition decompU (G1 G2 : sgraph) (D1 : T1 -> {set G1}) (D2 : T2 -> {set G2}) : 
    tjoin -> {set sjoin G1 G2} := 
    [fun a => match a with 
          | inl a => [set inl x | x in D1 a]
          | inr a => [set inr x | x in D2 a]
          end].

  Lemma join_decomp (G1 G2 : sgraph) (D1 : T1 -> {set G1}) (D2 : T2 -> {set G2})  :
    sdecomp T1 G1 D1 -> sdecomp T2 G2 D2 -> sdecomp tjoin (sjoin G1 G2) (decompU D1 D2).
  Proof using.
    move => dec1 dec2. split.
    - move => [x|x]. 
      + case: (sbag_cover dec1 x) => t Ht. exists (inl t) => /=. by rewrite mem_imset.
      + case: (sbag_cover dec2 x) => t Ht. exists (inr t) => /=. by rewrite mem_imset.
    - move => [x|x] [y|y] // xy. 
      + case: (sbag_edge dec1 xy) => t /andP [H1 H2]. exists (inl t) => /=. by rewrite !mem_imset.
      + case: (sbag_edge dec2 xy) => t /andP [H1 H2]. exists (inr t) => /=. by rewrite !mem_imset.
    - have inl_inr x t : inl x \in decompU D1 D2 (inr t) = false.
      { rewrite /decompU /=. apply/negbTE/negP. by case/imsetP. }
      have inr_inl x t : inr x \in decompU D1 D2 (inl t) = false.
      { rewrite /decompU /=. apply/negbTE/negP. by case/imsetP. }
      move => [x|x] [t1|t1] [t2|t2] /= ; rewrite ?inl_inr ?inr_inl // => A B. 
      + pose e := restrict [pred t | x \in D1 t] sedge.
        apply: (homo_connect (e:= e) (f := inl)).
        * move => a b. rewrite /e /= !in_simpl -andbA => /and3P[? ? ?].  
          by rewrite !mem_imset.
        * apply: sbag_conn => //. 
          move: A. by case/imsetP => ? ? [->].
          move: B. by case/imsetP => ? ? [->].
      + pose e := restrict [pred t | x \in D2 t] sedge.
        apply: (homo_connect (e:= e) (f := inr)).
        * move => a b. rewrite /e /= !in_simpl -andbA => /and3P[? ? ?].  
          by rewrite !mem_imset.
        * apply: sbag_conn => //. 
          move: A. by case/imsetP => ? ? [->].
          move: B. by case/imsetP => ? ? [->].
  Qed.

  Lemma join_width (G1 G2 : sgraph) (D1 : T1 -> {set G1}) (D2 : T2 -> {set G2}) : 
    width (decompU D1 D2) <= maxn (width D1) (width D2).
  Proof.
    apply/bigmax_leqP => [[x|x] _]. 
    all: rewrite /decompU /= card_imset; try solve [exact: inl_inj|exact: inr_inj].
    - apply: leq_trans (leq_maxl _ _). exact: leq_bigmax.
    - apply: leq_trans (leq_maxr _ _). exact: leq_bigmax.
  Qed.

End JoinT.


(** ** Link Construction (without intermediate node) *)

(* TOTHINK: The assumption [s1 != s2] is redundant, but usually available. *)
Lemma add_edge_break (G : sgraph) (s1 s2 x y : G) (p : @Path (add_edge s1 s2) x y) :
  s1 != s2 ->
  let U := [set s1;s2] in
  irred p -> ~~ @connect G sedge x y ->
  exists u v : G, exists q1 : Path x u, exists q2 : Path v y, 
  [/\ u \in U, v \in U, u != v & nodes p = nodes q1 ++ nodes q2].
Proof.
  move => D U Ip NCxy.
  (* have D : s1 != s2. { } *)
  have/andP [H1 H2] : (s1 \in p) && (s2 \in p).
  { rewrite -[_ && _]negbK negb_and. apply: contraNN NCxy => H. 
    case: (add_edge_avoid p H) => p' Ep. exact: Path_connect. }
  case: (@split_at_first (add_edge s1 s2) (mem U) _ _ p s1) => //.
  { by rewrite !inE eqxx. }
  move => z [p1] [p2] [P1 P2 P3]. subst U.
  wlog ? : s1 s2 p D Ip NCxy H1 H2 z p1 p2 P1 P3 {P2 H1} / z = s1.
  { move => W. case/setUP : P2 => /set1P P2; subst z.
    - by apply W with s1 p1 p2. 
    - case: (add_edge_pathC p) => p' Ep.
      case: (add_edge_pathC p1) => p1' Ep1.
      case: (add_edge_pathC p2) => p2' Ep2.
      pose G':= add_edge s1 s2. pose G'' := add_edge s2 s1.
      case: (W s2 s1 p' _ _ _ _ _ s2 p1' p2') => //.
      + by rewrite eq_sym.
      + by rewrite irredE Ep.
      + by rewrite (@mem_path G'') Ep -(@mem_path G').
      + by rewrite (@mem_path G'') Ep -(@mem_path G').
      + apply/eqP. by rewrite -nodes_eqE Ep P1 !nodes_pcat Ep1 Ep2.
      + move => z. rewrite setUC. rewrite (@mem_path G'') Ep1 -(@mem_path G').
        exact: P3.
      + move => u [v] [q1] [q2]. rewrite setUC => [[? ? ? E]]. 
        exists u. exists v. exists q1. exists q2. split => //. congruence. }
  subst. move: H2. rewrite (@mem_pcat (add_edge s1 s2)).
  have {P3} s2p1 : s2 \notin p1. apply: contraNN D => C. by rewrite [s2]P3 ?inE ?eqxx.
  rewrite (negbTE s2p1) /= => s2p2. case/irred_catE : Ip => Ip1 Ip2 Ip12. 
  case: (splitL p2) => [|z [s1z] [pR [def_p2 _]]].
  { apply: contraNneq D => ?;subst y. 
    move: s2p2. by rewrite [p2]irredxx // mem_idp eq_sym. }
  move: Ip2. rewrite def_p2 irred_edgeL => /andP [s1pR IpR].
  case: (add_edge_avoid p1) => [|p1' Ep]; first by rewrite s2p1.
  case: (add_edge_avoid pR) => [|pR' ER]; first by rewrite s1pR.
  have ? : z = s2. 
  { apply: contraNeq NCxy => zNs2. move: (s1z) => /=. 
    rewrite /edge_rel/= (negbTE zNs2) [z == s1]eq_sym (sg_edgeNeq s1z) ?eqxx.
    case/or3P => //= s1z'.
    exact: (Path_connect (pcat p1' (pcat (edgep s1z') pR'))). }
  subst z. exists s1; exists s2; exists p1'; exists pR'. rewrite !inE ?eqxx. split => //.
  rewrite Ep ER. by rewrite !nodesE. 
Qed.

Lemma path_return (G : sgraph) z (A : {set G}) (x y : G) (p : Path x y) :
  x \in A -> y \in A -> irred p -> 
  (forall u v, u -- v -> u \in A -> v \notin A -> u = z) -> p \subset A.
Abort.

Section AddEdge.
  Variables (T : forest) (t0 t1 : T).
  Hypothesis discT : ~~ connect sedge t0 t1.

  Let T' := add_edge t0 t1.
  Notation Path G x y := (@Path G x y).

  Lemma add_edge_is_forest : is_forest [set: T'].
  Proof using discT.
    apply: unique_forestT => x y p q Ip Iq. 
    have D : t0 != t1 by apply: contraNneq discT => ->.
    case: (boolP (@connect T sedge x y)) => [|NC].
    - case/connect_irredP => r Ir. apply/eqP. rewrite -nodes_eqE. 
      wlog suff {q Iq} S : p Ip / nodes p = nodes r.
      { by rewrite (S p) ?(S q). }
      suff S : (t0 \notin p) || (t1 \notin p).
      { case: (add_edge_avoid p S) => p' Ep.
        by rewrite -Ep (@forestP _ _ _ p' r) // irredE Ep. }
      rewrite -negb_and. apply:contraNN discT => /andP [T1 T2].
      wlog before : x y p Ip D r Ir T1 T2 / t0 <[p] t1.
      { move => W. case: (ltngtP (idx p t0) (idx p t1)).
        - by apply W with r.
        - rewrite idx_swap //. 
          apply W with (prev r); rewrite ?prev_irred //.
          all: by rewrite (@mem_prev (add_edge t0 t1)). 
        - move/idx_inj. rewrite -mem_path. by move/(_ T1)->. }
      case:(three_way_split Ip T1 T2 before) => p1 [p2] [p3] [_ P2 P3].
      case:(add_edge_avoid p1 _) => [|p1' _] ; first by rewrite P3.
      case:(add_edge_avoid p3 _) => [|p3' _] ; first by rewrite P2.
      exact: (Path_connect (pcat (prev p1') (pcat r (prev p3')))).
    - case:(add_edge_break D Ip NC) => u [u'] [p1] [p2] [U1 U2 U3 E1].
      wlog [? ?]: x y p q Ip Iq NC u u' p1 p2 E1 {U1 U2 U3} / u = t0 /\ u' = t1.
      { move => W. 
        case/setUP : U1 => /set1P U1; case/setUP : U2 => /set1P U2; subst.
        - by rewrite eqxx in U3.
        - exact: (W x y p q _ _ _ t0 t1 p1 p2).
        - have H := (W y x (prev p) (prev q) _ _ _ t0 t1 (prev p2) (prev p1)).
          rewrite -[p]prevK H ?prevK ?prev_irred // 1?sconnect_sym //.
          by rewrite !nodes_prev E1 rev_cat.
        - by rewrite eqxx in U3. }
      subst. 
      case:(add_edge_break D Iq NC) => v [v'] [q1] [q2] [V1 V2 V3 E2].
      have {V1} V1 : v = t0.
      { apply: contraTeq V1 => H. rewrite !inE (negbTE H) /=.
        apply: contraNneq discT => <-. exact: (Path_connect (pcat (prev p1) q1)). }
      have {V2 V3} V2 : v' = t1. 
      { subst. rewrite !inE eq_sym (negbTE V3) in V2. exact/eqP. }
      subst. apply/eqP. rewrite -nodes_eqE E1 E2.
      rewrite !irredE E1 E2 !cat_uniq in Ip Iq.
      case/and3P : Ip => [? _ ?]. case/and3P : Iq => [? _ ?].
      rewrite (@forestP _ _ _ p1 q1) 1?(@forestP _ _ _ p2 q2) //.
  Qed.

End AddEdge.

(** ** Link Construction (with intermediate node) *)


Section Link.
  Variables (T : forest) (U : {set T}).
  Hypothesis U_disc : {in U &,forall x y, x != y -> ~~ connect sedge x y}.
  
  Definition link := add_node T U.
  
  Lemma link_unique_lift (x y : link) : 
    unique (fun p : Path x y => irred p /\ None \notin p).
  Proof. 
    move: x y => [x|] [y|] p q [Ip Np] [Iq Nq]; 
      try by rewrite ?(@path_end link) ?(@path_begin link) in Np Nq.
    gen have H,Hp : p Ip Np / {subset p <= codom Some}.
    { move => [u|]; by rewrite ?codom_f // (negbTE Np). }
    case: (lift_Path (p' := p)) => //. 
    case: (lift_Path (p' := q)) => //; first exact: H.
    move => p0 Ep Ip0 q0 Eq Iq0. 
    have E : p0 = q0. apply: forestP; by rewrite ?Ip0 ?Iq0.
    apply/eqP. rewrite -nodes_eqE. by apply/eqP;congruence.
  Qed.

  Lemma link_bypass (x y : T) (p : @Path link (Some x) (Some y)) : 
    x \in U -> y \in U -> None \notin p -> x = y.
  Proof. 
    move => xU yU Np. case: (lift_Path (p' := p)) => // => [|p' _ _].
    { move => [u|]; by rewrite ?codom_f // (negbTE Np). }
    apply: contraTeq isT => /U_disc => /(_ xU yU). 
    by rewrite (Path_connect p').
  Qed.

  Lemma link_unique_None (x : link) : 
    unique (fun p : @Path link None x => irred p).
  Proof.
    move: x => [x|] p q Ip Iq; last by rewrite (irredxx Ip) (irredxx Iq).
    case: (splitL p) => // [] [y|] [/= xy] [p'] [P1 _] //. 
    case: (splitL q) => // [] [z|] [/= xz] [q'] [Q1 _] //. subst. 
    move: Ip Iq. rewrite !irred_edgeL => /andP[Np Ip] /andP[Nq Iq].
    have ? : y = z. { 
      apply: (link_bypass (p := pcat p' (prev q'))) => //.
      by rewrite (@mem_pcat link) mem_prev negb_or Np Nq. }
    subst. congr pcat; first exact: val_inj. exact: link_unique_lift.
  Qed.

  Lemma link_has_None (x y : link) (p q : Path x y) : 
    irred p -> irred q -> None \in p -> None \in q.
  Proof using U_disc.
    move: x y p q => [x|] [y|] p q; 
      try by rewrite ?(@path_end link) ?(@path_begin link).
    move => Ip Iq Np. apply: contraTT isT => Nq. 
    case/(isplitP Ip) def_p : _  / Np => [p1 p2 Ip1 Ip2 I12]. subst.
    case: (splitL p2) => // [] [a|] [/= na] [p2'] [D _] //. 
    case: (splitL (prev p1)) => // [] [b|] [/= nb] [p1'] [D' _] //. 
    have ? : b = a; last subst.
    { suff [p Hp] : exists p : @Path link (Some b) (Some a), None \notin p.
      { exact: link_bypass Hp. }
      exists (pcat p1' (pcat q (prev p2'))). 
      rewrite !(@mem_pcat link) mem_prev (negbTE Nq) /= negb_or. 
      move: Ip1 Ip2. rewrite -irred_rev D' D !irred_edgeL. by do 2 case: (_ \notin _). }
    move: (I12 (Some a)). case/(_ _ _)/Wrap => //; rewrite ?mem_pcat ?path_end //.
    by rewrite -mem_prev D' mem_pcat path_begin.
  Qed.

  Lemma link_is_forest : is_forest [set: link].
  Proof.
    apply: unique_forestT => x y p q Ip Iq. 
    case: (boolP (None \in p)) => Np.
    - have Nq := link_has_None Ip Iq Np.
      case/(isplitP Ip) def_p : _ / Np => [p1 p2 Ip1 Ip2 _].
      case/(isplitP Iq) def_q : _ / Nq => [q1 q2 Iq1 Iq2 _].
      congr pcat. 
      + apply: prev_inj. apply: link_unique_None; by rewrite irred_rev.
      + exact: link_unique_None.
    - suff Nq : None \notin q by apply: link_unique_lift. 
      apply: contraNN Np. exact: link_has_None.
  Qed.
      
  Definition tlink := @Forest link link_is_forest.

  Definition decompL (G:sgraph) (D : T -> {set G}) A a := 
    match a with Some x => D x | None => A end.

  Lemma decomp_link (G : sgraph) (D : T -> {set G}) (A  : {set G}) : 
    A \subset \bigcup_(t in U) D t ->
    sdecomp T G D -> @sdecomp tlink G (decompL D A).
  Proof.
    move => HA decD. split => //.
    - move => x. case: (sbag_cover decD x) => t Ht. by exists (Some t). 
    - move => x y xy. case: (sbag_edge decD xy) => t Ht. by exists (Some t).
    - have X x a : x \in D a -> x \in A ->
        connect (restrict [pred t | x \in decompL D A t] (add_node_rel U)) 
                (Some a) None.
      { move => H1 H2. move/(subsetP HA) : (H2) => /bigcupP [t Ht1 Ht2].
        apply: (connect_trans (y := Some t)).
        - move: (sbag_conn decD H1 Ht2). exact: homo_connect.
        - apply: connect1 => /=; by rewrite !in_simpl H2 Ht1. }
      move => x [a|] [b|] /= H1 H2; last exact: connect0. 
      + move: (sbag_conn decD H1 H2). exact: homo_connect. 
      + exact: X.
      + rewrite (@srestrict_sym link). exact: X. 
  Qed.

  Lemma width_link (G : sgraph) (D : T -> {set G}) (A  : {set G}) : 
    width (decompL D A) <= maxn (width D) #|A|.
  Proof.
    apply/bigmax_leqP => [] [t|] _ /=; last by rewrite ?leq_maxr. 
    apply: leq_trans (leq_maxl _ _). exact: leq_bigmax.
  Qed.

End Link.

(** ** Every clique is contained in some bag *)

Section DecompTheory.
  Variables (G : sgraph) (T : forest) (B : T -> {set G}).
  Implicit Types (t u v : T) (x y z : G).

  Hypothesis decD : sdecomp T G B.

  Arguments sbag_conn [T G B] dec x t1 t2 : rename.


  (** This proof is based on a stackexchange post to be found here:
      https://math.stackexchange.com/questions/1227867/
      a-clique-in-a-tree-decomposition-is-contained-in-a-bag 

      The assumption [0 < #|S|] ensures that [T] is nonempty. *)
  Lemma decomp_clique (S : {set G}): 
    0 < #|S| -> clique S -> exists t : T, S \subset B t.
  Proof. 
    elim/card_ind : S => S IH inh_S clique_S.
    case: (leqP #|S| 1) => [card_S | card_S {inh_S}]. 
    - have/cards1P [x ->] : #|S| == 1 by rewrite eqn_leq card_S.
      case: (sbag_cover decD x) => t A. exists t. by rewrite sub1set. 
    - have [v [v0] [Hv Hv0 X]] := card_gt1P (card_S).
      pose S0 := S :\ v.
      pose T0 := [set t | S0 \subset B t]. 
      wlog /forall_inP HT0 : / [forall t in T0, v \notin B t].
      { case: (boolP [forall _ in _,_]) => [H|/forall_inPn [t H1 /negPn H2] _]; first by apply.
        exists t. rewrite inE in H1. by rewrite -(setD1K Hv) subUset sub1set H2 H1. }
      have HT0' t : v \in B t -> ~~ (S0 \subset B t).
      { apply: contraTN => C. apply: HT0. by rewrite inE. }
      have pairs x y : x \in S -> y \in S -> exists t, x \in B t /\ y \in B t.
      { move => xS yS. case: (altP (x =P y)) => [?|xDy].
        - subst y. case: (sbag_cover decD x) => t A. by exists t. 
        - move/clique_S : xDy. case/(_ _ _)/Wrap => // xy.
          case: (sbag_edge decD xy) => t A. exists t. exact/andP. }
      (* obtain some node [c] whose bag contains [[set v,v0]] and
      consider its subtree outside of T0 *)
      have [c [Hc1 Hc2]] : exists t, v \in B t /\ v0 \in B t by apply: pairs. 
      pose C := [set t in [predC T0] | connect (restrict [predC T0] sedge) c t].
      have inC: c \in C. { by rewrite !inE connect0 andbT HT0'. }
      have con_C : connected C. 
      { apply: connected_restrict_in. move: inC. rewrite inE. by case/andP. }
      have dis_C : [disjoint C & T0]. 
      { rewrite disjoints_subset /C. apply/subsetP => t. rewrite !inE. by case/andP. }
      have [t0 [c0 [Ht0 Hc0 tc0]]] : exists t0 c0, [/\ t0 \in T0, c0 \in C & t0 -- c0].
      { have [t Ht] : exists t, S0 \subset B t.
        { case: (IH S0 _ _) => [|||t Ht]; last by exists t.
          - by rewrite [#|S|](cardsD1 v) Hv.
          - apply/card_gt0P. exists v0. by rewrite !inE eq_sym X.
          - apply: sub_in2W clique_S; apply/subsetP; by rewrite subD1set. }
        have A : v0 \in B t. { apply (subsetP Ht). by rewrite !inE eq_sym X. }
        have/connect_irredRP [|p Ip _] := (sbag_conn decD v0 c t Hc2 A).
        { apply: contraTneq inC => ->. by rewrite !inE Ht. }
        move: (c) p Ip (inC). apply: irred_ind; first by rewrite !inE Ht.
        move => x z p xz Ip xp IHp xC.
        case: (boolP (z \in C)) => [|zNC {IHp}] ; first exact: IHp.
        exists z; exists x. rewrite sgP. split => //. apply: contraNT zNC => H.
        rewrite 2!inE /= in xC. case/andP : xC => H1 H2.
        rewrite 2!inE /= (negbTE H) /=. apply: connect_trans H2 _.
        apply: connect1 => /=. by  rewrite 2!inE H1 2!inE xz H. }
      (* Every path into [C] must use this edge (and [c0]) *)
      have t0P c' (p : Path t0 c') : irred p -> c' \in C -> c0 \in p.
      { move => Ip inC'.
        case: (altP (c0 =P c')) => [-> |?]. by rewrite path_end.
        have/connect_irredRP [//|q Iq /subsetP subC] := con_C _ _ Hc0 inC'.
        suff -> : p = pcat (edgep tc0) q by rewrite mem_pcat path_end.
        apply: forest_is_forest; (repeat split) => //.
        rewrite irred_edgeL Iq andbT.
        apply: contraTN Ht0 => /subC => H. by rewrite (disjointFr dis_C H). }
      (* We show that [B c0] contains the full clique *)
      suff A : c0 \in T0 by case: (disjointE dis_C Hc0 A).
      rewrite inE. apply/subsetP => u u_in_S0.
      have Hu: u \in B t0. { rewrite inE in Ht0. exact: (subsetP Ht0). }
      have [cu [Hcu1 Hcu2]] : exists t, u \in B t /\ v \in B t. 
      { apply: (pairs u v) => //. move: u_in_S0. rewrite inE. by case: (_ \notin _). }
      case/connect_irredRP:(sbag_conn decD u t0 cu Hu Hcu1) => [|q irr_p /subsetP has_u]. 
      { apply: contraTneq Hcu2 => <-.  exact: HT0. }
      suff Hq : c0 \in q. { move/has_u : Hq. by rewrite inE. }
      apply: t0P irr_p _. rewrite !inE /= HT0' //=. 
      move: (sbag_conn decD v c cu Hc1 Hcu2). 
      apply: connect_mono => t t' /=. 
      rewrite !inE -andbA => /and3P [*]. by rewrite !HT0'.
  Qed.
      
End DecompTheory.
Arguments rename_decomp [T G H D].

(** decompositsions of ['K_m] have width at least [m] *)

Lemma Km_bag m (T : forest) (D : T -> {set 'K_m.+1}) : 
  sdecomp T 'K_m.+1 D -> exists t, m.+1 <= #|D t|.
Proof.
  move => decD.
  case: (@decomp_clique _ _ _ decD setT _ _) => //.
  - by rewrite cardsT card_ord.
  - move => t A. exists t. rewrite -{1}[m](card_ord m) -cardsT. 
    apply: leq_trans (subset_leq_card A). by rewrite !cardsT !card_ord.
Qed.

Lemma Km_width m (T : forest) (D : T -> {set 'K_m.+1}) : 
  sdecomp T 'K_m.+1 D -> m.+1 <= width D.
Proof. case/Km_bag => t Ht. apply: leq_trans Ht _. exact: leq_bigmax. Qed.

(** Obtaining a tree decomposition from tree decompositions of (induced) subgraphs *)
Lemma separation_decomp (G:sgraph) (V1 V2 : {set G}) T1 T2 B1 B2 :
  @sdecomp T1 (induced V1) B1 -> @sdecomp T2 (induced V2) B2 -> 
  separation V1 V2 -> clique (V1 :&: V2) ->
  exists T B, @sdecomp T G B /\ width B <= maxn (width B1) (width B2).
Proof.
  move => dec1 dec2 sepV clV.
  have dec12 := join_decomp dec1 dec2.
  set G' := sjoin _ _ in dec12.
  set T := tjoin T1 T2 in dec12.
  set B : tjoin T1 T2 -> {set G'}:= decompU B1 B2 in dec12.
  pose h (x : G') : G := match x with inl x => val x | inr x => val x end.
  case: (boolP (0 < #|V1 :&: V2|)) => [cliquen0|clique0].
  - (* clique not empty *)
    case/card_gt0P : cliquen0 => v0 /setIP [v01 v02].
    have HVx (V : {set G}) : (V = V1) \/ V = V2 -> v0 \in V ->
       let V' := val @^-1: (V1 :&: V2) : {set induced V} in 0 < #|V'| /\ clique V'.
    { move => HV xV /=. split.
      - apply/card_gt0P; exists (Sub v0 xV). rewrite inE /=. case: HV => ?; by set_tac.
      - move => u v. rewrite [_:&:_]lock !inE -lock -val_eqE. exact: clV. }
    set S := V1 :&: V2 in HVx.
    pose S1 := val @^-1: S : {set induced V1}. 
    pose S2 := val @^-1: S : {set induced V2}.
    have [cln01 clS1] : 0 < #|S1| /\ clique S1 by apply: HVx; auto.
    have [cln02 clS2] : 0 < #|S2| /\ clique S2 by apply: HVx; auto.
    case: (decomp_clique dec1 cln01 clS1) => t1 Ht1.
    case: (decomp_clique dec2 cln02 clS2) => t2 Ht2.
    have dis_t1_t2 : ~~ connect (@sedge T)(inl t1) (inr t2) by rewrite join_disc.
    set T' := Forest (add_edge_is_forest dis_t1_t2).
    have dec12' : sdecomp T' G' B. 
    { apply: sdecomp_tree_subrel dec12. exact: subrelUl. }
    case/Wrap: (rename_decomp dec12' h). case/(_ _ _ _ _)/Wrap.
    + by move => [u|u] [v|v].
    + move => v. 
      case/setUP : (sepV.1 v) => Hv; apply/codomP; by [exists (inl (Sub v Hv))|exists (inr (Sub v Hv))].
    + move => x y xy.
      suff: x \in V1 /\ y \in V1 \/ x \in V2 /\ y \in V2.
      { case => [[Hx Hy]|[Hx Hy]].
        - by exists (inl (Sub x Hx)); exists (inl (Sub y Hy)). 
        - by exists (inr (Sub x Hx)); exists (inr (Sub y Hy)). }
      case: (boolP (x \in V1));case: (boolP (y \in V1)) => Hy Hx; 
        first [by left|right; apply/andP].
      * rewrite [y \in _](sep_inR sepV) // andbT. 
        apply: contraTT xy => H. by rewrite sepV.
      * rewrite [x \in _](sep_inR sepV) //=.
        apply: contraTT xy => H. by rewrite sgP sepV.
      * by rewrite !(sep_inR sepV).
    + case: dec1 => dec1A dec1B dec1C. case: dec2 => dec2A dec2B dec2C.
      have X (x : induced V1) (y : induced V2) : val x = val y -> 
         ((inl x \in B (inl t1) = true) * (inr y \in B (inr t2) = true))%type.
      { move => Exy. rewrite /B /decompU /= !mem_imset //.
        - apply: (subsetP Ht2). rewrite !inE -{1}Exy. 
          apply/andP; split; exact: valP.
        - apply: (subsetP Ht1). rewrite !inE {2}Exy.
          apply/andP; split; exact: valP. }
      move => [x|x] [y|y]; simpl h.
      * move/val_inj => ?;subst y. 
        case: (dec1A x) => t Ht. left. exists (inl t). 
        by rewrite /B /decompU /= mem_imset.
      * move => Exy. right. exists (inl t1). exists (inr t2).
        by rewrite /edge_rel/= !(X _ _ Exy) /= !eqxx.
      * move/esym => Eyx. right. exists (inr t2). exists (inl t1). 
        by rewrite /edge_rel/= !(X _ _ Eyx) /= !eqxx.
      * move/val_inj => ?;subst y. 
        case: (dec2A x) => t Ht. left. exists (inr t). 
        by rewrite /B /decompU /= mem_imset.
    + move => decRB. do 2 eexists. split. eapply decRB.
      apply: leq_trans (rename_width _ _) _. exact: join_width.
  - (* clique size 0 *)
    suff iso: diso G' G.
    + case: (decomp_iso dec12 iso) => B' sdecB' wB'B.
      exists T; exists B'. split => //. by rewrite wB'B join_width.
    + suff HH: V2 = ~:V1.
      { rewrite /G' HH. apply ssplit_disconnected. move => x y xV1 yNV1.
        rewrite (sepV.2 x y) => //. by rewrite HH inE xV1. }
      apply/setP => z. rewrite inE. case: (boolP (z \in V1)) => Hz.
      * apply: contraNF clique0 => H. apply/card_gt0P. exists z. by set_tac.
      * apply: contraTT (sepV.1 z). by set_tac.
Qed.

(** ** Forests have treewidth 1 *)

Lemma forest_vseparator (G : sgraph) : 
  is_forest [set: G] -> 3 <= #|G| -> exists2 S : {set G}, vseparator S & #|S| <= 1.
Proof.
  move => forest_G card_G. 
  have {card_G} [x [y [xDy xy]]] := forest3 forest_G card_G.
  have [/connect_irredP [p Ip]|nCxy]:= (boolP (connect sedge x y)).
  move/forestT_unique in forest_G.
  - have/set0Pn [z z_p] : interior p != set0.
    { apply: contraNneq xy => Ip0. by case: (interior0E xDy Ip Ip0). }
    exists [set z]; last by rewrite cards1. 
    exists x; exists y; apply: separatesI. 
    move: (interiorN z_p); rewrite !inE negb_or ![z == _]eq_sym => /andP[-> ->].
    split => // q Iq. exists z; rewrite ?inE ?eqxx //.
    apply: interiorW. by rewrite (forest_G _ _ _ _ Iq Ip).
  - exists set0; last by rewrite cards0. exists x;exists y. split; rewrite ?inE // => p.
    case: notF. apply: contraNT nCxy => _. exact: Path_connect p.
Qed.

Lemma forest_TW1 (G : sgraph) : 
  is_forest [set: G] -> exists T B, sdecomp T G B /\ width B <= 2.
Proof.
  elim/(size_ind (fun G : sgraph => #|G|)) : G => G Hind forest_G. 
  have:= forest_vseparator forest_G.
  case: leqP => [Glt2 _|Ggt2 /(_ isT) [S sepS Slt2]]; first exact: decomp_small.
  have [V1 [V2 [[sep [x0 [y0 [Hx0 Hy0]]]] SV12]]] := vseparator_separation sepS.
  have V1properG: #|induced V1| < #|G|.
  { rewrite card_sig. eapply card_ltnT. simpl. eauto. }
  have {x0 Hx0 y0 Hy0} V2properG: #|induced V2| < #|G|.
  { rewrite card_sig. eapply card_ltnT. simpl. eauto. }
  have C: clique (V1 :&: V2) by rewrite -SV12; exact: small_clique.
  case: (Hind (induced V1)) => // [|T1 [B1 [sd1 w1]]].
  { apply: induced_forest. exact: sub_forest forest_G. }
  case: (Hind (induced V2)) => // [|T2 [B2 [sd2 w2]]].
  { apply: induced_forest. exact: sub_forest forest_G. }  
  case separation_decomp with G V1 V2 T1 T2 B1 B2 => // T [B [sd w]].
  exists T. exists B. split => //. 
  apply leq_trans with (maxn (width B1) (width B2)) => //.
  by rewrite geq_max w1 w2. 
Qed.
