Require Import RelationClasses.

From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries sgraph.
Require Import set_tac.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 

(** * Tree Decompositions *)

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
  move => E [D1 D2 D3]. split => //.
  move => x y /= xy. apply: D2 => /=. by rewrite E.
Qed.

Definition triv_sdecomp (G : sgraph) :
  sdecomp tunit G (fun _ => [set: G]).
Proof.
  split => [x|e|x [] [] _ _]; try by exists tt; rewrite !inE.
  exact: connect0.
Qed.

Lemma sg_iso_decomp (G1 G2 : sgraph) (T : forest) B1 : 
  sdecomp T G1 B1 -> sg_iso G1 G2 -> 
  exists2 B2, sdecomp T G2 B2 & width B2 = width B1.
Proof.
  case => D1 D2 D3 [f g can_f can_g hom_f hom_g]. 
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

(** ** Renaming *)
Arguments sdecomp [T G] B.

Lemma rename_decomp (T : forest) (G H : sgraph) D (dec_D : sdecomp D) (h : G -> H) : 
  hom_s h -> 
  surjective h -> 
  (forall x y : H, x -- y -> exists x0 y0, [/\ h x0 = x, h y0 = y & x0 -- y0]) ->
  (forall x y, h x = h y -> 
    (exists t, (x \in D t) && (y \in D t)) \/ (exists t1 t2, [/\ t1 -- t2, x \in D t1 & y \in D t2])) ->
  @sdecomp T _ (rename D h).
Proof.
  move => hom_h sur_h sur_e comp_h. 
  split. 
  - move => x. pose x0 := cr sur_h x. case: (sbag_cover dec_D x0) => t Ht.
    exists t. apply/imsetP. exists x0; by rewrite ?crK. 
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
Proof. rewrite max_mono // => t. exact: leq_imset_card. Qed.

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
    sdecomp D1 -> sdecomp D2 -> sdecomp (decompU D1 D2).
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
        apply: (connect_img (e:= e) (f := inl)).
        * move => a b. rewrite /e /= !in_simpl -andbA => /and3P[? ? ?].  
          by rewrite !mem_imset.
        * apply: sbag_conn => //. 
          move: A. by case/imsetP => ? ? [->].
          move: B. by case/imsetP => ? ? [->].
      + pose e := restrict [pred t | x \in D2 t] sedge.
        apply: (connect_img (e:= e) (f := inr)).
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

(*
Section AddClique.
Variables (G : sgraph) (U : {set G}).
Implicit Types x y : G.

Definition add_clique_rel := relU sedge [rel x y in U | x != y].

Lemma add_clique_rel_irred : irreflexive add_clique_rel.
Admitted.

Lemma add_clique_rel_sym : symmetric add_clique_rel.
Admitted.

Definition add_clique := SGraph add_clique_rel_sym add_clique_rel_irred.

Lemma add_clique_lift x y (p : @Path G x y) : 
  exists q : @Path add_clique x y, nodes q = nodes p.
Admitted.

Lemma add_clique_unlift x y (p : @Path add_clique x y) : 
  #|[set x in U | x \in p]| <= 1 ->
  exists q : @Path G x y, nodes q = nodes p.
Admitted.

End AddClique.
*)
 



Local Notation PATH G x y := (@Path G x y).

Lemma mem_path' (G : sgraph) (x y : G) (p : Path x y) z :
  (z \in p) = (z \in nodes p).
Admitted.

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
      + by rewrite (@mem_path' G'') Ep -(@mem_path' G').
      + by rewrite (@mem_path' G'') Ep -(@mem_path' G').
      + apply/eqP. by rewrite -nodes_eqE Ep P1 !nodes_pcat Ep1 Ep2.
      + move => z. rewrite setUC. rewrite (@mem_path' G'') Ep1 -(@mem_path' G').
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
    rewrite (negbTE zNs2) [z == s1]eq_sym (sg_edgeNeq s1z) ?eqxx.
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
    - case/uPathP => r Ir. apply/eqP. rewrite -nodes_eqE. 
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
        - move/idx_inj. rewrite -mem_path'. by move/(_ T1)->. }
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
    sdecomp D -> @sdecomp tlink G (decompL D A).
  Proof.
    move => HA decD. split => //.
    - move => x. case: (sbag_cover decD x) => t Ht. by exists (Some t). 
    - move => x y xy. case: (sbag_edge decD xy) => t Ht. by exists (Some t).
    - have X x a : x \in D a -> x \in A ->
        connect (restrict [pred t | x \in decompL D A t] (add_node_rel U)) 
                (Some a) None.
      { move => H1 H2. move/(subsetP HA) : (H2) => /bigcupP [t Ht1 Ht2].
        apply: (connect_trans (y := Some t)).
        - move: (sbag_conn decD H1 Ht2). exact: connect_img.
        - apply: connect1 => /=; by rewrite !in_simpl H2 Ht1. }
      move => x [a|] [b|] /= H1 H2; last exact: connect0. 
      + move: (sbag_conn decD H1 H2). exact: connect_img. 
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

Section DecompTheory.
  Variables (G : sgraph) (T : forest) (B : T -> {set G}).
  Implicit Types (t u v : T) (x y z : G).

  Hypothesis decD : sdecomp B.

  Arguments sbag_conn [T G B] dec x t1 t2 : rename.


  (** This proof is based on a stackexchange post to be found here:
      https://math.stackexchange.com/questions/1227867/
      a-clique-in-a-tree-decomposition-is-contained-in-a-bag 

      The assumption [0 < #|S|] ensures that [T] is nonempty. *)
  Lemma decomp_clique (S : {set G}): 
    0 < #|S| -> clique S -> exists t : T, S \subset B t.
  Proof. 
    move: S. apply: (nat_size_ind (f := fun S : {set G} => #|S|)) => S IH inh_S clique_S.
    case: (leqP #|S| 2) => [card_S | card_S {inh_S}]. 
    - case: (card12 inh_S card_S) => [[x]|[x] [y] [Hxy]] ?; subst S.
      + case: (sbag_cover decD x) => t A. exists t. by rewrite sub1set.
      + have xy: x -- y. by apply: clique_S => //; rewrite !inE !eqxx ?orbT.
        case: (sbag_edge decD xy) => t A. exists t. by rewrite subUset !sub1set.
    - have [v [v0] [Hv Hv0 X]] := card_gt1P (ltnW card_S).
      pose S0 := S :\ v.
      pose T0 := [set t | S0 \subset B t]. 
      wlog /forall_inP HT0 : / [forall t in T0, v \notin B t].
      { case: (boolP [forall _ in _,_]) => [H|/forall_inPn [t H1 /negPn H2] _]; first by apply.
        exists t. rewrite inE in H1. by rewrite -(setD1K Hv) subUset sub1set H2 H1. }
      have HT0' t : v \in B t -> ~~ (S0 \subset B t).
      { apply: contraTN => C. apply: HT0. by rewrite inE. }
      have pairs x y : x \in S -> y \in S -> exists t, x \in B t /\ y \in B t.
      { move => xS yS. case: (IH [set x;y]). 
        - rewrite cardsU1 cards1 addn1. case (_ \notin _) => //=. exact: ltnW.
        - by rewrite cards2. 
        - apply: sub_in11W clique_S. apply/subsetP. by rewrite subUset !sub1set xS. 
        - move => t. rewrite subUset !sub1set => /andP [? ?]. by exists t. }
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
          - apply: sub_in11W clique_S. apply/subsetP. by rewrite subD1set. }
        have A : v0 \in B t. { apply (subsetP Ht). by rewrite !inE eq_sym X. }
        have/uPathRP [|p Ip _] := (sbag_conn decD v0 c t Hc2 A).
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
        have/uPathRP [//|q Iq /subsetP subC] := con_C _ _ Hc0 inC'.
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
      case/uPathRP:(sbag_conn decD u t0 cu Hu Hcu1) => [|q irr_p /subsetP has_u]. 
      { apply: contraTneq Hcu2 => <-.  exact: HT0. }
      suff Hq : c0 \in q. { move/has_u : Hq. by rewrite inE. }
      apply: t0P irr_p _. rewrite !inE /= HT0' //=. 
      move: (sbag_conn decD v c cu Hc1 Hcu2). 
      apply: connect_mono => t t' /=. 
      rewrite !inE -andbA => /and3P [*]. by rewrite !HT0'.
  Qed.
      
End DecompTheory.

(** K4 has with at least 4 *)
Lemma K4_bag (T : forest) (D : T -> {set K4}) : 
  sdecomp D -> exists t, 4 <= #|D t|.
Proof.
  move => decD.
  case: (@decomp_clique _ _ _ decD setT _ _) => //.
  - by rewrite cardsT card_ord.
  - move => t A. exists t. rewrite -[4](card_ord 4) -cardsT. 
    exact: subset_leq_card.
Qed.

Lemma K4_width (T : forest) (D : T -> {set K4}) : 
  sdecomp D -> 4 <= width D.
Proof. case/K4_bag => t Ht. apply: leq_trans Ht _. exact: leq_bigmax. Qed.

(** * Minors *)

(** H is a minor of G -- The order allows us to write [minor G] for the
collection of [G]s minors *)

Definition minor_map (G H : sgraph) (phi : G -> option H) := 
  [/\ (forall y : H, exists x : G, phi x = Some y),
     (forall y : H, connected (phi @^-1 Some y)) &
     (forall x y : H, x -- y -> exists x0 y0 : G,
      [/\ x0 \in phi @^-1 Some x, y0 \in phi @^-1 Some y & x0 -- y0])].

Definition minor_rmap (G H : sgraph) (phi : H -> {set G}) :=
  [/\ (forall x : H, phi x != set0),
     (forall x : H, connected (phi x)),
     (forall x y : H, x != y -> [disjoint phi x & phi y]) &
     (forall x y : H, x -- y -> neighbor (phi x) (phi y))].

Lemma minor_map_rmap (G H : sgraph) (phi : H -> {set G}) : 
  minor_rmap phi -> minor_map (fun x : G => [pick x0 : H | x \in phi x0]).
Proof.
  set phi' := (fun x => _).
  case => P1 P2 P3 P4. 
  have phiP x x0 : x0 \in phi x = (phi' x0 == Some x).
  { rewrite /phi'. case: pickP => [x' Hx'|]; last by move->. 
    rewrite Some_eqE. apply/idP/eqP => [|<-//]. 
    apply: contraTeq => /P3 D. by rewrite (disjointFr D Hx'). }
  split.
  - move => y. case/set0Pn : (P1 y) => y0. rewrite phiP => /eqP <-. by exists y0.
  - move => y x0 y0. rewrite !inE -!phiP => H1 H2. move: (P2 y _ _ H1 H2). 
    apply: connect_mono => u v. by rewrite /= -!mem_preim !phiP.
  - move => x y /P4/neighborP [x0] [y0] [*]. exists x0;exists y0. by rewrite -!mem_preim -!phiP.
Qed.

Lemma minor_rmap_map (G H : sgraph) (phi : G -> option H) : 
  minor_map phi -> minor_rmap (fun x => [set y | phi y == Some x]).
Proof.
  set phi' := fun _ => _.
  case => P1 P2 P3.
  split.
  - move => x. apply/set0Pn. case: (P1 x) => x0 H0. exists x0. by rewrite !inE H0.
  - move => x u v Hu Hv. move: (P2 x _ _ Hu Hv). 
    apply: connect_mono => a b. by rewrite /= !inE.
  - move => x y D. rewrite disjoint_exists. 
    apply: contraNN D => /exists_inP [x0]. by rewrite -Some_eqE !inE => /eqP<-/eqP<-.
  - move => x y /P3 [x0] [y0] [*]. apply/neighborP. exists x0;exists y0. by rewrite !inE !mem_preim. 
Qed.

Lemma rmap_add_edge_sym (G H : sgraph) (s1 s2 : G) (phi : H -> {set G}) :
  @minor_rmap (add_edge s1 s2) H phi -> @minor_rmap (add_edge s2 s1) H phi.
Proof.
  case => [P1 P2 P3 P4]; split => //.
  - move => x. exact/add_edge_connected_sym. 
  - move => x y /P4/neighborP => [[x'] [y'] [A B C]]. 
    apply/neighborP; exists x'; exists y'. by rewrite add_edgeC.
Qed.

Definition minor (G H : sgraph) : Prop := exists phi : G -> option H, minor_map phi.

Fact minor_of_map (G H : sgraph) (phi : G -> option H): 
  minor_map phi -> minor G H.
Proof. case => *. by exists phi. Qed.

Fact minor_of_rmap (G H : sgraph) (phi : H -> {set G}): 
  minor_rmap phi -> minor G H.
Proof. move/minor_map_rmap. exact: minor_of_map. Qed.

Lemma minorRE G H : minor G H -> exists phi : H -> {set G}, minor_rmap phi.
Proof. case => phi /minor_rmap_map D. eexists. exact: D. Qed.

Lemma minor_map_comp (G H K : sgraph) (f : G -> option H) (g : H -> option K) :
  minor_map f -> minor_map g -> minor_map (obind g \o f).
Proof.
  move=> [f1 f2 f3] [g1 g2 g3]; rewrite /funcomp; split.
  - move => y. case: (g1 y) => y'. case: (f1 y') => x E1 ?.
    exists x. by rewrite E1.
  - move => z x y. rewrite !inE. 
    case Ef : (f x) => [fx|] //= gfx. case Eg : (f y) => [fy|] //= gfy.
    move: (g2 z fx fy). rewrite !inE. case/(_ _ _)/Wrap => // /connectP => [[p]]. 
    elim: p x fx Ef gfx => /= [|a p IH] x fx Ef gfx.
    + move => _ ?. subst fy. 
      move: (f2 fx x y). rewrite !inE Ef Eg. case/(_ _ _)/Wrap => //. 
      apply: connect_mono => a b /=. rewrite !inE -andbA. 
      case/and3P => /eqP-> /eqP-> -> /=. by rewrite (eqP gfx) !eqxx.
    + rewrite !inE -!andbA => /and4P [H1 H2 H3 H4] H5. 
      case: (f1 a) => x' Hx'. apply: (connect_trans (y := x')); last exact: IH H5.
      move/f3 : (H3) => [x0] [y0] [X1 X2 X3]. 
      apply: (connect_trans (y := x0)); last apply: (connect_trans (y := y0)).
      * move: (f2 fx x x0). rewrite !inE ?Ef ?eqxx in X1 *. case/(_ _ _)/Wrap => //.
        apply: connect_mono => u v /=. rewrite !inE -andbA. 
        case/and3P => /eqP-> /eqP-> -> /=. by rewrite H1.
      * apply: connect1. rewrite /= !inE ?X3 ?andbT in X1 X2 *. 
        by rewrite (eqP X1) (eqP X2) /= (eqP gfx) eqxx.
      * move: (f2 a y0 x' X2). case/(_ _)/Wrap. by rewrite !inE Hx'.
        apply: connect_mono => u v /=. rewrite !inE -andbA. 
        case/and3P => /eqP-> /eqP-> -> /=. by rewrite H2.
  - move => x y /g3 [x'] [y'] [Hx' Hy'] /f3 [x0] [y0] [Hx0 Hy0 ?].
    exists x0. exists y0. rewrite !inE in Hx' Hy' Hx0 Hy0 *. 
    split => //; reflect_eq; by rewrite (Hx0,Hy0) /= (Hx',Hy'). 
Qed.

Lemma minor_trans : Transitive minor.
Proof.
  move => G H I [f mm_f] [g mm_g]. eexists.
  exact: minor_map_comp mm_f mm_g.
Qed.

Definition total_minor_map (G H : sgraph) (phi : G -> H) :=
  [/\ (forall y : H, exists x, phi x = y), 
     (forall y : H, connected (phi @^-1 y)) &
     (forall x y : H, x -- y -> 
     exists x0 y0, [/\ x0 \in phi @^-1 x, y0 \in phi @^-1 y & x0 -- y0])].

Definition strict_minor (G H : sgraph) : Prop := 
  exists phi : G -> H, total_minor_map phi.

Lemma map_of_total (G H : sgraph) (phi : G -> H) :
  total_minor_map phi -> minor_map (Some \o phi).
Proof. case => A B C. split => // y. case: (A y) => x <-. by exists x. Qed.

Lemma strict_is_minor (G H : sgraph) : strict_minor G H -> minor G H.
Proof. move => [phi A]. exists (Some \o phi). exact: map_of_total. Qed.

Lemma sub_minor (S G : sgraph) : subgraph S G -> minor G S.
Proof.
  move => [h inj_h hom_h].
  pose phi x := if @idP (x \in codom h) is ReflectT p then Some (iinv p) else None.
  exists phi; split.
  - move => y. exists (h y). rewrite /phi. 
    case: {-}_ / idP => [p|]; by rewrite ?iinv_f ?codom_f.
  - move => y x0 y0. rewrite !inE {1 2}/phi. 
    case: {-}_ / idP => // p /eqP[E1]. 
    case: {-}_ / idP => // q /eqP[E2]. 
    suff -> : (x0 = y0) by exact: connect0. 
    by rewrite -(f_iinv p) -(f_iinv q) E1 E2. 
  - move => x y A. move/hom_h : (A) => B.
    exists (h x). exists (h y). rewrite !inE /phi B. 
    + by do 2 case: {-}_ / idP => [?|]; rewrite ?codom_f ?iinv_f ?eqxx //.
    + apply: contraTneq A => /inj_h ->. by rewrite sgP.
Qed.

Lemma iso_strict_minor (G H : sgraph) : sg_iso G H -> strict_minor H G.
Proof.
  case=> g h ghK hgK gH hH.
  have in_preim_g x y : (y \in g @^-1 x) = (y == h x).
    rewrite -mem_preim; exact: can2_eq.
  exists g; split.
  + by move=> y; exists (h y); rewrite hgK.
  + move=> y x1 x2. rewrite !in_preim_g => /eqP-> /eqP->. exact: connect0.
  + move=> x y xy. exists (h x); exists (h y). rewrite !in_preim_g.
    split=> //. exact: hH.
Qed.

Lemma induced_minor (G : sgraph) (S : {set G}) : minor G (induced S).
Proof. apply: sub_minor. exact: induced_sub. Qed.

Definition edge_surjective (G1 G2 : sgraph) (h : G1 -> G2) :=
  forall x y : G2 , x -- y -> exists x0 y0, [/\ h x0 = x, h y0 = y & x0 -- y0].

(* The following should hold but does not fit the use case for minors *)
Lemma rename_sdecomp (T : forest) (G H : sgraph) D (dec_D : sdecomp D) (h :G -> H) : 
  hom_s h -> surjective h -> edge_surjective h -> 
  (forall x y, h x = h y -> exists t, (x \in D t) && (y \in D t)) -> 
  @sdecomp T _ (rename D h).
Abort. 



Lemma width_minor (G H : sgraph) (T : forest) (B : T -> {set G}) : 
  sdecomp B -> minor G H -> exists B', @sdecomp T H B' /\ width B' <= width B.
Proof.
  move => decT [phi [p1 p2 p3]].
  pose B' t := [set x : H | [exists (x0 | x0 \in B t), phi x0 == Some x]].
  exists B'. split.
  - split. 
    + move => y. case: (p1 y) => x /eqP Hx.
      case: (sbag_cover decT x) => t Ht.
      exists t. apply/pimsetP. by exists x.
    + move => x y xy. move/p3: xy => [x0] [y0]. rewrite !inE => [[H1 H2 H3]].
      case: (sbag_edge decT H3) => t /andP [T1 T2]. exists t. 
      apply/andP; split; apply/pimsetP; by [exists x0|exists y0].
    + have conn_pre1 t1 t2 x x0 :
        phi x0 == Some x -> x0 \in B t1 -> x0 \in B t2 ->
        connect (restrict [pred t | x \in B' t] sedge) t1 t2.
      { move => H1 H2 H3. move: (sbag_conn decT H2 H3).
        apply: connect_mono => u v /=. rewrite !in_simpl -!andbA => /and3P [? ? ?]. 
        apply/and3P; split => //; apply/pimsetP; eexists; eauto. }
      move => x t1 t2 /pimsetP [x0 X1 X2] /pimsetP [y0 Y1 Y2].
      move: (p2 x x0 y0). rewrite !inE. case/(_ _ _)/Wrap => // /connectP [p]. 
      elim: p t1 x0 X1 X2 => /= [|z0 p IH] t1 x0 X1 X2. 
      * move => _ E. subst x0. exact: conn_pre1 X1 Y1.
      * rewrite -!andbA => /and3P [H1 H2 /andP [H3 H4] H5].
        case: (sbag_edge decT H3) => t /andP [T1 T2].
        apply: (connect_trans (y := t)). 
        -- move => {p IH H4 H5 y0 Y1 Y2 X2}. rewrite !inE in H1 H2.
           exact: conn_pre1 X1 T1.
        -- apply: IH H4 H5 => //. by rewrite inE in H2.
  - apply: max_mono => t. exact: pimset_card.
Qed.

Lemma minor_of_clique (G : sgraph) (S : {set G}) n :
  n <= #|S| -> clique S -> minor G 'K_n.
Proof.
  case/card_gtnP => s [uniq_s /eqP size_s sub_s clique_S].
  pose t := Tuple size_s.
  pose phi (i : 'K_n) := [set tnth t i].
  suff H: minor_rmap phi by apply (minor_of_map (minor_map_rmap H)).
  split.
  - move => i. apply/set0Pn; exists (tnth t i). by rewrite !inE.
  - move => i. exact: connected1.
  - move => i j iNj. rewrite disjoints1. apply: contraNN iNj.
    by rewrite inE tnth_uniq.
  - move => i j /= ?. apply/neighborP. exists (tnth t i); exists (tnth t j). 
    rewrite !inE !tnth_uniq ?eqxx //. 
    rewrite clique_S // ?tnth_uniq // ?sub_s //; exact: mem_tnth.
Qed.

Lemma Kn_clique n : clique [set: 'K_n].
Proof. by []. Qed.  

Definition K4_free (G : sgraph) := ~ minor G K4.

Lemma minor_K4_free (G H : sgraph) : 
  minor G H -> K4_free G -> K4_free H.
Proof. move => M F C. apply: F. exact: minor_trans C. Qed.

Lemma subgraph_K4_free (G H : sgraph) : 
  subgraph H G -> K4_free G -> K4_free H.
Proof. move/sub_minor. exact: minor_K4_free. Qed.

Lemma iso_K4_free (G H : sgraph) : 
  sg_iso G H -> K4_free H -> K4_free G.
Proof. move => iso_GH. apply: subgraph_K4_free. exact: iso_subgraph. Qed.

Lemma TW2_K4_free (G : sgraph) (T : forest) (B : T -> {set G}) : 
  sdecomp B -> width B <= 3 -> K4_free G.
Proof.
  move => decT wT M. case: (width_minor decT M) => B' [B1 B2].
  suff: 4 <= 3 by []. 
  apply: leq_trans wT. apply: leq_trans B2. exact: K4_width.
Qed.

(* TODO: theory for [induced [set~ : None : add_node]] *)
Lemma minor_induced_add_node (G : sgraph) (N : {set G}) : @minor_map (induced [set~ None : add_node G N]) G val.
Proof.
  have inNoneD (a : G) : Some a \in [set~ None] by rewrite !inE. split.
  + move=> y. by exists (Sub (Some y) (inNoneD y)).
  + move=> y x1 x2. rewrite -!mem_preim =>/eqP<- /eqP/val_inj->. exact: connect0.
  + move=> x y xy. exists (Sub (Some x) (inNoneD x)).
    exists (Sub (Some y) (inNoneD y)). by split; rewrite -?mem_preim.
Qed.


Lemma add_node_minor (G G' : sgraph) (U : {set G}) (U' : {set G'}) (phi : G -> G') :
  (forall y, y \in U' -> exists2 x, x \in U & phi x = y) ->
  total_minor_map phi ->
  minor (add_node G U) (add_node G' U').
Proof.
  move => H [M1 M2 M3]. 
  apply: strict_is_minor. exists (omap phi). split.
  - case => [y|]; last by exists None. case: (M1 y) => x E. 
    exists (Some x). by rewrite /= E.
  - move => [y|]. 
    + rewrite preim_omap_Some. exact: connected_add_node. 
    + rewrite preim_omap_None. exact: connected1.
  - move => [x|] [y|] //=. 
    + move/M3 => [x0] [y0] [H1 H2 H3]. exists (Some x0); exists (Some y0).
      by rewrite !preim_omap_Some !mem_imset.
    + move/H => [x0] H1 H2. exists (Some x0); exists None. 
      rewrite !preim_omap_Some !preim_omap_None !inE !eqxx !mem_imset //.
      by rewrite -mem_preim H2.
    + move/H => [y0] H1 H2. exists None; exists (Some y0).
      rewrite !preim_omap_Some !preim_omap_None !inE !eqxx !mem_imset //.
      by rewrite -mem_preim H2.
Qed.

Lemma minor_with (H G': sgraph) (S : {set H}) (i : H) (N : {set G'})
  (phi : (sgraph.induced S) -> option G') : 
  i \notin S -> 
  (forall y, y \in N -> exists2 x , x \in phi @^-1 (Some y) & val x -- i) ->
  @minor_map (sgraph.induced S) G' phi -> 
  minor H (add_node G' N).
Proof.
  move => Hi Hphi mm_phi.
  pose psi (u:H) : option (add_node G' N) := 
    match @idP (u \in S) with 
    | ReflectT p => obind (fun x => Some (Some x)) (phi (Sub u p))
    | ReflectF _ => if u == i then Some None else None
    end.
  (* NOTE: use (* case: {-}_ / idP *) to analyze psi *)
  have psi_G' (a : G') : psi @^-1 (Some (Some a)) = val @: (phi @^-1 (Some a)).
  { apply/setP => x. rewrite !inE. apply/eqP/imsetP.
    + rewrite /psi. case: {-}_ / idP => p; last by case: ifP. 
      case E : (phi _) => [b|//] /= [<-]. exists (Sub x p) => //. by rewrite !inE E.
    + move => [[/= b Hb] Pb] ->. rewrite /psi. case: {-}_ / idP => //= Hb'. 
      rewrite !inE (bool_irrelevance Hb Hb') in Pb. by rewrite (eqP Pb). }
  have psi_None : psi @^-1 (Some None) = [set i].
  { apply/setP => z. rewrite !inE /psi. 
    case: {-}_ / idP => [p|_]; last by case: ifP.
    have Hz : z != i. { apply: contraNN Hi. by move/eqP <-. }
    case: (phi _) => [b|]; by rewrite (negbTE Hz). }
  case: mm_phi => M1 M2 M3. exists psi;split.
  - case. 
    + move => a. case: (M1 a) => x E. exists (val x). apply/eqP. 
      rewrite mem_preim psi_G' mem_imset //. by rewrite !inE E. 
    + exists i. rewrite /psi. move: Hi. 
      case: {-}_ / idP => [? ?|_ _]; by [contrab|rewrite eqxx].
  - case. 
    + move => y. move: (M2 y). rewrite psi_G'. exact: connected_in_subgraph.
    + rewrite psi_None. exact: connected1.
  - move => [a|] [b|]; last by rewrite sg_irrefl.
    + move => /= /M3 [x0] [y0] [? ? ?]. 
      exists (val x0). exists (val y0). by rewrite !psi_G' !mem_imset.
    + move => /= /Hphi [x0] ? ?. exists (val x0); exists i. by rewrite psi_None set11 !psi_G' !mem_imset.
    + move => /= /Hphi [x0] ? ?.  exists i;exists (val x0). by rewrite sg_sym psi_None set11 !psi_G' !mem_imset.
Qed.
