From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries sgraph minor multigraph skeleton.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 

Implicit Types (G H : graph) (U : sgraph) (T : forest).

(** * Terms to Treewidth Two *)

(** NOTE: Contrary to what is written in the paper, the this file does not use
tree decompositions for simple graphs but a separate notion of
tree-decomposition for labeled multigraphs. We plan to eliminate this redundancy
for the final version. This requires transferring the results on unions and
quotients of treedecompositions to simple graphs *)

(** Covering is not really required, but makes the renaming theorem
easier to state *)
Record decomp (T : forest) (G : graph) (B : T -> {set G}) := Decomp
  { bag_cover x : exists t, x \in B t; 
    bag_edge (e : edge G) : exists t, (source e \in B t) && (target e \in B t);
    bag_conn x t1 t2  : x \in B t1 -> x \in B t2 ->
      connect (restrict [pred t | x \in B t] sedge) t1 t2}.


Definition compatible (T : forest) (G : graph2) (B : T -> {set G}) := 
  exists t, (g_in \in B t) && (g_out \in B t).

(** ** Renaming *)

Lemma rename_decomp (T : forest) (G H : graph) D (dec_D : decomp D) (h : h_ty G H) : 
  surjective2 h -> hom_g h -> 
  (forall x y, h.1 x = h.1 y -> exists t, (x \in D t) && (y \in D t)) -> 
  @decomp T _ (rename D h.1).
Proof.
  move => [sur1 sur2] hom_h comp_h. 
  split.
  - move => x. pose x0 := cr sur1 x. case: (bag_cover dec_D x0) => t Ht.
    exists t. apply/imsetP. exists x0; by rewrite ?crK. 
  - move => e. pose e0 := cr sur2 e. case: (bag_edge dec_D e0) => t /andP [t1 t2].
    exists t. apply/andP;split. 
    + apply/imsetP. exists (source e0) => //. by rewrite hom_h crK.
    + apply/imsetP. exists (target e0) => //. by rewrite hom_h crK.
  - move => x t1 t2 bg1 bg2. 
    case/imsetP : (bg1) (bg2) => x0 A B /imsetP [x1 C E]. subst. rewrite E in bg2.
    case: (comp_h _ _ E) => t /andP [F I]. 
    apply: (connect_trans (y := t)). 
    + apply: connect_mono (bag_conn dec_D A F) => u v /= /andP [/andP [X Y] Z]. 
      rewrite Z andbT. apply/andP;split; by apply/imsetP;exists x0.
    + apply: connect_mono (bag_conn dec_D I C) => u v /= /andP [/andP [X Y] Z]. 
      rewrite E Z andbT. apply/andP;split; by apply/imsetP;exists x1.
Qed.

Lemma rename_width (T : forest) (G : graph) (D : T -> {set G}) (G' : finType) (h : G -> G') :
  width (rename D h) <= width D.
Proof. rewrite max_mono // => t. exact: leq_imset_card. Qed.


Lemma iso2_decomp (G1 G2 : graph2) (T : forest) B1 : 
  @decomp T G1 B1 -> compatible B1 -> G1 ≈ G2 -> 
  exists B2, [/\ @decomp T G2 B2, width B2 = width B1 & compatible B2].
Proof.
  move => decD compD [f hom_f bij_f].
  case: (bij_f) => /bij_inj inj_f ?. 
  exists (rename B1 f.1). split.
  - case: hom_f => [[hom_f fi] fo]. 
    apply: rename_decomp => //. 
    + split; apply: bij_surj;by case: bij_f.
    + move => x y /inj_f <-. case: decD => A  _ _. 
      case: (A x) => t Ht. exists t. by rewrite Ht.
  - rewrite /width. apply: eq_bigr => i _. by rewrite card_imset.
  - case: bij_f => [[/= g A B] _]. 
    case: compD => t /andP [t1 t2]. exists t.
    rewrite /rename. rewrite -[g_in]B -[g_out]B !mem_imset //. 
    + by rewrite -[g_out]hom_f A.
    + by rewrite -[g_in]hom_f A.
Qed.

(** ** Disjoint Union *)

(** TODO: The graph constructions below still use unpackaged paths. Using the
infrastructure for packaged paths should simplify the proofs *)

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
    move => [a|a] [b|b] _ _ p q [Ip _] [Iq _].
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

  Definition decompU G1 G2 (D1 : T1 -> {set G1}) (D2 : T2 -> {set G2}) : 
    tjoin -> {set union G1 G2} := 
    [fun a => match a with 
          | inl a => [set inl x | x in D1 a]
          | inr a => [set inr x | x in D2 a]
          end].

  Lemma join_decomp G1 G2 (D1 : T1 -> {set G1}) (D2 : T2 -> {set G2})  :
    decomp D1 -> decomp D2 -> decomp (decompU D1 D2).
  Proof.
    move => dec1 dec2. split.
    - move => [x|x]. 
      + case: (bag_cover dec1 x) => t Ht. exists (inl t) => /=. by rewrite mem_imset.
      + case: (bag_cover dec2 x) => t Ht. exists (inr t) => /=. by rewrite mem_imset.
    - move => [e|e]. 
      + case: (bag_edge dec1 e) => t /andP [H1 H2]. exists (inl t) => /=. by rewrite !mem_imset.
      + case: (bag_edge dec2 e) => t /andP [H1 H2]. exists (inr t) => /=. by rewrite !mem_imset.
    - have inl_inr x t : inl x \in decompU D1 D2 (inr t) = false.
      { rewrite /decompU /=. apply/negbTE/negP. by case/imsetP. }
      have inr_inl x t : inr x \in decompU D1 D2 (inl t) = false.
      { rewrite /decompU /=. apply/negbTE/negP. by case/imsetP. }
      move => [x|x] [t1|t1] [t2|t2] /=  ; rewrite ?inl_inr ?inr_inl // => A B. 
      + pose e := restrict [pred t | x \in D1 t] sedge.
        apply: (connect_img (e:= e) (f := inl)).
        * move => a b. rewrite /e /= !in_simpl -andbA => /and3P[? ? ?].  
          by rewrite !mem_imset.
        * apply: bag_conn => //. 
          move: A. by case/imsetP => ? ? [->].
          move: B. by case/imsetP => ? ? [->].
      + pose e := restrict [pred t | x \in D2 t] sedge.
        apply: (connect_img (e:= e) (f := inr)).
        * move => a b. rewrite /e /= !in_simpl -andbA => /and3P[? ? ?].  
          by rewrite !mem_imset.
        * apply: bag_conn => //. 
          move: A. by case/imsetP => ? ? [->].
          move: B. by case/imsetP => ? ? [->].
  Qed.

  Lemma join_width G1 G2 (D1 : T1 -> {set G1}) (D2 : T2 -> {set G2}) (t1 : T1) (t2 : T2) : 
    width (decompU D1 D2) <= maxn (width D1) (width D2).
  Proof. 
    pose p := mem (codom inl) : pred tjoin.
    rewrite /width. rewrite (bigID p) /= geq_max. apply/andP; split.
    - apply: leq_trans (leq_maxl _ _). apply: eq_leq.
      rewrite (reindex inl) /=. 
      + apply eq_big => x; first by rewrite /p /= codom_f.
        move => _. rewrite /decompU /= card_imset //. exact: inl_inj.
      + apply: bij_on_codom t1. exact: inl_inj.
    - apply: leq_trans (leq_maxr _ _). apply: eq_leq.
      rewrite (reindex inr) /=. 
      + apply eq_big => x; first by apply/negP => /mapP [?]. 
        move => _. rewrite /decompU /= card_imset //. exact: inr_inj.
      + exists (fun x => if x is inr y then y else t2) => //= [[x0|//]]. 
        by rewrite in_simpl /p /= codom_f.
  Qed.

End JoinT.

(** ** Link Construction *)

Section Link.
  Variables (T : forest) (U : {set T}).
  Hypothesis U_disc : {in U &,forall x y, x != y -> ~~ connect sedge x y}.
  
  Definition link := add_node T U.
  
  Lemma link_unique_lift (x y : link) : 
    unique (fun p : Path x y => irred p /\ None \notin p).
  Proof. 
    move: x y => [x|] [y|] p q [Ip Np] [Iq Nq]; 
      try by rewrite ?(@nodes_end link) ?(@nodes_start link) in Np Nq.
    gen have H,Hp : p Ip Np / {subset p <= codom Some}.
    { move => [u|]; by rewrite ?codom_f // (negbTE Np). }
    case: (lift_Path (p' := p)) => //; first exact: Some_inj.
    case: (lift_Path (p' := q)) => //; first exact: Some_inj. exact: H.
    move => p0 Ep Ip0 q0 Eq Iq0. 
    have E : p0 = q0. apply: forestP; by rewrite ?Ip0 ?Iq0.
    apply/eqP. rewrite -nodes_eqE. by apply/eqP;congruence.
  Qed.

  Lemma link_bypass (x y : T) (p : @Path link (Some x) (Some y)) : 
    x \in U -> y \in U -> None \notin p -> x = y.
  Proof. 
    move => xU yU Np. apply: contraTeq isT => /U_disc. 
    move/(_ xU yU). apply: contraNN => _.
    have Hp: {subset p <= codom Some}.
    { move => [u|]; by rewrite ?codom_f // (negbTE Np). }
    case: (lift_Path (p' := p)) => //; first exact: Some_inj.
    move => p' _ _. exact: Path_connect p'. 
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
  Proof. 
    move: x y p q => [x|] [y|] p q; 
      try by rewrite ?(@nodes_end link) ?(@nodes_start link).
    move => Ip Iq Np. apply: contraTT isT => Nq. 
    case/(isplitP Ip) def_p : _  / Np => [p1 p2 _ _ _]. subst.
    move: Ip. rewrite irred_cat' => /and3P[Ip1 Ip2 /eqP/setP I12].
    case: (splitL p2) => // [] [a|] [/= na] [p2'] [D _] //. 
    case: (splitL (prev p1)) => // [] [b|] [/= nb] [p1'] [D' _] //. 
    have ? : b = a.
    { suff [p Hp] : exists p : @Path link (Some b) (Some a), None \notin p.
      { exact: link_bypass Hp. }
      exists (pcat p1' (pcat q (prev p2'))). 
      rewrite !(@mem_pcat link) mem_prev (negbTE Nq) /= negb_or. 
      move: Ip1 Ip2. rewrite -irred_rev D' D !irred_edgeL. by do 2 case: (_ \notin _). }    
    subst. move: (I12 (Some a)). 
    rewrite !inE !mem_pcat mem_edgep -mem_prev D' !eqxx /=.
    by rewrite (@mem_pcat link) nodes_start orbT => /esym. 
  Qed.

  Lemma link_is_forest : is_forest [set: link].
  Proof.
    apply: unique_forestT => x y p q Ip Iq. 
    case: (boolP (None \in p)) => Np.
    - have Nq := link_has_None Ip Iq Np.
      case/(isplitP Ip) def_p : _ / Np => [p1 p2 Ip1 Ip2 _].
      case/(isplitP Iq) def_q : _ / Nq => [q1 q2 Iq1 Iq2 _].
      congr pcat. 
      + apply: srev_inj. apply: link_unique_None; by rewrite irred_rev.
      + exact: link_unique_None.
    - suff Nq : None \notin q by apply: link_unique_lift. 
      apply: contraNN Np. exact: link_has_None.
  Qed.
      
  Definition tlink := @Forest link link_is_forest.

  Definition decompL G (D : T -> {set G}) A a := 
    match a with Some x => D x | None => A end.

  Lemma decomp_link (G : graph) (D : T -> {set G}) (A  : {set G}) : 
    A \subset \bigcup_(t in U) D t ->
    decomp D -> @decomp tlink G (decompL D A).
  Proof.
    move => HA decD. split => //.
    - move => x. case: (bag_cover decD x) => t Ht. by exists (Some t). 
    - move => e. case: (bag_edge decD e) => t Ht. by exists (Some t).
    - have X x a : x \in D a -> x \in A ->
        connect (restrict [pred t | x \in decompL D A t] (add_node_rel U)) 
                (Some a) None.
      { move => H1 H2. move/(subsetP HA) : (H2) => /bigcupP [t Ht1 Ht2].
        apply: (connect_trans (y := Some t)).
        - move: (bag_conn decD H1 Ht2). exact: connect_img.
        - apply: connect1 => /=; by rewrite !in_simpl H2 Ht1. }
      move => x [a|] [b|] /= H1 H2; last exact: connect0. 
      + move: (bag_conn decD H1 H2). exact: connect_img. 
      + exact: X.
      + rewrite (@srestrict_sym link). exact: X. 
  Qed.

  Lemma width_link (G : graph) (D : T -> {set G}) (A  : {set G}) : 
    width (decompL D A) <= maxn (width D) #|A|.
  Proof.
    apply/bigmax_leqP => [] [t|] _ /=; last by rewrite ?leq_maxr. 
    apply: leq_trans (leq_maxl _ _). exact: leq_bigmax.
  Qed.

End Link.


(** * Subalgebra of Tree-Width 2 Graphs *)

(** ** Closure Properties for operations *)

Arguments decomp T G B : clear implicits.

Section Quotients. 
  Variables (G1 G2 : graph2).
  
  Let P : {set union G1 G2} := [set inl g_in; inl g_out; inr g_in; inr g_out].

  Definition admissible (eqv : rel (union G1 G2)) := 
    forall x y, eqv x y -> x = y \/ [set x;y] \subset P. 
 
  Lemma decomp_quot (T1 T2 : forest) D1 D2 (e : equiv_rel (union G1 G2)): 
    decomp T1 G1 D1 -> decomp T2 G2 D2 -> 
    compatible D1 -> compatible D2 ->
    width D1 <= 3 -> width D2 <= 3 ->
    admissible e -> #|(hom_of e).1 @: P| <= 3 ->
    exists T D, [/\ decomp T (merge (union G1 G2) e) D, 
              width D <= 3 & exists t, 
              D t = (hom_of e).1 @: P].
  Proof.
    move => dec1 dec2 [t1 /andP [comp1_in comp1_out]] [t2 /andP [comp2_in comp2_out]] W1 W2.
    move => adm_e collapse_P.
    pose T := tjoin T1 T2.
    pose D := decompU D1 D2.
    have dec_D : decomp T (union G1 G2) D by exact: join_decomp. 
    have dis_t1_t2 : ~~ connect (@sedge T)(inl t1) (inr t2) by rewrite join_disc.
    have dis_T12 : {in [set inl t1;inr t2] &, forall x y, x != y -> ~~ connect (@sedge T) x y}.
    { move => [?|?] [?|?] /setUP[] /set1P-> /setUP[]/set1P ->. 
      all: by rewrite ?eqxx // => _; rewrite sconnect_sym. }
    pose T' := @tlink T _ dis_T12.
    pose D' := decompL D P.
    have dec_D' : decomp T' (union G1 G2) D'.
    { apply: decomp_link => //. apply/subsetP => x.
      rewrite !inE -!orbA => /or4P [] /eqP->.
      all: apply/bigcupP; solve 
        [ by exists (inl t1) => //; rewrite ?inE ?mem_imset ?eqxx 
        | by exists (inr t2) => //; rewrite ?inE ?mem_imset ?eqxx]. }
    pose h := @hom_of (union G1 G2) e : h_ty _ (merge (union G1 G2) e).
    exists T'. exists (rename D' h.1); split; last by exists None.
    - apply: rename_decomp => //; first exact: hom_of_surj.
      move => x y. move/eqmodP => /=. case/adm_e => [<-|A].
      + case: (bag_cover dec_D' x) => t Ht. exists t. by rewrite Ht.
      + exists None. rewrite /= -!sub1set -subUset. done.
    - rewrite /width (bigID (pred1 None)).
      rewrite big_pred1_eq. rewrite geq_max. apply/andP;split => //.
      + rewrite (reindex Some) /=.
        * apply: (@leq_trans (maxn (width D1) (width D2))); last by rewrite geq_max W1 W2.
          apply: leq_trans (join_width _ _ t1 t2). 
          apply: max_mono => t. exact: leq_imset_card.
        * apply: subon_bij; last by apply bij_on_codom; [exact: Some_inj|exact: (inl t1)]. 
          by move => [x|]; rewrite !in_simpl // codom_f. 
  Qed.

  Definition par2_eqv : rel (union G1 G2) :=
    fun x y => (x == y) ||
      if (g_in != g_out :> G1) && (g_in != g_out :> G2)
      then [set x; y] \in [set [set inl g_in; inr g_in]; [set inl g_out; inr g_out]]
      else [set x; y] \subset [set inl g_in; inl g_out; inr g_in; inr g_out].

  Definition par2_eqv_refl : reflexive par2_eqv.
  Proof. by move=> ?; rewrite /par2_eqv eqxx. Qed.

  Lemma par2_eqv_sym : symmetric par2_eqv.
  Proof. move=> x y. by rewrite /par2_eqv [[set y; x]]setUC [y == x]eq_sym. Qed.

  Definition par2_eqv_trans : transitive par2_eqv.
  Proof.
    move=> y x z. rewrite /par2_eqv.
    case/altP: (x =P y) => [<-//|xNy/=]. case/altP: (y =P z) => [<-->//|yNz/=].
    case/boolP: ((g_in != g_out :> G1) && (g_in != g_out :> G2)).
    - rewrite !inE -(implyNb (x == z)).
      case/andP=> /negbTE iNo1 /negbTE iNo2 Hxy Hyz. apply/implyP=> xNz.
      move: Hxy xNy. rewrite 2!eqEcard 2!subUset 4!sub1set !inE.
      case/orP => /andP[]/andP[] /orP[]/eqP ? /orP[]/eqP ? _; subst=> // _.
      all: move: Hyz xNz yNz; rewrite 2!eqEcard 2!subUset 4!sub1set !inE.
      all: rewrite ?eqxx ?sum_eqE ?[g_out == g_in]eq_sym ?iNo1 ?iNo2 ?orbT ?orbF /=.
      all: case/andP => /orP[]/eqP-> _; by rewrite !eqxx.
    - rewrite -implyNb => _ Hxy Hyz. apply/implyP=> xNz.
      rewrite subUset !sub1set. apply/andP; split.
      + apply: (subsetP Hxy). by rewrite !inE eqxx.
      + apply: (subsetP Hyz). by rewrite !inE eqxx.
  Qed.

  Canonical par2_eqv_equivalence :=
    EquivRel par2_eqv par2_eqv_refl par2_eqv_sym par2_eqv_trans.

  Lemma par2_eqv_io :
    (par2_eqv (inl g_in) (inr g_in)) * (par2_eqv (inl g_out) (inr g_out)).
  Proof.
    rewrite /par2_eqv/=. case: ifP => _.
    - by rewrite !inE !eqxx.
    - by rewrite !subUset !sub1set !inE !eqxx.
  Qed.

  Definition par2_eq (x y : union G1 G2) :=
    match x,y with
    | inl x, inr y => (x == g_in) && (y == g_in) || (x == g_out) && (y == g_out)
    | _,_ => false
    end.

  Lemma par2_equiv_of : par2_eqv =2 equiv_of par2_eq.
  Proof.
    move=> x y. apply/idP/idP.
    - rewrite /par2_eqv. case/altP: (x =P y) => [<- _|xNy]/=; first exact: connect0.
      case: ifP => [_|/negbT].
      + rewrite !inE 2!eqEcard 2!subUset 4!sub1set !inE => H.
        case/orP: H xNy => /andP[]/andP[]/orP[]/eqP->/orP[]/eqP-> _.
        all: rewrite ?eqxx // ?[equiv_of _ (inr _) _]equiv_of_sym => _.
        all: apply: sub_equiv_of; by rewrite /par2_eq 2!eqxx.
      + rewrite negb_and 2!negbK. case/orP=> [/eqP Eio1|/eqP Eio2].
        * rewrite -Eio1 setUid => Exy.
          have Rio2 : equiv_of par2_eq (inr g_out) (inr g_in).
          { apply: (@equiv_of_trans _ _ (inl g_in)); first rewrite equiv_of_sym Eio1;
            by apply: sub_equiv_of; rewrite /par2_eq !eqxx. }
          move: Exy xNy; rewrite subUset 2!sub1set !inE -2!orbA.
          case/andP=> /or3P[]/eqP-> /or3P[]/eqP->.
          all: rewrite ?eqxx // ?[equiv_of _ _ (inl _)]equiv_of_sym => _.
          all: try solve [apply: (@sub_equiv_of _ _ (inl _));
                          by rewrite /par2_eq -?Eio1 !eqxx].
          by rewrite equiv_of_sym.
        * rewrite -setUA -Eio2 setUid => Exy.
          have Rio2 : equiv_of par2_eq (inl g_out) (inl g_in).
          { apply: (@equiv_of_trans _ _ (inr g_out)); last rewrite equiv_of_sym -Eio2;
            by apply: sub_equiv_of; rewrite /par2_eq !eqxx. }
          move: Exy xNy; rewrite subUset 2!sub1set !inE -2!orbA.
          case/andP=> /or3P[]/eqP-> /or3P[]/eqP->.
          all: rewrite ?eqxx // ?[equiv_of _ (inr _) _]equiv_of_sym => _.
          all: try solve [apply: (@sub_equiv_of _ _ (inl _));
                          by rewrite /par2_eq -?Eio2 !eqxx].
          by rewrite equiv_of_sym.
    - case/connectP=> p. elim: p x; first by [move=> x _ ->; exact: par2_eqv_refl].
      move=> /= a p IH x /andP[x_a p_path p_last].
      have {p_path p_last} : par2_eqv a y by exact: IH. apply: par2_eqv_trans.
      move: x a x_a => [x|x] [a|a] //=; first rewrite orbF.
      all: case/orP=> /andP[/eqP-> /eqP->].
      all: by rewrite ?par2_eqv_io // par2_eqv_sym par2_eqv_io.
  Qed.

  Lemma par2_eqv_ii x y : 
    x = g_in :> G1 -> y = g_in :> G2 ->
    par2_eqv (inl x) (inr y).
  Proof.
    move => -> ->. rewrite par2_equiv_of. apply: sub_equiv_of.
      by rewrite /par2_eq !eqxx. 
  Qed.
  
  Lemma par2_eqv_oo x y : 
    x = g_out :> G1 -> y = g_out :> G2 ->
    par2_eqv (inl x) (inr y).
  Proof.
    move => -> ->. rewrite par2_equiv_of. apply: sub_equiv_of.
      by rewrite /par2_eq !eqxx. 
  Qed.

  Definition par2 := 
    {| graph_of := merge (union G1 G2) par2_eqv ;
       g_in := \pi_{eq_quot par2_eqv} (inl g_in);
       g_out := \pi_{eq_quot par2_eqv} (inl g_out) |}.

  Lemma par2_eqvP : admissible par2_eqv.
  Proof. 
    move=> x y. case/orP=> [/eqP|]; first by left. case: ifP; last by right.
    rewrite !inE => _ /orP[]/eqP->; by right; rewrite subUset !sub1set !inE !eqxx.
  Qed.

  Lemma decomp_par2 (T1 T2 : forest) D1 D2 : 
    decomp T1 G1 D1 -> decomp T2 G2 D2 -> 
    compatible D1 -> compatible D2 ->
    width D1 <= 3 -> width D2 <= 3 ->
    exists T D, [/\ decomp T (par2) D, compatible D & width D <= 3].
  Proof.
    move => dec1 dec2 comp1 comp2 W1 W2.
    case: (decomp_quot (e:= [equiv_rel of par2_eqv]) dec1 dec2 comp1 comp2 W1 W2 _ _).
    - exact: par2_eqvP.
    - pose P' : {set union G1 G2} := [set inl g_in; inl g_out].
      apply: (@leq_trans #|P'|); last by rewrite cards2; by case (_ != _).
      apply: (@leq_trans #|[set (\pi x : par2) | x in P']|); last exact: leq_imset_card.
      apply: subset_leq_card.
      apply/subsetP => ? /imsetP [x H1 ->]. case/setUP : H1 => H1; first case/setUP : H1 => H1.
      * by rewrite mem_imset.
      * move/set1P : H1 => ->. apply/imsetP. exists (inl g_in); first by rewrite !inE eqxx ?orbT.
        apply/eqmodP. by rewrite equiv_sym /= par2_eqv_io.
      * move/set1P : H1 => ->. apply/imsetP. exists (inl g_out); first by rewrite !inE eqxx ?orbT.
        apply/eqmodP. by rewrite equiv_sym /= par2_eqv_io.
    - move => T [D] [A B [t C]]. exists T. exists D. split => //. exists t. 
      by rewrite C !mem_imset // !inE ?eqxx ?orbT.
  Qed.

  Definition seq2_eqv : rel (union G1 G2) :=
    fun x y => (x == y) || ([set x; y] == [set inl g_out; inr g_in]).

  Definition seq2_eqv_refl : reflexive seq2_eqv.
  Proof. by move=> ?; rewrite /seq2_eqv eqxx. Qed.

  Lemma seq2_eqv_sym : symmetric seq2_eqv.
  Proof. move=> x y. by rewrite /seq2_eqv [[set y; x]]setUC [y == x]eq_sym. Qed.

  Definition seq2_eqv_trans : transitive seq2_eqv.
  Proof.
    move=> y x z. rewrite /seq2_eqv.
    case/altP: (x =P y) => [<-//|/= xNy Exy].
    case/altP: (y =P z) => [<-|/= yNz Eyz]; first by rewrite Exy.
    case/altP: (x =P z) => //= xNz.
    have := eq_refl #|[set inl (@g_out G1); inr (@g_in G2)]|.
    rewrite -{1}(setUid [set _; _]) -{1}(eqP Exy) -{1}(eqP Eyz).
    rewrite set2C -setUUr (cardsU1 y) !cards2 !inE.
    by rewrite (eq_sym y x) negb_or xNy yNz xNz.
  Qed.

  Canonical seq2_eqv_equivalence :=
    EquivRel seq2_eqv seq2_eqv_refl seq2_eqv_sym seq2_eqv_trans.

  Lemma seq2_eqv_io : seq2_eqv (inl g_out) (inr g_in).
  Proof. by rewrite /seq2_eqv/=. Qed.

  Definition seq2_eq : rel (union G1 G2) :=
    [rel a b | (a == inl g_out) && (b == inr g_in)].

  Lemma seq2_equiv_of : seq2_eqv =2 equiv_of seq2_eq.
  Proof.
    move=> x y. apply/idP/idP.
    - case/altP: (x =P y) => [<- _|xNy]; first exact: connect0.
      rewrite /seq2_eqv (negbTE xNy) /= eqEcard subUset !sub1set !inE => /andP[H _].
      case/andP: H xNy => /orP[]/eqP-> /orP[]/eqP->; rewrite ?eqxx // => _.
      + apply: sub_equiv_of. by rewrite /seq2_eq/= !eqxx.
      + rewrite equiv_of_sym. apply: sub_equiv_of. by rewrite /seq2_eq/= !eqxx.
    - case/connectP=> p. elim: p x; first by [move=> x _ ->; exact: seq2_eqv_refl].
      move=> /= a p IH x /andP[x_a p_path p_last].
      have {p_path p_last} : seq2_eqv a y by exact: IH. apply: seq2_eqv_trans.
      case/orP: x_a => /andP[/eqP-> /eqP->];
      last rewrite seq2_eqv_sym; exact: seq2_eqv_io.
  Qed.

  Definition seq2 :=
    {| graph_of := merge (union G1 G2) seq2_eqv ;
       g_in := \pi_{eq_quot seq2_eqv} (inl g_in);
       g_out := \pi_{eq_quot seq2_eqv} (inr g_out) |}.

  Lemma seq2_eqvP : admissible seq2_eqv.
  Proof. 
    move=> x y. case/orP => /eqP->; [by left | right].
    by rewrite subUset !sub1set !inE !eqxx.
  Qed.

  Lemma decomp_seq2 (T1 T2 : forest) D1 D2 : 
    decomp T1 G1 D1 -> decomp T2 G2 D2 -> 
    compatible D1 -> compatible D2 ->
    width D1 <= 3 -> width D2 <= 3 ->
    exists T D, [/\ decomp T seq2 D, compatible D & width D <= 3].
  Proof.
    move => dec1 dec2 comp1 comp2 W1 W2.
    case: (decomp_quot (e:= [equiv_rel of seq2_eqv]) dec1 dec2 comp1 comp2 W1 W2 _ _).
    - exact: seq2_eqvP.
    - pose P' : {set union G1 G2} := [set inl g_in; inl g_out; inr g_out].
      apply: (@leq_trans #|P'|); last apply cards3.
      apply: (@leq_trans #|[set (\pi x : seq2) | x in P']|); last exact: leq_imset_card.
      apply: subset_leq_card.
      apply/subsetP => ? /imsetP [x H1 ->]. move: H1. 
      rewrite /P -!setUA [[set _;_]]setUC !setUA. case/setUP => H1.
      * by rewrite mem_imset.
      * case/set1P : H1 => ->. apply/imsetP. exists (inl g_out); first by rewrite !inE eqxx ?orbT.
        apply/eqmodP. by rewrite equiv_sym /= seq2_eqv_io.
    - move => T [D] [A B [t C]]. exists T. exists D. split => //. exists t. 
      by rewrite C !mem_imset // !inE ?eqxx ?orbT.
  Qed.

End Quotients.

Definition cnv2 (G : graph2) :=
  {| graph_of := G; g_in := g_out; g_out := g_in |}.

Lemma decomp_cnv (G : graph2) T D : 
  decomp T G D -> decomp T (cnv2 G) D.
Proof. done. Qed.

Lemma compat_cnv (G : graph2) T (D : T -> {set G}) : 
  compatible D -> compatible (G := cnv2 G) D.
Proof. move => [t] H. exists t => /=. by rewrite andbC. Qed.

Definition dom2 (G : graph2) := 
  {| graph_of := G; g_in := g_in; g_out := g_in |}.

Lemma decomp_dom (G : graph2) T D : 
  decomp T G D -> decomp T (dom2 G) D.
Proof. done. Qed.

Lemma compat_dom (G : graph2) T (D : T -> {set G}) : 
  compatible D -> compatible (G := dom2 G) D.
Proof. 
  move => [t] /andP [H _]. exists t => /=. by rewrite !H. 
Qed.

Definition triv_decomp (G : graph) :
  decomp tunit G (fun _ => [set: G]).
Proof. 
  split => [x|e|x [] [] _ _]; try by exists tt; rewrite !inE.
  exact: connect0.
Qed.

Notation vfun := (fun x : void => match x with end).  
Definition unit_graph := @Graph [finType of unit] _ vfun vfun vfun.

Definition one2 := {| graph_of := unit_graph; g_in := tt; g_out := tt |}.

Definition two_graph := @Graph [finType of bool] _ vfun vfun vfun.

Definition top2 := {| graph_of := two_graph; g_in := false; g_out := true |}.

Definition edge_graph (a : sym) := 
  Graph (fun _ : unit => false) (fun _ => true) (fun _ => a).                           

Definition sym2 a := {| graph_of := edge_graph a; g_in := false; g_out := true |}.

Lemma decomp_small (G : graph2) : #|G| <= 3 -> 
  exists T D, [/\ decomp T G D, compatible D & width D <= 3].
Proof. 
  exists tunit; exists (fun => setT). split.
  - exact: triv_decomp.
  - exists tt. by rewrite !inE.
  - by rewrite /width (big_pred1 tt _) // cardsT. 
Qed.

(** ** Terms and tree-width 2 property *)

Inductive term := 
| tmA of sym
| tm1 
| tmT 
| tmC of term
| tmS of term & term
| tmI of term & term
| tmD of term
.

Fixpoint graph_of_term (u:term) {struct u} : graph2 := 
  match u with
  | tmA a => sym2 a
  | tm1 => one2
  | tmT => top2
  | tmC u => cnv2 (graph_of_term u)
  | tmS u v => seq2 (graph_of_term u) (graph_of_term v)
  | tmI u v => par2 (graph_of_term u) (graph_of_term v)
  | tmD u => dom2 (graph_of_term u)
  end.

Theorem graph_of_TW2' (u : term) : 
  exists T D, [/\ decomp T (graph_of_term u) D, compatible D & width D <= 3].
Proof.
  elim: u => [a| | | u IHu | u IHu v IHv | u IHu v IHv | u IHu ].
  - apply: decomp_small. by rewrite card_bool.
  - apply: decomp_small. by rewrite card_unit.
  - apply: decomp_small. by rewrite card_bool.
  - move: IHu => [T] [D] [D1 D2 D3]. exists T. exists D. split => //. 
    exact: compat_cnv. (* FIXME: Hidden argument *)
  - move: IHu IHv => [T1] [D1] [? ? ?] [T2] [D2] [? ? ?].
    simpl graph_of_term. exact: (decomp_seq2 (D1 := D1) (D2 := D2)).
  - move: IHu IHv => [T1] [D1] [? ? ?] [T2] [D2] [? ? ?].
    simpl graph_of_term. exact: (decomp_par2 (D1 := D1) (D2 := D2)).
  - move: IHu => [T] [D] [D1 D2 D3]. exists T. exists D. split => //. 
    exact: compat_dom. (* FIXME: Hidden argument *)
Qed.


(** Transfer multigraph tree decomposition to the skeleton *)

Lemma decomp_skeleton (G : graph) (T : forest) (D : T -> {set G}) :
  decomp T G D -> sdecomp T (skeleton G) D.
Proof.
  case => D1 D2 D3. split => //. apply skelP => // x y.
  move => [t] A. exists t. by rewrite andbC.
Qed.

Lemma decomp_sskeleton (G : graph2) (T : forest) (D : T -> {set G}) :
  decomp T G D -> compatible D -> sdecomp T (sskeleton G) D.
Proof.
  case => D1 D2 D3 C. split => //. apply sskelP  => // x y.
  move => [t] A. exists t. by rewrite andbC.
Qed.

(** obtain that the term graphs are K4-free *)

(** NOTE: For the moment, we use separate definition of multigraph tree
decomposition for the induction on terms. We plan to eliminate
this redundancy and use tree decompositions of the skeletons instead *)

Theorem graph_of_TW2 (u : term) : 
  exists T D, [/\ sdecomp T (sskeleton (graph_of_term u)) D & width D <= 3].
Proof.
  case: (graph_of_TW2' u) => T [B] [B1 B2 B3].
  exists T. exists B. split => //. exact: decomp_sskeleton. 
Qed.

Lemma sskel_K4_free (u : term) : K4_free (sskeleton (graph_of_term u)).
Proof.
  case: (graph_of_TW2 u) => T [B] [B1 B2]. 
  exact: TW2_K4_free B1 B2.
Qed.

Lemma skel_K4_free (u : term) : K4_free (skeleton (graph_of_term u)).
Proof.
  apply: minor_K4_free (@sskel_K4_free u).
  exact: sub_minor (skel_sub _).
Qed.
