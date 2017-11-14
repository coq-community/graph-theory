From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries sgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 

(** * Tree Width and Minors *)

(** ** Tree Decompositions *)

(** Covering is not really required, but makes the renaming theorem
easier to state *)

Record sdecomp (T:tree) (G : sgraph) (bag : T -> {set G}) := SDecomp
  { sbag_cover x : exists t, x \in bag t; 
    sbag_edge x y : x -- y -> exists t, (x \in bag t) && (y \in bag t);
    sbag_conn x t1 t2  : x \in bag t1 -> x \in bag t2 ->
      connect (restrict [pred t | x \in bag t] sedge) t1 t2}.

Arguments sdecomp T G bag : clear implicits.

Section DecompTheory.
  Variables (G : sgraph) (T : tree) (B : T -> {set G}).
  Implicit Types (t u v : T) (x y z : G).

  Hypothesis decD : sdecomp T G B.

  (* This lemma is not acutally used below *)
  Lemma sbag_mid t u v p : upath u v p -> t \in p -> B u :&: B v \subset B t.
  Proof.
    move => upth_p in_p. apply/subsetP => z /setIP [z_in_u z_in_v].
    case/upathPR : (sbag_conn decD z_in_u z_in_v) => q upth_q.
    have ? : q = p. { apply: treeP upth_p. exact: restrict_upath upth_q. }
    subst q. move/upathWW/path_restrict : upth_q. by apply.
  Qed.
    
  Arguments sbag_conn [T G B] dec x t1 t2 : rename.

  Lemma subtree_link (C : {set T}) t0 c0 c p : 
    subtree C -> t0 \notin C -> c0 \in C -> t0 -- c0 -> c \in C -> upath t0 c p -> c0 \in p.
  Proof.
    move => sub_C H1 H2 H3 H4 H5. 
    have [q Hq] : exists p, upath  c0 c p. 
    { apply/upathP. apply: (connect_trans (y := t0)). 
      + apply: connect1. by rewrite sgP.
      + apply/upathP. by exists p. }
    have X : upath  t0 c (c0::q). 
    { rewrite upath_cons H3 Hq /= andbT inE. 
      apply/orP => [[/eqP X|X]]. by subst; contrab. 
      move/sub_C : Hq. case/(_ _ _)/Wrap => // /(_ _ X) ?. by contrab. }
    rewrite (treeP H5 X). exact: mem_head.
  Qed.

  Lemma decomp_clique (S : {set G}) : 
    0 < #|S| -> clique S -> exists t : T, S \subset B t.
  Proof. 
    move: S. 
    apply: (nat_size_ind (f := fun S : {set G} => #|S|)) => S IH inh_S clique_S.
    case: (leqP #|S| 2) => card_S. 
    - case: (card12 inh_S card_S) => [[x]|[x] [y] [Hxy]] ?; subst S.
      + case: (sbag_cover decD x) => t A. exists t. by rewrite sub1set.
      + have xy: x -- y. by apply: clique_S => //; rewrite !inE !eqxx ?orbT.
        case: (sbag_edge decD xy) => t A. exists t. by rewrite subUset !sub1set.
    - have [v [v0] [[Hv Hv0 X]]] := card_gt1P (ltnW card_S).
      pose S0 := S :\ v.
      pose T0 := [set t | S0 \subset B t]. 
      (* Wlog. no bag from [T0] contains [v] *)
      case: (boolP [forall t in T0, v \notin B t]); last first. (* TODO: wlog? *)
      { rewrite negb_forall_in. case/exists_inP => t. rewrite inE negbK => H1 H2.
        exists t. by rewrite -(setD1K Hv) subUset sub1set H2 H1. }
      move/forall_inP => HT0.
      have HT0' t : v \in B t -> ~~ (S0 \subset B t).
      { apply: contraTN => C. apply: HT0. by rewrite inE. }
      have pairs x y : x \in S -> y \in S -> exists t, x \in B t /\ y \in B t.
      { move => xS yS.  case: (IH [set x;y]). 
        - rewrite cardsU1 cards1 addn1. case (_ \notin _) => //=. exact: ltnW.
        - by rewrite cards2. 
        - apply: sub_in11W clique_S. apply/subsetP. by rewrite subUset !sub1set xS. 
        - move => t. rewrite subUset !sub1set => /andP [? ?]. by exists t. }
      (* obtain some node [c] whose bag contains [[set v,v0]] and
      consider its subtree outside of T0 *)
      have [c [Hc1 Hc2]] : exists t, v \in B t /\ v0 \in B t by apply: pairs. 
      pose C := [set t | connect (restrict [predC T0] sedge) c t].
      have inC: c \in C by rewrite inE connect0. 
      have C_subtree : subtree C by apply: subtree_connect.
      have disC: [disjoint C & T0]. 
      { rewrite disjoints_subset. apply/subsetP => c0. rewrite 2!inE.
        case: (boolP (c == c0)) => [/eqP<- _|H].
        - apply/negPn. move/HT0. by rewrite Hc1.
        - case/(uPathRP H) => p _ /subsetP. apply. exact: nodes_end. }
      (* Let [t0 -- c0] be the link connecting [T0] to [C] *)
      have [t0 [c0 [Ht0 Hc0 tc0]]] : exists t0 c0, [/\ t0 \in T0, c0 \in C & t0 -- c0].
      { case: (IH S0 _ _) => [|||t Ht].
        - by rewrite [#|S|](cardsD1 v) Hv.
        - apply/card_gt0P. exists v0. by rewrite !inE eq_sym X.
        - apply: sub_in11W clique_S. apply/subsetP. by rewrite subD1set.
        - have A : v0 \in B t. { apply (subsetP Ht). by rewrite !inE eq_sym X. }
          have H : connect sedge c t. 
          { apply: connect_mono (sbag_conn decD v0 c t Hc2 A). exact: subrel_restrict. }
          (* bespoke - is there a reasonable lemma? *)
          (* TOTHINK: this should follow with uPathRP / split_at_first / splitL / splitR *)
          case/connectP : H => p. generalize c inC. 
          elim: p => /= [|a p IHp] c0 inC0.
          + move => _ /= ?. subst c0. 
            case: (disjointE disC inC0 _). by rewrite !inE.
          + case/andP => H1 H2 H3. case: (boolP (a \in T0)) => Ha.
            * exists a. exists c0. by rewrite sgP.
            * apply: IHp H3 => //. rewrite inE. 
              apply: (connect_trans (y := c0)).
              by rewrite inE in inC0.
              apply: connect1 => /=. rewrite !in_simpl /= Ha H1 !andbT. 
              apply/negP. exact: disjointE disC inC0. }
      have t0P p c' : c' \in C -> upath t0 c' p -> c0 \in p.
      { apply: subtree_link tc0 => //.  apply/negP => H. exact: (disjointE disC H Ht0). }
      suff A : c0 \in T0 by case: (disjointE disC Hc0 A).
      rewrite inE. apply/subsetP => u u_in_S0.
      have Hu: u \in B t0. { rewrite inE in Ht0. exact: (subsetP Ht0). }
      have [cu [Hcu1 Hcu2]] : exists t,  u \in B t /\ v \in B t. 
      { apply: (pairs u v) => //. move: u_in_S0. rewrite inE. by case: (_ \notin _). }
      move:(sbag_conn decD u t0 cu Hu Hcu1). case/upathPR => q upth_q. 
      suff Hq : c0 \in q. { move/upathWW/path_restrict : upth_q. by apply. }
      apply: t0P (restrict_upath upth_q).
      rewrite inE. move: (sbag_conn decD v c cu Hc1 Hcu2).
      apply: connect_mono => t t' /=. 
      rewrite !inE -andbA => /and3P [*]. by rewrite !HT0'.
  Qed.
      
End DecompTheory.

(* TODO: use one generic construction for C3 and K4 *)

Definition C3_rel := [rel x y : 'I_3 | x != y].

Fact C3_sym : symmetric C3_rel. 
Proof. move => x y /=. by rewrite eq_sym. Qed.

Fact C3_irrefl : irreflexive C3_rel. 
Proof. move => x /=. by rewrite eqxx. Qed.

Definition C3 := SGraph C3_sym C3_irrefl.

Definition K4_rel := [rel x y : 'I_4 | x != y].

Fact K4_sym : symmetric K4_rel. 
Proof. move => x y /=. by rewrite eq_sym. Qed.

Fact K4_irrefl : irreflexive K4_rel. 
Proof. move => x /=. by rewrite eqxx. Qed.

Definition K4 := SGraph K4_sym K4_irrefl.

Lemma K4_bag (T : tree) (D : T -> {set K4}) : 
  sdecomp T K4 D -> exists t, 4 <= #|D t|.
Proof.
  move => decD.
  case: (@decomp_clique _ _ _ decD setT _ _) => //.
  - by rewrite cardsT card_ord.
  - move => t A. exists t. rewrite -[4](card_ord 4) -cardsT. 
    exact: subset_leq_card.
Qed.

(** K4 has with at least 4 *)

Lemma K4_width (T : tree) (D : T -> {set K4}) : 
  sdecomp T K4 D -> 4 <= width D.
Proof. case/K4_bag => t Ht. apply: leq_trans Ht _. exact: leq_bigmax. Qed.

(** ** Minors *)

Notation "f @^-1 x" := (preimset f (mem (pred1 x))) (at level 24) : set_scope.  

Lemma mem_preim (aT rT : finType) (f : aT -> rT) x y : 
  (f x == y) = (x \in f @^-1 y).
Proof. by rewrite !inE. Qed.

(** H is a minor of G -- The order allows us to write [minor G] for the
colletion of [G]s minors *)

Definition minor_map (G H : sgraph) (phi : G -> option H) := 
  [/\ (forall y : H, exists x : G, phi x = Some y),
     (forall y : H, connected (phi @^-1 Some y)) &
     (forall x y : H, x -- y -> exists x0 y0 : G,
      [/\ x0 \in phi @^-1 Some x, y0 \in phi @^-1 Some y & x0 -- y0])].

Definition minor (G H : sgraph) : Prop := exists phi : G -> option H, minor_map phi.

Fact minor_of_map (G H : sgraph) (phi : G -> option H): 
  minor_map phi -> minor G H.
Proof. case => *. by exists phi. Qed.


Lemma minor_trans : Transitive minor.
Proof.
  move => G H I [f [f1 f2 f3]] [g [g1 g2 g3]].
  exists (fun x => obind g (f x)); split.
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

Definition strict_minor_map (G H : sgraph) (phi : G -> H) := 
  [/\ (forall y : H, exists x, phi x = y), 
     (forall y : H, connected (phi @^-1 y)) &
     (forall x y : H, x -- y -> 
     exists x0 y0, [/\ x0 \in phi @^-1 x, y0 \in phi @^-1 y & x0 -- y0])].

Definition strict_minor (G H : sgraph) : Prop := 
  exists phi : G -> H, strict_minor_map phi.

Lemma map_of_strict (G H : sgraph) (phi : G -> H) : 
  strict_minor_map phi -> minor_map (Some \o phi).
Proof. case => A B C. split => // y. case: (A y) => x <-. by exists x. Qed.

Lemma strict_is_minor (G H : sgraph) : strict_minor G H -> minor G H.
Proof. move => [phi A]. exists (Some \o phi). exact: map_of_strict. Qed.

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
  - move => x y A. move/hom_h : (A). 
    case => [/inj_h ?|B]; first by subst; rewrite sgP in A.
    exists (h x). exists (h y). rewrite !inE /phi B. 
    by do 2 case: {-}_ / idP => [?|]; rewrite ?codom_f ?iinv_f ?eqxx //.
Qed.

Lemma induced_minor (G : sgraph) (S : {set G}) : minor G (induced S).
Proof. apply: sub_minor. exact: induced_sub. Qed.

Definition edge_surjective (G1 G2 : sgraph) (h : G1 -> G2) :=
  forall x y : G2 , x -- y -> exists x0 y0, [/\ h x0 = x, h y0 = y & x0 -- y0].

(* The following should hold but does not fit the use case for minors *)
Lemma rename_sdecomp (T : tree) (G H : sgraph) D (dec_D : sdecomp T G D) (h :G -> H) : 
  hom_s h -> surjective h -> edge_surjective h -> 
  (forall x y, h x = h y -> exists t, (x \in D t) && (y \in D t)) -> 
  @sdecomp T _ (rename D h).
Abort. 

(* This should hold, but there are several choices for S, the induced
subgraph of the range of [phi] seems to be the canonical one. *)
Lemma minor_split (G H : sgraph) : 
  minor G H -> exists2 S, subgraph S G & strict_minor S H.
Proof.
  move => [phi [p1 p2 p3]].
  set S := [set x | phi x]. 
  exists (induced S); first exact: induced_sub.
  wlog x0 : / H.
  { admit. (* the empty graph is a minor of ever graph *) }
  pose f (x : induced S) := odflt x0 (phi (val x)).
  exists f. 
Abort. 


Lemma width_minor (G H : sgraph) (T : tree) (B : T -> {set G}) : 
  sdecomp T G B -> minor G H -> exists B', sdecomp T H B' /\ width B' <= width B.
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
      { move => H1 H2 H3. case: (sbag_conn decT H2 H3).
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


Definition K4_free (G : sgraph) := ~ minor G K4.

Lemma TW2_K4_free (G : sgraph) (T : tree) (B : T -> {set G}) : 
  sdecomp T G B -> width B <= 3 -> K4_free G.
Proof.
  move => decT wT M. case: (width_minor decT M) => B' [B1 B2].
  suff: 4 <= 3 by []. 
  apply: leq_trans wT. apply: leq_trans B2. exact: K4_width.
Qed.

Section AddNode.
  Variables (G : sgraph) (N : {set G}).
  
  Definition add_node_rel (x y : option G) := 
    match x,y with 
    | None, Some y => y \in N
    | Some x, None => x \in N
    | Some x,Some y => x -- y
    | None, None => false
    end.

  Lemma add_node_sym : symmetric add_node_rel.
  Proof. move => [a|] [b|] //=. by rewrite sgP. Qed.

  Lemma add_node_irrefl : irreflexive add_node_rel.
  Proof. move => [a|] //=. by rewrite sgP. Qed.

  Definition add_node := SGraph add_node_sym add_node_irrefl.
End AddNode.
Arguments add_node : clear implicits.


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
