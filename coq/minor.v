Require Import RelationClasses.

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

Record sdecomp (T : forest) (G : sgraph) (B : T -> {set G}) := SDecomp
  { sbag_cover x : exists t, x \in B t; 
    sbag_edge x y : x -- y -> exists t, (x \in B t) && (y \in B t);
    sbag_conn x t1 t2  : x \in B t1 -> x \in B t2 ->
      connect (restrict [pred t | x \in B t] sedge) t1 t2}.

Arguments sdecomp T G B : clear implicits.

Lemma sdecomp_eq (V : finType) (e1 e2 : rel V) (T:forest) (D : T -> {set V}) 
      (e1_sym : symmetric e1) (e1_irrefl : irreflexive e1) 
      (e2_sym : symmetric e2) (e2_irrefl : irreflexive e2):
  e1 =2 e2 -> 
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

Section DecompTheory.
  Variables (G : sgraph) (T : forest) (B : T -> {set G}).
  Implicit Types (t u v : T) (x y z : G).

  Hypothesis decD : sdecomp T G B.

  Arguments sbag_conn [T G B] dec x t1 t2 : rename.

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
    - have [v [v0] [Hv Hv0 X]] := card_gt1P (ltnW card_S).
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
      { move => xS yS. case: (IH [set x;y]). 
        - rewrite cardsU1 cards1 addn1. case (_ \notin _) => //=. exact: ltnW.
        - by rewrite cards2. 
        - apply: sub_in11W clique_S. apply/subsetP. by rewrite subUset !sub1set xS. 
        - move => t. rewrite subUset !sub1set => /andP [? ?]. by exists t. }
      (* obtain some node [c] whose bag contains [[set v,v0]] and
      consider its subtree outside of T0 *)
      have [c [Hc1 Hc2]] : exists t, v \in B t /\ v0 \in B t by apply: pairs. 
      pose C := [set t in [predC T0] | connect (restrict [predC T0] sedge) c t].
      have inC: c \in C. { rewrite !inE connect0 andbT. exact: HT0'. }
      have con_C : connected C. 
      { apply: connected_restrict. move: inC. rewrite inE. by case/andP. }
      have dis_C : [disjoint C & T0]. 
      { rewrite disjoints_subset /C. apply/subsetP => t. rewrite !inE. by case/andP. }
      (* There exists an edge connecting [C] and [T0] *)
      have [t0 [c0 [Ht0 Hc0 tc0]]] : exists t0 c0, [/\ t0 \in T0, c0 \in C & t0 -- c0].
      { case: (IH S0 _ _) => [|||t Ht].
        - by rewrite [#|S|](cardsD1 v) Hv.
        - apply/card_gt0P. exists v0. by rewrite !inE eq_sym X.
        - apply: sub_in11W clique_S. apply/subsetP. by rewrite subD1set.
        - have A : v0 \in B t. { apply (subsetP Ht). by rewrite !inE eq_sym X. }
          have/uPathRP [|p Ip _] := (sbag_conn decD v0 c t Hc2 A).
          { apply: contraTneq inC => ->. by rewrite !inE Ht. }
          move: (c) p Ip (inC). apply: irred_ind; first by rewrite !inE Ht.
          move => x z p xz Ip xp IHp xC.
          case: (boolP (z \in C)) => [|zNC {IHp}] ; first exact: IHp.
          exists z; exists x. rewrite sgP. split => //. apply: contraNT zNC => H.
          rewrite 2!inE /= in xC. case/andP : xC => H1 H2.
          rewrite 2!inE /= (negbTE H) /=. apply: connect_trans H2 _.
          apply: connect1 => /=. by  rewrite 2!inE H1 2!inE xz H. }
      (* In fact, every path into [C] must use this edge (and [c0]) *)
      have t0P c' (p : Path t0 c') : irred p -> c' \in C -> c0 \in p.
      { move => Ip inC'. 
        case: (altP (c0 =P c')) => [-> |?]. by rewrite path_end.
        have/uPathRP [//|q Iq /subsetP subC] := con_C _ _ Hc0 inC'.
        suff -> : p = pcat (edgep tc0) q by rewrite mem_pcat path_end.
        apply: forest_is_forest; (repeat split) => //. 
        rewrite irred_edgeL Iq andbT. 
        apply: contraTN Ht0 => /subC => H. by rewrite (disjointFr dis_C H). }
      (* We show that [c0] contains the full clique *)
      suff A : c0 \in T0 by case: (disjointE dis_C Hc0 A).
      rewrite inE. apply/subsetP => u u_in_S0.
      have Hu: u \in B t0. { rewrite inE in Ht0. exact: (subsetP Ht0). }
      have [cu [Hcu1 Hcu2]] : exists t, u \in B t /\ v \in B t. 
      { apply: (pairs u v) => //. move: u_in_S0. rewrite inE. by case: (_ \notin _). }
      move:(sbag_conn decD u t0 cu Hu Hcu1). 
      case/uPathRP => [|q irr_p /subsetP has_u]. 
      { apply: contraTneq Hcu2 => <-.  exact: HT0. }
      suff Hq : c0 \in q. { move/has_u : Hq. by rewrite inE. }
      apply: t0P irr_p _. rewrite !inE /= HT0' //=. 
      move: (sbag_conn decD v c cu Hc1 Hcu2). 
      apply: connect_mono => t t' /=. 
      rewrite !inE -andbA => /and3P [*]. by rewrite !HT0'.
  Qed.
      
End DecompTheory.



(** ** Complete graphs *)

Definition complete_rel n := [rel x y : 'I_n | x != y].
Fact complete_sym n : symmetric (complete_rel n).
Proof. move => x y /=. by rewrite eq_sym. Qed.
Fact complete_irrefl n : irreflexive (complete_rel n).
Proof. move => x /=. by rewrite eqxx. Qed.
Definition complete n := SGraph (@complete_sym n) (@complete_irrefl n).
Notation "''K_' n" := (complete n)
  (at level 8, n at level 2, format "''K_' n").

Definition C3 := 'K_3.
Definition K4 := 'K_4.

Lemma K4_bag (T : forest) (D : T -> {set K4}) : 
  sdecomp T K4 D -> exists t, 4 <= #|D t|.
Proof.
  move => decD.
  case: (@decomp_clique _ _ _ decD setT _ _) => //.
  - by rewrite cardsT card_ord.
  - move => t A. exists t. rewrite -[4](card_ord 4) -cardsT. 
    exact: subset_leq_card.
Qed.

(** K4 has with at least 4 *)

Lemma K4_width (T : forest) (D : T -> {set K4}) : 
  sdecomp T K4 D -> 4 <= width D.
Proof. case/K4_bag => t Ht. apply: leq_trans Ht _. exact: leq_bigmax. Qed.


(** ** Minors *)

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
     (forall x y : H, x -- y -> exists x' y' : G, [/\ x' \in phi x, y' \in phi y & x' -- y'])].

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
  - move => x y /P4 [x0] [y0] [*]. exists x0;exists y0. by rewrite -!mem_preim -!phiP.
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
  - move => x y /P3 [x0] [y0] [*]. exists x0;exists y0. by rewrite !inE !mem_preim. 
Qed.
      

Definition minor (G H : sgraph) : Prop := exists phi : G -> option H, minor_map phi.

Fact minor_of_map (G H : sgraph) (phi : G -> option H): 
  minor_map phi -> minor G H.
Proof. case => *. by exists phi. Qed.

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
Lemma rename_sdecomp (T : forest) (G H : sgraph) D (dec_D : sdecomp T G D) (h :G -> H) : 
  hom_s h -> surjective h -> edge_surjective h -> 
  (forall x y, h x = h y -> exists t, (x \in D t) && (y \in D t)) -> 
  @sdecomp T _ (rename D h).
Abort. 



Lemma width_minor (G H : sgraph) (T : forest) (B : T -> {set G}) : 
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

  Lemma add_node_lift_Path (x y : G) (p : Path x y) :
    exists q : @Path add_node (Some x) (Some y), nodes q = map Some (nodes p).
  Proof.
    case: p => p0 p'.
    set q0 : seq add_node := map Some p0.
    have q' : @spath add_node (Some x) (Some y) q0.
      move: p'; rewrite /spath/= last_map (inj_eq (@Some_inj _)).
      move=> /andP[p' ->]; rewrite andbT.
      exact: project_path p'.
    by exists (Sub _ q'); rewrite !nodesE /=.
  Qed.

  (* TODO: theory for [induced [set~ : None : add_node]] *)
  Lemma minor_induced_add_node : @minor_map (induced [set~ None : add_node]) G val.
  Proof.
  have inNoneD (a : G) : Some a \in [set~ None] by rewrite !inE. split.
    + move=> y. by exists (Sub (Some y) (inNoneD y)).
    + move=> y x1 x2. rewrite -!mem_preim =>/eqP<- /eqP/val_inj->. exact: connect0.
    + move=> x y xy. exists (Sub (Some x) (inNoneD x)).
      exists (Sub (Some y) (inNoneD y)). by split; rewrite -?mem_preim.
  Qed.
End AddNode.
Arguments add_node : clear implicits.

Lemma add_node_complete n : sg_iso 'K_n.+1 (add_node 'K_n setT).
Proof.
  pose g : add_node 'K_n setT -> 'K_n.+1 := oapp (lift ord_max) ord_max.
  pose h : 'K_n.+1 -> add_node 'K_n setT := unlift ord_max.
  exists g h; rewrite /g/h/=.
  + move=> [x|] /=; [by rewrite liftK | by rewrite unlift_none].
  + by move=> x; case: unliftP.
  + move=> [x|] [y|] //=; rewrite ?[_ == ord_max]eq_sym ?neq_lift //.
    by rewrite (inj_eq (@lift_inj _ ord_max)).
  + move=> x y /=; do 2 case: unliftP => /= [?|]-> //; last by rewrite eqxx.
    by rewrite (inj_eq (@lift_inj _ ord_max)).
Qed.

Lemma connected_add_node (G : sgraph) (U A : {set G}) : 
  connected A -> @connected (add_node G U) (Some @: A).
Proof. 
  move => H x y /imsetP [x0 Hx0 ->] /imsetP [y0 Hy0 ->].
  have/uPathRP := H _ _ Hx0 Hy0. 
  case: (x0 =P y0) => [-> _|_ /(_ isT) [p _ Hp]]; first exact: connect0.
  case: (add_node_lift_Path U p) => q E. 
  apply: (connectRI (p := q)) => ?. 
  rewrite !inE mem_path -nodesE E.
  case/mapP => z Hz ->. rewrite mem_imset //. exact: (subsetP Hp).
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
