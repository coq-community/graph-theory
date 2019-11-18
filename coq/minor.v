Require Import RelationClasses.

From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries digraph sgraph treewidth.
Require Import set_tac.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 

(** * Minors, links with treewidth *)

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
  move=> [f1 f2 f3] [g1 g2 g3]. rewrite /comp; split.
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

Lemma iso_strict_minor (G H : sgraph) : diso G H -> strict_minor H G.
Proof.
  (* TODO: update proof to abstract against concrete implem of [diso] *)
  move=> [[h g hgK ghK] /= hH gH].
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
  diso G H -> K4_free H -> K4_free G.
Proof. move => iso_GH. apply: subgraph_K4_free. exact: iso_subgraph. Qed.

Lemma treewidth_K_free (G : sgraph) (T : forest) (B : T -> {set G}) m : 
  sdecomp B -> width B <= m.+1 -> ~ minor G 'K_m.+2.
Proof.
  move => decT wT M. case: (width_minor decT M) => B' [B1 B2].
  suff: m.+1 < m.+1 by rewrite ltnn.
  apply: leq_trans wT. apply: leq_trans B2. apply: (Km_width B1).
Qed.

Lemma TW2_K4_free (G : sgraph) (T : forest) (B : T -> {set G}) : 
  sdecomp B -> width B <= 3 -> K4_free G.
Proof. exact: treewidth_K_free. Qed.

Lemma small_K_free m (G : sgraph): #|G| <= m.+1 -> ~ minor G 'K_m.+2.
Proof.
  move => H. case: (decomp_small H) => T [D] [decD wD].
  exact: treewidth_K_free decD wD.
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


(** ** Excluded-Minor Characterization of Forests *)

Hint Resolve ivalP : core.

(* TODO: use this whenever explicitly exhibiting a minor map *)
Lemma minor_rmapI (G H : sgraph) (phi : H -> {set G}) (f : H -> nat) : 
  injective f ->
  (forall x : H, phi x != set0) -> 
  (forall x : H, connected (phi x)) -> 
  (forall x y : H, f x < f y -> [disjoint phi x & phi y]) ->
  (forall x y : H, f x < f y -> x -- y -> neighbor (phi x) (phi y)) ->
  minor_rmap phi.
Proof.
  move => inj_f M1 M2 M3 M4. split => // x y xy.
  - wlog: x y xy / f x < f y; last exact: M3.
    move => W. case: (ltngtP (f x) (f y)); first exact: W.
    + rewrite disjoint_sym eq_sym in xy *. exact: W.
    + move/inj_f => E. by rewrite E eqxx in xy.
  - wlog: x y xy / f x < f y; last by move => Hf; exact: M4 Hf xy.
    move => W. case: (ltngtP (f x) (f y)); first exact: W.
    + rewrite neighborC sgP in xy *. exact: W.
    + move/inj_f => E. by rewrite E sgP in xy.
Qed.

Section K3.
Variable (G : sgraph).

Lemma is_forestPn (S : {set G}) : 
  reflect (exists x y (p1 p2 : IPath x y), [/\ p1 \subset S, p2 \subset S & p1 != p2])
          (~~ is_forestb S).
Proof.
  rewrite negb_forall. apply: existsPP => x. 
  rewrite negb_forall. apply: existsPP => y. 
  rewrite -ltnNge. apply: (iffP card_gt1P) => /=. 
  all: by move => [p1] [p2] [A B C]; exists p1; exists p2.
Qed.

Lemma disjoint_part (x y : G) (p1 p2 : Path x y) : 
  irred p1 -> irred p2 -> p1 != p2 -> 
  exists (x' y' : G) (p1' p2' : IPath x' y'), [disjoint interior p1' & interior p2'] /\ interior p1' != set0.
Proof.
  move def_P : (mem p1 : pred G) => P. elim/proper_ind : P x y p1 def_P p2. 
  move => A IH x y p1 ? p2 Ip1 Ip2 Dp; subst A.
  have Dxy : x != y. 
  { apply: contraNneq Dp => ?; subst y. by rewrite (irredxx Ip1) (irredxx Ip2). }
  case: (boolP [disjoint interior p1 & interior p2]) => [dis12|].
  - wlog int_p1 : p1 p2 Ip1 Ip2 dis12 {IH Dp} / interior p1 != set0.
    { suff/orP [N|N] : (interior p1 != set0) || (interior p2 != set0).
      - by move => S; apply: S dis12 N. 
      - rewrite disjoint_sym in dis12. by move => S; apply: S dis12 N. 
      - apply: contra_neqT Dp. rewrite negb_or !negbK => /andP [/eqP N1 /eqP N2].
        have [[xy ->] [xy' ->]] := (interior0E Dxy Ip1 N1,interior0E Dxy Ip2 N2).
        exact/eqP. }
    by exists x; exists y; exists (Build_IPath Ip1); exists (Build_IPath Ip2). 
  - rewrite disjoint_exists negbK. case/exists_inP => z Z1 Z2.
    case/(isplitP Ip1) def_p1 : _ / (interiorW Z1) => [p1l p1r Ip1l Ip1r Iz1].
    case/(isplitP Ip2) def_p2 : _ / (interiorW Z2) => [p2l p2r Ip2l Ip2r Iz2].
    have/orP [Dl|Dr] : (p1l != p2l) || (p1r != p2r).
    { apply: contraNT Dp. by rewrite negb_or !negbK def_p1 def_p2 => /andP[/eqP->/eqP->]. }
    + apply: (IH _ _ x z p1l _ p2l) => //=. apply/properP. 
      rewrite def_p1 subset_pcatL; split => //; exists y; first by rewrite !inE.
      apply: contraTN Z1 => C. by rewrite -(Iz1 y) ?inE // eqxx. 
    + apply: (IH _ _ z y p1r _ p2r) => //=. apply/properP. 
      rewrite def_p1 subset_pcatR; split => //; exists x; first by rewrite !inE.
      apply: contraTN Z1 => C. by rewrite -(Iz1 x) ?inE // eqxx. 
Qed.

Lemma non_forerst_K3 : ~ is_forest [set: G] -> minor G 'K_3.
Proof.
  move/is_forestP/is_forestPn => [x0] [y0] [p0] [q0] [_ _ pDq].
  have [x [y] [p1] [p2] [p12_disj p1_ne]] := disjoint_part (valP p0) (valP q0) pDq.
  clear x0 y0 p0 q0 pDq.
  pose phi (i : 'K_3) : {set G} :=
    match i with 
    | Ordinal 0 _ => [set x]
    | Ordinal 1 _ => interior p1
    | Ordinal 2 _ => y |: interior p2
    | Ordinal _ _ => set0
    end.
  suff: minor_rmap phi by apply: minor_of_rmap.
  have xDy : x != y. 
  { apply: contra_neq p1_ne => ?; subst y. 
    by rewrite /path_of_ipath (irredxx (valP p1)) interior_idp. }
  apply: minor_rmapI; first exact: ord_inj.
  - case => [[|[|[|i]]] Hi] //=; [exact: set10 | exact: setU1_neq]. 
  - case => [[|[|[|i]]] Hi] //=. 
    + exact: connected1. 
    + exact: connected_interior.
    + exact: connected_interiorR.
  - case => [[|[|[|i]]] Hi]; case => [[|[|[|j]]] Hj] //= _.
    + by rewrite disjoints1 !inE eqxx.
    + by rewrite disjoints1 !inE eqxx (negbTE xDy).
    + rewrite disjoint_sym disjointsU // ?disjoints1 1?disjoint_sym //.
      by rewrite !inE eqxx.
  - case => [[|[|[|i]]] Hi]; case => [[|[|[|j]]] Hj] //= _ _.
    + apply: path_neighborL => //. by rewrite inE.
    + exact: neighbor_interiorL.
    + apply: neighborUl. rewrite neighborC. 
      apply: path_neighborR => //. by rewrite inE.
Qed.

Lemma K3_free_forest : ~ minor G 'K_3 -> is_forest [set: G].
Proof. 
  rewrite (rwP (is_forestP _)). apply: contraPT. move/is_forestP.
  exact: non_forerst_K3.
Qed.

(* TODO: This is actually redundant if we also prove that forests have
tree decompositions of width 1 *)
Lemma forest_K3_free : is_forest [set: G] -> ~ minor G 'K_3.
Proof.
  move/forestT_unique => forest_G /minorRE [phi [M1 M2 M3 M4]].
  have/neighborP [x1 [y1] [Px1 Py1 xy1]] := (M4 ord0 ord1 isT).
  have/neighborP [x2 [y2] [Px2 Py2 xy2]] := (M4 ord0 ord2 isT).
  have Dy : y1 != y2. 
  { apply: contraTneq (M3 ord1 ord2 _) => //= ?; subst y2. 
    exact: disjointNI Py1 Py2. }
  pose A := phi ord1 :|: phi ord2.
  have conn_A : connected A. { apply: neighbor_connected => //. exact: M4. }
  have disj_A : [disjoint A & phi ord0] by apply: disjointsU; apply: M3.
  have [Y1 Y2] : y1 \in A /\ y2 \in A by rewrite /A !inE Py1 Py2.
  have [p Ip p_sub_A] := path_in_connected conn_A Y1 Y2.
  have [q Iq q_sub_A] := path_in_connected (M2 _) Px1 Px2.
  rewrite sg_sym in xy1.
  pose q' := pcat (edgep xy1) (pcat q (edgep xy2)).
  suff Ip' : irred q'.
  { apply/negP : disj_A. apply: disjointNI Px1. 
    apply: (subsetP p_sub_A). by rewrite (forest_G _ _ p q') // !inE. }
  rewrite irred_edgeL irred_edgeR Iq andbT !inE negb_or mem_edgep.
  gen have Hq,-> : y1 {Py1 Dy} Y1 {p Ip p_sub_A xy1 q'} / y1 \notin q.
  { apply: contraTN disj_A => /(subsetP q_sub_A). exact: disjointNI. }
  rewrite Hq //= andbT (negbTE Dy) orbF. 
  apply: contraTneq disj_A => ?;subst. exact: disjointNI Px2. 
Qed.

End K3.
