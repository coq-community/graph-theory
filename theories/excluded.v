Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect.
(* Note: ssrbool is empty and shadows Coq.ssr.ssrbool, use Coq.ssrbool for "Find" *)

Require Import edone preliminaries set_tac.
Require Import digraph sgraph treewidth minor connectivity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs". 

(** * Tree Decompositions for K4-free graphs *)

Ltac notHyp b ::= assert_fails (assert b by assumption).

Prenex Implicits vseparator.
Implicit Types G H : sgraph.
Arguments sdecomp : clear implicits.
Arguments rename_decomp [T G H D]. 

(* Pushing M-freeness (for some excluded minor M) to the subgraphs of
[add_edge G x y] induced by [V1] and [V2] where [V1,V2] is a proper
separation whose shared part is the minimal separator [[set x;y]]. *)

Section AddEdgeMinor.
Variables (G : sgraph) (x y : G) (V1 V2 : {set G}).
Let G' := add_edge x y.

Lemma unused_add_edge_connect_r (A : {pred G}) : 
  y \notin A -> subrel (restrict A (@sedge G')) (restrict A (@sedge G)).
Proof.
move=> yNA u v /=; rewrite -!andbA => /and3P [uA vA].
gen have H,-> : u uA / u == y = false; first by apply:contraTF uA => /eqP->.
by rewrite (H v) // !andbF !orbF uA vA.
Qed.

Lemma unused_rmap_add_edge_r (M : sgraph) (phi : M -> {set G'}) : 
  (forall i, y \notin phi i) -> minor_rmap phi -> @minor_rmap G M phi.
Proof.
move => y_unused [P1 P2 P3 P4].
have Y u i : u \in phi i -> u == y = false by apply: contraTF => /eqP ->.
split => //; last by move => i j ij; apply: neighbor_del_edge2 (P4 i j ij).
move => i u v u_pi v_pi; have:= P2 i u v u_pi v_pi.
exact/connect_mono/unused_add_edge_connect_r/y_unused.
Qed.

Hypothesis xDy : x != y.
Hypothesis psepV : proper_separation V1 V2.
Let S := V1 :&: V2.
Hypothesis defS : S = [set x;y].
Hypothesis ssepS : smallest vseparator S.

Lemma add_edge_rmap_separation_minor (M : sgraph) (phi : M -> {set G'}) : 
  minor_rmap phi -> (forall u, phi u \subset V1) -> minor G M.
Proof.
move => rmap_phi sub_phi.
have [/existsP[i] y_phi_i|/existsPn Y] := boolP [exists i, y \in phi i]; last first.
  by have := unused_rmap_add_edge_r Y rmap_phi; apply: minor_of_rmap.
have x_S : x \in S by rewrite defS !inE eqxx.
have [_ [z [_ zNV1 _ xz]]] := svseparator_neighbours psepV ssepS x_S.
have [p irp dis] : exists2 p : Path z y, irred p & [disjoint p & [set x]].
{ apply: (@avoid_nonseperator G [set x] z y).
  - by apply: below_smallest ssepS _; rewrite defS cards1 cards2 xDy.
  - by rewrite inE eq_sym ?(sg_edgeNeq xz). 
  - by rewrite inE eq_sym. }
rewrite disjoint_sym disjoints1 in dis.
have pV2: p \subset V2. 
{ apply: contraTT isT => /subsetPn [z' z'p z'NV2].
  case/psplitP: _ / z'p irp dis => {p} [p1 p2] /irred_catE [_ _ Ip] s1p.
  move/proper_separation_symmetry : (psepV) => psepV'.
  case: (separation_separates psepV'.1 zNV1 z'NV2) => _ _ /(_ p1) [s S1].
  rewrite setIC -/S defS => /set2P [?|?]; subst s; first by set_tac.
  rewrite -(Ip y) // in z'NV2. 
  by move/setP/(_ y) : defS; rewrite /S !inE (negbTE z'NV2) eqxx orbT andbF. }
pose g := phi[upd i := phi i :|: [set v in p]] : M -> {set G}.
suff: minor_rmap g by apply minor_of_rmap.
have [P1 P2 P3 P4] := rmap_phi.
rewrite /g; split.
- move=> j; have [->{j}|jDi] := eqVneq j i; rewrite updateE //.
  by case/set0Pn : (P1 i) => v v_pi; apply/set0Pn; exists v; rewrite inE v_pi.
- move=> j; have [->{j}|jDi] := eqVneq j i; rewrite updateE //; last first.
    move => u v u_pj v_pj; apply: connect_mono (P2 j u v u_pj v_pj).
    by apply/unused_add_edge_connect_r; rewrite (disjointFl (P3 _ _ jDi)).
  apply: (@connected_center _ y) => [u|]; last by rewrite inE y_phi_i.
  case/setUP => [u_phi_i|]; last first. 
  + rewrite !inE srestrict_sym => u_p. 
    case/psplitP def_p : _  / u_p => [p1 p2].
    by apply: (connectRI p2) => v; rewrite !inE => ->.
  + have [<- //|yDu] := eqVneq y u.
    have/connect_irredRP-/(_ yDu) [q Iq q_sub_i] := P2 _ _ _ y_phi_i u_phi_i.
    have [v [yv [q' [def_q _]]]] := splitL q yDu.
    have v_phi_i : v \in phi i by rewrite (subsetP q_sub_i) // def_q !inE.      
    apply: (@connect_trans _ _ v); last first.
    * have yNq : y \notin q' by move: Iq; rewrite def_q irred_edgeL => /andP[->].
      have := add_edge_avoid q'; rewrite yNq orbT /= => /(_ isT) [q'' eq_q]. 
      apply: (connectRI q'') => w; rewrite !inE mem_path eq_q => w_q.
      by rewrite (subsetP q_sub_i) // def_q !inE !mem_path w_q.
    * move: (yv). rewrite /edge_rel/= eqxx [v == y]eq_sym (sg_edgeNeq yv).
      rewrite !(andbF,andbT)/= orbC => /predU1P [eq_vx|yvG]; last first.
        by apply: connect1 => /=; rewrite !inE v_phi_i.
      subst v. apply: (@connect_trans _ _ z); last first.
        by apply: connect1 => /=; rewrite !inE v_phi_i sgP.
      by rewrite srestrict_sym; apply: (connectRI p) => w; rewrite !inE => ->.
- move => j k jDk; have [i_jk|] := boolP (i \in [set j; k]); last first.
    rewrite !inE negb_or ![i == _]eq_sym => /andP[? ?].
    by rewrite !updateE // P3.
  wlog ?: j k jDk {i_jk} / i = j => [W|]; last subst j.
    case/set2P : i_jk; last rewrite disjoint_sym; apply: W => //.
    by rewrite eq_sym.
  rewrite !updateE 1?eq_sym // disjointsU // ?P3 // disjoint_subset.
  apply/subsetP => v; rewrite !inE => v_p; apply: contraNN dis => v_phi_k.
  have: v \in S by apply/setIP; rewrite (subsetP pV2) // (subsetP (sub_phi k)).
  rewrite defS => /set2P [<- //|vEy]. 
  by rewrite vEy (disjointFr (P3 _ _ jDk)) in v_phi_k.
- move=> j k jk; have [i_jk|] := boolP (i \in [set j; k]); last first.
  { rewrite !inE negb_or ![i == _]eq_sym => /andP[A B].
    rewrite !updateE // neighbor_del_edge2 // ?P4 //.
    all: by rewrite ?(disjointFl (P3 _ _ A)) ?(disjointFl (P3 _ _ B)). }
  wlog ?: j k jk {i_jk} / i = j => [W|]; last subst j.
    case/set2P : i_jk; first exact: W.
    by rewrite neighborC; apply: W; rewrite // sgP.
  rewrite !updateE 1?eq_sym ?sg_edgeNeq //.
  have/neighborP[u[v [u_phi_i v_phi_k]]] := P4 _ _ jk.
  have dis_ij w w' : w \in phi i -> w' \in phi k -> w' == w = false.
  { move => A B. apply: contraTF jk => /eqP ?; subst w'.
    by rewrite (rmap_disjE rmap_phi A B) sgP. }
  rewrite /edge_rel/= (dis_ij _ _ y_phi_i v_phi_k) !andbF.
  rewrite (dis_ij _ _ u_phi_i v_phi_k) /= => /orP [uv|/andP[/eqP? /eqP?]].
    by apply/neighborP; exists u,v; rewrite !inE u_phi_i v_phi_k uv.
  by subst v u; apply/neighborP; exists z,x; rewrite !inE v_phi_k sgP xz.
Qed.

Lemma add_edge_separation_minor M : minor (@induced G' V1) M -> minor G M.
Proof.
move=> minorM.
suff [phi]: exists2 phi : M -> {set G'}, minor_rmap phi & forall u, phi u \subset V1.
  exact: add_edge_rmap_separation_minor.
case/minorRE : minorM => phi rmap_phi.
pose phi' (u : M) := \bigcup_(v in phi u) induced_rmap v : {set G'}.
exists phi'; first by apply: minor_rmap_comp => //; apply: induced_rmapP.
move=> u. apply/bigcupsP=> v ?. exact: induced_rmap_sub. 
Qed.

Lemma add_edge_separation_excluded M : 
  ~ minor G M -> ~ minor (@induced G' V1) M.
Proof. exact/contra_not/add_edge_separation_minor. Qed.

End AddEdgeMinor.

Lemma connectedI_clique (G : sgraph) (A B S : {set G}) :
  connected A -> clique S -> 
  (forall x y (p : Path x y), p \subset A -> x \in B -> y \notin B -> 
     exists2 z, z \in p & z \in S :&: B) ->
  connected (A :&: B).
Proof.
  move => conA clS H x y /setIP [X1 X2] /setIP [Y1 Y2].
  case: (altP (x =P y)) => [->|xDy]; first exact: connect0.
  case/connect_irredRP : (conA _ _ X1 Y1) => // p Ip subA. 
  case: (boolP (p \subset B)) => subB.
  - apply connectRI with p => z zp. by set_tac.
  - case/subsetPn : subB => z Z1 Z2. 
    gen have C,Cx : x y p Ip subA X1 X2 Y1 Y2 Z1 Z2 {xDy} / 
        exists2 s, s \in S :&: A :&: B & connect (restrict (A :&: B) sedge) x s.
    { case: (split_at_first (A := [predC B]) Z2 Z1) => u' [p1] [p2] [P1 P2 P3].
      subst p. case/irred_catE : Ip => Ip1 Ip2 Ip.
      case/splitR : (p1); first by apply: contraNneq P2 => <-.
      move => u [p1'] [uu'] E. subst p1. 
      have uB : u \in B. apply: contraTT (uu') => C. by rewrite [u]P3 ?sgP // !inE.
      exists u. case: (H _ _ (edgep uu')) => //.
      - apply: subset_trans subA. 
        apply: subset_trans (subset_pcatL _ _). exact: subset_pcatR.
      - move => ?. rewrite !inE mem_edgep. case/orP => /eqP-> /andP[U1 U2]. 
        + by rewrite U1 U2 (subsetP subA) // !inE.
        + by rewrite !inE U2 in P2.
      - apply connectRI with p1' => v Hv. 
        rewrite !inE (subsetP subA) ?inE ?Hv //=.
        move: Ip1. rewrite irred_edgeR andbC => /andP [Ip1].
        apply: contraNT => C. by rewrite -(P3 v) // !inE Hv. }
    case: Cx => s. rewrite !inE -andbA => /and3P [S1 S2 S3 S4].
    case: (C _ _ (prev p)); rewrite ?mem_prev ?irred_rev //. 
    + apply: subset_trans subA. apply/subsetP => ?. by rewrite !inE.
    + move => t. rewrite !inE -andbA => /and3P [T1 T2 T3 T4].
      apply: connect_trans S4 _. rewrite srestrict_sym.
      apply: connect_trans T4 _. case: (altP (t =P s)) => [-> //|E].
      apply: connect1 => /=. by rewrite !inE clS. 
Qed.

(** only needed for [K4_free_add_edge_sep_size2] *)
Lemma separation_K4side G (V1 V2 : {set G}) : 
  separation V1 V2 -> clique (V1 :&: V2) -> #|V1 :&: V2| <= 2 ->
  minor G K4 -> 
  exists2 phi : K4 -> {set G}, minor_rmap phi & 
     (forall x, phi x \subset V1) \/ (forall x, phi x \subset V2).
Proof.
  move => sepV clV12 cardV12 /minorRE [phi] [P1 P2 P3 P4].
  wlog/forallP cutV1 : V1 V2 sepV clV12 cardV12 / [forall x, phi x :&: V1 != set0].
  { move => W.
    case: (boolP [forall x, phi x :&: V1 != set0]) => A; first exact: (W V1 V2).
    case: (boolP [forall x, phi x :&: V2 != set0]) => B. 
    { setoid_rewrite <- or_comm. by apply: W; rewrite 1?setIC // separation_sym. }
    case: notF. case/forallPn : A => i /negPn Hi. case/forallPn : B => j /negPn Hj.
    case: (altP (i =P j)) => [E|E].
    - subst j. case/set0Pn : (P1 i) => x Hx. case/setUP : (sepV.1 x) => Hx'.
      + move/eqP/setP/(_ x) : Hi. by rewrite !inE Hx Hx'.
      + move/eqP/setP/(_ x) : Hj. by rewrite !inE Hx Hx'.
    - move/neighborP : (P4 i j E) => [x] [y] [A B]. rewrite sgP sepV //.
      apply: contraTN Hj => Hy. by apply/set0Pn; exists y; rewrite inE B.
      apply: contraTN Hi => Hx. by apply/set0Pn; exists x; rewrite inE A. }
  set S := V1 :&: V2 in clV12 cardV12.
  have phiP i y : y \in phi i -> y \notin V1 -> phi i :&: S != set0.
  { case/set0Pn : (cutV1 i) => x /setIP [xpi xV1 ypi yV1].
    case: (boolP (x \in V2)) => xV2; first by apply/set0Pn; exists x; rewrite !inE.
    case/connect_irredRP : (P2 i x y xpi ypi); first by apply: contraNneq yV1 => <-.
    move => p Ip subP. 
    have [_ _ /(_ p)] := separation_separates sepV xV2 yV1.
    case => z /(subsetP subP) => ? ?. apply/set0Pn; exists z. by rewrite /S inD. }
  pose phi' (i : K4) := phi i :&: V1.
  exists phi'; first split.
  - move => i. exact:cutV1.
  - move => i. apply connectedI_clique with S => //.
    + move => x y p sub_phi Hx Hy. case: (boolP (x \in V2)) => Hx'.
      * exists x => //. by rewrite /S inD.
      * have [_ _ /(_ p) [z ? ?]] := (separation_separates sepV Hx' Hy).
        exists z => //. by rewrite /S inD.
  - move => i j /P3 => D. apply: disjointW D; exact: subsetIl.
  - move => i j ij. move/P4/neighborP : (ij) => [x] [y] [H1 H2 H3]. 
    have S_link u v : u \in S -> v \in S -> u \in phi i -> v \in phi j -> u -- v.
    { have D: [disjoint phi i & phi j] by apply: P3; rewrite sg_edgeNeq.
      (* TOTHINK: make set_tac use/prove [x == y] or [x != u]. *)
      move => H *. apply: clV12 => //. by apply: contraTneq H => ?; set_tac. }
    have/subsetP subV : S \subset V1 by exact: subsetIl.
    have inS u v : u -- v -> u \in V1 -> v \notin V1 -> u \in S.
    { move => uv HVu HVv. apply: contraTT uv => /= C. subst S. 
      by rewrite sepV // notinD. }   
    apply/neighborP. case: (boolP (x \in V1)) => HVx; case: (boolP (y \in V1)) => HVy.
    + exists x; exists y. by rewrite !inE HVx HVy.
    + case/set0Pn : (phiP _ _ H2 HVy) => s /setIP [S1 S2]. 
      exists x; exists s. rewrite !inE H1 HVx S1 S_link // ?subV //. exact: inS HVy.
    + case/set0Pn : (phiP _ _ H1 HVx) => s /setIP [S1 S2].
      exists s; exists y. rewrite !inE H2 HVy S1 S_link // ?subV //. 
      apply: inS HVx => //. by rewrite sgP.
    + case/set0Pn : (phiP _ _ H1 HVx) => s /setIP [S1 S2].
      case/set0Pn : (phiP _ _ H2 HVy) => s' /setIP [S3 S4].
      exists s; exists s'. by rewrite !inE S1 S3 S_link // !subV.
  - left => x. exact: subsetIr.
Qed.

Lemma K4_of_paths (G : sgraph) x y s0 s1' (p0 p1 p2 : Path x y) (q1 : Path s0 s1') : 
  x!=y -> independent p0 p1 -> independent p0 p2 -> independent p1 p2 ->
  s0 \in interior p0 -> s1' \in interior p1 -> 
  irred p0 -> irred p1 -> irred p2 -> irred q1 -> 
  [disjoint q1 & [set x; y]] -> 
  (forall z' : G, z' \in [predU interior p1 & interior p2] -> z' \in q1 -> z' = s1') -> 
  minor G K4.
Proof.
  move => xDy ind01 ind02 ind12 sp0 in_p1 Ip0 Ip1 Ip2 Iq av_xy s1'firstp12.
  pose phi (i : K4) := match i with
                  | Ordinal 0 _ => [set x]
                  | Ordinal 1 _ => interior p0 :|: interior q1
                  | Ordinal 2 _ => interior p1
                  | Ordinal 3 _ => y |: interior p2
                  | Ordinal p n => set0
                  end.
  suff: minor_rmap phi by apply minor_of_rmap.
  split.
  - move => [m i]. case m as [|[|[|[|m]]]] => //=; apply /set0Pn.
    + exists x. by set_tac.
    + exists (s0). by rewrite inE sp0.
    + by exists s1'.
    + exists y. by set_tac.
  - move => [m i]. case m as [|[|[|[|m]]]] => //=.
    + exact: connected1.
    + case: (altP (interior q1 =P set0)) => [->|H].
      * rewrite setU0. exact: connected_interior. 
      * apply: neighbor_connected; try exact: connected_interior.
        exact: path_neighborL.
    + exact: connected_interior. 
    + exact: connected_interiorR. 
  - move => i j iNj. wlog iltj: i j {iNj} / i < j.
    { move => H. rewrite /= neq_ltn in iNj. 
      move: iNj => /orP [iltj|jlti]; [|rewrite disjoint_sym]; exact: H. }
    destruct i as [m i]. destruct j as [n j].
    case m as [|[|[|[|m]]]] => //=; case n as [|[|[|[|m']]]] => //=.
    + rewrite disjoints1. rewrite inE negb_or /interior notinD /=.
      have: (x \in [set x; y]); by set_tac.
    + rewrite disjoints1. by rewrite /interior; set_tac.
    + rewrite disjoints1. by rewrite /interior; set_tac.
    + apply: disjointsU => //. apply/disjointP => z Z1 Z2. 
      suff: z = s1' by move: Z1 Z2; rewrite /interior; set_tac.
      apply: s1'firstp12. by rewrite inE /= Z2. exact: interiorW.
    + apply: disjointsU => //.
      * rewrite disjoint_sym. apply: disjointsU. 
        -- rewrite /interior. apply/disjointP; by set_tac.
        -- by rewrite disjoint_sym. 
      * rewrite disjoint_sym. apply: disjointsU.
        -- apply/disjointP. rewrite /interior. have: (y \in [set x; y]); by set_tac. 
        -- apply/disjointP => z Z1 Z2. 
           suff: z = s1' by move: Z1 Z2; rewrite /interior; set_tac.
           apply: s1'firstp12. by rewrite inE /= Z1. exact: interiorW.
    + rewrite disjoint_sym. apply: disjointsU. 
      * rewrite disjoints1 /interior. by set_tac.
      * by rewrite disjoint_sym.
  - move => i j iNj. wlog iltj: i j {iNj} / i < j.
    { move => H. rewrite /edge_rel /= neq_ltn in iNj. 
      move: iNj => /orP [iltj|jlti]; [|rewrite neighborC]; exact: H. }
    destruct i as [m i]. destruct j as [n j].
    (* Hints for automation *)
    have [[? ?] ?] := (valP (p0),valP p1, valP p2).
    case m as [|[|[|[|m]]]] => //=; case n as [|[|[|[|m']]]] => //=.
    + apply: neighborUl. apply: path_neighborL => //; by set_tac.
    + apply: path_neighborL => //; by set_tac.
    + exact: neighbor_interiorL. 
    + case: (altP (interior q1 =P set0)) => [E|H]. 
      * rewrite E setU0. apply/neighborP; exists (s0); exists s1'. split => //.
        case/interior0E : E => //. apply: contraTneq ind01. 
        rewrite /independent; set_tac. 
      * rewrite neighborC. apply: neighborUr. exact: path_neighborR.
    + apply: neighborUl. rewrite neighborC. apply: neighborUl.
      apply: path_neighborR => //; by set_tac.
    + apply: neighborUl. rewrite neighborC. apply: path_neighborR => //; by set_tac.
Qed.


Lemma K4_of_vseparators (G : sgraph) : 
  3 < #|G| -> (forall S : {set G}, vseparator S -> 2 < #|S|) -> minor G K4.
Proof.
  move => G4elt minsep3.
  case: (boolP (cliqueb [set: G])) => [|/cliquePn [x] [y] [_ _ xNy xNEy]].
  { move/cliqueP. apply: minor_of_clique. by rewrite cardsT. }
  have minsep_xy S : separates x y S -> 3 <= #|S|.
  { move => A. apply: minsep3. by exists x; exists y. }
  case: (theta xNEy xNy minsep_xy) => p ind_p.
  case: (theta_vertices p xNy xNEy) => s Hs.
  (* name [p1] and [p2] (plus assumptions) because we will need to generalize over them *)
  pose p1 := p ord1. pose p2 := p ord2.
  pose s1 := s ord1. pose s2 := s ord2.
  have ind12 : independent p1 p2 by apply: ind_p.
  have ind01 : independent (p ord0) p1 by apply: ind_p.
  have ind02 : independent (p ord0) p2 by apply: ind_p.
  have sp1 : s1 \in interior p1 by rewrite Hs.
  have sp2 : s2 \in interior p2 by rewrite Hs.
  case (@avoid_nonseperator G [set x; y] (s ord0) (s1)) => //; try (apply: interiorN; eauto).
  { move/minsep3. by rewrite cards2 xNy. }
  move => q Iq av_xy. 
  case: (@split_at_first G [predU interior p1 & interior p2] (s ord0) s1 q s1) => //.  
  { by rewrite inE /= sp1. }
  move => s1' [q1 [q2 [catp s1'p12 s1'firstp12]]].
  subst q. case/irred_catE : Iq => Iq _ _.
  have {av_xy} av_xy : [disjoint q1 & [set x; y]] by apply/disjointP => z; set_tac. 
  wlog in_p1: p1 p2 s1 s2 ind01 ind02 ind12 sp1 {sp2} {q2 s1'p12} s1'firstp12 / s1' \in interior p1.
  { move => W. case/orP: (s1'p12) => /= [s1'p1|s1'p2].
    - by apply W with p1 p2 s1.
    - apply W with p2 p1 s2 => //. by apply: independent_sym.
      move => z' H1 H2. apply s1'firstp12 => //. move: H1. by rewrite !inE orbC. }
  apply K4_of_paths with x y (s ord0) s1' (p ord0) p1 p2 q1 => //; exact: valP.
Qed.

Lemma no_K4_smallest_vseparator (G : sgraph) :
  ~ minor G K4 -> #|G| <= 3 \/ (exists S : {set G}, smallest vseparator S /\ #|S| <= 2).
Proof.
  move => HM. case (boolP (3 < #|G|)) => sizeG; last by rewrite leqNgt; left. 
  right. case: (boolP ([exists (S : {set G} | #|S| <= 2), vseparatorb S])).
  - case/exists_inP => /= S sizeS sepS. 
    case: (arg_minP (fun a : {set G} => #|a|) sepS) => U /vseparatorP sepU HU.
    exists U. repeat split => //. 
    + move => V /vseparatorP. exact: HU.
    + move: (HU S sepS) => ?. exact: leq_trans sizeS.
  - move/exists_inPn => H. exfalso. apply HM. apply K4_of_vseparators => //.
    move => S. move: (H S). rewrite unfold_in (rwP (vseparatorP _)) => H'.
    apply: contraTT. by rewrite ltnNge negbK.
Qed.

Lemma add_edge_separation (G : sgraph) V1 V2 s1 s2:
  @separation G V1 V2 -> s1 \in V1:&:V2 -> s2 \in V1:&:V2 ->
  @separation (add_edge s1 s2) V1 V2.
Proof.
  move => sep s1S s2S. split; first by move => x; apply sep.  
  move => x1 x2 x1V2 x2V1 /=. rewrite /edge_rel/= sep //=.
  apply: contraTF isT. case/orP => [] /and3P[_ /eqP ? /eqP ?]; by set_tac.
Qed.

Theorem TW2_of_K4F (G : sgraph) :
  K4_free G -> exists (T : forest) (B : T -> {set G}), sdecomp T G B /\ width B <= 3.
Proof.
  elim/card_ind : G => G Hind K4free. 
  (* Either G is small, or it has a smallest vseparator of size at most two *)
  case (no_K4_smallest_vseparator K4free) =>[|[S [ssepS Ssmall2]]].
  { exact: decomp_small. }
  move: (vseparator_separation ssepS.1) => [V1 [V2 [[sep prop] SV12]]].
  move: (prop) => [x0 [y0 [Hx0 Hy0]]]. 
  case: (ltngtP #|S| 2) Ssmall2 => // [Sless2|/eqP Ssize2] _.
  - have V1properG: #|induced V1| < #|G|.
    { rewrite card_sig. eapply card_ltnT. simpl. eauto. }
    have {x0 Hx0 y0 Hy0} V2properG: #|induced V2| < #|G|.
    { rewrite card_sig. eapply card_ltnT. simpl. eauto. }
    case: (Hind (induced V1)) => // [|T1 [B1 [sd1 w1]]]. 
      apply: subgraph_K4_free K4free; exact: induced_sub.
    case: (Hind (induced V2)) => // [|T2 [B2 [sd2 w2]]]. 
      apply: subgraph_K4_free K4free; exact: induced_sub.
    have [|T[B [sdB wB]]] := separation_decomp sd1 sd2 sep _.
      by rewrite -SV12; exact: small_clique.
    by exists T,B; split => //; apply: leq_trans wB _; rewrite geq_max w1 w2.
  - case/cards2P : Ssize2 => s1 [s2] [s1Ns2 S12]; pose G' := add_edge s1 s2.
    suff [T[B [dcB wB]]] : 
      exists (T : forest) (B : T -> {set G'}), sdecomp T G' B /\ width B <= 3.
    { exists T,B; split => //; move: dcB. 
      destruct G; apply sdecomp_subrel. exact: subrelUl. }
    have V1properG: #|@induced G' V1| < #|G|.
    { rewrite card_sig. eapply card_ltnT. simpl. eauto. }
    have {x0 Hx0 y0 Hy0} V2properG: #|@induced G' V2| < #|G|.
    { rewrite card_sig. eapply card_ltnT. simpl. eauto. }
    case: (Hind (@induced G' V1)) => // [|T1 [B1 [sd1 w1]]].
    { apply: (@add_edge_separation_excluded G s1 s2 V1 V2) => //.
      by rewrite -SV12 S12. by rewrite -SV12. }
    case: (Hind (@induced G' V2)) => // [|T2 [B2 [sd2 w2]]].
    { apply: (@add_edge_separation_excluded G s1 s2 V2 V1) => //.
      - rewrite proper_separation_symmetry //.
      - by rewrite setIC -SV12 S12.
      - by rewrite setIC -SV12. }
    have [||T [B [sdB wB]]] := @separation_decomp G' _ _ _ _ _ _ sd1 sd2 _ _.
      by apply: add_edge_separation => //; rewrite -SV12 S12 !inE eqxx.
      by rewrite -SV12 S12; apply: clique2; rewrite /edge_rel/= !eqxx s1Ns2.
    by exists T,B; split => //; apply: leq_trans wB _; rewrite geq_max w1 w2.
Qed.

Theorem excluded_minor_TW2 (G : sgraph) :
  K4_free G <-> 
  exists (T : forest) (B : T -> {set G}), sdecomp T G B /\ width B <= 3.
Proof. split => [|[T][B][]]. exact: TW2_of_K4F. exact: TW2_K4_free. Qed.


Lemma K4_free_add_edge_sep_size2 (G : sgraph) (s1 s2 : G):
  K4_free G -> smallest vseparator [set s1; s2] -> s1 != s2 -> K4_free (add_edge s1 s2).
Proof.
  move S12 : [set s1;s2] => S. move/esym in S12. move => K4free ssepS s1Ns2 K4G'.
  case: (vseparator_separation ssepS.1) => V1 [V2] [psep SV12].
  wlog [phi rmapphi HphiV1] : {K4G'} V1 V2 psep SV12 / exists2 phi : K4 -> {set add_edge s1 s2},
         minor_rmap phi & forall x : K4, phi x \subset V1.
  { move => W.  case: (@separation_K4side (add_edge s1 s2) V1 V2) => //.
    - apply: add_edge_separation psep.1 _ _; by rewrite -SV12 S12 !inE eqxx.
    - rewrite -SV12 S12. apply: clique2. by rewrite /edge_rel/= !eqxx s1Ns2. 
    - by rewrite -SV12 S12 cards2 s1Ns2. 
    - move => phi map_phi [subV1|subV2]; first by apply: (W V1 V2) => //; exists phi.
      apply: (W V2 V1) => //; rewrite 1?proper_separation_symmetry 1?setIC //.
      by exists phi. }
  apply: K4free. 
  apply: add_edge_rmap_separation_minor psep _ _ _ _ rmapphi HphiV1 => //.
  all: by rewrite -SV12.
Qed.
