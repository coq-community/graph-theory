Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect.
(* Note: ssrbool is empty and shadows Coq.ssr.ssrbool, use Coq.ssrbool for "Find" *)

Require Import edone finite_quotient preliminaries set_tac.
Require Import digraph sgraph minor menger.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs". 

(** * Separators *)

Ltac notHyp b ::= assert_fails (assert b by assumption).

(** TODO: using clauses to speed up make quick *)

Arguments separatesP [G x y U].

Section Separators.
Variable (G : sgraph).
Implicit Types (x y z u v : G) (S U V : {set G}).

Fact separates_sym x y U : separates x y U <-> separates y x U.
Proof.
  wlog suff: x y / separates x y U -> separates y x U by firstorder.
  move => [xU yU H] //. rewrite /separates; split => // p.
  move: (H (prev p)) => [z zpp zU]. exists z; by try rewrite mem_prev in zpp.
Qed.

Lemma separatesNE x y U :
  x \notin U -> y \notin U -> ~ separates x y U -> connect (restrict [predC U] edge_rel) x y.
Proof.
  move => xU yU /(introN separatesP). rewrite /separatesb xU yU !negb_and //= negb_forall.
  case: (altP (x =P y)) => [<-|xDy H]; first by rewrite connect0.
  apply/uPathRP => //. case/existsP : H => p Hp. exists p => //. exact: ivalP.
  by rewrite -disjoint_subset disjoint_exists.
Qed.

Definition separator U := exists x y, separates x y U.

Lemma separatorNE U x y : ~ separator U -> ~ separates x y U.
Proof. move => nsepU sepU. by apply nsepU; exists x; exists y. Qed.

Lemma sseparator_connected S : 
  smallest separator S -> 0 < #|S| -> connected [set: G].
Proof.
  move => SS gt0 x y _ _.
  have: (connect (restrict [predC set0] sedge) x y).
  { apply (@separatesNE x y set0); rewrite ?inE => //. rewrite -(@cards0 G) in gt0. 
    move: (below_smallest SS gt0). exact: separatorNE. }
  rewrite !restrictE //; intro; rewrite !inE //.
Qed.

(** separators do not make precises what the separated comonents are,
i.e., a separator can disconnect the graph into more than two
components. Hence, we also define separations, which make the
separated sides explicit *)
Definition separation V1 V2 := 
  ((forall x, x \in V1 :|: V2) * (forall x1 x2, x1 \notin V2 -> x2 \notin V1 -> x1 -- x2 = false))%type.

Lemma sep_inR x V1 V2 : separation V1 V2 -> x \notin V1 -> x \in V2.
Proof. move => sepV. by case/setUP : (sepV.1 x) => ->. Qed.

Lemma sep_inL x V1 V2 : separation V1 V2 -> x \notin V2 -> x \in V1.
Proof. move => sepV. by case/setUP : (sepV.1 x) => ->. Qed.

Definition proper_separation V1 V2 := separation V1 V2 /\ exists x y, x \notin V2 /\ y \notin V1.

Lemma separate_nonadjacent x y : x != y -> ~~ x -- y -> proper_separation [set~ x] [set~ y].
Proof.
  move => xDy xNy. split; last by exists y; exists x; rewrite !inE !eqxx.
  split => [z | x1 x2].
  - rewrite !inE -negb_and. by apply: contraNN xDy => /andP[/eqP->/eqP->].
  - rewrite !inE !negbK sg_sym => /eqP-> /eqP->. by rewrite (negbTE xNy).
Qed.

Lemma separation_separates x y V1 V2:
  separation V1 V2 -> x \notin V2 -> y \notin V1 -> separates x y (V1 :&: V2).
Proof.
  move => sepV Hx Hy. split; rewrite ?inE ?negb_and ?Hx ?Hy //. 
  move => p.
  case: (@split_at_first G (mem V2) x y p y) => // ; rewrite ?(sep_inR sepV) //.
  move => z [p1 [p2 [H1 H2 H3]]]. rewrite inE in H2. 
  exists z; rewrite ?H1 !inE ?H2 // andbT.
  case: (@splitR G x z p1) => [|z0 [p1' [z0z H4]]]. 
  { by apply: contraTneq H2 => <-. }
  apply: contraTT (z0z) => Hz1. rewrite sepV ?inE //.
  apply: contraTN (z0z) => H0. by rewrite [z0]H3 ?sgP // H4 !inE.
Qed.

Lemma proper_separator V1 V2 :
  proper_separation V1 V2 -> separator (V1 :&: V2).
Proof.
  case => Hsep [x] [y] [Hx Hy]. exists x. exists y. exact: separation_separates. 
Qed.

Lemma separator_separation S : 
  separator S -> exists V1 V2, proper_separation V1 V2 /\ S = V1 :&: V2.
Proof.
  case => x1 [x2] [S1 S2 P12].
  set U := locked [set x | connect (restrict [predC S] sedge) x1 x].
  set V1 := U :|: S. set V2 := ~: U. exists V1; exists V2.
  have D : x1 != x2.
  { apply/negP => /eqP A. subst x2. case: (P12 (idp x1)) => ?.
    rewrite mem_idp => /eqP-> ?. contrab. }
  have HU x : x \in U -> x \notin S.
  { rewrite /U -lock inE srestrict_sym. case/connectP => [[/= _ <- //|/= y p]].
    rewrite inE /=. by case: (x \in S). }
  split; first split; first split.
  - move => x. rewrite !inE. by case: (x \in U).
  - move => u v. rewrite !inE !(negb_or,negb_and,negbK) => [Hu] /andP [Hv1 Hv2].
    apply: contraNF Hv1 => uv. move: (Hu). rewrite /U -lock !inE => H.
    apply: connect_trans H _. apply: connect1. by rewrite /= !inE HU.
  - exists x1; exists x2; split.
    + suff H: (x1 \in U) by rewrite !inE H.
      by rewrite /U -lock inE connect0.
    + rewrite !inE negb_or S2 (_ : x2 \notin U = true) //.
      apply: contraTN isT. rewrite /U -lock inE => /uPathRP.
      case => [//|p Ip /subsetP subS].
      case: (P12 p) => z /subS. rewrite inE /= => *. contrab.
  - apply/setP => x. rewrite !inE. case E: (x \in U) => //=.
    by rewrite (negbTE (HU _ _)).
Qed.

Definition separatorb U := [exists x, exists y, separatesb x y U].

Lemma separatorP U : reflect (separator U) (separatorb U).
Proof. rewrite /separator /separatorb.
  apply: (iffP existsP).
  - move => [x /existsP [y /separatesP H]]. exists x; exists y; done.
  - move => [x [y H]]. exists x. apply /existsP. exists y. by apply /separatesP.
Qed.

Lemma minimal_separation x y : x != y -> ~~ x -- y -> 
  exists V1 V2, proper_separation V1 V2 /\ smallest separator (V1 :&: V2).
Proof.
  move => xDy xNy. 
  move/proper_separator/separatorP : (separate_nonadjacent xDy xNy) => sep.
  case (ex_smallest (fun S => #|S|) sep) => U /separatorP sepU HU {sep xDy xNy}.
  move: (separator_separation sepU) => [V1 [V2 [ps UV]]].
  exists V1; exists V2. repeat split => //; rewrite -UV // => V /separatorP. exact: HU.
Qed.

Lemma separation_sym V1 V2 : separation V1 V2 <-> separation V2 V1.
Proof.
  wlog suff W : V1 V2 / separation V1 V2 -> separation V2 V1. { split; exact: W. }
  move => sepV. split => [x|x1 x2 A B]; by rewrite 1?setUC 1?sgP sepV. 
Qed.

Lemma proper_separation_symmetry V1 V2 :
  proper_separation V1 V2 <-> proper_separation V2 V1.
Proof. rewrite /proper_separation separation_sym. by firstorder. Qed.

Lemma sseparator_neighbours V1 V2 s : 
  proper_separation V1 V2 -> smallest separator (V1 :&: V2) -> 
  s \in V1 :&: V2 -> exists x1 x2, [/\ x1 \notin V2, x2 \notin V1, s -- x1 & s -- x2].
Proof.
  wlog: V1 V2 / [forall x1, (x1 \notin V2) ==> ~~ s -- x1].
  { move => H ps ss sS.
    case (boolP [forall x1, (x1 \notin V2) ==> ~~ s -- x1]).
    - move => HH. apply (H V1 V2) => //.
    - move => /forall_inPn [x1 x1V /negPn sx1].
      case (boolP [forall x, (x \notin V1) ==> ~~ s -- x]).
      + move => HH. rewrite setIC in sS ss. case (H V2 V1) => //.
        * by apply proper_separation_symmetry.
        * move => y [z [? ? ? ?]]. exists z; exists y. split; done.
      + move => /forall_inPn [x2 x2V sx2].
        exists x1; exists x2. split => //; by apply negbNE. }
  move => /forall_inP Hwlog [sepV [x1] [x2] [x1V12  x2V21]] smallS sS.
  pose S' := V1 :&: V2:\ s. 
  suff: separator S'.
  - move => sS'. case: (below_smallest (V := S') smallS) => //. 
    by rewrite /S' (cardsD1 s (V1 :&: V2)) sS. 
  - (* cant use [separator S], because the two vertices could be both in V2 *)
    exists x1; exists x2. split; try by rewrite /S' notinD.
    + move => p.
      case: (@split_at_first G (mem V2) x1 x2 p x2) => //.
      { by rewrite (sep_inR sepV x2V21). }
      move => z [p1 [p2 [H1 H2 H3]]]. rewrite inE in H2. 
      exists z; first by rewrite H1 !inE. 
      case: (@splitR G x1 z p1).
      { apply: contraTN isT => /eqP ?. subst x1; contrab. }
      move => z0 [p' [z0z Hp']].
      have z0V1: z0 \notin V2. 
      { apply: contraTN (z0z) => ?. by rewrite [z0]H3 ?sgP // Hp' !inE. }
      rewrite !inE H2 andbT. apply/andP; split.
      * apply: contraTN (z0z) => /eqP->. by rewrite sgP Hwlog.
      * apply: contraTT (z0z) => ?. by rewrite sepV.
Qed.

(** Note: This generalizes the corresponding lemma on checkpoints *)
Lemma avoid_nonseperator U x y : ~ separator U -> x \notin U -> y \notin U -> 
  exists2 p : Path x y, irred p & [disjoint p & U].
Proof.
  move => nsep_u xU yU. 
  case: (altP (x =P y)) => [?|A];first subst y.
  - exists (idp x); first exact: irred_idp. 
    rewrite (@eq_disjoint1 _ x) // => y. by rewrite mem_idp.
  - have/separatesNE/uPathRP : ~ separates x y U by apply separatorNE.
    case => // p irr_p. rewrite -disjoint_subset. by exists p.
Qed.

Lemma sseparator_uniq x y S:
  smallest separator S -> separates x y S -> S != set0 ->
  exists2 p : Path x y, irred p & exists! z, z \in p /\ z \in S.
Proof.
  (* Since [S != set0], [G] is connected. Assunme every path needs to
  visit at least two distinct vertices fro [S]. Thus, there exists a
  vertex in [S], say [s], such that every xy-path through [s] must
  vist another node. Then [S :\ s] separates [x] and [y],
  contradiction. *)
Admitted.


Lemma separation_connected_same_component V1 V2:
  separation V1 V2 -> forall x0 x, x0 \notin V2 ->
  connect (restrict [predC (V1:&:V2)] sedge) x0 x -> x \notin V2.
Proof.
  set S := V1 :&: V2.
  move => sepV x0 x x0NV2.
  case: (boolP (x0==x)) => [/eqP ? | x0x]; first by subst x0.
  move => /(PathRP x0x) [p /subsetP Hp].
  case: (boolP(x \in V2)) => // xV2.
  case: (@split_at_first G (mem V2) x0 x p x) => //.
    move => z [p1 [p2 [H1 H2 H3]]]. rewrite inE /= in H2.
  case: (altP (x0 =P z)) => ?; first by subst x0; contrab.
  case: (@splitR G x0 z p1) => [|z0 [p1' [z0z H4]]] //.
  apply: contraTT (z0z) => _. rewrite sepV //.
  + apply: contraTN (z0z) => z0V2. by rewrite [z0]H3 ?sgP // H4 !inE.
  + have ? : (z \notin S) by apply: Hp; rewrite H1 !inE. by subst S; set_tac.
Qed.

End Separators.


Prenex Implicits separator.
Implicit Types G H : sgraph.

Arguments sdecomp : clear implicits.
Arguments rename_decomp [T G H D]. 

(** TODO: This proof should become simpler there was a join-lemma
without intermediate node *)
Lemma separation_decomp G (V1 V2 : {set G}) T1 T2 B1 B2 :
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
      case/setUP : (sepV.1 v) => Hv; by [exists (inl (Sub v Hv))|exists (inr (Sub v Hv))].
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
    suff iso: sg_iso G' G.
    + case: (sg_iso_decomp dec12 iso) => B' sdecB' wB'B.
      exists T; exists B'. split => //. by rewrite wB'B join_width.
    + suff HH: V2 = ~:V1.
      { rewrite /G' HH. apply ssplit_disconnected. move => x y xV1 yNV1.
        rewrite (sepV.2 x y) => //. by rewrite HH inE xV1. }
      apply/setP => z. rewrite inE. case: (boolP (z \in V1)) => Hz.
      * apply: contraNF clique0 => H. apply/card_gt0P. exists z. by set_tac.
      * apply: contraTT (sepV.1 z). by set_tac.
Qed.

Lemma connectedI_clique (G : sgraph) (A B S : {set G}) :
  connected A -> clique S -> 
  (forall x y (p : Path x y), p \subset A -> x \in B -> y \notin B -> 
     exists2 z, z \in p & z \in S :&: B) ->
  connected (A :&: B).
Proof.
  move => conA clS H x y /setIP [X1 X2] /setIP [Y1 Y2].
  case: (altP (x =P y)) => [->|xDy]; first exact: connect0.
  case/uPathRP : (conA _ _ X1 Y1) => // p Ip subA. 
  case: (boolP (p \subset B)) => subB.
  - apply connectRI with p => z zp. by clean_mem;set_tac.
  - case/subsetPn : subB => z Z1 Z2. 
    gen have C,Cx : x y p Ip subA X1 X2 Y1 Y2 Z1 Z2 {xDy} / 
        exists2 s, s \in S :&: A :&: B & connect (restrict (mem (A :&: B)) sedge) x s.
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
    case/uPathRP : (P2 i x y xpi ypi); first by apply: contraNneq yV1 => <-.
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

Lemma subsetIlP1 (T : finType) (A B : pred T) x : 
  reflect (forall y, y \in A -> y \in B -> y = x) ([predI A & B] \subset pred1 x).
Proof.
  apply: (iffP subsetP) => [H y H1 H2|H y /andP [/= H1 H2]]. 
  - by rewrite [y](eqP (H _ _ )) ?inE ?H1 ?H2.
  - by rewrite inE [y]H.
Qed.
Arguments subsetIlP1 [T A B x].

Lemma predIpcatR (G : sgraph) (x y z : G) (p : Path x y) (q : Path y z) (S A : pred G) : 
  [predI pcat p q & S] \subset A -> [predI q & S] \subset A.
Proof. 
  move/subsetP => H. apply/subsetP => u /andP [/= H1 H2]. 
  apply: H. by rewrite !inE H1 H2.
Qed.

Lemma connected_interiorR (G : sgraph) (x y : G) (p : Path x y) : 
  irred p -> connected (y |: interior p).
Proof.
  move => Ip. case: (set_0Vmem (interior p)) => [->|[z Hz]]. 
  - rewrite setU0. exact: connected1.
  - apply: neighbor_connected; [exact: connected1|exact: connected_interior|].
    apply: path_neighborR => //; by set_tac. 
Qed.

Lemma neighbor_interiorL (G : sgraph) (x y : G) (p : Path x y) :
  x != y -> irred p -> neighbor [set x] (y |: interior p).
Proof.
  move => xDy Ip. case: (set_0Vmem (interior p)) => [E|[z Hz]]. 
  - apply: neighborUl. apply/neighborP; exists x; exists y. 
    case: (interior0E xDy Ip E) => xy _. split => //; by rewrite inE eqxx.
  - apply: neighborUr. apply: path_neighborL => //; by set_tac. 
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
    (** Hints for automation *)
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


Lemma K4_of_separators (G : sgraph) : 
  3 < #|G| -> (forall S : {set G}, separator S -> 2 < #|S|) -> minor G K4.
Proof.
  move => G4elt minsep3.
  case: (boolP (cliqueb [set: G])) => [|/cliquePn [x] [y] [_ _ xNy xNEy]].
  { move/cliqueP. apply: minor_of_clique. by rewrite cardsT. }
  have minsep_xy S : separates x y S -> 3 <= #|S|.
  { move => A. apply: minsep3. by exists x; exists y. }
  case: (theta xNEy xNy minsep_xy) => p ind_p.
  case: (theta_vertices p xNy xNEy) => s Hs.
  (** name [p1] and [p2] (plus assumptions) because we will need to generalize over them *)
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

Lemma no_K4_smallest_separator (G : sgraph) :
  ~ minor G K4 -> #|G| <= 3 \/ (exists S : {set G}, smallest separator S /\ #|S| <= 2).
Proof.
  move => HM. case (boolP (3 < #|G|)) => sizeG; last by rewrite leqNgt; left. 
  right. case: (boolP ([exists (S : {set G} | #|S| <= 2), separatorb S])).
  - case/exists_inP => /= S sizeS sepS. 
    case (@ex_smallest _ (@separatorb G) (fun a => #|a|) S sepS) => U /separatorP sepU HU.
    exists U. repeat split => //. 
    + move => V /separatorP. exact: HU.
    + move: (HU S sepS) => ?. exact: leq_trans sizeS.
  - move/exists_inPn => H. exfalso. apply HM. apply K4_of_separators => //.
    move => S. move: (H S). rewrite unfold_in (rwP (separatorP _)) => H'.
    apply: contraTT. by rewrite ltnNge negbK.
Qed.

Lemma rmap_disjE (G H : sgraph) (phi : H -> {set G}) x i j :
  minor_rmap phi -> x \in phi i -> x \in phi j -> i=j.
Proof.
  move => [_ _ map _] xi. apply contraTeq => iNj. 
  by erewrite (disjointFr (map _ _ iNj)).
Qed.


(** If [minor (add_edge s1 s2) K4] but [K4_free G], then the
additional edge must be used eihter to connect two different
inflations or ensure connectedness of one of the inflations *)
Lemma cases_without_edge (G : sgraph) (s1 s2 : G) phi:
  K4_free G -> (@minor_rmap (add_edge s1 s2) K4 phi) ->
  (exists i j, [/\ s1 \in phi i, s2 \in phi j & i != j]) \/
  exists i, [/\ s1 \in phi i, s2 \in phi i & ~ @connected G (phi i)].
Proof.
  move => K4F_G phi_map.
  case (boolP ([exists i, s1 \in phi i] && [exists j, s2 \in phi j])).
  - (* s1 and s2 appear in some bags *)
    move => /andP [/existsP [i s1i] /existsP [j s2j]]. 
    case (altP (i=Pj)) => [?|]; last by move => ?; left; exists i; exists j.
    (* s1 s2 in same bag *)
    subst j. case (boolP (@connectedb G (phi i))).
    + (* [phi i] connected without using [s1 -- s2], so find minor *)
      have disjE := rmap_disjE phi_map.
      case: phi_map => [map0 map1 map2 map3].
      move/connectedP => coni.
      suff H: @minor_rmap G K4 phi by case: K4F_G; exact: minor_of_rmap H.
      split => //.
      * move => x. case: (altP (x =P i)) => [->//|xNi].
        apply add_edge_keep_connected_l with s1 s2 => //.
        apply: contraNN xNi => ?. by rewrite (disjE s1 x i). 
      * move => i' j' i'j'.  wlog H : i' j' i'j' / j' != i. 
        { move => W. case: (altP (j' =P i)) => [E|]; last by apply: W.
          rewrite neighborC W 1?sgP //. apply: contraTneq i'j' => ->. 
          by rewrite E sgP. }
        apply: neighbor_del_edgeR (map3 _ _ i'j'); 
        apply: contraNN H => H; by rewrite ?(disjE _ _ _ s1i H) ?(disjE _ _ _ s2j H).
    + (* bag not connected *)
      move/connectedP => nconi. right. by exists i. 
  - (* either s1 or s2 is not in any bag *) (* so find minor *)
    rewrite negb_and !negb_exists => H.
    suff HH: @minor_rmap G K4 phi by case: K4F_G; exact: minor_of_rmap HH.
    wlog H : s1 s2 phi phi_map {H} / forall x, s1 \notin phi x.
    { move => W. case/orP : H => /forallP; first exact: W.
      apply: (W s2 s1). exact: rmap_add_edge_sym. }
    case: phi_map => [map0 map1 map2 map3]; split => //.    
    + move => x. exact: add_edge_keep_connected_l. 
    + move => i j ij. exact: neighbor_del_edge1 (map3 _ _ ij).
Qed.


Lemma add_edge_separation (G : sgraph) V1 V2 s1 s2:
  @separation G V1 V2 -> s1 \in V1:&:V2 -> s2 \in V1:&:V2 ->
  @separation (add_edge s1 s2) V1 V2.
Proof.
  move => sep s1S s2S. split; first by move => x; apply sep.  
  move => x1 x2 x1V2 x2V1 /=. rewrite /edge_rel/= sep //=.
  apply: contraTF isT. case/orP => [] /and3P[_ /eqP ? /eqP ?]; by set_tac.
Qed.

(** TODO: simplify below ... *)

Definition component_in G (A : {set G}) s :=
    [set z in A | connect (restrict (mem A) sedge) s z].

Lemma add_edge_split_connected (G :sgraph) (s1 s2 : G) (A : {set G}):
    connected (A : {set add_edge s1 s2}) -> s1 \in A -> s2 \in A ->
    forall (x : G), x \in A -> x \in component_in A s1 \/ x \in component_in A s2.
Proof. 
  move => conA s1A s2A x xA. case: (altP (s1 =P x)) => [->|s1Nx].
  { left. by rewrite inE connect0. }
  case/PathRP: (conA s1 x s1A xA) => // p subA. 
  case: (@split_at_last (@add_edge G s1 s2) (mem [set s1; s2]) s1 x p s1); 
    try by rewrite ?inE ?eqxx.
  move => z [p1 [p2 [catp zS Hlast]]].
  suff HH: x \in component_in A z.
  { case/setUP : zS => /set1P <-; rewrite HH; by auto. } 
  case: (@lift_Path_on _ _ (fun (v : G) => (v : add_edge s1 s2)) z x p2 ) => //.
  - move => u v up vp /=. case/or3P => //.
    + case/and3P => [E /eqP ? /eqP ?]; subst. 
      by rewrite [s1]Hlast 1?[s2]Hlast ?inE ?eqxx in E. 
    + case/and3P => [E /eqP ? /eqP ?]; subst. 
      by rewrite [s1]Hlast 1?[s2]Hlast ?inE ?eqxx in E.
  - move => a ap1. rewrite mem_map // mem_enum //.
  - move => p3 t1 _. rewrite inE xA. apply connectRI with p3 => a. 
    rewrite mem_path -[_ p3]map_id t1 -(mem_path p2). 
    (* TODO: this should be autmatable *)
    subst. move => H. apply: (subsetP subA). exact: (subsetP (subset_pcatR _ _)).
Qed.

Lemma add_edge_split_disjoint (G :sgraph) (s1 s2 : G) (A : {set add_edge s1 s2}):
    connected A -> s1 \in A -> s2 \in A -> ~ @connected G A ->
    [disjoint (component_in (A : {set G}) s1) & (component_in (A : {set G}) s2)].
Proof. 
  move => conA s1A s2A nconA. apply /disjointP => z.
  rewrite !inE => /andP [_ ps1z] /andP [_ ps2z].
  apply nconA. move => a b ai bi.
  have cons1s2: @connect G (@restrict G (mem A) sedge) s1 s2.
  { rewrite srestrict_sym in ps2z. apply connect_trans with z => //. }
  case: (add_edge_split_connected conA s1A s2A bi); rewrite inE => /andP [_ bC];
    [apply connect_trans with s1 |apply connect_trans with s2] => //; rewrite srestrict_sym.
  all: case: (add_edge_split_connected conA s1A s2A ai);
    rewrite inE => /andP [_ aC];
    [apply connect_trans with s1|apply connect_trans with s2] => //=.
  by rewrite srestrict_sym.
Qed.

(* This lemma is the core of the construction of tree decompositions
for K4-free graphs. *)

Lemma K4_free_add_edge_sep_size2 (G : sgraph) (s1 s2 : G):
  K4_free G -> smallest separator [set s1; s2] -> s1 != s2 -> K4_free (add_edge s1 s2).
Proof.
  move S12 : [set s1;s2] => S. move/esym in S12. move => K4free ssepS s1Ns2 K4G'.
  case: (separator_separation ssepS.1) => V1 [V2] [psep SV12].
  wlog [phi rmapphi HphiV1] : {K4G'} V1 V2 psep SV12 / exists2 phi : K4 -> {set add_edge s1 s2},
         minor_rmap phi & forall x : K4, phi x \subset V1.
  { move => W.  case: (@separation_K4side (add_edge s1 s2) V1 V2) => //.
    - apply: add_edge_separation psep.1 _ _; by rewrite -SV12 S12 !inE eqxx.
    - rewrite -SV12 S12. apply: clique2. by rewrite /edge_rel/= !eqxx s1Ns2. 
    - by rewrite -SV12 S12 cards2 s1Ns2. 
    - move => phi map_phi [subV1|subV2]; first by apply: (W V1 V2) => //; exists phi.
      apply: (W V2 V1) => //; rewrite 1?proper_separation_symmetry 1?setIC //.
      by exists phi. }
  apply K4free. rewrite SV12 in S12.
  (* case A :  s1 and s2 in different bags 
     we generalize over s1,s2 and phi, so that case B reduces to this case. *)
  gen have caseA: s1 s2 s1Ns2 S12 phi rmapphi HphiV1 /
    (exists i j : K4, [/\ s1 \in phi i, s2 \in phi j & i != j]) -> minor G K4.
  { move => [i [j [s1i s2j iNj]]]. rewrite SV12 in ssepS.
    (* s1 as a neighbour [z \notin V1] *)
    case: (@sseparator_neighbours _ _ _ s1 psep ssepS) => [|_ [z [_ zNV1 _ s1z]]].
    { by rewrite S12 !inE eqxx. }
    (* path from z to s2 avoiding s1 *)
    have [p irp dis] : exists2 p : Path z s2, irred p & [disjoint p & [set s1]].
    { apply: (@avoid_nonseperator G [set s1] z s2).
      - apply: below_smallest ssepS _. by rewrite S12 cards1 cards2 s1Ns2. 
      - by rewrite inE eq_sym ?(sg_edgeNeq s1z). 
      - by rewrite inE eq_sym. }
    rewrite disjoint_sym disjoints1 in dis.
    (* path included in V2 *)
    have pV2: p \subset V2. 
    { apply: contraTT isT => /subsetPn [z' z'p z'NV2].
      case/psplitP: _ / z'p irp dis => {p} [p1 p2] /irred_catE [_ _ Ip] s1p.
      move/proper_separation_symmetry in psep.
      case: (separation_separates psep.1 zNV1 z'NV2) => _ _ /(_ p1) [s S1 S2].
      rewrite -(Ip s2) // in z'NV2; by set_tac. }
    (* phi' := phi[j := phi j :|: p] *)
    pose phi' (k : K4) := if k==j then phi j :|: [set a in p] else phi k .
    suff HH: @minor_rmap G K4 phi' by apply: minor_of_rmap HH.
    have disjE := (rmap_disjE rmapphi).
    destruct rmapphi as [map0 map1 map2 map3].
    rewrite /phi'. split => [x|x|x y xNy|x y xy].
    + case: (altP (x =P j)) => xj //=. apply /set0Pn. exists s2. by rewrite !inE.
    + case: (altP (x =P j)) => xj.
      * apply connectedU_common_point with s2 => //. by rewrite !inE.
        -- apply add_edge_keep_connected_l => //. 
           apply: contraNN iNj => s1x. by rewrite (disjE s1 i j s1i s1x). 
        -- by apply connected_path.
      * apply (@add_edge_keep_connected_l G s2 s1) => //. (* TODO: _r variant *)
        -- by apply add_edge_connected_sym. 
        -- apply: contraNN xj => s1x. by rewrite (disjE s2 x j s1x s2j).
    + wlog yNj: x y xNy / y!=j.
      { move => H. case: (boolP (y==j)) => yj //=.
        - rewrite eq_sym in xNy. case: (altP (x=Pj)) => xj //=.
          + subst x. contrab.
          + move: (H y x xNy xj). rewrite (negbTE xj) yj => ?. by rewrite disjoint_sym.
        - move: (H x y xNy yj). by rewrite (negbTE yj). }
      rewrite (negbTE yNj). case: (altP (x=Pj)) => ? //=; [ subst x | by apply map2].
      rewrite disjointsU ?map2 //. apply /disjointP => a ap ay. rewrite inE in ap.
      have/setU1P[H|H] : a \in [set s1; s2] by move: (HphiV1 y); set_tac.
      - by subst; contrab.
      - move: (map2 _ _ xNy). by set_tac.
    + wlog yNj: x y xy / y!=j.
      { move => H. case: (boolP (y==j)) => yj //=.
        - simpl in xy. rewrite /edge_rel/= eq_sym in xy. case: (altP (x =P j)) => xj //=.
          + subst x. contrab.
          + move: (H y x xy xj). by rewrite (negbTE xj) yj neighborC. 
        - move: (H x y xy yj). by rewrite (negbTE yj). }
      rewrite (negbTE yNj). case: (altP (x =P j)) => xj.
      * subst x. case: (altP (y =P i)) => yi.
        -- subst y. apply/neighborP; exists z. exists s1. split => //; by rewrite ?inE // sgP.
        -- apply: (neighborW G (phi j) (phi y)); rewrite ?subsetUl //.
           move: (map2 _ _ yi) (map2 _ _ yNj) => *.
           apply: neighbor_del_edgeR (map3 _ _ xy); by set_tac.
      * move: (map2 _ _ xj) (map2 _ _ yNj) => *. 
        apply: neighbor_del_edge2 (map3 _ _ xy); by set_tac. }

  case: (cases_without_edge K4free rmapphi) => [twobags|onebag].
  -  apply caseA with s1 s2 phi => //. 

  - (* case B, s1 and s2 in same bag, not connected *)
    move: onebag => [i [s1i s2i notconi]].
    have disjE := (rmap_disjE rmapphi).
    case: (rmapphi) => [_ map1 _ _].

    (* [phi i] = [component of s1] U [component of s2] *)
    move C_def : (component_in ((phi i) : {set G})) => C.
    have I4inC12: phi i \subset C s1 :|: C s2.
    { apply/subsetP. rewrite -C_def => ? ?. apply/setUP.
      by apply (add_edge_split_connected (map1 i) s1i s2i). }
    have C1inphii: (C s1 : {set (add_edge s1 s2)}) \subset phi i.
    { rewrite -C_def /component_in setIdE. apply subsetIl. }
    have C2inphii: (C s2 : {set (add_edge s1 s2)}) \subset phi i.
    { rewrite -C_def /component_in setIdE. apply subsetIl. }
    have disC1C2: [disjoint (C s1) & (C s2)].
    { rewrite -C_def.
      apply (add_edge_split_disjoint (map1 i) s1i s2i notconi). }
    have conC1: @connected G (C s1).
    { rewrite -C_def. apply connected_restrict_in => //. }
    have conC2: @connected G (C s2).
    { rewrite -C_def. apply connected_restrict_in => //. }
    have/andP [s1C s2C] : (s1 \in C s1) && (s2 \in C s2).
    { by rewrite -C_def !inE s1i s2i !connect0. }

    wlog [B1|B2]: s1 s2 s1Ns2 s1C s2C phi rmapphi {map1} HphiV1 s1i s2i notconi disjE C_def 
      I4inC12 C1inphii C2inphii S12 caseA disC1C2 conC1 conC2 / 
      (forall j, j != i -> neighbor (C s1) (phi j)) \/ 
      ( let G' := add_edge s1 s2 in 
        exists j, [/\ j != i, @neighbor G' (C s2) (phi j) & forall k, k \notin pred2 i j -> @neighbor G' (C s1) (phi k)]).
    { move => W. pose G' := add_edge s1 s2.
      Notation NB G A B := (@neighbor G A B).
      have s2Ns1 : s2 != s1 by rewrite eq_sym.
      have rmapphi' := rmap_add_edge_sym rmapphi.
      have I4inC21: phi i \subset C s2 :|: C s1. by rewrite setUC.
      have disC2C1 : [disjoint C s2 & C s1] by rewrite disjoint_sym.
      have S21 : V1 :&: V2 = [set s2; s1] by rewrite setUC.
      case: (rmapphi) => {map1} [map0 map1 map2 map3].
      have iP z : z != i -> (s1 \in phi z = false)*(s2 \in phi z = false).
      { move => Hz. by rewrite !(disjointFl (map2 _ _ Hz)). }
      case (boolP [forall (j | j != i), NB G' (C s1) (phi j)]) => [|C1].
      { move/forall_inP => H. apply: (W s1 s2) => //. 
        left => j Hj. move/H : (Hj). apply: neighbor_del_edgeR; by rewrite !iP. }
      case (boolP [forall (j | j != i), NB G' (C s2) (phi j)]) => [|C2].
      { move/forall_inP => H. apply (W s2 s1 s2Ns1 s2C s1C phi) => //. 
        left => j Hj. move/H : (Hj). apply: neighbor_del_edgeR; by rewrite !iP. }
      case/forall_inPn : C1 => j2 Dj2 Nj2. 
      case/forall_inPn : C2 => j1 Dj1 Nj1. rewrite !unfold_in in Dj1 Dj2.

      have NC A  : neighbor A (phi i) -> @neighbor G' (C s1) A || @neighbor G' (C s2) A.
      { rewrite ![_ _ A] neighborC. exact: neighbor_split.  }
      have j1Dj2 : j1 != j2. 
      { apply: contraNneq Nj2 => ?;subst j2.
        move/NC : (map3  _ _ Dj2). by rewrite (negbTE Nj1) orbF. }
      have {Nj2} Nj2 : NB G' (C s2) (phi j2).
      { move/NC : (map3  _ _ Dj2). by rewrite (negbTE Nj2). }
      have {Nj1} Nj1 : NB G' (C s1) (phi j1).
      { move/NC : (map3  _ _ Dj1). by rewrite (negbTE Nj1) orbF. }
      have [k Hk] : exists k, k \notin [:: i; j1;j2] by apply: ord_fresh.
      move: Hk. rewrite !inE !negb_or => /and3P[Hk1 Hk2 Hk3]. 
      have zP z : z \in [:: k;j1;j2;i]. 
      { by apply: ord_size_enum; rewrite //= !inE !negb_or Hk1 Hk2 Hk3 Dj1 Dj2 j1Dj2. }
      case/NC/orP : (map3  _ _ Hk1) => [Ks1|Ks2].
      - apply: (W s1 s2) => //.
        right; exists j2. 
        split => // z. rewrite !inE negb_or => /andP[Z1 Z2]. move: (zP z). 
        rewrite !inE (negbTE Z1) (negbTE Z2) /= orbF. by case/orP=>/eqP->.
      - apply: (W s2 s1) => //. exact: rmapphi'. 
        right. exists j1. rewrite neighbor_add_edgeC.
        split => // z. rewrite !inE negb_or => /andP[Z1 Z2]. move: (zP z). 
        rewrite !inE (negbTE Z1) (negbTE Z2) /= orbF. 
        case/orP=>/eqP-> //; by rewrite neighbor_add_edgeC. }  
    + (* case x1 x2 x3 in same component (wlog component of s1) *)
      pose phi' (k : K4) := if k==i then C s1 else phi k .
      suff HH: @minor_rmap G K4 phi' by apply (minor_of_map (minor_map_rmap HH)).
      case: rmapphi => [map0 map1 map2 map3].
      rewrite /phi'. split => [x|x|x y xNy|x y xy].
      * case: (boolP (x==i)) => xi //=. apply/set0Pn; by exists s1.
      * case: (boolP (x==i)) => xi //=. 
        apply: (@add_edge_keep_connected_l G s2 s1) => //.
        -- rewrite add_edge_connected_sym. apply: map1.
        -- apply: contraNN xi => s1x. by rewrite (disjE s2 x i s1x s2i).
      * have disC1y: forall y, i!=y -> [disjoint C s1 & (phi y : {set G})].
        { move => y' y'Ni. apply: disjoint_transL (map2 _ _ y'Ni). 
          rewrite -C_def /component_in setIdE. exact: subsetIl. }
        case: (altP (x =P i)) => xNi //=; try subst x;
        case: (altP (y =P i)) => yNi //=; try subst y.
        -- by rewrite eqxx in xNy.
        -- by apply disC1y.
        -- rewrite disjoint_sym. apply disC1y. by rewrite eq_sym.
        -- by apply map2.
      * wlog yNj: x y xy / y!=i.
        { move => H. case: (boolP (y==i)) => yi //=.
          - rewrite sg_sym in xy. case: (altP (x =P i)) => xj //=.
            + subst x. by rewrite (sg_edgeNeq xy) in yi. 
            + move: (H y x xy xj). rewrite (negbTE xj) yi. by rewrite neighborC.
          - move: (H x y xy yi). by rewrite (negbTE yi). }
        rewrite (negbTE yNj). case: (altP (x =P i)) => xi //=; first exact: B1.
        apply neighbor_del_edge1 with s1 s2.
        -- by rewrite (disjointFl (map2 _ _ xi)).
        -- by rewrite (disjointFl (map2 _ _ yNj)).
        -- exact: map3.
    + (* case x1 x2 x3 in different components (wlog C1 C1 C2) *)
      Notation conn G A := (@connected G A).
      case: B2 => j [jNi NCs2Pj NCs1Pk].
      case: rmapphi => [map0 map1 map2 map3].
      pose phi' (k : K4) := if k==i then C s1 else 
                            if k==j then phi j :|: C s2 else phi k.
      have C1V1: C s1 \subset V1 by apply: subset_trans (HphiV1 i). 
      have C2V1: C s2 \subset V1 by apply: subset_trans (HphiV1 i).
      suff rmapphi' : @minor_rmap (add_edge s1 s2) K4 phi'.
      { apply caseA with s1 s2 phi' => //.
        * rewrite /phi' => x. case: (boolP (x==i)) => xi //=.
          case: (boolP (x==j)) => xl //=. by apply/subUsetP. 
        * rewrite /phi'. exists i. exists j. rewrite (negbTE jNi) !eqxx.
          by rewrite eq_sym jNi in_setU s1C s2C. }
      rewrite /phi'. split => [x|x|x y xNy|x y xy].
      * case: (boolP (x==i)) => xi; [|case: (boolP (x==j)) => xj //].
        -- apply/set0Pn; by exists s1. 
        -- apply/set0Pn. exists s2. by rewrite inE s2C. 
      * case: (boolP (x==i)) => xi => //; case:(boolP (x==j)) => xj //;
          try by apply add_edge_connected.
        rewrite setUC. apply: neighbor_connected => //. exact: add_edge_connected.
      * clear C1V1 C2V1.
        do ! match goal with 
             | |- is_true [disjoint _ (C s1) & _ (C s2)] => done
             | |- context[ if ?x == ?y then _ else _] => case: (altP (x =P y)) => [?|?]; try subst x
             | H : is_true (?x != ?x) |- _ => by rewrite eqxx in H
             | |- is_true [disjoint _ (_ :|: _) & _] => apply disjointsU
             | |- is_true [disjoint _ & _ (_ :|: _)] => rewrite disjoint_sym; apply disjointsU
             | |- is_true [disjoint _ (C s2) & _ (C s1)] => by rewrite disjoint_sym
             | |- is_true [disjoint _ (C _) & _ (phi _)] => 
                 apply disjoint_transL with (mem (phi i)) => //
             | |- is_true [disjoint _ (phi _) & _ (C _)] => 
                 apply disjoint_transR with (mem (phi i)) => //
             end. 
        all: apply: map2 => //; by rewrite eq_sym.
      * rewrite /= in xy.
        wlog yNj : x y xy / y != j; last rewrite (negbTE yNj).
        { move => W. case: {-}_ / (altP (y =P j)) => [E|H]; last exact: W.
          by rewrite neighborC W // -?E // /edge_rel/= eq_sym. }
        case:(altP (x =P i)) => xi. 
        { rewrite eq_sym -xi (negbTE xy). apply NCs1Pk.
          by rewrite inE (negbTE yNj) -xi eq_sym (negbTE xy). }
        case:(altP (x =P j)) => xj. 
        { subst x. case: (altP (y =P i)) => [E|yNi].
          - rewrite neighborC. apply: neighborUr. 
            apply/neighborP; exists s1; exists s2. by rewrite s1C s2C /edge_rel /= s1Ns2 !eqxx.
          - rewrite neighborC. apply: neighborUl. exact: map3. }
        case:(altP (y =P i)) => yi; last exact: map3.
        by rewrite neighborC NCs1Pk // inE (negbTE xi) (negbTE xj).
Qed.



Theorem TW2_of_K4F (G : sgraph) :
  K4_free G -> exists (T : forest) (B : T -> {set G}), sdecomp T G B /\ width B <= 3.
Proof.
  move: G. apply: (nat_size_ind (f := fun G => #|G|)) => G Hind K4free. 
  (* Either G is small, or it has a smallest separator of size at most two *)
  case (no_K4_smallest_separator K4free) =>[|[S [ssepS Ssmall2]]].
  { move => Gsmall. exists tunit. exists (fun _ => [set: G]). split.
    + exact (triv_sdecomp G).
    + apply leq_trans with #|G| => //. apply width_bound. }
  move: (separator_separation ssepS.1) => [V1 [V2 [[sep prop] SV12]]].
  move: (prop) => [x0 [y0 [Hx0 Hy0]]]. 
  have V1properG: #|induced V1| < #|G|.
  { rewrite card_sig. eapply card_ltnT. simpl. eauto. }
  have {x0 Hx0 y0 Hy0} V2properG: #|induced V2| < #|G|.
  { rewrite card_sig. eapply card_ltnT. simpl. eauto. }
  wlog C : G S Hind K4free {ssepS Ssmall2} V1 V2 sep {prop} SV12 V1properG V2properG
         / clique (V1 :&: V2).
  { move => W. case: (ltngtP #|S| 2) Ssmall2 => // [Sless2|/eqP Ssize2] _.
   - apply W with S V1 V2 => //. 
     rewrite -SV12. exact: small_clique.
   - case/cards2P : Ssize2 => s1 [s2] [s1Ns2 S12].
     case (W (add_edge s1 s2)) with S V1 V2 => // {W}.
     + rewrite S12 in ssepS. exact: K4_free_add_edge_sep_size2 ssepS s1Ns2.
     + apply add_edge_separation => //; by rewrite -SV12 S12 !inE eqxx.
     + rewrite -SV12 S12. apply (@clique2 (add_edge s1 s2)) => /=.
       by rewrite /edge_rel/= !eqxx s1Ns2.
     + move => T [B] [B1 B2]. exists T. exists B. split => //. move: B1. 
      destruct G; apply sdecomp_subrel. exact: subrelUl. }
  case: (Hind (induced V1)) => // [|T1 [B1 [sd1 w1]]].
  { apply: subgraph_K4_free K4free. exact: induced_sub. }
  case: (Hind (induced V2)) => // [|T2 [B2 [sd2 w2]]].
  { apply: subgraph_K4_free K4free. exact: induced_sub. } 
  case separation_decomp with G V1 V2 T1 T2 B1 B2 => // T [B [sd w]].
  exists T. exists B. split => //. 
  apply leq_trans with (maxn (width B1) (width B2)) => //.
  by rewrite geq_max w1 w2.  
Qed.
