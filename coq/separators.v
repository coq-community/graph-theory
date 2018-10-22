Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect.
(* Note: ssrbool is empty and shadows Coq.ssr.ssrbool, use Coq.ssrbool for "Find" *)

Require Import edone finite_quotient preliminaries sgraph minor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs". 

(** * Separators *)

(** Preliminaries *)


Definition inE := (inE,mem_pcat,path_begin,path_end,mem_prev).

Section Separators.
Variable (G : sgraph).
Implicit Types (x y z u v : G) (S U V : {set G}).

Definition separates x y U := [/\ x \notin U, y \notin U & forall p : Path x y, exists2 z, z \in p & z \in U].

(** Standard trick to show decidability: quantify only over irredundant paths *)
Definition separatesb x y U := [&& x \notin U, y \notin U & [forall p : IPath x y, exists z in p, z \in U]].

Lemma separatesP x y U : reflect (separates x y U) (separatesb x y U).
Proof. 
  apply: (iffP and3P) => [[? ? A]|[? ? A]]; split => //.
  - move => p. case: (uncycle p) => p' sub_p Ip'. 
    move/forallP/(_ (Build_IPath Ip')) : A. 
    case/exists_inP => z Z1 Z2. exists z => //. exact: sub_p.
  - apply/forallP => p. by move/exists_inP : (A p). 
Qed.
Arguments separatesP [x y U].

Fact separatesNeq x y U : separates x y U -> x != y.
Proof. 
  case => Hx _ Hp. apply: contraNN Hx => /eqP C. subst y. case: (Hp (idp x)).
  move => ?. by rewrite mem_idp => /eqP->. 
Qed.

Fact separates_sym x y U : separates x y U <-> separates y x U.
Proof.
  wlog suff: x y / separates x y U -> separates y x U by firstorder.
  move => [xU yU H] //. rewrite /separates; split => // p.
  move: (H (prev p)) => [z zpp zU]. exists z; by try rewrite mem_prev in zpp.
Qed.

Fact separates0P x y : reflect (separates x y set0) (~~ connect sedge x y).
Proof.
  apply:(iffP idP) => [nconn_xy|]. 
  - rewrite /separates !inE. split => // p. by rewrite Path_connect in nconn_xy.
  - case => _ _ H. apply/negP. case/uPathP => p _. case: (H p) => z. by rewrite inE.
Qed.

Lemma separatesNE x y U : 
  x \notin U -> y \notin U -> ~ separates x y U -> connect (restrict [predC U] sedge) x y.
Proof.
  move => xU yU /(introN separatesP). rewrite /separatesb xU yU !negb_and //= negb_forall.
  case: (altP (x =P y)) => [<-|xDy H]; first by rewrite connect0.
  apply/uPathRP => //. case/existsP : H => p Hp. exists p => //. exact: ivalP. 
  by rewrite -disjoint_subset disjoint_exists. 
Qed.

Definition separator U := exists x y, separates x y U.

Lemma sseparator_connected S : 
  smallest separator S -> 0 < #|S| -> connected [set: G].
Proof.
  case => SS H cSgt0 x y _ _.
  have: (connect (restrict [predC set0] sedge) x y).
  { apply (@separatesNE x y set0); rewrite ?inE => //.
    intro. apply (H set0). rewrite cards0 //. exists x. exists y. done. }
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
  move: (separate_nonadjacent xDy xNy) => /proper_separator /separatorP sep.
  case (ex_smallest (fun S => #|S|) sep) => U /separatorP sepU HU {sep xDy xNy}.
  move: (separator_separation sepU) => [V1 [V2 [ps UV]]].
  exists V1; exists V2. repeat split => //; rewrite -UV // => V. 
  apply: contraTnot => /separatorP H. by rewrite -leqNgt HU.
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
  rewrite /smallest.
  move => /forall_inP Hwlog [sepV [x1] [x2] [x1V12  x2V21]] [sepS smallS] sS.
  pose S' := V1 :&: V2:\ s. suff: separator S'.
  - move => sS'. exfalso. move: sS'. apply smallS.
    rewrite /S'. rewrite (cardsD1 s (V1 :&: V2)) sS //=.
  - (* cant use [separator S], because the two vertices could be both in V2 *)
    exists x1; exists x2. split.
    + by rewrite /S' !inE !negb_and x1V12. 
    + by rewrite /S' !inE !negb_and x2V21.
    + move => p.
      case: (@split_at_first G (mem V2) x1 x2 p x2) => //.
      { by rewrite (sep_inR sepV x2V21). }
      move => z [p1 [p2 [H1 H2 H3]]]. rewrite inE in H2. 
      exists z; first by rewrite H1 !inE. 
      case: (@splitR G x1 z p1).
      { apply: contraTN isT => /eqP ?. subst x1; contrab. }
      move => z0 [p' [z0z Hp']].
      have z0V1: z0 \notin V2. 
      { move: (sg_edgeNeq z0z) => zz0. apply: contraFN zz0 => ?.
        apply /eqP. apply H3 => //. by rewrite Hp' !inE. }
      rewrite !inE H2 andbT. apply/andP; split.
      * move: (z0z) => /prev_edge_proof zz0. (* TODO: simplify *)
        apply: contraTN zz0 => /eqP->. by rewrite Hwlog // !inE z0V1 (sep_inL sepV).
      * apply: contraTT (z0z) => ?. by rewrite sepV.
Qed.

(* TOTHINK: This definition really only makes sense for irredundant paths *)
Definition independent x y (p q : Path x y) := 
  forall z, z \in p -> z \in q -> z = x \/ z = y.

Lemma independent_sym x y (p q : Path x y):
  independent p q -> independent q p.
Proof. move => ipq z zq zp. by case: (ipq z zp zq) => H; auto. Qed.


Definition left_independent x y y' (p : Path x y) (q : Path x y') := 
  forall z, z \in p -> z \in q -> z = x.

Lemma left_independent_sym (x y y' : G) (p : Path x y) (q : Path x y') :
  left_independent p q -> left_independent q p.
Proof. move => H z A B. exact: H. Qed.

Lemma separatorNE U x y : ~ separator U -> ~ separates x y U.
Proof. move => nsepU sepU. by apply nsepU; exists x; exists y. Qed.

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
  case (boolP (x0 == z)) => [/eqP ?|?]; first by subst x0; contrab.
  case: (@splitR G x0 z p1) => [|z0 [p1' [z0z H4]]] //.
  apply: contraTT (z0z) => _. rewrite sepV //. 
  + have: z0==z = false by rewrite sg_edgeNeq. apply: contraFT => z0V2.
    rewrite negbK in z0V2. apply /eqP. apply H3; first by rewrite !inE z0V2. 
    by rewrite H4 mem_pcat path_end.
  + have zNS: z \in [predC S]. { apply Hp. by rewrite H1 mem_pcat path_end. }
    move: (sepV.1 z) => zV12.
    rewrite /S !inE !negb_and /= in zV12 zNS. 
    move: zV12 zNS => /orP [zV1 | zV2] /orP [zNV1 | zNV2] //; contrab.
Qed.

End Separators.

Prenex Implicits separator.
Implicit Types G H : sgraph.

Arguments sdecomp : clear implicits.

Lemma separation_decomp G (V1 V2 : {set G}) T1 T2 B1 B2 :
  @sdecomp T1 (induced V1) B1 -> @sdecomp T2 (induced V2) B2 -> 
  separation V1 V2 -> clique (V1 :&: V2) ->
  exists T B, @sdecomp T G B /\ width B <= maxn (width B1) (width B2).
Proof.
  move => dec1 dec2 sepV subV.
  have dec12 := join_decomp dec1 dec2. set G' := sjoin _ _ in dec12.
  pose h (x : G') : G := match x with inl x => val x | inr x => val x end.
Admitted.

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
  - apply connectRI with p => z zp. 
    by rewrite !inE (subsetP subA) ?(subsetP subB).
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

Lemma separation_K4side G (V1 V2 : {set G}) s1 s2 : 
  separation V1 V2 -> V1 :&: V2 = [set s1; s2] -> s1 -- s2 -> 
  minor G K4 -> 
  exists2 phi : K4 -> {set G}, minor_rmap phi & 
     (forall x, phi x \subset V1) \/ (forall x, phi x \subset V2).
Proof.
  move def_S : (V1 :&: V2) => S. (* pose C1 := V1 :\: V2; pose C2 := V2 :\: V1. *)
  move => sepV HS s12 /minorRE [phi] [P1 P2 P3 P4].
  wlog/forallP cutV1 : V1 V2 sepV def_S / [forall x, phi x :&: V1 != set0].
  { move => W. 
    case: (boolP [forall x, phi x :&: V1 != set0]) => A; first exact: (W V1 V2).
    case: (boolP [forall x, phi x :&: V2 != set0]) => B. 
    - case: (W V2 V1) => //; rewrite 1?separation_sym 1?setIC //. 
      move => phi' ? [?|?]; by exists phi'; auto.
    - case: notF. 
      case/forallPn : A => i /negPn Hi. 
      case/forallPn : B => j /negPn Hj.
      case: (altP (i =P j)) => [E|E].
      + subst j. case/set0Pn : (P1 i) => x Hx. case/setUP : (sepV.1 x) => Hx'.
        move/eqP/setP/(_ x) : Hi. by rewrite !inE Hx Hx'.
        move/eqP/setP/(_ x) : Hj. by rewrite !inE Hx Hx'.
      + move: (P4 i j E) => [x] [y] [A B]. rewrite sgP sepV //.
        apply: contraTN Hj => Hy. by apply/set0Pn; exists y; rewrite inE B.
        apply: contraTN Hi => Hx. by apply/set0Pn; exists x; rewrite inE A. }
  have phiP i y : y \in phi i -> y \notin V1 -> phi i :&: S != set0.
  { case/set0Pn : (cutV1 i) => x /setIP [xpi xV1 ypi yV1].
    case: (boolP (x \in V2)) => xV2; first by apply/set0Pn; exists x; rewrite -def_S !inE.
    case/uPathRP : (P2 i x y xpi ypi); first by apply: contraNneq yV1 => <-.
    move => p Ip subP. 
    have [_ _ /(_ p)] := separation_separates sepV xV2 yV1. rewrite def_S.
    case => z /(subsetP subP) => ? ?. by apply/set0Pn; exists z; rewrite !inE. }
  pose phi' (i : K4) := phi i :&: V1.
  exists phi'; first split.
  - move => i. by case/cutV1 : (i). 
  - move => i. apply connectedI_clique with S.
    + exact: P2.
    + rewrite HS. exact: clique2.
    + move => x y p sub_phi Hx Hy. case: (boolP (x \in V2)) => Hx'.
      * exists x => //. by rewrite -def_S !inE Hx.
      * have/(_ x y Hx' Hy) [_ _ /(_ p) [z]] := (separation_separates sepV).
        rewrite def_S => X1 X2. exists z => //. 
        by rewrite setIC -def_S setIA setIid def_S.
  - move => i j /P3 => D. apply: disjointW D; exact: subsetIl.
  - move => i j ij. move/P4: (ij) => [x] [y] [H1 H2 H3]. 
    have S_link u v : u \in S -> v \in S -> u \in phi i -> v \in phi j -> u -- v.
    { have D: [disjoint phi i & phi j]. apply: P3. by rewrite sg_edgeNeq. 
      rewrite HS !inE => /orP[] /eqP -> /orP[] /eqP -> // upi vpj; 
        solve [by rewrite (disjointFr D upi) in vpj|by  rewrite sgP]. }
    have/subsetP subV : S \subset V1 by rewrite -def_S subsetIl.
    have inS u v : u -- v -> u \in V1 -> v \notin V1 -> u \in S.
    { move => uv HVu HVv. rewrite -def_S !inE HVu /=. 
      apply: contraTT uv => /= C. by rewrite sepV. }
    case: (boolP (x \in V1)) => HVx; case: (boolP (y \in V1)) => HVy.
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

Lemma sseparator_path G (S : {set G}) x s : 
  smallest separator S -> x \notin S -> s \in S -> 
  exists2 p : Path x s, irred p & [predI p & S] \subset pred1 s.
Proof.
  move => ssepS. case: (ssepS) => sepS smallS xS sS. 
  have nSs : ~ separator (S :\ s). 
  { apply: smallS. by rewrite [in X in _ < X](cardsD1 s) sS. }
  case: (@avoid_nonseperator _ _ x s nSs _ _) => [||p irr_p dis_p]; 
    rewrite ?inE ?eqxx ?(negbTE xS) //.
  exists p => //. apply/subsetP => z. rewrite !inE => /andP [Y1 Y2].
  apply: contraTT dis_p => H. apply: disjointNI Y1 _. exact/setD1P.
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

Lemma independent_paths_aux G S (s1 s2 s3 :G) x0 : 
  smallest separator S -> x0 \notin S ->
  s1 != s2 -> s2 != s3 -> s3 != s1 -> s1 \in S -> s2 \in S -> s3 \in S ->
  exists x (p1 : Path x s1) (p2 : Path x s2) (p3 : Path x s3),
    [/\ irred p1, irred p2 & irred p3] /\
    [/\ [predI p1 & S] \subset pred1 s1, [predI p2 & S] \subset pred1 s2 & [predI p3 & S] \subset pred1 s3] /\ 
    [/\ connect (restrict [predC S] sedge) x0 x, 
       left_independent p1 p2, left_independent p2 p3 & left_independent p3 p1].
Proof.
  move => ssepS H0 D1 D2 D3 S1 S2 S3. 
  case: (sseparator_path ssepS H0 S1) => p1 I1 P1.
  case: (sseparator_path ssepS H0 S2) => p2 I2 P2.
  case: (sseparator_path ssepS H0 S3) => p3 I3 P3.
  case: (split_at_last (A := [predU p2 & p3]) _ (path_begin p1)).
  { by rewrite inE /= path_begin. }
  move => x [p11] [p12] [P11 P12 P13].
  wlog P12 : s2 s3 S2 S3 D1 D2 D3 p2 p3 P2 I2 P3 I3 {P12} P13 / x \in p2.
  { move => W. case/orP : P12 => /= in_p2; first exact: (W _ _ _ _ _ _ _ p2 p3). 
    case: (W _ _ _ _ _ _ _ p3 p2) => //; try by rewrite eq_sym.
    - move => z. move: (P13 z). by rewrite !inE orbC.
    - move => x' [p1'] [p2'] [p3'] [[? ? ?] [[? ? ?] [? ? ? ?]]]. 
      exists x'; exists p1'; exists p3'; exists p2'. do ! split => //; exact: left_independent_sym. }
  case: (split_at_last (A := mem p2) _ (path_begin p3)) => [|]; 
    first exact: path_begin.
  move => y [p31] [p32] [P31 P32 P33].
  have {P33} P33 z' : z' \in [predU p2 & p12] -> z' \in p32 -> z' = y.
  { case/orP. exact: P33. rewrite inE => A B. 
    have E : z' = x by rewrite [z']P13 ?inE ?P31 ?inE ?B //.
    subst z'. by rewrite [x]P33 //. }
  have {P13} P13 z' : z' \in [predU p2 & p32] -> z' \in p12 -> z' = x.
  { case/orP => [/= A|/= A];apply: P13 => //; by rewrite inE /= P31 ?inE A. }
  rewrite -[y \in mem p2]/(y \in p2) in P32. (* ugly *) (* rewrite inE in P32. ?*)
  subst p1; subst p3. 
  case/irred_catE : I1 => _ I1 _. case/irred_catE : I3 => _ I3 _.
  move/predIpcatR : P1 => P1. move/predIpcatR : P3 => P3. 
  have xS : x \notin S. 
  { apply: contraNN D1 => xS.
    by rewrite -(subsetIlP1 P2 x) // -(subsetIlP1 P1 x) // path_begin. }
  have yS : y \notin S. 
  { apply: contraNN D2 => yS. 
    by rewrite -(subsetIlP1 P2 y) // -(subsetIlP1 P3 y) // path_begin. }
  clear p31 p11.
  case: (altP (x =P y)) => [?|xDy].
  - subst y. 
    case/(isplitP I2) def_p2 : _  / P12 => [p21 p22 _ I22 I2'].
    subst p2. 
    exists x. exists p12. exists p22. exists p32. do 3 split => //. 
    + exact: predIpcatR P2.
    + apply: (connectRI (p := p21)) => z. rewrite !inE => Z1. 
      apply: contraNN xS => zS. 
      suff? : z = s2 by subst z; rewrite -(I2' s2).
      by apply:(subsetIlP1 P2) => //; rewrite !inE Z1. 
    + move => z Z1 Z2; by rewrite [z]P13 // !inE Z2.
    + move => z Z1 Z2; by rewrite [z]P33 // !inE Z1.
    + move => z Z1 Z2. by rewrite [z]P33 // !inE Z2. 
  - wlog {xDy} Hxy : x y xS yS P12 P32 s1 s3 S1 S3 D1 D2 D3 p12 p32 I1 I3 P13 P33 P1 P3 / x <[p2] y. 
    { move => W. case: (ltngtP (idx p2 x) (idx p2 y)) => H.
      - exact: (W _ _ _ _ _ _ _ _ _ _ _ _ _ p12 p32).
      - case: (W _ _ _ _ _ _ _ _ _ _ _ _ _ p32 p12) => //; try by rewrite eq_sym.
        move => x' [p1'] [p2'] [p3'] [[? ? ?] [[? ? ?] [? ? ? ?]]]. 
        exists x'; exists p3'; exists p2'; exists p1'. do ! split => //; exact: left_independent_sym. 
      - move/idx_inj : H. rewrite nodesE -mem_path P12 => /(_ isT) E. 
        by rewrite E eqxx in xDy. }
    case: (three_way_split I2 P12 P32 Hxy) => p21 [p22] [p23] [def_p2 Hx Hy].
    subst p2. case/irred_catE : I2 => _ I2 I2'. case/irred_catE : I2 => I22 I23 I2.
    exists y. exists (pcat (prev p22) (p12)). exists p23. exists p32. repeat split => //.
    + rewrite irred_cat irred_rev I1 I22 /=. apply/eqP/setP => z.
      rewrite !inE. apply/andP/eqP => [[A B]|-> //]. by rewrite [z]P13 // !inE A.
    + apply/subsetIlP1 => z. rewrite !inE => /orP [A|A] B; last exact: (subsetIlP1 P1).
      have ? : z = s2. by apply: (subsetIlP1 P2); rewrite // !inE A. subst z.
      apply: contraNeq yS => _. by rewrite -(I2 s2).
    + move/predIpcatR : P2 => P2. exact : predIpcatR P2.
    + apply: (connectRI (p := pcat p21 p22)) => z; rewrite !inE => Z1.
      apply: contraNN yS => zS. 
      have ? : z = s2. apply: (subsetIlP1 P2) => //. by rewrite -pcatA !inE Z1. subst.
      case/orP : Z1 => Z1; first by rewrite [s2]I2' // in zS; contrab.
      by rewrite [s2]I2 // in zS.
    + move => z. rewrite !inE => /orP [|A B]; first exact: I2. 
      have E: x = z by rewrite [z]P13 ?inE ?B. subst z. by rewrite [x]I2.
    + move => z Z1 Z2. by rewrite [z]P33 ?inE ?Z1.
    + move => z Z1. rewrite !inE => /orP [Z2|Z2]; first by rewrite [z]P33 ?inE ?Z2.
      have E: z = x by apply: P13; rewrite ?inE ?Z1. subst.
      by apply: P33 => //; rewrite ?inE.
Qed.

Lemma path_touch_separation G (x : G) (S V1 V2 : {set G}) (s1 : G) (pxs1 : Path x s1):
  S = V1 :&: V2 -> s1 \in S -> irred pxs1 ->
  (forall y : G, y \in pxs1 -> y \in S -> y = s1) -> x \notin V2 ->
  separation V1 V2 -> {subset pxs1 <= V1}.
Proof.
  move => HS s1S ir subset xNV2 sepV.
  case: (@splitR G x s1 pxs1). 
  { apply: contraTneq s1S => <-. by rewrite HS !inE negb_and xNV2. }
  move => z [pxz [zs1 pcat1]].
  move: (ir) => irc. rewrite pcat1 irred_edgeR in irc. case/andP: irc => [s1pxz _].
  rewrite pcat1. move => x1. rewrite mem_pcatT. move => /orP [x1p | xs1].
  - rewrite (sep_inL sepV) //.
    case (boolP (x == x1)) => [/eqP ?|?]; first by subst.
    apply separation_connected_same_component with V1 x => //.
    case /psplitP pcat2: _/x1p => [pxx1 px1z]. 
    apply connectRI with pxx1. rewrite -HS => x2 x2pxx1. 
    apply: contraNN s1pxz => /= x2S. 
    by rewrite -(subset x2) // !(pcat2,pcat1) !inE x2pxx1.
  - rewrite !inE in xs1. rewrite (eqP xs1). 
    move: s1S. rewrite HS inE. by case/andP.
Qed.

Lemma independent_paths G (V1 V2 : {set G}) : 
  proper_separation V1 V2 -> smallest separator (V1 :&: V2) -> 3 <= #|V1 :&: V2| ->
  exists x1 x2 (p1 p2 p3 : Path x1 x2), 
    [/\ irred p1, irred p2 & irred p3] /\
    [/\(exists2 s1, s1 \in p1 & s1 \in V1 :&: V2),
       (exists2 s2, s2 \in p2 & s2 \in V1 :&: V2)&
       (exists2 s3, s3 \in p3 & s3 \in V1 :&: V2)] /\
    [/\ x1 \notin V2, x2 \notin V1, independent p1 p2, independent p2 p3 & independent p3 p1].
Proof.
  set S := V1 :&: V2.
  move => propsep ssS /card_gt2P [s1 [s2 [s3 [[s1S s2S s3S] [Ns12 Ns23 Ns31]]]]].
  move: (propsep) => [[V12G nedgeC12] [x0 [y0 [x0NV2 y0NV1]]]].
  case: (@independent_paths_aux G S s1 s2 s3 x0) => //=. 
  { by rewrite /S !inE negb_and x0NV2. }
  move => x [pxs1 [pxs2 [pxs3 [[irx1 irx2 irx3] 
    [[/subsetIlP1 px1Ss1 /subsetIlP1 px2Ss2 /subsetIlP1 px3Ss3]
    [connx0x ind_pxs1pxs2 ind_pxs2pxs3 ind_pxs3pxs1]]]]]].
  case: (@independent_paths_aux G S s1 s2 s3 y0) => //=. 
  { by rewrite /S !inE negb_and y0NV1. }
  move => y [pys1 [pys2 [pys3 [[iry1 iry2 iry3] 
    [[/subsetIlP1 py1Ss1 /subsetIlP1 py2Ss2 /subsetIlP1 py3Ss3]
    [conny0y ind_pys1pys2 ind_pys2pys3 ind_pys3pys1]]]]]].
  set p1 := pcat pxs1 (prev pys1).
  set p2 := pcat pxs2 (prev pys2).
  set p3 := pcat pxs3 (prev pys3).
  exists x; exists y; exists p1; exists p2; exists p3.

  have S21: S = V2 :&: V1 by rewrite setIC.
  have sep21: separation V2 V1 by apply/separation_sym.
  have xNV2: x \notin V2 by apply separation_connected_same_component with V1 x0.
  have yNV1: y \notin V1.
  { apply separation_connected_same_component with V2 y0 => //. by rewrite -S21. }
  have pxs1V1: {subset pxs1 <= V1}. { apply path_touch_separation with S V2 => //. }
  have pxs2V1: {subset pxs2 <= V1}. { apply path_touch_separation with S V2 => //. }
  have pxs3V1: {subset pxs3 <= V1}. { apply path_touch_separation with S V2 => //. }
  have pys1V2: {subset pys1 <= V2}. { apply path_touch_separation with S V1 => //. }
  have pys2V2: {subset pys2 <= V2}. { apply path_touch_separation with S V1 => //. }
  have pys3V2: {subset pys3 <= V2}. { apply path_touch_separation with S V1 => //. }

  gen have irredpi: s1 pxs1 pys1 {ind_pys1pys2 ind_pys3pys1 p1 py1Ss1
      ind_pxs1pxs2 ind_pxs3pxs1 s1S Ns12 Ns31} px1Ss1 irx1 iry1 pxs1V1 pys1V2
    / irred (pcat pxs1 (prev pys1)).
  { rewrite irred_cat. apply /and3P; split => //; first by rewrite irred_rev.
    apply /eqP /setP => z. rewrite inE mem_prev in_set1.
    apply Bool.eq_true_iff_eq; split. (* ugly *)
    * move => /andP [zpxs1 /pys1V2 zV2]. move: (zpxs1) => /pxs1V1 zV1.
      apply /eqP. apply (px1Ss1 z); rewrite /S ?inE //=.
    * move => /eqP->. apply /andP; split; apply path_end.
  }
  gen have indep: s1 s2 pxs1 pys1 pxs2 pys2
      {Ns23 Ns31 iry2 ind_pys2pys3 irx2 ind_pxs2pxs3 iry1 ind_pys3pys1 irx1 ind_pxs3pxs1 p1 p2}
      ind_pxs1pxs2 ind_pys1pys2 pxs1V1 pxs2V1 pys1V2 pys2V2 Ns12 s2S s1S px1Ss1 px2Ss2 py1Ss1 py2Ss2
      / independent (pcat pxs1 (prev pys1)) (pcat pxs2 (prev pys2)).
  { move => z. rewrite !mem_pcat !mem_prev.
    move => /orP [zpxs1 | zpys1] /orP [zpxs2 | zpys2].
    + left. by apply ind_pxs1pxs2.
    + exfalso. move: Ns12 => /eqP; apply.
      move: (pxs1V1 z zpxs1) (pys2V2 z zpys2) => zV1 zV2.
      rewrite -(px1Ss1 z) ?inE //.
      rewrite -(py2Ss2 z) ?inE //.
    + exfalso. move: Ns12 => /eqP; apply.
      move: (pxs2V1 z zpxs2) (pys1V2 z zpys1) => zV1 zV2.
      rewrite -(px2Ss2 z) ?inE //.
      rewrite -(py1Ss1 z) ?inE //.
    + right. by apply ind_pys1pys2.
  }

  split; [|split].
  - (* irred *) split; by apply irredpi.
  - (* si \in p & si \in S *) split; [exists s1|exists s2|exists s3] => //; by rewrite !inE.
  - (* x/y \notin V2/V1 + independent *) split => //; by apply indep.
Qed.


Lemma K4_of_complete_graph (G : sgraph) : 
  3 < #|G| -> (forall x y : G, x!=y -> x--y) -> minor G K4.
Proof.
  case/card_gtnP => [sq [uniqsq sq4elt sqG]].
  destruct sq as [|g0 [|g1 [|g2 [|g3 [|g4 q]]]]]; simpl in sq4elt => //=.
  clear sq4elt. move => H.
  pose phi (i : K4) := match i with
                | Ordinal 0 _ => [set g0]
                | Ordinal 1 _ => [set g1]
                | Ordinal 2 _ => [set g2]
                | Ordinal 3 _ => [set g3]
                | Ordinal p n => set0
                end.
  suff HH: minor_rmap phi by apply (minor_of_map (minor_map_rmap HH)).
  move: uniqsq => /and5P  [g0i g1i g2i _ _].
  rewrite !(inE,negb_or) in g0i g1i g2i.
  move: g0i g1i g2i => /and3P [g01 g02 g03] /andP [g12 g13] g23.
  split.
  - move => [m i]. case m as [|[|[|[|m]]]] => //=; apply /set0Pn;
    by (eexists; rewrite inE).
  - move => [m i]. case m as [|[|[|[|m]]]] => //=; by (apply connected1).
  - move => [m i] [m' i']. 
    case m as [|[|[|[|m]]]] => //=;
    case m' as [|[|[|[|m']]]] => //= _; by rewrite disjoints1 !inE // eq_sym.
  - move => [m i] [m' i']. case m as [|[|[|[|m]]]] => //=;
    case m' as [|[|[|[|m']]]] => //= _.
    all: eexists; eexists; split; solve [by rewrite inE | by apply H; rewrite // eq_sym].
Qed.


Lemma K4_of_separators (G : sgraph) : 
  3 < #|G| -> (forall S : {set G}, separator S -> 2 < #|S|) -> minor G K4.
Proof.
  move => G4elt minsep3.
  case: (boolP [forall x : G, forall (y |x!=y), (x--y)]).
  { move/forallP => H. apply K4_of_complete_graph => // x. exact/forall_inP. }
  move => /forallPn [x /forall_inPn [y xNy xNEy]]. rewrite unfold_in in xNy.
  move: (minimal_separation xNy xNEy) => [V1 [V2 [[sepV propV] [sS HS]]]].
  set S := V1 :&: V2. rewrite -/S in HS sS.
  move: (minsep3 S sS) => S3elt. clear x y xNy xNEy.
  case: (@independent_paths _ V1 V2) => // => x [y [p1 [p2 [p3 [[ir1 ir2 ir3]
    [[[s1 s1p1 s1S] [s2 s2p2 s2S] [s3 s3p3 s3S]] [xNV2 yNV1 ind12 ind23 ind31]]]]]]].
  have temp: forall s, s \in S -> s!=x /\ s!=y.
  { move => s sS2. rewrite /S inE in sS2. move: sS2 => /andP [? ?].
    split; apply: contraTN isT => /eqP ?; subst s; contrab. }
  move: (temp s1 s1S) (temp s2 s2S) => [s1Nx s1Ny] [s2Nx s2Ny]. clear temp.
  have xNy: x!=y. { apply: contraTN isT => /eqP ?; subst x.
    move: (sepV.1 y). rewrite inE. move => /orP [?|?]; contrab. }
  case (@avoid_nonseperator G [set x; y] s1 s2) => //.
    { apply HS. rewrite cards2. rewrite xNy. exact S3elt. }
    { by rewrite !inE negb_or s1Nx s1Ny. }
    { by rewrite !inE negb_or s2Nx s2Ny. }
  move => p irp dispxy.
  case: (@split_at_first G (predU (mem p2) (mem p3)) s1 s2 p s2) => //; first by rewrite !inE s2p2.
  move => s2' [p' [p'' [catp s2'p23 s2'firstp23]]].

  wlog s2'p2: p2 p3 {s3p3 s2p2} ir2 ir3 s2'firstp23 ind12 ind23 ind31 s2'p23 / (s2' \in p2).
  { rewrite inE /= in s2'p23. move: (s2'p23) => /orP [s2'p2|s2'p3].
    - apply. exact ir2. exact ir3. all:eauto.
    - apply. exact ir3. exact ir2. 2-4: apply independent_sym; eauto.
      + move => z' H1 H2. apply s2'firstp23. rewrite inE /= in H1.
        move: H1 => /orP [H1|H1]; by rewrite !inE /= H1. done.
      + by rewrite !inE /= s2'p3.
      + done.
  }

  case: (splitR p3 xNy) => [y3 [p3' [y3y catp3]]].
  case: (splitL p2 xNy) => [x2 [xx2 [p2' [catp2' _]]]].
  case: (splitL p1 xNy) => [x1 [xx1 [p1' [catp1' _]]]].
  case: (@splitR G x1 y p1') => //.
  { apply: contraTN (xx1) => /eqP ?. subst x1. rewrite sepV.2 => //=. }
  move => y1 [p1'' [y1y catp1'']].
  case: (@splitR G x2 y p2') => //.
  { apply: contraTN (xx2) => /eqP ?. subst x2. rewrite sepV.2 => //=. }
  move => y2 [p2'' [y2y catp2'']].
  case: (@splitR G s1 s2' p') => //.
  { apply: contraTN isT => /eqP ?. subst s2'.
    move: (ind12 s1 s1p1 s2'p2) => [/eqP aa|/eqP bb]; contrab. }
  move => s' [ps1s' [s's2' catps1s']].

  set M1 := [set y].
  set M2 := [set z in p3'].
  set M3 := [set z in p2''].
  set M4 := [set z in p1''] :|: [set z in ps1s'].

  pose phi (i : K4) := match i with
                  | Ordinal 0 _ => M1
                  | Ordinal 1 _ => M2
                  | Ordinal 2 _ => M3
                  | Ordinal 3 _ => M4
                  | Ordinal p n => set0
                  end.
  suff HH: minor_rmap phi by apply (minor_of_map (minor_map_rmap HH)).

  have s2'M3: s2' \in M3. 
  { rewrite !inE. rewrite catp2' catp2'' in s2'p2.
    rewrite -mem_prev prev_cat mem_pcatT mem_prev mem_pcatT !inE in s2'p2.
    have temp: s2' \in p by rewrite catp inE path_end.
    move: (disjointFr dispxy temp). rewrite !inE. move => /negbT temp2.
    rewrite negb_or in temp2. move: temp2 => /andP [? ?].
    case/orP: s2'p2 => [/orP [?|?]|?] => //=; contrab. }

  have irrE := (irred_edgeL,irred_edgeR,irred_cat).

  (* only used in the have: below *)
  have ?: y \notin p3'. { apply: contraTN ir3 => C. by subst; rewrite !irrE C. }
  have ?: y \notin p1''. { apply: contraTN ir1 => C. by subst; rewrite !irrE C. }
  have ?: y \notin p2''. { apply: contraTN ir2 => C. by subst; rewrite !irrE C. }
  have N1: y \notin ps1s'.
  { suff: (y \notin p). { apply: contraNN. by subst; rewrite !inE => ->. }
    rewrite (@disjointFl _ (mem p) (mem [set x; y])) => //. by rewrite !inE eqxx. }
  have ?: x \notin p2''. { apply: contraTN ir2 => C. by subst; rewrite !irrE !inE C. }
  have ?: x \notin p1''. { apply: contraTN ir1 => C. by subst; rewrite !irrE !inE C. }
  have N2: s2' \notin ps1s'. { apply: contraTN irp => C. by subst; rewrite !irrE C. }

  have ?: forall i j : K4, i != j -> [disjoint phi i & phi j].
  { move => i j iNj. wlog iltj: i j {iNj} / i < j.
    { move => H. rewrite neq_ltn in iNj. move: iNj => /orP [iltj|jlti].
      - by apply H.
      - rewrite disjoint_sym. by apply H. }
    destruct i as [m i]. destruct j as [n j].
    case m as [|[|[|[|m]]]] => //=; case n as [|[|[|[|m']]]] => //=.
    - by rewrite disjoints1 inE. 
    - by rewrite disjoints1 inE. 
    - rewrite disjoints1 !inE negb_or. by apply/andP;split.
    - rewrite disjoints_subset. apply /subsetP => z /=. rewrite !inE.
      move => zp3'. apply: contraTN isT => zp2''.
      case: (ind23 z); solve [by subst; rewrite ?inE ?zp2'' ?zp3'
                             | move => ?; subst z; contrab].
    - rewrite disjoints_subset. apply /subsetP => z /=. rewrite !inE.
      move => zp3'. apply: contraTN isT => /orP [zp1''|zps1s'].
      + case: (ind31 z); solve [by subst; rewrite ?inE ?zp1'' ?zp3'
                               | move => ?; subst z; contrab].
      + suff: z = s2' by move => ?; subst z; contrab.
        apply s2'firstp23; subst; by rewrite ?inE mem_edgep ?zp3' ?zps1s'.
    - rewrite disjoints_subset. apply /subsetP => z /=. rewrite !inE.
      move => zp2''. apply: contraTN isT => /orP [zp1''|zps1s'].
      + case: (ind12 z); solve [by subst; rewrite ?inE ?zp1'' ?zp2''
                               | move => ?; subst z; contrab].
      + suff: z = s2' by move => ?; subst z; contrab.
        apply s2'firstp23; subst; by rewrite ?inE !mem_edgep ?zp2'' ?zps1s'.
  }

  have ?: forall i j : K4, i != j -> exists x' y' : G, [/\ x' \in phi i, y' \in phi j & x' -- y'].
  { move => i j iNj. wlog iltj: i j {iNj} / i < j.
    { move => H. rewrite neq_ltn in iNj. move: iNj => /orP [iltj|jlti].
      - by apply H.
      - case: (H j i jlti) => [x' [y' [x'j y'i edge]]].
        exists y'. exists x'. split => //. by rewrite sg_sym. }
    destruct i as [m i]. destruct j as [n j].
    case m as [|[|[|[|m]]]] => //=; case n as [|[|[|[|m']]]] => //=;
      [ exists y; exists y3  (* M1 M2 *)
      | exists y; exists y2  (* M1 M3 *)
      | exists y; exists y1  (* M1 M4 *)
      | exists x; exists x2  (* M2 M3 *)
      | exists x; exists x1  (* M2 M4 *)
      | exists s2'; exists s'(* M3 M4 *)
      ]; split; try done; try (by rewrite !inE); by rewrite sg_sym.
  }

  split.
  - move => [m i]. case m as [|[|[|[|m]]]] => //=; apply /set0Pn.
    + exists y. by rewrite inE.
    + exists x. by rewrite inE.
    + exists s2'. done.
    + exists s1. by rewrite !inE.
  - move => [m i]. case m as [|[|[|[|m]]]] => //=.
    + apply connected1.
    + apply connected_path.
    + apply connected_path.
    + apply connectedU_common_point with s1.
      * rewrite catp1' catp1'' in s1p1.
        rewrite -mem_prev prev_cat mem_pcatT mem_prev mem_pcatT !inE in s1p1.
        case/orP: s1p1 => [/orP [?|?]|?] => //=; try contrab; by rewrite inE.
      * by rewrite !inE.
      * apply connected_path.
      * apply connected_path.
  - done.
  - done.
Qed.

Lemma no_K4_smallest_separator (G : sgraph) :
  ~ (minor G K4) -> #|G| <= 3 \/ (exists S : {set G}, smallest separator S /\ #|S| <= 2).
Proof.
  move => HM. case (boolP (3 < #|G|)) => sizeG; last by rewrite leqNgt; left. right.
  case (boolP ([exists S : {set G}, separatorb S && (#|S| <= 2)])).
  - move => /existsP [S /andP [sepS sizeS]]. simpl in S.
    case (@ex_smallest _ (@separatorb G) (fun a => #|a|) S sepS) => U /separatorP sepU HU.
    exists U. repeat split => //. 
    + move => V. apply: contraTnot => /separatorP H. by rewrite -leqNgt HU.
    + move: (HU S sepS) => ?. by apply leq_trans with #|S|.
  - move => /existsPn H. exfalso. apply HM. apply K4_of_separators => //.
    move => S. move: (H S). rewrite negb_and. move => /orP [/separatorP nsepS|bb] sepS.
    + exfalso. by apply nsepS.
    + by rewrite ltnNge.
Qed.

Lemma add_edge_sym_iso (G : sgraph) (s1 s2 : G):
  sg_iso (@add_edge G s1 s2) (@add_edge G s2 s1).
Proof.
  pose f1 (v : add_edge s1 s2) := (v : add_edge s2 s1).
  pose f2 (v : add_edge s2 s1) := (v : add_edge s1 s2).
  exists f2 f1.
  - done.
  - done.
  - rewrite /homomorphism_2. move => x y xy. rewrite /f2.
    simpl in xy. simpl. apply /orP. move: xy => /or3P [?|/and3P [? ? ?]|/and3P [? ? ?]].
    + by left.
    + right. apply /orP. right. apply /and3P; split => //. by rewrite eq_sym.
    + right. apply /orP. left. apply /and3P; split => //. by rewrite eq_sym.
  - rewrite /homomorphism_2. move => x y xy. rewrite /f1.
    simpl in xy. simpl. apply /orP. move: xy => /or3P [?|/and3P [? ? ?]|/and3P [? ? ?]].
    + by left.
    + right. apply /orP. right. apply /and3P; split => //. by rewrite eq_sym.
    + right. apply /orP. left. apply /and3P; split => //. by rewrite eq_sym.
(*TODO : simplify *)
Qed.

Lemma add_edge_sedge_sym (G : sgraph) s1 s2 x y:
  (@sedge (@add_edge G s1 s2) x y) <-> (@sedge (@add_edge G s2 s1) x y).
Proof.
Admitted.

Lemma add_edge_connected_sym (G : sgraph) s1 s2 A:
  @connected (@add_edge G s1 s2) A <-> @connected (@add_edge G s2 s1) A.
Proof.
Admitted.

Lemma add_edge_keep_connected_l (G : sgraph) s1 s2 A:
  @connected (@add_edge G s1 s2) A -> s1 \notin A -> @connected G A.
Proof.
Admitted.

Lemma cases_without_edge (G : sgraph) (V1 V2 : {set G}) (s1 s2 : G) phi:
  proper_separation V1 V2 -> V1 :&: V2 = [set s1; s2] -> (@minor_rmap (add_edge s1 s2) K4 phi) ->
  minor G K4 \/ (exists i, exists j, [/\ s1 \in (phi i), s2 \in (phi j) & i!=j])
    \/ exists i, [/\ s1 \in (phi i), s2 \in (phi i) & ~ @connected G (phi i)].
Proof.
  move => psep V12s12 [map0 map1 map2 map3].
  case (boolP ([exists i, s1 \in phi i] && [exists j, s2 \in phi j])).
  - (* s1 and s2 appear in a bag *)
    move => /andP [/existsP [i s1i] /existsP [j s2j]]. case (boolP (i==j));
      last by move => ?; right; left; exists i; exists j; split => //.
    (* s1 s2 in same bag *)
    move => /eqP temp. subst j. case (boolP (@connectedb G (phi i))).
    + (* bag connected, so find minor *)
      move => /connectedP coni. left.
      suff HH: @minor_rmap G K4 phi by apply (minor_of_map (minor_map_rmap HH)).
      have disjE: forall x i j, x \in phi i -> x \in phi j -> i==j. (* TODO: independent lemma *)
      { move => x' i' j' x'i'. apply contraTT => i'Nj'.
        move: (map2 i' j' i'Nj'). rewrite disjoints_subset => /subsetP iINx. 
        move: (iINx x' x'i') => temp. by rewrite inE in temp. }
      split => //.
      * move => x. case (boolP (x==i)) => [xi|xNi]. by move: xi => /eqP ->.
        apply add_edge_keep_connected_l with s1 s2 => //.
        apply: contraNN xNi => ?. apply disjE with s1 => //.
      *  move => i' j' i'j'. case: (map3 i' j' i'j') => x' [y' [x'i' y'j' x'y']].
        exists x'. exists y'. split => //.
        have i'Nj': i'!=j' by rewrite (sg_edgeNeq i'j').
        move: x'y' => /or3P [?|/and3P [x'Ny' /eqP ? /eqP ?]
          |/and3P [y'Nx' /eqP ? /eqP ?]] => //; subst x' y'.
        { move: (disjE s1 i i' s1i x'i') => /eqP temp.
          move: (disjE s2 i j' s2j y'j') => temp2. subst i. contrab. }
        { move: (disjE s1 i j' s1i y'j') => temp.
          move: (disjE s2 i i' s2j x'i') => /eqP temp2. subst i. contrab. }
    + (* bag not connected *)
      move => /connectedP nconi. right. right. exists i. split => //.
  - (* either s1 or s2 is not in any bag *)
    rewrite negb_and !negb_exists.
    wlog /forallP Hs1: s1 s2 V12s12 phi map0 map1 map2 map3 / [forall x, s1 \notin phi x].
    { move => H /orP [Hs1b | Hs2b]. { apply H => //. by apply /orP; left. }
      move: (Hs2b) => /forallP Hs2. case: (H s2 s1 _ phi) => //.
      + by rewrite V12s12 set2C.
      + move => x. by rewrite add_edge_connected_sym.
      + move => i' j' i'j'. case: (map3 i' j' i'j') => x' [y' [? ? ?]].
        exists x'. exists y'. split => //. by rewrite add_edge_sedge_sym.
      + by apply /orP; left.
      + auto.
      + move => [[i [j [? ? ?]]]|[i [? ? ?]]]; right; [left|right].
        * exists j. exists i. split => //. by rewrite eq_sym.
        * exists i. split => //.
    } (* wlog assume s1 is not in any bag *)
    move => _. left. (* so find minor *)
    suff HH: @minor_rmap G K4 phi by apply (minor_of_map (minor_map_rmap HH)).
    split => //.
    + move => x. apply add_edge_keep_connected_l with s1 s2 => //.
    + move => i j ij. case: (map3 i j ij) => x' [y' [x'i y'j x'y']].
      exists x'. exists y'. split => //.
      move: x'y' => /or3P [?|/and3P [x'Ny' /eqP ? /eqP ?]
        |/and3P [y'Nx' /eqP ? /eqP ?]] => //; subst x' y'.
      * move: (Hs1 i) => s1i. contrab.
      * move: (Hs1 j) => s1j. contrab.
Qed.

Lemma card2' G (S : {set G}):
  #|S| == 2 -> exists x y, S = [set x; y] /\ x!=y.
Admitted.

Lemma disjointU' (G : sgraph) (A B C : {set G}):
  [disjoint A & C] -> [disjoint B & C] -> [disjoint A :|: B & C].
Proof.
move => a b. (* rewrite disjointU. *)
Admitted.

Lemma disjointI (G :sgraph) (A B : {set G}):
  (forall x, x \in A -> x \in B -> False) -> [disjoint A & B].
Proof.
  move => H. rewrite -setI_eq0. apply /eqP /setP => z. rewrite !inE.
  apply: contraTF isT => /andP [zCs1 zy]. exfalso. apply H with z => //.
Qed.

Lemma K4_free_add_edge_sep_size2 (G : sgraph) (V1 V2 S: {set G}) (s1 s2 : G):
  K4_free G -> S = V1 :&: V2 -> proper_separation V1 V2 -> smallest separator S ->
  @separation (add_edge s1 s2) V1 V2 -> S = [set s1; s2] -> s1 != s2 ->
  K4_free (add_edge s1 s2).
Proof.
  move => K4free SV12 psep ssepS sep' S12 s1Ns2 K4G'.
  case: (@separation_K4side (add_edge s1 s2) V1 V2 s1 s2) => //.
  { by rewrite -SV12. }
  { apply /orP. right. apply /orP. left. apply /and3P. split => //. }
  move => phi rmapphi.
  (* wlog forall k, Ik \subset V1 *)
  wlog: V1 V2 psep {sep'} SV12 / forall x : K4, phi x \subset V1.
  { move => H [?|?].
    - apply H with V1 V2 => //. by left.
    - apply H with V2 V1 => //. by apply proper_separation_symmetry.
      by rewrite setIC. by left. }
  move => HphiV1 _. apply K4free. rewrite SV12 in S12.

  case: (cases_without_edge psep S12 rmapphi). { done. }

  have caseA: forall (phi2 : K4 -> {set add_edge s1 s2}), minor_rmap phi2 ->
    (exists i j : K4, [/\ s1 \in phi2 i, s2 \in phi2 j & i != j]) ->
    (forall x : K4, phi2 x \subset V1) -> minor G K4.
  { clear rmapphi HphiV1 phi. move => phi rmapphi twobags HphiV1.
    (* case A, s1 and s2 in different bags *)
    move: twobags => [i [j [s1i s2j iNj]]]. rewrite SV12 in ssepS.
    (* s1 as a neighbour z /notin V1 *)
    case: (@sseparator_neighbours _ _ _ s1 psep ssepS).
    { rewrite S12 !inE. apply /orP. by left. }
    move => _ [z [_ zNV1 _ s1z]].
    (* path from z to s2 avoiding s1 *)
    case: (@avoid_nonseperator G [set s1] z s2).
    { apply ssepS.2. by rewrite S12 cards1 cards2 s1Ns2. }
    { by rewrite inE eq_sym (sg_edgeNeq s1z). }
    { by rewrite inE eq_sym. }
    move => p irp dis.

    (* path included in V2 ? *)
    have pV2: p \subset V2.
    { case: (boolP (p \subset V2)) => // /subsetPn [z' z'p z'Nv2].
      case /psplitP pcatz': _/z'p => [pzz' pz's2].  
      move: psep. rewrite proper_separation_symmetry => psep'.
      move: (separation_separates psep'.1 zNV1 z'Nv2) => [zNS z'NS Hp].
      move: (Hp pzz') => [s sp].
      rewrite setIC S12 !inE => /orP [/eqP ?|/eqP ?]; subst s.
      - exfalso. apply: (@disjointE _ _ _ s1 dis); by rewrite ?pcatz' !inE ?sp.
      - rewrite pcatz' in irp. move: (irred_catE irp) => [_ _ Hir].
        have s2z': s2 = z' by apply Hir. subst z'.
        rewrite setIC S12 !inE negb_or in z'NS. case/andP: z'NS => ? t.
        by apply: contraNT t. (* how do we conclude with premise a!=a ? *) }

    (* phi' := phi[k := phi k `union` p] *)
    pose phi' (k : K4) := if k==j then phi k :|: [set a in p] else phi k .
    suff HH: @minor_rmap G K4 phi' by apply (minor_of_map (minor_map_rmap HH)).
    destruct rmapphi as [map0 map1 map2 map3].
    have disjE: forall x i j, x \in phi i -> x \in phi j -> i==j. (* TODO: independent lemma *)
    { move => x' i' j' x'i'. apply contraTT => i'Nj'.
      move: (map2 i' j' i'Nj'). rewrite disjoints_subset => /subsetP iINx.
      move: (iINx x' x'i') => temp. by rewrite inE in temp. }
    rewrite /phi'. split => [x|x|x y xNy|x y xy].
    + case (boolP (x==j)) => xj //=. apply /set0Pn. exists s2. by rewrite !inE.
    + case (boolP (x==j)) => [/eqP xj|xj] //=.
      * subst x. apply connectedU_common_point with s2 => //. by rewrite !inE.
        apply add_edge_keep_connected_l => //. apply: contraNN iNj => s1x.
        by apply: (disjE s1 i j s1i s1x).
        by apply connected_path.
      * apply (@add_edge_keep_connected_l G s2 s1) => //.
        by apply add_edge_connected_sym. apply: contraNN xj => s1x.
        by apply: (disjE s2 x j s1x s2j).
    + wlog yNj: x y xNy / y!=j.
      { move => H. case (boolP (y==j)) => yj //=.
        - rewrite eq_sym in xNy. case (boolP (x==j)) => [/eqP xj | xj] //=.
          + subst x. contrab.
          + move: (H y x xNy xj). rewrite (negbTE xj) yj => ?. by rewrite disjoint_sym.
        - move: (H x y xNy yj). by rewrite (negbTE yj). }
      rewrite (negbTE yNj). case (boolP (x==j)) => [/eqP xj|xj] //=;
        [ subst x | by apply map2].
      rewrite disjointU' => //. by apply map2. apply disjointI => a ap ay.
      rewrite inE in ap. case: (boolP (a==s1)) => [/eqP as1|aNs1].
      { subst a. apply: (@disjointE _ _ _ s1 dis) => //. by rewrite inE. }
      move: (subsetP (HphiV1 y) a ay) => aV1. move: (subsetP pV2 a ap) => aV2.
      have: a \in [set s1; s2] by rewrite -S12 !inE.
      rewrite !inE => /orP [as1|/eqP as2]; first by contrab. subst a.
      move: (disjE s2 j y s2j ay) => ?. contrab.
    + wlog yNj: x y xy / y!=j.
      { move => H. case (boolP (y==j)) => yj //=.
        - simpl in xy. rewrite eq_sym in xy. case (boolP (x==j)) => [/eqP xj | xj] //=.
          + subst x. contrab.
          + move: (H y x xy xj). rewrite (negbTE xj) yj. move => [t1 [t2 [t3 t4 t5]]].
            exists t2. exists t1. split => //. by rewrite sg_sym.
        - move: (H x y xy yj). by rewrite (negbTE yj). }
      (* factorize that with the wlog of the previous case ? *)
      case (boolP (x==j)) => [/eqP xj|xj] //=; try subst x; rewrite (negbTE yNj).
      * case (boolP (y==i)) => [/eqP yi|yNi]. { subst y. exists z. exists s1.
          split => //; last by rewrite sg_sym. by rewrite !inE. }
        move: (map3 j y xy) => [t1 [t2 [t3 t4 t5]]]. exists t1. exists t2. split => //.
        by rewrite !inE t3. move: t5 => /or3P [? | /and3P [t6 /eqP t7 /eqP t8] |
          /and3P [t6 /eqP t7 /eqP t8] ] //; subst t1 t2.
          move: (disjE s2 y j t4 s2j) => ?. contrab.
          move: (disjE s1 y i t4 s1i) => ?. contrab.
      * move: (map3 x y xy) => [t1 [t2 [t3 t4 t5]]]. exists t1. exists t2. split => //.
        move: t5 => /or3P [? | /and3P [t6 /eqP t7 /eqP t8] | /and3P [t6 /eqP t7 /eqP t8] ] //;
          subst t1 t2. move: (disjE s2 y j t4 s2j) => ?. contrab.
          move: (disjE s2 x j t3 s2j) => ?. contrab.
  }

  (* case A with s2 s1 for the wlog of case B *)
  have caseA': forall (phi2 : K4 -> {set add_edge s2 s1}), minor_rmap phi2 ->
    (exists i j : K4, [/\ s2 \in phi2 i, s1 \in phi2 j & i != j]) ->
    (forall x : K4, phi2 x \subset V1) -> minor G K4.
  { clear rmapphi HphiV1 phi. move => phi' rmapphi' twobags' Hphi'V1.
    pose phi (k : K4) := (phi' k : {set add_edge s1 s2}).
    apply caseA with phi => //; rewrite /phi.
    - destruct rmapphi' as [map0 map1 map2 map3]. split => //.
      + move => x. by rewrite add_edge_connected_sym.
      + move => x y xy. move: (map3 x y xy) => [x' [y' [t1 t2 t3]]].
        exists x'. exists y'. split => //. by rewrite add_edge_sedge_sym.
    - move: twobags' => [i [j [t1 t2 t3]]].
      exists j. exists i. split => //. by rewrite eq_sym. }

  move => [twobags|onebag].

  - apply caseA with phi => //.

  - (* case B, s1 and s2 in same bag, not connected *)
    move: onebag => [i [s1i s2i notconi]].
    destruct rmapphi as [map0 map1 map2 map3].
    have disjE: forall x i j, x \in phi i -> x \in phi j -> i==j. (* TODO: separate lemma *)
    { move => x' i' j' x'i'. apply contraTT => i'Nj'.
      move: (map2 i' j' i'Nj'). rewrite disjoints_subset => /subsetP iINx. 
      move: (iINx x' x'i') => temp. by rewrite inE in temp. }

    (* prove [phi i] = [component of s1] U [component of s2] *)
    move C_def : (fun s => [set z | @connect G (@restrict G (mem (phi i)) sedge) z s]) => C.

    have I4inC12: forall (x : G), x \in phi i -> x \in C s1 \/ x \in C s2.
    { move => x xi. case: (boolP (x==s1)) => [/eqP ->|xNs1].
      { left. by rewrite -C_def inE connect0. }
      move: (map1 i x s1 xi s1i) => /PathRP conxs1. case: (conxs1 xNs1) => p Hp.
      case: (@split_at_first (@add_edge G s1 s2) (mem [set s1; s2]) x s1 p s1).
      { rewrite !inE. by apply /orP; left. } { by rewrite inE. }
      move => z [p1 [p2 [catp zS Hfirst]]].
      case: (boolP (z==s1)) => [/eqP ?|zNs1].
      - subst z. left.
        case: (@lift_Path_on _ _ (fun (v : G) => (v : add_edge s1 s2)) x s1 p1 ) => //.
        + move => a b ap1 bp1 /or3P [? | /and3P [t1 /eqP t2 /eqP t3] |
              /and3P [t1 /eqP t2 /eqP t3]] => //; subst a b;
            apply: contraNT t1 => nedge; apply /eqP; symmetry; apply Hfirst => //;
            rewrite !inE; apply /orP; by right.
        + move => a ap1. rewrite /codom. (* ? *) admit.
        + move => p3 t1 t2. rewrite -C_def inE. apply connectRI with p3.
          (* ? *) admit.
      - have /eqP zs2: z==s2. rewrite !inE in zS. move: zS => /orP [?|?] //. contrab.
        subst z. right. admit.
      (* probably a wlog to do
         need to turn a path in G+s1s2 into a path in G *)
    }
    have C1inphii: C s1 \subset phi i.
    { apply /subsetP => z Hz. rewrite -C_def !inE in Hz.
      case: (connect_restrict_case Hz) => [?|[_ ?]]. by subst z. done. }
    have C2inphii: C s2 \subset phi i.
    { apply /subsetP => z Hz. rewrite -C_def !inE in Hz.
      case: (connect_restrict_case Hz) => [?|[_ ?]]. by subst z. done. }
    have disC1C2: C s1 :&: C s2 == set0.
    { rewrite -subset0. apply /subsetP => z. rewrite !inE => /andP [pzs1 pzs2].
      exfalso. apply notconi. move => a b ai bi.
      have cons1s2: @connect G (@restrict G (mem (phi i)) sedge) s1 s2.
      { rewrite -C_def !inE in pzs1 pzs2.
        rewrite srestrict_sym in pzs1. apply connect_trans with z => //. }
      case: (I4inC12 a ai) => aC; rewrite -C_def inE in aC;
        [apply connect_trans with s1|apply connect_trans with s2] => //;
        rewrite srestrict_sym.
      all: case: (I4inC12 b bi) => bC; rewrite -C_def inE in bC;
        [apply connect_trans with s1|apply connect_trans with s2] => //=.
      by rewrite srestrict_sym.
    }

    (* find x1 x2 x3 *)
    have temp: 2 < #|[set: K4] :\ i|.
    { have card4: #|[set: K4]| == 4. { by rewrite cardsT (card_ord 4). }
      rewrite (cardsD1 i) inE eqn_add2l in card4. by rewrite (eqP card4). }

    move: temp => /card_gt2P [j [k [l [[t1 t2 t3] [jk kl lj]]]]].
    rewrite !in_setD1 in t1 t2 t3.
    move: t1 t2 t3 => /andP [ji _] /andP [ki _] /andP [li _].
    move: (map3 j i ji) => [x1' [x1 [x1'j x1i x1'x1]]].
    move: (map3 k i ki) => [x2' [x2 [x2'k x2i x2'x2]]].
    move: (map3 l i li) => [x3' [x3 [x3'l x3i x3'x3]]].
    move: (I4inC12 x1 x1i) (I4inC12 x2 x2i) (I4inC12 x3 x3i).

    (* wlog x1 in C1, x2 in C1, and x3 either in C1 or C2 *)
    have map1': forall x : K4, @connected (@add_edge G s2 s1) (phi x).
    { move => x. rewrite add_edge_connected_sym. apply map1. }
    have map3': forall x y : K4, x -- y -> exists x' y' : add_edge s2 s1,
      [/\ x' \in phi x, y' \in phi y & x' -- y'].
    { move => x y xy. move: (map3 x y xy) => [x' [y' [t1 t2 t3]]].
      exists x'. exists y'. split => //. by rewrite add_edge_sedge_sym. }
    have I4inC12': forall (x : G), x \in phi i -> x \in C s2 \/ x \in C s1.
    { move => x xi. case: (I4inC12 x xi) => ?; [by right| by left]. }

    wlog: s1 s2 j k l x1 x2 x3 x1' x2' x3' phi C_def HphiV1 s1i s2i notconi S12
      x1i x2i x3i x1'j x2'k x3'l x1'x1 x2'x2 x3'x3 s1Ns2 map0 map1 map2 map3 map1' map3'
      jk kl lj ki li ji caseA caseA' disC1C2 C1inphii C2inphii disjE I4inC12 I4inC12' {K4G'}
    / [/\ x1 \in C s1, x2 \in C s1 & x3 \in C s1] \/ [/\ x1 \in C s1, x2 \in C s1 & x3 \in C s2].
    { move => HHH  [x1C1|x1C2] [x2C1|x2C2] [x3C1|x3C2].
      - (* x1C1 x2C1 x3C1 *)
        apply HHH with s1 s2 j k l x1 x2 x3 x1' x2' x3' phi => //;
          try solve [by left | by right].
      - (* x1C1 x2C1 x3C2 *)
        apply HHH with s1 s2 j k l x1 x2 x3 x1' x2' x3' phi => //;
          try solve [by left | by right].
      - (* x1C1 x2C2 x3C1 *)
        apply HHH with s1 s2 j l k x1 x3 x2 x1' x3' x2' phi => //;
          try solve [by left | by right | by rewrite eq_sym ].
      - (* x1C1 x2C2 x3C2 *)
        apply HHH with s2 s1 k l j x2 x3 x1 x2' x3' x1' phi => //;
          try solve [by left | by right | by rewrite add_edge_sedge_sym
                    | by rewrite eq_sym | by rewrite S12 set2C | by rewrite setIC].
      - (* x1C2 x2C1 x3C1 *)
        apply HHH with s1 s2 k l j x2 x3 x1 x2' x3' x1' phi => //;
          try solve [by left | by right | by rewrite eq_sym ].
      - (* x1C2 x2C1 x3C2 *)
        apply HHH with s2 s1 j l k x1 x3 x2 x1' x3' x2' phi => //;
          try solve [by left | by right | by rewrite add_edge_sedge_sym
                    | by rewrite eq_sym | by rewrite S12 set2C | by rewrite setIC].
      - (* x1C2 x2C2 x3C1 *)
        apply HHH with s2 s1 j k l x1 x2 x3 x1' x2' x3' phi => //;
          try solve [by left | by right | by rewrite add_edge_sedge_sym
                    | by rewrite eq_sym | by rewrite S12 set2C | by rewrite setIC].
      - (* x1C2 x2C2 x3C2 *)
        apply HHH with s2 s1 j k l x1 x2 x3 x1' x2' x3' phi => //;
          try solve [by left | by right | by rewrite add_edge_sedge_sym
                    | by rewrite eq_sym | by rewrite S12 set2C | by rewrite setIC].
    }

    (* proving this after the wlog to avoid proving the same for every permutation *)
    have all_ords: forall (x:K4), [ || x==i, x==j, x==k | x==l].
    { move => x. have xK4: x \in [set: K4] by done.
      apply: contraTT isT. rewrite !negb_or => /and4P [xi xj xk xl].
      have card4: 4 == #|[set: K4]|. { by rewrite cardsT (card_ord 4). }
      suff: 5<=#|[set: K4]|. by rewrite ltn_neqAle card4.
      apply /card_gtnP. exists [::i;j;k;l;x]. split => //.
      - apply /and5P. rewrite !inE !negb_or. split => //=;
          [apply /and4P | apply /and3P | apply /andP | ];
          try split => //; by rewrite eq_sym.
      - move => y. by rewrite !inE. }

    (* can place this higher *)
    have conC1: @connected G (C s1).
    { rewrite -C_def. (* connected_restrict. ?*) admit. }
    have conC2: @connected G (C s2).
    { admit. }

    move => [samecomp | diffcomp] _ _ _.

    + (* case x1 x2 x3 in same component (wlog component of s1) *)

      pose phi' (k : K4) := if k==i then C s1 else phi k .
      suff HH: @minor_rmap G K4 phi' by apply (minor_of_map (minor_map_rmap HH)).
      rewrite /phi'. split => [x|x|x y xNy|x y xy].
      * case (boolP (x==i)) => xi //=. apply /set0Pn. exists s1.
        by rewrite -C_def inE connect0.
      * case (boolP (x==i)) => xi //=.
        apply (@add_edge_keep_connected_l G s2 s1) => //.
        apply: contraNN xi => s1x. apply: disjE s2 x i s1x s2i.
      * wlog yNj: x y xNy / y!=i.
        { move => H. case (boolP (y==i)) => yi //=.
          - rewrite eq_sym in xNy. case (boolP (x==i)) => [/eqP xj | xj] //=.
            + subst x. contrab.
            + move: (H y x xNy xj). rewrite (negbTE xj) yi => ?. by rewrite disjoint_sym.
          - move: (H x y xNy yi). by rewrite (negbTE yi). }
        rewrite (negbTE yNj). case (boolP (x==i)) => [/eqP xi|xi] //=;
          [ subst x | by apply map2].
        apply disjointI => z zCs1 zy. move: (subsetP C1inphii z zCs1) => zi.
        apply: (@disjointE _ _ _ z (map2 i y xNy)) => //.
      * wlog yNj: x y xy / y!=i.
        { move => H. case (boolP (y==i)) => yi //=.
          - rewrite sg_sym in xy. case (boolP (x==i)) => [/eqP xj | xj] //=.
            + subst x. rewrite (sg_edgeNeq xy) in yi. done.
            + move: (H y x xy xj). rewrite (negbTE xj) yi. move => [x' [y' [? ? ?]]].
              exists y'. exists x'. split => //. by rewrite sg_sym.
          - move: (H x y xy yi). by rewrite (negbTE yi). }
        rewrite (negbTE yNj). case (boolP (x==i)) => [/eqP xi|xi] //=.
        { subst x. destruct samecomp.
          move: (all_ords y) => /or4P [yi|/eqP yj|/eqP yk|/eqP yl]; try contrab; subst y.
          - exists x1. exists x1'. split => //. rewrite sg_sym.
            move: x1'x1 => /or3P [? | /and3P [t1 /eqP t2 /eqP t3] |
              /and3P [t1 /eqP t2 /eqP t3] ] //; subst x1 x1'.
            move: (disjE s1 j i x1'j s1i) => ?. contrab.
            move: (disjE s2 j i x1'j s2i) => ?. contrab.
          - exists x2. exists x2'. split => //. rewrite sg_sym.
            move: x2'x2 => /or3P [? | /and3P [t1 /eqP t2 /eqP t3] |
              /and3P [t1 /eqP t2 /eqP t3] ] //; subst x2 x2'.
            move: (disjE s1 k i x2'k s1i) => ?. contrab.
            move: (disjE s2 k i x2'k s2i) => ?. contrab.
          - exists x3. exists x3'. split => //. rewrite sg_sym.
            move: x3'x3 => /or3P [? | /and3P [t1 /eqP t2 /eqP t3] |
              /and3P [t1 /eqP t2 /eqP t3] ] //; subst x3 x3'.
            move: (disjE s1 l i x3'l s1i) => ?. contrab.
            move: (disjE s2 l i x3'l s2i) => ?. contrab.
            (* would be nice to factorize this a bit *) }
        move: (map3 x y xy) => [x' [y' [t1 t2 t3]]]. exists x'. exists y'. split => //.
        move: t3 => /or3P [?|/and3P [t4 /eqP t5 /eqP t6]|/and3P [t4 /eqP t5 /eqP t6]] => //;
        subst x' y'. move: (disjE s1 x i t1 s1i) => ?. contrab.
          move: (disjE s2 x i t1 s2i) => ?. contrab.

    + (* case x1 x2 x3 in different components (wlog C1 C1 C2) *)

      pose phi' (k : K4) := if k==i then C s1
        else (if k==l then phi l :|: C s2 else phi k).
      have ?: C s1 \subset V1.
      { apply subset_trans with (mem (phi i)) => //. apply HphiV1. }
      have ?: C s2 \subset V1.
      { apply subset_trans with (mem (phi i)) => //. apply HphiV1. }
      have rmapphi' : @minor_rmap (add_edge s1 s2) K4 phi'.
      { rewrite /phi'. split => [x|x|x y xNy|x y xy].
        - case (boolP (x==i)) => xi; [|case (boolP (x==l)) => xl //].
          + apply /set0Pn. exists s1. rewrite -C_def inE. apply connect0.
          + apply /set0Pn. exists s2. rewrite -C_def !inE. by rewrite connect0.
        - case (boolP (x==i)) => xi => //; case (boolP (x==l)) => xl //;
            try by apply add_edge_connected.
          apply connectedU_edge with (x3' : add_edge s1 s2) x3 => //.
          by destruct diffcomp. by apply add_edge_connected.
        - wlog [xNi yNl]: x y xNy / x!=i /\ y!=l.
          { move => H. case (boolP (x==i)) => xi; case (boolP (y==l)) => yl //=.
            - rewrite eq_sym in xNy. have h: y!=i /\ x!=l.
              { split; apply: contraNN li => /eqP<- => //. by rewrite eq_sym. }
              move: h (H y x xNy h) => [h1 h2].
              rewrite (negbTE h1) (negbTE h2) xi yl. by rewrite disjoint_sym.
            - rewrite eq_sym in xNy. have h: y!=i /\ x!=l.
              { split. apply: contraNN xNy => /eqP-> => //. by rewrite eq_sym.
                       apply: contraNN li => /eqP<- => //. }
              move: h (H y x xNy h) => [h1 h2].
              rewrite (negbTE h1) (negbTE h2) xi (negbTE yl). by rewrite disjoint_sym.
            - rewrite eq_sym in xNy. have h: y!=i /\ x!=l.
              { split. apply: contraNN li => /eqP<- => //. by rewrite eq_sym.
                       apply: contraNN xNy => /eqP-> => //. }
              move: h (H y x xNy h) => [h1 h2].
              rewrite (negbTE h1) (negbTE h2) (negbTE xi) yl. by rewrite disjoint_sym.
            - have h: x!=i /\ y!=l by done.
              move: (H x y xNy h). by rewrite (negbTE xi) (negbTE yl).
          }
          rewrite (negbTE xNi) (negbTE yNl).
          case (boolP (x==l)) => xl; case (boolP (y==i)) => yi => //.
          + apply disjointI => z. rewrite !inE. move => /orP [zl|z2] z1.
            * apply: (@disjointE _ _ _ z (map2 l i li)) => //. by apply (subsetP C1inphii).
            * move: disC1C2 => /eqP /setP => temp. move: (temp z). by rewrite !inE z1 z2.
          + apply disjointI => z. rewrite !inE. move => /orP [zl|z2] zy.
            * apply: (@disjointE _ _ _ z (map2 y l yNl)) => //.
            * apply: (@disjointE _ _ _ z (map2 y i yi)) => //. by apply (subsetP C2inphii).
          + apply disjoint_transR with (mem (phi i)) => //. apply map2 => //.
          + by apply map2.
        - have Hsym: forall (A B : {set G}),
            (exists x' y' : (add_edge s1 s2), [/\ x' \in A, y' \in B & x' -- y']) ->
            exists x' y' : (add_edge s1 s2), [/\ x' \in B, y' \in A & x' -- y'].
          { move => x0 y0 [x' [y' [a b]]]. exists y'. exists x'.
            split => //. rewrite sg_sym. exact p. }
          wlog [xNi yNl]: x y xy / x!=i /\ y!=l.
          { move => H. case (boolP (x==i)) => xi; case (boolP (y==l)) => yl //.
            - rewrite sg_sym in xy. have h: y!=i /\ x!=l.
              { split; apply: contraNN li => /eqP<- => //. by rewrite eq_sym. }
              move: h (H y x xy h) => [h1 h2].
              rewrite (negbTE h1) (negbTE h2) xi yl. apply Hsym.
            - rewrite sg_sym in xy. have h: y!=i /\ x!=l.
              { split. apply: contraNN xy => /eqP-> => //. by rewrite eq_sym.
                       apply: contraNN li => /eqP<- => //. }
              move: h (H y x xy h) => [h1 h2].
              rewrite (negbTE h1) (negbTE h2) xi (negbTE yl). apply Hsym.
            - rewrite sg_sym in xy. have h: y!=i /\ x!=l.
              { split. apply: contraNN li => /eqP<- => //. by rewrite eq_sym.
                       apply: contraNN xy => /eqP-> => //. }
              move: h (H y x xy h) => [h1 h2].
              rewrite (negbTE h1) (negbTE h2) (negbTE xi) yl. apply Hsym.
            - have h: x!=i /\ y!=l by done.
              move: (H x y xy h). by rewrite (negbTE xi) (negbTE yl).
          }
          (* can we factorize that with the wlog of the previous case ? *)
          (* the cases removed by this wlog are shorter to prove than the wlog... kinda useless *)
          rewrite (negbTE xNi) (negbTE yNl).
          case (boolP (x==l)) => [/eqP xl|xNl]; case (boolP (y==i)) => [yi|yNi] => //.
          + exists s2. exists s1. split; try by rewrite -C_def !inE connect0.
            apply /orP. right. apply /orP. right. apply /and3P. split => //.
          + move: (all_ords y) => /or4P [yi|/eqP yj|/eqP yk|yl]; try contrab; subst y x.
            { move: (map3 l j xy) => [x' [y' [t1 t2 t3]]].
              exists x'. exists y'. split => //. by rewrite inE t1. }
            move: (map3 l k xy) => [x' [y' [t1 t2 t3]]].
              exists x'. exists y'. split => //. by rewrite inE t1.
          + move: (all_ords x) => /or4P [xi|/eqP xj|/eqP xk|xl]; try contrab; subst x.
            { exists x1'. exists x1. split => //. by destruct diffcomp. }
            exists x2'. exists x2. split => //. by destruct diffcomp.
          + by apply map3.
      }
      apply caseA with phi' => //.
      * rewrite /phi'. exists i. exists l. rewrite (negbTE li) !eq_refl.
        split; try rewrite -C_def !inE connect0; try rewrite eq_sym; done.
      * rewrite /phi'. move => x. case (boolP (x==i)) => xi //=.
        case (boolP (x==l)) => xl //=. (* why doesnt it simplify ? *)
        { rewrite xl. rewrite -(setUid V1). apply setUSS => //. }
        rewrite (negbTE xl). done.

Admitted.


Theorem TW2_of_K4F (G : sgraph) :
  K4_free G -> exists (T : forest) (B : T -> {set G}), sdecomp T G B /\ width B <= 3.
Proof.
  move: G.
  apply: (@nat_size_ind _ _ (fun G => #|G|)) .
  move => G Hind K4free. case (no_K4_smallest_separator K4free).
  { move => Gsmall. exists tunit. exists (fun _ => [set: G]). split.
    + exact (triv_sdecomp G).
    + apply leq_trans with #|G| => //. apply width_bound. }
  move => [S [ssepS Ssmall2]].
  move: (separator_separation ssepS.1) => [V1 [V2 [psep SV12]]].

  have V1properG: #|induced V1| < #|G|.
  { admit. }
  have V2properG: #|induced V2| < #|G|.
  { admit. }

  rewrite leq_eqVlt in Ssmall2. move: Ssmall2 => /orP [Ssize2|Sless2].

  - (* If #|S| = 2, find S = [set s1; s2], use (add_edge s1 s2) *)
    move: (card2' Ssize2) => [s1 [s2 [S12 s1Ns2]]].
    (* a tree decomposition for G+s1s2 is enough *)
    suff: (exists (T : forest) (B : T -> {set G}), sdecomp T (add_edge s1 s2) B /\ width B <= 3).
    { move => [T [B [sdec wid]]]. exists T. exists B.
      destruct sdec. split => //. split.
      + move => x. destruct (sbag_cover x). eexists; eauto.
      + move => x y xy. case (sbag_edge x y). { apply /orP. by left. }
        move => t /andP [t1 t2]. exists t. by rewrite t1 t2.
      + move => x t1 t2 xt1 xt2. apply sbag_conn => //. }

    (* separation still valid in G+s1s2
       used for K4free_addedge and for separation_decomp *)
    have sep': @separation (add_edge s1 s2) V1 V2.
    { split. { move => x. by move: (psep.1.1 x). } 
      move => x1 x2 x1V2 x2V1. move: (psep.1.2 x1 x2 x1V2 x2V1) => x1x2f.
       have: s1 \in S by rewrite S12 !inE; apply /orP; left.
      rewrite SV12 !inE. move => /andP [? ?]. 
      simpl. rewrite Bool.orb_false_iff; split => //.
      rewrite Bool.orb_false_iff. split; rewrite Bool.andb_false_iff; right.
      + case: (boolP (x1==s1)) => /eqP ?; case: (boolP (x2==s2)) => /eqP ? //=.
        subst x1 x2. contrab.
      + case: (boolP (x1==s2)) => /eqP ?; case: (boolP (x2==s1)) => /eqP ? //=.
        subst x1 x2. contrab.
    }

    have K4free_addedge: K4_free (add_edge s1 s2).
    { apply K4_free_add_edge_sep_size2 with V1 V2 S => //. }

    (* then use separation_decomp *)
    case: (Hind (@induced (add_edge s1 s2) V1)) => //.
    { apply subgraph_K4_free with (add_edge s1 s2) => //. apply induced_sub. }
    move => T1 [B1 [sd1 w1]].
    case: (Hind (@induced (add_edge s1 s2) V2)) => //.
    { apply subgraph_K4_free with (add_edge s1 s2) => //. apply induced_sub. }
    move => T2 [B2 [sd2 w2]].
    case separation_decomp with (add_edge s1 s2) V1 V2 T1 T2 B1 B2 => //.
    { rewrite -SV12 S12. apply (@clique2 (add_edge s1 s2)).
      apply /orP; right. apply /orP; left. apply /and3P; split => //. }
    move => T [B [sd w]]. exists T. exists B. split => //.
    apply leq_trans with (maxn (width B1) (width B2)) => //.
    by rewrite geq_max w1 w2.

  - (* If #|S| < 2, can use separation_decomp directly *)
    case: (Hind (induced V1)) => //.
    { apply subgraph_K4_free with G => //. apply induced_sub. }
    move => T1 [B1 [sd1 w1]].
    case: (Hind (induced V2)) => //.
    { apply subgraph_K4_free with G => //. apply induced_sub. }
    move => T2 [B2 [sd2 w2]].
    case separation_decomp with G V1 V2 T1 T2 B1 B2 => //.
    { apply psep.1. }
    { have temp: #|S|<=1 by done. move: temp => /card_le1P temp.
      rewrite -SV12. move => x y xS yS xNy.
      move: (temp x y xS yS) => /eqP xy. contrab. }
    move => T [B [sd w]]. exists T. exists B. split => //.
    apply leq_trans with (maxn (width B1) (width B2)) => //.
    by rewrite geq_max w1 w2.

Admitted.

