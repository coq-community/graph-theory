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

Definition smallest (T : finType) P (U : {set T}) := P U /\ forall V : {set T}, #|V| < #|U| -> ~ P V.

Lemma ex_smallest (T : finType) (p : pred T) (m : T -> nat) x0 : 
  p x0 -> exists2 x, p x & forall y, p y -> m x <= m y.
Proof.
  move: x0. apply: (nat_size_ind (f := m)) => x0 IH p0.
  case: (boolP [exists x in p, m x < m x0]).
  - case/exists_inP => x *. exact: (IH x).
  - move/exists_inPn => H. exists x0 => // y /H. by rewrite -leqNgt.
Qed.

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

Definition component x := [set y | connect sedge x y].

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
(* TOTHINK: maybe use [forall x, x \in V1 :|: V2] or [forall x, x \notin V1 -> x \in V2] as first part *)
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

Lemma pcat_subset: forall x y z (p : Path x y) (q : Path y z) (A: simpl_pred G),
  p \subset A -> q \subset A -> pcat p q \subset A.
Admitted.

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
  (* There exist finitely many proper separations, pick one for which
  [V1 :&: V2] is smallest. This is smallest separator since every
  separator can be extended to a proper separation *)
  move => xDy xNy. move: (separate_nonadjacent xDy xNy) => /proper_separator /separatorP sep.
  case (ex_smallest (fun S => #|S|) sep) => U /separatorP sepU HU.
  move: (separator_separation sepU) => [V1 [V2 [ps UV]]].
  exists V1; exists V2.
  rewrite -UV /smallest. split; last split; move => // V ineq /separatorP sepV.
  move: (HU V sepV) => ineq2. rewrite ltnNge in ineq. contrab.
Qed.

Lemma separation_sym V1 V2 : separation V1 V2 <-> separation V2 V1.
Admitted.

(* TODO: should be an equivalence *)
Lemma proper_separation_symmetry V1 V2 :
  proper_separation V1 V2 -> proper_separation V2 V1.
Proof.
Admitted.



(** TOTHINK: the second assumption is half-redundant but makes for a nice statement *)
(** TOTHINK: provide [x \notin V2] instead *)
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
        exists x1; exists x2. split => //; by apply negbNE.
  }
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
      rewrite !inE. apply /and3P. split => //.
      * move: (z0z) => /prev_edge_proof zz0. (* TODO: simplify *)
        apply: contraTN zz0 => /eqP->. by rewrite Hwlog // !inE z0V1 (sep_inL sepV).
      * apply: contraTT (z0z) => ?. by rewrite sepV.
Qed.

(* TOTHINK: This definition really only makes sense for irredundant paths *)
Definition independent x y (p q : Path x y) := 
  forall z, z \in p -> z \in q -> z = x \/ z = y.

Definition left_independent x y y' (p : Path x y) (q : Path x y') := 
  forall z, z \in p -> z \in q -> z = x.

Lemma left_independent_sym (x y y' : G) (p : Path x y) (q : Path x y') :
  left_independent p q -> left_independent q p.
Proof. move => H z A B. exact: H. Qed.

Lemma separatorNE U x y : ~ separator U -> x \notin U -> y \notin U -> ~ separates x y U.
Proof. move => nsepU Hx Hy sepU. by apply nsepU; exists x; exists y. Qed.

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
  proper_separation V1 V2 -> forall x0 x, x0 \in V1:\:V2 ->
  connect (restrict [predC (V1:&:V2)] sedge) x0 x -> x \in V1:\:V2.
Proof.
  set S := V1 :&: V2. set C1 := V1 :\: V2. set C2 := V2 :\: V1.
  move => [sepV propV] x0 x x0C1.
  case: (boolP (x0==x)) => [/eqP ? | x0x]; first by subst x0.
  move => /(PathRP x0x) [p /subsetP Hp].
  case: (boolP(x \in C1)) => // xNC1.
  case: (@split_at_first G [predC C1] x0 x p x) => //.
    move => z [p1 [p2 [H1 H2 H3]]]. rewrite inE /= in H2.
  case (boolP (x0 == z)) => [/eqP ?|?]; first by subst x0; contrab.
  case: (@splitR G x0 z p1) => [|z0 [p1' [z0z H4]]] //.
  apply: contraTT (z0z) => _. rewrite sepV //. 
  + have: z0==z = false by rewrite sg_edgeNeq.
    apply: contraFT => z0NC1. apply /eqP. apply H3; first by rewrite !inE negb_and z0NC1. 
    by rewrite H4 mem_pcat path_end.
  + have zNS: z \in [predC S]. { apply Hp. by rewrite H1 mem_pcat path_end. }
    (** What is going on here? *)
    move: (sepV.1 z) => zV12.
    rewrite /S !inE !negb_and /= in zV12 zNS H2 *. 
    move: zV12 zNS H2 => /orP [zV1 | zV2] /orP [zNV1 | zNV2] /orP [?|?] //; contrab.
Qed.

End Separators.

Prenex Implicits separator.
Implicit Types G H : sgraph.

Lemma separation_decomp G (V1 V2 : {set G}) T1 T2 B1 B2 t1 t2 :
  sdecomp T1 (induced V1) B1 -> sdecomp T2 (induced V2) B2 -> 
  separation V1 V2 -> V1 :&: V2 \subset (val @: B1 t1) :&: (val @: B2 t2) ->
  exists T B, sdecomp T G B /\ width B <= maxn (width B1) (width B2).
Admitted.

Lemma minorRE G H : minor G H -> exists phi : H -> {set G}, minor_rmap phi.
Proof. case => phi /minor_rmap_map D. eexists. exact: D. Qed.

Lemma disjointW (T : finType) (A B C D : pred T) : 
    A \subset B -> C \subset D -> [disjoint B & D] -> [disjoint A & C].
Proof. 
  move => subAB subCD BD. apply: (disjoint_trans subAB). 
  move: BD. rewrite !(disjoint_sym B). exact: disjoint_trans.
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

Definition remainder (G : sgraph) (U S : {set G}) : {set induced U} := 
  [set x : induced U | val x \in S].
Arguments remainder [G] U S.

(** TOHINK: This is one possibility, but this has the potential to
lead to messy sigma-type. Alternative: define separators for induced
subgraphs and lift the required lemmas *)
Lemma sseparator_remove G (S : {set G}) s : 
  smallest separator S -> s \in S -> 
 @smallest (induced [set~ s]) separator (remainder _ S).
Proof.
Admitted.

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

Lemma path_touch_separation :
  forall G (x : G) (S V1 V2 : {set G}) (s1 : G) (pxs1 : Path x s1) (C1 : {set G}),
  C1 = V1 :\: V2 -> S = V1 :&: V2 -> s1 \in S -> irred pxs1 ->
  (forall y : G, y \in pxs1 -> y \in S -> y = s1) -> x \in C1 ->
  proper_separation V1 V2 -> {subset pxs1 <= V1}.
Proof.
  move => G x S V1 V2 s1 pxs1 C1 HC1 HS s1S ir subset xC1 psep.
  case: (@splitR G x s1 pxs1). { rewrite HS HC1 !inE in xC1 s1S.
    move: s1S xC1 => /andP [_ ?] /andP [? _].
    apply: contraTN isT => /eqP ?. subst x. contrab. }
  move => z [pxz [zs1 pcat1]].
  move: (ir) => irc. rewrite pcat1 irred_edgeR in irc. case/andP: irc => [s1pxz _].
  rewrite pcat1. move => x1. rewrite mem_pcatT. move => /orP [x1p | xs1].
  - suff: x1 \in C1. rewrite HC1 inE. by move => /andP [_ ?]. rewrite HC1.
    case (boolP (x == x1)) => [/eqP ?|?]; first by subst.
    apply separation_connected_same_component with x => //; first by rewrite -HC1.
    apply /PathRP => //.
    case /psplitP pcat2: _/x1p => [pxx1 px1z].
    exists pxx1. rewrite -HS. apply /subsetP => x2 x2pxx1.
    apply: contraNT s1pxz => x2S. rewrite inE Bool.negb_involutive /= in x2S.
    rewrite -(subset x2) => //.
      + rewrite pcat2 inE x2pxx1. done.
      + rewrite pcat1 /= inE pcat2 inE x2pxx1. done.
  - rewrite /tail /edgep inE in xs1. move: xs1 => /eqP->.
    rewrite HS inE in s1S. by case/andP: s1S.
Qed.

Lemma independent_paths G (V1 V2 : {set G}) : 
  proper_separation V1 V2 -> smallest separator (V1 :&: V2) -> 3 <= #|V1 :&: V2| ->
  exists x1 x2 (p1 p2 p3 : Path x1 x2), 
    [/\ irred p1, irred p2 & irred p3] /\
    [/\(exists2 s1, s1 \in p1 & s1 \notin [set x1; x2]),
       (exists2 s2, s2 \in p2 & s2 \notin [set x1; x2])&
       (exists2 s3, s3 \in p3 & s3 \notin [set x1; x2])] /\
    [/\ x1 \in V1 :\: V2, x2 \in V2 :\: V1, 
       independent p1 p2, independent p2 p3 & independent p3 p1].
Proof.
  set S := V1 :&: V2.
  set C1 := V1 :\: V2.
  set C2 := V2 :\: V1.
  move => [[V12G nedgeC12] proper] ssS /card_gt2P [s1 [s2 [s3 [[s1S s2S s3S] [Ns12 Ns23 Ns31]]]]].
  move: (proper) => [/set0Pn [x0 x0C1] /set0Pn [y0 y0C2]].
  rewrite -/C1 -/C2 in x0C1 y0C2.
  case: (@independent_paths_aux G S s1 s2 s3 x0) => //=.
    { rewrite /S !inE. rewrite /C1 !inE in x0C1. by move: x0C1 => /andP [? ->]. }
  move => x [pxs1 [pxs2 [pxs3 [[irx1 irx2 irx3] [[/subsetIlP1 px1Ss1 /subsetIlP1 px2Ss2 /subsetIlP1 px3Ss3]
    [connx0x ind_pxs1pxs2 ind_pxs2pxs3 ind_pxs3pxs1]]]]]].
  case: (@independent_paths_aux G S s1 s2 s3 y0) => //=.
    { rewrite /S !inE. rewrite /C2 !inE in y0C2. by move: y0C2 => /andP [? ->]. }
  move => y [pys1 [pys2 [pys3 [[iry1 iry2 iry3] [[/subsetIlP1 py1Ss1 /subsetIlP1 py2Ss2 /subsetIlP1 py3Ss3]
    [conny0y ind_pys1pys2 ind_pys2pys3 ind_pys3pys1]]]]]].
  set p1 := pcat pxs1 (prev pys1).
  set p2 := pcat pxs2 (prev pys2).
  set p3 := pcat pxs3 (prev pys3).
  exists x; exists y; exists p1; exists p2; exists p3.

  have S21: S = V2 :&: V1 by rewrite setIC.
  have psep21: proper_separation V2 V1 by apply proper_separation_symmetry.
  have xC1: x \in C1 by apply separation_connected_same_component with x0.
  have yC2: y \in C2.
  { apply separation_connected_same_component with y0 => //. by rewrite -S21. }
  have pxs1V1: {subset pxs1 <= V1}. { apply path_touch_separation with S V2 C1 => //. }
  have pxs2V1: {subset pxs2 <= V1}. { apply path_touch_separation with S V2 C1 => //. }
  have pxs3V1: {subset pxs3 <= V1}. { apply path_touch_separation with S V2 C1 => //. }
  have pys1V2: {subset pys1 <= V2}. { apply path_touch_separation with S V1 C2 => //. }
  have pys2V2: {subset pys2 <= V2}. { apply path_touch_separation with S V1 C2 => //. }
  have pys3V2: {subset pys3 <= V2}. { apply path_touch_separation with S V1 C2 => //. }

  gen have irredpi: s1 pxs1 pys1 {ind_pys1pys2 ind_pys3pys1 p1 py1Ss1
      ind_pxs1pxs2 ind_pxs3pxs1 s1S Ns12 Ns31} px1Ss1 irx1 iry1 pxs1V1 pys1V2
    / irred (pcat pxs1 (prev pys1)).
  { rewrite irred_cat. apply /and3P; split => //; first by rewrite irred_rev.
    apply /eqP /setP => z. rewrite inE mem_prev in_set1.
    apply Bool.eq_true_iff_eq; split.
    * move => /andP [zpxs1 /pys1V2 zV2]. move: (zpxs1) => /pxs1V1 zV1.
      apply /eqP. apply (px1Ss1 z); rewrite /S ?inE //=.
    * move => /eqP->. apply /andP; split; apply path_end.
  }

  gen have indep: s1 s2 pxs1 pys1 pxs2 pys2
      {Ns23 Ns31 iry2 ind_pys2pys3 irx2 ind_pxs2pxs3 iry1 ind_pys3pys1 irx1 ind_pxs3pxs1 p1 p2}
      ind_pxs1pxs2 ind_pys1pys2 pxs1V1 pxs2V1 pys1V2 pys2V2 Ns12 s2S s1S px1Ss1 px2Ss2 py1Ss1 py2Ss2
      / independent (pcat pxs1 (prev pys1)) (pcat pxs2 (prev pys2)).
  { rewrite /independent => z. rewrite !mem_pcat !mem_prev.
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

  gen have sinotxy: s1 p1 pxs1 pys1 {Ns12 Ns31 iry1 py1Ss1 ind_pys1pys2 ind_pys3pys1
      p1 pys1V2 irx1 px1Ss1 ind_pxs1pxs2 ind_pxs3pxs1 pxs1V1}
      s1S / exists2 s0 : G, s0 \in (pcat pxs1 (prev pys1)) & s0 \notin [set x; y].
  { exists s1; first by rewrite !inE. rewrite !inE !negb_or.
    rewrite !inE in xC1 yC2 s1S. move: xC1 yC2 s1S => /andP [? ?] /andP [? ?] /andP [? ?].
    apply /andP. split; apply: contraTN isT => /eqP ?; subst s1; contrab.
  }

  split; [|split]; split.
  - (* irred p1 *) by apply irredpi.
  - (* irred p2 *) by apply irredpi.
  - (* irred p3 *) by apply irredpi.
  - (* s1 \notin [set x; y] *) by apply sinotxy.
  - (* s2 \notin [set x; y] *) by apply sinotxy.
  - (* s3 \notin [set x; y] *) by apply sinotxy.
  - (* x \in C1 *) done.
  - (* y \in C2 *) done.
  - (* independent p1 p2 *) by apply indep.
  - (* independent p2 p3 *) by apply indep.
  - (* independent p3 p1 *) by apply indep.
Qed.

Lemma independent_symmetry (G : sgraph):
  forall (x y : G) (p q : Path x y), independent p q -> independent q p.
Proof.
  move => x y p q ipq z zq zp.
  case: (ipq z zp zq) => H. by left. by right.
Qed.

Lemma connectedU_common_point :
  forall (G : sgraph) (U V : {set G}) (x : G),
  x \in U -> x \in V -> connected U -> connected V -> connected (U :|: V).
Proof.
Admitted.

Lemma splitR_buffed: forall (G : sgraph) (x y : G) (p : Path x y),
  x != y -> irred p -> exists (z : G) (p' : Path x z) (zy : z -- y),
  [/\ irred p', p = pcat p' (edgep zy) & [set z in p'] = ([set z in p] :\ y)].
Proof.
  move => G x y p xNy ip.
  case: (splitR p xNy) => z [p' [zy cat]].
  exists z. exists p'. exists zy. split => //.
  - rewrite cat irred_edgeR in ip. by case/andP: ip.
  - rewrite cat irred_edgeR in ip. case/andP: ip => [yNp' ip'].
    apply /setP => a. rewrite !inE. rewrite cat mem_pcatT !inE.
    case: (boolP (a==y)) => [/eqP ay | aNy] //=. subst a.
    case: (boolP (y \in p')) => [? | ?] //=. contrab.
Qed.

Lemma splitL_buffed: forall (G : sgraph) (x y : G) (p : Path x y),
  x != y -> irred p -> exists (z : G) (p' : Path z y) (xz : x -- z),
  [/\ irred p', p = pcat (edgep xz) p' & [set z in p'] = ([set z in p] :\ x)].
Proof.
  move => G x y p xNy ip.
  case: (splitL p xNy) => z [xz [p' [cat _]]].
  exists z. exists p'. exists xz. split => //.
  - rewrite cat irred_edgeL in ip. by case/andP: ip.
  - rewrite cat irred_edgeL in ip. case/andP: ip => [xNp' ip'].
    apply /setP => a. rewrite !inE. rewrite -(mem_prev p) cat prev_cat mem_pcatT !inE.
    case: (boolP (a==x)) => [/eqP ax | aNx] //=. subst a.
    case: (boolP (x \in p')) => [? | ?] //=. contrab.
Qed.


Lemma K4_of_separators (G : sgraph) : 
  3 < #|G| -> (forall S : {set G}, separator S -> 2 < #|S|) -> minor G K4.
Proof.
  move => G4elt minsep3.
  case: (boolP [forall x : G, forall y : G, (x==y) || (x--y)]).
  { case/card_gtnP: G4elt => [sq [uniqsq sq4elt sqG]].
    destruct sq as [|g0 [|g1 [|g2 [|g3 [|g4 q]]]]]; simpl in sq4elt => //=.
    clear sq4elt. move => H.
    have Htemp: forall x y : G, x!=y -> x--y.
    { move => x y xNy. move: H => /forallP H'. move: (H' x) => /forallP Hx.
      move: (Hx y) => /orP [xy | ?] => //. contrab. }
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
    - move => [m i] [m' i']. case m as [|[|[|[|m]]]] => //=;
      case m' as [|[|[|[|m']]]] => //= _.
      all: erewrite eq_disjoint1; [ rewrite inE | move => ?; rewrite inE; reflexivity] => //=;
        try done; by rewrite eq_sym.
    - move => [m i] [m' i']. case m as [|[|[|[|m]]]] => //=;
      case m' as [|[|[|[|m']]]] => //= _.
      all: eexists; eexists; split; [by rewrite inE | by rewrite inE
        | apply Htemp; try done; by rewrite eq_sym].
  }

  move => /forallPn [x /forallPn [y temp]].
  rewrite negb_or in temp. move: temp => /andP [xNy xNEy].
  move: (minimal_separation xNy xNEy) => [V1 [V2 [psepV12 [sS HS]]]].
  set S := V1 :&: V2. set C1 := V1 :\: V2. set C2 := V2 :\: V1.
  rewrite -/S in HS sS. move: (minsep3 S sS) => S3elt. clear x y xNy xNEy.
  case: (independent_paths psepV12) => //. move => x [y [p1 [p2 [p3 [[ir1 ir2 ir3]
    [[[s1 s1p1 s1Nxy] [s2 s2p2 s2Nxy] [s3 s3p3 s3Nxy]] [xC1 yC2 ind12 ind23 ind31]]]]]]].
  rewrite -/C1 -/C2 in xC1 yC2.
  have xNy: x!=y. { apply: contraTN isT => /eqP ?; subst x.
    rewrite !inE in xC1 yC2. move: xC1 yC2 => /andP [? ?] /andP [? ?]. contrab. }
  case (@avoid_nonseperator G [set x; y] s1 s2) => //.
    { apply HS. rewrite cards2. rewrite xNy. exact S3elt. }
  move => p irp dispxy.
  case: (@split_at_first G (predU (mem p2) (mem p3)) s1 s2 p s2) => //; first by rewrite !inE s2p2.
  move => s2' [p' [p'' [catp s2'p23 s2'firstp23]]].

  wlog s2'p2: p2 p3 {s3p3 s2p2} ir2 ir3 s2'firstp23 ind12 ind23 ind31 s2'p23 / (s2' \in p2).
  { rewrite inE /= in s2'p23. move: (s2'p23) => /orP [s2'p2|s2'p3].
    - apply. exact ir2. exact ir3. all:eauto.
    - apply. exact ir3. exact ir2. 2-4: apply independent_symmetry; eauto.
      + move => z' H1 H2. apply s2'firstp23. rewrite inE /= in H1.
        move: H1 => /orP [H1|H1]; by rewrite !inE /= H1. done.
      + by rewrite !inE /= s2'p3.
      + done.
  }

set M1 := [set y].
set M2 := [set z in p3] :\ y.
set M3 := [set z in p2] :\: [set x; y].
set M4 := ([set z in p1] :\: [set x; y]) :|: ([set z in p']:\s2').

pose phi (i : K4) := match i with
                  | Ordinal 0 _ => M1
                  | Ordinal 1 _ => M2
                  | Ordinal 2 _ => M3
                  | Ordinal 3 _ => M4
                  | Ordinal p n => set0
                  end.
  suff HH: minor_rmap phi by apply (minor_of_map (minor_map_rmap HH)).

  have ?: [disjoint M1 & M2].
  { rewrite /M1 /M2 disjoints_subset.
    apply /subsetP => z /=. rewrite !(inE,negb_and,negb_or,negbK) => //=.
    move => ->. done. }
  have ?: [disjoint M1 & M3].
  { rewrite /M1 /M3 disjoints_subset.
    apply /subsetP => z /=. rewrite !(inE,negb_and,negb_or,negbK) => //=.
    move => ->. done. }
  have ?: [disjoint M1 & M4].
  { rewrite /M1 /M4 disjoints_subset.
    apply /subsetP => z /=. rewrite !(inE,negb_and,negb_or,negbK) => //=.
    move => zNy. rewrite zNy. move: zNy => /eqP ->. apply /andP; split => //.
    apply /orP. right.
    suff: (y \notin p). by rewrite catp inE negb_or => /andP [? _].
    rewrite (@disjointFl _ (mem p) (mem [set x; y])) => //.
    rewrite !inE. apply /orP. right. done. }
  have ?: [disjoint M2 & M3].
  { rewrite /M2 /M3 disjoints_subset.
    apply /subsetP => z /=. rewrite !inE. move => /andP [zNy zp3].
    rewrite !(inE,negb_and,negb_or,negbK) => //=.
    case: (boolP (z \in p2)) => [zp2|zNp2] => //=.
    move: (ind23 z zp2 zp3) => [/eqP ->|/eqP ->] //=. }
  have ?: [disjoint M2 & M4].
  { rewrite /M2 /M4 disjoints_subset.
    apply /subsetP => z /=. rewrite !inE. move => /andP [zNy zp3].
    rewrite !(inE,negb_and,negb_or,negbK) => //=.
    apply /andP; split.
    - case: (boolP (z \in p1)) => [zp1|zNp1] => //=.
      move: (ind31 z zp3 zp1) => [/eqP ->|/eqP ->] //=.
    - case: (boolP (z \in p')) => [zp'|zNp'] => //=.
      rewrite (s2'firstp23 z) => //=. by rewrite inE /= zp3. }
  have ?: [disjoint M3 & M4].
  { rewrite /M3 /M4 disjoints_subset.
    apply /subsetP => z /=. rewrite !inE negb_or. move => /andP [/andP [zNx zNy] zp2].
    rewrite !(inE,negb_and,negb_or,negbK) => //=.
    apply /andP; split.
    - apply /orP; right. case: (boolP (z \in p1)) => [zp1|zNp1] => //=.
      move: (ind12 z zp1 zp2) => [/eqP ?|/eqP ?] //=; contrab.
    - case: (boolP (z \in p')) => [zp'|zNp'] => //=.
      rewrite (s2'firstp23 z) => //=. by rewrite inE /= zp2. }

  case: (splitR_buffed xNy ir3) => [y3 [p3' [y3y [ir3' catp3 rewM2]]]].
  case: (splitL_buffed xNy ir2) => [x2 [p2' [xx2 [ir2' catp2' rewM3']]]].
  case: (splitL_buffed xNy ir1) => [x1 [p1' [xx1 [ir1' catp1' rewM41']]]].
  case: (@splitR_buffed G x1 y p1') => //.
  { apply: contraTN (xx1) => /eqP ?. subst x1. rewrite psepV12.1.2 => //=.
    - rewrite !inE in xC1. by case/andP : xC1 => ? _.
    - rewrite !inE in yC2. by case/andP : yC2 => ? _. }
  move => y1 [p1'' [y1y [irp1'' catp1'' rewM41]]]. rewrite rewM41' setDDl in rewM41.
  case: (@splitR_buffed G x2 y p2') => //.
  { apply: contraTN (xx2) => /eqP ?. subst x2. rewrite psepV12.1.2 => //=.
    - rewrite !inE in xC1. by case/andP : xC1 => ? _.
    - rewrite !inE in yC2. by case/andP : yC2 => ? _. }
  move => y2 [p2'' [y2y [irp2'' catp2'' rewM3]]]. rewrite rewM3' setDDl in rewM3.
  case: (@splitR_buffed G s1 s2' p') => //.
  { apply: contraTN isT => /eqP ?. subst s2'.
    rewrite !inE negb_or in s1Nxy. move: s1Nxy => /andP [? ?].
    move: (ind12 s1 s1p1 s2'p2) => [/eqP aa|/eqP bb]; contrab. }
  { rewrite catp irred_cat in irp. by case /and3P: irp. } 
  move => s' [ps1s' [s's2' [irps1s' catps1s' rewM42]]].
  have s2'M3: s2' \in M3.
  { rewrite !inE s2'p2 negb_or. apply /andP; split => //=.
    have temp: s2' \in p. { rewrite catp inE path_end. done. }
    move: (disjointFr dispxy temp). rewrite !inE. move => /negbT aa.
    by rewrite negb_or in aa. }

  have ?: exists x' y' : G, [/\ x' \in M1, y' \in M2 & x' -- y'].
  { exists y; exists y3; split.
    - by rewrite /M1 inE.
    - by rewrite /M2 -rewM2 !inE.
    - by rewrite sg_sym. }
  have ?: exists x' y' : G, [/\ x' \in M1, y' \in M3 & x' -- y'].
  { exists y; exists y2; split.
    - by rewrite /M1 inE.
    - by rewrite /M3 -rewM3 !inE.
    - by rewrite sg_sym. }
  have ?: exists x' y' : G, [/\ x' \in M1, y' \in M4 & x' -- y'].
  { exists y; exists y1; split.
    - by rewrite /M1 inE.
    - by rewrite /M4 -rewM41 -rewM42 !inE.
    - by rewrite sg_sym. }
  have ?: exists x' y' : G, [/\ x' \in M2, y' \in M3 & x' -- y'].
  { exists x; exists x2; split.
    - by rewrite /M2 !inE.
    - by rewrite /M3 -rewM3 !inE.
    - done. }
  have ?: exists x' y' : G, [/\ x' \in M2, y' \in M4 & x' -- y'].
  { exists x; exists x1; split.
    - by rewrite /M2 !inE.
    - by rewrite /M4 -rewM41 -rewM42 !inE.
    - done. }
  have ?: exists x' y' : G, [/\ x' \in M3, y' \in M4 & x' -- y'].
  { exists s2'; exists s'; split.
    - done.
    - by rewrite /M4 -rewM41 -rewM42 !inE.
    - by rewrite sg_sym. }
  have hsymcon: forall A B, (exists x' y' : G, [/\ x' \in A, y' \in B & x' -- y']) ->
                          (exists x' y' : G, [/\ x' \in B, y' \in A & x' -- y']).
  { move => ? ? ? ?. case => [x' [y' [? ? ?]]]. exists y'; exists x'; split => //. by rewrite sg_sym. }

  split.
  - move => [m i]. case m as [|[|[|[|m]]]] => //=; apply /set0Pn.
    + exists y. by rewrite inE.
    + exists x. by rewrite !inE xNy.
    + exists s2'. done.
    + exists s1. rewrite /M4 -rewM42. by rewrite !inE.
  - move => [m i]. case m as [|[|[|[|m]]]] => //=.
    + apply connected1.
    + rewrite /M2 -rewM2. apply connected_path.
    + rewrite /M3 -rewM3. apply connected_path.
    + rewrite /M4 -rewM41 -rewM42. apply connectedU_common_point with s1.
      * rewrite catp1' catp1'' in s1p1.
        rewrite -mem_prev prev_cat mem_pcatT mem_prev mem_pcatT !inE in s1p1.
        rewrite !inE negb_or in s1Nxy. case/andP: s1Nxy => [? ?].
        case/orP: s1p1 => [/orP [?|?]|?] => //=; try contrab; by rewrite inE.
      * rewrite inE. apply path_begin.
      * apply connected_path.
      * apply connected_path.
  - move => [m i] [m' i']. case m as [|[|[|[|m]]]] => //=;
    case m' as [|[|[|[|m']]]] => //= _; by rewrite disjoint_sym.
  - move => [m i] [m' i']. case m as [|[|[|[|m]]]] => //=;
    case m' as [|[|[|[|m']]]] => //= _; by apply hsymcon.
Qed.

Theorem TW2_of_K4F (G : sgraph) :
  K4_free G -> exists (T : forest) (B : T -> {set G}), sdecomp T G B /\ width B <= 3.
Proof.
Admitted.
