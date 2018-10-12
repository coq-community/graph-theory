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

Definition proper V1 V2 := V1 :\: V2 != set0 /\ V2 :\: V1 != set0.

Definition proper_separation V1 V2 := separation V1 V2 /\ proper V1 V2.

Lemma separate_nonadjacent x y : x != y -> ~~ x -- y -> proper_separation [set~ x] [set~ y].
Proof.
  move => xDy xNy. split.
  - split.
    + move => z. rewrite !inE -negb_and. by apply: contraNN xDy => /andP[/eqP->/eqP->].
    + move => x1 x2. rewrite !inE !negbK sg_sym => [/eqP->] [/eqP->].
      by rewrite (negbTE xNy).
  - split. 
    + apply/set0Pn. exists y. by rewrite !inE eqxx eq_sym (negbTE xDy).
    + apply/set0Pn. exists x. by rewrite !inE eqxx (negbTE xDy).
Qed.

Lemma proper_separator V1 V2 :
  proper_separation V1 V2 -> separator (V1 :&: V2).
Proof.
  move => [Hsep [/set0Pn[x Hx] /set0Pn[y Hy]]]. exists x. exists y.
  split; try by move: Hx Hy; rewrite !inE; do ! case (_ \in _).
  - move => p.
    case: (@split_at_first G (mem V2) x y p y) => //; first by case/setDP: Hy.
    move => z [p1 [p2 [H1 H2 H3]]]. rewrite inE in H2. exists z.
    (* z is the first node of the path \in V2 *)
    + by rewrite H1 mem_pcat path_end.
    + rewrite inE H2 andbT.
      case: (@splitR G x z p1) => [|z0 [p1' [z0z H4]]].
      { apply: contraTneq H2 => ?; subst x. by case/setDP : Hx. }
      apply: contraTT (z0z) => Hz1. rewrite Hsep ?inE //.
      case: (boolP (z0 \in V2)) => /= H0.
      * move: (z0z). rewrite [z0]H3 ?sgP //. by rewrite H4 mem_pcat path_end.
      * move: (z0z). by rewrite Hsep.
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
  - split; apply/set0Pn.
    + exists x1. suff H: (x1 \in U) by rewrite !inE H.
      by rewrite /U -lock inE connect0.
    + exists x2. rewrite !inE negb_or S2 (_ : x2 \notin U = true) //.
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

Lemma proper_separation_symmetry V1 V2 :
  proper_separation V1 V2 -> proper_separation V2 V1.
Proof. move => [[? nedgeC12] [? ?]].
  split; split => //; first by rewrite setUC.
  move => x1 x2 H H'. rewrite sg_sym. by apply nedgeC12.
Qed.

Lemma separation_path V1 V2:
  separation V1 V2 -> forall x y, x \in (V1 :\: V2) -> y \in (V2 :\: V1) ->
  separates x y (V1 :&: V2).
Proof.
Admitted.

(** TOTHINK: the second assumption is half-redundant but makes for a nice statement *)
(** TOTHINK: provide [x \notin V2] instead *)
Lemma sseparator_neighbours V1 V2 s : 
  proper_separation V1 V2 -> smallest separator (V1 :&: V2) -> 
  s \in V1 :&: V2 -> exists x1 x2, [/\ x1 \in V1 :\: V2, x2 \in V2 :\: V1, s -- x1 & s -- x2].
Proof.
  wlog: V1 V2 / [forall x1 in (V1:\:V2), ~~ s -- x1].
  { move => H ps ss sS.
    case (boolP [forall x in (V1 :\: V2), ~~ s -- x]).
    - move => HH. apply (H V1 V2) => //.
    - move => /forall_inPn [x1 x1V sx1].
      case (boolP [forall x in (V2 :\: V1), ~~ s -- x]).
      + move => HH. rewrite setIC in sS ss. case (H V2 V1) => //.
        * by apply proper_separation_symmetry.
        * move => y [z [? ? ? ?]]. exists z; exists y. split; done.
      + move => /forall_inPn [x2 x2V sx2].
        exists x1; exists x2. split => //; by apply negbNE.
  }
  rewrite /smallest.
  move => /forall_inP Hwlog [sepV [/set0Pn [x1 x1V12] /set0Pn [x2 x2V21]]] [sepS smallS] sS.
  pose S' := V1 :&: V2:\ s. suff: separator S'.
  - move => sS'. exfalso. move: sS'. apply smallS.
    rewrite /S'. rewrite (cardsD1 s (V1 :&: V2)) sS //=.
  - (* cant use [separator S], because the two vertices could be both in V2 *)
    exists x1; exists x2. split.
    + subst S'. rewrite !inE in x1V12. move: x1V12 => /andP [x1V2 _].
      rewrite !inE !negb_and. by rewrite x1V2.
    + subst S'. rewrite !inE in x2V21. move: x2V21 => /andP [x2V1 _].
      rewrite !inE !negb_and. by rewrite x2V1.
    + move => p.
      case: (@split_at_first G (mem V2) x1 x2 p x2) => //; first by case/setDP: x2V21.
      move => z [p1 [p2 [H1 H2 H3]]]. rewrite inE in H2. exists z;
        first by rewrite H1 mem_pcat path_end.
      case: (@splitR G x1 z p1). { apply: contraTN isT => /eqP ?.
        subst x1. case/setDP: x1V12 => _ ?. contrab. }
      move => z0 [p' [z0z Hp']].
      have z0V1: z0 \notin V2. 
      { (* have: z0 \in [set: G] by done. rewrite -sep1 !inE. *)
        (* suff: z0 \notin V2 by move => ? /orP [?|?] //; contrab. *)
        move: (sg_edgeNeq z0z) => zz0. apply: contraFN zz0 => ?.
        apply /eqP. apply H3 => //. rewrite Hp'. rewrite mem_pcat mem_edgep.
        by rewrite eq_refl.
      }
      rewrite !inE. apply /and3P. split => //.
      * move: (z0z) => /prev_edge_proof zz0.
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

Lemma separation_K4 G (V1 V2 : {set G}) : 
  separation V1 V2 -> #|V1 :&: V2| <= 2 -> 
  minor G K4 -> 
  exists2 phi : G -> option K4, minor_map phi & phi @^-1: [set~ None] \subset V1.
Admitted.                                     

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

Definition inE := (inE,mem_pcat,path_begin,path_end,mem_prev).

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
  rewrite -[y \in mem p2]/(y \in p2) in P32. (* ugly *)
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
    move: s1S => /andP [_ ?]. move: xC1 => /andP [? _].
    apply: contraTN isT => /eqP ?. subst x. contrab. }
  move => z [pxz [zs1 pcat1]].
  move: (ir) => irc. rewrite pcat1 irred_edgeR in irc. move: irc => /andP [s1pxz _].
  rewrite pcat1. move => x1. rewrite mem_pcatT. move => /orP [x1p | xs1].
  - suff: x1 \in C1. rewrite HC1 inE /andP. by move => /andP [_ ?]. rewrite HC1.
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
    rewrite HS inE in s1S. by move: s1S => /andP [? _].
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
  rewrite -/C1 -/C2 in nedgeC12 x0C1 y0C2.
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
Admitted.

Lemma K4_of_separators (G : sgraph) : 
  3 < #|G| -> (forall S : {set G}, separator S -> 2 < #|S|) -> minor G K4.
Proof.
  move => G4elt minsep3.
  case: (boolP [forall x : G, forall y : G, (x==y) || (x--y)]).
  { (*TODO, take 4 elements in G, exact K4 *) admit. }

  move => /forallPn [x /forallPn [y temp]].
  rewrite negb_or in temp. move: temp => /andP [xNy xNEy].
  move: (minimal_separation xNy xNEy) => [V1 [V2 [psepV12 [sS HS]]]].
  set S := V1 :&: V2. set C1 := V1 :\: V2. set C2 := V2 :\: V1.
  rewrite -/S in HS sS. move: (minsep3 S sS) => S3elt. clear x y xNy xNEy.
  case: (independent_paths psepV12) => //. move => x [y [p1 [p2 [p3 [[ir1 ir2 ir3]
    [[[s1 s1p1 s1Nxy] [s2 s2p2 s2Nxy] [s3 s3p3 s3Nxy]] [xC1 yC2 ind12 ind23 ind31]]]]]]].
  rewrite -/C1 -/C2 in xC1 yC2.

  case (@avoid_nonseperator G [set x; y] s1 s2) => //.
  { have temp: x!=y. { apply: contraTN isT => /eqP ?; subst x.
      rewrite !inE in xC1 yC2. move: xC1 yC2 => /andP [? ?] /andP [? ?]. contrab. }
    apply HS. rewrite cards2. rewrite temp. exact S3elt. }
  move => p irp dispxy.

  case: (@split_at_first G (predU (mem p2) (mem p3)) s1 s2 p s2) => //;
    first by rewrite !inE s2p2.
  move => s2' [p' [p'' [catp'p'' s2'p23 s2'firstp23]]].

  wlog s2'p2: p2 p3 {ir3 ir2 s3p3 s2p2 s2'firstp23} ind12 ind23 ind31 s2'p23 / (s2' \in p2).
  { rewrite inE /= in s2'p23. move: (s2'p23) => /orP [s2'p2|s2'p3].
    - apply; eauto.
    - apply; try (apply independent_symmetry; eauto).
      by rewrite !inE /= s2'p3. done.
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
  { rewrite /M1 /M2 /M3 /M4 disjoints_subset.
    apply /subsetP => z /=. rewrite !(inE,negb_and,negb_or,negbK) => //=.
    move => ->. done. }
  have ?: [disjoint M1 & M3].
  { rewrite /M1 /M2 /M3 /M4 disjoints_subset.
    apply /subsetP => z /=. rewrite !(inE,negb_and,negb_or,negbK) => //=.
    move => ->. done. }
  have ?: [disjoint M1 & M4].
  { rewrite /M1 /M2 /M3 /M4 disjoints_subset.
    apply /subsetP => z /=. rewrite !(inE,negb_and,negb_or,negbK) => //=.
    move => zNy. rewrite zNy. move: zNy => /eqP ->. apply /andP; split => //.
    apply /orP. right. (* from [p = pcat p' p''] and [disjoint p & [set x; y]]*)
    admit. }
  have ?: [disjoint M2 & M3].
  { rewrite /M1 /M2 /M3 /M4 disjoints_subset.
    apply /subsetP => z /=. rewrite !inE. move => /andP [zNy zp3].
    rewrite !(inE,negb_and,negb_or) => //=.
    rewrite /independent in ind23. (* case z \in p2 *)
    admit. }
  have ?: [disjoint M2 & M4].
  { rewrite /M1 /M2 /M3 /M4 disjoints_subset.
    apply /subsetP => z /=. rewrite !inE. move => /andP [zNy zp3].
    rewrite !(inE,negb_and,negb_or) => //=. admit. }
  have ?: [disjoint M3 & M4]. { admit. }

  have con12: exists x' y' : G, [/\ x' \in M1, y' \in M2 & x' -- y']. { admit. }
  have con13: exists x' y' : G, [/\ x' \in M1, y' \in M3 & x' -- y']. { admit. }
  have con14: exists x' y' : G, [/\ x' \in M1, y' \in M4 & x' -- y']. { admit. }
  have con23: exists x' y' : G, [/\ x' \in M2, y' \in M3 & x' -- y']. { admit. }
  have con24: exists x' y' : G, [/\ x' \in M2, y' \in M4 & x' -- y']. { admit. }
  have con34: exists x' y' : G, [/\ x' \in M3, y' \in M4 & x' -- y']. { admit. }

  have hsymcon: forall A B, (exists x' y' : G, [/\ x' \in A, y' \in B & x' -- y']) ->
                          (exists x' y' : G, [/\ x' \in B, y' \in A & x' -- y']).
  { move => ? ? ? ?. case => [x' [y' [? ? ?]]].
    exists y'; exists x'; split => //. by rewrite sg_sym. }

  split.

  - move => [m i]. case m as [|[|[|[|m]]]] => //=.

    + admit. (* M1 != set0 *)
    + admit.
    + admit.
    + admit.

  - move => [m i]. case m as [|[|[|[|m]]]] => //=.
    + admit. (* connected M1 *)
    + admit.
    + admit.
    + admit.

  - move => [m i] [m' i']. case m as [|[|[|[|m]]]] => //=;
    case m' as [|[|[|[|m']]]] => //= _; by rewrite disjoint_sym.

  - move => [m i] [m' i']. case m as [|[|[|[|m]]]] => //=;
    case m' as [|[|[|[|m']]]] => //= _; by apply hsymcon.

Admitted.

Theorem TW2_of_K4F (G : sgraph) :
  K4_free G -> exists (T : forest) (B : T -> {set G}), sdecomp T G B /\ width B <= 3.
Proof.
Admitted.
