Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect.
(* Note: ssrbool is empty and shadows Coq.ssr.ssrbool, use Coq.ssrbool for "Find" *)

Require Import edone finite_quotient preliminaries set_tac.
Require Import sgraph minor.

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
  move/proper_separator/separatorP : (separate_nonadjacent xDy xNy) => sep.
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

(** TODO: This proof should become simpler there was a join-lemma
without intermediate node *)
Lemma separation_decomp G (V1 V2 : {set G}) T1 T2 B1 B2 :
  @sdecomp T1 (induced V1) B1 -> @sdecomp T2 (induced V2) B2 -> 
  separation V1 V2 -> clique (V1 :&: V2) ->
  exists T B, @sdecomp T G B /\ width B <= maxn (width B1) (width B2).
Proof.
  move => dec1 dec2 sepV subV.
  have dec12 := join_decomp dec1 dec2.
  set G' := sjoin _ _ in dec12.
  set T := tjoin T1 T2 in dec12.
  set B : tjoin T1 T2 -> {set G'}:= decompU B1 B2 in dec12.
  pose h (x : G') : G := match x with inl x => val x | inr x => val x end.
  case: (boolP (0 < #|V1 :&: V2|)) => [cliquen0|clique0].

  - (* clique not empty *)
    move def_S : (V1 :&: V2) => S. rewrite def_S in subV cliquen0.

    pose S1 := [set x | val x \in S] : {set induced V1}.
    have cln01: 0 < #|S1|.
    { move/card_gt0P: cliquen0 => [s sS]. apply/card_gt0P. 
      have sV1: s \in V1 by set_tac. by exists (Sub s sV1); rewrite !inE. }
    have clS1: clique S1.
    { move => x y xS yS xNy. rewrite !inE in xS yS. exact: (subV (val x : G) (val y)). }
    pose S2 := [set x | val x \in S] : {set induced V2}.
    have cln02: 0 < #|S2|.
    { move/card_gt0P: cliquen0 => [s sS].
      apply/card_gt0P. move: (sS); rewrite -def_S inE => /andP [_ sV2].
      exists (Sub s sV2). by rewrite inE. }
    have clS2: clique S2.
    { move => x y xS yS xNy. rewrite !inE in xS yS.
      apply: (subV (val x : G) (val y)) => //. }

    case: (decomp_clique dec1 cln01 clS1) => t1 Ht1.
    case: (decomp_clique dec2 cln02 clS2) => t2 Ht2.
    have dis_t1_t2 : ~~ connect (@sedge T)(inl t1) (inr t2) by rewrite join_disc.
    have dis_T12 : {in [set inl t1;inr t2] &, forall x y, x != y -> ~~ connect (@sedge T) x y}.
    { move => [?|?] [?|?] /setUP[] /set1P-> /setUP[]/set1P ->.
      all: by rewrite ?eqxx // => _; rewrite sconnect_sym. }
    pose T' := @tlink T _ dis_T12.
    pose P := [set inl x | x in S1] :|: [set inr x | x in S2].
    pose B' := decompL B P : _ -> {set G'}.

    have imhS : h @: B' None = S.
    { apply /setP => x. apply /imsetP. case: (boolP (x \in S)) => [xS|xNS].
      - have xV1: x \in V1 by move: xS; rewrite -def_S inE => /andP [].
        exists (inl (Sub x xV1)) => //. rewrite inE. apply /orP; left.
        apply /imsetP. eexists => //=. by rewrite inE.
      - apply: contraNnot xNS. move => [x' x'P xx']. subst x.
        move: x'P. rewrite inE => /orP [] /imsetP [x xS x'x];
          subst x'; by rewrite inE in xS. }

    have dec3: sdecomp T' G (rename B' h).
    { apply rename_decomp.
      - apply: decomp_link => //.
        apply/subsetP => x.
        rewrite !inE => /orP [xS1|xS2]; apply /bigcupP.
        + exists (inl t1); first by rewrite !inE eqxx.
          move: xS1 => /imsetP [x0 x0s1 xlx0]. rewrite xlx0.
          rewrite /B /decompU mem_imset => //. by rewrite (subsetP Ht1).
        + exists (inr t2); first by rewrite !inE eqxx.
          move: xS2 => /imsetP [x0 x0s2 xrx0]. rewrite xrx0.
          rewrite /B /decompU mem_imset => //. by rewrite (subsetP Ht2).
      - rewrite /h. move => [x|x] [y|y] xy hxNhy; done.
      - move => x. move: (sepV.1 x). rewrite inE => /orP [xV1|xV2].
        + by exists (inl (Sub x xV1)).
        + by exists (inr (Sub x xV2)).
      - move => x y xy. (* probaby a better way, a bit brute forced *)
        case: (boolP (x \in V1)) => [xV1|xNV1]; case: (boolP (x \in V2)) => [xV2|xNV2];
          last by move: (sepV.1 x); rewrite inE => /orP [] ?; contrab.
        + move: (sepV.1 y); rewrite inE => /orP [yV1|yV2].
          * exists (inl (Sub x xV1)). exists (inl (Sub y yV1)). split => //=.
          * exists (inr (Sub x xV2)). exists (inr (Sub y yV2)). split => //=.
        + case: (boolP (y \in V1)) => [yV1|yNV1].
          * exists (inl (Sub x xV1)). exists (inl (Sub y yV1)). split => //=.
          * by rewrite (sepV.2 x y xNV2 yNV1) in xy.
        + case: (boolP (y \in V2)) => [yV2|yNV2].
          * exists (inr (Sub x xV2)). exists (inr (Sub y yV2)). split => //=.
          * rewrite sg_sym in xy. by rewrite (sepV.2 y x yNV2 xNV1) in xy.
      - move => x y hxEhy.
        case: (altP (x=Py)) => xNy.
        { subst y. case: dec12 => [H1 _ _]. move: (H1 x) => [t Ht].
          left. exists (Some t). by rewrite Ht. }
        wlog: x y hxEhy xNy / exists x' y', x = inl x' /\ y = inr y'.
        { move => W. case Hx: (x) => [lx|rx]; case Hy: (y) => [ly|ry].
          + suff ?: x==y by contrab. rewrite Hx Hy in hxEhy. rewrite Hx Hy inl_eqE.
            apply /eqP. apply val_inj. simpl in hxEhy. simpl. by rewrite hxEhy.
          + rewrite Hx Hy in hxEhy. apply W => //. eexists. eexists. split => //.
          + case: (W y x) => //; first by rewrite eq_sym.
            * eexists. eexists. rewrite Hx Hy. split => //. 
            * rewrite Hx Hy. case => t /andP [? ?]. left. by exists t.
            * rewrite Hx Hy. case => t [t'] [? ? ?]. right. exists t';exists t. by rewrite sgP.
          + suff ?: x==y by contrab. rewrite Hx Hy in hxEhy. rewrite Hx Hy inr_eqE.
            apply /eqP. apply val_inj. simpl in hxEhy. simpl. by rewrite hxEhy.
        }
        move => [x' [y' [xx' yy']]]. rewrite xx' yy' in hxEhy. simpl in hxEhy.
        case Hx': (x') => [x0 x0V1]. case Hy': (y') => [y0 y0V2].
        have x0y0: x0 = y0 by rewrite Hx' Hy' in hxEhy. subst x0.
        simpl in x0V1. simpl in y0V2. left. exists None.
        rewrite xx' yy'. simpl. rewrite !inE. apply /andP.
        split; apply /orP; [left|right];
          apply /imsetP; (eexists;[|eauto]);
          by rewrite inE -def_S inE ?Hx' ?Hy' x0V1 y0V2.
    }

    exists T'. exists (rename B' h). split => //.
    rewrite {1}/width (bigID (pred1 None)).
    rewrite big_pred1_eq. rewrite geq_max. apply/andP;split => //.
    + rewrite leq_max; apply /orP; left. apply leq_trans with #|S1| => /=.
      * rewrite imhS -(on_card_preimset (f := fun x : induced V1 => val x)) //=. 
        case/card_gt0P : cln01 => x0. 
        exists (insubd x0) => x //. by rewrite valKd.
        move => inS. rewrite insubdK //= unfold_in. 
        move: inS. rewrite -def_S inE. by case: (_ \in _). (* Where is this being proved? *)
      * rewrite /width. apply leq_trans with #|B1 t1|; first by apply subset_leq_card.
        apply (@leq_bigmax _ (fun t => #|B1 t|)).
    + rewrite (reindex Some) /=.
      * apply: leq_trans (join_width B1 B2).
        apply: max_mono => t. exact: leq_imset_card.
      * apply: subon_bij; last by (apply bij_on_codom => //; exact: (inl t1)). 
        by move => [x|]; rewrite !in_simpl // codom_f.

  - (* clique size 0 *)
    suff iso: sg_iso G' G.
    + case: (sg_iso_decomp dec12 iso) => B' sdecB' wB'B.
      exists T; exists B'. split => //. by rewrite wB'B join_width.
    + suff HH: V2 = ~:V1.
      * rewrite /G' HH. apply ssplit_disconnected. move => x y xV1 yNV1.
        rewrite (sepV.2 x y) => //. by rewrite HH inE xV1.
      * rewrite card_gt0 negbK in clique0. apply /setP => x.
        case: (boolP (x \in V1)) => [xV1|xNV1]; case: (boolP (x \in V2)) => [xV2|xNV2];
          try solve [rewrite inE ?xV1 ?xNV1 => //];
          last by (move: (sepV.1 x); rewrite inE => /orP [] ?; contrab).
        suff: (x \in set0) by rewrite inE.
        rewrite -(eqP clique0). by rewrite !inE.
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
  - apply connectRI with p => z zp. by rewrite inD. (* set_tac fails due to [mem] *)
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
    (* TOTHINK: Make set_tac make use of [A == set0] and [A != set0]? *)
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
  rewrite inE in P32. subst p1; subst p3. 
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
    case: (altP (x =P x1)) => ?; first by subst.
    apply separation_connected_same_component with V1 x => //.
    case /psplitP pcat2: _/x1p => [pxx1 px1z]. 
    apply connectRI with pxx1. rewrite -HS => x2 x2pxx1. 
    apply: contraNN s1pxz => /= x2S. 
    by rewrite -(subset x2) // !(pcat2,pcat1) !inE x2pxx1.
  - rewrite !inE in xs1. by rewrite (eqP xs1) inD.
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
  { by rewrite /S; set_tac. }
  move => x [pxs1 [pxs2 [pxs3 [[irx1 irx2 irx3] 
    [[/subsetIlP1 px1Ss1 /subsetIlP1 px2Ss2 /subsetIlP1 px3Ss3]
    [connx0x ind_pxs1pxs2 ind_pxs2pxs3 ind_pxs3pxs1]]]]]].
  case: (@independent_paths_aux G S s1 s2 s3 y0) => //=. 
  { by rewrite /S; set_tac. }
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
  { move => z. rewrite !inE => /orP [zpxs1 | zpys1] /orP [zpxs2 | zpys2].
    + left. by apply ind_pxs1pxs2.
    + exfalso. move/eqP : Ns12. apply.
      move: (pxs1V1 z zpxs1) (pys2V2 z zpys2) => zV1 zV2.
      rewrite -(px1Ss1 z) ?inE // -(py2Ss2 z) ?inE //.
    + exfalso. move/eqP : Ns12; apply.
      move: (pxs2V1 z zpxs2) (pys1V2 z zpys1) => zV1 zV2.
      rewrite -(px2Ss2 z) ?inE // -(py1Ss1 z) ?inE //.
    + right. by apply ind_pys1pys2.
  }

  split; [|split].
  - (* irred *) split; by apply irredpi.
  - (* si \in p & si \in S *) split; [exists s1|exists s2|exists s3] => //; by rewrite !inE.
  - (* x/y \notin V2/V1 + independent *) split => //; by apply indep.
Qed.


Lemma K4_of_separators (G : sgraph) : 
  3 < #|G| -> (forall S : {set G}, separator S -> 2 < #|S|) -> minor G K4.
Proof.
  move => G4elt minsep3.
  case: (boolP (cliqueb [set: G])) => [|/cliquePn [x] [y] [_ _ xNy xNEy]].
  { move/cliqueP. apply: minor_of_clique. by rewrite cardsT. }
  move: (minimal_separation xNy xNEy) => [V1 [V2 [[sepV propV] [sS HS]]]].
  set S := V1 :&: V2. rewrite -/S in HS sS.
  move: (minsep3 S sS) => S3elt. clear x y xNy xNEy.
  case: (@independent_paths _ V1 V2) => // => x [y [p1 [p2 [p3 [[ir1 ir2 ir3]
    [[[s1 s1p1 s1S] [s2 s2p2 s2S] [s3 s3p3 s3S]] [xNV2 yNV1 ind12 ind23 ind31]]]]]]].
  have temp: forall s, s \in S -> s!=x /\ s!=y. (* this is ugly! *)
  { move => s. rewrite /S inE => /andP [? ?].
    split; apply: contraTN isT => /eqP ?; subst s; contrab. }
  move: (temp s1 s1S) (temp s2 s2S) => [s1Nx s1Ny] [s2Nx s2Ny]. clear temp.
  have xNy: x!=y.
  { apply: contraTN isT => /eqP ?; subst x. move: (sepV.1 y). by set_tac. }
  case (@avoid_nonseperator G [set x; y] s1 s2) => //; try by set_tac.
  { apply HS. by rewrite cards2 xNy. }
  move => p irp dispxy.
  case: (@split_at_first G (predU (mem p2) (mem p3)) s1 s2 p s2) => //.  
  { by rewrite !inE s2p2. }
  move => s2' [p' [p'' [catp s2'p23 s2'firstp23]]].

  wlog s2'p2: p2 p3 {s3p3 s2p2} ir2 ir3 s2'firstp23 ind12 ind23 ind31 s2'p23 / (s2' \in p2).
  { move => W. move: (s2'p23). rewrite inE /= => /orP [s2'p2|s2'p3].
    - by apply W with p2 p3. 
    - apply W with p3 p2 => //; try exact: independent_sym.
      + move => z' H1 H2. apply s2'firstp23 => //. move: H1. by rewrite !inE orbC. 
      + by rewrite !inE /= s2'p3. }

  case: (splitR p3 xNy) => [y3 [p3' [y3y catp3]]].
  case: (splitL p2 xNy) => [x2 [xx2 [p2' [catp2' _]]]].
  case: (splitL p1 xNy) => [x1 [xx1 [p1' [catp1' _]]]].
  case: (@splitR G x1 y p1') => // [|y1 [p1'' [y1y catp1'']]].
  { apply: contraTneq (xx1) => ?. subst x1. by rewrite sepV. }
  case: (@splitR G x2 y p2') => // [|y2 [p2'' [y2y catp2'']]].
  { apply: contraTneq (xx2) => ?. subst x2. by rewrite sepV. }
  case: (@splitR G s1 s2' p') => // [|s' [ps1s' [s's2' catps1s']]].
  { apply: contraTneq isT => ?. subst s2'.
    move: (ind12 s1 s1p1 s2'p2) => [/eqP aa|/eqP bb]; contrab. }

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
  suff: minor_rmap phi by apply minor_of_rmap.

  have s2'M3: s2' \in M3. (* TOTHINK: this looks roundabout *)
  { rewrite !inE. rewrite catp2' catp2'' in s2'p2.
    rewrite -mem_prev prev_cat mem_pcatT mem_prev mem_pcatT !inE in s2'p2.
    have temp: s2' \in p by rewrite catp inE path_end.
    move: (disjointFr dispxy temp). rewrite !inE. move => /negbT temp2.
    rewrite negb_or in temp2. move: temp2 => /andP [? ?].
    case/orP: s2'p2 => [/orP [?|?]|?] => //=; contrab. }

  have irrE := (irred_edgeL,irred_edgeR,irred_cat).

  (* only used in the 'have:' below *)
  have ?: y \notin p3'. { apply: contraTN ir3 => C. by subst; rewrite !irrE C. }
  have ?: y \notin p1''. { apply: contraTN ir1 => C. by subst; rewrite !irrE C. }
  have ?: y \notin p2''. { apply: contraTN ir2 => C. by subst; rewrite !irrE C. }
  have N1: y \notin ps1s'.
  { suff: (y \notin p). { apply: contraNN. by subst; rewrite !inE => ->. }
    rewrite (@disjointFl _ (mem p) (mem [set x; y])) => //. by rewrite !inE eqxx. }
  have ?: x \notin p2''. { apply: contraTN ir2 => C. by subst; rewrite !irrE !inE C. }
  have ?: x \notin p1''. { apply: contraTN ir1 => C. by subst; rewrite !irrE !inE C. }
  have N2: s2' \notin ps1s'. { apply: contraTN irp => C. by subst; rewrite !irrE C. }
  
  split.
  - move => [m i]. case m as [|[|[|[|m]]]] => //=; apply /set0Pn.
    + exists y. by rewrite inE.
    + exists x. by rewrite inE.
    + exists s2'. done.
    + exists s1. by rewrite !inE.
  - move => [m i]. case m as [|[|[|[|m]]]] => //=.
    + exact: connected1.
    + exact: connected_path.
    + exact: connected_path.
    + apply connectedU_common_point with s1; try exact: connected_path.
     rewrite catp1' catp1'' in s1p1.
     rewrite -mem_prev prev_cat mem_pcatT mem_prev mem_pcatT !inE in s1p1.
     case/orP: s1p1 => [/orP [?|?]|?] => //=; try contrab; by rewrite inE.
     by rewrite !inE.
  - move => i j iNj. wlog iltj: i j {iNj} / i < j.
    { move => H. rewrite /= neq_ltn in iNj. 
      move: iNj => /orP [iltj|jlti]; [|rewrite disjoint_sym]; exact: H. }
    destruct i as [m i]. destruct j as [n j].
    case m as [|[|[|[|m]]]] => //=; case n as [|[|[|[|m']]]] => //=.
    + by rewrite disjoints1 inE.
    + by rewrite disjoints1 inE.
    + rewrite disjoints1 !inE negb_or. by apply/andP.
    + apply/disjointP => z. rewrite !inE => zp3' zp2''.
      case: (ind23 z); solve [ by subst; rewrite ?inE ?zp2'' ?zp3'
                             | move => ?; subst z; contrab].
    + apply/disjointP => z. rewrite !inE => zp3' /orP [zp1''|zps1s'].
      * case: (ind31 z); solve [by subst; rewrite ?inE ?zp1'' ?zp3'
                               | move => ?; subst z; contrab].
      * suff: z = s2' by move => ?; subst z; contrab.
        apply s2'firstp23; subst; by rewrite ?inE mem_edgep ?zp3' ?zps1s'.
    + apply/disjointP => z. rewrite !inE => zp2'' /orP [zp1''|zps1s'].
      * case: (ind12 z); solve [by subst; rewrite ?inE ?zp1'' ?zp2''
                               | move => ?; subst z; contrab].
      * suff: z = s2' by move => ?; subst z; contrab.
        apply s2'firstp23; subst; by rewrite ?inE !mem_edgep ?zp2'' ?zps1s'.
  - move => i j iNj. wlog iltj: i j {iNj} / i < j.
    { move => H. rewrite /= neq_ltn in iNj. 
      move: iNj => /orP [?|?]; [|rewrite neighborC]; exact: H. }
    destruct i as [m i]. destruct j as [n j]. apply/neighborP.
    case m as [|[|[|[|m]]]] => //=; case n as [|[|[|[|m']]]] => //=;
      [ exists y; exists y3  (* M1 M2 *)
      | exists y; exists y2  (* M1 M3 *)
      | exists y; exists y1  (* M1 M4 *)
      | exists x; exists x2  (* M2 M3 *)
      | exists x; exists x1  (* M2 M4 *)
      | exists s2'; exists s'(* M3 M4 *)
      ]; split; try done; try (by rewrite !inE); by rewrite sg_sym.
Qed.

Lemma no_K4_smallest_separator (G : sgraph) :
  ~ minor G K4 -> #|G| <= 3 \/ (exists S : {set G}, smallest separator S /\ #|S| <= 2).
Proof.
  move => HM. case (boolP (3 < #|G|)) => sizeG; last by rewrite leqNgt; left. 
  right. case: (boolP ([exists (S : {set G} | #|S| <= 2), separatorb S])).
  - case/exists_inP => /= S sizeS sepS. 
    case (@ex_smallest _ (@separatorb G) (fun a => #|a|) S sepS) => U /separatorP sepU HU.
    exists U. repeat split => //. 
    + move => V. apply: contraTnot => /separatorP H. by rewrite -leqNgt HU.
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
  move => x1 x2 x1V2 x2V1 /=. rewrite sep //=. apply: contraTF isT.
  case/orP => [] /and3P[_ /eqP ? /eqP ?]; by set_tac.
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
    (* TODO: fix nodesE/mem_path lemmase *)
    rewrite mem_path -nodesE -[_ p3]map_id t1 nodesE -(mem_path p2). 
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

Lemma K4_free_add_edge_sep_size2 (G : sgraph) (V1 V2 S: {set G}) (s1 s2 : G):
  K4_free G -> S = V1 :&: V2 -> proper_separation V1 V2 -> smallest separator S ->
  S = [set s1; s2] -> s1 != s2 -> K4_free (add_edge s1 s2).
Proof.
  move => K4free SV12 psep ssepS S12 s1Ns2 K4G'.
  case: (@separation_K4side (add_edge s1 s2) V1 V2) => //.
  { apply add_edge_separation; try by rewrite -SV12 S12 !inE eqxx. exact psep.1. }
  { rewrite -SV12 S12. apply: clique2. by rewrite /= !eqxx s1Ns2. }
  { by rewrite -SV12 S12 cards2 s1Ns2. }
  move => phi rmapphi {K4G'}.
  (* wlog forall k, Ik \subset V1 *)
  wlog: V1 V2 psep SV12 / forall x : K4, phi x \subset V1.
  { move => H [?|?].
    - apply H with V1 V2 => //. by left.
    - apply H with V2 V1 => //. by apply proper_separation_symmetry.
      by rewrite setIC. by left. }
  move => HphiV1 _. apply K4free. rewrite SV12 in S12.

  (* case A, s1 and s2 in different bags *)
  gen have caseA: s1 s2 s1Ns2 S12 phi rmapphi HphiV1 /
    (exists i j : K4, [/\ s1 \in phi i, s2 \in phi j & i != j]) -> minor G K4.
  { move => [i [j [s1i s2j iNj]]]. rewrite SV12 in ssepS.
    (* s1 as a neighbour z /notin V1 *)
    case: (@sseparator_neighbours _ _ _ s1 psep ssepS) => [|_ [z [_ zNV1 _ s1z]]].
    { by rewrite S12 !inE eqxx. }
    (* path from z to s2 avoiding s1 *)
    case: (@avoid_nonseperator G [set s1] z s2) => [|||p irp dis].
    { apply ssepS.2. by rewrite S12 cards1 cards2 s1Ns2. }
    { by rewrite inE eq_sym ?(sg_edgeNeq s1z). }
    { by rewrite inE eq_sym. }
    (* path included in V2 *)
    have pV2: p \subset V2. (* TODO: simplify *)
    { case: (boolP (p \subset V2)) => // /subsetPn [z' z'p z'Nv2].
      case /psplitP pcatz': _/z'p => [pzz' pz's2].
      move: psep. rewrite proper_separation_symmetry => psep'.
      move: (separation_separates psep'.1 zNV1 z'Nv2) => [zNS z'NS Hp].
      move: (Hp pzz') => [s sp].
      rewrite setIC S12 !inE => /orP [] /eqP ?; subst s.
      - exfalso. apply: (@disjointE _ _ _ s1 dis); by rewrite ?pcatz' !inE ?sp.
      - rewrite pcatz' in irp. move: (irred_catE irp) => [_ _ Hir].
        have s2z': s2 = z' by apply Hir. subst z'.
        rewrite setIC S12 !inE negb_or eqxx in z'NS. by case/andP: z'NS. }
    (* phi' := phi[k := phi k `union` p] *)
    pose phi' (k : K4) := if k==j then phi j :|: [set a in p] else phi k .
    suff HH: @minor_rmap G K4 phi' by apply (minor_of_map (minor_map_rmap HH)).
    have disjE := (rmap_disjE rmapphi).
    destruct rmapphi as [map0 map1 map2 map3].
    rewrite /phi'. split => [x|x|x y xNy|x y xy].
    + case: (altP (x =P j)) => xj //=. apply /set0Pn. exists s2. by rewrite !inE.
    + case: (altP (x =P j)) => xj //=.
      * apply connectedU_common_point with s2 => //. by rewrite !inE.
        apply add_edge_keep_connected_l => //. apply: contraNN iNj => s1x.
        by rewrite (disjE s1 i j s1i s1x). by apply connected_path.
      * apply (@add_edge_keep_connected_l G s2 s1) => //.
        -- by apply add_edge_connected_sym. 
        -- apply: contraNN xj => s1x. by rewrite (disjE s2 x j s1x s2j).
    + wlog yNj: x y xNy / y!=j.
      { move => H. case: (boolP (y==j)) => yj //=.
        - rewrite eq_sym in xNy. case: (altP (x=Pj)) => xj //=.
          + subst x. contrab.
          + move: (H y x xNy xj). rewrite (negbTE xj) yj => ?. by rewrite disjoint_sym.
        - move: (H x y xNy yj). by rewrite (negbTE yj). }
      rewrite (negbTE yNj). case: (altP (x=Pj)) => ? //=; [ subst x | by apply map2].
      rewrite disjointsU => //. by apply map2. apply /disjointP => a ap ay.
      rewrite inE in ap.
      move/(subsetP (HphiV1 _)) : (ay) => aV1.
      move/(subsetP pV2) : (ap) => aV2.
      have: a \in [set s1; s2] by rewrite -S12 !inE.
      rewrite !inE => /orP [/eqP as1|/eqP as2]; subst a.
      * apply: (@disjointE _ _ _ s1 dis) => //. by rewrite inE. 
      * by rewrite (disjE s2 j y s2j ay) eqxx in xNy. 
    + wlog yNj: x y xy / y!=j.
      { move => H. case: (boolP (y==j)) => yj //=.
        - simpl in xy. rewrite eq_sym in xy. case: (altP (x =P j)) => xj //=.
          + subst x. contrab.
          + move: (H y x xy xj). by rewrite (negbTE xj) yj neighborC. 
        - move: (H x y xy yj). by rewrite (negbTE yj). }
      rewrite (negbTE yNj). case: (altP (x =P j)) => xj.
      * subst x. case: (altP (y =P i)) => yi.
        -- subst y. apply/neighborP; exists z. exists s1. split => //; by rewrite ?inE // sgP.
        -- apply: (neighborW G (phi j) (phi y)); rewrite ?subsetUl //.
           apply: neighbor_del_edgeR (map3 _ _ xy).
           by rewrite (disjointFl (map2 _ _ yi)).
           by rewrite (disjointFl (map2 _ _ yNj)).
      * apply: neighbor_del_edge2 (map3 _ _ xy).
        by rewrite (disjointFl (map2 _ _ xj)).
        by rewrite (disjointFl (map2 _ _ yNj)). }

  case: (cases_without_edge K4free rmapphi) => [twobags|onebag].

  - apply caseA with s1 s2 phi => //.

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

    wlog [B1|B2]: s1 s2 s1Ns2 phi rmapphi {map1} HphiV1 s1i s2i notconi disjE C_def 
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
      { move/forall_inP => H. apply (W s2 s1 s2Ns1 phi) => //. 
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
      * case: (boolP (x==i)) => xi //=. 
        apply/set0Pn. exists s1. by rewrite -C_def inE connect0.
      * case: (boolP (x==i)) => xi //=.
        apply (@add_edge_keep_connected_l G s2 s1) => //.
        -- rewrite add_edge_connected_sym. apply map1.
        -- apply: contraNN xi => s1x. by rewrite (disjE s2 x i s1x s2i).
      * have disC1y: forall y, y!=i -> [disjoint C s1 & (phi y : {set G})].
        { move => y' y'Ni. apply /disjointP => z zCs1 zy'. (*TODO: with subset_trans *)
        move: (subsetP C1inphii z zCs1) => zi.
        apply: (@disjointE _ _ _ z (map2 y' i y'Ni)) => //. }
        case: (altP (x =P i)) => xNi //=; try subst x;
        case: (altP (y =P i)) => yNi //=; try subst y.
        -- by rewrite eqxx in xNy.
        -- by apply disC1y.
        -- rewrite disjoint_sym. by apply disC1y.
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
      pose phi' (k : K4) := if k==i then C s1
        else (if k==j then phi j :|: C s2 else phi k).
      have C1V1: C s1 \subset V1.
      { apply subset_trans with (mem (phi i)) => //. apply HphiV1. }
      have C2V1: C s2 \subset V1.
      { apply subset_trans with (mem (phi i)) => //. apply HphiV1. }
      suff rmapphi' : @minor_rmap (add_edge s1 s2) K4 phi'.
      { apply caseA with s1 s2 phi' => //.
        * rewrite /phi'. move => x. case: (boolP (x==i)) => xi //=.
          case: (boolP (x==j)) => xl //=. rewrite -(setUid V1). apply setUSS => //.
        * rewrite /phi'. exists i. exists j. rewrite (negbTE jNi) !eqxx.
          split; try rewrite -C_def !inE ?s1i ?s2i connect0; try rewrite eq_sym; done. }
      rewrite /phi'. split => [x|x|x y xNy|x y xy].
      * case: (boolP (x==i)) => xi; [|case: (boolP (x==j)) => xj //].
        -- apply/set0Pn. exists s1. rewrite -C_def inE s1i. apply connect0.
        -- apply/set0Pn. exists s2. rewrite -C_def !inE s2i. by rewrite connect0.
      * case: (boolP (x==i)) => xi => //; case:(boolP (x==j)) => xj //;
          try by apply add_edge_connected.
        rewrite setUC. apply: neighbor_connected => //. exact: add_edge_connected.
      * clear C1V1 C2V1.
        case:(altP (x =P i)) => xi; [|case:(altP (x =P j)) => xj]; try subst x.
        all: case:(altP (y =P i)) => yi; [|case:(altP (y =P j)) => yl];
          try subst y; try by rewrite eqxx in xNy.
        all: repeat match goal with
          | [H1 : is_true (?E \subset ?G), H2 : is_true (?F \subset ?G)
            |- is_true [disjoint ?A & ?B]] => match B with
              | context [?C :|: ?D] => rewrite disjoint_sym
              | _ => try done; match A with
                | context [?C :|: ?D] => apply disjointsU
                | context [E] => rewrite disjoint_sym
                | context [F] => rewrite disjoint_sym
                | _ => match B with
                  | context [E] => apply disjoint_transR with (mem (phi i)) => //
                  | context [F] => apply disjoint_transR with (mem (phi i)) => //
                  | _ =>  apply map2 => //; by rewrite eq_sym
        end end end end.
      * rewrite /= in xy.
        wlog yNj : x y xy / y != j; last rewrite (negbTE yNj).
        { move => W. case: {-}_ / (altP (y =P j)) => [E|H]; last exact: W.
          by rewrite neighborC W // -?E // eq_sym. }
        case:(altP (x =P i)) => xi. 
        { rewrite eq_sym -xi (negbTE xy). apply NCs1Pk.
          by rewrite inE (negbTE yNj) -xi eq_sym (negbTE xy). }
        case:(altP (x =P j)) => xj.
        { subst x. case: (altP (y =P i)) => [E|yNi].
          - apply/neighborP; exists s2; exists s1. 
            by rewrite /= s1Ns2 !eqxx !orbT -C_def !inE !connect0 // s1i s2i.
          - apply: neighborW (map3 _ _ xy) => //. exact: subsetUl. }
         case:(altP (y =P i)) => yi; last exact: map3.
         by rewrite neighborC NCs1Pk // inE (negbTE xi) (negbTE xj).
Qed.



Theorem TW2_of_K4F (G : sgraph) :
  K4_free G -> exists (T : forest) (B : T -> {set G}), sdecomp T G B /\ width B <= 3.
Proof.
  move: G. apply: (@nat_size_ind _ _ (fun G => #|G|)) => G Hind K4free. 
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
     + exact: K4_free_add_edge_sep_size2 SV12 _ _ S12 s1Ns2.
     + apply add_edge_separation => //; by rewrite -SV12 S12 !inE eqxx.
     + rewrite -SV12 S12. apply (@clique2 (add_edge s1 s2)) => /=.
       by rewrite !eqxx s1Ns2.
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
