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
  (*case: (@separatesNE x y set0).  ... connect not inductive*)
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
  ((V1 :|: V2 = setT) * (forall x1 x2, x1 \in V1 :\: V2 -> x2 \in V2 :\: V1 -> x1 -- x2 = false))%type.


Definition proper V1 V2 := V1 :\: V2 != set0 /\ V2 :\: V1 != set0.

Definition proper_separation V1 V2 := separation V1 V2 /\ proper V1 V2.

Lemma sparate_nonadjacent x y : x != y -> ~~ x -- y -> proper_separation [set~ x] [set~ y].
Proof.
  move => xDy xNy. split.
  - split.
    + apply/setP => z. rewrite !inE. apply: contraNT xDy. 
      rewrite negb_or !negbK. by case/andP => [/eqP<- /eqP<-].
    + move => x1 x2. rewrite !inE !negbK sg_sym => /andP[/eqP-> _] /andP[/eqP-> B].
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
      * (* z0 \in V2 => contradiction with split_at_first *)
        move: (z0z). rewrite [z0]H3 ?sgP //. by rewrite H4 mem_pcat path_end.
      * (* z0 \notin V2 => z0 \in V1 by Hset *)
        (* having to use in_setT/-Hsep is not nice *)
        apply: contraTT (in_setT z0) => C. by rewrite -Hsep inE (negbTE C).
Qed.


(*
Can't destroy an 'exists' if the final goal is a Type rather than a Prop.
Lemma patate2:
  forall (n:nat), (exists m:nat, n=m) -> (exists p, p=n).
Proof. move => a [b c]. Check a=b. Check (exists p, p=a).
Abort.
Lemma patate3 x y U V: 
  (exists p: Path x y, p \subset V) -> Path x x.
Proof. Check Path x y. Check Path x x.
(*move => [p H].*)
Abort.
Lemma patate x y U V: 
  (exists p: Path x y, p \subset V) -> exists p : Path x x, True.
Proof. Check Path x y. Check Path x x.
move => [p H]. exists (idp x). done.
Qed.
*)


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
  - apply/setP => x. rewrite !inE. by case: (x \in U).
  - move => u v.
    rewrite !inE !(negb_or,negb_and,negbK) -andbA => /andP[xU _] /and3P [U1 U2 _].
    apply: contraNF U1 => uv. move: (xU). rewrite /U -lock !inE => H.
    apply: connect_trans H _. apply: connect1. by rewrite /= !inE U2 uv HU.
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

Lemma minimal_separation x y : x != y -> ~~ x -- y -> 
  exists V1 V2, proper_separation V1 V2 /\ smallest separator (V1 :&: V2).
Proof.
  (* There exist finitely many proper separations, pick one for which
  [V1 :&: V2] is smallest. This is smallest separator since every
  separator can be extended to a proper separation *)
Admitted.

(** TOTHINK: the second assumption is half-redundant but makes for a nice statement *)
Lemma sseparator_neighbours V1 V2 s : 
  proper_separation V1 V2 -> smallest separator (V1 :&: V2) -> 
  s \in V1 :&: V2 -> exists x1 x2, [/\ x1 \in V1 :\: V2, x2 \in V2 :\: V1, s -- x1 & s -- x2].
Proof.
  (* - G is connected, since its smallest separator is nonempty
     - Wlog. [~~ s -- x1] for all elements of [C1 := V1:\:V2] ([V1] and [V2] are symmetric)
     - suff: [S' := V1 :&: V2 :\ s] is a separator. 
     - Let [x1 \in C1, x2 \in C2 := V2 :\: V1] and [p : Path x1 x2] be irredundant.
     - Let [s'] be the first vertex on [p] that is not in [C1]. Then [s' \in S']. *) 
Admitted.


(* TOTHINK: This definition really only makes sense for irredundant paths *)
Definition independent x y (p q : Path x y) := 
  forall z, z \in p -> z \in q -> z = x \/ z = y.

(** Note: This generalizes the corresponding lemma on checkpoints *)
Lemma avoid_nonseperator U x y : ~ separator U -> x \notin U -> y \notin U -> 
  exists2 p : Path x y, irred p & [disjoint p & U].
Proof.
  move => nsep_u xU yU. 
  case: (altP (x =P y)) => [?|A];first subst y.
  - exists (idp x); first exact: irred_idp. 
    rewrite (@eq_disjoint1 _ x) // => y. by rewrite mem_idp.
  - have/separatesNE/uPathRP : ~ separates x y U. admit. (* easy lemma *)
    case => // p irr_p. rewrite -disjoint_subset. by exists p.
Admitted.

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

End Separators.

Prenex Implicits separator.
Implicit Types G H : sgraph.

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

Lemma indepentent_paths G (V1 V2 : {set G}) : 
  proper_separation V1 V2 -> smallest separator (V1 :&: V2) -> 3 <= #|V1 :&: V2| ->
  exists x1 x2 (p1 p2 p3 : Path x1 x2), 
    [/\ irred p1, irred p2 & irred p3] /\
    [/\ x1 \in V1 :\: V2, x2 \in V2 :\: V1, 
       independent p1 p2, independent p2 p3 & independent p3 p1].
Proof.
  set S := V1 :&: V2.
  set C1 := V1 :\: V2.
  set C2 := V2 :\: V1.
  (* - take some [u \in C1] and [v \in C2] and some irredundant [q1 : Path u v] 
       visiting exactly one element from [S], say [s1] [sseparator_uniq] 
     - removing [s1] yields a connected graph where the remainder of [S] 
       is again a minimal separator. 
     - this yields a path [q2] containing [s2 \in S] different from [s1]
     - traversing [q2] in both directions from [s2] up to the first vertex
       shared with [q1] yields vertices [u',v'] and two indepentent 
       u'v'-paths [q1'] and [q2']
     - obtain a path avoiding [{s1,s2}] containing [s3].
     - traverse this path to the first vertices shared with [q1' :|: q2']
     - take the first shared vertex in [C1] to be [x1] and likewise for [x2] 
   Note: It may be useful to prove the case [2 <= #|S|] as a separate lemma *)
Admitted.

Lemma K4_of_separators (G : sgraph) : 
  3 < #|G| -> (forall S : {set G}, separator S -> 2 < #|S|) -> minor G K4.
Proof.
  (* If [G] is complete, it clearly has [K4] as a minor, so assume
  distinct [x] [y] that are not adjacent. Let [V1,V2] be given as by
  Lemma [minimal_separation].

  By assumption, [3 <= #|V1 :&: V|]. Hence, hence we can use the
  [indepentent_paths] lemma. Moreover [~: [set x;y]] is connected, so
  there is a fourth (independent) path connecting two of the three
  paths. This yields K4. 
*)
Admitted.

Theorem TW2_of_K4F (G : sgraph) :
  K4_free G -> exists (T : forest) (B : T -> {set G}), sdecomp T G B /\ width B <= 3.
Proof.
Admitted.


