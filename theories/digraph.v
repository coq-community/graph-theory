Require Import Setoid CMorphisms.
Require Relation_Definitions.
From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries bij.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Directed Graphs  *)

(** This file contains a number of constructions and lemmas to reason about
paths in (finite) graphs. The most basic notion of a graph is just a type
packaged together with a relation. *)

(** The underlying type could be more permissive e.g. [countType] or even
[eqType]. However, this would required a more complicated setup in order to
ensure that the coercions to [countType] and [finType] (for finite graphs) are
not just convertible but indeed equal. Otherwise, some automation using [auto]
fails. So far, we only deal with with finite graphs, so "telescopes" suffice *)

Record relType := RelType { rel_car :> finType; edge_rel : rel rel_car }.
Notation "x -- y" := (edge_rel x y) (at level 30).
Prenex Implicits edge_rel.

(** maintain the notation [x -- y] under simplification *)

Arguments edge_rel : simpl never.

(** For [G : relType] and [x, y : G] we define two auxiliary notions: *) 

(** [pathp x y p] == the list (x::p) is an xy-path in G. *)
  
(** [upath x y p] == the list (x::p) is an irredundant xy-path in G. *)


(** Due to the asymmetry in the definitions of of [path],[pathp], and [upath], these
are ill-suited for the symmetry reasoning prevalent in graph theory. We remedy
this by providing a type family of packaged paths [Path x y] which abstracts
away this asymmetry. We then lift many of the lemmas from the path library to
the setting of simple graphs. *)

(** ** Unpackaged Paths *)

Section PathP.
Variable (T : relType).
Implicit Types (x y : T) (p : seq T).

Definition pathp x y p := path (@edge_rel T) x p && (last x p == y).

Lemma pathpW y x p : pathp x y p -> path edge_rel x p.
Proof. by case/andP. Qed.

Lemma pathp_last y x p : pathp x y p -> last x p = y.
Proof. by case/andP => _ /eqP->. Qed.

Lemma pathp_cat x y p1 p2 : 
  pathp x y (p1++p2) = (pathp x (last x p1) p1) && (pathp (last x p1) y p2).
Proof. by rewrite {1}/pathp cat_path last_cat /pathp eqxx andbT /= -andbA. Qed.

Lemma pathp_concat x y z p q : 
  pathp x y p -> pathp y z q -> pathp x z (p++q).
Proof. 
  move => /andP[A B] /andP [C D]. 
  rewrite pathp_cat (eqP B) /pathp -andbA. exact/and4P.
Qed.

Lemma pathpxx x : pathp x x [::].
Proof. exact: eqxx. Qed.

Lemma pathp_nil x y : pathp x y [::] -> x = y.
Proof. by case/andP => _ /eqP. Qed.

Lemma pathp_cons x y z p : 
  pathp x y (z :: p) = x -- z && pathp z y p. 
Proof. by rewrite -cat1s pathp_cat {1}/pathp /= eqxx !andbT. Qed.

Lemma pathp_rcons x y z p: pathp x y (rcons p z) -> y = z.
Proof. case/andP => _ /eqP <-. exact: last_rcons. Qed.

Lemma rcons_pathp x y p : path edge_rel x (rcons p y) = pathp x y (rcons p y).
Proof. by rewrite /pathp last_rcons eqxx andbT. Qed.

CoInductive pathp_split z x y : seq T -> Prop := 
  PPSplit p1 p2 : pathp x z p1 -> pathp z y p2 -> pathp_split z x y (p1 ++ p2).

Lemma ppsplitP z x y p : z \in x :: p -> pathp x y p -> pathp_split z x y p.
Proof. 
  case/splitPl => p1 p2 /eqP H1 /andP [H2 H3]. 
  rewrite cat_path last_cat in H2 H3. case/andP : H2 => H2 H2'.
  constructor; last rewrite -(eqP H1); exact/andP. 
Qed.

Lemma pathp_shorten x y p :
  pathp x y p -> exists p', [/\ pathp x y p', uniq (x::p') & {subset p' <= p}].
Proof. case/andP. case/shortenP => p' *. by exists p'. Qed.

(** Irredundant paths *)

Definition upath x y p := uniq (x::p) && pathp x y p.

Lemma upathW x y p : upath x y p -> pathp x y p.
Proof. by case/andP. Qed.

Lemma upathWW x y p : upath x y p -> path edge_rel x p.
Proof. by move/upathW/pathpW. Qed.

Lemma upath_uniq x y p : upath x y p -> uniq (x::p).
Proof. by case/andP. Qed.

Lemma upath_cons x y z p : 
  upath x y (z::p) = [&& x -- z, x \notin (z::p) & upath z y p].
Proof. 
  rewrite /upath pathp_cons [z::p]lock /= -lock.
  case: (x -- z) => //. by case (uniq _).
Qed.

Lemma upath_consE x y z p : 
  upath x y (z :: p) -> [/\ x -- z, x \notin z :: p & upath z y p].
Proof. rewrite upath_cons. by move/and3P. Qed.

Lemma upath_nil x p : upath x x p -> p = [::].
Proof. case: p => //= a p /and3P[/= A B C]. by rewrite -(eqP C) mem_last in A. Qed.

End PathP.

(** Lifting Lemmas for unpackaged paths *)

Lemma subrel_pathp (T : finType) (e1 e2 : rel T) (x y : T) (p : seq T) :
  subrel e1 e2 -> @pathp (RelType e1) x y p -> @pathp (RelType e2) x y p.
Proof. 
  move => sub12. elim: p x => //= z p IHp x. rewrite !pathp_cons => /andP [A B].
  apply/andP;split; [exact: sub12 | exact: IHp].
Qed.

Lemma lift_pathp_on (G H : relType) (f : G -> H) a b p' : 
  (forall x y, f x \in f a :: p' -> f y \in f a :: p' -> f x -- f y -> x -- y) -> injective f -> 
  pathp (f a) (f b) p' -> {subset p' <= codom f} -> exists p, pathp a b p /\ map f p = p'.
Proof. 
  move => A I /andP [B /eqP C] D.  case: (lift_path A B D) => p [p1 p2]; subst. 
  exists p. split => //. apply/andP. split => //. rewrite last_map in C. by rewrite (I _ _ C).
Qed.

Lemma lift_pathp (G H : relType) (f : G -> H) a b p' : 
  (forall x y, f x -- f y -> x -- y) -> injective f -> 
  pathp (f a) (f b) p' -> {subset p' <= codom f} -> exists p, pathp a b p /\ map f p = p'.
Proof. move => I. apply: lift_pathp_on. auto. Qed.

Lemma lift_upath_on (G H : relType) (f : G -> H) a b p' : 
  (forall x y, f x \in f a :: p' -> f y \in f a :: p' -> f x -- f y -> x -- y) -> injective f -> 
  upath (f a) (f b) p' -> {subset p' <= codom f} -> exists p, upath a b p /\ map f p = p'.
Proof.
  move => A B /andP [C D] E. case: (lift_pathp_on A B D E) => p [p1 p2].
  exists p. split => //. apply/andP. split => //. by rewrite -(map_inj_uniq B) /= p2.
Qed.

Lemma lift_upath (G H : relType) (f : G -> H) a b p' : 
  (forall x y, f x -- f y -> x -- y) -> injective f -> 
  upath (f a) (f b) p' -> {subset p' <= codom f} -> exists p, upath a b p /\ map f p = p'.
Proof. move => I. apply: lift_upath_on. auto. Qed.


(** ** Packaged paths *)

(** We now define packaged paths (i.e., a vertex-indexed collection of
types [Path x y] whose elements are the paths between [x] and [y]). In
particular, this abstracts from the asymmetry in [spath x y p] which
states that [x::p] is an xy-path (paths are never empty). *)

Section Pack.
Variables (T : relType).
Implicit Types x y z : T.

Section PathDef.
  Variables (x y : T).

  Record Path : predArgType := { pval : seq T; _ : pathp x y pval }.

  Canonical Path_subType := [subType for pval].
  Definition Path_eqMixin := Eval hnf in [eqMixin of Path by <:].
  Canonical Path_eqType := Eval hnf in EqType Path Path_eqMixin.
  Definition Path_choiceMixin := Eval hnf in [choiceMixin of Path by <:].
  Canonical Path_choiceType := Eval hnf in ChoiceType Path Path_choiceMixin.
  Definition Path_countMixin := Eval hnf in [countMixin of Path by <:].
  Canonical Path_countType := Eval hnf in CountType Path Path_countMixin.

  Record UPath : predArgType := { uval : seq T; _ : upath x y uval }.

  Canonical UPath_subType := [subType for uval].
  Definition UPath_eqMixin := Eval hnf in [eqMixin of UPath by <:].
  Canonical UPath_eqType := Eval hnf in EqType UPath UPath_eqMixin.
  Definition UPath_choiceMixin := Eval hnf in [choiceMixin of UPath by <:].
  Canonical UPath_choiceType := Eval hnf in ChoiceType UPath UPath_choiceMixin.
  Definition UPath_countMixin := Eval hnf in [countMixin of UPath by <:].
  Canonical UPath_countType := Eval hnf in CountType UPath UPath_countMixin.

End PathDef.
End Pack.

Section PathOps.
Variables (T : relType) (x y z : T) (p : Path x y) (q : Path y z).

Definition nodes := locked (x :: val p).
Lemma nodesE : nodes = x :: val p. by rewrite /nodes -lock. Qed.
Definition irred := uniq nodes.
Lemma irredE : irred = uniq nodes. by []. Qed.
Definition tail := val p.

Definition pcat_proof := pathp_concat (valP p) (valP q).
Definition pcat : Path x z := Sub (val p ++ val q) pcat_proof.

Lemma path_last: last x (val p) = y.
Proof. move: (valP p). exact: pathp_last. Qed.

End PathOps.

Definition in_nodes (T : relType) (x y : T) (p : Path x y) : collective_pred T := 
  [pred u | u \in nodes p].
Canonical Path_predType (T : relType) (x y :T) := 
  Eval hnf in @PredType T (Path x y) (@in_nodes T x y).
Coercion in_nodes : Path >-> collective_pred.

Section PathTheory.
Variable (G : relType).
Implicit Types (x y z u : G).

Lemma nodes_eqE x y (p q : Path x y) : (nodes p == nodes q) = (p == q).
Proof.
  case: q p => q pth_q [p pth_p]. 
  by rewrite !nodesE -val_eqE /= eqseq_cons eqxx.
Qed.

Lemma mem_path x y (p : Path x y) u : u \in p = (u \in nodes p).
Proof. by rewrite in_collective. Qed.

Section Fixed.
Variables (x y z : G) (p : Path x y) (q : Path y z).

Lemma in_tail : z != x -> z \in p -> z \in tail p.
Proof. move => A. by rewrite mem_path nodesE inE (negbTE A). Qed.

Lemma path_end : y \in p. 
Proof. by rewrite mem_path nodesE -[in X in X \in _](path_last p) mem_last. Qed.

Lemma path_begin : x \in p.
Proof. by rewrite mem_path nodesE mem_head. Qed.

Lemma mem_pcatT u : (u \in pcat p q) = (u \in p) || (u \in tail q).
Proof. by rewrite !mem_path !nodesE !inE mem_cat -orbA. Qed.

Lemma tailW : {subset tail q <= q}.
Proof. move => u. rewrite mem_path nodesE. exact: mem_tail. Qed.

Lemma mem_pcat u :  (u \in pcat p q) = (u \in p) || (u \in q).
Proof. 
  rewrite mem_pcatT. case A: (u \in p) => //=. 
  rewrite mem_path !nodesE inE (_ : u == y = false) //. 
  apply: contraFF A => /eqP->. exact: path_end. 
Qed.

Lemma nodes_pcat : nodes (pcat p q) = nodes p ++ behead (nodes q).
Proof. by rewrite !nodesE. Qed.

End Fixed.

Lemma pcatA u v x y (p : Path u v) (q : Path v x) (r : Path x y) : 
  pcat (pcat p q) r = pcat p (pcat q r).
Proof. apply/eqP. by rewrite -val_eqE /= catA. Qed.

(** The one-node path *)

Definition idp (u : G) := Build_Path (pathpxx u).

Lemma mem_idp (x u : G) : (x \in idp u) = (x == u).
Proof. by rewrite mem_path nodesE !inE. Qed.

Lemma irred_idp (x : G) : irred (idp x).
Proof. by rewrite irredE nodesE. Qed.

Lemma pcat_idL (x y : G) (p : Path x y) : 
  pcat (idp x) p = p.
Proof. exact: val_inj. Qed.

Lemma pcat_idR (x y : G) (p : Path x y) : 
  pcat p (idp y) = p.
Proof. apply: val_inj => /=. by rewrite cats0. Qed.

Lemma irredxx (x : G) (p : Path x x) : irred p -> p = idp x.
Proof.
  rewrite irredE /tail (lock uniq); case: p => p p_pth /=.
  rewrite nodesE /= -lock => p_uniq. apply/val_inj => /=.
  by have /upath_nil-> : upath x x p by rewrite /upath p_uniq p_pth.
Qed.

(** Paths with a single edge using an injection from (proofs of) [x -- y] *)

Lemma edgep_proof x y (xy : x -- y) : pathp x y [:: y]. 
Proof. by rewrite pathp_cons xy pathpxx. Qed.

Definition edgep x y (xy : x -- y) := Build_Path (edgep_proof xy).

Lemma mem_edgep x y z (xy : x -- y) :
  z \in edgep xy = (z == x) || (z == y).
Proof. by rewrite mem_path nodesE !inE. Qed.

Lemma mem_pcat_edgeL x y z (xy : x -- y) (p : Path y z) u : 
  (u \in pcat (edgep xy) p) = (u == x) || (u \in p).
Proof.
  rewrite mem_pcat mem_edgep. case: (altP (u =P y)) => //= ->. by rewrite path_begin.
Qed.

Lemma mem_pcat_edgeR x y z (yz : y -- z) (p : Path x y) u : 
  (u \in pcat p (edgep yz)) = (u == z) || (u \in p).
Proof.
  rewrite mem_pcat mem_edgep. 
  case: (altP (u =P y)) => //= [->|]; by rewrite ?path_end 1?orbC.
Qed.

Lemma edgeLP x y z (xy : x -- y) (p : Path y z) u : 
  reflect (u = x \/ u \in p) (u \in pcat (edgep xy) p).
Proof. 
  rewrite mem_pcat mem_edgep -orbA. apply: (iffP or3P) => [|[->|->]]; rewrite ?eqxx. 
  1: case => [/eqP->|/eqP->|->]; rewrite ?inE. all: by firstorder using path_begin.
Qed.

(** These are easier to prove by breaking the abstraction barrier than by using
[irred_cat] below. *)

Lemma irred_edge x y (xy: x -- y) : irred (edgep xy) = (x != y).
Proof. by rewrite irredE nodesE /= inE andbT. Qed.

Lemma irred_edgeL y x z1 (xz1 : x -- z1) (p : Path z1 y) : 
  irred (pcat (edgep xz1) p) = (x \notin p) && irred p.
Proof. case: p => p pth_p. by rewrite !irredE /= mem_path !nodesE /=. Qed.

Lemma irred_edgeR y x z (yz : y -- z) (p : Path x y) : 
  irred (pcat p (edgep yz)) = (z \notin p) && irred p.
Proof.
  rewrite !irredE !mem_path !nodesE /= cats1 rcons_uniq mem_rcons !inE.
  rewrite eq_sym !negb_or. case: (x \notin pval p); by rewrite andbA.
Qed.

(** Induction principles for packaged paths *)

Lemma Path_ind (P : forall x x0 : G, Path x x0 -> Type) (y : G) (x : G) (p : Path x y) :
  P y y (idp y) ->
  (forall (x z : G) (p : Path z y) (xz : x -- z), P z y p -> P x y (pcat (edgep xz) p)) ->
  P x y p.
Proof. 
  move => Hbase Hstep. case: p => [p pth_p]. 
  elim: p x pth_p => [|z p IH] x A. 
  - have ?: x = y. { exact: pathp_nil. }
    subst y. rewrite [Build_Path _](_ : _ = idp x) //. exact: val_inj.
  - move: {-}(A). rewrite pathp_cons => /andP [xz B2].
    have -> : Build_Path A = 
             (pcat (edgep xz) (Build_Path B2)) by exact: val_inj.
    apply: Hstep. exact: IH.
Qed.

Lemma irred_ind P (y : G) :
  P y y (idp y) ->
  (forall x z (p : Path z y) (xz : x -- z),
      irred p -> x \notin p -> P z y p -> P x y (pcat (edgep xz) p)) ->
  forall x (p : Path x y), irred p -> P x y p.
Proof.
  move => Hbase Hstep x p.
  pattern x,y,p. apply: Path_ind => // {x p} x z p xz IH. 
  rewrite irred_edgeL => /andP[A B]. by apply: Hstep; auto.
Qed.


Lemma path_closed (A : pred G) x y (p : Path x y) : 
  x \in A -> (forall y z, y \in A -> y -- z -> z \in A) -> {subset p <= A}.
Proof.
  move => xA clos_A. move: xA. pattern x,y,p. apply: Path_ind => {x p}.
  - move => yA z. by rewrite mem_idp => /eqP->.
  - move => x z p xz IH xA u. rewrite mem_pcat mem_edgep -orbA.
    have ? : z \in A by exact: clos_A xz.
    case/or3P => [/eqP->|/eqP->|] //. exact: IH. 
Qed.

Lemma uncycle x y (p : Path x y) :
  exists2 p' : Path x y, {subset p' <= p} & irred p'.
Proof.
  case: p => p pth_p. case/pathp_shorten : (pth_p) => p' [A B C].
  exists (Build_Path A). move => z. rewrite !mem_path !nodesE !SubK.
  + rewrite !inE. case/predU1P => [->|/C ->] //. by rewrite eqxx.
  + by rewrite /irred nodesE.
Qed.


End PathTheory.
Definition inE := (inE,mem_pcat,path_begin,path_end).

(** NOTE: Up to here, nothing depends on the vertex type being finite. The
constuctions below make use of functions that are only defined on finite types,
e.g., [connect] or [#|G|] *)

(* 
Record diGraph := DiGraph { di_vertex : finType; 
                            di_edge : rel di_vertex }.

Canonical digraph_relType (D : diGraph) := RelType (@di_edge D).
Coercion digraph_relType : diGraph >-> relType.
Coercion di_vertex : diGraph >-> finType.
Prenex Implicits di_edge. 
*)

(** The simple setup above causes the coercion to [finType] to be different from
(but convertible to) the coercions to [choiceType]. This causes [auto] and hence
[trivial] and [by] to fail. *)

Notation diGraph := relType.
Notation DiGraph := RelType.
Notation di_edge := edge_rel (only parsing).
Goal forall (T : diGraph) (A : pred T), A \subset [set: T]. by []. Qed.

Section DiGraphTheory.
Variables (D : diGraph).
Implicit Types (x y : D).

Lemma upath_size x y p : upath x y p -> size p < #|D|.
Proof. move=> /upath_uniq/card_uniqP/= <-. exact: max_card. Qed.

CoInductive usplit z x y : seq D -> Prop := 
  USplit p1 p2 : upath x z p1 -> upath z y p2 -> [disjoint x::p1 & p2]
                 -> usplit z x y (p1 ++ p2).

Lemma usplitP z x y p : z \in x :: p -> upath x y p -> usplit z x y p.
Proof. 
  move => in_p /andP [U P]. case: (ppsplitP in_p P) U  => p1 p2 sp1 sp2.
  rewrite -cat_cons cat_uniq -disjoint_has disjoint_sym => /and3P [? C ?].
  suff H: z \notin p2 by constructor.
  apply/negP. apply: disjointE C _. by rewrite -(pathp_last sp1) // mem_last. 
Qed.

Lemma upathP x y : reflect (exists p, upath x y p) (connect di_edge x y).
Proof.
  apply: (iffP connectP) => [[p p1 p2]|[p /and3P [p1 p2 /eqP p3]]]; last by exists p.
  exists (shorten x p). case/shortenP : p1 p2 => p' ? ? _ /esym/eqP ?. exact/and3P. 
Qed.

Lemma pathpP x y : reflect (exists p, pathp x y p) (connect di_edge x y).
Proof. 
  apply: (iffP idP) => [|[p] /andP[A /eqP B]]; last by apply/connectP; exists p.
  case/upathP => p /upathW ?. by exists p.
Qed.

(* Set Printing All. *)

Section Fixed.
Variables (x y z : D) (p : Path x y) (q : Path y z).

(** NOTE: [rewrite mem_pcat] requres [digraph_relType] to be canonical *)
Lemma subset_pcatL : p \subset pcat p q.
Proof. apply/subsetP => u. by rewrite mem_pcat => ->. Qed.

Lemma subset_pcatR : q \subset pcat p q.
Proof. apply/subsetP => u. by rewrite mem_pcat => ->. Qed.

Lemma pcat_subset (A : pred D) : p \subset A -> q \subset A -> pcat p q \subset A.
Proof. 
  move => /subsetP Hp /subsetP Hq. apply/subsetP => u. 
  rewrite !mem_pcat. case/orP; [exact: Hp|exact: Hq].
Qed.

(** This is easy to prove and in some contetxs exactly what is needed. However,
it introduces an unpleasant asymmetry between [p] and [q]. *)
Lemma irred_catD :
  irred (pcat p q) = [&& irred p, irred q & [disjoint p & tail q]].
Proof.
  rewrite /irred {1}/nodes -lock /pcat SubK -cat_cons cat_uniq.
  rewrite -disjoint_has disjoint_sym -nodesE.
  case A : [disjoint _ & _] => //. case: (uniq (nodes p)) => //=. rewrite nodesE /=.
  case: (uniq _) => //=. by rewrite !andbT (disjointFr A _) // path_end.
Qed.

(** This lemma is more symmetric than [irred_catD], but the set equality is
sometimes cumbersome to use. *)
Lemma irred_cat : 
  irred (pcat p q) = [&& irred p, irred q & [set u : D in p | u \in q] == [set y]].
Proof.
  rewrite /irred {1}nodesE (lock uniq) /= -lock -cat_cons -nodesE cat_uniq.
  congr (_ && _). rewrite (nodesE q) /=. case: uniq => //; rewrite !andbT.
  apply/hasPn/andP.
  - move=> H. split; first by apply/negP=>/H/=; rewrite path_end.
    apply/eqP/setP=> u; rewrite !inE.
    apply/andP/eqP; last by [move=>->; rewrite path_begin path_end].
    case=> u_p. rewrite mem_path nodesE inE =>/orP[/eqP//|/H/=]. by rewrite u_p.
  - case=> zNTq. rewrite eqEsubset =>/andP[/subsetP sub _].
    move=> u u_q /=. apply/negP=> u_p.
    case/(_ u _)/Wrap: sub; rewrite inE.
    + rewrite u_p /=; exact: tailW.
    + apply/negP; by apply: contraNneq zNTq =>{1}<-.
Qed.

(** Introduction and elimination lemmas for [irred (pcat p q)] that avoid the
use of set equality *)
Lemma irred_catI : 
  (forall k : D, k \in p -> k \in q -> k = y) -> irred p -> irred q -> irred (pcat p q).
Proof. 
  move => H Ip Iq. rewrite irred_cat Ip Iq /=. apply/eqP/setP => k.
  rewrite !inE. apply/andP/eqP => [[]|->]. exact: H. by rewrite path_begin path_end.
Qed.

(** TODO: This lemma should be used instead of the [irred_cat] where appropriate *)
Lemma irred_catE : 
  irred (pcat p q) -> [/\ irred p, irred q & forall k, k \in p -> k \in q -> k = y].
Proof.
  rewrite irred_cat. case/and3P => [? ? A]. split => // k K1 K2.
  apply/eqP. move/eqP/setP/(_ k) : A. by rewrite !inE K1 K2. 
Qed.

End Fixed.

Lemma connect_irredP x y : 
  reflect (exists p : Path x y, irred p) (connect di_edge x y).
Proof.
  apply: (iffP (upathP _ _)) => [[p /andP [U P]]|[p I]].
  + exists (Sub p P).  by rewrite /irred nodesE.
  + exists (val p). apply/andP;split; by [rewrite /irred nodesE in I| exact: valP].
Qed.

Lemma Path_connect x y (p : Path x y) : connect di_edge x y.
Proof. apply/pathpP. exists (val p). exact: valP. Qed.


(** *** Splitting Paths **)

Lemma splitL x y (p : Path x y) : 
  x != y -> exists z xz (p' : Path z y), p = pcat (edgep xz) p' /\ p' =i tail p.
Proof.
  move => xy. case: p => p. elim: p x xy => [|a p IH] x xy H.
  - move/pathp_nil : (H) => ?. subst y. by rewrite eqxx in xy.
  - move: (H) => H'. move: H. rewrite pathp_cons => /andP [A B].
    exists a. exists A. exists (Build_Path B). split; first exact: val_inj.
    move => w. by rewrite in_collective nodesE !inE.
Qed.

Lemma splitR x y (p : Path x y) : 
  x != y -> exists z (p' : Path x z) zy, p = pcat p' (edgep zy).
Proof.
  move => xy. case: p. elim/last_ind => [|p a IH] H.
  - move/pathp_nil : (H) => ?. subst y. by rewrite eqxx in xy.
  - move: (H) => H'. 
    case/andP : H. rewrite rcons_path => /andP [A B] C.
    have sP : pathp x (last x p) p by rewrite /pathp A eqxx.
    move: (pathp_rcons H') => ?; subst a.
    exists (last x p). exists (Build_Path sP). exists B. 
    apply: val_inj => /=. by rewrite cats1.
Qed.

CoInductive psplit z x y : Path x y -> Prop := 
  PSplit (p1 : Path x z) (p2 : Path z y) : psplit z (pcat p1 p2).

Lemma psplitP z x y (p : Path x y) : z \in p -> psplit z p.
Proof. 
  move: (valP p) => pth_p in_p. rewrite mem_path nodesE in in_p.
  case/(ppsplitP in_p) E : _ / pth_p => [p1 p2 P1 P2].
  have -> : p = pcat (Sub p1 P1) (Sub p2 P2) by exact: val_inj.
  by constructor.
Qed.

(** This should be the canonical way to split irredundant paths *)
CoInductive isplit z x y : Path x y -> Prop := 
  ISplit (p1 : Path x z) (p2 : Path z y) : 
    irred p1 -> irred p2 -> (forall k, k \in p1 -> k \in p2 -> k = z) -> isplit z (pcat p1 p2).

Lemma isplitP z x y (p : Path x y) : irred p -> z \in p -> isplit z p.
Proof.
  move => I in_p. case/psplitP : _ / in_p I => p1 p2 /irred_catE [*]. 
  by constructor.
Qed.

Lemma split_at_first_aux {A : pred D} x y (p : seq D) k : 
    pathp x y p -> k \in A -> k \in x::p -> 
    exists z p1 p2, [/\ p = p1 ++ p2, pathp x z p1, pathp z y p2, z \in A 
                & forall z', z' \in A -> z' \in x::p1 -> z' = z].
Proof.
  move => pth_p in_A in_p. 
  pose n := find A (x::p). 
  pose p1 := take n p.
  pose p2 := drop n p.
  pose z := last x p1.
  have def_p : p = p1 ++ p2 by rewrite cat_take_drop.
  move: pth_p. rewrite {1}def_p pathp_cat. case/andP => pth_p1 pth_p2.
  have X : has A (x::p) by apply/hasP; exists k.
  exists z. exists p1. exists p2. split => //.
  - suff -> : z = nth x (x :: p) (find A (x :: p)) by exact: nth_find.
    rewrite /z /p1 last_take // /n -ltnS. by rewrite has_find in X. 
  - move => z' in_A' in_p'. 
    have has_p1 : has A (x::p1) by (apply/hasP;exists z').
    rewrite /z (last_nth x) -[z'](nth_index x in_p').
    suff -> : index z' (x::p1) = size p1 by [].
    apply/eqP. rewrite eqn_leq. apply/andP;split.
    + by rewrite -ltnS -[(size p1).+1]/(size (x::p1)) index_mem.
    + rewrite leqNgt. apply: contraTN in_A' => C.
      rewrite -[z'](nth_index x in_p') unfold_in before_find //.
      apply: leq_trans C _. 
      have -> : find A (x :: p1) = n by rewrite /n def_p -cat_cons find_cat has_p1. 
      rewrite size_take. by case: (ltngtP n (size p)) => [|/ltnW|->].
Qed.


Lemma split_at_first {A : pred D} x y (p : Path x y) k :
  k \in A -> k \in p ->
  exists z (p1 : Path x z) (p2 : Path z y), 
    [/\ p = pcat p1 p2, z \in A & forall z', z' \in A -> z' \in p1 -> z' = z].
Proof.
  case: p => p pth_p /= kA kp. rewrite mem_path nodesE in kp.
  case: (split_at_first_aux pth_p kA kp) => z [p1] [p2] [def_p pth_p1 pth_p2 A1 A2].
  exists z. exists (Build_Path pth_p1). exists (Build_Path pth_p2). split => //.
  + subst p. exact: val_inj.
  + move => ?. rewrite mem_path nodesE. exact: A2.
Qed.

Lemma irred_is_edge (x y : D) (p : Path x y) :
  irred p -> x != y -> {subset p <= [set x;y]} -> exists xy : x -- y, p = edgep xy.
Proof.
  move => Ip xDy sub_xy. case: (splitL p xDy) => y' [xy'] [p' [def_p _]]. 
  subst. move: Ip. rewrite irred_edgeL => /andP[xp' Ip'].
  suff ? : y' = y. { subst. rewrite [p']irredxx // pcat_idR. by exists xy'. }
  move/(_ y') : sub_xy. rewrite mem_pcat path_begin orbT !inE => /(_ isT). 
  case/orP => /eqP ?; subst => //. by rewrite path_begin in xp'.
Qed.

(** *** Between nodes (reflection lemmas) *)

(** NOTE: need to require either x != y or x \in A since packaged
paths are never empty *)
Lemma connect_irredRP {A : pred D} x y : x != y ->
  reflect (exists2 p: Path x y, irred p & p \subset A) 
          (connect (restrict A edge_rel) x y).
Proof.
  move => Hxy. apply: (iffP connect_restrictP) => //.
  - case => p [pth_p lst_p uniq_p sub_A]. 
    have pvalP : pathp x y p by rewrite /pathp pth_p lst_p.
    exists (Build_Path pvalP); first by rewrite irredE nodesE.
    apply/subsetP => z. rewrite mem_path nodesE. exact: sub_A.
  - case => p [Ip /subsetP subA]; exists (val p). 
    by case/andP : (valP p) => ? /eqP ?; rewrite -nodesE -irredE.
Qed.

(* This is only useful if the [x = y] case does not require [x \in A] *)
Lemma connect_restrict_case x y (A : pred D) : 
  connect (restrict A edge_rel) x y -> 
  x = y \/ [/\ x != y, x \in A, y \in A & connect (restrict A edge_rel) x y].
Proof.
  case: (altP (x =P y)) => [|? conn]; first by left. 
  case/connect_irredRP : (conn) => // p _ /subsetP subA. 
  right; split => //; by rewrite subA ?path_end ?path_begin.
Qed.

Lemma connectRI (A : pred D) x y (p : Path x y) :
  {subset p <= A} -> connect (restrict A edge_rel) x y.
Proof. 
  case: (boolP (x == y)) => [/eqP ?|]; first by subst y; rewrite connect0. 
  move => xy subA. apply/connect_irredRP => //. case: (uncycle p) => p' p1 p2.
  exists p' => //. apply/subsetP => z /p1. exact: subA.
Qed.

End DiGraphTheory.
Arguments connect_irredRP {D A x y}.
Arguments connectRI {D A x y} p.
Arguments irred_is_edge [D x y] p.

Section DiPathTheory.
Variable (G : diGraph).
Implicit Types (x y z : G).

Section Finite.
  Variables x y : G.
  Notation UPath := (UPath x y).

  Definition UPath_tuple (up : UPath) : {n : 'I_#|G| & n.-tuple G} :=
    let (p, Up) := up in existT _ (Ordinal (upath_size Up)) (in_tuple p).
  Definition tuple_UPath (s : {n : 'I_#|G| & n.-tuple G}) : option UPath :=
    let (_, p) := s in match boolP (upath x y p) with
      | AltTrue Up => Some (Sub (val p) Up)
      | AltFalse _ => None
    end.
  Lemma UPath_tupleK : pcancel UPath_tuple tuple_UPath.
  Proof.
    move=> [/= p Up].
    case: {-}_ / boolP; last by rewrite Up.
    by move=> Up'; rewrite (bool_irrelevance Up' Up).
  Qed.

  Definition UPath_finMixin := Eval hnf in PcanFinMixin UPath_tupleK.
  Canonical UPath_finType := Eval hnf in FinType UPath UPath_finMixin.

  Definition UPathW (up : UPath) : Path x y := let (p, Up) := up in Sub p (upathW Up).
  Coercion UPathW : UPath >-> Path.
End Finite.

(** ** Packaged Irredundant Paths

Quantification over all paths is, a priori, undecidable. However,
quantification over irredundant paths is decidable and usually
sufficient. We define a type family of irredundant paths and endow it
with a finType structure. *)

Section IPath.
  Variables (x y : G).
  Record IPath : predArgType := { ival : Path x y; ivalP : irred ival }.
  
  Canonical IPath_subType := [subType for ival].
  Definition IPath_eqMixin := Eval hnf in [eqMixin of IPath by <:].
  Canonical IPath_eqType := Eval hnf in EqType IPath IPath_eqMixin.
  Definition IPath_choiceMixin := Eval hnf in [choiceMixin of IPath by <:].
  Canonical IPath_choiceType := Eval hnf in ChoiceType IPath IPath_choiceMixin.
  Definition IPath_countMixin := Eval hnf in [countMixin of IPath by <:].
  Canonical IPath_countType := Eval hnf in CountType IPath IPath_countMixin.

  Lemma upath_irred p (Up : upath x y p) : irred (Build_Path (upathW Up)).
  Proof. rewrite irredE nodesE. exact: upath_uniq Up. Qed.

  Lemma irred_upath (p : Path x y) : irred p -> upath x y (val p).
  Proof. 
    move => Ip. rewrite /upath irredE nodesE in Ip *. rewrite Ip /=. 
    by case: p {Ip}.
  Qed.

  Definition irred_of (p0 : UPath x y) : IPath := 
    let (p,Up) := p0 in (Sub (Build_Path (upathW Up)) (upath_irred Up)).
  Definition upath_of (p0 : IPath) : UPath x y := 
    let (p,Ip) := p0 in Sub (val p) (irred_upath Ip).

  Lemma can_irred_of : cancel upath_of irred_of. 
  Proof. (do 2 case) => p ? ?. by do 2 apply: val_inj. Qed.

  Definition IPath_finMixin := Eval hnf in CanFinMixin can_irred_of.
  Canonical IPath_finType := Eval hnf in FinType IPath IPath_finMixin.

  Definition path_of_ipath (p : IPath) := ival p. 
  Definition in_ipath p x := x \in path_of_ipath p.
  Canonical IPath_predType := Eval hnf in @PredType G (IPath) in_ipath.
  Coercion path_of_ipath : IPath >-> Path.
End IPath.

End DiPathTheory.
Hint Resolve ivalP : core.

(** In some constructions a vertex can be typed as belonging to different
graphs. This makes [Path x y] or [x -- y] insufficent for understanding the
proofs. In these contexts one can open the implicit scope to display implicit
types for the most frequently used constructions *)

(* Declare Scope implicit_scope. compat:coq-8.9*)
Notation "x -- y :> G" := (@edge_rel G x y) (at level 30, y at next level) : implicit_scope.
Notation "'PATH' G x y" := (@Path G x y) (at level 4) : implicit_scope.
Notation "'IPATH' G x y" := (@IPath G x y) (at level 4) : implicit_scope.

(** ** Basic Constructions on digraphs *)

(** *** Induced Subgraphs *)

Section InducedSubgraph.
  Variables (G : diGraph) (S : {set G}).

  Definition induced_type := sig [eta mem S].

  Definition induced_rel := [rel x y : induced_type | val x -- val y].

  Definition induced := DiGraph induced_rel.

End InducedSubgraph.

Lemma path_to_induced (G : diGraph) (S : {set G}) (x y : induced S) p' : 
  @pathp G (val x) (val y) p' -> {subset p' <= S} -> 
  exists2 p, pathp x y p & p' = map val p.
Proof.
  move=> pth_p' sub_p'.
  case: (lift_pathp _ _ pth_p' _) => //; first exact: val_inj.
  - move=> z /sub_p' z_S. by apply/codomP; exists (Sub z z_S).
  - move=> p [pth_p /esym eq_p']. by exists p.
Qed.

Lemma induced_path (G : diGraph) (S : {set G}) (x y : induced S) (p : seq (induced S)) : 
  pathp x y p -> @pathp G (val x) (val y) (map val p).
Proof.
  elim: p x => /= [|z p IH] x pth_p.
  - by rewrite (pathp_nil pth_p) pathpxx.
  - rewrite !pathp_cons in pth_p *. 
    case/andP : pth_p => p1 p2. apply/andP; split => //. exact: IH.
Qed.

Lemma Path_to_induced (G : diGraph) (S : {set G}) (x y : induced S) 
  (p : Path (val x) (val y)) : {subset p <= S} -> exists q : Path x y, map val (nodes q) = nodes p.
Proof.
  case: p => p pth_p sub_p. case: (path_to_induced pth_p).
  - move=> z z_p; apply: sub_p. by rewrite mem_path nodesE /= inE z_p.
  - move=> q pth_q eq_p. exists (Sub q pth_q). by rewrite !nodesE /= eq_p.
Qed.

Lemma Path_from_induced (G : diGraph) (S : {set G}) (x y : induced S) (p : Path x y) : 
  { q : Path (val x) (val y) | {subset q <= S} & nodes q = map val (nodes p) }.
Proof. 
  case: p => p pth_p.
  exists (Build_Path (induced_path pth_p)); last by rewrite !nodesE.
  move=> z; rewrite mem_path nodesE /= -map_cons => /mapP[z' _ ->]; exact: valP.
Qed.

(** *** Edge Deletion *)

Definition num_edges (G : diGraph) := #|[pred x : G * G | x.1 -- x.2]|.

Section DelEdge.

Variable (G : diGraph) (a b : G).

Definition del_rel a b := [rel x y : G | x -- y && ((x != a) || (y != b))].

Definition del_edge := DiGraph (del_rel a b).

Definition subrel_del_edge : subrel (del_rel a b) (@edge_rel G).
Proof. by move => x y /andP []. Qed.

Hypothesis ab : a -- b.

Lemma card_del_edge : num_edges del_edge < num_edges G.
Proof.
  apply: proper_card. apply/properP; split.
  - apply/subrelP. exact: subrel_del_edge. 
  - exists (a,b); by rewrite !inE //= /edge_rel /= !eqxx. 
Qed.

(** This is the fundamental case analysis for irredundant paths in [G] in
terms of paths in [del_edge a b] *)

(** TOTHINK: The proof below is a slighty messy induction on
[p]. Informally, one would simply check wether [nodes p] contains and
[a] followed by a [b] *)
Lemma del_edge_path_case (x y : G) (p : Path x y) (Ip : irred p) :
    (exists (p1 : @IPath del_edge x a) (p2 : @IPath del_edge b y), 
        [/\ nodes p = nodes p1 ++ nodes p2, a \notin p2 & b \notin p1])
  \/ (exists p1 : @IPath del_edge x y, nodes p = nodes p1).
Proof.
  pattern x, y, p. apply irred_ind => //.
  - move => {p Ip}.  
    have Ip : irred (@idp del_edge y) by apply: irred_idp. by right;exists (Sub _ Ip).
  - move => {x p Ip} x z p xz Ip xp [[p1] [p2] [A B C]|[p1] E].
    + left. 
      have xyD : (x:del_edge) -- z. 
      { rewrite /edge_rel/= xz (_ : x != a) //. apply: contraNneq xp => -> .
        by rewrite mem_path A mem_cat -(@mem_path del_edge) path_end. }
      have Iq : irred (pcat (edgep xyD) p1). 
      { rewrite irred_edgeL (valP p1) andbT. 
        rewrite mem_path A mem_cat -(@mem_path del_edge) negb_or in xp.
        by case/andP : xp. }
      exists (Sub _ Iq). exists p2. split => //. 
      * by rewrite /= !nodes_pcat A [nodes p1](nodesE) /= -catA. 
      * change (b \notin pcat (edgep xyD) p1). 
        rewrite (@mem_pcat del_edge) (negbTE C) orbF mem_edgep negb_or.
        rewrite irred_edgeL in Iq. apply/andP; split.
        -- apply: contraNneq xp => <-. 
           by rewrite mem_path A mem_cat -!(@mem_path del_edge) path_begin.
        -- apply: contraTneq Ip => ?. subst z. 
           rewrite irredE A cat_uniq [has _ _](_ : _ = true) //. 
           apply/hasP. by exists b => /=; rewrite -!(@mem_path del_edge) path_begin.
    + case: (boolP ((x : del_edge) -- z)) => [xzD|xzND].
      * right. 
        have Iq : irred (pcat (edgep xzD) p1). 
        { by rewrite irred_edgeL (valP p1) mem_path -E -(@mem_path G) xp. }
        exists (Sub _ Iq). by rewrite !nodes_pcat E. 
      * left. rewrite /edge_rel/= xz /= negb_or !negbK in xzND. 
        case/andP : xzND => /eqP ? /eqP ?. subst x. subst z. 
        have Iq : irred (@idp del_edge a) by apply: irred_idp.
        exists (Sub _ Iq). exists p1. split => //=. 
        -- by rewrite nodes_pcat E [nodes p1]nodesE /= -cat1s catA !nodesE. 
        -- by rewrite (@mem_path del_edge) -E -(@mem_path G).
        -- rewrite (@mem_path del_edge) nodesE /= inE. 
           apply: contraNneq xp => <-. 
           by rewrite mem_path E -(@mem_path del_edge) path_begin.
Qed.

End DelEdge.

Lemma del_edge_lift_proof (G : diGraph) (a b x y : G) p : 
  @pathp (del_edge a b) x y p -> @pathp G x y p.
Proof. case: G a b x y p => T e a b x y p. apply: subrel_pathp. exact: subrel_del_edge. Qed.

(** ** Interior of irredundant paths *)

(* TOTHINK: This definition really only makes sense for irredundant paths *)
Section Interior.
Variable (G : diGraph) (x y : G).
Implicit Types (p : Path x y).

Definition interior p := [set x in p] :\: [set x;y].

Lemma interior_edgep (xy : x -- y) : interior (edgep xy) = set0.
Proof. apply/setP => z. rewrite !inE mem_edgep. by do 2 (case: (_ == _)). Qed.

Lemma interiorN p z : z \in interior p -> z \notin [set x; y].
Proof. rewrite inE. by case (_ \in _). Qed.

Lemma interiorW p z : z \in interior p -> z \in p.
Proof. rewrite !inE. case: (_ \in _) => //. by rewrite andbF. Qed.

Lemma interior0E p : x != y -> irred p -> interior p = set0 -> exists xy, p = edgep xy.
Proof.
  move => xNy Ip P0. 
  case: (splitL p xNy) Ip => z [xz] [p'] [E _]. 
  rewrite E irred_edgeL => /andP [xNp Ip']. 
  suff zNy : z = y. { subst. exists xz. by rewrite (irredxx Ip') pcat_idR. }
  apply: contra_eq P0 => C. apply/set0Pn. exists z. 
  rewrite !inE negb_or C eq_sym E mem_pcat mem_edgep !eqxx //= orbT !andbT. 
  apply: contraNneq xNp => ?. subst z. exact: path_begin.
Qed.

Definition independent (p q : Path x y) := 
  [disjoint interior p & interior q].

Lemma independent_sym (p q : Path x y):
  independent p q -> independent q p.
Proof. by rewrite /independent disjoint_sym. Qed.

End Interior.

(** The lemma below loses the connection between [p1]/[p2] and
[p1']/[p2']. However adding [p1' \subset p1] and [p2' \subset p2]
means that we would only get [interior p1' :|: interior p2' != set0] *)
Lemma disjoint_part (G : diGraph) (x y : G) (p1 p2 : Path x y) : 
  irred p1 -> irred p2 -> p1 != p2 -> 
  exists (x' y' : G) (p1' p2' : IPath x' y'), independent p1' p2' /\ interior p1' != set0.
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



Section Transfer.
  Variables (T : finType) (e1 e2 : rel T).
  Let D1 := DiGraph e1.
  Let D2 := DiGraph e2.
  Variables (x y : T) (p p' : @Path D1 x y) (q q' : @Path D2 x y).
  Hypothesis Npq : nodes p = nodes q.
  Hypothesis Npq' : nodes p' = nodes q'.

  Lemma irred_eq_nodes : irred p = irred q.
  Proof. by rewrite !irredE Npq. Qed.

  Lemma mem_eq_nodes : p =i q.
  Proof. move => z /=. by rewrite (@mem_path D1) Npq -(@mem_path D2). Qed.

  Lemma interior_eq_nodes : interior p = interior q.
  Proof. 
    rewrite /interior (_ : [set x in p] = [set x in q]) //. 
    apply/setP => z. by rewrite !inE mem_eq_nodes.
  Qed.

End Transfer.

Lemma independent_nodes (T : finType) (e1 e2 : rel T) x y (p p' : @Path (DiGraph e1) x y) 
  (q q' : @Path (DiGraph e2) x y) (Npq : nodes p = nodes q) (Npq' : nodes p' = nodes q') : 
  independent p p' = independent q q'.
Proof. by rewrite /independent (interior_eq_nodes Npq) (interior_eq_nodes Npq'). Qed.

(** ** Isomorphisms *)

Definition is_dhom (F G: diGraph) (h: F -> G): Prop := forall x y, x -- y -> h x -- h y.

Lemma dhom_id G: @is_dhom G G id.
Proof. by []. Qed.

Lemma dhom_comp F G H h k:
  @is_dhom F G h -> @is_dhom G H k -> is_dhom (k \o h).
Proof. intros E E' => x y O. apply E', E, O. Qed.

Record diso (F G: diGraph): Type := Diso
  { diso_v:> bij F G;
    diso_hom: is_dhom diso_v;
    diso_hom': is_dhom diso_v^-1 }.

Lemma edge_diso F G (h: diso F G) x y: h x -- h y = x -- y.
Proof.
  apply/idP/idP; last exact: diso_hom. 
  move/(diso_hom' h). by rewrite 2!bijK.
Qed.

Definition diso_id {A}: diso A A := @Diso A A bij_id (@dhom_id A) (@dhom_id A). 

Definition diso_sym {A B}: diso A B -> diso B A.
Proof. move=>f. apply Diso with (bij_sym f); apply f. Defined.

Definition diso_comp {A B C}: diso A B -> diso B C -> diso A C.
Proof.
  move=> f g.
  apply Diso with (bij_comp f g); apply dhom_comp. apply f. apply g. apply g. apply f. 
Defined.

Instance diso_Equivalence: Equivalence diso.
constructor. exact @diso_id. exact @diso_sym. exact @diso_comp. Defined.

Lemma edge_diso' F G (h: diso F G) x y: h^-1 x -- h^-1 y = x -- y.
Proof. apply (edge_diso (diso_sym h)). Qed.

Lemma Diso' (F G: diGraph) (f: F -> G) (g: G -> F):
  cancel f g -> cancel g f -> (forall x y, x--y <-> f x -- f y) -> diso F G.
Proof.
  move=> fg gf H. 
  exists (Bij fg gf). 
  abstract (firstorder).
  abstract (move => x y /=; by rewrite H !gf).
Defined.

Lemma Diso'' (F G: diGraph) (f: F -> G) (g: G -> F):
  cancel f g -> cancel g f ->
  (forall x y, x--y -> f x -- f y) -> (forall x y, x--y -> g x -- g y) -> diso F G.
Proof.
  move=>fg gf H H'. eapply Diso'. apply fg. apply gf.
  move=>x y. split. apply H.
  abstract by move=> /H' E; rewrite 2!fg in E. 
Defined.

(** ** Unindexed paths *)

(** In order to define the notion of [AB]-connector, we need to
abstract from the incices in [Path x y] *)

Section PathS.
Variable (G : diGraph).

Definition pathS := { x : G * G & Path x.1 x.2 }.
Definition PathS x y (p : Path x y) : pathS := existT (fun x : G * G => Path x.1 x.2) (x,y) p.

Definition in_pathS (p : pathS) : collective_pred G := [pred x | x \in tagged p].
Canonical pathS_predType := Eval hnf in PredType (@in_pathS).
Arguments in_pathS _ /.

(** We can override fst because MathComp uses .1 *)
Definition fst (p : pathS) := (tag p).1.
Definition lst (p : pathS) := (tag p).2.
Arguments fst _ /.
Arguments lst _ /.

Lemma pathS_eta (p : pathS) : 
  p = @PathS (fst p) (lst p) (tagged p).
Proof. by case: p => [[x y] ri]. Qed.

Lemma fst_mem (p : pathS) : fst p \in p.
Proof. case: p => [[x y] p] /=. exact: path_begin. Qed.

Lemma lst_mem (p : pathS) : lst p \in p.
Proof. case: p => [[x y] p] /=. exact: path_end. Qed.

(** Concatenation on [pathS] *)

Definition castL (x' x y : G) (E : x = x') (p : Path x y) : Path x' y :=
  match E in (_ = y0) return (Path y0 y) with erefl => p end.

Definition pcatS (p1 p2 : pathS) : pathS :=
  let: (existT x p,existT y q) := (p1,p2) in
  match altP (y.1 =P x.2) with
    AltTrue E => PathS (pcat p (castL E q))
  | AltFalse _ => PathS p
  end.

Lemma pcatSE (x y z : G) (p : Path x y) (q : Path y z) : 
  pcatS (PathS p) (PathS q) = PathS (pcat p q).
Proof. 
  rewrite /pcatS /=. case: {-}_ /altP => [E|]; last by rewrite eqxx.
  rewrite /castL. by rewrite (eq_irrelevance E erefl).
Qed.

End PathS.

Definition del_edge_liftS (G : diGraph) (a b : G) (p : pathS (del_edge a b)) :=
  let: existT (x,y) p' := p in PathS (Build_Path (del_edge_lift_proof (valP p'))).

Lemma mem_del_edge_liftS (G : diGraph) (a b : G) (p : pathS (del_edge a b))  x : 
  (x \in del_edge_liftS p) = (x \in p).
Proof. by case: p => [[u v] p]. Qed.
