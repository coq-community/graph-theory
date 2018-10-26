From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Simple Graphs

This file defines (finite) simple graphs, i.e. undirected and
unlabeled graphs without self-loops. We provide a number of
constructions and lemmas to reason about paths in simple graphs:

For [G : sgraph] and [x, y : G] we define two auxiliary notions:

[spath x y p] == the list (x::p) is an xy-path in G.

[upath x y p] == the list (x::p) is an irredundant xy-path in G.

Due to the asymmetry in the definitions of of [path],[spath], and
[upath], these are ill-suited for the symmetry reasoning prevalent in
graph theory. We remedy this by providing a type family of packaged
paths [Path x y] which abstracts away this asymmetry. We then list
many of the lemmas from the path library to the setting of simple
graphs. *)

Record sgraph := SGraph { svertex :> finType ; 
                         sedge: rel svertex; 
                         sg_sym: symmetric sedge;
                         sg_irrefl: irreflexive sedge}.

Notation "x -- y" := (sedge x y) (at level 30).
Definition sgP := (sg_sym,sg_irrefl).
Prenex Implicits sedge.

Lemma sg_edgeNeq (G : sgraph) (x y : G) : x -- y -> (x == y = false).
Proof. apply: contraTF => /eqP ->. by rewrite sg_irrefl. Qed.

Lemma sconnect_sym (G : sgraph) : connect_sym (@sedge G).
Proof. apply: connect_symI. exact: sg_sym. Qed.

Lemma sedge_equiv (G : sgraph) : 
  equivalence_rel (connect (@sedge G)).
Proof.  apply: equivalence_rel_of_sym. exact: sg_sym. Qed.

Lemma symmetric_restrict_sedge (G : sgraph) (A : pred G) :
  symmetric (restrict A sedge).
Proof. apply: symmetric_restrict. exact: sg_sym. Qed.
Hint Resolve symmetric_restrict_sedge.

Lemma srestrict_sym (G : sgraph) (A : pred G) : 
  connect_sym (restrict A sedge).
Proof. apply: connect_symI. exact: symmetric_restrict_sedge. Qed.

Lemma sedge_in_equiv (G : sgraph) (A : {set G}) : 
  equivalence_rel (connect (restrict (mem A) sedge)). 
Proof. 
  apply: equivalence_rel_of_sym.  
  apply: symmetric_restrict. exact:sg_sym. 
Qed.

Lemma sedge_equiv_in (G : sgraph) (A : {set G}) :
  {in A & &, equivalence_rel (connect (restrict (mem A) sedge))}.
Proof. move: (sedge_in_equiv A). by firstorder. Qed.

(** ** Disjoint Union *)

Section JoinSG.
  Variables (G1 G2 : sgraph).
  
  Definition join_rel (a b : G1 + G2) := 
    match a,b with
    | inl x, inl y => x -- y
    | inr x, inr y => x -- y
    | _,_ => false
    end.

  Lemma join_rel_sym : symmetric join_rel.
  Proof. move => [x|x] [y|y] //=; by rewrite sg_sym. Qed.

  Lemma join_rel_irrefl : irreflexive join_rel.
  Proof. move => [x|x] //=; by rewrite sg_irrefl. Qed.

  Definition sjoin := SGraph join_rel_sym join_rel_irrefl. 

  Lemma join_disc (x : G1) (y : G2) : 
    connect join_rel (inl x) (inr y) = false.
  Proof. 
    apply/negP. case/connectP => p. elim: p x => // [[a|a]] //= p IH x.
    case/andP => _. exact: IH. 
  Qed.

End JoinSG.

Prenex Implicits join_rel.

(** ** Homomorphisms *)

Definition hom_s (G1 G2 : sgraph) (h : G1 -> G2) := 
  forall x y, x -- y -> h x != h y -> (h x -- h y).

Definition subgraph (S G : sgraph) := 
  exists2 h : S -> G, injective h & hom_s h.

Section InducedSubgraph.
  Variables (G : sgraph) (S : {set G}).

  Definition induced_type := sig [eta mem S].

  Definition induced_rel := [rel x y : induced_type | val x -- val y].

  Lemma induced_sym : symmetric induced_rel.  
  Proof. move => x y /=. by rewrite sgP. Qed.
         
  Lemma induced_irrefl : irreflexive induced_rel.  
  Proof. move => x /=. by rewrite sgP. Qed.

  Definition induced := SGraph induced_sym induced_irrefl.

  Lemma induced_sub : subgraph induced G.
  Proof. exists val => //. exact: val_inj. Qed.

End InducedSubgraph.

Lemma irreflexive_restrict (T : Type) (e : rel T) (A : pred T) : 
  irreflexive e -> irreflexive (restrict A e).
Proof. move => irr_e x /=. by rewrite irr_e. Qed.

Definition srestrict (G : sgraph) (A : pred G) :=
  Eval hnf in SGraph (symmetric_restrict A (@sg_sym G))
                     (irreflexive_restrict A (@sg_irrefl G)).

(** *** Isomorphism of graphs *)

CoInductive sg_iso (G H : sgraph) : Prop :=
  SgIso (g : H -> G) (h : G -> H) : cancel g h -> cancel h g ->
    {homo g : x y / x -- y} -> {homo h : x y / x -- y} -> sg_iso G H.

Lemma sg_iso_refl (G : sgraph) : sg_iso G G.
Proof. by exists id id. Qed.

Lemma sg_iso_sym (G H : sgraph) : sg_iso G H -> sg_iso H G.
Proof. by case=> g h ? ? ? ?; exists h g. Qed.

Lemma sg_iso_trans (G H K : sgraph) : sg_iso G H -> sg_iso H K -> sg_iso G K.
Proof.
  case=> gh1 gh2 ghK1 ghK2 ghH1 ghH2.
  case=> hk1 hk2 hkK1 hkK2 hkH1 hkH2.
  exists (gh1 \o hk1) (hk2 \o gh2).
    + by move=> x /=; rewrite ghK1 hkK1.
    + by move=> x /=; rewrite hkK2 ghK2.
    + by move=> x y /hkH1 /ghH1.
    + by move=> x y /ghH2 /hkH2.
Qed.

Lemma iso_subgraph (G H : sgraph) : sg_iso G H -> subgraph G H.
Proof.
  case=> g h _ hK _ hH.
  exists h ; by [exact: can_inj hK | move=> x y /hH->].
Qed.

(** Splitting off disconnected parts *)
Lemma ssplit_disconnected (G:sgraph) (V : {set G}) : 
  (forall x y, x \in V -> y \notin V -> ~~ x -- y) ->
  sg_iso (sjoin (induced V) (induced (~: V))) G.
Proof.
  move => HV. set H := sjoin _ _.
  have cast x (p : x \notin V) : x \in ~: V. by rewrite inE.
  pose g (x : G) : H := 
    match (@boolP (x \in V)) with 
      | AltTrue p => inl (Sub x p) 
      | AltFalse p => inr (Sub x (cast x p)) 
    end.
  pose h (x : H) : G := match x with inl x => val x | inr x => val x end.
  exists g h. 
  - move => x. rewrite /g /h. by case: {-}_ /boolP.
  - move => [x|x]; rewrite /g /h. 
    + case: {-}_ /boolP => px. 
      * congr inl. symmetry. apply/eqP. by rewrite sub_val_eq.
      * case:notF.  apply: contraNT px => _. exact: valP.
    + case: {-}_ /boolP => px.
      * case:notF.  apply: contraTT px => _. move: (valP x). by rewrite !inE.
      * congr inr. symmetry. apply/eqP. by rewrite sub_val_eq.
  - move => x y xy.
    rewrite /g. case: {-}_/boolP => px;case: {-}_/boolP => py => //.
    + apply: contraTT xy => _. exact: HV.
    + apply: contraTT xy => _. rewrite sg_sym. exact: HV.
  - by move => [x|x] [y|y] xy.
Qed.

(** ** Unpackaged Simple Paths *)

Section SimplePaths.
Variable (G : sgraph).

Implicit Types (x y z : G).

Definition srev x p := rev (belast x p).

Lemma last_rev_belast x y p : 
  last x p = y -> last y (srev x p) = x.
Proof. case: p => //= a p _. by rewrite /srev rev_cons last_rcons. Qed.

Lemma path_srev x p : 
  path sedge x p = path sedge (last x p) (srev x p).
Proof. 
  rewrite rev_path [in RHS](eq_path (e' := sedge)) //. 
  move => {x} x y. exact: sg_sym. 
Qed.

(** We define paths in stages, we first define an spath predicate for
paths between nodes and later package this asymmetric notion to obtain
something more symmetric *)

Definition spath (x y : G) p := path sedge x p && (last x p == y).

Lemma spathW y x p : spath x y p -> path sedge x p.
Proof. by case/andP. Qed.

Lemma spath_last y x p : spath x y p -> last x p = y.
Proof. by case/andP => _ /eqP->. Qed.

Lemma rcons_spath x y p : path sedge x (rcons p y) -> spath x y (rcons p y).
Proof. move => A. apply/andP. by rewrite last_rcons eqxx. Qed.

Lemma spathxx x : spath x x [::].
Proof. exact: eqxx. Qed.

Lemma spath_nil x y : spath x y [::] -> x = y.
Proof. by case/andP => _ /eqP. Qed.

Lemma spath_rcons x y z p: spath x y (rcons p z) -> y = z.
Proof. case/andP => _ /eqP <-. exact: last_rcons. Qed.

Lemma spath_cat x y p1 p2 : 
  spath x y (p1++p2) = (spath x (last x p1) p1) && (spath (last x p1) y p2).
Proof. by rewrite {1}/spath cat_path last_cat /spath eqxx andbT /= -andbA. Qed.

Lemma spath_cons x y z p : 
  spath x y (z :: p) = x -- z && spath z y p.
Proof. by rewrite -cat1s spath_cat {1}/spath /= eqxx !andbT. Qed.

Lemma spath_concat x y z p q : 
  spath x y p -> spath y z q -> spath x z (p++q).
Proof. 
  move => /andP[A B] /andP [C D]. 
  rewrite spath_cat (eqP B) /spath -andbA. exact/and4P.
Qed.

Lemma spath_end x y p : spath x y p -> y \in x :: p.
Proof. move => A. by rewrite -(spath_last A) mem_last. Qed.

Lemma spath_endD x y p : spath x y p -> x != y -> y \in p.
Proof. move => A B. move: (spath_end A). by rewrite !inE eq_sym (negbTE B). Qed.

Lemma srev_rcons x z p : srev x (rcons p z) = rcons (rev p) x.
Proof. by rewrite /srev belast_rcons rev_cons. Qed.

(** Note that the converse of the following does not hold since [srev
x p] forgets the last element of [p]. Consequently, double reversal
only cancels if the right nodes are added back. *)
Lemma spath_rev x y p : spath x y p -> spath y x (srev x p).
Proof.
  rewrite /spath. elim/last_ind: p => /= [|p z _]; first by rewrite eq_sym.
  rewrite !srev_rcons !last_rcons eqxx andbT path_srev last_rcons srev_rcons. 
  by move/andP => [A /eqP <-].
Qed.

Lemma srevK x y p : last x p = y -> srev y (srev x p) = p.
Proof. 
  elim/last_ind: p => // p z _. 
  by rewrite last_rcons !srev_rcons revK => ->.
Qed.

Lemma srev_nodes x y p : spath x y p -> x :: p =i y :: srev x p.
Proof. 
  elim/last_ind: p => //; first by move/spath_nil ->.
  move => p z _ H a. rewrite srev_rcons !(inE,mem_rcons,mem_rev). 
  rewrite (spath_rcons H). by case: (a == x).
Qed.

CoInductive spath_split z x y : seq G -> Prop := 
  SSplit p1 p2 : spath x z p1 -> spath z y p2 -> spath_split z x y (p1 ++ p2).

Lemma ssplitP z x y p : z \in x :: p -> spath x y p -> spath_split z x y p.
Proof. 
  case/splitPl => p1 p2 /eqP H1 /andP [H2 H3]. 
  rewrite cat_path last_cat in H2 H3. case/andP : H2 => H2 H2'.
  constructor; last rewrite -(eqP H1); exact/andP. 
Qed.

Lemma spath_shorten x y p :
  spath x y p -> exists p', [/\ spath x y p', uniq (x::p') & {subset p' <= p}].
Proof. case/andP. case/shortenP => p' *. by exists p'. Qed.

End SimplePaths.
Arguments spath_last [G].


(** ** Unpackaged Irredundant Paths *)
 
Section Upath.
Variable (G : sgraph).
Implicit Types (x y z : G).

Definition upath x y p := uniq (x::p) && spath x y p.

Lemma upathW x y p : upath x y p -> spath x y p.
Proof. by case/andP. Qed.

Lemma upathWW x y p : upath x y p -> path sedge x p.
Proof. by move/upathW/spathW. Qed.

Lemma upath_uniq x y p : upath x y p -> uniq (x::p).
Proof. by case/andP. Qed.

Lemma upath_size x y p : upath x y p -> size p < #|G|.
Proof. move=> /upath_uniq/card_uniqP/= <-. exact: max_card. Qed.

Lemma rev_upath x y p : upath x y p -> upath y x (srev x p).
Proof. 
  case/andP => A B. apply/andP; split; last exact: spath_rev.
  apply: leq_size_uniq A _ _. 
  - move => z. by rewrite -srev_nodes.
  - by rewrite /= size_rev size_belast.
Qed.

Lemma upath_sym x y : unique (upath x y) -> unique (upath y x).
Proof. 
  move => U p q Hp Hq. 
  suff S: last y p = last y q. 
  { apply: last_belast_eq S _; apply: rev_inj; apply: U; exact: rev_upath. }
  rewrite !(spath_last x) //; exact: upathW.
Qed.

Lemma upath_cons x y z p : 
  upath x y (z::p) = [&& x -- z, x \notin (z::p) & upath z y p].
Proof. 
  rewrite /upath spath_cons [z::p]lock /= -lock.
  case: (x -- z) => //. by case (uniq _).
Qed.

Lemma upath_consE x y z p : 
  upath x y (z :: p) -> [/\ x -- z, x \notin z :: p & upath z y p].
Proof. rewrite upath_cons. by move/and3P. Qed.

Lemma upath_nil x p : upath x x p -> p = [::].
Proof. case: p => //= a p /and3P[/= A B C]. by rewrite -(eqP C) mem_last in A. Qed.

CoInductive usplit z x y : seq G -> Prop := 
  USplit p1 p2 : upath x z p1 -> upath z y p2 -> [disjoint x::p1 & p2]
                 -> usplit z x y (p1 ++ p2).

Lemma usplitP z x y p : z \in x :: p -> upath x y p -> usplit z x y p.
Proof. 
  move => in_p /andP [U P]. case: (ssplitP in_p P) U  => p1 p2 sp1 sp2.
  rewrite -cat_cons cat_uniq -disjoint_has disjoint_sym => /and3P [? C ?].
  suff H: z \notin p2 by constructor.
  apply/negP. apply: disjointE C _. by rewrite -(spath_last z x p1) // mem_last. 
Qed.

Lemma upathP x y : reflect (exists p, upath x y p) (connect sedge x y).
Proof.
  apply: (iffP connectP) => [[p p1 p2]|[p /and3P [p1 p2 /eqP p3]]]; last by exists p.
  exists (shorten x p). case/shortenP : p1 p2 => p' ? ? _ /esym/eqP ?. exact/and3P. 
Qed.

Lemma spathP x y : reflect (exists p, spath x y p) (connect sedge x y).
Proof. 
  apply: (iffP idP) => [|[p] /andP[A /eqP B]]; last by apply/connectP; exists p.
  case/upathP => p /upathW ?. by exists p.
Qed.

End Upath.

Lemma upathPR (G : sgraph) (x y : G) A :
  reflect (exists p : seq G, @upath (srestrict A) x y p)
          (connect (restrict A sedge) x y).
Proof. exact: (@upathP (srestrict A)). Qed.

Lemma restrict_upath (G:sgraph) (x y:G) (A : pred G) (p : seq G) : 
  @upath (srestrict A) x y p -> upath x y p.
Proof. 
  elim: p x => // z p IH x /upath_consE [/= /andP [_ u1] u2 u3]. 
  rewrite upath_cons u1 u2 /=. exact: IH.
Qed.

Lemma lift_spath_on (G H : sgraph) (f : G -> H) a b p' : 
  (forall x y, f x \in f a :: p' -> f y \in f a :: p' -> f x -- f y -> x -- y) -> injective f -> 
  spath (f a) (f b) p' -> {subset p' <= codom f} -> exists p, spath a b p /\ map f p = p'.
Proof. 
  move => A I /andP [B /eqP C] D.  case: (lift_path A B D) => p [p1 p2]; subst. 
  exists p. split => //. apply/andP. split => //. rewrite last_map in C. by rewrite (I _ _ C).
Qed.

Lemma lift_spath (G H : sgraph) (f : G -> H) a b p' : 
  (forall x y, f x -- f y -> x -- y) -> injective f -> 
  spath (f a) (f b) p' -> {subset p' <= codom f} -> exists p, spath a b p /\ map f p = p'.
Proof. move => I. apply: lift_spath_on. auto. Qed.

Lemma lift_upath_on (G H : sgraph) (f : G -> H) a b p' : 
  (forall x y, f x \in f a :: p' -> f y \in f a :: p' -> f x -- f y -> x -- y) -> injective f -> 
  upath (f a) (f b) p' -> {subset p' <= codom f} -> exists p, upath a b p /\ map f p = p'.
Proof.
  move => A B /andP [C D] E. case: (lift_spath_on A B D E) => p [p1 p2].
  exists p. split => //. apply/andP. split => //. by rewrite -(map_inj_uniq B) /= p2.
Qed.

Lemma lift_upath (G H : sgraph) (f : G -> H) a b p' : 
  (forall x y, f x -- f y -> x -- y) -> injective f -> 
  upath (f a) (f b) p' -> {subset p' <= codom f} -> exists p, upath a b p /\ map f p = p'.
Proof. move => I. apply: lift_upath_on. auto. Qed.

(* TOTHINK: is this the best way to transfer path from induced subgraphs *)
Lemma induced_path (G : sgraph) (S : {set G}) (x y : induced S) (p : seq (induced S)) : 
  spath x y p -> @spath G (val x) (val y) (map val p).
Proof.
  elim: p x => /= [|z p IH] x pth_p.
  - by rewrite (spath_nil pth_p) spathxx.
  - rewrite !spath_cons in pth_p *. 
    case/andP : pth_p => p1 p2. apply/andP; split => //. exact: IH.
Qed.


(** ** Packaged paths *)

(** We now define packaged paths (i.e., a vertex-indexed collection of
types [Path x y] whose elements are the paths between [x] and [y]). In
particular, this abstracts from the asymmetry in [spath x y p] which
states that [x::p] is an xy-path (paths are never empty). *)

Section Pack.
Variables (G : sgraph).
Implicit Types x y z : G.

Section PathDef.
  Variables (x y : G).

  Record Path := { pval : seq G; _ : spath x y pval }.

  Canonical Path_subType := [subType for pval].
  Definition Path_eqMixin := Eval hnf in [eqMixin of Path by <:].
  Canonical Path_eqType := Eval hnf in EqType Path Path_eqMixin.
  Definition Path_choiceMixin := Eval hnf in [choiceMixin of Path by <:].
  Canonical Path_choiceType := Eval hnf in ChoiceType Path Path_choiceMixin.
  Definition Path_countMixin := Eval hnf in [countMixin of Path by <:].
  Canonical Path_countType := Eval hnf in CountType Path Path_countMixin.

  Record UPath : predArgType := { uval : seq G; _ : upath x y uval }.

  Canonical UPath_subType := [subType for uval].
  Definition UPath_eqMixin := Eval hnf in [eqMixin of UPath by <:].
  Canonical UPath_eqType := Eval hnf in EqType UPath UPath_eqMixin.
  Definition UPath_choiceMixin := Eval hnf in [choiceMixin of UPath by <:].
  Canonical UPath_choiceType := Eval hnf in ChoiceType UPath UPath_choiceMixin.
  Definition UPath_countMixin := Eval hnf in [countMixin of UPath by <:].
  Canonical UPath_countType := Eval hnf in CountType UPath UPath_countMixin.

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

  Definition UPathW (up : UPath) : Path := let (p, Up) := up in Sub p (upathW Up).
  Coercion UPathW : UPath >-> Path.
End PathDef.

Section Primitives.
  Variables (x y z : G) (p : Path x y) (q : Path y z).

  Definition nodes := locked (x :: val p).
  Lemma nodesE : nodes = x :: val p. by rewrite /nodes -lock. Qed.
  Definition irred := uniq nodes.
  Lemma irredE : irred = uniq (x :: val p). by rewrite /irred nodesE.  Qed.
  Definition tail := val p.

  Definition pcat_proof := spath_concat (valP p) (valP q).
  Definition pcat : Path x z := Sub (val p ++ val q) pcat_proof.

  Definition prev_proof := spath_rev (valP p).
  Definition prev : Path y x := Sub (srev x (val p)) prev_proof.

  Lemma path_last: last x (val p) = y.
  Proof. move: (valP p). exact: spath_last. Qed.

End Primitives.

Definition in_nodes x y (p : Path x y) : collective_pred G := 
  [pred u | u \in nodes p].
Canonical Path_predType x y := 
  Eval hnf in @mkPredType G (Path x y) (@in_nodes x y).
Coercion in_nodes : Path >-> collective_pred.

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
  Proof. rewrite irredE. exact: upath_uniq Up. Qed.

  Lemma irred_upath (p : Path x y) : irred p -> upath x y (val p).
  Proof. 
    move => Ip. rewrite /upath irredE in Ip *. rewrite Ip /=. 
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
  Canonical IPath_predType := Eval hnf in @mkPredType G (IPath) (fun p x => x \in path_of_ipath p).
  Coercion path_of_ipath : IPath >-> Path.
End IPath.

(** TODO: This should be [irredE] *)
Lemma irred_nodes x y (p : Path x y) : irred p = uniq (nodes p).
Proof. by rewrite irredE nodesE. Qed.

Lemma nodes_eqE x y (p q : Path x y) : (nodes p == nodes q) = (p == q).
Proof.
  case: q p => q pth_q [p pth_p]. 
  by rewrite !nodesE -val_eqE /= eqseq_cons eqxx.
Qed.

Lemma mem_path x y (p : Path x y) u : u \in p = (u \in x :: val p).
Proof. by rewrite in_collective /nodes -lock. Qed.

Section PathTheory.
Variables (x y z : G) (p : Path x y) (q : Path y z).

Lemma in_tail : z != x -> z \in p -> z \in tail p.
Proof. move => A. by rewrite mem_path inE (negbTE A). Qed.

Lemma path_end : y \in p. 
Proof. by rewrite mem_path -[in X in X \in _](path_last p) mem_last. Qed.

Lemma path_begin : x \in p.
Proof. by rewrite mem_path mem_head. Qed.

Lemma mem_pcatT u : (u \in pcat p q) = (u \in p) || (u \in tail q).
Proof. by rewrite !mem_path !inE mem_cat -orbA. Qed.

Lemma tailW : {subset tail q <= q}.
Proof. move => u. rewrite mem_path. exact: mem_tail. Qed.

Lemma mem_pcat u :  (u \in pcat p q) = (u \in p) || (u \in q).
Proof. 
  rewrite mem_pcatT. case A: (u \in p) => //=. 
  rewrite mem_path inE (_ : u == y = false) //. 
  apply: contraFF A => /eqP->. exact: path_end. 
Qed.

Lemma subset_pcatL : p \subset pcat p q.
Proof. apply/subsetP => u. by rewrite mem_pcat => ->. Qed.

Lemma subset_pcatR : q \subset pcat p q.
Proof. apply/subsetP => u. by rewrite mem_pcat => ->. Qed.

Lemma pcat_subset (A : pred G) : p \subset A -> q \subset A -> pcat p q \subset A.
Proof. 
  move => /subsetP Hp /subsetP Hq. apply/subsetP => u. 
  rewrite !mem_pcat. case/orP; [exact: Hp|exact: Hq].
Qed.

End PathTheory.

Lemma prevK x y (p : Path x y) : prev (prev p) = p.
Proof. apply/val_inj=> /=. apply: srevK. exact: path_last. Qed.

Lemma prev_inj x y : injective (@prev x y).
Proof. apply: (can_inj (g := (@prev y x))) => p. exact: prevK. Qed.

Lemma mem_prev x y (p : Path x y) u : (u \in prev p) = (u \in p).
Proof. rewrite !mem_path -srev_nodes //. exact: valP. Qed.

Lemma pcatA u v x y (p : Path u v) (q : Path v x) (r : Path x y) : 
  pcat (pcat p q) r = pcat p (pcat q r).
Proof. apply/eqP. by rewrite -val_eqE /= catA. Qed.

Lemma prev_cat x y z (p : Path x y) (q : Path y z) : 
  prev (pcat p q) = pcat (prev q) (prev p).
Proof. apply/eqP. by rewrite -val_eqE /= /srev belast_cat rev_cat path_last. Qed.

(** TOTHINK: This is easy to prove and in some contetxt exact what is
needed. However, it introduces an unpleasant asymmetry between [p] and
[q]. *)
Lemma irred_catD x y z (p : Path x z) (q : Path z y) :
  irred (pcat p q) = [&& irred p, irred q & [disjoint p & tail q]].
Proof.
  rewrite /irred {1}/nodes -lock /pcat SubK -cat_cons cat_uniq.
  rewrite -disjoint_has disjoint_sym -nodesE.
  case A : [disjoint _ & _] => //. case: (uniq (nodes p)) => //=. rewrite nodesE /=.
  case: (uniq _) => //=. by rewrite !andbT (disjointFr A _) // path_end.
Qed.

(** This lemma is more symmetric than [irred_cat]. However, the set
equality is sometimes cumbersome to use. Better elimination lemma? *)    
Lemma irred_cat x y z (p : Path x z) (q : Path z y) :
  irred (pcat p q) = [&& irred p, irred q & [set u in p | u \in q] == [set z]].
Proof.
  rewrite /irred {1}nodesE (lock uniq) /= -lock -cat_cons -nodesE cat_uniq.
  congr (_ && _). rewrite (nodesE q) /=. case: uniq => //; rewrite !andbT.
  apply/hasPn/andP.
  - move=> H. split; first by apply/negP=>/H/=; rewrite path_end.
    apply/eqP/setP=> u; rewrite !inE.
    apply/andP/eqP; last by [move=>->; rewrite path_begin path_end].
    case=> u_p. rewrite mem_path inE =>/orP[/eqP//|/H/=]. by rewrite u_p.
  - case=> zNTq. rewrite eqEsubset =>/andP[/subsetP sub _].
    move=> u u_q /=. apply/negP=> u_p.
    case/(_ u _)/Wrap: sub; rewrite inE.
    + rewrite u_p /=; exact: tailW.
    + apply/negP; by apply: contraNneq zNTq =>{1}<-.
Qed.

(** TODO: This lemma should be used instead of the [irred_cat] where appropriate *)
Lemma irred_catE x y z (p : Path x z) (q : Path z y) :
  irred (pcat p q) -> [/\ irred p, irred q & forall k, k \in p -> k \in q -> k = z].
Proof.
  rewrite irred_cat. case/and3P => [? ? A]. split => // k K1 K2.
  apply/eqP. move/eqP/setP/(_ k) : A. by rewrite !inE K1 K2.
Qed.

Lemma prev_irred x y (p : Path x y) : irred p -> irred (prev p).
Proof.
  rewrite /irred /nodes => U. apply: leq_size_uniq U _ _.
  - move => u. by rewrite mem_prev.
  - by rewrite -!lock /= ltnS /srev size_rev size_belast.
Qed.

Lemma irred_rev x y (p : Path x y) : irred (prev p) = irred p.
Proof. apply/idP/idP; first rewrite -[p as X in irred X]prevK; exact: prev_irred. Qed.

Lemma uPathP x y : reflect (exists p : Path x y, irred p) (connect sedge x y).
Proof.
  apply: (iffP (upathP _ _)) => [[p /andP [U P]]|[p I]].
  + exists (Sub p P).  by rewrite /irred nodesE.
  + exists (val p). apply/andP;split; by [rewrite /irred nodesE in I| exact: valP].
Qed.

Lemma Path_connect x y (p : Path x y) : connect sedge x y.
Proof. apply/spathP. exists (val p). exact: valP. Qed.

(** The one-node path *)

Definition idp (u : G) := Build_Path (spathxx u).

Lemma mem_idp (x u : G) : (x \in idp u) = (x == u).
Proof. by rewrite mem_path !inE. Qed.

Lemma irred_idp (x : G) : irred (idp x).
Proof. by rewrite irredE. Qed.

Lemma irredxx (x : G) (p : Path x x) : irred p -> p = idp x.
Proof.
  rewrite irredE /tail (lock uniq); case: p => p p_pth /=.
  rewrite -lock => p_uniq. apply/val_inj => /=.
  by have /upath_nil-> : upath x x p by rewrite /upath p_uniq p_pth.
Qed.

(** Paths with a single edge using an injection from (proofs of) [x -- y] *)

Lemma edgep_proof x y (xy : x -- y) : spath x y [:: y]. 
Proof. by rewrite spath_cons xy spathxx. Qed.

Definition edgep x y (xy : x -- y) := Build_Path (edgep_proof xy).

Lemma mem_edgep x y z (xy : x -- y) :
  z \in edgep xy = (z == x) || (z == y).
Proof. by rewrite mem_path !inE. Qed.

Fact prev_edge_proof x y (xy : x -- y) : y -- x. by rewrite sgP. Qed.
Lemma prev_edge x y (xy : x -- y) : prev (edgep xy) = edgep (prev_edge_proof xy).
Proof. by apply/eqP. Qed.

Lemma irred_edge x y (xy : x -- y) : irred (edgep xy).
Proof. by rewrite irredE /= andbT inE sg_edgeNeq. Qed.

Lemma irred_edgeL y x z1 (xz1 : x -- z1) (p : Path z1 y) : 
  irred (pcat (edgep xz1) p) = (x \notin p) && irred p.
Proof. case: p => p pth_p. by rewrite !irredE /= mem_path /=. Qed.


  
Lemma irred_edgeR y x z (xz : y -- z) (p : Path x y) : 
  irred (pcat p (edgep xz)) = (z \notin p) && irred p.
Proof. by rewrite -irred_rev prev_cat prev_edge irred_edgeL irred_rev mem_prev. Qed.

(** Induction principles for packaged paths *)

Lemma Path_ind P (y : G) : 
  P y y (idp y) -> 
  (forall x z (p : Path z y) (xz : x -- z), 
      P z y p -> P x y (pcat (edgep xz) p)) -> 
  forall x (p : Path x y), P x y p.
Proof. 
  move => Hbase Hstep x [p pth_p]. 
  elim: p x pth_p => [|z p IH] x A. 
  - have ?: x = y. { exact: spath_nil. }
    subst y. rewrite [Build_Path _](_ : _ = idp x) //. exact: val_inj.
  - move: {-}(A). rewrite spath_cons => /andP [xz B2].
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
  move => Hbase Hstep. 
  apply: (Path_ind (P := (fun x y p => irred p -> P x y p))) => //.
  move => x z p xz IH. rewrite irred_edgeL => /andP[A B]. 
  by apply: Hstep; auto.
Qed.

Lemma path_closed (A : pred G) x y (p : Path x y) : 
  x \in A -> (forall y z, y \in A -> y -- z -> z \in A) -> {subset p <= A}.
Proof.
  move: x p. 
  apply (Path_ind (P := fun x y p =>  
         x \in A -> (forall y0 z : G, y0 \in A -> y0 -- z -> z \in A) -> {subset p <= A})).
  - move => yA _ z. by rewrite mem_idp => /eqP->.
  - move => x z p xz IH xA clos_A u. rewrite mem_pcat mem_edgep -orbA.
    have ? : z \in A by exact: clos_A xz.
    case/or3P => [/eqP->|/eqP->|] //. exact: IH. 
Qed.

(** *** Splitting Paths **)

Lemma splitL x y (p : Path x y) : 
  x != y -> exists z xz (p' : Path z y), p = pcat (edgep xz) p' /\ p' =i tail p.
Proof.
  move => xy. case: p => p. elim: p x xy => [|a p IH] x xy H.
  - move/spath_nil : (H) => ?. subst y. by rewrite eqxx in xy.
  - move: (H) => H'. move: H. rewrite spath_cons => /andP [A B].
    exists a. exists A. exists (Build_Path B). split; first exact: val_inj.
    move => w. by rewrite in_collective nodesE !inE.
Qed.

Lemma splitR x y (p : Path x y) : 
  x != y -> exists z (p' : Path x z) zy, p = pcat p' (edgep zy).
Proof.
  move => xy. case: p. elim/last_ind => [|p a IH] H.
  - move/spath_nil : (H) => ?. subst y. by rewrite eqxx in xy.
  - move: (H) => H'. 
    case/andP : H. rewrite rcons_path => /andP [A B] C.
    have sP : spath x (last x p) p by rewrite /spath A eqxx.
    move: (spath_rcons H') => ?; subst a.
    exists (last x p). exists (Build_Path sP). exists B. 
    apply: val_inj => /=. by rewrite cats1.
Qed.

CoInductive psplit z x y : Path x y -> Prop := 
  PSplit (p1 : Path x z) (p2 : Path z y) : psplit z (pcat p1 p2).

Lemma psplitP z x y (p : Path x y) : z \in p -> psplit z p.
Proof. 
  move: (valP p) => pth_p in_p. rewrite mem_path in in_p.
  case/(ssplitP in_p) E : _ / pth_p => [p1 p2 P1 P2].
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

Lemma split_at_first_aux {A : pred G} x y (p : seq G) k : 
    spath x y p -> k \in A -> k \in x::p -> 
    exists z p1 p2, [/\ p = p1 ++ p2, spath x z p1, spath z y p2, z \in A 
                & forall z', z' \in A -> z' \in x::p1 -> z' = z].
Proof.
  move => pth_p in_A in_p. 
  pose n := find A (x::p). 
  pose p1 := take n p.
  pose p2 := drop n p.
  pose z := last x p1.
  have def_p : p = p1 ++ p2 by rewrite cat_take_drop.
  move: pth_p. rewrite {1}def_p spath_cat. case/andP => pth_p1 pth_p2.
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
                                                                
Lemma split_at_first {A : pred G} x y (p : Path x y) k :
  k \in A -> k \in p ->
  exists z (p1 : Path x z) (p2 : Path z y), 
    [/\ p = pcat p1 p2, z \in A & forall z', z' \in A -> z' \in p1 -> z' = z].
Proof.
  case: p => p pth_p /= kA kp. rewrite mem_path in kp.
  case: (split_at_first_aux pth_p kA kp) => z [p1] [p2] [def_p pth_p1 pth_p2 A1 A2].
  exists z. exists (Build_Path pth_p1). exists (Build_Path pth_p2). split => //.
  + subst p. exact: val_inj.
  + move => ?. rewrite mem_path. exact: A2.
Qed.

Lemma split_at_last {A : pred G} (x y : G) (p : Path x y) (k : G) : 
  k \in A -> k \in p ->
  exists (z : G) (p1 : Path x z) (p2 : Path z y),
    [/\ p = pcat p1 p2, z \in A & forall z' : G, z' \in A -> z' \in p2 -> z' = z].
Proof.
  move => kA kp. rewrite -mem_prev in kp. 
  case: (split_at_first kA kp) => z [p1] [p2] [E zA I].
  exists z. exists (prev p2). exists (prev p1). rewrite -prev_cat -E prevK. 
  split => // z'. rewrite mem_prev. exact: I. 
Qed.


Lemma UPath_from_irred x y (p : Path x y) : irred p ->
  exists q : UPath x y, val p = val q.
Proof.
  case: p => p pth. rewrite irredE [_ :: _]/= => Up /=.
  have {pth Up} Up : upath x y p by rewrite /upath; apply/andP; split.
  by exists (Sub p Up).
Qed.

Lemma uncycle x y (p : Path x y) :
  exists2 p' : Path x y, {subset p' <= p} & irred p'.
Proof.
  case: p => p pth_p. case/spath_shorten : (pth_p) => p' [A B C].
  exists (Build_Path A). move => z. rewrite !mem_path !SubK.
  + rewrite !inE. case/predU1P => [->|/C ->] //. by rewrite eqxx.
  + by rewrite /irred nodesE.
Qed.

End Pack.

Hint Resolve path_begin path_end.

(** *** Transporting paths to and from induced subgraphs *)

Lemma path_to_induced (G : sgraph) (S : {set G}) (x y : induced S) p' : 
  @spath G (val x) (val y) p' -> {subset p' <= S} -> 
  exists2 p, spath x y p & p' = map val p.
Proof.
  move=> pth_p' sub_p'.
  case: (lift_spath _ _ pth_p' _) => //; first exact: val_inj.
  - move=> z /sub_p' z_S. by apply/codomP; exists (Sub z z_S).
  - move=> p [pth_p /esym eq_p']. by exists p.
Qed.

Lemma Path_to_induced (G : sgraph) (S : {set G}) (x y : induced S) 
  (p : Path (val x) (val y)) : 
  {subset p <= S} -> exists q : Path x y, map val (nodes q) = nodes p.
Proof.
  case: p => p pth_p sub_p. case: (path_to_induced pth_p).
  - move=> z z_p; apply: sub_p. by rewrite mem_path /= inE z_p.
  - move=> q pth_q eq_p. exists (Sub q pth_q). by rewrite !nodesE /= eq_p.
Qed.


Lemma Path_from_induced (G : sgraph) (S : {set G}) (x y : induced S) (p : Path x y) : 
  exists2 q : Path (val x) (val y), {subset q <= S} & nodes q = map val (nodes p).
Proof. 
  case: p => p pth_p.
  exists (Build_Path (induced_path pth_p)); last by rewrite !nodesE.
  move=> z; rewrite mem_path /= -map_cons => /mapP[z' _ ->]; exact: valP.
Qed.

(* TOTHINK: Use this to prove the lemmas above? *)
Lemma lift_Path_on (G H : sgraph) (f : G -> H) a b (p' : Path (f a) (f b)) : 
  (forall x y, f x \in p' -> f y \in p' -> f x -- f y -> x -- y) -> injective f -> {subset p' <= codom f} -> 
  exists2 p : Path a b, map f (nodes p) = nodes p' & irred p = irred p'.
Proof.
  move => A I S. case: (lift_spath_on _ I (valP p') _).
  - move => x y. rewrite -!mem_path. exact: A.
  - move => x V. apply: S. by rewrite mem_path inE V.
  - move => p [p1 p2]. exists (Sub p p1). 
    + by rewrite !nodesE /= p2. 
    + by rewrite !irredE -p2 -map_cons map_inj_uniq.
Qed.

Lemma lift_Path (G H : sgraph) (f : G -> H) a b (p' : Path (f a) (f b)) : 
  (forall x y, f x -- f y -> x -- y) -> injective f -> {subset p' <= codom f} -> 
  exists2 p : Path a b, map f (nodes p) = nodes p' & irred p = irred p'.
Proof. move => ?. apply: lift_Path_on; auto. Qed.

(** *** Path indexing and 3-way split *)

Definition idx (G : sgraph) (x y : G) (p : Path x y) u := index u (nodes p).

(* TOTHINK: This only parses if the level is at most 10, why? *)
Notation "x '<[' p ] y" := (idx p x < idx p y) (at level 10, format "x  <[ p ]  y").
(* (at level 70, p at level 200, y at next level, format "x  <[ p ]  y"). *)

Section PathIndexing.
  Variables (G : sgraph).
  Implicit Types x y z : G.

  Lemma idx_mem x y (p : Path x y) z :
    z \in p -> idx p z <= size (tail p).
  Proof. 
    case: p => p pth_p. rewrite /idx /irred in_collective nodesE inE /=.
    case: ifP => // E. rewrite eq_sym E /= -index_mem => H. exact: leq_trans H _. 
  Qed.

  Lemma idx_start x y (p : Path x y) : idx p x = 0.
  Proof. by rewrite /idx nodesE /= eqxx. Qed.

  Lemma idx_end x y (p : Path x y) : 
    irred p -> idx p y = size (tail p).
  Proof.
    rewrite /irred nodesE => irr_p. 
    by rewrite /idx nodesE -[in index _](path_last p) index_last.
  Qed.

  Lemma idx_catL (x y z u v : G) (p : Path x y) (q : Path y z) :
    u \in p -> v \in p -> idx (pcat p q) u <= idx (pcat p q) v = (idx p u <= idx p v).
  Proof.
    move=> u_p v_p. rewrite /idx (nodesE (pcat _ _)) (lock index)/= -lock.
    by rewrite -cat_cons -nodesE !index_cat u_p v_p.
  Qed.

  Lemma idx_catR (x y z u v : G) (p : Path x y) (q : Path y z) :
    u \notin p -> v \notin p ->
    idx (pcat p q) u <= idx (pcat p q) v = (idx q u <= idx q v).
  Proof.
    move=> uNp vNp. rewrite /idx (nodesE (pcat _ _)) (lock index)/= -lock.
    rewrite -cat_cons lastI cat_rcons path_last -nodesE !index_cat.
    have /negbTE-> : u \notin belast x (val p).
    { apply: contraNN uNp. by rewrite mem_path lastI mem_rcons inE =>->. }
    have /negbTE-> : v \notin belast x (val p).
    { apply: contraNN vNp. by rewrite mem_path lastI mem_rcons inE =>->. }
    by rewrite leq_add2l.
  Qed.

  Section IDX.
    Variables (x z y : G) (p : Path x z) (q : Path z y).
    Implicit Types u v : G.

    Lemma idx_inj : {in nodes p, injective (idx p) }.
    Proof.
      move => u in_s v E. rewrite /idx in E.
      have A : v \in nodes p. by rewrite -index_mem -E index_mem.
      by rewrite -(nth_index x in_s) E nth_index.
    Qed.

    Hypothesis irr_pq : irred (pcat p q).
    
    Let dis_pq : [disjoint nodes p & tail q].
    Proof. move: irr_pq. by rewrite irred_catD => /and3P[]. Qed.

    Let irr_p : irred p. by case/irred_catE : irr_pq. Qed.

    Let irr_q : irred q. by case/irred_catE : irr_pq. Qed.

    Lemma idxR u : u \in pcat p q -> u \in tail q = z <[pcat p q] u.
    Proof.
      move => A. symmetry. 
      rewrite /idx /pcat nodesE -cat_cons index_cat -nodesE path_end.
      rewrite index_cat mem_pcatT in A *. case/orP: A => A.
      - rewrite A (disjointFr dis_pq A). apply/negbTE. 
        rewrite -leqNgt -!/(idx _ _) (idx_end irr_p) -ltnS. 
        rewrite -index_mem in A. apply: leq_trans A _. by rewrite nodesE.
      - rewrite A (disjointFl dis_pq A) -!/(idx _ _) (idx_end irr_p).
        by rewrite nodesE /= addSn ltnS leq_addr. 
    Qed.

    Lemma idx_nLR u : u \in nodes (pcat p q) -> 
      idx (pcat p q) z < idx (pcat p q) u -> u \notin nodes p /\ u \in tail q.
    Proof. move => A B. rewrite -idxR // in B. by rewrite (disjointFl dis_pq B). Qed.
  
  End IDX.

  Lemma index_rcons (T : eqType) a b (s : seq T):
    a \in b::s -> uniq (b :: s) ->
    index a (rcons s b) = if a == b then size s else index a s.
  Proof.
    case: (boolP (a == b)) => [/eqP<- _|]. 
    - elim: s a {b} => //= [|b s IH] a; first by rewrite eqxx. 
      rewrite !inE negb_or -andbA => /and4P[A B C D].
      rewrite eq_sym (negbTE A) IH //. 
    - elim: s a b => //. 
      + move => a b. by rewrite inE => /negbTE->. 
      + move => c s IH a b A. rewrite inE (negbTE A) /=. 
        rewrite inE eq_sym. case: (boolP (c == a)) => //= B C D. 
        rewrite IH //. 
        * by rewrite inE C.
        * case/and3P:D => D1 D2 D3. rewrite /= D3 andbT. exact: notin_tail D1.
  Qed.

  Lemma index_rev (T : eqType) a (s : seq T) : 
    a \in s -> uniq s -> index a (rev s) = (size s).-1 - index a s.
  Proof.
    elim: s => // b s IH. rewrite in_cons [uniq _]/=. 
    case/predU1P => [?|A] /andP [B uniq_s].
    - subst b. rewrite rev_cons index_rcons. 
      + by rewrite eqxx index_head subn0 size_rev.
      + by rewrite mem_head.
      + by rewrite /= rev_uniq mem_rev B.
    - have D : b == a = false. { by apply: contraNF B => /eqP->. }
      rewrite rev_cons index_rcons. 
      + rewrite eq_sym D IH //= D. by case s.
      + by rewrite inE mem_rev A. 
      + by rewrite /= rev_uniq mem_rev B.
  Qed.
    
  Lemma idx_srev a x y (p : Path x y) : 
    a \in p -> irred p -> idx (prev p) a = size (pval p) - idx p a.
  Proof. 
    move => A B. rewrite /idx /prev !nodesE SubK /srev. 
    case/andP: (valP p) => p1 /eqP p2. 
    by rewrite -rev_rcons -[X in rcons _ X]p2 -lastI index_rev // -?nodesE -?irredE. 
  Qed.
                                              
  Lemma idx_swap a b x y (p : Path x y) : a \in p -> b \in p -> irred p ->
    idx p a < idx p b -> idx (prev p) b < idx (prev p) a.
  Proof.
    move => aP bP ip A. 
    have H : a != b. { apply: contraTN A => /eqP->. by rewrite ltnn. }
    rewrite !idx_srev //. apply: ltn_sub2l => //. 
    apply: (@leq_trans (idx p b)) => //. 
    rewrite -ltnS -[X in _ < X]/(size (x :: pval p)).
    by rewrite -nodesE index_mem.
  Qed. 

  Lemma three_way_split x y (p : Path x y) a b :
    irred p -> a \in p -> b \in p -> a <[p] b -> 
    exists (p1 : Path x a) (p2 : Path a b) p3, 
      [/\ p = pcat p1 (pcat p2 p3), a \notin p3 & b \notin p1].
  Proof.
    move => irr_p a_in_p b_in_p a_before_b.
    case/(isplitP irr_p) def_p : _ / (a_in_p) => [p1 p2' irr_p1 irr_p2' _]. subst p.
    case: (idx_nLR irr_p b_in_p) => // Y1 Y2.
    case/(isplitP irr_p2') def_p1' : _ / (tailW Y2) => [p2 p3 irr_p2 irr_p3 D2]. subst p2'.
    exists p1. exists p2. exists p3. split => //. 
    have A: a != b. { apply: contraTN a_before_b => /eqP=>?. subst b. by rewrite ltnn. }
    apply: contraNN A => A. by rewrite [a]D2 // path_begin.
  Qed.

End PathIndexing.


(** ** Connectedness *)

(** *** Between nodes (reflection lemmas) *)

(** NOTE: need to require either x != y or x \in A since packaged
paths are never empty *)
Lemma uPathRP (G : sgraph) {A : pred G} x y : x != y ->
  reflect (exists2 p: Path x y, irred p & p \subset A) 
          (connect (restrict A sedge) x y).
Proof.
  move => Hxy. apply: (iffP connectUP). 
  - move => [p [p1 p2 p3]]. 
    have pth_p : spath x y p. 
    { rewrite /spath p2 eqxx andbT. 
      apply: sub_path p1. exact: subrel_restrict. }
    exists (Build_Path pth_p); first by rewrite /irred nodesE.
    apply/subsetP => z. rewrite mem_path SubK inE. 
    case: p p1 p2 {p3 pth_p} => [/= _ /eqP?|a p pth_p _]; first by contrab.
    case/predU1P => [->|]; last exact: path_restrict pth_p _.
    move: pth_p => /=. by case: (x \in A).
  - move => [p irr_p subA]. case/andP: (valP p) => p1 /eqP p2.
    exists (val p); split => //; last by rewrite /irred nodesE in irr_p.
    have/andP [A1 A2] : (x \in A) && (val p \subset A).
    { move/subsetP : subA => H. rewrite !H ?path_begin //=. 
      apply/subsetP => z Hz. apply: H. by rewrite mem_path !inE Hz. }
    apply: restrict_path => //. exact/subsetP.
Qed.

(* This is only useful if the [x = y] case does not require [x \in A] *)
Lemma connect_restrict_case (G : sgraph) (x y : G) (A : pred G) : 
  connect (restrict A sedge) x y -> 
  x = y \/ [/\ x != y, x \in A, y \in A & connect (restrict A sedge) x y].
Proof.
  case: (altP (x =P y)) => [|? conn]; first by left. 
  case/uPathRP : (conn) => // p _ /subsetP subA. 
  right; split => //; by rewrite subA ?path_end ?path_begin.
Qed.

Lemma PathRP (G : sgraph) {A : pred G} x y : x != y ->
  reflect (exists p: Path x y, p \subset A)
          (connect (restrict A sedge) x y).
Proof.
  move=> xNy; apply: (iffP (uPathRP xNy)); first by firstorder.
  move=> [p] p_sub_A. case: (uncycle p) => [q] /subsetP q_sub_p Iq.
  by exists q; last apply: subset_trans p_sub_A.
Qed.

Lemma connectRI (G : sgraph) (A : pred G) x y (p : Path x y) :
  {subset p <= A} -> connect (restrict A sedge) x y.
Proof. 
  case: (boolP (x == y)) => [/eqP ?|]; first by subst y; rewrite connect0. 
  move => xy subA. apply/uPathRP => //. case: (uncycle p) => p' p1 p2.
  exists p' => //. apply/subsetP => z /p1. exact: subA.
Qed.

(** *** Of subsets *)

Definition connected (G : sgraph) (S : {set G}) :=
  {in S & S, forall x y : G, connect (restrict (mem S) sedge) x y}.

Definition disconnected (G : sgraph) (S : {set G}) :=
  exists x y : G, [/\ x \in S, y \in S & ~~ connect (restrict (mem S) sedge) x y].

Lemma disconnectedE (G : sgraph) (S : {set G}) : disconnected S <-> ~ connected S.
Proof.
  split; first by case=> [x] [y] [x_S y_S /negP xNy] /(_ x y x_S y_S).
  move=> SNconn. apply/'exists_'exists_and3P.
  rewrite -[X in is_true X]negbK. apply/negP => SNdisconn.
  apply: SNconn => x y x_S y_S. move: SNdisconn.
  rewrite negb_exists => /forallP/(_ x). rewrite negb_exists => /forallP/(_ y).
  by rewrite x_S y_S /= negbK.
Qed.

Lemma connectedTE (G : sgraph) : 
  connected [set: G] -> forall x y : G, connect sedge x y. 
Proof. 
  move => A x y. move: (A x y). 
  rewrite !inE !restrictE; first by apply. by move => ?; rewrite !inE.
Qed.

Lemma connectedTI (G : sgraph) : 
  (forall x y : G, connect sedge x y) -> connected [set: G].
Proof. move => H x y _ _. rewrite restrictE // => z. by rewrite inE. Qed.

Lemma connected_restrict (G : sgraph) (A : pred G) x : 
  connected [set y | connect (restrict A sedge) x y].
Proof.
  move => u v. rewrite !inE => Hu Hv. move defP : (mem _) => P.
  wlog suff W: u Hu / connect (restrict P sedge) x u.
  { apply: connect_trans (W _ Hv). rewrite srestrict_sym. exact: W. }
  case: (altP (x =P u)) => [-> //|xDu].
  case/uPathRP : Hu => // p Ip Ap.
  apply connectRI with p => z in_p.
  rewrite -defP inE. case/psplitP : in_p Ap => p1 p2 Ap. 
  apply connectRI with p1. apply/subsetP. 
  apply: subset_trans Ap. exact: subset_pcatL.
Qed.

Lemma connect_range (G : sgraph) (A : pred G) x : x \in A -> 
  [set y | connect (restrict A sedge) x y] = 
  [set y in A | connect (restrict A sedge) x y].
Proof. 
  move => inA. apply/setP => z. rewrite !inE srestrict_sym.
  apply/idP/andP => [|[//]]. by case/connect_restrict_case => [->|[]].
Qed.

Lemma connected_restrict_in (G : sgraph) (A : pred G) x : x \in A -> 
  connected [set y in A | connect (restrict A sedge) x y].
Proof. move => inA. rewrite -connect_range //. exact: connected_restrict. Qed.

(* NOTE: This could be generalized to sets and their images *)
Lemma iso_connected (G H : sgraph) :
  sg_iso G H -> connected [set: H] -> connected [set: G].
Proof.
  case => g h can_g can_h hom_g hom_h con_H x y _ _.
  rewrite restrictE; last by move => z; rewrite !inE.
  have := con_H (h x) (h y). rewrite !inE => /(_ isT isT).
  rewrite restrictE; last by move => z; rewrite !inE.
  case/spathP => p. case/lift_spath => //.
  + move => {x y} x y. rewrite -{2}[x]can_h -{2}[y]can_h. exact: hom_g.
  + exact: can_inj can_h.
  + move => z _. apply/codomP. exists (g z). by rewrite can_g.
  + move => p' [Hp' _]. apply/spathP. by exists p'.
Qed.

Lemma connected1 (G : sgraph) (x : G) : connected [set x].
Proof. move => ? ? /set1P <- /set1P <-. exact: connect0. Qed.

Lemma connected2 (G : sgraph) (x y: G) : x -- y -> connected [set x; y].
Proof.
  move=> xy ? ? /set2P[]-> /set2P[]->; try exact: connect0;
  apply: connect1; rewrite /= !inE !eqxx orbT //=. by rewrite sg_sym.
Qed.

Lemma connected_center (G:sgraph) x (S : {set G}) :
  {in S, forall y, connect (restrict (mem S) sedge) x y} -> x \in S ->
  connected S.
Proof.
  move => H inS y z Hy Hz. apply: connect_trans (H _ Hz).
  rewrite connect_symI; by [apply: H | apply: symmetric_restrict_sedge].
Qed.


Lemma connectedU_common_point (G : sgraph) (U V : {set G}) (x : G):
  x \in U -> x \in V -> connected U -> connected V -> connected (U :|: V).
Proof.
  move => xU xV conU conV. 
  apply connected_center with x; last by rewrite !inE xU.
  move => y. case/setUP => [yU|yV]. 
  - apply: connect_restrict_mono (conU _ _ xU yU); exact: subsetUl.
  - apply: connect_restrict_mono (conV _ _ xV yV); exact: subsetUr.
Qed.


Lemma connectedU_edge (G : sgraph) (U V : {set G}) (x y : G) :
  x \in U -> y \in V -> x -- y -> connected U -> connected V -> connected (U :|: V).
Proof.
  move=> x_U y_V xy U_conn V_conn u v u_UV v_UV.
  have subl : {subset mem U <= mem (U :|: V)} by move=> ?; rewrite !inE =>->.
  have subr : {subset mem V <= mem (U :|: V)} by move=> ?; rewrite !inE =>->.
  case: (altP (u =P v)) => [->|uNv]; first exact: connect0.
  wlog [u_U v_V] : u v uNv {u_UV v_UV} / u \in U /\ v \in V.
  { move=> Hyp. move: u_UV v_UV. rewrite !inE.
    move=> /orP[u_U | u_V] /orP[v_U | v_V].
    - apply: connect_mono (U_conn u v u_U v_U). exact: restrict_mono.
    - exact: Hyp.
    - rewrite srestrict_sym. apply: Hyp; by [rewrite eq_sym |].
    - apply: connect_mono (V_conn u v u_V v_V). exact: restrict_mono. }
  apply: (@connect_trans _ _ y); last first.
  { apply: connect_mono (V_conn y v y_V v_V). exact: restrict_mono. }
  apply: (@connect_trans _ _ x).
  { apply: connect_mono (U_conn u x u_U x_U). exact: restrict_mono. }
  by apply: connect1; rewrite /= !inE x_U y_V xy.
Qed.


Lemma connected_path (G : sgraph) (x y : G) (p : Path x y) :
  connected [set z in p].
Proof. 
  apply: (@connected_center _ x); last by rewrite inE.
  move => z. rewrite inE => A. case/psplitP : _ / A => {p} p1 p2.
  apply: (connectRI (p := p1)) => u Hu. by rewrite inE mem_pcat Hu.
Qed.

Lemma connected_in_subgraph (G : sgraph) (S : {set G}) (A : {set induced S}) : 
  connected A -> connected [set val x | x in A].
Proof.
  move => conn_A ? ? /imsetP [/= x xA ->] /imsetP [/= y yA ->].
  case: (boolP (x == y)) => [/eqP->|Hxy]; first exact: connect0.
  move: (conn_A _ _ xA yA) => /uPathRP. move/(_ Hxy) => [p irr_p /subsetP subA]. 
  case: (Path_from_induced p) => q sub_S Hq. 
  apply: (connectRI (p := q)) => z.
  rewrite in_collective Hq => /mapP[z'] /subA Hz' ->.
  exact: mem_imset.
Qed.

Lemma connected_induced (G : sgraph) (S : {set G}) : 
  connected S -> connected [set: induced S].
Proof.
  move => conn_S x y _ _. 
  rewrite restrictE => [|u]; last by rewrite inE.
  have/uPathRP := conn_S _ _ (valP x) (valP y).
  case: (boolP (val x == val y)) => [|E /(_ isT) [p] _ /subsetP sub_S].
  - rewrite val_eqE => /eqP-> _. exact: connect0.
  - case: (Path_to_induced sub_S) => q _. exact: Path_connect q.
Qed.

Lemma connected_card_gt1 (G : sgraph) (S : {set G}) :
  connected S -> {in S &, forall x y, x != y -> exists2 z, z \in S & x -- z }.
Proof.
  move=> conn_S x y x_S y_S xNy.
  move: conn_S => /(_ x y x_S y_S)/(PathRP xNy)[p]/subsetP p_S.
  case: (splitL p xNy) => [z] [xz] [p'] [_ eqi_p'].
  exists z; last by []; apply: p_S.
  by rewrite in_collective nodesE inE -eqi_p' path_begin.
Qed.



(** *** Connected components *)

Definition components (G : sgraph) (H : {set G}) : {set {set G}} :=
  equivalence_partition (connect (restrict (mem H) sedge)) H.

Lemma partition_components (G : sgraph) (H : {set G}) :
  partition (components H) H.
Proof. apply: equivalence_partitionP. exact: (@sedge_equiv_in G). Qed.

Lemma components_pblockP (G : sgraph) (H : {set G}) (x y : G) :
  reflect (exists p : Path x y, p \subset H) (y \in pblock (components H) x).
Proof.
  apply: (iffP idP).
  - case/(pblock_eqvE (@sedge_equiv_in _ _)) => xH yH. 
    wlog xNy : / x != y.
    { move=> Hyp. case: (altP (x =P y)) => [<- _|]; last exact: Hyp.
      exists (idp x). apply/subsetP=> z. by rewrite mem_idp => /eqP->. }
    case/(PathRP xNy) => p p_sub. by exists p.
  - case=> p /subsetP p_sub. rewrite pblock_equivalence_partition.
    + exact: connectRI p_sub.
    + exact: sedge_equiv_in.
    + apply: p_sub; exact: path_begin.
    + apply: p_sub; exact: path_end.
Qed.


Lemma connected_in_components (G : sgraph) (H C : {set G}) :
  C \in components H -> connected C.
Proof.
  have PEQ := pblock_equivalence_partition (@sedge_equiv_in G H).
  move => C_comp.  
  case/and3P: (partition_components H) => /eqP compU compI comp0.
  have/set0Pn [x in_C] : C != set0. by apply: contraNN comp0 => /eqP<-.
  have CH: {subset C <= H}. 
  { move => z Hz. rewrite -compU. apply/bigcupP; by exists C. } 
  move/CH : (in_C) => in_H. 
  suff -> : C = [set y in H | connect (restrict (mem H) sedge) x y].
  { exact: connected_restrict_in. }
  apply/setP => y. rewrite inE. case: (boolP (y \in H)) => /= [y_in_H|y_notin_H].
  - by rewrite -PEQ // ?(def_pblock _ C_comp).
  - apply: contraNF y_notin_H. exact: CH.
Qed.


Lemma component_exit (G : sgraph) (V C : {set G}) (x y : G) :
  x -- y -> C \in components V -> x \in C -> y \in ~: V :|: C.
Proof.
  move=> xy C_comp x_C. rewrite !inE -implybE. apply/implyP => y_V.
  case/and3P: (partition_components V) => /eqP compU compI comp0n.
  have x_V : x \in V by rewrite -compU; apply/bigcupP; exists C.
  rewrite -(def_pblock compI C_comp x_C) pblock_equivalence_partition //;
    last exact: sedge_equiv_in.
  apply/PathRP; first by rewrite sg_edgeNeq.
  exists (edgep xy); apply/subsetP=> z; rewrite mem_edgep.
  by case/orP=> /eqP->.
Qed.

Lemma remove_component (G : sgraph) (V C : {set G}) (x0 : G) : x0 \notin V ->
  C \in components V -> connected [set: G] -> connected (~: V) -> connected (~: C).
Proof.
  move=> ? C_comp G_conn VC_conn.
  case/and3P: (partition_components V) => /eqP compU compI _.
  have sub : C \subset V by rewrite -compU; exact: bigcup_sup.
  have subr : subrel (connect (restrict (mem (~: V)) sedge))
                     (connect (restrict (mem (~: C)) sedge))
    by apply: connect_mono; apply: restrict_mono; apply/subsetP; rewrite setCS.
  suff to_x0 (x : G) : x \in ~: C -> connect (restrict (mem (~: C)) sedge) x x0.
  { move=> x y /to_x0 x_x0 /to_x0. rewrite srestrict_sym. exact: connect_trans. }
  rewrite inE => xNC. wlog x_V : x xNC / x \in V.
  { move=> Hyp. case: (boolP (x \in V)); first exact: Hyp. move=> xNV.
    apply: subr. apply: VC_conn; by rewrite inE. }
  case/uPathP: (connectedTE G_conn x x0) => p Ip.
  have x0_VC : x0 \in ~: V by rewrite inE.
  case: (split_at_first x0_VC (path_end p)) => [x1][p1][p2][Ep x1_VC x1_first].
  have {p p2 Ep Ip} Ip1 : irred p1 by move: Ip; rewrite Ep irred_cat; case/and3P.
  apply: connect_trans (subr _ _ (VC_conn _ _ x1_VC x0_VC)).
  rewrite inE in x1_VC. apply/PathRP; first by apply: contraNneq x1_VC => <-.
  exists p1. apply/subsetP=> z z_p1. rewrite inE.
  case: (altP (z =P x1)) => [->|zNx1]; first by apply: contraNN x1_VC; apply/subsetP.
  apply: contraNN xNC => z_C.
  rewrite -(def_pblock compI C_comp z_C). apply/components_pblockP.
  case/(isplitP Ip1) Ep1 : _ / z_p1 => [q1 q2 _ _ H].
  have x1Nq1 : x1 \notin q1 by apply: contraNN zNx1 => A; rewrite [x1]H.
  exists (prev q1). apply/subsetP=> u. rewrite mem_prev => u_q1.
  apply: contraNT x1Nq1 => uNV. rewrite -(x1_first u) ?inE //.
  by rewrite Ep1 mem_pcat u_q1.
Qed.

(** *** Cliques *)

Definition clique (G : sgraph) (S : {set G}) :=
  {in S&S, forall x y, x != y -> x -- y}.

Lemma clique1 (G : sgraph) (x : G) : clique [set x].
Proof. move => y z /set1P-> /set1P ->. by rewrite eqxx. Qed.

Lemma clique2 (G : sgraph) (x y : G) : x -- y -> clique [set x;y].
Proof.
  move => xy z z'. rewrite !inE.
  do 2 case/orP => /eqP-> // ; try by rewrite eqxx.
  by rewrite sg_sym.
Qed.


(** ** Forests and Trees

As with connected, we define forest and set predicates for sets of
vertices of some graph. This avoids having to package subtrees (such
as [CP U] for neighbors U) as a graph *)

Section Forests.

Variables (G : sgraph).
Implicit Types (x y : G) (S : {set G}).

Definition is_forest S :=
  forall x y : G, unique (fun p : Path x y => irred p /\ (p \subset S)).

Definition is_tree S := is_forest S /\ connected S.

Definition is_forestb S := 
  [forall x in S, forall y in S, #|[pred p : IPath x y| val p \subset S]| <= 1] .

Lemma is_forestP S : reflect (is_forest S) (is_forestb S).
Proof.
  apply: (iffP idP) => H.
  - move => x y p q [Ip Sp] [Iq Sq]. have [xS yS] : x \in S /\ y \in S.
    { by split; apply: (subsetP Sp); rewrite ?path_begin ?path_end. }
    move/forall_inP/(_ _ xS)/forall_inP/(_ _ yS) : H => H.
    suff: Sub p Ip == Sub q Iq :> IPath x y by rewrite -val_eqE => /eqP.
    apply/eqP. apply: card_le1 H _ _; by rewrite inE.
  - apply/forall_inP => x xS. apply/forall_inP => y yS. 
    apply/card_le1P => [[p Ip]] [q Iq]. rewrite !inE /= => pS qS.
    apply: val_inj => /=. exact: H.
Qed.

Definition connectedb S := 
  [forall x in S, forall y in S, connect (restrict (mem S) sedge) x y].

Lemma connectedP S : reflect (connected S) (connectedb S).
Proof. 
  apply: (iffP idP) => H.
  - move => x y xS yS. by move/forall_inP/(_ _ xS)/forall_inP/(_ _ yS) : H.
  - do 2 apply/forall_inP => ? ?. exact: H.
Qed.

Lemma forestT_unique : 
  is_forest [set: G] -> forall x y, unique (fun p : Path x y => irred p).
Proof. move => H x y p q Ip Iq. exact: H. Qed.

Lemma unique_forestT : 
  (forall x y, unique (fun p : Path x y => irred p)) -> is_forest [set: G].
Proof. move => H x y p q [Ip _] [Iq _]. exact: H. Qed.

Lemma forestI S : 
  ~ (exists x y (p1 p2 : Path x y), [/\ irred p1, irred p2 & p1 != p2] /\ 
     [/\ x \in S, y \in S, p1 \subset S & p2\subset S]) ->
  is_forest S.
Proof.
  move=> H x y p1 p2 [Ip1 Sp1] [Ip2 Sp2]. case: (altP (p1 =P p2)) => // pN12.
  have [xS yS] : x \in S /\ y \in S.
  { by split; apply: (subsetP Sp1); rewrite ?path_begin ?path_end. }
  case: H. exists x; exists y; exists p1; exists p2. by repeat split.
Qed.

Lemma treeI S : 
  connected S -> 
  ~ (exists x y (p1 p2 : Path x y), [/\ irred p1, irred p2 & p1 != p2] /\ 
     [/\ x \in S, y \in S, p1 \subset S & p2\subset S]) ->
  is_tree S.
Proof. move => A B. split => //. exact: forestI. Qed.

Lemma sub_forest S S' : 
  S' \subset S -> is_forest S -> is_forest S'.
Proof.
  move => subS H x y p q [Ip Sp] [Iq Sq].
  apply: H; try split; 
    try solve [ done |exact: (subsetP subS) | exact: subset_trans subS].
Qed.
 
End Forests.

(** *** Forest Type (for tree decompositions) *)

(** We define forests to be simple graphs where there exists at most one
duplicate free path between any two nodes *)

Record forest := Forest { sgraph_of_forest :> sgraph ;
                          forest_is_forest :> is_forest [set: sgraph_of_forest] }.

Lemma forestP (T : forest) (x y : T) (p q : Path x y) :
  irred p -> irred q -> p = q.
Proof.
  move/forestT_unique : (@forest_is_forest T) => fP.
  move => Ip Iq. exact: fP.
Qed.

Definition sunit := @SGraph [finType of unit] rel0 rel0_sym rel0_irrefl.

Definition unit_forest : is_forest [set: sunit].
Proof. by move => [] [] p1 p2 [/irredxx -> _] [/irredxx -> _]. Qed.

Definition tunit := Forest unit_forest.

(** We define [width] and [rename] for tree decompositions already
here, so that we can use use them for tree decompositions of simple
graphs and directed graphs. *)

(** Non-standard: we do not substract 1 *)
Definition width (T G : finType) (D : T -> {set G}) := \max_(t:T) #|D t|.

Lemma width_bound (T G : finType) (D : T -> {set G}) : width D <= #|G|.
Proof. apply/bigmax_leqP => t _; exact: max_card. Qed.

Definition rename (T G G' : finType) (B: T -> {set G}) (h : G -> G') :=
  [fun x => h @: B x].


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

(** ** Adding Edges *)

Definition add_edge_rel (G:sgraph) (i o : G) := 
  relU (@sedge G) (sc [rel x y | [&& x != y, x == i & y == o]]).

Lemma add_edge_sym (G:sgraph) (i o : G) : symmetric (add_edge_rel i o).
Proof. apply: relU_sym'. exact: sg_sym. exact: sc_sym. Qed.

Lemma add_edge_irrefl (G:sgraph) (i o : G) : irreflexive (add_edge_rel i o).
Proof. move => x /=. by rewrite sg_irrefl eqxx. Qed.

Definition add_edge (G:sgraph) (i o : G) :=
  {| svertex := G;
     sedge := add_edge_rel i o;
     sg_sym := add_edge_sym i o;
     sg_irrefl := add_edge_irrefl i o |}.

Lemma add_edge_Path (G : sgraph) (i o x y : G) (p : @Path G x y) :
  exists q : @Path (add_edge i o) x y, nodes q = nodes p.
Proof.
  case: p => p p_pth.
  have p_iopth : @spath (add_edge i o) x y p.
  { case/andP: p_pth => p_path p_last. apply/andP; split=> //.
    apply: sub_path p_path. by move=> u v /=->. }
  by exists (Sub (p : seq (add_edge i o)) p_iopth).
Qed.

Lemma add_edge_connected (G : sgraph) (i o : G) (U : {set G}) :
  @connected G U -> @connected (add_edge i o) U.
Proof.
  move => con1 x y xU yU. 
  apply: connect_mono (con1 _ _ xU yU) => {x y xU yU} x y /=.
  by rewrite -andbA => /and3P[-> -> ->].
Qed.

Lemma add_edgeC (G : sgraph) (s1 s2 : G):
  @sedge (add_edge s1 s2) =2 @sedge (add_edge s2 s1).
Proof.
  move => x y. rewrite /= [y == x]eq_sym. 
  by case (x -- y) => //=; do ! (case (_ == _); rewrite //=).
Qed.
Arguments add_edgeC [G].

Lemma eq_connected (V : finType) (e1 e2 : rel V) (A : {set V}) 
  (e1_sym : symmetric e1) (e1_irrefl : irreflexive e1) 
  (e2_sym : symmetric e2) (e2_irrefl : irreflexive e2):
  e1 =2 e2 -> 
  @connected (SGraph e1_sym e1_irrefl) A <-> @connected (SGraph e2_sym e2_irrefl) A.
Proof.
  move => E. split.
  - move => H x y xA yA. erewrite eq_connect. eapply H => //. 
    move => u v. by rewrite /= E.
  - move => H x y xA yA. erewrite eq_connect. eapply H => //. 
    move => u v. by rewrite /= E.
Qed.
  

Lemma add_edge_connected_sym (G : sgraph) s1 s2 A:
  @connected (@add_edge G s1 s2) A <-> @connected (@add_edge G s2 s1) A.
Proof. apply: eq_connected => u v. exact: (add_edgeC s1 s2). Qed.

Lemma add_edge_keep_connected_l (G : sgraph) s1 s2 A:
  @connected (@add_edge G s1 s2) A -> s1 \notin A -> @connected G A.
Proof.
  move => H s1A x y xA yA. case: (altP (x =P y)) => [-> //|xDy].
  case/uPathRP : (H _ _ xA yA) => // p Ip /subsetP subA. 
  case: (@lift_Path_on G (add_edge s1 s2) id x y p) => //.
  - move => u v up vp /=. case: (_ -- _ ) => //=. 
    case/orP => /and3P[? /eqP ? /eqP ?]; subst; by rewrite subA in s1A. 
  - move => u. by rewrite mem_map // mem_enum.
  - move => p' nodeE irrE. apply connectRI with p' => u.
    rewrite mem_path -nodesE -(mem_map (f := id)) // nodeE nodesE.
    rewrite -(@mem_path (add_edge s1 s2)). exact: subA.
Qed.

(** Adding Vertices *)

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

(** ** Neighboring sets *)

Section Neighbor.
  Variable (G : sgraph).
  Implicit Types A B C D : {set G}.
  
  Definition neighbor A B := [exists x in A, exists y in B, x -- y].
  
  Lemma neighborP A B : reflect (exists x y, [/\ x \in A, y \in B & x -- y]) (neighbor A B).
  Proof.
    apply:(iffP exists_inP) => [[x xA] /exists_inP [y inB xy]|[x] [y] [xA yB xy]].
    - by exists x; exists y.
    - exists x => //. apply/exists_inP; by exists y.
  Qed.

  Lemma neighborC A B : neighbor A B = neighbor B A.
  Proof. by apply/neighborP/neighborP => [] [x] [y] [*];exists y; exists x; rewrite sgP. Qed.

  Lemma neighbor_connected A B : 
    connected A -> connected B -> neighbor A B -> connected (A :|: B).
  Proof. 
    move => conA conB /neighborP [x] [y] [? ? xy]. 
    exact: connectedU_edge xy _ _.
  Qed.

  Lemma neighborW C D A B : 
    C \subset A -> D \subset B -> neighbor C D -> neighbor A B.
  Proof.
    move/subsetP => subA /subsetP subB /neighborP [x] [y] [? ? ?].
    apply/neighborP; exists x; exists y. by rewrite subA ?subB.
  Qed.

  
End Neighbor.
Arguments neighborW : clear implicits.

Lemma neighbor_add_edgeC (G : sgraph) (s1 s2 : G) :
  @neighbor (add_edge s1 s2) =2 @neighbor (add_edge s2 s1).
Proof. 
  move => x y.
  apply/neighborP/neighborP => [] [u] [v] [? ? ?]; exists u; exists v.
  all: by rewrite add_edgeC.
Qed.

Lemma neighbor_del_edgeR (G : sgraph) (s1 s2 : G) (A B : {set G}) :
  s1 \notin B -> s2 \notin B -> @neighbor (add_edge s1 s2) A B -> @neighbor G A B.
Proof.
  move => H1 H2 /neighborP [x] [y] [/= N1 N2 N3]. apply/neighborP. exists x; exists y.
  case/or3P : N3 => [-> //|] /and3P [_ /eqP ? /eqP ?]; by subst;contrab.
Qed.

Lemma neighbor_del_edge2 (G : sgraph) (s1 s2 : G) (A B : {set G}) :
  s2 \notin A -> s2 \notin B -> @neighbor (add_edge s1 s2) A B -> @neighbor G A B.
Proof.
  move => H1 H2 /neighborP [x] [y] [/= N1 N2 N3]. apply/neighborP. exists x; exists y.
  case/or3P : N3 => [-> //|] /and3P [_ /eqP ? /eqP ?]; by subst;contrab.
Qed.

Lemma neighbor_del_edge1 (G : sgraph) (s1 s2 : G) (A B : {set G}) :
  s1 \notin A -> s1 \notin B -> @neighbor (add_edge s1 s2) A B -> @neighbor G A B.
Proof. move => ? ?. rewrite neighbor_add_edgeC. exact: neighbor_del_edge2. Qed.

Lemma neighbor_add_edge (G : sgraph) (s1 s2 : G) : 
  subrel (@neighbor G) (@neighbor (add_edge s1 s2)).
Proof. 
  move => A B /neighborP [u] [v] [? ? E]. 
  apply/neighborP; exists u; exists v. by rewrite /= E.
Qed.

Lemma neighbor_split (G : sgraph) (A B C1 C2 : {set G}) :
  B \subset C1 :|: C2 -> neighbor A B -> neighbor A C1 || neighbor A C2.
Proof.
  move/subsetP => S /neighborP [u] [v] [? /S H E]. apply/orP.
  by case/setUP : H => ?; [left|right]; apply/neighborP; exists u; exists v.
Qed.
