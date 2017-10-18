From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 


(** * Simple Graphs *)

Record sgraph := SGraph { svertex :> finType ; 
                         sedge: rel svertex; 
                         sg_sym: symmetric sedge;
                         sg_irrefl: irreflexive sedge}.

Record sgraph2 := SGraph2 { sgraph_of :> sgraph; 
                            s_in : sgraph_of; 
                            s_out : sgraph_of}.

Arguments s_in [s].
Arguments s_out [s].
Notation "x -- y" := (sedge x y) (at level 30).
Definition sgP := (sg_sym,sg_irrefl).
Prenex Implicits sedge.

(** ** Homomorphisms *)

Definition hom_s (G1 G2 : sgraph) (h : G1 -> G2) := 
  forall x y, x -- y -> (h x = h y) \/ (h x -- h y).

Definition hom_s2 (G1 G2 : sgraph2) (h : G1 -> G2) :=
  [/\ hom_s h , h s_in = s_in & h s_out = s_out].

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
  Proof. exists val => //. exact: val_inj. by right. Qed.

End InducedSubgraph.

Lemma irreflexive_restrict (T : Type) (e : rel T) (A : pred T) : 
  irreflexive e -> irreflexive (restrict A e).
Proof. move => irr_e x /=. by rewrite irr_e. Qed.

Definition srestrict (G : sgraph) (A : pred G) :=
  Eval hnf in SGraph (symmetric_restrict A (@sg_sym G))
                     (irreflexive_restrict A (@sg_irrefl G)).


(** ** Paths through simple graphs *)


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

(** Lemmas on splitting and concatenating paths between nodes *)
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
x p] forgets the last element of [p]. Consequently, doulbe reversal
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


End SimplePaths.
Arguments spath_last [G].

(** ** Irredundant Paths *)

Section Upath.
Variable (G : sgraph).
Implicit Types (x y z : G).

Definition upath x y p := uniq (x::p) && spath x y p.

Lemma upathW x y p : upath x y p -> spath x y p.
Proof. by case/andP. Qed.

Lemma upath_uniq x y p : upath x y p -> uniq (x::p).
Proof. by case/andP. Qed.

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
  { apply: rev_belast S _. apply: U; exact: rev_upath. }
  rewrite !(spath_last x) //; exact: upathW.
Qed.

Lemma upath_cons x y z p : 
  upath x y (z::p) = [&& x -- z, x \notin (z::p) & upath z y p].
Proof. 
  rewrite /upath spath_cons [z::p]lock /= -lock.
  case: (x -- z) => //. by case (uniq _).
Qed.

Lemma upath_consE x y z p : upath x y (z :: p) -> [/\ x -- z, x \notin z :: p & upath z y p].
Proof. rewrite upath_cons. by move/and3P. Qed.

(* TODO: should be upathxx *)
Lemma upath_refl x : upath x x [::].
Proof. by rewrite /upath spathxx. Qed.

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

(* CoInductive usplitr z x y : seq G -> Prop :=  *)
(*   USplit p1 p2 : upath x z p1 -> upath z y p2 -> [disjoint x::rcons p1 z & p2] *)
(*                  -> usplit z x y (p1 ++ p2). *)


(* Lemma usplitPr z x y p : z \in p -> upath x y p -> usplit z x y p. *)


Lemma upathP x y : reflect (exists p, upath x y p) (connect sedge x y).
Proof.
  apply: (iffP connectP) => [[p p1 p2]|[p /and3P [p1 p2 /eqP p3]]]; last by exists p.
  exists (shorten x p). case/shortenP : p1 p2 => p' ? ? _ /esym/eqP ?. exact/and3P. 
Qed.

(* Really useful? *)
Lemma spathP x y : reflect (exists p, spath x y p) (connect sedge x y).
Proof. 
  apply: (iffP idP) => [|[p] /andP[A /eqP B]]; last by apply/connectP; exists p.
  case/upathP => p /upathW ?. by exists p.
Qed.

End Upath.

Lemma restrict_upath (G:sgraph) (x y:G) (A : pred G) (p : seq G) : 
  @upath (srestrict A) x y p -> upath x y p.
Proof. 
  elim: p x => // z p IH x /upath_consE [/= /andP [_ u1] u2 u3]. 
  rewrite upath_cons u1 u2 /=. exact: IH.
Qed.

Lemma lift_spath (G H : sgraph) (f : G -> H) a b p' : 
  (forall x y, f x -- f y -> x -- y) -> injective f -> 
  spath (f a) (f b) p' -> {subset p' <= codom f} -> exists p, spath a b p /\ map f p = p'.
Proof. 
  move => A I /andP [B /eqP C] D.  case: (lift_path A B D) => p [p1 p2]; subst. 
  exists p. split => //. apply/andP. split => //. rewrite last_map in C. by rewrite (I _ _ C).
Qed.

Lemma lift_upath (G H : sgraph) (f : G -> H) a b p' : 
  (forall x y, f x -- f y -> x -- y) -> injective f -> 
  upath (f a) (f b) p' -> {subset p' <= codom f} -> exists p, upath a b p /\ map f p = p'.
Proof.
  move => A B /andP [C D] E. case: (lift_spath A B D E) => p [p1 p2].
  exists p. split => //. apply/andP. split => //. by rewrite -(map_inj_uniq B) /= p2.
Qed.



Ltac spath_tac :=
  repeat match goal with [H : is_true (upath _ _ _) |- _] => move/upathW : H => H end;
  eauto using spath_concat, spath_rev.

(** ** Packaged paths *)

Section Pack.
Variables (G : sgraph).
Implicit Types x y z : G.

Section PathDef.
  Variables (x y : G).

  Record Path := { pval : seq G; _ : spath x y pval }.

  (* Inductive Path := BPath p of spath x y p.   *)
  (* Definition pval p := let: BPath s _ := p in s.  *)

  Canonical Path_subType := [subType for pval].
  Definition Path_eqMixin := Eval hnf in [eqMixin of Path by <:]. 
  Canonical Path_eqType := Eval hnf in EqType Path Path_eqMixin.
  

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

Lemma mem_path x y (p : Path x y) u : u \in p = (u \in x :: val p).
Proof. by rewrite in_collective /nodes -lock. Qed.

Section PathTheory.
Variables (x y z : G) (p : Path x y) (q : Path y z).

Lemma nodes_end : y \in p. 
Proof. by rewrite mem_path -[in X in X \in _](path_last p) mem_last. Qed.

Lemma nodes_start : x \in p.
Proof. by rewrite mem_path mem_head. Qed.

Lemma mem_pcatT u : (u \in pcat p q) = (u \in p) || (u \in tail q).
Proof. by rewrite !mem_path !inE mem_cat -orbA. Qed.

Lemma tailW : {subset tail q <= q}.
Proof. move => u. rewrite mem_path. exact: mem_tail. Qed.

Lemma mem_pcat u :  (u \in pcat p q) = (u \in p) || (u \in q).
Proof. 
  rewrite mem_pcatT. case A: (u \in p) => //=. 
  rewrite mem_path inE (_ : u == y = false) //. 
  apply: contraFF A => /eqP->. exact: nodes_end. 
Qed.

End PathTheory.

(** Providing an injection from (proofs of [x -- y]) to one edge paths
and then using the monoid structure with [pcat] seems preferable to
providing a cons operation *)

Lemma edgep_proof x y (xy : x -- y) : spath x y [:: y]. 
Proof. by rewrite spath_cons xy spathxx. Qed.

Definition edgep x y (xy : x -- y) := Build_Path (edgep_proof xy).

Lemma mem_edgep x y z (xy : x -- y) :
  z \in edgep xy = (z == x) || (z == y).
Proof. by rewrite mem_path !inE. Qed.

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

Lemma mem_prev x y (p : Path x y) u : (u \in prev p) = (u \in p).
Proof. rewrite !mem_path -srev_nodes //. exact: valP. Qed.

Lemma Path_split z x y (p : Path x y) : 
  z \in p -> exists (p1 : Path x z) p2, p = pcat p1 p2.
Proof.
  move: (valP p) => pth_p in_p. rewrite mem_path in in_p.
  case/(ssplitP in_p) E : {1}(val p) / pth_p => [p1 p2 P1 P2].
  exists (Sub p1 P1). exists (Sub p2 P2). exact: val_inj. 
Qed.

Lemma irred_cat x y z (p : Path x z) (q : Path z y) : 
  irred (pcat p q) = [&& irred p, irred q & [disjoint p & tail q]].
Proof.
  rewrite /irred {1}/nodes -lock /pcat SubK -cat_cons cat_uniq -disjoint_has disjoint_sym -nodesE.
  case A : [disjoint _ & _] => //. case: (uniq (nodes p)) => //=. rewrite nodesE /=.
  case: (uniq _) => //=. by rewrite !andbT (disjointFr A _) // nodes_end. 
Qed.

Lemma prev_irred x y (p : Path x y) : irred p -> irred (prev p).
Proof.
  rewrite /irred /nodes => U. apply: leq_size_uniq U _ _. 
  - move => u. by rewrite mem_prev.
  - by rewrite -!lock /= ltnS /srev size_rev size_belast.
Qed.
 
Lemma uPathP x y : reflect (exists p : Path x y, irred p) (connect sedge x y).
Proof. 
  apply: (iffP (upathP _ _)) => [[p /andP [U P]]|[p I]]. 
  + exists (Sub p P).  by rewrite /irred nodesE.
  + exists (val p). apply/andP;split; by [rewrite /irred nodesE in I| exact: valP].
Qed.

CoInductive isplit z x y : Path x y -> Prop := 
  ISplit (p1 : Path x z) (p2 : Path z y) : 
    irred p1 -> irred p2 -> [disjoint p1 & tail p2] -> isplit z (pcat p1 p2).

Lemma isplitP z x y (p : Path x y) : irred p -> z \in p -> isplit z p.
Proof.
  move => I in_p. case: (Path_split in_p) => p1 [p2] E; subst. 
  move: I. rewrite irred_cat => /and3P[*]. by constructor. 
Qed.

End Pack.

(* TOTHINK: What do we do about the forest constructions, to we move to packaged paths? *)
Lemma lift_spath' (G H : sgraph) (f : G -> H) a b (p' : Path (f a) (f b)) : 
  (forall x y, f x -- f y -> x -- y) -> injective f -> {subset p' <= codom f} -> 
  exists p : Path a b, map f (val p) = val p'.
Proof. 
  move => A I S. case: (lift_spath A I (valP p') _). admit.
  move => p [p1 p2]. exists (Sub p p1). by rewrite -p2. 
Abort. 

(** ** Forests *)

(** We define forests to be simple graphs where there exists at most one
duplicate free path between any two nodes *)


Definition tree_axiom (G:sgraph) := forall (x y : G), unique (upath x y).
  
Record tree := Tree { sgraph_of_tree :> sgraph ; 
                      treeP : tree_axiom sgraph_of_tree}.

Lemma restrict_tree (T : tree) (A : pred T) : 
  connect_sym (restrict A sedge).
Proof. apply: connect_symI => x y /=. by rewrite sgP [(x \in A) && _]andbC. Qed.


(** We define [width] and [rename] for tree decompositions already
here, so that we can use use them for tree decompositions of simple
graphs and directed graphs. *)

(** Non-standard: we do not substract 1 *)
Definition width (T G : finType) (D : T -> {set G}) := \max_(t:T) #|D t|.

Definition rename (T G G' : finType) (B: T -> {set G}) (h : G -> G') := 
  [fun x => h @: B x].


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

  Lemma join_disc (x : G1) (y : G2) : connect join_rel (inl x) (inr y) = false.
  Proof. 
    apply/negP. case/connectP => p. elim: p x => // [[a|a]] //= p IH x.
    case/andP => _. exact: IH. 
  Qed.

End JoinSG.

Prenex Implicits join_rel.

Lemma upathPR (G : sgraph) (x y : G) A : 
  reflect (exists p : seq G, @upath (srestrict A) x y p) 
          (connect (restrict A sedge) x y).
Proof. exact: (@upathP (srestrict A)). Qed.

(** TODO: this should be one of the first lemmas we prove *)
Lemma connectUP (T : finType) (e : rel T) (x y : T) : 
  reflect (exists p, [/\ path e x p, last x p = y & uniq (x::p)])
          (connect e x y).
Proof.
  apply: (iffP connectP) => [[p p1 p2]|]; last by firstorder.
  exists (shorten x p). by case/shortenP : p1 p2 => p' ? ? _ /esym ?. 
Qed.
Arguments connectUP [T e x y]. 

Lemma restrict_path (G : eqType) (e : rel G) (A : pred G) (x : G) (p : seq G) :
  path e x p -> x \in A -> {subset p <= A} -> path (restrict A e) x p.
Proof.
  elim: p x => [//|a p IH] x /= /andP[-> pth_p] -> /subset_cons [? Ha] /=.
  rewrite /= Ha. exact: IH.
Qed.

(** NOTE: need to require either x != y or x \in A since packaged
paths are never empy *)
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
    { move/subsetP : subA => H. rewrite !H ?nodes_start //=. 
      apply/subsetP => z Hz. apply: H. by rewrite mem_path !inE Hz. }
    apply: restrict_path => //. exact/subsetP.
Qed.

Lemma upathWW (G : sgraph) (x y : G) p : upath x y p -> path (@sedge G) x p.
Proof. by move/upathW/spathW. Qed.


Definition clique (G : sgraph) (S : {set G}) :=
  {in S&S, forall x y, x != y -> x -- y}.

Definition subtree (T : tree) (A : {set T}) :=
  {in A&A, forall (x y : T) p, upath x y p -> {subset p <= A}}.

Set Printing Implicit Defensive.
Lemma subtree_connect (T : tree) (c : T) (a : pred T) : 
  subtree [set c' | connect (restrict a sedge) c c'].
Proof.
  move => u u' H1 H2 p H3.  
  have/upathPR [q pth_q] : connect (restrict a sedge) u u'.
  { apply: (connect_trans (y := c)).
    - by rewrite restrict_tree inE in H1 *.
    - by rewrite inE in H2. }
  have -> : p = q. { move/restrict_upath : pth_q. exact: treeP H3. }
  move => c' /(mem_tail u) in_q. 
  case: (usplitP (G := srestrict a) in_q pth_q) => p1 p2 A _ _.
  rewrite !inE in H1 H2 *. apply: connect_trans H1 _.
  apply/upathPR. by exists p1.
Qed.

Lemma subtree_link (T : tree) (C : {set T}) t0 c0 c p : 
  subtree C -> t0 \notin C -> c0 \in C -> t0 -- c0 -> c \in C -> upath t0 c p -> c0 \in p.
Proof.
  move => sub_C H1 H2 H3 H4 H5. 
  have [q Hq] : exists p, upath  c0 c p. 
  { apply/upathP. apply: (connect_trans (y := t0)). 
    + apply: connect1. by rewrite sgP.
    + apply/upathP. by exists p. }
  have X : upath  t0 c (c0::q). 
  { rewrite upath_cons H3 Hq /= andbT inE. 
    apply/orP => [[/eqP X|X]]. by subst; contrab. 
    move/sub_C : Hq. case/(_ _ _)/Wrap => // /(_ _ X) ?. by contrab. }
  rewrite (treeP H5 X). exact: mem_head.
Qed.

(** decidability of cycle agnostic path properties *)
Definition short_prop (T:eqType) e (P : T -> seq T -> bool) := 
  forall x p, path e x p -> P x (shorten x p) -> P x p.

Lemma short_prop_dec (T : finType) e (P : T -> seq T -> bool) x : 
  short_prop e P -> decidable (forall p, path e x p -> P x p).
Proof.
  move => spP. 
  pose Pb := [forall n : 'I_#|T|, forall p : n.-tuple T, path e x p ==> P x p].
  apply: (decP (b := Pb)). apply: (iffP forallP) => H.
  - move => p pth_p. apply: spP => //. 
    case/shortenP : pth_p => p' pth_p' uniq_p' _. 
    have bound_p' : size p' < #|T|. 
    { move/card_uniqP : uniq_p' => /= <-. exact: max_card. }
    move/forall_inP: (H (Ordinal bound_p')) => /(_ (in_tuple p')). 
    by apply.
  - move => n. apply/forall_inP => p. exact: H.
Qed.

Lemma dec_eq (P : Prop) (decP : decidable P) : decP <-> P.
Proof. by case: decP. Qed.

