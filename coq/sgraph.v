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

Definition in_nodes x y (p : Path x y) : collective_pred G := [pred u | u \in nodes p].
Canonical Path_predType x y := Eval hnf in @mkPredType G (Path x y) (@in_nodes x y).

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

(** ** Checkpoints *)

Section CheckPoints.
  Variables (G : sgraph).
  Implicit Types x y z : G.

  Let avoids z x y (p : seq G) := upath x y p && (z \notin x::p).
  Definition avoidable z x y := [exists n : 'I_#|G|, exists p : n.-tuple G, avoids z x y p].

  Definition cp x y := locked [set z | ~~ avoidable z x y].

  Lemma cpPn {z x y} : reflect (exists2 p, upath x y p & z \notin x::p) (z \notin cp x y).
  Proof.
    rewrite /cp -lock inE negbK. apply: (iffP existsP) => [[n] /exists_inP|[p]].
    - case => p ? ?. by exists p.
    - case/andP => U S I.
      have size_p : size p < #|G|.
      { by rewrite -[(size p).+1]/(size (x::p)) -(card_uniqP U) max_card. }
      exists (Ordinal size_p). by apply/exists_inP; exists (in_tuple p).
  Qed.

  Lemma cpNI z x y p : spath x y p -> z \notin x::p -> z \notin cp x y.
  Proof.
    case/andP. case/shortenP => p' ? ? sub_p ? E. apply/cpPn. exists p' => //.
    apply: contraNN E. rewrite !inE. case: (_ == _) => //=. exact: sub_p.
  Qed.
  
  Definition checkpoint x y z := forall p, spath x y p -> z \in x :: p.

  Lemma cpP {x y z} : reflect (checkpoint x y z) (z \in cp x y).
  Proof.
    apply: introP.
    - move => H p pth_p. apply: contraTT H. exact: cpNI.
    - case/cpPn => p /upathW pth_p mem_p /(_ p pth_p). by rewrite (negbTE mem_p).
  Qed.

  (** wrapped versions of the checkpoint/path lemmas *)
  
  Lemma cpP' x y z : reflect (forall p : Path x y, z \in p) (z \in cp x y).
  Proof. 
    apply: (iffP cpP) => [H p|H p Hp]. 
    + rewrite in_collective nodesE. apply: H. exact: valP. 
    + move: (H (Sub p Hp)). by rewrite in_collective nodesE. 
  Qed.

  Lemma cpPn' x y z : reflect (exists2 p : Path x y, irred p & z \notin p) (z \notin cp x y).
  Proof. 
    apply: (iffP cpPn) => [[p /andP [I Hp] N]|[p U N]]. 
    + exists (Sub p Hp); by rewrite /irred ?in_collective nodesE. 
    + rewrite /irred ?in_collective nodesE in U N.
      exists (val p) => //. apply/andP. split => //. exact: valP. 
  Qed.

  Lemma cpNI' x y (p : Path x y) z : z \notin p -> z \notin cp x y.
  Proof. by apply: contraNN => /cpP'. Qed.

  Hypothesis G_conn : forall x y:G, connect sedge x y.

  Lemma cp_sym x y : cp x y = cp y x.
  Proof.
    wlog suff S : x y / cp x y \subset cp y x. 
    { apply/eqP. by rewrite eqEsubset !S. }
    apply/subsetP => z /cpP H. apply/cpP => p p_pth. 
    rewrite (srev_nodes p_pth). apply: H. exact: spath_rev.
  Qed.

  Lemma mem_cpl x y : x \in cp x y.
  Proof. apply/cpP => p. by rewrite mem_head. Qed.

  Lemma subcp x y : [set x;y] \subset cp x y.
  Proof. by rewrite subUset !sub1set {2}cp_sym !mem_cpl. Qed.

  Lemma cpxx x : cp x x = [set x].
  Proof. 
    apply/setP => z; rewrite !inE. 
    apply/idP/idP; last by move/eqP ->; rewrite mem_cpl.
    move/cpP/(_ [::] (spathxx _)). by rewrite inE.
  Qed.

  Lemma cp_triangle z {x y} : cp x y \subset cp x z :|: cp z y.
  Proof.
    apply/subsetP => u /cpP' => A. apply: contraT. 
    rewrite !inE negb_or => /andP[/cpPn' [p1 _ up1]] /cpPn' [p2 _ up2]. 
    move: (A (pcat p1 p2)). by rewrite mem_pcat (negbTE up1) (negbTE up2).
  Qed.
  
  Lemma cpN_cat a x z y : a \notin cp x z -> a \notin cp z y -> a \notin cp x y.
  Proof. 
    move => /negbTE A /negbTE B. apply/negP. move/(subsetP (cp_triangle z)). 
    by rewrite !inE A B.
  Qed.

  Definition CP (U : {set G}) := \bigcup_(xy in setX U U) cp xy.1 xy.2.
  
  Unset Printing Implicit Defensive.

  Lemma cp_mid (z x y t : G) : t != z -> z \in cp x y ->
   exists (p1 : Path z x) (p2 : Path z y), t \notin p1 \/ t \notin p2.
  Proof. 
    move => tNz cp_z.
    case/uPathP : (G_conn x y) => p irr_p.
    move/cpP'/(_ p) : cp_z. case/(isplitP irr_p) => p1 p2 A B C.
    exists (prev p1). exists p2. rewrite mem_prev. apply/orP. 
    case E : (t \in p1) => //=. 
    by rewrite mem_path !inE (negbTE tNz) (disjointFr C E).
  Qed.
  
  Lemma CP_closed U x y : 
    x \in CP U -> y \in CP U -> cp x y \subset CP U.
  Proof.
    case/bigcupP => [[x1 x2] /= /setXP [x1U x2U] x_cp]. 
    case/bigcupP => [[y1 y2] /= /setXP [y1U y2U] y_cp]. 
    apply/subsetP => t t_cp. 
    case (boolP (t == y)) => [/eqP-> //|T2].
    { apply/bigcupP. exists (y1,y2); by [exact/setXP|]. }
    case (boolP (t == x)) => [/eqP-> //|T1].
    { apply/bigcupP. exists (x1,x2); by [exact/setXP|]. }
    move: (cp_mid T1 x_cp) => [p1] [p2] H.
    wlog P1 : x1 x2 p1 p2 x1U x2U x_cp H / t \notin p1 => [W|{H}].
    { case: H => H. 
      - by apply : (W _ _ p1 p2) => //; tauto.
      - rewrite cp_sym in x_cp. apply : (W _ _ p2 p1) => //; tauto. }
    move: (cp_mid T2 y_cp) => [q1] [q2] H.
    wlog P2 : y1 y2 q1 q2 y1U y2U y_cp H / t \notin q1 => [W|{H}].
    { case: H => H. 
      - by apply : (W _ _ q1 q2) => //; tauto.
      - rewrite cp_sym in y_cp. apply : (W _ _ q2 q1) => //; tauto. }
    apply/bigcupP; exists (x1,y1) => /= ; first exact/setXP. 
    apply: contraTT t_cp => /cpPn' [s _ Hs]. 
    suff: t \notin (pcat p1 (pcat s (prev q1))) by apply: cpNI'.
    by rewrite !mem_pcat !mem_prev (negbTE P1) (negbTE P2) (negbTE Hs).
  Qed.

  (* END TEST *)

  Definition link_rel := [rel x y | (x != y) && (cp x y \subset [set x; y])].

  Lemma link_sym : symmetric link_rel.
  Proof. move => x y. by rewrite /= eq_sym cp_sym set2C. Qed.

  Lemma link_irrefl : irreflexive link_rel.
  Proof. move => x /=. by rewrite eqxx. Qed.

  Definition link_graph := SGraph link_sym link_irrefl.

  Lemma link_avoid (x y z : G) : 
    z \notin [set x; y] -> link_rel x y -> exists2 p, spath x y p & z \notin (x::p).
  Admitted.
  (* Proof. *)
  (*   move => Hz /andP[l1 l2]. *)
  (*   suff/cpPn [[p] [? ?]] : z \notin cp x y by exists p. *)
  (*   apply: contraNN Hz. by move/(subsetP l2).  *)
  (* Qed. *)

  (* Lemma path_ind y (P : forall x, Path x y -> Prop) :  *)
  (*   (forall x (p : Path x x), p = [:: x] -> P x p)  *)
  (*   (forall x y (p : Path x y) *)
  (*   forall x (p : Path x y) : P x P  *)

  (* Lemma link_seq_cp (y x : G) (p : @Path link_graph x y) :  *)
  (*   cp x y \subset p. *)
  (* Proof. *)

  Lemma link_seq_cp (y x : G) p :
    @spath link_graph x y p -> cp x y \subset x :: p.
  Proof.
    elim: p x => [|z p IH] x /=.
    - move/spath_nil->. rewrite cpxx. apply/subsetP => z. by rewrite !inE.
    - rewrite spath_cons => /andP [/= /andP [A B] /IH C]. 
      apply: subset_trans (cp_triangle z) _.
      rewrite subset_seqR. apply/subUsetP; split. 
      + apply: subset_trans B _. by rewrite !set_cons setUA subsetUl.
      + apply: subset_trans C _. by rewrite set_cons subset_seqL subsetUr.
  Qed.

  (* Lemma 10 *)
  Lemma link_cycle (p : seq link_graph) : ucycle sedge p -> clique [set x in p].
  Proof. 
    move => cycle_p x y. rewrite !inE /= => xp yp xy. rewrite xy /=.
    case/andP : cycle_p => C1 C2. 
    case: (rot_to_arc C2 xp yp xy) => i p1 p2 _ _ I. 
    have {C1} C1 : cycle sedge (x :: p1 ++ y :: p2) by rewrite -I rot_cycle. 
    have {C2} C2 : uniq (x :: p1 ++ y :: p2) by rewrite -I rot_uniq.
    rewrite /cycle -cat_rcons rcons_cat cat_path last_rcons in C1. 
    case/andP : C1 => /rcons_spath P1 /rcons_spath /spath_rev P2. 
    rewrite srev_rcons in P2. 
    move/link_seq_cp : P1 => P1. move/link_seq_cp : P2 => P2. 
    have D: [disjoint p1 & p2].
    { move: C2 => /= /andP [_]. rewrite cat_uniq -disjoint_has disjoint_cons disjoint_sym.
      by case/and3P => _ /andP [_ ?] _. }
    apply: contraTT D. case/subsetPn => z. rewrite !inE negb_or => A /andP [B C].
    move: (subsetP P1 _ A) (subsetP P2 _ A). 
    rewrite !(inE,mem_rcons,negbTE B,negbTE C,mem_rev) /=. 
    exact: disjointNI.
  Qed.

  
  (** This is redundant, but a boolean property. See [checkpoint_seq]
  in extraction.v *)
  Variables (i o : G).
  Hypothesis conn_io : connect sedge i o.

  Lemma the_upath_proof : exists p, upath i o p.
  Proof. case/upathP : conn_io => p Hp. by exists p. Qed.
                                                                
  Definition the_upath := xchoose (the_upath_proof).

  Lemma the_upathP x y : upath i o (the_upath).
  Proof. exact: xchooseP. Qed.

  Definition cpo x y := let p := the_upath in 
                        index x (i::p) <= index y (i::p).

  Lemma cpo_trans : transitive cpo.
  Proof. move => ? ? ?. exact: leq_trans. Qed.

  Lemma cpo_total : total cpo.
  Proof. move => ? ?. exact: leq_total. Qed.

  Lemma cpo_antisym : {in cp i o&,antisymmetric cpo}.
  Proof. 
    move => x y Cx Cy. rewrite /cpo -eqn_leq. 
    have Hx: x \in i :: the_upath. 
    { move/cpP : Cx => /(_ (the_upath)). 
      apply. apply upathW. exact: the_upathP. }
    have Hy: y \in i :: the_upath.
    { move/cpP : Cy => /(_ (the_upath)). 
      apply. apply upathW. exact: the_upathP. }
    by rewrite -{2}[x](nth_index i Hx) -{2}[y](nth_index i Hy) => /eqP->.
  Qed.

  (** All paths visist all checkpoints in the same order as the canonical upath *)
  (* TOTHINK: Is this really the formulation that is needed in the proofs? *)
  Lemma cpo_order (x y : G) p : x \in cp i o -> y \in cp i o -> upath i o p -> 
    cpo x y = (index x (i::p) <= index y (i::p)).
    move => cp_x cp_y pth_p. rewrite /cpo. 
  Admitted.

  Variable (U : {set G}).

  (* Lemma 16 *)
 
  (* BEGIN TEST *)

  Lemma CP_base x y : x \in CP U -> y \in CP U ->
    exists x' y':G, [/\ x' \in U, y' \in U & [set x;y] \subset cp x' y'].
  Proof.
    move => U1 U2. case/bigcupP : U1 => [[x1 x2]]. case/bigcupP : U2 => [[y1 y2]] /=.
    rewrite !inE /= => /andP[Uy1 Uy2] cp_y /andP[Ux1 Ux2] cp_x.
    case: (boolP (x \in cp y1 y2)) => [C|Wx]; first by exists y1; exists y2; rewrite subUset !sub1set C.
    case: (boolP (y \in cp x1 x2)) => [C|Wy]; first by exists x1; exists x2; rewrite subUset !sub1set C.
    gen have H,A: x x1 x2 y1 y2 {Ux1 Ux2 Uy1 Uy2 Wy cp_y} Wx cp_x /
      (x \in cp x1 y1) || (x \in cp x2 y2).
    { case/cpPn' : Wx => p irr_p av_x. 
      apply: contraTT cp_x. rewrite negb_or => /andP[/cpPn' [s s1 s2] /cpPn' [t t1 t2]].
      apply (cpNI' (p := pcat s (pcat p (prev t)))). 
      by rewrite !mem_pcat !mem_prev (negbTE av_x) (negbTE s2) (negbTE t2). }
    move: (H _ _ _ _ _ Wy cp_y) => B {H}. rewrite (cp_sym y1 x1) (cp_sym y2 x2) in B. 
    wlog {A} /andP [Hx Hy] : x1 x2 y1 y2 A B cp_x cp_y Ux1 Ux2 Uy1 Uy2 Wx Wy
        / (x \in cp x1 y1) && (y \notin cp x1 y1).
    { case: (boolP (y \in cp x1 y1)) A B => A; case: (boolP (x \in cp x1 y1)) => /= B C D W. 
      - by exists x1; exists y1; rewrite subUset !sub1set B. 
      - case: (boolP (y \in cp x2 y2)) => E. (* TOTHINK: why the second case anlysis in this case? *)
        + exists x2; exists y2; by rewrite subUset !sub1set C.
        + move: (W x2 x1 y2 y1). rewrite (cp_sym x2 x1) (cp_sym y2 y1) A C /= orbT. exact.
      - apply: (W x1 x2 y1 y2) => //. by rewrite B. by rewrite D. (* exact/andP. *)
      - exists x2; exists y2; by rewrite subUset !sub1set C D. }
    rewrite (negbTE Hy) /= in B.
    case: (boolP (x \in cp x2 y2)) => [C|Wx']; first by exists x2; exists y2; rewrite subUset !sub1set C.
    exists x1. exists y2. rewrite subUset !sub1set. split => //. apply/andP; split.
    - apply: contraTT cp_x => C. apply: cpN_cat C _. by rewrite cp_sym.
    - apply: contraTT cp_y. apply: cpN_cat. by rewrite cp_sym.
  Qed.

  (* END TEST *)

  Print Assumptions CP_base.

  (* Lemma 16 *)
  Definition CP_ := @induced link_graph (CP U).

  Lemma link_sup (x y : CP_) : x -- y -> (val x:G) -- val y.
  Abort.

  Lemma index_uniq_inj (T:eqType) (s : seq T) : 
    {in s, injective (index^~ s)}. 
  Proof. 
    move => x in_s y E. 
    have A : y \in s by rewrite -index_mem -E index_mem.
    by rewrite -(nth_index x in_s) E nth_index.
  Qed.

  Lemma mem_catD (T:finType) (x:T) (s1 s2 : seq T) : [disjoint s1 & s2] ->
      (x \in s1 ++ s2) = (x \in s1) (+) (x \in s2).
  Proof. 
    move => D. rewrite mem_cat. case C1 : (x \in s1) => //=. 
    symmetry. apply/negP. exact: disjointE D _.
  Qed.
  Arguments mem_catD [T x s1 s2].
    

  Lemma CP_base_ (x y : CP_) : 
    exists x' y':G, [/\ x' \in U, y' \in U & [set val x;val y] \subset cp x' y'].
  Proof. exact: CP_base  (svalP x) (svalP y). Qed.


  Arguments cpP' [x y z].

  Definition idx x y (p : Path x y) u := index u (nodes p).

  (* TOTHINK: This only parses if the level is at most 10, why? *)
  Notation "x '<[' p ] y" := (idx p x < idx p y) (at level 10, format "x  <[ p ]  y").
  (* (at level 70, p at level 200, y at next level, format "x  <[ p ]  y"). *)


  Lemma idx_end x y (p : Path x y) : 
    irred p -> idx p y = size (tail p).
  Proof.
    rewrite /irred nodesE => irr_p. 
    by rewrite /idx nodesE -[in index _](path_last p) index_last.
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
    Proof. move: irr_pq. by rewrite irred_cat => /and3P[]. Qed.

    Let irr_p : irred p.
    Proof. move: irr_pq. by rewrite irred_cat => /and3P[]. Qed.

    Let irr_q : irred q.
    Proof. move: irr_pq. by rewrite irred_cat => /and3P[]. Qed.

    Lemma idxR u : u \in nodes (pcat p q) -> 
      (u \in tail q) = z <[pcat p q] u.
    Proof.
      move => A. symmetry. rewrite /idx /pcat nodesE -cat_cons index_cat -nodesE nodes_end.
      rewrite index_cat mem_pcatT in A *. case/orP: A => A.
      - rewrite A (disjointFr dis_pq A). apply/negbTE. 
        rewrite -leqNgt -!/(idx _ _) (idx_end irr_p) -ltnS. 
        rewrite -index_mem in A. apply: leq_trans A _. by rewrite nodesE.
      - rewrite A (disjointFl dis_pq A) -!/(idx _ _) (idx_end irr_p).
        by rewrite nodesE /= addSn ltnS leq_addr. 
    Qed.

    Lemma idx_catL u v : u \in tail q -> v \in tail q -> u <[pcat p q] v = u <[q] v.
    Proof.
      move => A B. rewrite /idx nodesE -!cat_cons !index_cat -nodesE.
      have C : (u \notin nodes p). 
      { apply/negP. apply: disjointE A. by rewrite disjoint_sym dis_pq. }
      have D : (v \notin nodes p). 
      { apply/negP. apply: disjointE B. by rewrite disjoint_sym dis_pq. }
      rewrite (negbTE C) (negbTE D) ltn_add2l nodesE /=.
      have -> : z == u = false. apply: contraTF C => /eqP<-. by rewrite negbK nodes_end.
      have -> : z == v = false. apply: contraTF D => /eqP<-. by rewrite negbK nodes_end.
      by rewrite ltnS.
    Qed.

    Lemma idx_nLR u : u \in nodes (pcat p q) -> 
      idx (pcat p q) z < idx (pcat p q) u -> u \notin nodes p /\ u \in tail q.
    Proof. move => A B. rewrite -idxR // in B. by rewrite (disjointFl dis_pq B). Qed.
  
  End IDX.

  Lemma CP_triangle_avoid x' y' (x y z: link_graph) : 
    x -- y -> y -- z -> z -- x -> x \in cp x' y' -> y \in cp x' y' -> z \notin cp x' y'.
  Proof.
    move => xy yz zx Cx Cy. apply/negP => Cz.
    case/uPathP : (G_conn x' y') => p irr_p.
    move: (cpP' Cx p) (cpP' Cy p) (cpP' Cz p) => x_in_p y_in_p z_in_p.
    pose I := idx p. 
    have D (x1 x2 : link_graph) : x1 -- x2 -> x1 \in nodes p -> I x1 <> I x2.
    { move => H in_p. move/idx_inj. case/(_ _ )/Wrap => //. 
      move => ?. subst. by rewrite sgP in H. }
    wlog /andP [x_lt_y y_lt_z] : x y z xy yz zx x_in_p y_in_p z_in_p Cy {Cx Cz D}
      / I x < I y < I z => [W|].
    { wlog x_lt_y : x y xy yz zx Cx Cy x_in_p y_in_p z_in_p / I x < I y => [W2|].
      { case: (ltngtP (I x) (I y)); [exact: W2|apply:W2; by rewrite // sg_sym |exact: D]. }
      case: (ltngtP (I y) (I z)) => [Hyz|Hyz|]; last exact: D. 
      - exact: (W x y z).
      - case: (ltngtP (I z) (I x)) => [Hzx|Hzx|]; last exact: D. 
        + exact: (W z x y).
        + apply: (W x z y); by rewrite // sg_sym. }
    suff: y \notin cp x' y' by rewrite Cy.
    case/(isplitP (G := G) irr_p) def_p : {1}p / (x_in_p) => [p1 p2 irr_p1 irr_p2 D]. subst.
    case: (idx_nLR irr_p y_in_p) => // Y1 Y2.
    (case: (idx_nLR irr_p z_in_p); first by apply: ltn_trans y_lt_z) => Z1 Z2.
    case/(isplitP (G:=G) irr_p2) def_p1 : {1}p2 / (tailW Z2) => [p21 p22 irr21 irr22 D2]. subst.
    have Hy' : y \notin tail p22.
    { rewrite (idxR irr_p2) ?tailW //. rewrite -(idx_catL irr_p Z2 Y2). by rewrite -leqNgt ltnW. }
    have/cpPn' [q q1 q2] : y \notin cp x z. 
    { case/andP : zx => _ sub. apply/negP. rewrite cp_sym. move/(subsetP sub). 
      rewrite !inE. by case/orP => /eqP ?;subst; rewrite sg_irrefl in xy yz. }
    apply: (cpNI' (p := pcat p1 (pcat q p22))). 
    by rewrite mem_pcat mem_pcatT (negbTE Hy') (negbTE Y1) (negbTE q2).
  Qed.

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
    case/(isplitP irr_p) def_p : {1}p / (a_in_p) => [p1 p2' irr_p1 irr_p2' D1]. subst p.
    case: (idx_nLR irr_p b_in_p) => // Y1 Y2.
    case/(isplitP irr_p2') def_p1' : {1}p2' / (tailW Y2) => [p2 p3 irr_p2 irr_p3 D2]. subst p2'.
    exists p1. exists p2. exists p3. split => //. 
    have A: a != b. { apply: contraTN a_before_b => /eqP=>?. subst b. by rewrite ltnn. }
    by rewrite mem_path inE (negbTE A) (disjointFr D2 (nodes_start p2)).
  Qed.

  Lemma CP_triangle (x y z: CP_) : 
    x -- y -> y -- z -> z -- x -> 
    exists x' y' z':G, 
      [/\ x' \in U, y' \in U & z' \in U] /\
      [/\ [set val x;val y] \subset cp x' y',
         [set val y;val z] \subset cp y' z'&
         [set val z;val x] \subset cp z' x'].
  Proof.
    move => xy yz zx.
    move: (CP_base_ x y) => [x'] [y'] [Ux Uy]. 
    rewrite subUset !sub1set => /andP[cp_x cp_y].
    have ncp_z : val z \notin cp x' y' by apply: CP_triangle_avoid cp_x cp_y. 
    case/cpPn' : ncp_z => p irr_p av_z. 
    have x_in_p : val x \in p by apply/cpP'.
    have y_in_p : val y \in p by apply/cpP'.
  
    wlog x_before_y : x' y' Ux Uy cp_x cp_y p irr_p av_z x_in_p y_in_p / 
      idx p (val x) < idx p (val y). 
    { move => W. case: (ltngtP (idx p (val x)) (idx p (val y))) => H.
      - exact: (W x' y' _ _ _ _ p). 
      - apply: (W y' x' _ _ _ _ (prev p)); rewrite 1?cp_sym //. 
        + exact: prev_irred.
        + by rewrite mem_prev.
        + rewrite /=. (* FIXME: why is this needed *) by rewrite mem_prev.
        + by rewrite /= mem_prev.
        + exact: idx_swap H. 
      - move/idx_inj : H. move/(_ x_in_p)/val_inj => ?. subst y. by rewrite sgP in xy. }
    
    move: (CP_base_ x z) => [x''] [z'] [Ux' Uz]. 
    rewrite subUset !sub1set => /andP[cp_x' cp_z].
    have ncp_z : val y \notin cp x'' z' by apply: CP_triangle_avoid cp_x' cp_z; by rewrite sgP.
    case/cpPn' : ncp_z => q irr_q av_y.
    have x_in_q : val x \in q by apply/cpP'.
    have z_in_q : val z \in q by apply/cpP'.

    wlog x_before_z : x'' z' Ux' Uz cp_x' cp_z q irr_q av_y x_in_q z_in_q / 
      idx q (val x) < idx q (val z).
    { move => W. case: (ltngtP (idx q (val x)) (idx q (val z))) => H.
      - exact: (W x'' z' _ _ _ _ q).
      - apply: (W z' x'' _ _ _ _ (prev q)); try rewrite 1?cp_sym /= ?mem_prev //. 
        + exact: prev_irred.
        + exact: idx_swap H. 
      - move/idx_inj : H. move/(_ x_in_q)/val_inj => ?. subst z. by rewrite sgP in zx. }

    case: (three_way_split irr_p x_in_p y_in_p x_before_y) => p1 [p2] [p3] [? ? ?]. subst p.
    rewrite !mem_pcat 2!negb_or in av_z. case/and3P : av_z => p1_z p2_z p3_z. 
    case: (three_way_split irr_q x_in_q z_in_q x_before_z) => q1 [q2] [q3] [? ? ?]. subst q.
    rewrite !mem_pcat 2!negb_or in av_y. case/and3P : av_y => q1_y q2_y q3_y.

    exists x'. exists y'. exists z'. split; split; rewrite // subUset !sub1set; apply/andP;split.
    - done.
    - done.
    - apply: contraTT cp_y. case/cpPn' => r _ Hr. 
      apply: (cpNI' (p := pcat p1 (pcat q2 (pcat q3 (prev r))))).
      rewrite /= !mem_pcat !mem_prev 3!negb_or. exact/and4P.
    - apply: contraTT cp_z. case/cpPn' => r _ Hr. 
      apply: (cpNI' (p := pcat q1 (pcat p2 (pcat p3 r)))).
      rewrite /= !mem_pcat 3!negb_or. exact/and4P.
    - rewrite cp_sym. 
      apply: contraTT cp_z. case/cpPn' => r _ Hr. 
      apply: (cpNI' (p := pcat q1 (pcat (prev p1) r))).
      rewrite /= !mem_pcat mem_prev 2!negb_or. exact/and3P.
    - rewrite cp_sym. 
      have: val x \notin cp (val y) (val z).
      { apply/negP. move: yz => /= /andP [_ B] /(subsetP B).
        rewrite !inE => /orP[]/eqP/val_inj=>?; subst x. 
        by rewrite sgP in xy. by rewrite sgP in zx. }
      case/cpPn' => s _ Hs. 
      apply: contraTT cp_x. case/cpPn' => r _ Hr. 
      apply: (cpNI' (p := pcat r (pcat (prev q3) (pcat (prev s) p3)))).
      rewrite /= !mem_pcat !mem_prev 3!negb_or. exact/and4P.
  Qed.

    
End CheckPoints.
