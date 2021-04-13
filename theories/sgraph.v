Require Import Setoid CMorphisms.
From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries bij digraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Simple Graphs

This file defines (finite) simple graphs, i.e. undirected and
unlabeled graphs without self-loops. *)

Record sgraph := SGraph { svertex : finType ; 
                          sedge: rel svertex; 
                          sg_sym': symmetric sedge;
                          sg_irrefl': irreflexive sedge}.

Canonical digraph_of (G : sgraph) := DiGraph (@sedge G).
Coercion digraph_of : sgraph >-> diGraph.

(** The notation [x -- y] is now inherited *)
(* Notation "x -- y" := (sedge x y) (at level 30). *)

Definition sg_sym (G : sgraph) : @symmetric G (--). exact: sg_sym'. Qed.
Definition sg_irrefl (G : sgraph) : @irreflexive G (--). exact: sg_irrefl'. Qed.

Definition sgP := (sg_sym,sg_irrefl).
Prenex Implicits sedge.

Lemma sg_edgeNeq (G : sgraph) (x y : G) : x -- y -> (x == y = false).
Proof. apply: contraTF => /eqP ->. by rewrite sg_irrefl. Qed.

Lemma sconnect_sym (G : sgraph) : @connect_sym G (--). 
Proof. exact/connect_symI/sg_sym. Qed.

Lemma sedge_equiv (G : sgraph) : 
  equivalence_rel (connect (@sedge G)).
Proof.  apply: equivalence_rel_of_sym. exact: sg_sym. Qed.

Lemma symmetric_restrict_sedge (G : sgraph) (A : pred G) :
  symmetric (restrict A (--)).
Proof. apply: restrict_sym. exact: sg_sym. Qed.

Lemma srestrict_sym (G : sgraph) (A : pred G) :
  connect_sym (restrict A (--)).
Proof. exact/connect_symI/symmetric_restrict_sedge. Qed.

Lemma sedge_in_equiv (G : sgraph) (A : {set G}) :
  equivalence_rel (connect (restrict A (--))).
Proof. exact/equivalence_rel_of_sym/symmetric_restrict_sedge. Qed.

Lemma sedge_equiv_in (G : sgraph) (A : {set G}) :
  {in A & &, equivalence_rel (connect (restrict A (--)))}.
Proof. exact: in3W (sedge_in_equiv A). Qed.

Declare Scope sgraph_scope.
Delimit Scope sgraph_scope with sg.
Bind Scope sgraph_scope with sgraph.

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

Notation "G ∔ H" := (sjoin G H) (at level 20, left associativity) : sgraph_scope.

Lemma sjoin_disconnected (G H : sgraph) (x : G) (y : H) :
  ~~ connect (--) (inl x : (G ∔ H)%sg) (inr y).
Proof.
apply: contraTN isT => /connectP [p]; elim: p x => // -[/=|//] z p IHp x.
case/andP => _ . exact: IHp.
Qed.

Prenex Implicits join_rel.

(** ** Homomorphisms *)

Definition hom_s (G1 G2 : sgraph) (h : G1 -> G2) := 
  forall x y, x -- y -> h x != h y -> (h x -- h y).

Definition subgraph (S G : sgraph) := 
  exists2 h : S -> G, injective h & hom_s h.

Section InducedSubgraph.
  Variables (G : sgraph) (S : {set G}).

  Definition induced_type := { x | x \in S}.

  Definition induced_rel := [rel x y : induced_type | val x -- val y].

  Lemma induced_sym : symmetric induced_rel.  
  Proof. move => x y /=. by rewrite sgP. Qed.
         
  Lemma induced_irrefl : irreflexive induced_rel.  
  Proof. move => x /=. by rewrite sgP. Qed.

  Definition induced := SGraph induced_sym induced_irrefl.

  Lemma induced_sub : subgraph induced G.
  Proof. by exists val. Qed.

  Lemma induced_edge (x y : induced) : (x -- y) = (val x -- val y).
  Proof. by []. Qed.

  Lemma ucycle_induced (s : seq induced) : 
    ucycle (--) s = ucycle (--) [seq val x | x <- s].
  Proof.
    rewrite /ucycle map_inj_uniq; last exact: val_inj; congr (_ && _).
    rewrite /cycle; case: s => //= x s. rewrite -map_rcons.
    by elim: (rcons s x) {1 3}x => //= {x s} y s <- x.
  Qed.
  
  Lemma sub_induced (A : {set induced}) : val @: A \subset S.
  Proof. by apply/subsetP => ? /imsetP[x xH ->]; apply: valP. Qed.

End InducedSubgraph.

(** Link to isubgraph *)
Lemma induced_isubgraph (G : sgraph) (A : {set G}) : induced A ⇀ G.
Proof.
pose f (x : induced A) : G := val x.
have : {mono f : x y / x -- y} by abstract by move => x y; rewrite induced_edge.
apply: ISubgraph; exact: val_inj.
Defined.

Lemma isubgraph_induced (F G : sgraph) (i : F ⇀ G) : 
  F ≃ induced [set x in codom i].
Proof.
set A := [set _ in _].
have jP (x : induced A) : val x \in codom i. 
  abstract by move: (valP x); rewrite inE.
pose j (x : induced A) : F := iinv (jP x).
have iP (x : F) : i x \in A by abstract by rewrite inE codom_f.
pose i' (x : F) : induced A := Sub (i x) (iP x).
have can_i : cancel i' j. 
  abstract by move=> x; apply: (isubgraph_inj i); rewrite f_iinv.
have can_j : cancel j i'. 
  abstract by move => [x xA]; apply: val_inj; rewrite /j/=f_iinv.
apply: Diso' can_i can_j _. 
  abstract by move => x y; rewrite induced_edge /= isubgraph_mono.
Defined.




Definition srestrict (G : sgraph) (A : pred G) :=
  Eval hnf in SGraph (restrict_sym A (@sg_sym G))
                     (restrict_irrefl A (@sg_irrefl G)).

(** ** Isomorphism of simple graphs *)

Lemma eq_diso (T : finType) (e1 e2 : rel T) 
  (e1_sym : symmetric e1) (e1_irrefl : irreflexive e1) 
  (e2_sym : symmetric e2) (e2_irrefl : irreflexive e2) :
e1 =2 e2 -> diso (SGraph e1_sym e1_irrefl) (SGraph e2_sym e2_irrefl).
Proof. 
intro E. exists (@bij_id T); abstract (move => x y /=; by rewrite /edge_rel /= E). 
Defined.

Lemma iso_subgraph (G H : sgraph) : diso G H -> subgraph G H.
Proof.
  case => g E _.
  exists g. apply (can_inj (bijK g)).
  move=> x y e _. by apply E.
Qed.

(** Splitting off disconnected parts *)
Lemma ssplit_disconnected (G:sgraph) (V : {set G}) : 
  (forall x y, x \in V -> y \notin V -> ~~ x -- y) ->
  diso (sjoin (induced V) (induced (~: V))) G.
Proof.
  move => HV. set H := sjoin _ _.
  have cast x (p : x \notin V) : x \in ~: V. by rewrite inE.
  pose g (x : G) : H := 
    match (@boolP (x \in V)) with 
      | AltTrue p => inl (Sub x p) 
      | AltFalse p => inr (Sub x (cast x p)) 
    end.
  pose h (x : H) : G := match x with inl x => val x | inr x => val x end.
  pose g' := @Bij _ _ g h.
  apply Diso'' with h g. 
  - move => [x|x]; rewrite /g /h. 
    + case: {-}_ /boolP => px. 
      * congr inl. symmetry. apply/eqP. by rewrite sub_val_eq.
      * case:notF.  apply: contraNT px => _. exact: valP.
    + case: {-}_ /boolP => px.
      * case:notF.  apply: contraTT px => _. move: (valP x). by rewrite !inE.
      * congr inr. symmetry. apply/eqP. by rewrite sub_val_eq.
  - move => x. rewrite /g /h. by case: {-}_ /boolP.
  - move => x y. by case: x=>[x|x]; case: y=>[y|y] xy. 
  - move => x y xy. rewrite /g. case: {-}_/boolP => px;case: {-}_/boolP => py => //.
    + apply: contraTT xy => _. exact: HV.
    + apply: contraTT xy => _. rewrite sg_sym. exact: HV.
Qed.

(** ** Unpackaged Simple Paths

We establish those properties of [pathp] and [upath] that require symmetry or
irreflexivity, i.e. path reversal *)

Section SimplePaths.
Variable (G : sgraph).
Implicit Types (x y z : G).

Definition srev x p := rev (belast x p).

Lemma last_rev_belast x y p : 
  last x p = y -> last y (srev x p) = x.
Proof. case: p => //= a p _. by rewrite /srev rev_cons last_rcons. Qed.

Lemma path_srev x p : 
  path (--) x p = path (--) (last x p) (srev x p).
Proof. 
  rewrite rev_path [in RHS](eq_path (e' := (--))) //. 
  move => {x} x y. exact: sg_sym. 
Qed.

Lemma srev_rcons x z p : srev x (rcons p z) = rcons (rev p) x.
Proof. by rewrite /srev belast_rcons rev_cons. Qed.

(** Note that the converse of the following does not hold since [srev
x p] forgets the last element of [p]. Consequently, double reversal
only cancels if the right nodes are added back. *)
Lemma pathp_rev x y p : pathp x y p -> pathp y x (srev x p).
Proof.
  rewrite /pathp. elim/last_ind: p => /= [|p z _]; first by rewrite eq_sym.
  rewrite !srev_rcons !last_rcons eqxx andbT path_srev last_rcons srev_rcons. 
  by move/andP => [A /eqP <-].
Qed.

Lemma srevK x y p : last x p = y -> srev y (srev x p) = p.
Proof. 
  elim/last_ind: p => // p z _. 
  by rewrite last_rcons !srev_rcons revK => ->.
Qed.

Lemma srev_nodes x y p : pathp x y p -> x :: p =i y :: srev x p.
Proof. 
  elim/last_ind: p => //; first by move/pathp_nil ->.
  move => p z _ H a. rewrite srev_rcons !(inE,mem_rcons,mem_rev). 
  rewrite (pathp_rcons H). by case: (a == x).
Qed.

Lemma rev_upath x y p : upath x y p -> upath y x (srev x p).
Proof. 
  case/andP => A B. apply/andP; split; last exact: pathp_rev.
  apply: leq_size_uniq A _ _. 
  - move => z. by rewrite -srev_nodes.
  - by rewrite /= size_rev size_belast.
Qed.

Lemma upath_sym x y : unique (upath x y) -> unique (upath y x).
Proof. 
  move => U p q Hp Hq. 
  suff S: last y p = last y q. 
  { apply: last_belast_eq S _; apply: rev_inj; apply: U; exact: rev_upath. }
  rewrite !(@pathp_last _ x) //; exact: upathW.
Qed.

End SimplePaths.

Lemma upathPR (G : sgraph) (x y : G) A :
  reflect (exists p : seq G, @upath (srestrict A) x y p)
          (connect (restrict A (--)) x y).
Proof. exact: (@upathP (srestrict A)). Qed.

(* TOTHINK: is this the best way to transfer path from induced subgraphs *)
Lemma induced_path (G : sgraph) (S : {set G}) (x y : induced S) (p : seq (induced S)) : 
  pathp x y p -> @pathp G (val x) (val y) (map val p).
Proof.
  elim: p x => /= [|z p IH] x pth_p.
  - by rewrite (pathp_nil pth_p) pathpxx.
  - rewrite !pathp_cons in pth_p *. 
    case/andP : pth_p => p1 p2. apply/andP; split => //. exact: IH.
Qed.

Section Packaged.
Variables (G : sgraph).
Implicit Types x y z : G.

Section Prev.
Variables (x y z : G) (p : Path x y) (q : Path y z).

Definition prev_proof := pathp_rev (valP p).
Definition prev : Path y x := Sub (srev x (val p)) prev_proof.

End Prev.

Lemma prevK x y (p : Path x y) : prev (prev p) = p.
Proof. apply/val_inj=> /=. apply: srevK. exact: path_last. Qed.

Lemma prev_inj x y : injective (@prev x y).
Proof. apply: (can_inj (g := (@prev y x))) => p. exact: prevK. Qed.

Lemma mem_prev x y (p : Path x y) u : (u \in prev p) = (u \in p).
Proof. rewrite !mem_path !nodesE -srev_nodes //. exact: valP. Qed.

Lemma nodes_prev (x y : G) (p : Path x y) : 
  nodes (prev p) = rev (nodes p).
Proof. 
  apply: rev_inj. rewrite /prev /srev !nodesE /=. 
  by rewrite rev_cons !revK -{2}[y](path_last p) -lastI.
Qed.

Definition inE := (inE,mem_prev).

Lemma prev_cat x y z (p : Path x y) (q : Path y z) :
  prev (pcat p q) = pcat (prev q) (prev p).
Proof. apply/eqP. by rewrite -val_eqE /= /srev belast_cat rev_cat path_last. Qed.


Lemma prev_irred x y (p : Path x y) : irred p -> irred (prev p).
Proof.
  rewrite /irred /nodes => U. apply: leq_size_uniq U _ _.
  - move => u. by rewrite mem_prev.
  - by rewrite -!lock /= ltnS /srev size_rev size_belast.
Qed.

Lemma irred_rev x y (p : Path x y) : irred (prev p) = irred p.
Proof. apply/idP/idP; first rewrite -[p as X in irred X]prevK; exact: prev_irred. Qed.


(** Paths with a single edge using an injection from (proofs of) [x -- y] *)

Fact prev_edge_proof x y (xy : x -- y) : y -- x. by rewrite sgP. Qed.
Lemma prev_edge x y (xy : x -- y) : prev (edgep xy) = edgep (prev_edge_proof xy).
Proof. by apply/eqP. Qed.

Lemma irred_edge x y (xy : x -- y) : irred (edgep xy).
Proof. by rewrite irredE nodesE /= andbT inE sg_edgeNeq. Qed.

(** TODO: The following lemma hold for digraphs, but the proof uses
symmetry of the edge relation *)
                                                                
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


End Packaged.

#[export]
Hint Resolve path_begin path_end : core.

(** *** Transporting paths to and from induced subgraphs *)

Lemma path_to_induced (G : sgraph) (S : {set G}) (x y : induced S) p' : 
  @pathp G (val x) (val y) p' -> {subset p' <= S} -> 
  exists2 p, pathp x y p & p' = map val p.
Proof.
  move=> pth_p' sub_p'.
  case: (lift_pathp _ _ pth_p' _) => //.
  - move=> z /sub_p' z_S. by apply/codomP; exists (Sub z z_S).
  - move=> p [pth_p /esym eq_p']. by exists p.
Qed.

Lemma Path_to_induced (G : sgraph) (S : {set G}) (x y : induced S) 
  (p : Path (val x) (val y)) : 
  {subset p <= S} -> exists q : Path x y, map val (nodes q) = nodes p.
Proof.
  case: p => p pth_p sub_p. case: (path_to_induced pth_p).
  - move=> z z_p; apply: sub_p. by rewrite mem_path nodesE /= inE z_p.
  - move=> q pth_q eq_p. exists (Sub q pth_q). by rewrite !nodesE /= eq_p.
Qed.


Lemma Path_from_induced (G : sgraph) (S : {set G}) (x y : induced S) (p : Path x y) : 
  { q : Path (val x) (val y) | {subset q <= S} & nodes q = map val (nodes p) }.
Proof. 
  case: p => p pth_p.
  exists (Build_Path (induced_path pth_p)); last by rewrite !nodesE.
  move=> z; rewrite mem_path nodesE /= -map_cons => /mapP[z' _ ->]; exact: valP.
Qed.

(* TOTHINK: Use this to prove the lemmas above? *)
Lemma lift_Path_on (G H : sgraph) (f : G -> H) a b (p' : Path (f a) (f b)) : 
  (forall x y, f x \in p' -> f y \in p' -> f x -- f y -> x -- y) -> injective f -> {subset p' <= codom f} -> 
  exists2 p : Path a b, map f (nodes p) = nodes p' & irred p = irred p'.
Proof.
  move => A I S. case: (lift_pathp_on _ I (valP p') _).
  - move => x y. rewrite -!nodesE -!mem_path. exact: A.
  - move => x V. apply: S. by rewrite mem_path nodesE inE V.
  - move => p [p1 p2]. exists (Sub p p1). 
    + by rewrite !nodesE /= p2. 
    + by rewrite !irredE !nodesE -p2 -map_cons map_inj_uniq.
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
    { apply: contraNN uNp. by rewrite mem_path nodesE lastI mem_rcons inE =>->. }
    have /negbTE-> : v \notin belast x (val p).
    { apply: contraNN vNp. by rewrite mem_path nodesE lastI mem_rcons inE =>->. }
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
        * case/and3P:D => D1 D2 D3. rewrite /= D3 andbT. 
          apply: contraNN D1; exact: mem_tail.
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

  Lemma idx_swap_aux a b x y (p : Path x y) : a \in p -> b \in p -> irred p ->
    idx p a < idx p b -> idx (prev p) b < idx (prev p) a.
  Proof.
    move => aP bP ip A. rewrite !idx_srev //. apply: ltn_sub2l => //. 
    apply: (@leq_trans (idx p b)) => //. 
    rewrite -ltnS -[X in _ < X]/(size (x :: pval p)).
    by rewrite -nodesE index_mem.
  Qed. 

  Lemma idx_swap a b x y (p : Path x y) :
    a \in p -> b \in p -> irred p -> a <[p] b = b <[prev p] a.
  Proof.
    move => aP bP ip. apply/idP/idP => /idx_swap_aux; auto.
    rewrite irred_rev prevK !mem_prev. by apply.
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

(** *** Of subsets *)

Definition connected (G : sgraph) (S : {set G}) :=
  {in S & S, forall x y : G, connect (restrict S edge_rel) x y}.

Lemma eq_connected (V : finType) (e1 e2 : rel V) (A : {set V}) 
  (e1_sym : symmetric e1) (e1_irrefl : irreflexive e1) 
  (e2_sym : symmetric e2) (e2_irrefl : irreflexive e2):
  e1 =2 e2 -> 
  @connected (SGraph e1_sym e1_irrefl) A <-> @connected (SGraph e2_sym e2_irrefl) A.
Proof.
  move => E. split. 
  - move => H x y xA yA. erewrite eq_connect. eapply H => //. 
    move => u v. by rewrite /edge_rel /= E.
  - move => H x y xA yA. erewrite eq_connect. eapply H => //. 
    move => u v. by rewrite /edge_rel /= E.
Qed.

Definition disconnected (G : sgraph) (S : {set G}) :=
  exists x y : G, [/\ x \in S, y \in S & ~~ connect (restrict S edge_rel) x y].

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
  connected [set: G] -> forall x y : G, connect (--) x y. 
Proof. 
  move => A x y. move: (A x y). 
  rewrite !inE !restrictE; first by apply. by move => ?; rewrite !inE.
Qed.

Lemma connectedTI (G : sgraph) : 
  (forall x y : G, connect (--) x y) -> connected [set: G].
Proof. move => H x y _ _. rewrite restrictE // => z. by rewrite inE. Qed.

Lemma connected_restrict (G : sgraph) (A : pred G) x : 
  connected [set y | connect (restrict A (--)) x y].
Proof.
  move => u v. rewrite !inE => Hu Hv. move defP : (mem _) => P.
  wlog suff W: u Hu / connect (restrict P (--)) x u.
  { apply: connect_trans (W _ Hv). rewrite srestrict_sym. exact: W. }
  case: (altP (x =P u)) => [-> //|xDu].
  case/connect_irredRP : Hu => // p Ip Ap.
  apply connectRI with p => z in_p.
  rewrite -defP inE. case/psplitP : in_p Ap => p1 p2 Ap. 
  apply connectRI with p1. apply/subsetP. 
  apply: subset_trans Ap. exact: subset_pcatL.
Qed.

Lemma connect_range (G : sgraph) (A : pred G) x : x \in A -> 
  [set y | connect (restrict A (--)) x y] = 
  [set y in A | connect (restrict A (--)) x y].
Proof. 
  move => inA. apply/setP => z. rewrite !inE srestrict_sym.
  apply/idP/andP => [|[//]]. by case/connect_restrict_case => [->|[]].
Qed.

Lemma connected_restrict_in (G : sgraph) (A : pred G) x : x \in A -> 
  connected [set y in A | connect (restrict A (--)) x y].
Proof. move => inA. rewrite -connect_range //. exact: connected_restrict. Qed.

(* NOTE: This could be generalized to sets and their images *)
Lemma iso_connected (G H : sgraph) :
  diso G H -> connected [set: H] -> connected [set: G].
Proof.
  (* TODO: update proof to abstract against concrete implem of [diso] *)
  move=> [[h g can_h can_g] /= hom_h hom_g] con_H x y _ _.
  rewrite restrictE; last by move => z; rewrite !inE.
  have := con_H (h x) (h y). rewrite !inE => /(_ isT isT).
  rewrite restrictE; last by move => z; rewrite !inE.
  case/pathpP => p. case/lift_pathp => //.
  + move => {x y} x y. rewrite -{2}[x]can_h -{2}[y]can_h. exact: hom_g.
  + exact: can_inj can_h.
  + move => z _. apply/codomP. exists (g z). by rewrite can_g.
  + move => p' [Hp' _]. apply/pathpP. by exists p'.
Qed.

Lemma connected0 (G : sgraph) : connected (@set0 G).
Proof. move => x y. by rewrite inE. Qed.

Lemma connected1 (G : sgraph) (x : G) : connected [set x].
Proof. move => ? ? /set1P <- /set1P <-. exact: connect0. Qed.

Lemma connected2 (G : sgraph) (x y: G) : x -- y -> connected [set x; y].
Proof.
  move=> xy ? ? /set2P[]-> /set2P[]->; try exact: connect0.
  all: apply: connect1; rewrite /= !inE !eqxx orbT //=; by rewrite sg_sym.
Qed.

Lemma connected_center (G:sgraph) x (S : {set G}) :
  {in S, forall y, connect (restrict S (--)) x y} -> x \in S ->
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

Lemma path_in_connected (G:sgraph) (T : {set G}) x y : connected T -> x \in T -> y \in T ->
  exists2 p : Path x y, irred p & p \subset T.
Proof. 
  move => C Hx Hy. 
  case: (altP (x =P y)) => [?|D]. 
  - subst y. exists (idp x); rewrite ?irred_idp //. apply/subsetP => A. by rewrite mem_idp => /eqP->.
  - case/connect_irredRP : (C _ _ Hx Hy) => // p Ip Sp. by exists p.
Qed.

Lemma connected_path (G : sgraph) (x y : G) (p : Path x y) :
  connected [set z in p].
Proof. 
  apply: (@connected_center _ x); last by rewrite inE.
  move => z. rewrite inE => A. case/psplitP : _ / A => {p} p1 p2.
  apply: (connectRI p1) => u Hu. by rewrite inE mem_pcat Hu.
Qed.

Lemma connected_in_subgraph (G : sgraph) (S : {set G}) (A : {set induced S}) : 
  connected A -> connected [set val x | x in A].
Proof.
  move => conn_A ? ? /imsetP [/= x xA ->] /imsetP [/= y yA ->].
  case: (boolP (x == y)) => [/eqP->|Hxy]; first exact: connect0.
  move: (conn_A _ _ xA yA) => /connect_irredRP. move/(_ Hxy) => [p irr_p /subsetP subA]. 
  case: (Path_from_induced p) => q sub_S Hq. 
  apply: (connectRI q) => z.
  rewrite in_collective Hq => /mapP[z'] /subA Hz' ->.
  exact: imset_f.
Qed.

Lemma connected_induced (G : sgraph) (S : {set G}) : 
  connected S -> connected [set: induced S].
Proof.
  move => conn_S x y _ _. 
  rewrite restrictE => [|u]; last by rewrite inE.
  have/connect_irredRP := conn_S _ _ (valP x) (valP y).
  case: (boolP (val x == val y)) => [|E /(_ isT) [p] _ /subsetP sub_S].
  - rewrite val_eqE => /eqP-> _. exact: connect0.
  - case: (Path_to_induced sub_S) => q _. exact: Path_connect q.
Qed.

Lemma connected_card_gt1 (G : sgraph) (S : {set G}) :
  connected S -> {in S &, forall x y, x != y -> exists2 z, z \in S & x -- z }.
Proof.
  move=> conn_S x y x_S y_S xNy.
  move: conn_S => /(_ x y x_S y_S)/(connect_irredRP xNy)[p] _ /subsetP p_S.
  case: (splitL p xNy) => [z] [xz] [p'] [_ eqi_p'].
  exists z; last by []; apply: p_S.
  by rewrite in_collective nodesE inE -eqi_p' path_begin.
Qed.

(** *** Connected components *)

Definition components (G : sgraph) (H : {set G}) : {set {set G}} :=
  equivalence_partition (connect (restrict H (--))) H.

Lemma partition_components (G : sgraph) (H : {set G}) :
  partition (components H) H.
Proof. apply: equivalence_partitionP. exact: (@sedge_equiv_in G). Qed.

Lemma trivIset_components (G : sgraph) (U : {set G}) : trivIset (components U).
Proof.  by case/and3P : (partition_components U). Qed.

Lemma partition0 (T : finType) (P : {set {set T}}) (D : {set T}) :
  partition P D -> set0 \in P = false.
Proof. case/and3P => _ _. by apply: contraNF. Qed.
Arguments partition0 [T P] D.

#[export]
Hint Resolve partition_components trivIset_components : core.

Lemma components_pblockP (G : sgraph) (H : {set G}) (x y : G) :
  reflect (exists p : Path x y, p \subset H) (y \in pblock (components H) x).
Proof.
  apply: (iffP idP).
  - case/(pblock_eqvE (@sedge_equiv_in _ _)) => xH yH. 
    wlog xNy : / x != y.
    { move=> Hyp. case: (altP (x =P y)) => [<- _|]; last exact: Hyp.
      exists (idp x). apply/subsetP=> z. by rewrite mem_idp => /eqP->. }
    case/(connect_irredRP xNy) => p _ p_sub. by exists p.
  - case=> p /subsetP p_sub. rewrite pblock_equivalence_partition.
    + exact: connectRI p_sub.
    + exact: sedge_equiv_in.
    + apply: p_sub; exact: path_begin.
    + apply: p_sub; exact: path_end.
Qed.

Lemma components_nonempty (G : sgraph) (U C : {set G}) :
  C \in components U -> exists x, x \in C.
Proof.
  case: (set_0Vmem C) => [->|[x inC] _]; by [rewrite (partition0 U)| exists x].
Qed.

Lemma components_subset (G : sgraph) (U C : {set G}) : 
  C \in components U -> C \subset U.
Proof.
  move => comp_C. 
  case/and3P : (partition_components U) => /eqP <- _ _.  
  apply/subsetP => x. exact: mem_cover.
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
  suff -> : C = [set y in H | connect (restrict H (--)) x y].
  { exact: connected_restrict_in. }
  apply/setP => y. rewrite inE. case: (boolP (y \in H)) => /= [y_in_H|y_notin_H].
  - by rewrite -PEQ // ?(def_pblock _ C_comp).
  - apply: contraNF y_notin_H. exact: CH.
Qed.

Lemma connected_one_component (G : sgraph) (U C : {set G}) :
  C \in components U -> U \subset C -> connected U.
Proof.
  move => comp_C sub_UC. 
  have ? : connected C by apply: connected_in_components comp_C.
  suff : U == C by move/eqP->. 
  by rewrite eqEsubset sub_UC components_subset.
Qed.



Lemma component_exit (G : sgraph) (V C : {set G}) (x y : G) :
  x -- y -> C \in components V -> x \in C -> y \in ~: V :|: C.
Proof.
  move=> xy C_comp x_C. rewrite !inE -implybE. apply/implyP => y_V.
  case/and3P: (partition_components V) => /eqP compU compI comp0n.
  have x_V : x \in V by rewrite -compU; apply/bigcupP; exists C.
  rewrite -(def_pblock compI C_comp x_C) pblock_equivalence_partition //;
    last exact: sedge_equiv_in.
  apply: (connectRI (edgep xy)) => z; rewrite mem_edgep.
  by case/orP=> /eqP->.
Qed.

Lemma remove_component (G : sgraph) (V C : {set G}) (x0 : G) : x0 \notin V ->
  C \in components V -> connected [set: G] -> connected (~: V) -> connected (~: C).
Proof.
  move=> ? C_comp G_conn VC_conn.
  case/and3P: (partition_components V) => /eqP compU compI _.
  have sub : C \subset V by rewrite -compU; exact: bigcup_sup.
  have subr : subrel (connect (restrict (~: V) (--)))
                     (connect (restrict (~: C) (--)))
    by apply: connect_mono; apply: restrict_mono; apply/subsetP; rewrite setCS.
  suff to_x0 (x : G) : x \in ~: C -> connect (restrict (~: C) (--)) x x0.
  { move=> x y /to_x0 x_x0 /to_x0. rewrite srestrict_sym. exact: connect_trans. }
  rewrite inE => xNC. wlog x_V : x xNC / x \in V.
  { move=> Hyp. case: (boolP (x \in V)); first exact: Hyp. move=> xNV.
    apply: subr. apply: VC_conn; by rewrite inE. }
  case/connect_irredP: (connectedTE G_conn x x0) => p Ip.
  have x0_VC : x0 \in ~: V by rewrite inE.
  case: (split_at_first x0_VC (path_end p)) => [x1][p1][p2][Ep x1_VC x1_first].
  have {p p2 Ep Ip} Ip1 : irred p1 by move: Ip; rewrite Ep irred_cat; case/and3P.
  apply: connect_trans (subr _ _ (VC_conn _ _ x1_VC x0_VC)).
  rewrite inE in x1_VC. apply: (connectRI p1) => z z_p1. rewrite inE.
  case: (altP (z =P x1)) => [->|zNx1]; first by apply: contraNN x1_VC; apply/subsetP.
  apply: contraNN xNC => z_C.
  rewrite -(def_pblock compI C_comp z_C). apply/components_pblockP.
  case/(isplitP Ip1) Ep1 : _ / z_p1 => [q1 q2 _ _ H].
  have x1Nq1 : x1 \notin q1 by apply: contraNN zNx1 => A; rewrite [x1]H.
  exists (prev q1). apply/subsetP=> u. rewrite mem_prev => u_q1.
  apply: contraNT x1Nq1 => uNV. rewrite -(x1_first u) ?inE //.
  by rewrite Ep1 mem_pcat u_q1.
Qed.



(** Component of a given vertex *)

Definition component_of (G : sgraph) (x : G) := pblock (components [set: G]) x.

Lemma in_component_of (G : sgraph) (x : G) : x \in component_of x.
Proof. by rewrite mem_pblock (cover_partition (D := setT)). Qed.

Lemma component_of_components (G : sgraph) (x : G) : 
  component_of x \in components [set: G].
Proof. by rewrite pblock_mem // (cover_partition (D := setT)). Qed.

Lemma connected_component_of (G : sgraph) (x : G) : 
  connected (component_of x). 
Proof. apply: connected_in_components. exact: component_of_components. Qed.

Lemma same_component (G : sgraph) (x y : G) : 
  x \in component_of y -> component_of x = component_of y.
Proof. move => xy. exact: same_pblock. Qed.

Lemma component_exchange (G : sgraph) (x y : G) : 
  (y \in component_of x) = (x \in component_of y).
Proof. 
  apply/components_pblockP/components_pblockP.
  all: case => p _; by exists (prev p).
Qed.

Lemma mem_component (G : sgraph) (C : {set G}) x : 
  C \in components [set: G] -> x \in C -> C = component_of x.
Proof. move => comp_C inC. symmetry. exact: def_pblock. Qed.



(** *** Cliques *)

Section Cliques.
Variables (G : sgraph).
Implicit Types S : {set G}.

Definition clique S := {in S&, forall x y, x != y -> x -- y}.

Definition cliqueb S := [forall x in S, forall y in S, (x != y) ==> x -- y]. 

Lemma cliqueP S : reflect (clique S) (cliqueb S).
Proof.
  apply: (equivP forall_inP). setoid_rewrite <- (rwP forall_inP). 
  setoid_rewrite <- (rwP implyP). by firstorder.
Qed.

Lemma cliquePn S : 
  reflect (exists x y, [/\ x \in S, y \in S, x != y & ~~ x -- y]) (~~ cliqueb S).
Proof.
  apply: (equivP forall_inPn). setoid_rewrite <- (rwP forall_inPn). 
  setoid_rewrite negb_imply. setoid_rewrite <- (rwP andP). by firstorder.
Qed.

Lemma clique1 (x : G) : clique [set x].
Proof. move => y z /set1P-> /set1P ->. by rewrite eqxx. Qed.

Lemma clique2 (x y : G) : x -- y -> clique [set x;y].
Proof.
  move => xy z z'. rewrite !inE.
  do 2 case/orP => /eqP-> // ; try by rewrite eqxx.
  by rewrite sg_sym.
Qed.

Lemma small_clique (S : {set G}) : #|S| <= 1 -> clique S.
Proof. move/card_le1_eqP => H x y xS yS. by rewrite (H x y) ?eqxx. Qed.


End Cliques.


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
  [forall x, forall y, #|[pred p : IPath x y| val p \subset S]| <= 1] .

Lemma is_forestP S : reflect (is_forest S) (is_forestb S).
Proof.
  apply: (iffP idP) => [H x y p q [Ip Sp] [Iq Sq]|H].
    move/forallP/(_ x)/forallP/(_ y) : H => H.
    suff: Sub p Ip == Sub q Iq :> IPath x y by rewrite -val_eqE => /eqP.
    apply/eqP. apply:(card_le1_eqP H); by rewrite inE.
  - apply/forallP => x. apply/forallP => y. 
    apply/card_le1_eqP => [[p Ip]] [q Iq]. rewrite !inE /= => pS qS.
    apply: val_inj => /=. exact: H.
Qed.

Lemma is_forestPn (S : {set G}) : 
  reflect (exists x y (p1 p2 : IPath x y), [/\ p1 \subset S, p2 \subset S & p1 != p2])
          (~~ is_forestb S).
Proof.
  rewrite negb_forall. apply: existsPP => x. 
  rewrite negb_forall. apply: existsPP => y. 
  rewrite -ltnNge. apply: (iffP card_gt1P) => /=. 
  all: by move => [p1] [p2] [A B C]; exists p1; exists p2.
Qed.

Lemma forest3 : is_forest [set: G] -> 3 <= #|G| -> exists x y : G, x != y /\ ~~ x -- y.
Proof.
  move => /is_forestP forest_G card_G. 
  setoid_rewrite (rwP andP). do ! setoid_rewrite (rwP existsP).  
  apply: contraTT forest_G => P.
  have {P} comp_G : forall x y : G, x != y -> x -- y.
  { move => x y xDy. move/existsPn : P => /(_ x)/exists_inPn/(_ y xDy). by rewrite negbK. }
  case/card_gt2P : card_G => x [y] [z] [_ [D1 D2 D3]].
  rewrite eq_sym in D1.
  apply/is_forestPn; exists y; exists x. 
  pose p1 := Build_IPath (irred_edge (comp_G y x D1)).
  have Ip2 : irred (pcat (edgep (comp_G y z D2)) (edgep (comp_G z x D3))).
  { by rewrite irred_edgeL irred_edge andbT /= mem_edgep negb_or D1 D2. }
  pose p2 := Build_IPath Ip2.
  exists p1; exists p2. split => //. 
  have: z \in p2 by rewrite !inE. 
  apply: contraTneq => <-. by rewrite mem_edgep negb_or D3 eq_sym D2.
Qed.

Definition connectedb S := 
  [forall x in S, forall y in S, connect (restrict S (--)) x y].

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

Lemma induced_forest (G : sgraph) (F : {set G}) : 
  is_forest F -> is_forest [set: induced F].
Proof.
  move => forest_F. apply: unique_forestT => x y p q Ip Iq.
  have [p0 /subsetP p0_sub_F eq_p0] := (Path_from_induced p).
  have [q0 /subsetP q0_sub_F eq_q0] := (Path_from_induced q).
  have ?: irred p0 by rewrite irredE eq_p0 map_inj_uniq //; exact: val_inj.
  have ?: irred q0 by rewrite irredE eq_q0 map_inj_uniq //; exact: val_inj.
  have Epq : p0 = q0 by apply: forest_F. 
  apply/eqP; rewrite -nodes_eqE; apply/eqP. (* fixme *)
  apply: (inj_map val_inj). by rewrite -eq_p0 -eq_q0 Epq.
Qed.

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

Definition sunit := @SGraph unit_finType rel0 rel0_sym rel0_irrefl.

Definition unit_forest : is_forest [set: sunit].
Proof. by move => [] [] p1 p2 [/irredxx -> _] [/irredxx -> _]. Qed.

Definition tunit := Forest unit_forest.

(** Non-standard: we do not substract 1 *)
Definition width (T G : finType) (D : T -> {set G}) := \max_(t:T) #|D t|.

Lemma width_bound (T G : finType) (D : T -> {set G}) : width D <= #|G|.
Proof. apply/bigmax_leqP => t _; exact: max_card. Qed.

Definition rename (T G G' : finType) (B: T -> {set G}) (h : G -> G') :=
  [fun x => h @: B x].

(** ** Complete graphs *)

Definition complete_rel n := [rel x y : 'I_n | x != y].
Fact complete_sym n : symmetric (@complete_rel n).
Proof. move => x y /=. by rewrite eq_sym. Qed.
Fact complete_irrefl n : irreflexive (@complete_rel n).
Proof. move => x /=. by rewrite eqxx. Qed.
Definition complete n := SGraph (@complete_sym n) (@complete_irrefl n).
Notation "''K_' n" := (complete n)
  (at level 8, n at level 2, format "''K_' n").

Definition C3 := 'K_3.
Definition K4 := 'K_4.

Lemma diso_Kn (G : sgraph) : (forall x y : G, x != y -> x -- y) -> diso G 'K_#|G|.
Proof.
move => completeG; apply: (@Diso G 'K_#|G| bij_ord).
- by move=> x y xy; rewrite /edge_rel/= -(inj_eq enum_val_inj) !enum_rankK sg_edgeNeq.
- move => x y xy /=. apply: completeG.
  by rewrite -(inj_eq enum_rank_inj) !enum_valK.
Qed.

Lemma sub_Kn n (G : sgraph) : #|G| <= n -> subgraph G 'K_n.
Proof.
move=> leGn; pose h (x : G) : 'K_n := widen_ord leGn (enum_rank x).
by exists h; move => // x y /(congr1 val) E; apply /enum_rank_inj/ord_inj.
Qed.

(** ** Complete bipartite graphs *)
Section Knm.
Variables n m : nat.
Definition kb_rel (x y : 'I_n + 'I_m) := is_inl x (+) is_inl y.
Lemma kb_rel_sym : symmetric kb_rel. exact: addbC. Qed. 
Lemma kb_rel_irrefl : irreflexive kb_rel.
Proof. move => x. by rewrite /kb_rel -negb_eqb eqxx. Qed.
Definition KB := SGraph kb_rel_sym kb_rel_irrefl.

(** Injection from ['K_n,m] to nat, used to order the vertices to
break symmeties *)
Definition pickle_Knm (i : KB) : nat := 
  match i with inl (Ordinal k _) => k | inr (Ordinal k _) => n + k end.

Lemma pickle_Knn_inj : injective pickle_Knm.
Proof.
case => -[i Hi]; case => -[j Hj] => //= Eij.
- congr (inl _); exact/val_inj.
- case:notF. by rewrite Eij -ltn_subRL subnn ltn0 in Hi.
- case:notF. by rewrite -Eij -ltn_subRL subnn ltn0 in Hj.
- congr (inr _). by apply/val_inj/eqP; rewrite /= -(eqn_add2l n) Eij.
Qed.

End Knm.
Notation "''K_' n , m" := (KB n m)
  (at level 8, n at level 2, m at level 2,format "''K_' n , m").

Lemma Knm_connected n m : connected [set: 'K_n.+1,m.+1].
Proof.
apply: (@connected_center _ (inl ord0 : 'K_n.+1,m.+1)) => // y _.
rewrite restrictE; last by move=> ?; rewrite inE.
case: y => [y|y]; last exact: connect1.
by apply: (@connect_trans _ _ (inr ord0)); apply: connect1.
Qed.

(** ** Adding Edges *)

Definition add_edge_rel (G:sgraph) (i o : G) := 
  relU (@edge_rel G) (sc [rel x y | [&& x != y, x == i & y == o]]).

Lemma add_edge_sym_ (G:sgraph) (i o : G) : symmetric (add_edge_rel i o).
Proof. apply: relU_sym'. exact: sg_sym. exact: sc_sym. Qed.

Lemma add_edge_irrefl_ (G:sgraph) (i o : G) : irreflexive (add_edge_rel i o).
Proof. move => x /=. by rewrite sg_irrefl eqxx. Qed.

Definition add_edge (G:sgraph) (i o : G) :=
  {| svertex := G;
     sedge := add_edge_rel i o;
     sg_sym' := add_edge_sym_ i o;
     sg_irrefl' := add_edge_irrefl_ i o |}.

Lemma add_edge_Path (G : sgraph) (i o x y : G) (p : @Path G x y) :
  exists q : @Path (add_edge i o) x y, nodes q = nodes p.
Proof.
  case: p => p p_pth.
  have p_iopth : @pathp (add_edge i o) x y p.
  { case/andP: p_pth => p_path p_last. apply/andP; split=> //.
    apply: sub_path p_path. rewrite {2}/edge_rel/=. by move=> u v /=->. }
  by exists (Sub (p : seq (add_edge i o)) p_iopth).
Qed.

Lemma add_edge_connected (G : sgraph) (i o : G) (U : {set G}) :
  @connected G U -> @connected (add_edge i o) U.
Proof.
  move => con1 x y xU yU. 
  apply: connect_mono (con1 _ _ xU yU) => {x y xU yU} x y.
  by rewrite {2}/edge_rel /= -andbA => /and3P[-> -> ->].
Qed.

(** Lemmas to swap the nodes of add_edge, useful for wlog. reasoning *)

Lemma add_edgeC (G : sgraph) (s1 s2 : G):
  @edge_rel (add_edge s1 s2) =2 @edge_rel (add_edge s2 s1).
Proof.
  move => x y. rewrite /edge_rel /= [y == x]eq_sym. 
  by case (x -- y) => //=; do ! (case (_ == _); rewrite //=).
Qed.
Arguments add_edgeC [G].

Lemma add_edge_sym (G : sgraph) (s1 s2 : G):
  diso (@add_edge G s1 s2) (@add_edge G s2 s1).
Proof. apply: eq_diso. exact: add_edgeC. Defined.

Lemma add_edge_connected_sym (G : sgraph) s1 s2 A:
  @connected (@add_edge G s1 s2) A <-> @connected (@add_edge G s2 s1) A.
Proof. apply: eq_connected => u v. exact: (add_edgeC s1 s2). Qed.

Lemma add_edge_pathC (G : sgraph) (s1 s2 x y : G) (p : @Path (add_edge s1 s2) x y) :
  exists q : @Path (add_edge s2 s1) x y, nodes q = nodes p.
Proof.
  case: (@lift_Path (add_edge s2 s1) (add_edge s1 s2) id x y p) => //.
  - move => u v. by rewrite add_edgeC.
  - move => u. by rewrite mem_map // mem_enum.
  - move => q Hq _. exists q. by rewrite -Hq map_id.
Qed.

Lemma add_edge_avoid (G : sgraph) (s1 s2 x y : G) (p : @Path (add_edge s1 s2) x y) : 
  (s1 \notin p) || (s2 \notin p) -> exists q : @Path G x y, nodes q = nodes p.
Proof.
  move => H. 
  wlog H : s1 s2 p {H} / s1 \notin p => [W|].
  { case/orP: H => [|Hs]; first exact: W. 
    case: (add_edge_pathC p) => p' Hp'. 
    case: (W _ _ p' _). by rewrite (mem_path p') Hp' -(mem_path p).
    move => q Hq. exists q. congruence. }
  have pP u : u \in p -> u == s1 = false. { by apply: contraTF => /eqP->. }
  case: (@lift_Path_on G (add_edge s1 s2) id x y p) => //.
  - move => u v up vp /=. by rewrite {1}/edge_rel/= !(pP u,pP v) //= !andbF !orbF.
  - move => u. by rewrite mem_map // mem_enum.
  - move => q Hq _. exists q. by rewrite -Hq map_id.
Qed.
Arguments add_edge_avoid [G s1 s2 x y] p.  

Lemma add_edge_subgraph (G : sgraph) (x y : G) : subgraph G (add_edge x y).
Proof. by exists id => // u v uv _; rewrite /edge_rel/= uv. Qed.

(** Andding all edges between two sets of vertices (i.e., adding a complete bipartite subgraph graph) *)

Section AddEdges2.
Variables (G : sgraph) (U V : {set G}).
Definition add_edges2_rel := 
  [rel u v : G | u -- v || (u != v) && ((u \in U) && (v \in V) || (u \in V) && (v \in U))].

Fact add_edges2_irrefl : irreflexive add_edges2_rel.
Proof. by move=> x /=; rewrite sg_irrefl eqxx. Qed.

Fact add_edges2_sym : symmetric add_edges2_rel.
Proof. 
by move=> x y; rewrite /= ![_ && (x \in _)]andbC [_ && _ || _]orbC eq_sym sg_sym.
Qed.

Definition add_edges2 := SGraph add_edges2_sym add_edges2_irrefl.
End AddEdges2.

Arguments add_edges2 : clear implicits.

(* TODO: load earlier *)
Require Import set_tac.

Ltac set_tac_close_plus ::=
  match goal with
  (* coercion free variants ... *)                                                                         
  | [ H : is_true (?x \notin (pcat ?p ?q)) |- _] => 
    first[notHyp (x \notin p)|notHyp (x \notin q)];
    have/andP [? ?]: (x \notin p) && (x \notin q) by rewrite mem_pcat negb_or in H
  | [H : is_true (?u \notin (@edgep _ ?x ?y _)) |- _] => 
    first[notHyp (u != x)|notHyp (u != y)];
    have/andP[? ?]: (u != x) && (u != y) by (move: H; rewrite mem_edgep negb_or; apply)
  | [H : is_true (?x \notin ?p), p : Path ?x _ |- _] => by rewrite path_begin in H
  | [H : is_true (?x \notin ?p), p : Path _ ?x |- _] => by rewrite path_end in H
  (* variant with coercions ... TOHINK: remove? *)
  | [ H : is_true (?x \notin _ (pcat ?p ?q)) |- _] =>
    first[notHyp (x \notin p)|notHyp (x \notin q)];
    have/andP [? ?]: (x \notin p) && (x \notin q) by rewrite mem_pcat negb_or in H
  end.

Ltac set_tac_branch_plus ::=
  match goal with
  | [ H : is_true (?x \in (pcat ?p ?q)) |- _] =>
    notHyp (x \in p);notHyp (x \in q);
    have/orP [?|?]: (x \in p) || (x \in q) by rewrite mem_pcat in H
  end.

Lemma add_edge_keep_connected_l (G : sgraph) s1 s2 A:
  @connected (@add_edge G s1 s2) A -> s1 \notin A -> @connected G A.
Proof.
  move => H s1A x y xA yA. 
  case: (altP (x =P y)) => [-> //|xDy].
  case/connect_irredRP : (H _ _ xA yA) => // p Ip subA. 
  case: (add_edge_avoid p) => [|q Hq]; first by rewrite notinD.
  apply connectRI with q. move => u. 
  rewrite mem_path Hq -(mem_path p). by set_tac.
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
    have q' : @pathp add_node (Some x) (Some y) q0.
      move: p'; rewrite /pathp/= last_map (inj_eq (@Some_inj _)).
      move=> /andP[p' ->]; rewrite andbT.
      exact: homo_path p'.
    by exists (Sub _ q'); rewrite !nodesE /=.
  Qed.
End AddNode.
Arguments add_node : clear implicits.

Lemma diso_add_nodeK (G : sgraph) (A : {set G}) : 
  G ≃ @induced (add_node G A) [set~ None].
Proof.
set H := induced _. (* todo: factor out the bijetion *)
have h_proof (x : G) : Some x \in [set~ None] by rewrite !inE.
pose h (x : G) : H := Sub (Some x) (h_proof x).
have default (x : H) : G by case: x => -[x//|]; rewrite !inE eqxx.
pose g (x : H) : G := if val x is Some z then z else default x.
have can_h : cancel h g by [].
have can_g : cancel g h. 
  move => [[x|] p]; [exact: val_inj|by exfalso; rewrite !inE eqxx in p].
exact: Diso' can_h can_g _.
Defined.

(** recursive characterization of ['K_n] *)
Lemma diso_add_edge_KSn n : diso 'K_n.+1 (add_node 'K_n setT).
Proof.
set G := add_node _ _; apply: diso_sym.
have -> : n.+1 = #|G| by rewrite card_option card_ord.
by apply: diso_Kn => -[x|] [y|] // _; rewrite /edge_rel/= inE.
Qed.

Lemma connected_add_node (G : sgraph) (U A : {set G}) : 
  connected A -> @connected (add_node G U) (Some @: A).
Proof. 
  move => H x y /imsetP [x0 Hx0 ->] /imsetP [y0 Hy0 ->].
  have/connect_irredRP := H _ _ Hx0 Hy0. 
  case: (x0 =P y0) => [-> _|_ /(_ isT) [p _ Hp]]; first exact: connect0.
  case: (add_node_lift_Path U p) => q E. 
  apply: (connectRI q) => ?; rewrite mem_path E.
  case/mapP => z Hz ->. rewrite imset_f //. exact: (subsetP Hp).
Qed.

(** Spliting [add_node] into adding one edge/node and the remaining
edges. Useful for constructing plane embeddings *)

Lemma add_node_diso_proof (G : sgraph) (A : {set G}) (x : G) : x \in A ->
     @add_edges2_rel (add_node G [set x]) [set None] [set Some x | x in A :\ x] 
  =2 add_node_rel A.
Proof.
move=> x_A [u|] [v|] //=; rewrite [in LHS]/edge_rel/= ?inE //.
- rewrite andbT andFb /= inj_imset ?inE; last exact: Some_inj.
  by have [->|//] := eqVneq u x; rewrite x_A.
- rewrite andbF andTb orbF inj_imset ?inE; last exact: Some_inj.
  by have [->|//] := eqVneq v x; rewrite x_A.
Qed.

Lemma add_node_diso (G : sgraph) (A : {set G}) (x : G) : 
  x \in A -> 
  diso (add_edges2 (add_node G [set x]) [set None] (Some @: (A :\ x))) (add_node G A).
Proof. by move=> x_A; exact/eq_diso/add_node_diso_proof. Defined.

(** Complement Graph *)
Section complement.
Variable (G : sgraph).
Definition compl_rel := [rel x y : G | (x != y) && ~~ x -- y].

Fact compl_rel_irrefl : irreflexive compl_rel. 
Proof. by move=> x; rewrite /= eqxx. Qed.

Fact compl_rel_sym : symmetric compl_rel. 
Proof. by move=> x y; rewrite /= eq_sym sgP. Qed.

Definition compl := SGraph compl_rel_sym compl_rel_irrefl.

End complement.

Lemma diso_compl (G : sgraph) : compl (compl G) ≃ G.
Proof.
apply: (@Diso' (compl (compl G)) G id id) => // x y.
abstract 
 by rewrite [RHS]/edge_rel/= [in RHS]/edge_rel/= negb_and !negbK; 
 case: eqVneq => /= [->|]; rewrite sgP.
Defined.

Open Scope implicit_scope.

Lemma isubgraph_compLR_mono (F G : sgraph) (i : compl F ⇀ G) (x y : F) :
  i x -- i y :> compl G = x -- y.
Proof.
have I := isubgraph_inj i.
rewrite [LHS]/edge_rel/= isubgraph_mono [in LHS]/edge_rel/= inj_eq //.
rewrite negb_and !negbK andb_orr andbC andbN orFb andb_idl //.
by move/sg_edgeNeq ->.
Qed. 

Lemma isubgraph_complLR (F G : sgraph) (i : compl F ⇀ G) : F ⇀ compl G.
Proof.
have I := isubgraph_inj i; apply: (@ISubgraph F (compl G) i) => // x y.
exact: isubgraph_compLR_mono.
Defined.

Lemma iso_isubgraph (F G : sgraph) (i : F ≃ G) : F ⇀ G.
Proof. exists i. exact: bij_injective. exact: edge_diso. Defined.

Lemma isubgraph_compl (F G : sgraph) (i : F ⇀ G) : compl F ⇀ compl G.
Proof.
apply: isubgraph_complLR. exact: isubgraph_comp (iso_isubgraph (diso_compl F)) i.
Defined.

Close Scope implicit_scope.


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

  Lemma neighbor1P (x : G) (A : {set G}) : 
    reflect (exists2 y, x -- y & y \in A) (neighbor [set x] A).
  Proof.
    apply: (iffP (neighborP _ _)) => [[z] [y] [/set1P->]|[y ? ?]]; first by exists y.
    by exists x, y; rewrite !inE.
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

  Lemma neighborUl A B C : neighbor A B -> neighbor A (B :|: C).
  Proof. apply: neighborW => //. exact: subsetUl. Qed.

  Lemma neighborUr A B C : neighbor A C -> neighbor A (B :|: C).
  Proof. apply: neighborW => //. exact: subsetUr. Qed.

  Lemma neighbor11 x y: neighbor [set x] [set y] = x -- y.
  Proof.
    apply/neighborP/idP => [[?[?[/set1P -> /set1P ->]]] //|xy].
    by exists x,y; rewrite !inE eqxx.
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
  case/or3P : N3 => [-> //||] /and3P [_ /eqP ? /eqP ?]; by subst;contrab.
Qed.

Lemma neighbor_del_edge2 (G : sgraph) (s1 s2 : G) (A B : {set G}) :
  s2 \notin A -> s2 \notin B -> @neighbor (add_edge s1 s2) A B -> @neighbor G A B.
Proof.
  move => H1 H2 /neighborP [x] [y] [/= N1 N2 N3]. apply/neighborP. exists x; exists y.
  case/or3P : N3 => [-> //||] /and3P [_ /eqP ? /eqP ?]; by subst;contrab.
Qed.

Lemma neighbor_del_edge1 (G : sgraph) (s1 s2 : G) (A B : {set G}) :
  s1 \notin A -> s1 \notin B -> @neighbor (add_edge s1 s2) A B -> @neighbor G A B.
Proof. move => ? ?. rewrite neighbor_add_edgeC. exact: neighbor_del_edge2. Qed.

Lemma neighbor_add_edge (G : sgraph) (s1 s2 : G) : 
  subrel (@neighbor G) (@neighbor (add_edge s1 s2)).
Proof. 
  move => A B /neighborP [u] [v] [? ? E]. 
  apply/neighborP; exists u; exists v. by rewrite /edge_rel/= E.
Qed.

Lemma neighbor_split (G : sgraph) (A B C1 C2 : {set G}) :
  B \subset C1 :|: C2 -> neighbor A B -> neighbor A C1 || neighbor A C2.
Proof.
  move/subsetP => S /neighborP [u] [v] [? /S H E]. apply/orP.
  by case/setUP : H => ?; [left|right]; apply/neighborP; exists u; exists v.
Qed.


Lemma path_neighborL (G : sgraph) (x y : G) (p : Path x y) (A : {set G}) :
  irred p -> interior p != set0 -> x \in A -> neighbor A (interior p).
Proof.
  move => Ip /set0Pn [z Hz] xA. 
  have xDy : x != y.
  { apply: contraTneq Hz => ?; subst y. rewrite (irredxx Ip).
    rewrite !inE mem_idp. by case: (z == x). }
  case: (splitL p xDy) => u [xu] [p'] [E _]. rewrite E irred_edgeL in Ip.
  apply/neighborP; exists x; exists u; split => //. case/andP : Ip => Hp Ip.
  rewrite E !inE /= andbT eq_sym sg_edgeNeq //=.
  apply: contraTneq Hz => ?. subst u. 
  by rewrite E (irredxx Ip) pcat_idR interior_edgep inE.
Qed.

(** Interior of irredundant paths *)

Lemma interior_idp (G : sgraph) (x : G) : interior (idp x) = set0.
Proof. apply/setP => z. rewrite !inE mem_idp. by (case: (_ == _)). Qed.

Lemma interior_rev (G : sgraph) (x y : G) (p : Path x y): 
  interior (prev p) = interior p.
Proof. apply/setP => z. by rewrite !inE orbC. Qed.

Lemma path_neighborR (G : sgraph) (x y : G) (p : Path x y) (A : {set G}) :
  irred p -> interior p != set0 -> y \in A -> neighbor A (interior p).
Proof. 
  move => Ip P0 yA. rewrite -interior_rev. 
  apply: path_neighborL; by rewrite // ?irred_rev ?interior_rev.
Qed.

Lemma connected_interior (G : sgraph) (x y : G) (p : Path x y) :
  irred p -> connected (interior p).
Proof.
  case: (altP (x =P y)) => [?|xNy] Ip; subst.
  - rewrite (irredxx Ip) interior_idp. exact: connected0.
  - case: (splitL p xNy) => x' [xx'] [p'] [E _]. 
    rewrite E irred_edgeL in Ip. case/andP : Ip => xp Ip'.
    case: (altP (x' =P y)) => [?|x'Ny]; subst. 
    + rewrite (irredxx Ip') pcat_idR interior_edgep. exact: connected0.
    + case: (splitR p' x'Ny) => z [q] [zy] ?. subst.
      rewrite irred_edgeR in Ip'. case/andP : Ip' => yq Iq.
      suff -> : interior (pcat (edgep xx') (pcat q (edgep zy))) = [set u in q].
      { exact: connected_path. }
      apply/setP => u. rewrite 3!inE mem_pcat_edgeL mem_pcat_edgeR !inE. 
      case: (u =P x) => [ux|_];case: (u =P y) => [uy|_] => //=; subst u.
      all: rewrite ?(negbTE yq) //; symmetry.
      all: by apply: contraNF xp; rewrite !inE => ->.
Qed.

Lemma connected_interiorR (G : sgraph) (x y : G) (p : Path x y) : 
  irred p -> connected (y |: interior p).
Proof.
  move => Ip. case: (set_0Vmem (interior p)) => [->|[z Hz]]. 
  - rewrite setU0. exact: connected1.
  - apply: neighbor_connected; [exact: connected1|exact: connected_interior|].
    apply: path_neighborR => //; by set_tac. 
Qed.

(* TOTHINK: This lemma looks bespoke, but it is actually used multiple times *)
Lemma neighbor_interiorL (G : sgraph) (x y : G) (p : Path x y) :
  x != y -> irred p -> neighbor [set x] (y |: interior p).
Proof.
  move => xDy Ip. case: (set_0Vmem (interior p)) => [E|[z Hz]]. 
  - apply: neighborUl. apply/neighborP; exists x; exists y. 
    case: (interior0E xDy Ip E) => xy _. split => //; by rewrite inE eqxx.
  - apply: neighborUr. apply: path_neighborL => //; by set_tac. 
Qed.

(** ** Edge Sets *)

Definition sg_edge_set (G : sgraph) := [set [set x;y] | x in G, y in G & x -- y].
Notation "E( G )" := (sg_edge_set G) (at level 0, G at level 99, format "E( G )").

Lemma edgesP (G : sgraph) (e : {set G}) : 
  reflect (exists x y, e = [set x;y] /\ x -- y) (e \in E(G)).
Proof.
  apply: (iffP imset2P) => [[x y]|[x] [y] [E xy]].
  - rewrite !inE /= => _ xy ->. by exists x; exists y.
  - exists x y => //. by rewrite inE.
Qed.

Lemma in_edges (G : sgraph) (u v : G) : [set u; v] \in E(G) = (u -- v).
Proof. 
  apply/edgesP/idP => [[x] [y] []|]; last by exists u; exists v.
  by case/doubleton_eq_iff => -[-> ->] //; rewrite sgP.
Qed.

Lemma edges_opn0 (G : sgraph) (x : G) : E(G) = set0 -> #|N(x)| = 0.
Proof.
move => E0; apply: eq_card0 => y; rewrite !inE; apply: contra_eqF E0 => xy.
by apply/set0Pn; exists [set x;y]; rewrite in_edges.
Qed.

(* TODO: this shoudld be the definition of subgraph *)
Lemma sub_card_edge (G H : sgraph) (h : G -> H) : 
  injective h -> is_dhom h -> #|E(G)| <= #|E(H)|. 
Proof.
move=> inj_h hom_h ; pose h' (e : {set G}) := h @: e.
have inj_h' : {in E(G) &, injective h'} by apply:in2W; apply: imset_inj.
rewrite -(card_in_imset inj_h'); apply/subset_leq_card/subsetP => ?.
case/imsetP => e /edgesP [x[y [-> /hom_h xy]]] ->; apply/edgesP; exists (h x),(h y).
by rewrite /h' imsetU1 imset_set1.
Qed.
Arguments sub_card_edge [G H] h.

Lemma diso_card_edge (G H : sgraph) : diso G H -> #|E(G)| = #|E(H)|.
Proof.
case => -[g h can_g can_h] /= hom_g hom_h; apply/eqP.
rewrite eqn_leq (sub_card_edge g) ?(sub_card_edge h) //; exact: can_inj.
Qed.

(** useful to define functions (morally on edge-sets) that need access
to the endpoints of the edge *)
Variant edge_spec (G : sgraph) (e : {set G}) : Type :=
| Edge x y of x -- y & e = [set x; y] : edge_spec e 
| NoEdge of e \notin E(G) : edge_spec e.

Lemma edgeP (G : sgraph) (e : {set G}) : edge_spec e.
Proof. 
  have [edge_e|] := boolP (e \in E(G)); last by constructor.
  have E : exists p : G * G, (e == [set p.1; p.2]) && (p.1 -- p.2).
  { case/edgesP : edge_e => x [y] [/eqP ? ?]. by exists (x,y). }
  set p := xchoose E; case/andP: (xchooseP E) => /eqP ? ?.
  exact: (@Edge _ e p.1 p.2).
Qed.

(* TODO: use [disjoint e1 & e2] *)
Lemma edges_eqn_sub (G : sgraph) (e1 e2 : {set G}) : 
  e1 \in E(G) -> e2 \in E(G) -> e1 != e2 -> ~~ (e1 \subset e2).
Proof.
move => /edgesP [x1 [y1 [-> xy1]]] /edgesP [x2 [y2 [-> xy2]]].
apply/contraNN; rewrite subUset !sub1set !inE => EQS.
case/andP : EQS xy1 xy2 => /pred2P[->|->] /pred2P [->|->].
all: by rewrite ?sg_irrefl // setUC.
Qed.

(** edge sets and neighboorhoods for ['K_n] *)

Lemma deg_Kn n (x : 'K_n.+1) : n <= #|N(x)|.
Proof.
have E : N(x) =i [pred y in 'K_n.+1 | y != x] by move=> y; rewrite !inE eq_sym.
by rewrite -ltnS -[#|_|.+1]add1n (eq_card E) -cardD1x // card_ord.
Qed.

Lemma card_edge_Kn n : #|E('K_n)| = 'C(n,2).
Proof.
rewrite -[in RHS](card_ord n) -card_draws; apply: eq_card => e.
by rewrite !inE; apply/edgesP/cards2P => [[x[y[-> xy]]]|[x[y[xy ->]]]]; exists x,y.
Qed.

(** edge sets and neighboorhoods for 'K_3,3 *)

Lemma Knm_edges n m : 
  E('K_n,m) = [set [set inl x; inr y] | x in [set:'I_n], y in [set: 'I_m]].
Proof.
apply/setP=> e. apply/edgesP/imset2P => [|[x y _ _ ->]]; last by exists (inl x), (inr y).
by move=> [[x|x] [[y|y] [// -> _]]]; [exists x y|exists y x]; rewrite // setUC.
Qed.

Lemma card_edge_Knm n m : #|E('K_n,m)| = n * m.
Proof.
rewrite Knm_edges curry_imset2X card_imset ?cardsX ?cardsT ?card_ord //=.
by move => [x y] [x' y']; rewrite /= doubleton_eq_iff => -[[[->] [->]]|[//]].
Qed.

Lemma opn_Knm_l n m (x : 'I_n) : 
  N(inl x : 'K_n,m) = [set inr y | y in [set: 'I_m]].
Proof.
apply/setP=> -[z|z]; rewrite ?inj_imset ?inE //; last exact: inr_inj.
by symmetry; apply: contraTF isT => /imsetP [z']. 
Qed.

Lemma opn_Knm_r n m (y : 'I_m) : 
  N(inr y : 'K_n,m) = [set inl x | x in [set: 'I_n]].
Proof.
apply/setP=> -[z|z]; rewrite ?inj_imset ?inE //; first exact: inl_inj.
by symmetry; apply: contraTF isT => /imsetP [z']. 
Qed.

Lemma deg_Knm_l n m (x : 'I_n) : #|N(inl x : 'K_n,m)| = m.
Proof. by rewrite opn_Knm_l card_imset ?cardsT ?card_ord //; exact: inr_inj. Qed.

Lemma deg_Knm_r n m (y : 'I_m) : #|N(inr y : 'K_n,m)| = n.
Proof. by rewrite opn_Knm_r card_imset ?cardsT ?card_ord //; exact: inl_inj. Qed.
  
Lemma deg_Knm n m (x : 'K_n,m) : minn n m <= #|N(x)|.
Proof. by case: x => [x|y]; rewrite ?deg_Knm_l ?deg_Knm_r ?geq_minr ?geq_minl. Qed.

(** edge sets for add_node *)

(* not used currently *)
Lemma edges_add_node (G : sgraph) (A : {set G}) :
  E(add_node G A) = [set [set None; Some x] | x in A] :|: 
                    [set Some @: (e : {set G}) | e in E(G)].
Proof.
apply/setP => e; apply/edgesP/setUP => [[x] [y] [-> xy]|].
- have [None_e|NoneNe] := boolP (None \in [set x;y]); [left|right].
  + wlog ? : x y xy {None_e} / None = x; [move=> W|subst x].
      by case/set2P : None_e; last rewrite setUC; apply: W; rewrite // sgP.
    by case: y xy => //= a a_A; apply: imset_f.
  + move: x y xy NoneNe => [x|] [y|]; rewrite !inE ?eqxx //= => xy _.
    by apply/imsetP; exists [set x;y]; rewrite ?in_edges // imsetU1 imset_set1. 
- move=> [/imsetP[x xA ->]|/imsetP[e' eG ->]]; first by exists None, (Some x).
  have [x[y [-> xy]]] := edgesP _ eG; exists (Some x),(Some y).
  by rewrite imsetU1 imset_set1.
Qed.

Lemma card_edge_add_node (G : sgraph) (A : {set G}) :
  #|E(add_node G A)| = #|A| + #|E(G)|.
Proof.
rewrite edges_add_node cardsU disjoint_setI0 ?cards0 ?subn0; first congr (_ + _).
- apply: card_imset => x y /setP /(_ (Some y)); rewrite !inE eqxx orbT.
  by rewrite Some_eqE => /eqP ->.
- apply: card_imset => e1 e2 eq_Some; apply/setP => x.
  by rewrite -[LHS](inj_imset _ _ Some_inj) eq_Some inj_imset.
- apply/disjointP => e E1 E2. 
  have: None \in e by case/imsetP : E1 => x _ ->; rewrite !inE eqxx.
  suff: None \notin e by move/negPf->.
  by case/imsetP : E2 => x _ ->; apply/negP=>/imsetP => -[?].
Qed.

(** ** Edge Deletion  *)

Section del_edges.
Variables (G : sgraph) (A : {set G}).

Definition del_edges_rel := [rel x y : G | x -- y && ~~ ([set x;y] \subset A)]. 

Definition del_edges_sym : symmetric del_edges_rel. 
Proof. by move=>x y /=; rewrite sgP setUC. Qed.

Definition del_edges_irrefl : irreflexive del_edges_rel.
Proof. by move=> x /=; rewrite sgP. Qed.

Definition del_edges := SGraph del_edges_sym del_edges_irrefl.
End del_edges.

Section del_edges_facts.
Variables (G : sgraph).
Implicit Types (x y z : G) (A e : {set G}).

Local Open Scope implicit_scope.

Lemma mem_del_edges e A : e \in E(del_edges A) = (e \in E(G)) && ~~ (e \subset A).
Proof.
apply/edgesP/andP => [[x] [y] [-> /andP[xy xyA]]|[]]; first by rewrite in_edges.
by move/edgesP => [x] [y] [-> xy xyNA]; exists x,y; split => //; apply/andP.  
Qed.

(** Neighborhood version of the above *)
Lemma del_edges_opn A x z : 
  z \in N(del_edges A;x) = (z \in N(G;x)) && ~~ ([set x; z] \subset A).
Proof. by rewrite !inE -in_edges mem_del_edges in_edges. Qed.

Lemma del_edges_sub A : E(del_edges A) \subset E(G).
Proof. by apply/subsetP => e; rewrite mem_del_edges => /andP[]. Qed.

Lemma del_edges_proper e A : 
  e \in E(G) -> e \subset A -> E(del_edges A) \proper E(G).
Proof.
move=> edge_e e_sub_A. rewrite properE del_edges_sub /=.
by apply/subsetPn; exists e => //; rewrite mem_del_edges edge_e e_sub_A.
Qed.

(** Two useful lemmas for the case of deleting a single edge *)
Lemma del_edgesN e : e \notin E(del_edges e).
Proof. by rewrite mem_del_edges subxx andbF. Qed.

Lemma del_edges1 e : e \in E(G) -> E(G) = e |: E(del_edges e).
Proof.
move => edge_e; apply/setP => e'; rewrite in_setU mem_del_edges in_set1.
case: (eqVneq e e') => [<-//|eDe'/=].
case: (boolP (e' \in E(G))) => //= edge_e'; symmetry. 
rewrite eq_sym in eDe'; exact: edges_eqn_sub eDe'.
Qed.

End del_edges_facts.


(** ** Neighborhood lemmas for simple graphs *)

Section Neighborhood_theory.
Variable G : sgraph.
Implicit Types (u v : G).

Lemma v_notin_opneigh v : v \notin N(v).
Proof. by rewrite in_opn sg_irrefl. Qed.

Lemma cl_sg_sym : symmetric (@dominates G).
Proof. 
rewrite /symmetric /dominates /closed_neigh => x y ; by rewrite sg_sym eq_sym. 
Qed.

Lemma opn_cln u : N(u) = N[u] :\ u.
Proof. by apply/setP => v; rewrite !inE; case: (eqVneq u v ) => //= ->; rewrite sgP. Qed.

Lemma opn_proper_cln v : N(v) \proper N[v].
Proof. 
  apply/properP; rewrite subsetUr; split => //.
  by exists v; rewrite !inE ?eqxx sgP.
Qed.

Lemma opn_edges (u : G) : N(u) = [set v | [set u; v] \in E(G)].
Proof.
  apply/eqP ; rewrite eqEsubset ; apply/andP ; split.
  - by apply/subsetP=> w ; rewrite in_opn in_set in_edges.
  - by apply/subsetP=> w ; rewrite in_opn in_set in_edges.
Qed.

Lemma cln_eq (x x' y : G) : 
  N[x] = N[x'] -> y != x -> y != x' -> x -- y = x' -- y.
Proof.
by move/setP=> /(_ y); rewrite !inE; case: (eqVneq x y); case: (eqVneq x' y).
Qed.

Lemma eq_cln_iso (v v' : G) : N[v] = N[v'] -> induced [set~ v'] ≃ induced [set~ v].
Proof.
have [-> _|vDv' Nvv'] := eqVneq v v'; first exact: diso_id.
have vv' : v -- v'. 
  by move/setP/(_ v') : Nvv'; rewrite v_in_clneigh in_cln /dominates (negbTE vDv').
set Hv := induced [set~ v']; set Hv' := induced _.
have [vI v'I] : v \in [set~ v'] /\ v' \in [set~ v] 
  by rewrite !inE [v' == _]eq_sym (sg_edgeNeq vv').
pose f (x : Hv) : Hv' := insubd (Sub v' v'I) (val x).
pose g (x : Hv') : Hv := insubd (Sub v vI) (val x).
have can_f : cancel f g.
{ move => x. apply: val_inj. rewrite /f/g/= !val_insubd !inE !SubK. 
  have [/= ->|/=] := eqVneq (val x) v; rewrite ?eqxx // ifT // -in_set1 -in_setC. 
  exact (valP x). }
have can_g : cancel g f. 
{ move => x. apply: val_inj. rewrite /f/g/= !val_insubd !inE !SubK. 
  have [/= ->|/=] := eqVneq (val x) v'; rewrite ?eqxx // ifT // -in_set1 -in_setC.
  exact (valP x). }
apply: Diso' can_f can_g _.
move => [x px] [y py]; rewrite /f/=. rewrite /edge_rel/= !val_insubd !SubK !inE.
rewrite !inE in px py. 
have [?/=|/=] := eqVneq x v; subst.
  have [->|/= yDv] := eqVneq y v; [by rewrite !sgP | by rewrite (cln_eq Nvv')].
by have [->/= xDv|//] := eqVneq y v; rewrite [RHS]sgP (cln_eq Nvv') // sgP.
Qed.

End Neighborhood_theory.

Local Open Scope implicit_scope.
Theorem edges_sum_degrees (G : sgraph) : 2 * #|E(G)| = \sum_(x in G) #|N(x)|.
Proof.
elim/(size_ind (fun G => #|E(G)|)) : G => G IH.
case: (set_0Vmem E(G)) => [E0|[e edge_e]].
- rewrite E0 cards0 muln0. 
  under eq_bigr => x do rewrite edges_opn0 //.
  by rewrite sum_nat_const muln0.
- have [x [y] [def_e xy]] := edgesP _ edge_e; set G' := del_edges e.
  have/IH E' : #|E(G')| < #|E(G)|.
  { by apply: proper_card; exact: del_edges_proper edge_e _. }
  rewrite (del_edges1 edge_e) cardsU1 del_edgesN mulnDr /= muln1 {}E' /=.
  rewrite [in LHS](bigID (mem e)) [in RHS](bigID (mem e)) /= addnA.
  congr (_ + _); last first.
  { apply eq_bigr => z zNe; apply eq_card => w. 
    by rewrite del_edges_opn subUset sub1set (negbTE zNe) /= andbT. }
  rewrite def_e !big_setU1 ?inE ?sg_edgeNeq //= !big_set1.
  suff Ne w : w \in e -> #|N(G';w)|.+1 = #|N(G;w)|.
  { rewrite -!Ne ?def_e ?in_set2 ?eqxx ?orbT //.
    by rewrite [RHS]addSn [in RHS]addnS add2n. }
  rewrite {}/G' {}def_e => {edge_e} w_in_xy.
  wlog w_is_x : x y xy {w_in_xy} / w = x.
  { move => W. case/set2P : w_in_xy; first exact: W.
    by rewrite setUC; apply: W; rewrite sgP. }
  subst w; suff -> : N(G;x) = y |: N(del_edges [set x;y];x). 
  { by rewrite cardsU1 del_edges_opn subxx andbF add1n. }
  apply/setP => z; rewrite 2!inE del_edges_opn !inE. 
  rewrite subUset subsetUl sub1set !inE /=. 
  case: (eqVneq z y) => [-> //|zDy /=]. 
  case: (eqVneq z x) => [->|]; by rewrite ?sg_irrefl //= ?orbT ?andbT.
Qed.
