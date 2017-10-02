Require Import Omega Lia.

From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries sgraph multigraph subalgebra skeleton bounded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition dom t := tmI (tmS t tmT) tm1.

(** Preliminaries *)


Lemma equivalence_rel_of_sym (T : finType) (e : rel T) :
  symmetric e -> equivalence_rel (connect e).
Proof. 
  move => sym_e x y z. split => // A. apply/idP/idP; last exact: connect_trans.
  rewrite connect_symI // in A. exact: connect_trans A.
Qed.

Lemma eq_set1P (T : finType) (A : {set T}) (x : T) : 
  reflect (x \in A /\ forall y, y \in A -> y = x) (A == [set x]).
Proof.
  apply: (iffP eqP).
  - move->. rewrite !inE eqxx. by split => // y /set1P.
  - case => H1 H2. apply/setP => y. apply/idP/set1P;[exact: H2| by move ->].
Qed.

Lemma sub_val_eq (T : eqType) (P : pred T) (u : sig_subType P) x (Px : x \in P) :
  (u == Sub x Px) = (val u == x).
Proof. by case: (SubP u) => {u} u Pu. Qed.


Lemma mem_cover (T : finType) (P : {set {set T}}) (x : T) (A : {set T}) : 
  A \in P -> x \in A -> x \in cover P.
Proof. move => HP HA. apply/bigcupP. by exists A. Qed.

Lemma sum_ge_In (T : Type) (s : seq T) (F : T -> nat) b : 
  List.In b s -> F b <= \sum_(a <- s) F a.
Proof. 
  elim: s b => //= a s IH b [<-|A]; rewrite big_cons ?leq_addr //.
  apply: leq_trans (IH _ A) _. exact: leq_addl.
Qed.

Lemma sum_gt0 (T : Type) (s : seq T) (F : T -> nat) : 
  (forall a, List.In a s -> 0 < F a) -> 1 < size s ->
  forall b, List.In b s -> F b < \sum_(a <- s) F a.
Proof.
  move => A B a a_in_s. apply/negPn. apply/negP => C. rewrite -leqNgt in C.
  destruct s as [|b [|c s']] => //= {B}. rewrite !big_cons in C. 
  rewrite /= in a_in_s.
  (* should work even if we don't have decidable equality on elements of T *)
Admitted.

Lemma eq_big_seq_In (R : Type) (idx : R) (op : R -> R -> R) I (r : seq I) (F1 F2 : I -> R) :
  (forall x, List.In x r -> F1 x = F2 x) ->
  \big[op/idx]_(i <- r) F1 i = \big[op/idx]_(i <- r) F2 i.
Proof.
  elim: r => [|a r IH] eqF; rewrite ?big_nil // !big_cons eqF ?IH //; last by left.
  move => x Hx. apply: eqF. by right.
Qed.

Lemma set1_inj (T : finType) : injective (@set1 T).
Proof. move => x y /setP /(_ y). by rewrite !inE eqxx => /eqP. Qed.

Lemma subset2 (T : finType) (A : {set T}) (x y: T) : 
  (A \subset [set x;y]) = [|| A == set0, A == [set x], A == [set y] | A == [set x;y]].
Proof.
  case: (boolP (x == y)) => [/eqP ?|xy].
  - subst y. rewrite setUid subset1. by do 2  case (A == _).
Admitted.

(** Partitions possibly including the empty equivalence class *)
Definition pe_partition (T : finType) (P : {set {set T}}) (D : {set T}) :=
  (cover P == D) && (trivIset P).

Lemma trivIset3 (T : finType) (A B C : {set T}) : 
  [disjoint A & B] -> [disjoint B & C] -> [disjoint A & C] -> 
  trivIset [set A;B;C].
Proof. 
  move => D1 D2 D3. apply/trivIsetP => X Y. rewrite !inE -!orbA.
  do 2 (case/or3P => /eqP->); try by rewrite ?eqxx // 1?disjoint_sym. 
Qed.

Lemma restrictE (T : finType) (e : rel T) (A : pred T) : 
  A =i predT -> connect (restrict A e) =2 connect e.
Proof. 
  move => H x y. rewrite (eq_connect (e' := e)) //. 
  move => {x y} x y /=. by rewrite !H.
Qed.

(** Graph preliminaries *)

(* Isomorphim of graphs *)

Definition bijective2 (G1 G2 : graph) (h : h_ty G1 G2) := 
  bijective h.1 /\ bijective h.2.

Definition iso2 (G1 G2 : graph2) : Prop := 
  exists2 h : h_ty G1 G2, hom_g2 h & bijective2 h.

Notation "G ≈ H" := (iso2 G H) (at level 45).

Lemma consistentT (G : graph) (E : {set edge G}) : consistent setT E.
Proof. by []. Qed.
Arguments consistentT [G] E.

Definition remove_edges (G : graph2) (E : {set edge G}) :=
  @point (subgraph_for (consistentT (~:E))) 
         (Sub g_in (in_setT _)) 
         (Sub g_in (in_setT _)).

(** SGraph preliminaries *)

(* TOTHINK: is this the best way to  *)
Lemma induced_path (G : sgraph) (S : {set G}) (x y : sgraph.induced S) (p : Path x y) : 
  @spath G (val x) (val y) (map val (val p)).
Proof.
  case: p => p pth_p /=. elim: p x pth_p => /= [|z p IH] x pth_p.
  - by rewrite (spath_nil pth_p) spathxx.
  - rewrite !spath_cons in pth_p *. 
    case/andP : pth_p => p1 p2. apply/andP; split => //. exact: IH.
Qed.

Definition idp (G : sgraph) (u : G) := Build_Path (spathxx u).

Lemma mem_idp (G : sgraph) (x u : G) : (x \in idp u) = (x == u).
Proof. by rewrite inE. Qed.

Lemma Path_connect (G : sgraph) (x y : G) (p : Path x y) : connect sedge x y.
Abort. 


Lemma connectRI (G : sgraph) (A : pred G) x y (p : Path x y) :
  {subset p <= A} -> connect (restrict A sedge) x y.
Admitted.

(** NOTE: need to require either x != y or x \in A *)
Lemma uPathRP (G : sgraph) {A : pred G} x y : x != y ->
  reflect (exists2 p: Path x y, irred p & p \subset A) 
          (connect (restrict A sedge) x y).
Admitted. (* this is essentially upathPR *)

Lemma last_take (T : eqType) (x : T) (p : seq T) (n : nat): 
  n <= size p -> last x (take n p) = nth x (x :: p) n.
Proof.
  elim: p x n => [|a p IHp] x [|n] Hn //=.
  by rewrite IHp // (set_nth_default a x). 
Qed.

(** TOTHINK: Providing an injection from (proofs of [x -- y]) to
(trivial) paths and then using the monoid structure with [pcat] seems
preferable to providing a cons operation *)

Lemma trivp_proof (G : sgraph) (x y : G) (xy : x -- y) : 
  spath x y [:: y]. 
Proof. by rewrite spath_cons xy spathxx. Qed.

Definition trivp (G : sgraph) (x y : G) (xy : x -- y) := 
  Build_Path (trivp_proof xy).

Lemma splitL (G : sgraph) (x y : G) (p : Path x y) : 
  x != y -> exists z xy (p' : Path z y), p = pcat (trivp xy) p'.
Admitted.

Lemma splitR (G : sgraph) (x y : G) (p : Path x y) : 
  x != y -> exists z (p' : Path x z) zy, p = pcat p' (trivp zy).
Admitted.

(** 
Lemma pcons_proof (G : sgraph) (x y z : G) (p : seq G) :
  x -- y -> spath y z p -> spath x z (y::p).
Proof. by rewrite spath_cons => -> ->.  Qed.

Definition pcons (G : sgraph) (x y z : G) (xy : x -- y) (p : Path y z) :=
  Build_Path (pcons_proof xy (valP p)).
Arguments pcons [G x y z] xy p. 

Lemma splitL (G : sgraph) (x y : G) (p : Path x y) : 
  x != y -> exists z xz (p' : Path z y), p = pcons xz p'.
*)

Lemma split_at_first_aux (G : sgraph) {A : pred G} x y (p : seq G) k : 
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
  have z_nth : z = nth x (x :: p) (find A (x :: p)). 
  { rewrite /z /p1 last_take // /n -ltnS. by rewrite has_find in X. }
  exists z. exists p1. exists p2. split => //.
  - rewrite z_nth. exact: nth_find.
  - move => z' in_A' in_p'. rewrite z_nth. 
Admitted.
                                                                

Lemma split_at_first (G : sgraph) {A : pred G} x y (p : Path x y) k :
  k \in A -> k \in p ->
  exists z (p1 : Path x z) (p2 : Path z y), 
    [/\ p = pcat p1 p2, z \in A & forall z', z' \in A -> z' \in p1 -> z' = z].
Proof.
  case: p => p pth_p /= kA kp. 
  case: (split_at_first_aux pth_p kA kp) => z [p1] [p2] [def_p pth_p1 pth_p2 A1 A2].
  exists z. exists (Build_Path pth_p1). exists (Build_Path pth_p2). split => //.
  subst p. exact: val_inj.
Qed.
  

  case: p => p pth_p /= kA kp. rewrite inE in kp. case/predU1P : kp => kp.
  - subst x. exists k. exists (idp k). exists (Build_Path pth_p). admit.
  - rewrite /= in kp. 
    pose n := find A p.
Admitted. (* find-take-drop surgery *)

Lemma sedge_equiv (G : sgraph) (A : {set G}) : 
  equivalence_rel (connect (restrict (mem A) sedge)). 
Proof. apply: equivalence_rel_of_sym.  apply: symmetric_restrict. exact:sg_sym. Qed.

Lemma connectedTE (G : sgraph) (x y : G) : 
  connected [set: G] -> connect sedge x y. 
Proof. 
  move => A. move: (A x y). rewrite !restrictE; last by move => ?; rewrite inE.
  apply; by rewrite inE. 
Qed.

Lemma connectedTI (G : sgraph) : 
  (forall x y : G, connect sedge x y) -> connected [set: G].
Proof. move => H x y _ _. rewrite restrictE // => z. by rewrite inE. Qed.

Lemma connected2 (G : sgraph) (D : {set G}) : 
  (~ connected D) <-> exists x y, [/\ x \in D, y \in D & ~~ connect (restrict (mem D) sedge) x y].
Admitted.

Lemma clique1 (G : sgraph) (x : G) : clique [set x].
Proof. move => y z /set1P-> /set1P ->. by rewrite eqxx. Qed.

Lemma clique2 (G : sgraph) (x y : G) : x -- y -> clique [set x;y].
Proof. 
  move => xy z z'. rewrite !inE. 
  do 2 case/orP => /eqP-> // ; try by rewrite eqxx. 
  by rewrite sg_sym.
Qed.

(* TODO: tree_axiom still uses upath - should use packaged paths ... *)
Definition is_tree (G : sgraph) := 
  connected [set: G] /\ forall x y : G, unique (fun p : Path x y => irred p).


Definition neighbours (G : sgraph) (x : G) := [set y | x -- y].

(** Additional Checkpoint Properties *)

Local Notation "x ⋄ y" := (@sedge (link_graph _) x y) (at level 30).
Local Notation "x ⋄ y" := (@sedge (CP_ _) x y) (at level 30).

Section Checkpoints.
Variables (G : sgraph).

Hypothesis (conn_G : forall x y :G, connect sedge x y).

Lemma petalP (U : {set G}) x z : 
  reflect (forall y, y \in CP U -> x \in cp z y) (z \in petal U x).
Proof. rewrite inE. exact: (iffP forall_inP). Qed.

Lemma sinterval_sym (x y : G) : sinterval x y = sinterval y x.
Proof. apply/setP => p. by rewrite !inE orbC [_ _ _ _ && _ _ _ _]andbC. Qed.

Lemma CP_connected (U : {set G}) : connected [set: CP_ U].
Admitted.

Lemma CP_extensive (U : {set G}) : {subset U <= CP U}.
Proof.
  move => x inU. apply/bigcupP; exists (x,x); by rewrite ?inE /= ?inU // cpxx inE.
Qed.

Lemma CP_SubK (U : {set G}) x (Px : x \in CP U) :
  x = val (Sub x Px : CP_ U). 
Proof. by rewrite SubK. Qed.

Lemma cp_neighbours (x y : G) z : 
  x != y -> (forall x', x -- x' -> z \in cp x' y) -> z \in cp x y.
Proof.
  move => A B. apply/cpP => p. case: p => [|x' p].
  - move/spath_nil/eqP => ?. by contrab.
  - rewrite spath_cons in_cons => /andP [C D]. apply/orP;right. 
    apply/(cpP (y := y)) => //. exact: B. 
Qed.

Lemma CP_clique (U : {set G}) : 
 @clique (link_graph G) U -> CP U = U.
Proof.
  move => clique_U. apply/setP => x. apply/bigcupP/idP. 
  - case => [[x1 x2]]. rewrite !inE /= => /andP [U1 U2]. 
    move: (clique_U x1 x2 U1 U2). case: (boolP (x1 == x2)) => A B.
    + rewrite (eqP A) cpxx inE. by move/eqP->.
    + case/andP: (B erefl) => _ /subsetP => S /S. by case/setUP => /set1P->.
  - move => inU. by exists (x,x); rewrite ?inE /= ?inU // cpxx inE. 
Qed.

(** TOTHINK: have neighbouring checkpoints as {set G} or {set CP_ U} *)
Definition ncp (U : {set G}) (p : G) : {set G} := 
  [set x in CP U | connect (restrict [pred z | (z \in CP U) ==> (z == x)] sedge) p x]. 

(* TOTHINK: Do we also want to require [irred q] *)
Lemma ncpP (U : {set G}) (p : G) x : 
  reflect (x \in CP U /\ exists q : Path p x, forall y, y \in CP U -> y \in q -> y = x) (x \in ncp U p).
Proof.
  rewrite inE. apply: (iffP andP) => [[cp_x A]|[cp_x [q Hq]]]; split => //.
  - case: (boolP (p == x)) => [/eqP ?|px]. 
    + subst p. exists (idp x) => y _ . by rewrite mem_idp => /eqP.
    + case/(uPathRP px) : A => q irr_q /subsetP sub_q. 
      exists q => y CPy /sub_q. by rewrite !inE CPy => /eqP.
  - apply: (connectRI (p := q)) => y y_in_q.
    rewrite inE. apply/implyP => A. by rewrite [y]Hq.
Qed.

Lemma ncp_petal (U : {set G}) (p : G) x :
  x \in CP U -> (p \in petal U x) = (ncp U p == [set x]).
Proof.
  move => Ux. apply/petalP/eq_set1P.
  - move => A. split.
    + apply/ncpP; split => //.
      case/uPathP : (conn_G p x) => q irr_q. 
      case: (boolP [exists y in CP U, y \in [predD1 q & x]]).
      * case/exists_inP => y /= B. rewrite inE eq_sym => /= /andP [C D]. 
        case:notF. apply: contraTT (A _ B) => _. apply/cpPn'.
        case/(isplitP irr_q) def_q : q / D => [q1 q2 irr_q1 irr_q2 D12].
        exists q1 => //. rewrite (disjointFl D12) //. 
        suff: x \in q2. by rewrite inE (negbTE C). 
        by rewrite nodes_end.
      * rewrite negb_exists_in => /forall_inP B.
        exists q => y /B => C D. apply/eqP. apply: contraNT C => C. 
        by rewrite inE C.
    + move => y /ncpP [Uy [q Hq]]. 
      have Hx : x \in q. { apply/cpP'. exact: A. }
      apply: esym. exact: Hq. 
  - case => A B y Hy. apply/cpP' => q.
    have qy : y \in q by rewrite nodes_end.
    move: (split_at_first Hy qy) => [x'] [q1] [q2] [def_q cp_x' Hq1]. 
    suff ?: x' = x. { subst x'. by rewrite def_q mem_pcat nodes_end. }
    apply: B. apply/ncpP. split => //. exists q1 => z' H1 H2. exact: Hq1.
Qed.

Lemma petal_disj (U : {set G}) x y :
  x \in CP U -> y \in CP U -> x != y -> [disjoint petal U x & petal U y].
Proof.
  move => Ux Uy xy. apply/pred0P => p /=. apply:contraNF xy => /andP[].
  rewrite [x](CP_SubK Ux) [y](CP_SubK Uy) !ncp_petal //.
  by move => /eqP-> /eqP/set1_inj->.
Qed.

Lemma ncp_CP (U : {set G}) (u : G) :
  u \in CP U -> ncp U u = [set u].
Proof. 
  move => Hu.
  apply/setP => x. rewrite [_ \in [set _]]inE. apply/ncpP/eqP.
  - move => [Hx [q Hq]]. apply: esym. apply: Hq => //. exact: nodes_start.
  - move => ->. split => //. exists (idp u) => y _. by  rewrite mem_idp => /eqP.
Qed.

Lemma ncp0 (U : {set G}) x p : 
  x \in U -> ncp U p == set0 = false.
Proof. 
  move => Ux'. 
  case/uPathP : (conn_G p x) => q irr_q. 
  have Ux: x \in CP U by apply: CP_extensive.
  case: (split_at_first Ux (nodes_end q)) => y [q1] [q2] [def_q CPy Hy].
  suff: y \in ncp U p. { apply: contraTF => /eqP->. by rewrite inE. }
  apply/ncpP. split => //. by exists q1. 
Qed.
Arguments ncp0 [U] x p.

(** Do we really need the follwing lemma in its full generality *)
Lemma ncp_sinterval U (x y p : G) :
  [set x;y] \subset CP U ->
  sgraph.link_rel G x y -> 
  (p \in sinterval x y) = (ncp U p == [set x; y]).
Proof.
Abort.
  
(** NOTE: This looks fairly specific, but it also has a fairly
straightforward proof *)
Lemma interval_petal_disj U (x y : G) :
  y \in CP U -> [disjoint petal U x & sinterval x y].
Proof.
  move => Uy. rewrite disjoint_sym disjoints_subset. apply/subsetP => z.
  rewrite 3!inE negb_or !in_set1 => /and3P [/andP [A1 A2] B C]. 
  rewrite inE. apply:contraTN C => /petalP/(_ _ Uy). 
  apply: contraTN. case/uPathRP => // p _ /subsetP sub_p. 
  apply: (cpNI' (p := p)). apply/negP => /sub_p. by rewrite inE eqxx.
Qed.

Lemma ncp_interval U (x y p : G) : 
  x != y -> [set x;y] \subset ncp U p  -> p \in sinterval x y.
Proof.
  rewrite subUset !sub1set => xy /andP[Nx Ny]. 
  rewrite !inE negb_or. 
  gen have A,Ax : x y xy Nx Ny / p != x.
  { have Ux : x \in CP U. by case/ncpP : Nx.
    apply: contraNN xy => /eqP => ?; subst p. apply/eqP.
    case/ncpP : Ny => Uy [q] /(_ _ Ux). rewrite nodes_start. 
    by apply. }
  have Ay: p != y. apply: (A y x) => //. by rewrite eq_sym.
  rewrite Ax Ay /=. 
  gen have S,_: x y Nx Ny xy {A Ax Ay} / connect (restrict (predC1 y) sedge) p x.
  { case/ncpP : Nx => Ux [q Hq]. apply: (connectRI (p := q)).
    move => z in_q. apply: contraNT xy. rewrite negbK => /eqP ?; subst z.
    rewrite [y]Hq //. by case/ncpP : Ny. }
  apply/andP;split; apply: S => //. by rewrite eq_sym.
Qed.

Lemma link_part (x y : G) : sgraph.link_rel G x y ->
  pe_partition [set petal [set x; y] x; petal [set x; y] y; sinterval x y] [set: G].
Proof.
  move => /= /andP [xy cp_xy]. 
  have CPxy : CP [set x; y] = [set x; y].
  { apply: CP_clique. exact: clique2. }
  apply/andP; split.
  - rewrite eqEsubset subsetT /=. apply/subsetP => p _. 
    pose N := ncp [set x; y] p. 
    have: N \subset [set x; y]. by rewrite /N /ncp setIdE CPxy subsetIl.
    rewrite subset2 // (ncp0 x) ?in_setU ?set11 //=. case/or3P. 
    + rewrite -ncp_petal ?CPxy ?in_setU ?set11 //. 
      apply: mem_cover. by rewrite !inE eqxx. 
    + rewrite -ncp_petal ?CPxy ?in_setU ?set11 //. 
      apply: mem_cover. by rewrite !inE eqxx. 
    + rewrite /N. rewrite eqEsubset => /andP [_ /(ncp_interval xy)].
      apply: mem_cover. by rewrite !inE eqxx. 
  - apply: trivIset3. 
    + by apply: petal_disj => //; rewrite CPxy !inE eqxx.
    + by rewrite sinterval_sym interval_petal_disj // CPxy !inE eqxx.
    + by rewrite interval_petal_disj // CPxy !inE eqxx.
Qed.

Lemma link_cpL (x y u v : G) : sgraph.link_rel G x y -> 
  u \in petal [set x; y] x -> v \in petal [set x;y] y -> x \in cp u v.
Proof.
  move => /= /andP[xy CPxy]. rewrite !ncp_petal ?CP_extensive ?inE ?eqxx //. 
  move => Nu Nv. apply: contraTT Nu. 
  case/cpPn' => [p irr_p av_x]. 
  have/ncpP [CPy [q Hq]]: y \in ncp [set x;y] v by rewrite (eqP Nv) set11.
  rewrite eqEsubset negb_and. apply/orP;left. 
  apply/subsetPn; exists y; last by rewrite !inE eq_sym.
  apply/ncpP; split => //. exists (pcat p q) => z. 
  have ? : @clique (link_graph G) [set x; y] by apply: clique2.
  rewrite CP_clique // mem_pcat 3!inE => /orP[]/eqP-> //. 
  rewrite (negbTE av_x) /=. apply: Hq. by rewrite CP_clique // inE set11.
Qed.

Lemma link_cpR (x y u v : G) : sgraph.link_rel G x y -> 
  u \in petal [set x; y] x -> v \in petal [set x;y] y -> y \in cp u v.
Proof. rewrite link_sym setUC cp_sym => *. exact: (@link_cpL y x v u). Qed.


(* The following lemma looks a bit strange if [ncp : {set G}] *)
(* But do we really need this? *)
Lemma ncp_clique (U : {set G}) (u : G) : 
  @clique (CP_ U) [set x | val x \in (ncp U u)].
Abort. 
(* Proof.  *)
(*   case: (boolP (u \in CP U)) => Hu; first by rewrite (ncp_CP Hu); exact: clique1. *)
(*   move => x y. rewrite !inE => Hx Hy xy. *)
(*   gen have H, A : x y Hx Hy xy / u != val x.  *)
(*   { apply: contraNN Hu => /eqP->. exact: valP. } *)
(*   have {H} B : u != val y by apply: (H y x) => //; by rewrite eq_sym. *)
(*   case/(uPathRP A) : Hx => p irr_p /subsetP p_cp.  *)
(*   case/(uPathRP B) : Hy => q irr_q /subsetP q_cp.  *)
(*   rewrite /=. apply/andP;split. *)
(*   - apply: contraNN xy. by move/eqP/val_inj->. *)
(*   - set r := pcat (prev p) q. *)
(*     apply/subsetP => z cp_z.  *)
(*     have Hz : z \in CP U.  *)
(*     { admit. (* Follows with CP_closed when G is connected *) } *)
(*     move/cpP' : cp_z => /(_ r). rewrite mem_pcat mem_prev.  *)
(*     case/orP => [/p_cp|/q_cp]; rewrite inE Hz /= => /eqP->; by rewrite !inE eqxx ?orbT. *)
(* Admitted. *)

Arguments Path G x y : clear implicits.

Lemma link_path_cp (x y : G) (p : Path (link_graph G) x y) : 
  {subset cp x y <= p}.
Proof. apply/subsetP. apply: link_seq_cp. exact: (valP p). Qed.

Lemma CP_path_cp (U : {set G}) (x y : CP_ U) (p : Path _ x y) z : 
  val z \in @cp G (val x) (val y) -> z \in p.
Proof. 
  move/link_path_cp. 
  suff P : @spath (link_graph G) (val x) (val y) (map val (val p)).
  { move/(_ (Build_Path P)). rewrite inE /= mem_map //. exact: val_inj. }
  exact: induced_path.
Qed.

(* TOTHINK: What is the right formulation here? *)
Lemma CP_path_aux (U : {set G}) (x y : G) (p : seq G) :
  x \in CP U -> y \in CP U -> @spath G x y p -> uniq (x :: p) ->
  @spath (link_graph G) x y [seq z <- p | z \in CP U].
Admitted.

Lemma CP_path (U : {set G}) (x y : CP_ U) (p : @Path G (val x) (val y)) : 
  irred p -> exists2 q : @Path (CP_ U) x y, irred q & [set val z | z in q] \subset p.
Admitted.


(** NOTE: If [CP_ U] is a tree, then there exists exactly one irredundant xy-path. *)
Lemma CP_subtree1 (U : {set G}) (x y z : CP_ U) (p : @Path (CP_ U) x y) : 
  is_tree (CP_ U) -> irred p -> (z \in p <-> val z \in @cp G (val x) (val y)).
Proof.
  move => tree_U irr_p. split.
  - move => z_in_p. apply/negPn. apply/negP => /=. 
    case/cpPn' => q irr_q av_z. case: (CP_path irr_q) => r irr_r /subsetP sub_q. 
    have zr : z \notin r. { apply: contraNN av_z => in_r. apply: sub_q. by rewrite mem_imset. }
    case: tree_U => _ /(_ x y p r). case/(_ _ _)/Wrap => // ?. subst. by contrab.
  - simpl. exact: CP_path_cp.
Qed.



End Checkpoints.


(** * Term Extraction *)


(** Termination Metric *)
Definition term_of_measure (G : graph2) :=
  (g_in == g_out :> G) + 2*#|edge G|.

Local Notation measure G := (term_of_measure G).

Ltac normH := match goal 
  with 
  | [ H : is_true (_ <= _) |- _] => move/leP : H 
  | [ H : is_true (_ == _) |- _] => move/eqP : H 
  end.
Ltac elim_ops := rewrite -multE -plusE -!(rwP leP).
Ltac somega := repeat normH; elim_ops; intros; omega.

Lemma measure_card (G' G : graph2) : 
  #|edge G'| < #|edge G| -> measure G' < measure G.
Proof. 
  rewrite /term_of_measure. 
  do 2 case: (g_in == g_out) => /=; somega.
Qed.

Lemma measure_io (G' G : graph2) : 
  (g_in == g_out :> G) -> (g_in != g_out :> G') -> #|edge G'| <= #|edge G| -> 
  measure G' < measure G.
Proof. 
  rewrite /term_of_measure. 
  do 2 case: (g_in == g_out) => //=; somega.
Qed.

(** ** Subroutines *)

(** Splitting intro parallel components *)

Fact split_proof1 (T : finType) (A : {set T}) x y : x \in A :|: [set x; y].
Proof. by rewrite !inE eqxx ?orbT. Qed.

Fact split_proof2 (T : finType) (A : {set T}) x y : y \in A :|: [set x; y].
Proof. by rewrite !inE eqxx ?orbT. Qed.


(** The graph induced by "{i,o} ∪ H" 
    (with H being a component of "G\{i,o}" and G a lens *)

Definition parcomp (G : graph2) (A : {set G}) := 
  @point (induced (A :|: [set g_in; g_out]))
         (Sub g_in (split_proof1 A g_in g_out))
         (Sub g_in (split_proof1 A g_in g_out)).

Definition lens (G : graph2) := 
  [&& #|edge (@pgraph G [set g_in;g_out] g_in )| == 0,
      #|edge (@pgraph G [set g_in;g_out] g_out)| == 0&
      @sgraph.link_rel (skeleton G) g_in g_out].
(** alternative condition on i/o: [petal [set g_in;g_out] g_in  = [set g_in]] *)


(** NOTE: This only does the right thing if 
    - G is connected
    - there is no direct edge between i and o
    - i != o and no (nontrivial) petals on i and o
    - TOTHINK: Can we use the same construction for i=0 
      (i.e., using H := ~: [set g_in;g_out])  *)
Definition split_par (G : graph2) : seq graph2 := 
  let H := @sinterval (skeleton G) g_in g_out in 
  let P := equivalence_partition (connect (restrict (mem H) (@sedge (skeleton G)))) H in 
  [seq parcomp A | A <- enum P].

Definition edges (G : graph) (x y : G) := 
  [set e : edge G | (source e == x) && (target e == y)].

(* alternative: [exists e, e \in edges x y] || [exists e \in edges y x] *)
Definition adjacent (G : graph) (x y : G) := 
  0 < #|edges x y :|: edges y x|.

Lemma adjacentE (G : graph) (x y : skeleton G) : 
  (x != y) && adjacent x y = x -- y.
Proof.
  apply/andP/orP. 
  - move => /= [Hxy]. 
Admitted.

Lemma split_iso (G : graph2) :
  lens G -> ~~ @adjacent G g_in g_out -> 
  \big[par2/top2]_(H <- split_par G) H ≈ G.
Admitted.

Lemma split_inhab (G : graph2) : 0 < size (split_par G).
Abort.
(* Proof. *)
(*   rewrite /split_par. case: ifP => //. *)
(*   move/negbT. by rewrite -ltnNge size_map -cardE => /ltnW.  *)
(* Qed. *)

(* WARN: we do not have decidable equality on graphs, this might
become problematic? *)
Lemma split_nontrivial (G H : graph2) : 
  connected [set: skeleton G] -> lens G -> ~~ @adjacent G g_in g_out -> 
  List.In H (split_par G) -> 0 < #|edge H|.
Admitted.

Lemma split_subgraph (G H : graph2) : 
  List.In H (split_par G) -> subgraph H G.
Admitted.

Lemma split_connected (G H : graph2) :
  lens G -> 
  List.In H (split_par G) -> connected [set: skeleton H].
Admitted.

Lemma split_K4_free (G H : graph2) :
  lens G -> K4_free (sskeleton G) ->
  List.In H (split_par G) -> K4_free (sskeleton H).
Admitted.

Lemma split_edges (G : graph2) : 
  lens G -> ~~ @adjacent G g_in g_out -> 
  \sum_(H <- split_par G) #|edge H| = #|edge G|.
Admitted.

(* TOTHINK: What is the most natural formulation of "has at least two components"? *)

Lemma CP2_part (G : sgraph) x y x' y' : 
  [set x; y] \subset cp x' y' -> 
  let U := [set x'; y'] in 
  pe_partition [set petal U x; petal U y; sinterval x y] [set: G].
Proof.
  rewrite subUset !sub1set => /andP[A B]. 
Admitted.
(** TOTHINK: 
    Does the lemma above have a direct proof without going through Prop. 20?
    Is this really the formulation needed for Prop 21(i)?
    What is the right formulation for the edges? *)


(** Proposition 21(i) *)
(** TOTHINK: [[set val x | x in U] = neighbours i] corresponds to what
    is written in the paper. Is there a better way to phrase this? *)
Lemma CP_tree (H : sgraph) (i : H) (U : {set sgraph.induced [set~ i] }) :
  K4_free H -> [set val x | x in U] = neighbours i :> {set H} ->
  is_tree (CP_ U).
Admitted.


Lemma ssplit_K4_nontrivial (G : sgraph) (i o : G) : 
  ~~ i -- o -> sgraph.link_rel G i o -> K4_free (add_edge i o) -> 
  connected [set: G] -> ~ connected (sinterval i o).
Proof.
  move => /= io1 /andP [io2 io3] K4F conn_G. 
  pose G' := @sgraph.induced (add_edge i o) [set~ i].
  set H := add_edge i o in K4F *.
  set U := o |: neighbours i.
  have Ho : o \in [set~ i]. admit.
  pose o' : G' := Sub o Ho.
  set U' : {set G'} := [set insubd o' x | x in U].
  have tree_CPU' : is_tree (CP_ U').
  { apply: CP_tree K4F _. admit. }
  have o'_in_U' : o' \in CP U'. 
  { admit. }
  pose N := @neighbours (CP_ U') (Sub o' o'_in_U').
  have Ngt1: 1 < #|N|.
  { suff: 0 < #|N| /\ #|N| != 1. admit.
    split.
    - admit.
    - apply/negP. case/cards1P => z E. 
      (* need that the unique oi-path in CP(U) passes through {z}. Hence, z is a checkpoint *)
      admit.
  }
  case/card_gt1P : Ngt1 => x [y] [Nx Ny xy]. 
  (* TOTHINK: can we avoid nested vals using a proper lemma? *)
  apply/connected2. exists (val (val x)). exists (val (val y)). split.
  - admit. (* whats the argument that the neighbours are in ]]i;o[[ *)
  - admit.
  - admit. (* argue that o, which is not in ]]i;o[[, is a checkpoint beween x an y *)
Admitted.

(** This is one fundamental property underlying the term extraction *)
Lemma split_K4_nontrivial (G : graph2) : 
  g_in != g_out :> G -> lens G -> ~~ @adjacent G g_in g_out -> K4_free (sskeleton G) -> 
  connected [set: skeleton G] -> 
  1 < size (split_par G).
Proof.
  move => A B C D E. rewrite /split_par size_map -cardE. apply/equivalence_partition_gt1P. 
  - move => x y z _ _ _.  exact: (sedge_equiv (G := skeleton G)).
  - set H := sinterval _ _. apply/(@connected2 (skeleton G)). 
    apply: ssplit_K4_nontrivial => //. 
    + by rewrite -adjacentE A.
    + by case/and3P : B. 
Qed.


(* TOTHINK: do we need [split_par] to be maximal, i.e., such that the
parts do not have non-trivial splits *)

Fixpoint pairs (T : Type) (x : T) (s : seq T) := 
  if s is y::s' then (x,y) :: pairs y s' else nil.

(** list of checkpoint bewteen x and y (excluding x) *)
(* NOTE: see insub in eqtype.v *)
Definition checkpoint_seq (G : graph) (x y : G) := 
  if @idP (connect (@sedge (skeleton G)) x y) isn't ReflectT con_xy then [::]
  else sort (cpo con_xy) (enum (@cp (skeleton G) x y)).

Notation IO := ([set g_in; g_out]).

Definition check_point_term (t : graph2 -> term) (G : graph2) (x y : G) :=
  let c := checkpoint_seq x y in
  tmS (t (pgraph IO x)) 
      (\big[tmS/tm1]_(p <- pairs x c) tmS (t(igraph p.1 p.2)) (t(pgraph IO p.2))).

Definition check_point_wf (F1 F2 : graph2 -> term) (G : graph2) (x y : G) : 
  g_in != g_out :> G ->
  ~~ lens G -> 
  (forall H : graph2, connected [set: skeleton H] /\ K4_free (sskeleton H) -> 
        measure H < measure G -> F1 H = F2 H) -> 
  check_point_term F1 x y = check_point_term F2 x y.
Admitted.

(* NOTE: we assume the input to be connected *)
Definition term_of_rec (term_of : graph2 -> term) (G : graph2) := 
  if g_in == g_out :> G
  then (* input equals output *)
    let E := [set e : edge G | (source e == g_in) && (target e == g_in)] in
    if 0 < #|E| 
    then (* there are self loops) *)
      tmI (\big[tmI/tmT]_(e in E) tmA (label e)) 
          (term_of (remove_edges E))
    else (* only proper petals *)
      (* split into parallel components/petals *)
      let H := split_par G in
      if H isn't [:: H0]       
      then \big[tmI/tm1]_(G' <- H) term_of G' (* use tmT or tmI as identity? *)
      else if pick [pred x | @sedge (skeleton H0) g_in x] is Some x
           then dom (term_of (point g_in x)) (* have H0 ≈ G? G0 = G *)
           else tm1 
  else (* distinct input and output *)
    if lens G
    then (* no checkpoints and no petals on i and o *)
      if @adjacent G g_in g_out 
      then (* i and o are adjacent an we can remove some direct edges *)
        tmI (tmI (\big[tmI/tmT]_(e in @edges G g_in g_out) tmA (label e))
                 (\big[tmI/tmT]_(e in @edges G g_out g_in) tmC (tmA (label e))))
            (* FIXME: this graph could be g(tmT) *)
            (term_of (remove_edges (@edges G g_in g_out :|: edges g_out g_in)))
      else (* i and o not adjacent - no progress unless G is K4-free *)
        \big[tmI/tmT]_(H <- split_par G) term_of H
    else (* at least one nontrivial petal or checkpoint *)
      @check_point_term term_of G g_in g_out
.



Definition term_of := Fix tmT term_of_measure term_of_rec.

Lemma term_of_eq (G : graph2) : 
  connected [set: skeleton G] -> K4_free (sskeleton G) ->
  term_of G = term_of_rec term_of G.
Proof.
  move => con_G free_G. 
  pose P (H:graph2) := connected [set: skeleton H] /\ K4_free (sskeleton H).
  apply: (Fix_eq P) => // {con_G free_G G} f g G [con_G free_G] Efg.
  rewrite /term_of_rec. 
  case: (boolP (@g_in G == g_out)) => Hio.
  - (* input equals output *)
    case: (posnP #|[set e | source e == g_in & target e == g_in]|) => E.
    + admit.
    + rewrite Efg // /P; first split.
      ** admit. (*need: removing self loops does not change skeletons - does this force up to ISO? *)
      ** admit.
      ** apply: measure_card. by rewrite card_sig cardsI cardsCT.
  - case: (boolP (lens G)) => [deg_G|ndeg_G].
    + case: (boolP (adjacent g_in g_out)) => adj_io.
      * congr tmI. admit. 
      * apply: eq_big_seq_In => H in_parG. apply: Efg.
        + split. 
          * exact: split_connected in_parG.
          * exact: split_K4_free in_parG.
          * apply: measure_card. rewrite -[X in _ < X]split_edges //.
            apply: sum_gt0 => // [{H in_parG} H|].
            -- exact: split_nontrivial.
            -- exact: split_K4_nontrivial.
    + exact: check_point_wf.
Admitted.

Theorem term_of_iso (G : graph2) : 
  connected [set: skeleton G] ->  
  K4_free (sskeleton G) -> 
  iso2 G (graph_of_term (term_of G)).
Proof.
Admitted.
