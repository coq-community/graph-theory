Require Import Omega Lia.

From mathcomp Require Import all_ssreflect.

Require Import edone finite_quotient preliminaries sgraph minor checkpoint. 
Require Import multigraph subalgebra skeleton bounded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs". 

Definition dom t := tmI (tmS t tmT) tm1.

(* TODO: resolve this name clash *)
Local Notation link_rel := checkpoint.link_rel.

(** Preliminaries *)

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
  Admitted.

  Lemma add_node_irrefl : irreflexive add_node_rel.
  Admitted.

  Definition add_node := SGraph add_node_sym add_node_irrefl.
End AddNode.
Arguments add_node : clear implicits.

Lemma sg_edgeNeq (G : sgraph) (x y : G) : x -- y -> (x == y = false).
Proof. apply: contraTF => /eqP ->. by rewrite sg_irrefl. Qed.

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

(* TOTHINK: is this the best way to transfer path from induced subgraphs *)
Lemma induced_path (G : sgraph) (S : {set G}) (x y : sgraph.induced S) (p : Path x y) : 
  @spath G (val x) (val y) (map val (val p)).
Proof.
  case: p => p pth_p /=. elim: p x pth_p => /= [|z p IH] x pth_p.
  - by rewrite (spath_nil pth_p) spathxx.
  - rewrite !spath_cons in pth_p *. 
    case/andP : pth_p => p1 p2. apply/andP; split => //. exact: IH.
Qed.

Lemma ins (T : finType) (A : pred T) x : x \in A -> x \in [set z in A].
Proof. by rewrite inE. Qed.
  


Lemma connected2 (G : sgraph) (D : {set G}) : 
  (~ connected D) <-> exists x y, [/\ x \in D, y \in D & ~~ connect (restrict (mem D) sedge) x y].
Admitted.

Definition neighbours (G : sgraph) (x : G) := [set y | x -- y].

(** Additional Checkpoint Properties *)



Section Checkpoints.
Variables (G : sgraph).

Hypothesis (conn_G : forall x y :G, connect sedge x y).

Lemma edgeNeq (x y : G) : x -- y -> x != y.
Proof. apply: contraTN => /eqP->. by rewrite sgP. Qed.

Lemma linkNeq (x y : link_graph G) : x -- y -> x != y.
Proof. apply: contraTN => /eqP->. by rewrite sgP. Qed.


Lemma link_cpN (x y z : G) : 
  (x : link_graph G) -- y -> z != x -> z != y -> z \notin cp x y.
Proof.
  move => /= /andP [_ A] B C. 
  apply/negP. move/(subsetP A). by rewrite !inE (negbTE B) (negbTE C).
Qed.



Lemma eq_disjoint (T : finType) (A A' B : pred T) :
  A =i A' -> [disjoint A & B] = [disjoint A' & B].
Proof. Admitted.
Arguments eq_disjoint [T A] A' [B].

Lemma idx_end (x y : G) (p : Path x y) z : 
  irred p -> z \in p -> idx p z <= idx p y.
Proof.
  case: p => p pth_p. rewrite /idx /irred in_collective nodesE SubK.
  elim: p x pth_p  => [|a p IH] x.
  - rewrite inE. by move/spath_nil => -> _ /eqP->.
  - admit.
Admitted.
  

Arguments Path G x y : clear implicits.

(* TOTHINK/TODO: Lemmas about [disjoint] should be as below, to avoid exposing
conversions to collective predicates when rewriting *)
Lemma disjoint_sym' (T : finType) (A B : mem_pred T) : 
  disjoint A B = disjoint B A.
Admitted.

Lemma C3_of_triangle (x y z : link_graph G) : 
  x -- y -> y -- z -> z -- x -> exists2 phi : G -> option C3, 
  minor_map phi & [/\ phi x = Some ord0, phi y = Some ord1 & phi z = Some ord2].
Proof.
  move => xy yz zx.
  have/cpPn' [p irr_p av_z] : (z:G) \notin @cp G x y. 
  { apply: link_cpN => //; apply: linkNeq => //. by rewrite sg_sym. }
  have/cpPn' [q irr_q av_x] : (x:G) \notin @cp G z y.
  { apply: link_cpN => //; first (by rewrite sg_sym) ;apply: linkNeq => //. 
    by rewrite sg_sym. }
  have [Yq Yp] : y \in q /\ y \in p by split;apply: nodes_end.
  case: (split_at_first (G := G) (A := mem p) Yp Yq) => n1 [q1] [q2] [def_q Q1 Q2]. 
  have Hn : n1 != x.
  { apply: contraNN av_x => /eqP<-. by rewrite def_q mem_pcat nodes_end. }
  have {q irr_q av_x Yq def_q q2 Yp} irr_q1 : irred q1.
  { move:irr_q. rewrite def_q irred_cat. by case/and3P. }
  have/cpPn' [q irr_q av_n1] : n1 \notin @cp G z x. 
  { apply link_cpN => //. apply: contraNN av_z => /eqP?. by subst n1. }
  have [Xq Xp] : x \in q /\ x \in p by split; rewrite /= ?nodes_end ?nodes_start. 
  case: (split_at_first (G := G) (A := mem p) Xp Xq) => n2 [q2] [q2'] [def_q Q3 Q4].
  have N : n1 != n2. 
  { apply: contraNN av_n1 => /eqP->. by rewrite def_q mem_pcat nodes_end. }
  have {q irr_q av_n1 Xp Xq q2' def_q} irr_q2 : irred q2.
  { move:irr_q. rewrite def_q irred_cat. by case/and3P. }
  wlog before: n1 n2 q1 q2 irr_q1 irr_q2 Q1 Q2 Q3 Q4 N {Hn} / idx p n1 < idx p n2. 
  { move => W. 
    case: (ltngtP (idx p n1) (idx p n2)) => H.
    - by apply: (W n1 n2 q1 q2).
    - apply: (W n2 n1 q2 q1) => //. by rewrite eq_sym.
    - case:notF. apply: contraNT N => _. apply/eqP. exact: idx_inj H. }
  case: (splitR q1 _) => [|z1 [q1' [zn1 def_q1]]].
  { by apply: contraNN av_z => /eqP->. }
  case: (splitR q2 _) => [|z2 [q2' [zn2 def_q2]]].
  { by apply: contraNN av_z => /eqP->. }
  gen have D,D1 : z1 n1 q1 q1' zn1 irr_q1 def_q1  Q2 {Q1 N before} / 
     [disjoint p & q1'].
  { have A : n1 \notin q1'. 
    { move: irr_q1. rewrite def_q1 irred_cat /= => /and3P[_ _ A].
      by rewrite (disjointFl A _). }
    rewrite disjoint_subset; apply/subsetP => z' Hz'. rewrite !inE.
    apply: contraNN A => A. 
    by rewrite -[n1](Q2 _ Hz' _) // def_q1 mem_pcat A. }
  have {D} D2 : [disjoint p & q2'] by apply: (D z2 n2 q2 q2' zn2).
  case/(isplitP irr_p) def_p : p / Q1 => [p1 p2 _ irr_p2 D3].
  have N2 : n2 \in tail p2. { subst p. by rewrite -idxR in before. }
  have N1 : n1 != y. 
  { apply: contraTN before => /eqP->. by rewrite -leqNgt idx_end. }
  case: (splitL p2 N1) => n1' [n_edge] [p2'] [def_p2 tail_p2].
  have N2' : n2 \in p2' by rewrite tail_p2.
  
  pose pz := pcat (prev q1') q2'.
  pose phi u : option C3 := 
         if u \in p1  then Some ord0
    else if u \in p2' then Some ord1
    else if u \in pz  then Some ord2
                    else None.
  have D_aux : [disjoint p & pz].
  { (* ugly: exposes in_nodes *)
    rewrite ![[disjoint p & _]]disjoint_sym' in D1 D2 *. 
    rewrite (eq_disjoint [predU q1' & q2']) ?disjointU ?D1 //.
    move => u. by rewrite !inE mem_pcat mem_prev. }
  have {D_aux} D : [disjoint3 p1 & p2' & pz].
  { subst p; apply/and3P. split.
    - apply: disjoint_transR D3. apply/subsetP => u. by rewrite tail_p2. 
    - apply: disjoint_transL D_aux. apply/subsetP => u. 
      by rewrite mem_pcatT tail_p2 => ->.
    - rewrite disjoint_sym. apply: disjoint_transL D_aux. apply/subsetP => u. 
      by rewrite mem_pcat => ->. }
  (* clean up assumptions that are no longer needed *)
  move => {Q2 Q3 Q4 av_z irr_p before D2 D1 D3 irr_q1 irr_q2 xy yz zx}.
  move => {def_q1 def_q2 N1 N2 def_p2 tail_p2 p def_p N q1 q2}.

  have [Px Py Pz] : [/\ x \in p1, y \in p2' & z \in pz]. 
  { by rewrite /= mem_pcat ?nodes_start ?nodes_end. }
  have phi_x : phi x = Some ord0. 
  { rewrite /phi. by case: (disjoint3P x D) Px. }
  have phi_y : phi y = Some ord1. 
  { rewrite /phi. by case: (disjoint3P y D) Py. }
  have phi_z : phi z = Some ord2. 
  { rewrite /phi. by case: (disjoint3P z D) Pz. }
  exists phi => //. split. 
    + case. move => [|[|[|//]]] Hc; [exists x|exists y|exists z]; 
        rewrite ?phi_x ?phi_y ?phi_z;exact/eqP.
    + move => c u v. rewrite !inE => /eqP E1 /eqP E2; move: E1 E2. 
      rewrite {1 2}/phi. 
      case: (disjoint3P u D) => [Hu|Hu|Hu|? ? ?];
      case: (disjoint3P v D) => [Hv|Hv|Hv|? ? ?] // <- // _.      
      * move: (connected_path (p := p1) (ins Hu) (ins Hv)).
        apply: connect_mono. apply: restrict_mono => {u v Hu Hv} u.
        rewrite !inE /phi. by case: (disjoint3P u D).
      * move: (connected_path (p := p2') (ins Hu) (ins Hv)).
        apply: connect_mono. apply: restrict_mono => {u v Hu Hv} u.
        rewrite !inE /phi. by case: (disjoint3P u D).
      * move: (connected_path (p := pz) (ins Hu) (ins Hv)).
        apply: connect_mono. apply: restrict_mono => {u v Hu Hv} u.
        rewrite !inE /phi. by case: (disjoint3P u D).
    + move => c1 c2.
      wlog: c1 c2 / c1 < c2.
      { move => W. case: (ltngtP c1 c2) => [|A B|A B]; first exact: W.
        - case: (W _ _ A _) => [|y0 [x0] [? ? ?]]; first by rewrite sgP. 
          exists x0; exists y0. by rewrite sgP.
        - case/ord_inj : A => ?. subst. by rewrite sgP in B. }
      case: c1 => [[|[|[|//]]]]; case: c2 => [[|[|[|//]]]] //= Hc2 Hc1 _ _. 
      * exists n1. exists n1'. rewrite !inE n_edge. split => //.
        -- rewrite /phi. by case: (disjoint3P n1 D) (nodes_end p1). 
        -- rewrite /phi. by case: (disjoint3P n1' D) (nodes_start p2'). 
      * exists n1. exists z1. rewrite !inE sg_sym zn1. split => //.
        -- rewrite /phi. by case: (disjoint3P n1 D) (nodes_end p1). 
        -- rewrite /phi. by case: (disjoint3P z1 D) (nodes_start pz). 
      * exists n2. exists z2. rewrite !inE sg_sym zn2. split => //.
        -- rewrite /phi. by case: (disjoint3P n2 D) N2'.
        -- rewrite /phi. by case: (disjoint3P z2 D) (nodes_end pz). 
Qed.

Lemma sinterval_sym (x y : G) : sinterval x y = sinterval y x.
Proof. apply/setP => p. by rewrite !inE orbC [_ _ _ _ && _ _ _ _]andbC. Qed.

Lemma CP_connected (U : {set G}) : connected [set: CP_ U].
Admitted.


Lemma srestrict_sym A : connect_sym (restrict A (@sedge G)).
Admitted.

Lemma connected_petal x (U : {set G}) : x \in CP U -> connected (petal U x).
Proof.
  move => cp_x.
  suff S z : z \in petal U x -> connect (restrict (mem (petal U x)) sedge) x z.
  { move => u v Hu Hv. apply: connect_trans (S _ Hv). admit. }
  move/petalP => Hz. case/uPathP : (conn_G z x) => p irr_p. 
  have sP : p \subset petal U x.
  { apply/negPn/negP. move/subsetPn => [z' in_p N]. 
    case/petalPn : (N) => y cp_y. case/cpPn' => q irr_q av_x. 
    (* split p at z' (which is different from x) and obtain x-avoiding zy-path *)
    admit. }
  rewrite srestrict_sym. apply: (connectRI (p := p)). 
  (* trivial *) admit.
Admitted.


Lemma connectedU (S1 S2 : {set G}) x : x \in S1 :&: S2 -> connected (S1 :|: S2).
Admitted.




(** Do we really need the follwing lemma in its full generality *)
Lemma ncp_sinterval U (x y p : G) :
  [set x;y] \subset CP U ->
  link_rel G x y -> 
  (p \in sinterval x y) = (ncp U p == [set x; y]).
Proof.
Abort.
  
Lemma link_part (x y : G) : link_rel G x y ->
  pe_partition [set petal [set x; y] x; petal [set x; y] y; sinterval x y] [set: G].
Proof.
  move => /= /andP [xy cp_xy]. 
  have CPxy : CP [set x; y] = [set x; y].
  { apply: CP_clique. exact: clique2. }
  apply/andP; split.
  - rewrite eqEsubset subsetT /=. apply/subsetP => p _. 
    pose N := ncp [set x; y] p. 
    have: N \subset [set x; y]. by rewrite /N /ncp -lock setIdE CPxy subsetIl.
    rewrite subset2 // {1}/N (ncp0 conn_G x) ?in_setU ?set11 //=. case/or3P. 
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

Lemma link_cpL (x y u v : G) : link_rel G x y -> 
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

Lemma link_cpR (x y u v : G) : link_rel G x y -> 
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


Lemma link_path_cp (x y : G) (p : Path (link_graph G) x y) : 
  {subset cp x y <= p}.
Proof. 
  apply/subsetP. rewrite /in_nodes nodesE. apply: link_seq_cp.
  exact: (valP p). 
Qed.

Lemma CP_path_cp (U : {set G}) (x y : CP_ U) (p : Path _ x y) z : 
  val z \in @cp G (val x) (val y) -> z \in p.
Proof. 
  move/link_path_cp. 
  suff P : @spath (link_graph G) (val x) (val y) (map val (val p)).
  { move/(_ (Build_Path P)). 
    (* TOTHINK: Why do we need in_collective BEFORE mem_path??? *)
    rewrite !in_collective !mem_path -map_cons mem_map //. exact: val_inj. }
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

Lemma petal_dist (U : {set G}) x y : 
  x \in CP U -> y \in CP U -> x != y -> petal U x != petal U y.
Admitted. (* follows from disjointness *)

Lemma sintervalEl (x y : G) u : 
  u \in sinterval x y -> exists2 p : Path G u x, irred p & y \notin p.
Admitted. (* essentially the definition *)

Lemma ncp_anti (U U' : {set G}) x : 
  U \subset U' -> ncp U' x \subset ncp U x.
Admitted.

(* Lemma pe_partD1 (T : finType) (A D : {set T}) P :   *)
(*   pe_partition (A |: P) D = pe_partition P (D :\: A). *)
(* Admitted. *)

(* Lemma pe_partIr (T : finType) (A A' B B' D : {set T}) :  *)
(*   pe_partition [set A; B] D -> pe_partition [set A' ; B'] D ->  *)
(*   pe_partition [set A; A'; B :&: B'] D. *)
(* Admitted. *)

(* Lemma pe_part_fuse (T : finType) (A B B' C C' D : {set T}) :  *)
(*   pe_partition [set A; B ; C] D ->  *)
(*   pe_partition [set A; B' ; C'] D ->  *)
(*   [disjoint B & B'] -> *)
(*   pe_partition [set A; B; B'; C :&: C'] D. *)
(* Admitted. *)
  

(* TOTHINK: this should not be necessary, if the decomposition in
[CP_tree] is defined differently *)
(* Lemma triangle_partition (x y z : link_graph G) : *)
(*   x -- y -> y -- z -> z -- x ->  *)
(*   let U : {set G} := [set x;y;z] in  *)
(*   pe_partition [set petal U x; petal U y; petal U z;  *)
(*                 @sinterval G x y :&: @sinterval G x z ] [set: G]. *)
(* Proof. *)
(*   move => xy yz zx /=. set U : {set G} := [set x; y; z]. *)
(*   move: (link_part xy) => Pxy.  *)
(*   rewrite sg_sym in zx. move: (link_part zx) => Pxz.  *)
(*   have E1: @petal G [set x; y] x = petal U x. { admit. } *)
(*   have E2: @petal G [set x; y] y = petal U y. { admit. } *)
(*   have E3: @petal G [set x; z] x = petal U x. { admit. } *)
(*   have E4: @petal G [set x; z] z = petal U z. { admit. } *)
(*   rewrite E1 E2 E3 E4 in Pxy Pxz. apply: pe_part_fuse => //.  *)
(*   apply: petal_disj => // ; last by rewrite (sg_edgeNeq yz). *)
(*   - by apply: CP_extensive; rewrite !inE eqxx. *)
(*   - by apply: CP_extensive; rewrite !inE eqxx. *)
(* Admitted. *)

End Checkpoints.


CoInductive sg_iso (G H : sgraph) : Prop := 
  SgIso (h : G -> H) (g : H -> G) : cancel g h -> cancel h g -> 
    {homo h : x y / x -- y} -> {homo h : x y / x -- y} -> sg_iso G H.
  

Lemma minor_with (H G': sgraph) (S : {set H}) (i : H) (N : {set G'})
  (phi : (sgraph.induced S) -> option G') : 
  i \notin S -> 
  (forall y, y \in N -> exists2 x , x \in phi @^-1 (Some y) & val x -- i) ->
  @minor_map (sgraph.induced S) G' phi -> 
  minor H (add_node G' N).
Proof.
  move => Hi Hphi mm_phi.
  pose psi (u:H) : option (add_node G' N) := 
    match @idP (u \in S) with 
    | ReflectT p => obind (fun x => Some (Some x)) (phi (Sub u p))
    | ReflectF _ => if u == i then Some None else None
    end.
  (* NOTE: use (* case: {-}_ / idP *) to analyze psi *)
  have psi_G' (a : G') : psi @^-1 (Some (Some a)) = val @: (phi @^-1 (Some a)).
  { admit. }
  have psi_None : psi @^-1 (Some None) = [set i].
  { apply/setP => z. rewrite !inE /psi. 
    case: {-}_ / idP => [p|_]; last by case: (z == i).
    have: z != i. admit. case: (phi _) => [b|] /=; admit. }     
  case: mm_phi => M1 M2 M3. exists psi;split.
  - case. 
    + admit.
    + exists i. rewrite /psi. move: Hi. 
      case: {-}_ / idP => [? ?|_ _]; by [contrab|rewrite eqxx].
  - case. 
    + move => y. move: (M2 y). rewrite psi_G'. admit.
    + rewrite psi_None. (* singletons are connected *) admit.
  - move => [a|] [b|]; last by rewrite sg_irrefl.
    + move => /= /M3 [x0] [y0] [? ? ?]. exists (val x0). exists (val y0). by rewrite !psi_G' !mem_imset.
    + move => /= /Hphi [x0] ? ?. exists (val x0); exists i. by rewrite psi_None set11 !psi_G' !mem_imset.
    + admit. (* symmetric *)
Admitted.

Lemma K4_of_triangle (G:sgraph) (G_conn : forall x y:G, connect sedge x y) (x y z : link_graph G) : 
  x -- y -> y -- z -> z -- x -> minor (add_node G [set x;y;z]) K4.
Proof.
  move => xy yz zx. case: (C3_of_triangle G_conn xy yz zx) => phi mm_phi [phi_x phi_y phi_z].
  pose psi u : option K4 := 
    if u isn't Some u' then Some ord3 
    else obind (fun n => Some (widen_ord (isT : 3 <= 4) n)) (phi u').
  exists psi.
  split.
  - case. move => [|[|[|[|?]]]] // Hn.
    + exists (Some x). rewrite /psi phi_x /=. congr Some. exact: val_inj.
    + exists (Some y). rewrite /psi phi_y /=. congr Some. exact: val_inj.
    + exists (Some z). rewrite /psi phi_z /=. congr Some. exact: val_inj. 
    + exists None. rewrite /psi. congr Some. exact: val_inj.
  - admit.
  - admit.
    
Admitted.




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
      @link_rel (skeleton G) g_in g_out].
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
  let U := [set x; y] in 
  pe_partition [set petal U x; petal U y; sinterval x y] [set: G].
Proof.
  rewrite subUset !sub1set => /andP[A B]. 
Admitted.
(** TOTHINK: 
    Does the lemma above have a direct proof without going through Prop. 20?
    Is this really the formulation needed for Prop 21(i)?
    What is the right formulation for the edges? *)


Notation val2 x := (val (val x)).
Arguments cp : clear implicits.
Arguments Path : clear implicits.

(* Lemma Sub_eq (T : eqType) (P : pred T) (x y : T) (Px : x \in P) (Py : y \in P) : *)
(*   Sub (s := sig_subType P) x Px == Sub y Py = (x == y). *)
(* Proof. reflexivity. Qed. *)




Lemma Some_eqE (T : eqType) (x y : T) : 
  (Some x == Some y) = (x == y).
Proof. by apply/eqP/eqP => [[//]|->]. Qed.


Section Petals.
Variables (G : sgraph) (G_conn : forall x y : G, connect sedge x y).

Lemma petal_in_out (U : {set G}) x u v (p : Path G u v) :
  x \in CP U -> u \in x |: ~: petal U x -> v \in x |: ~: petal U x -> irred p -> 
  p \subset x |: ~: petal U x.
Proof.
  move => Ux Pu Pv. apply: contraTT => /subsetPn [w]. 
  rewrite !inE negb_or negbK => in_p /andP [W1 W2]. 
  case/Path_split : in_p => w1 [w2] def_p. subst. 
  rewrite irred_cat !negb_and (disjointNI (x := x)) //.
  + apply/cpP'. rewrite cp_sym. exact: petal_exit' Pu.
  + suff: x \in prev w2 by rewrite mem_prev mem_path inE eq_sym (negbTE W1). 
    apply/cpP'. rewrite cp_sym. exact: petal_exit' Pv.
Qed.

(* This is a bit bespoke, as it only only mentions petals rooted at
elements of [U] rather than [CP U]. At the point where we use it, U is
a clique, so [CP U] is [U]. *)
Lemma petals_in_out (U : {set G}) u v (p : Path G u v) :
  let T' := U :|: (~: \bigcup_(z in U) petal U z) in 
  u \in T' -> v \in T' -> irred p -> {subset p <= T'}.
Proof.
  (* Should follow with [petal_in_out] *)
Admitted.

End Petals.

Lemma bigcup_set1 (T I : finType) (i0 : I) (F : I -> {set T}) :
  \bigcup_(i in [set i0]) F i = F i0.
Proof. by rewrite -big_filter filter_index_enum enum_set1 big_seq1. Qed.

Lemma mem_preim (aT rT : finType) (f : aT -> rT) x y : 
  (f x == y) = (x \in f @^-1 y).
Proof. by rewrite !inE. Qed.

(** TOTHINK: this is a bit bespoke, in particular [@clique (link_graph
G) U] is stronger than necessary *)
Lemma collapse_petals (G : sgraph) (U : {set G}) u0' (inU : u0' \in U) :
  @clique (link_graph G) U -> 
  let T := U :|: ~: \bigcup_(x in U) petal U x in 
  let G' := sgraph.induced T in 
  exists phi : G -> G',
    [/\ strict_minor_map phi, 
     (forall u : G', val u \in T :\: U -> phi @^-1 u = [set val u]) &
     (forall u : G', val u \in U -> phi @^-1 u = petal U (val u))].
Proof.
  move => clique_U T G'. 
  have inT0 : u0' \in T by rewrite !inE inU.
  pose u0 : G' := Sub u0' inT0.  
  pose phi u := if [pick x in U | u \in petal U x] is Some x 
                then insubd u0 x else insubd u0 u.
  exists phi.
  have phiU (u : G') : val u \in U -> phi @^-1 u = petal U (val u).
  { admit. }
  have phiT (u : G') : val u \in T :\: U -> phi @^-1 u = [set val u].
  { admit. }
  split => //.
  - split. 
    + move => y. case: (boolP (val y \in U)) => x_inU. 
      * exists (val y). apply/eqP. by rewrite mem_preim phiU // petal_id. 
      * exists (val y). apply/eqP. rewrite mem_preim phiT inE // x_inU. exact: valP.
Admitted.     
Arguments collapse_petals [G] U u0' _.

(** Proposition 21(i) *)
(** TOTHINK: [[set val x | x in U] = neighbours i] corresponds to what
    is written in the paper. Is there a better way to phrase this? *)
Lemma CP_tree (H : sgraph) (i : H) (U : {set sgraph.induced [set~ i] }) :
  (forall x y : sgraph.induced [set~ i], connect sedge x y) -> 
  K4_free H -> [set val x | x in U] = neighbours i :> {set H} ->
  is_tree (CP_ U).
Proof.
  set G := sgraph.induced _ in U *.
  move => G_conn H_K4_free UisN. 
  suff: ~ exists x y z : CP_ U, [/\ x -- y, y -- z & z -- x] by apply CP_treeI.
  move => [x] [y] [z] [xy yz zx]. apply: H_K4_free. 
  move: (CP_triangle_petals G_conn xy yz zx) => 
    [x'] [y'] [z'] [[x_inU y_inU z_inU] [xX' yY' zZ']].
  set U3 : {set G} := [set val x; val y; val z] in xX' yY' zZ'. 
  pose X := petal U3 (val x). 
  pose Y := petal U3 (val y).
  pose Z := petal U3 (val z).
  have xX : val x \in X by apply: (@petal_id G).  
  have yY : val y \in Y by apply: (@petal_id G).
  have zZ : val z \in Z by apply: (@petal_id G).
  move def_T: (~: (X :|: Y :|: Z)) => T.
  (* do we acttually want to packaging as partition property ??? *)
  (* have part1 : pe_partition [set T; X; Y; Z] [set: G]. *)
  (* { admit. } *)
  
  pose T' : {set G} := U3 :|: T.
  pose G' := @sgraph.induced G T'.
  
  have xH' : val x \in T' by rewrite !inE eqxx. 
  have yH' : val y \in T' by rewrite !inE eqxx. 
  have zH' : val z \in T' by rewrite !inE eqxx. 

  have def_T' : T' = U3 :|: ~: (\bigcup_(v in U3) petal U3 v).
  { by rewrite {2}/U3 !bigcup_setU !bigcup_set1 /T' -def_T. }

  have clique_xyz : @clique (link_graph G) U3.
  { move => u v. rewrite !inE -!orbA. 
    do 2 (case/or3P => /eqP->); by rewrite ?eqxx // sg_sym. }
  case: (collapse_petals U3 (val x) _ clique_xyz); first by rewrite !inE eqxx.
  rewrite -def_T' -/G' => phi [mm_phi P1 P2].

  have irred_inT u v (p : Path G u v) : 
      u \in T' -> v \in T' -> irred p -> {subset p <= T'}.
  { rewrite def_T'. exact: petals_in_out. }
  (* 
  { move => Hu Hv irr_p. apply/subsetP. 
    have Px : p \subset val x |: ~: X. 
    { apply: petal_in_out => //. 
      - apply: CP_extensive. by rewrite !inE eqxx.
      - move: Hu. rewrite /T' -/X. 
        (* disjointness of petals, petal_id, partition properties *) admit. 
      - admit. }
    have Py : p \subset val y |: ~: Y. admit.
    have Pz : p \subset val z |: ~: Z. admit.
    admit. }
   *)
    
  have G'_conn : forall x y : G', connect sedge x y. 
  { apply: connectedTE. apply: connected_induced. 
    move => u v Hu Hv. case/uPathP : (G_conn u v) => p irr_p. 
    apply: (connectRI (p := p)). exact: irred_inT irr_p. }

  have cp_lift u v w : 
    w \in @cp G' u v -> val w \in @cp G (val u) (val v).
  { apply: contraTT => /cpPn' [p] /irred_inT. move/(_ (valP u) (valP v)).
    case/Path_to_induced => q /(_ w) <-. exact: cpNI'. }

  pose x0 : G' := Sub (val x) xH'.
  pose y0 : G' := Sub (val y) yH'.
  pose z0 : G' := Sub (val z) zH'.
  pose H' := @add_node G' [set x0;y0;z0].  

  have link_xy : @link_rel G' x0 y0.
  { rewrite /= -val_eqE /= val_eqE (sg_edgeNeq xy) /=. apply/subsetP.
    move => w /cp_lift. case/andP : (xy) => _ /subsetP S /S. 
    by rewrite !inE !sub_val_eq. }
  have link_yz : @link_rel G' y0 z0.
  { rewrite /= -val_eqE /= val_eqE (sg_edgeNeq yz) /=. apply/subsetP.
    move => w /cp_lift. case/andP : (yz) => _ /subsetP S /S. 
    by rewrite !inE !sub_val_eq. }
  have link_zx : @link_rel G' z0 x0.
  { rewrite /= -val_eqE /= val_eqE (sg_edgeNeq zx) /=. apply/subsetP.
    move => w /cp_lift. case/andP : (zx) => _ /subsetP S /S. 
    by rewrite !inE !sub_val_eq. }

  apply: minor_trans (K4_of_triangle G'_conn link_xy link_yz link_zx).
  idtac => {link_xy link_yz link_zx}.
  move/map_of_strict in mm_phi.
  (*   
  pose phi (u : G) : G' := 
         if u \in X then x0 
    else if u \in Y then y0
    else if u \in Z then z0 
         else (insubd x0 u).

  have D3 : [disjoint3 X & Y & Z].
  { case/andP : part1 => cov triv.
    have/trivIsetP T3: trivIset [set X;Y;Z]. { apply: trivIsetS triv. admit. }
    apply/and3P. 
    rewrite !T3 // ?inE ?eqxx // petal_dist // ?val_eqE 
    1?(sg_edgeNeq xy,sg_edgeNeq yz, sg_edgeNeq zx) //; 
    apply CP_extensive; by rewrite !inE eqxx. }

  have inT (u : G') : val u \in T -> phi @^-1 u = [set val u].
  { rewrite -def_T !inE !negb_or -andbA => /and3P [A B C]. 
    apply/setP => w. rewrite !inE. apply/eqP/eqP. 
    - rewrite /phi. case: (disjoint3P w D3); try by move => ? ?; subst; contrab.
      move => W1 W2 W3 <-. by rewrite insubdK // !inE -def_T !inE !negb_or W1 W2 W3. 
    - move => -> {w}. rewrite /phi (negbTE A) (negbTE B) (negbTE C). 
      apply: val_inj. by rewrite insubdK // !inE -def_T !inE !negb_or A B C. }
      
  have pre_x0 : phi @^-1 x0 = X.
  { apply/setP => u. rewrite !inE /phi. 
    case: (disjoint3P u D3); first by rewrite eqxx. 
    rewrite -val_eqE !SubK val_eqE. 
  { admit. }
      
  have preim_G' (u : G') : val u \in phi @^-1 u.
  { rewrite !inE. move: (valP u) => /=. rewrite !inE -!orbA. case/or4P. 
    + move/eqP => E. by rewrite E /phi xX -val_eqE SubK -E.
    + admit. (* as above *)
    + admit. 
    + move/inT/setP/(_ (val u)). by rewrite set11 !inE. }

  have mm_phi : minor_map (Some \o phi).
  { apply map_of_strict. split.
    - (* sujectivity *)
      move => v. exists (val v). move: (preim_G' v). by rewrite !inE => /eqP->. 
    - (* connectedness *)
      move => v. move: (valP v) => /=. rewrite 4!inE !in_set1. 
      rewrite -!sub_val_eq -/x0 -/y0 -/z0 -!orbA. case/or4P => [/eqP->|/eqP->|/eqP->|].
      + rewrite pre_x0. apply: connected_petal => //. 
        apply: CP_extensive; by rewrite !inE eqxx.
      + admit.
      + admit.
      + move => Hv. rewrite (inT _ Hv). exact: connected1. 
    - (* adjacency *)
      move => u v uv. exists (val u); exists (val v). by rewrite preim_G'. 
  }

  *)
  apply: (minor_with (i := i)) mm_phi; first by rewrite !inE eqxx.
  move => b. rewrite !inE -orbA. case/or3P => /eqP ?; subst b.
  - exists x'. 
    + rewrite !inE Some_eqE mem_preim P2 //; by rewrite !inE eqxx.
    + move/setP/(_ (val x')) : UisN. by rewrite !inE mem_imset // sg_sym. 
  - exists y'. 
    + rewrite !inE Some_eqE mem_preim P2 //; by rewrite !inE eqxx.
    + move/setP/(_ (val y')) : UisN. by rewrite !inE mem_imset // sg_sym.
  - exists z'. 
    + rewrite !inE Some_eqE mem_preim P2 //; by rewrite !inE eqxx.
    + move/setP/(_ (val z')) : UisN. by rewrite !inE mem_imset // sg_sym.
Qed.


Lemma ssplit_K4_nontrivial (G : sgraph) (i o : G) : 
  ~~ i -- o -> link_rel G i o -> K4_free (add_edge i o) -> 
  connected [set: G] -> ~ connected (sinterval i o).
Proof.
  move => /= io1 /andP [io2 io3] K4F conn_G. 
  pose G' := @sgraph.induced (add_edge i o) [set~ i].
  set H := add_edge i o in K4F *.
  set U := o |: neighbours i.
  have Ho : o \in [set~ i] by rewrite !inE eq_sym.
  pose o' : G' := Sub o Ho.
  set U' : {set G'} := [set insubd o' x | x in U].
  have tree_CPU' : is_tree (CP_ U').
  { apply: CP_tree K4F _. 
    + (* connectivity *) admit.
    + (* neighbour condition *) admit. }
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
  - move => x y z _ _ _.  exact: (sedge_in_equiv (G := skeleton G)).
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
        -- split. 
          ** exact: split_connected in_parG.
          ** exact: split_K4_free in_parG.
        -- apply: measure_card. rewrite -[X in _ < X]split_edges //.
           apply: sum_gt0 => // [{H in_parG} H|].
           ** exact: split_nontrivial.
           ** exact: split_K4_nontrivial.
    + exact: check_point_wf.
Admitted.

Theorem term_of_iso (G : graph2) : 
  connected [set: skeleton G] ->  
  K4_free (sskeleton G) -> 
  iso2 G (graph_of_term (term_of G)).
Proof.
Admitted.
