Require Import Omega Lia.

From mathcomp Require Import all_ssreflect.
Require Import finite_quotient preliminaries sgraph multigraph subalgebra skeleton bounded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition dom t := tmI (tmS t tmT) tm1.

(** (S)Graph preliminaries *)


Lemma consistentT (G : graph) (E : {set edge G}) : consistent setT E.
Proof. by []. Qed.
Arguments consistentT [G] E.

Definition remove_edges (G : graph2) (E : {set edge G}) :=
  @point (subgraph_for (consistentT (~:E))) 
         (Sub g_in (in_setT _)) 
         (Sub g_in (in_setT _)).


(** * Term Extraction *)

(* Isomorphim of graphs *)

Definition bijective2 (G1 G2 : graph) (h : h_ty G1 G2) := 
  bijective h.1 /\ bijective h.2.

Definition iso2 (G1 G2 : graph2) : Prop := 
  exists2 h : h_ty G1 G2, hom_g2 h & bijective2 h.

Notation "G ≈ H" := (iso2 G H) (at level 45).


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


Lemma equivalence_rel_of_sym (T : finType) (e : rel T) :
  symmetric e -> equivalence_rel (connect e).
Admitted.

Lemma sedge_equiv (G : sgraph) (A : {set G}) : 
  equivalence_rel (connect (restrict (mem A) sedge)). 
apply: equivalence_rel_of_sym.  apply: symmetric_restrict. exact:sg_sym. Qed.



Lemma connected2 (G : sgraph) (D : {set G}) : 
  (~ connected D) <-> exists x y, [/\ x \in D, y \in D & ~~ connect (restrict (mem D) sedge) x y].
Admitted.

  
Definition neighbours (G : sgraph) (x : G) := [set y | x -- y].

(* TODO: tree_axiom still uses upath - should use packaged paths ... *)
Definition is_tree (G : sgraph) := 
  connected [set: G] /\ forall x y : G, unique (fun p : Path x y => irred p).

Lemma CP_extensive (G : sgraph) (U : {set G}) : 
  {subset U <= CP U}.
Proof.
  move => x inU. apply/bigcupP; exists (x,x); by rewrite ?inE /= ?inU // cpxx inE.
Qed.

(* TOTHINK: What is the right formulation here? *)
Lemma CP_path_aux (G : sgraph) (U : {set G}) (x y : G) (p : seq G) :
  x \in CP U -> y \in CP U -> @spath G x y p -> uniq (x :: p) ->
  @spath (link_graph G) x y [seq z <- p | z \in CP U].
Admitted.

Lemma CP_path (G : sgraph) (U : {set G}) (x y : CP_ U) (p : @Path G (val x) (val y)) : 
  irred p -> exists2 q : @Path (CP_ U) x y, irred q & [set val z | z in q] \subset p.
Admitted.

Lemma restrictE (T : finType) (e : rel T) (A : pred T) : 
  A =i predT -> connect (restrict A e) =2 connect e.
Proof. 
  move => H x y. rewrite (eq_connect (e' := e)) //. 
  move => {x y} x y /=. by rewrite !H.
Qed.

Lemma connectedTE (G : sgraph) (x y : G) : 
  connected [set: G] -> connect sedge x y. 
Proof. 
  move => A. move: (A x y). rewrite !restrictE; last by move => ?; rewrite inE.
  apply; by rewrite inE. 
Qed.

Lemma connectedTI (G : sgraph) : 
  (forall x y : G, connect sedge x y) -> connected [set: G].
Proof. move => H x y _ _. rewrite restrictE // => z. by rewrite inE. Qed.


Lemma PathP (G : sgraph) (x y : G) :
  reflect (inhabited (Path x y)) (connect sedge x y).
Admitted.

Lemma CP_connected (G : sgraph) (U : {set G}) : 
  connected [set: G] -> connected [set: CP_ U].
Proof.
Admitted.


Lemma CP2_part (G : sgraph) x y x' y' : 
  [set x; y] \subset cp x' y' -> 
  let U := [set x'; y'] in 
  partition [set petal U x; petal U y; sinterval x y] [set: G].
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


Lemma cp_neighbours (G : sgraph) (x y : G) z : 
  x != y -> (forall x', x -- x' -> z \in cp x' y) -> z \in cp x y.
Proof.
  move => A B. apply/cpP => p. case: p => [|x' p].
  - move/spath_nil/eqP => ?. by contrab.
  - rewrite spath_cons in_cons => /andP [C D]. apply/orP;right. 
    apply/(cpP (y := y)) => //. exact: B. 
Qed.


Arguments Path G x y : clear implicits.

Lemma link_path_cp (G : sgraph) (x y : G) (p : Path (link_graph G) x y) : 
  {subset cp x y <= p}.
Proof. apply/subsetP. apply: link_seq_cp. exact: (valP p). Qed.

(* TOTHINK: is this the best way to  *)
Lemma induced_path (G : sgraph) (S : {set G}) (x y : sgraph.induced S) (p : Path _ x y) : 
  @spath G (val x) (val y) (map val (val p)).
Proof.
  case: p => p pth_p /=. elim: p x pth_p => /= [|z p IH] x pth_p.
  - by rewrite (spath_nil pth_p) spathxx.
  - rewrite !spath_cons in pth_p *. 
    case/andP : pth_p => p1 p2. apply/andP; split => //. exact: IH.
Qed.

Lemma CP_path_cp (G : sgraph) (U : {set G}) (x y : CP_ U) (p : Path _ x y) z : 
  val z \in @cp G (val x) (val y) -> z \in p.
Proof. 
  move/link_path_cp. 
  suff P : @spath (link_graph G) (val x) (val y) (map val (val p)).
  { move/(_ (Build_Path P)). rewrite inE /= mem_map //. exact: val_inj. }
  exact: induced_path.
Qed.


(** NOTE: If [CP_ U] is a tree, then there exists exactly one irredundant xy-path. *)
Lemma CP_subtree1 (G : sgraph) (U : {set G}) (x y z : CP_ U) (p : @Path (CP_ U) x y) : 
  is_tree (CP_ U) -> irred p -> (z \in p <-> val z \in @cp G (val x) (val y)).
Proof.
  move => tree_U irr_p. split.
  - move => z_in_p. apply/negPn. apply/negP => /=. 
    case/cpPn' => q irr_q av_z. case: (CP_path irr_q) => r irr_r /subsetP sub_q. 
    have zr : z \notin r. { apply: contraNN av_z => in_r. apply: sub_q. by rewrite mem_imset. }
    case: tree_U => _ /(_ x y p r). case/(_ _ _)/Wrap => // ?. subst. by contrab.
  - simpl. exact: CP_path_cp.
Qed.

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


Lemma eq_big_seq_In (R : Type) (idx : R) (op : R -> R -> R) I (r : seq I) (F1 F2 : I -> R) :
  (forall x, List.In x r -> F1 x = F2 x) ->
  \big[op/idx]_(i <- r) F1 i = \big[op/idx]_(i <- r) F2 i.
Proof.
  elim: r => [|a r IH] eqF; rewrite ?big_nil // !big_cons eqF ?IH //; last by left.
  move => x Hx. apply: eqF. by right.
Qed.

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
