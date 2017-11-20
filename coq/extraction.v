Require Import Omega Lia.

From mathcomp Require Import all_ssreflect.

Require Import edone finite_quotient preliminaries.
Require Import sgraph minor checkpoint cp_minor. 
Require Import multigraph subalgebra skeleton bounded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs". 

Definition dom t := tmI (tmS t tmT) tm1.

(* TODO: resolve this name clash *)
Local Notation link_rel := checkpoint.link_rel.

(** Preliminaries *)

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




(** Additional Checkpoint Properties *)



Section Checkpoints.
Variables (G : sgraph).

Hypothesis (conn_G : forall x y :G, connect sedge x y).


Lemma eq_disjoint (T : finType) (A A' B : pred T) :
  A =i A' -> [disjoint A & B] = [disjoint A' & B].
Proof. Admitted.
Arguments eq_disjoint [T A] A' [B].  



(* TOTHINK/TODO: Lemmas about [disjoint] should be as below, to avoid exposing
conversions to collective predicates when rewriting *)
Lemma disjoint_sym' (T : finType) (A B : mem_pred T) : 
  disjoint A B = disjoint B A.
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
