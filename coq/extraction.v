Require Import RelationClasses Morphisms Setoid Omega.

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


Lemma consistentT (G : graph) (E : {set edge G}) : consistent setT E.
Proof. by []. Qed.
Arguments consistentT [G] E.

(** * Term Extraction *)

(** ** Termination Metric *)

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

Lemma measure_subgraph (G : graph2) V E (con : @consistent G V E) x y e : 
  e \notin E -> measure (@point (subgraph_for con) x y) < measure G.
Proof. 
  move => He. apply: measure_card. rewrite card_sig. 
  apply: proper_card. apply/properP. split; by [exact/subsetP| exists e].
Qed.

Lemma measure_node (G : graph2) V E (con : @consistent G V E) v x y : 
  connected [set: skeleton G] -> 
  v \notin V -> measure (@point (subgraph_for con) x y) < measure G.
Proof.
  move => /connectedTE conn_G Hv. 
  case/uPathP : (conn_G v (val x)) => p _. 
  have vx: v != val x. { apply: contraNN Hv => /eqP->. exact: valP. }
  case: (splitL p vx) => u [vu] _ {p vx}. rewrite -adjacentE in vu.
  case/andP: vu => _ /orP[] [/existsP [e He]].
  - refine (@measure_subgraph _ _ _ _ _ _ e _). 
    apply: contraNN Hv. move/con => [Hs Ht]. 
    move: He. by rewrite inE => /andP[/eqP<- _].
  - refine (@measure_subgraph _ _ _ _ _ _ e _). 
    apply: contraNN Hv. move/con => [Hs Ht]. 
    move: He. by rewrite inE => /andP[_ /eqP<-].
Qed.

(** ** Subroutines *)

Notation IO := ([set g_in; g_out]).

Definition lens (G : graph2) := 
  [&& @petal G IO g_in  == [set g_in ],
      @petal G IO g_out == [set g_out]&
      @link_rel (skeleton G) g_in g_out].

Arguments cp : clear implicits.
Arguments Path : clear implicits.

Definition CK4F (G : graph2) := 
  connected [set: skeleton G] /\ K4_free (sskeleton G).

Definition components (G : graph) (H : {set G}) : {set {set G}} := 
  equivalence_partition (connect (restrict (mem H) (@sedge (skeleton G)))) H.

(** If G is a lens with non non-adjacent input and output, then it has
at least two parallel components *)
Lemma split_K4_nontrivial (G : graph2) : 
  g_in != g_out :> G -> 
  lens G -> 
  ~~ @adjacent G g_in g_out -> 
  CK4F G ->
  1 < #|components (@sinterval (skeleton G) g_in g_out)|.
Proof.
  move => A B C [D E]. 
  apply/equivalence_partition_gt1P.
  - move => x y z _ _ _. exact: (sedge_in_equiv (G := skeleton G)).
  - set H := sinterval _ _. apply/(@connected2 (skeleton G)).
    apply: ssplit_K4_nontrivial => //.
    + by rewrite -adjacentE A.
    + by case/and3P : B.
    + apply/eqP. by case/and3P : B => ? _ _.
Qed.

Fixpoint pairs (T : Type) (s : seq T) {struct s} : seq (T * T) := 
  if s isn't x::s' then [::] 
  else if s' is y :: s'' then (x,y):: pairs s' else [::].

Eval simpl in pairs [:: 1].
Eval simpl in pairs [:: 1;2].
Eval simpl in pairs [:: 1;2;3;4].

Lemma pairs_cons (T : Type) a b (s : seq T) : 
  pairs [:: a, b & s] = (a,b) :: pairs (b :: s).
Proof. done. Qed.

(* TOTHINK: this does not look easy to used *)
Lemma pairs_cat (T : Type) a1 a2 (s1 s2 : seq T) : 
  pairs (rcons s1 a1 ++ a2 :: s2) = 
  pairs (rcons s1 a1) ++ (a1,a2) :: pairs (a2 :: s2).
Admitted.

(* Fixpoint pairs (T : Type) (x : T) (s : seq T) :=  *)
(*   if s is y::s' then (x,y) :: pairs y s' else nil. *)

(** list of checkpoint bewteen x and y (excluding x) *)
(* NOTE: see insub in eqtype.v *)
(* TOTHINK: this actually does include both x and y *)
Definition checkpoint_seq (G : graph) (x y : G) := 
  if @idP (connect (@sedge (skeleton G)) x y) isn't ReflectT con_xy then [::]
  else sort (cpo con_xy) (enum (@cp (skeleton G) x y)).

Notation "u :||: v" := (tmI u v) (at level 35).
Notation "u :o: v" := (tmS u v) (at level 33).

Definition check_point_term (t : graph2 -> term) (G : graph2) :=
  let (i,o) := (g_in : G, g_out : G) in
  let c := checkpoint_seq i o in
  t (pgraph IO i) :o: 
  \big[tmS/tm1]_(p <- pairs c) (t(igraph p.1 p.2) :o: t(pgraph IO p.2)).

Fact redirect_proof1 (T : finType) x (A : {set T}) : x \in x |: A. 
Proof. by rewrite !inE eqxx. Qed.
Arguments redirect_proof1 [T x A].

(** subgraph induced by [i |: H] without i-selfloops and with output set
to [o] *)
Lemma redirect_consistent (G : graph2) (H : {set G}) (o : G) : 
  let H' := g_in |: (o |: H) in 
  consistent H' (edge_set H' :\: edges g_in g_in).
Proof. apply: consistent_setD. exact: induced_proof. Qed.

Fact redirect_output_proof (T : finType) x y (B : {set T}) : x \in y |: (x |: B). 
Proof. by rewrite !inE eqxx. Qed.
Arguments redirect_output_proof [T x y B].

Definition redirect_to (G : graph2) (H : {set G}) (o:G) :=
  @point (subgraph_for (@redirect_consistent G H o))
         (Sub g_in (setU11 _ _))
         (Sub o redirect_output_proof).

(** subgraph induced by [i |: H] without i-selfloops and with [o] set
to some neighbor of [i] in H *)
Definition redirect (G : graph2) (H : {set G}) : graph2 :=
  if [pick z in H | adjacent g_in z] isn't Some z then one2 
  else redirect_to H z.


(* NOTE: We need to use foldr1 here since there is no neutral element
for parallel composition in the term syntax for connected graphs *)
Definition big_tmI : seq term -> term := foldr1 tm1 tmI id.

Lemma component_consistent (G : graph2) (H : {set G}) : 
  let H' := g_in |: (g_out |: H) in 
  @consistent G H' (edge_set H' :\: edges g_in g_out :\: edges g_out g_in).
Proof. do 2 apply: consistent_setD. exact: induced_proof. Qed.

Definition component (G : graph2) (H : {set G}) : graph2 := 
  @point (subgraph_for (@component_consistent G H))
         (Sub g_in (setU11 _ _))
         (Sub g_out (redirect_output_proof)).

(** Possibly empty sequence of (trivial) terms corresponding to direct
i-o edges. Yields nonempty parallel composition when concatenated with
the terms for the i-o components *)
Definition tmEs (G : graph2) : seq term := 
  [seq tmA (label e) | e in @edges G g_in g_out] ++
  [seq tmC (tmA (label e)) | e in @edges G g_out g_in].

(* NOTE: we assume the input graph to be connected and K4-free *)
Definition term_of_rec (term_of : graph2 -> term) (G : graph2) := 
  if g_in == g_out :> G
  then (* input equals output *)
    let P := @components G [set~ g_in] in
    (\big[tmS/tm1]_(C in P) dom (term_of (redirect C))) :||:
    (\big[tmS/tm1]_(e in @edges G g_in g_in) tm1 :||: tmA (label e))
  else (* distinct input and output *)
    if lens G
    then (* no checkpoints and no petals on i and o *)
      let P := components (@sinterval (skeleton G) g_in g_out) in
      big_tmI ([seq term_of (component C) | C in P] ++ tmEs G)
    else (* at least one nontrivial petal or checkpoint *)
      @check_point_term term_of G.

Definition term_of := Fix tmT term_of_measure term_of_rec.

Lemma mem_pairs_sort (T : eqType) e x y (s : seq T) : 
  uniq s -> total e -> (x,y) \in pairs (sort e s) -> 
  [/\ x \in s, y \in s, x != y & forall z, z \in s -> e z x || e y z].
Admitted.

(** All pairs in the checkpoint sequence are adjacent in CP({i,o}) *)
Lemma cp_pairs_edge (G : graph) (i o x y : G) : 
  connected [set: skeleton G] ->
  (x,y) \in pairs (checkpoint_seq i o) -> 
  exists (px : x \in @CP G [set i;o]) (py : y \in @CP G [set i;o]), 
    (Sub x px : @CP_ G [set i;o]) -- (Sub y py).
Proof.
  move => conn_G. move/(_ i o) : (conn_G) => conn_io'.
  rewrite /checkpoint_seq. case: {-}_ / idP => [conn_io|].
  - move/mem_pairs_sort. case/(_ _ _)/Wrap => [||[P1 P2 P3 P4]].
    + exact: enum_uniq. 
    + exact: (@cpo_total (skeleton G)).
    + rewrite !mem_enum in P1,P2.
      suff S: cp G x y \subset [set x; y].
      { have px: x \in @CP G [set i;o]. 
        { apply/bigcupP. exists (i,o); by rewrite // !inE !eqxx. }
        have py: y \in @CP G [set i;o].
        { apply/bigcupP. exists (i,o); by rewrite // !inE !eqxx. }
        exists px. exists py. by rewrite /= P3. }
      apply/subsetP => z Hz. move: (P4 z). rewrite mem_enum.
      have Hz': z \in cp G i o. { apply: cp_widen Hz => //. }
      move/(_ Hz'). move: Hz. 
      rewrite (cpo_cp conn_io) // !inE => /andP[H1 H2].
      case/orP => H3. 
      * have H: cpo conn_io x z && cpo conn_io z x by rewrite H3.
        by rewrite (cpo_antisym _ _ H) // eqxx.
      * have H: cpo conn_io y z && cpo conn_io z y by rewrite H3.
        by rewrite (cpo_antisym _ _ H) // eqxx.        
  - rewrite restrictE // in conn_io'. by move => u;rewrite !inE.
Qed.

Notation sigraph := cp_minor.igraph.
Lemma sskeleton_add (G : graph) (x y : G) : 
  sgraph.subgraph (sskeleton (igraph x y))
                  (add_edge (sigraph G x y) istart iend).
Proof.
  rewrite /igraph /sigraph /sskeleton -/istart -/iend. 
Admitted.

Lemma CK4F_link (G : graph2) (x y : @CP_ G IO) : 
  CK4F G -> x -- y -> CK4F (igraph (val x) (val y)).
Proof.
  move => [conn_G K4F_G] xy. 
  split; first exact: connected_igraph.
  apply: subgraph_K4_free (sskeleton_add _ _) _.
  exact: igraph_K4_free. 
Qed.

Lemma sc_eq T T' (e : rel T) (e' : rel T') f x y : 
  (forall x y, e' (f x)  (f y) = e x y) -> sc e' (f x) (f y) = sc e x y.
Proof. move => H. by rewrite /sc /= !H. Qed.

Lemma skeleton_induced_edge (G : graph) (V : {set skeleton G}) u v : 
  ((val u : skeleton G) -- val v) = ((u : skeleton (induced V)) -- v).
Proof.
  rewrite /= /sk_rel. apply: sc_eq => {u v} u v /=.
  rewrite val_eqE. case E : (_ != _) => //=. 
  apply/existsP/existsP.
  - case => e e_uv. 
    have He: e \in edge_set V. 
    { case/andP : e_uv => E1 E2. rewrite inE (eqP E1) (eqP E2).
      apply/andP;split; exact: valP. }
    exists (Sub e He). by rewrite -!val_eqE.
  - case => e. rewrite -!val_eqE /= => e_uv. by exists (val e).
Qed.

(* TOTHINK: how to align induced subgraphs for simple graphs and
induced subgraphs for multigraphs *)
Lemma connected_induced (G : graph) (V : {set skeleton G}) : 
  connected V -> connected [set: skeleton (induced V)].
Proof. 
  move => conV. apply: connectedTI => u v. 
  move: (conV (val u) (val v) (valP u) (valP v)). 
  case/upathPR => p /upathW.
  elim: p u => [?|a p IH u]. 
  - move/spath_nil/val_inj ->. exact: connect0.
  - rewrite spath_cons /= -!andbA => /and4P [A B C D]. 
    apply: (connect_trans (y := Sub a B)); last exact: IH.
    apply: connect1. change (u -- (Sub a B)). 
    by rewrite -skeleton_induced_edge.
Qed.

Lemma induced_K4_free (G : graph2) (V : {set G}) : 
  K4_free (sskeleton G) -> K4_free (induced V).
Proof.
  apply: minor_K4_free. 
  apply: (minor_trans (y := skeleton G)).
  apply: sub_minor. apply: skel_sub. 
  (* NOTE: this is a relation on the respecive skeletons *)
  apply: sub_minor. apply: sub_sub. exact: induced_sub.
Qed.

Lemma CK4F_sub (G : graph2) (V : {set G})  x : 
  @connected G V -> CK4F G -> CK4F (point (induced V) x x).
Proof. 
  move => conV CK4F_G. split. 
  - exact: connected_induced.
  - apply: subgraph_K4_free (sub_pointxx _) _.
    apply: induced_K4_free. apply CK4F_G.
Qed.


Lemma rec_petal (G : graph2) (x : G) : 
  CK4F G -> x \in @CP (skeleton G) IO -> g_in != g_out :> G ->
  CK4F (pgraph IO x) /\ measure (pgraph IO x) < measure G.
Proof.
  move => [conn_G K4F_G] cp_x Dio. split. 
  - apply: CK4F_sub => //. exact: connected_petal.
  - suff: (g_in \notin @petal G IO x) || (g_out \notin @petal G IO x).
    { by case/orP; exact: measure_node. }
    rewrite -negb_and. apply:contraNN Dio => /andP[].
    rewrite !(petal_cp conn_G) // => [/eqP-> /eqP-> //||]; 
      by apply CP_extensive; rewrite !inE eqxx.
Qed.  

Lemma cp_pairs_measure (G : graph2) x y :
  CK4F G -> ~~ lens G -> (x,y) \in pairs (@checkpoint_seq G g_in g_out) ->
  measure (igraph x y) < measure G.
Proof. 
  move => CK4F_G no_lens pair_xy. 
  suff [z Hz] : exists z, z \notin interval x y. 
  { apply: measure_node Hz. by apply CK4F_G. }
  (* case/cp_pairs_edge : pair_xy; first by apply CK4F_G. *)
  (* move => x0 [y0] link_xy.  *)

  case: (boolP (link_rel G g_in g_out)) => H.
  - rewrite /lens H andbT negb_and in no_lens. 
    case/orP : no_lens => /petal_nontrivial [z]. 
    + admit.
    + admit.
  - 
  (* Either there exists a third checkpoint (that is not in the
  interval) or one of the petals is nontrivial since G is not a
  lens *)
Admitted.

Lemma cp_pairs_CK4G (G : graph2) (x y : G) :
  CK4F G -> ~~ lens G -> (x,y) \in pairs (@checkpoint_seq G g_in g_out) ->
  CK4F (igraph x y).
Proof.
  move => [G_conn G_K4F] ? Hxy.
  move/cp_pairs_edge : (Hxy) => /(_ G_conn) [px] [py] link_xy. 
  exact: CK4F_link link_xy. 
Qed.
                           
Definition check_point_wf (f g : graph2 -> term) (G : graph2) : 
  CK4F G -> 
  g_in != g_out :> G ->
  ~~ lens G -> 
  (forall H : graph2, CK4F H -> measure H < measure G -> f H = g H) -> 
  check_point_term f G = check_point_term g G.
Proof. 
  move => [G_conn G_K4F] Dio not_lens Efg.
  congr tmS. 
  - apply: Efg; apply rec_petal => // ; apply: CP_extensive; by rewrite !inE eqxx.
  - apply: eq_big_seq => [[x y] Hxy /=]. congr tmS. 
    + apply: Efg; by [apply: cp_pairs_CK4G|apply: cp_pairs_measure].
    + move/cp_pairs_edge : Hxy => /(_ G_conn) [px] [py] _. 
      by apply: Efg; apply rec_petal.
Qed.

Lemma CK4F_redirect (G : graph2) C : 
  CK4F G -> g_in == g_out :> G -> C \in @components G [set~ g_in] ->
  CK4F (redirect C).
Proof.
  split. 
  - rewrite /redirect. case: pickP. 
Admitted. (* Follows with proposition 21(iii) *)

Lemma measure_redirect (G : graph2) C : 
  CK4F G -> g_in == g_out :> G -> C \in @components G [set~ g_in] ->
  measure (redirect C) < measure G.
Proof.
  (* Since G is connected and C nonempty, there must be a neighbor of i.
  Hence, [redirect C] has distinct input an ouutput and no more edges than G. *)
Admitted. 

Lemma CK4F_lens (G : graph2) C : 
  CK4F G -> lens G -> C \in components (@sinterval (skeleton G) g_in g_out) -> 
  CK4F (component C).
Proof.
  (* Follows since all components are subgraphs of G (with same input and output *)
Admitted.

Lemma measure_lens (G : graph2) C : 
  CK4F G -> lens G -> C \in components (@sinterval (skeleton G) g_in g_out) -> 
  measure (component C) < measure G.
Proof. 
  (* By case distinction on [#|P|] where [P := components _]
  - #|P| = 0: trivial
  - #|P| = 1: Since G is K4-free, there must be a direct io-edge e by Prop. 22(i)
    e is not an edge of [component C].
  - #|P| > 1: Every component in P has at least one node (distinct from i and o) 
    and therefore at least one edge. *)     
Admitted. 

Lemma term_of_eq (G : graph2) : 
  CK4F G -> term_of G = term_of_rec term_of G.
Proof.
  apply: Fix_eq => // {G} f g G CK4F_G Efg. rewrite /term_of_rec. 
  case: (boolP (@g_in G == g_out)) => Hio.
  - congr tmI. apply: eq_big => // C HC. rewrite Efg //.
    + exact: CK4F_redirect.
    + exact: measure_redirect.
  - case: (boolP (lens G)) => [deg_G|ndeg_G].
    + congr big_tmI. congr cat. apply eq_in_map => C. 
      rewrite mem_enum => HC. apply: Efg.
      * exact: CK4F_lens.
      * exact: measure_lens. 
    + exact: check_point_wf.
Qed.

(** * Isomorphim Properties *)

Local Open Scope quotient_scope.


Definition iso2_congruence (op : graph2 -> graph2 -> graph2) :=
  forall (G1 G2 G1' G2' : graph2), G1 ≈ G1' -> G2 ≈ G2' -> op G1 G2 ≈ op G1' G2'.

Lemma par2_congr : iso2_congruence par2.
Proof.
  move => G1 G2 G1' G2' [f f1 f2] [g g1 g2].
  have [h [I1 I2 I3 I4]] := iso2_union f1 f2 g1 g2.
  apply: (merge_congr (h := h)) => //; try by rewrite I3 f1.
  move => [x|x] [y|y];rewrite /eq_par2 /= !(I3,I4) //.
  by rewrite !iso2_inv_in // !iso2_inv_out.
Qed.


(* Instance iso2_Morphism : *)
(*   Proper (iso2 ==> iso2 ==> iff) (iso2). *)
(* Proof. *)
(*   move => G1 G1' iso1 G2 G2' iso2. by rewrite -> iso1,iso2. *)
(* Qed. *)

Instance par2_morphisem : 
  Proper (iso2 ==> iso2 ==> iso2) par2.
Proof. move => ? ? ? ? ? ?. exact: par2_congr. Qed.

Definition big_par2 (s : seq graph2) : graph2 := 
  \big[par2/top2]_(G <- s) G.

Lemma big_par2_cons G Gs : 
  big_par2 (G::Gs) = par2 G (big_par2 Gs).
Proof. by rewrite /big_par2 big_cons. Qed.

(** NOTE: For the moment this is only needed to provide an identity
element to par2. If this turns out hard to prove, use foldr1 instead *)
Lemma par2_idR G : par2 G top2 ≈ G.
Admitted.

Lemma par2_idL G : par2 top2 G ≈ G.
Admitted.

Lemma big_par2_1 G : big_par2 [:: G] ≈ G.
Proof. rewrite /big_par2 big_cons big_nil. exact: par2_idR. Qed.

Lemma big_par2_map (r : seq term) : 
  ~~ nilp r -> big_par2 (map graph_of_term r) ≈ graph_of_term (big_tmI r).
Proof.
  elim: r => //= u s. case e : (nilp s).
  - move => _ _. by rewrite (nilP e) /= /big_par2_cons big_par2_1. 
  - move/(_ isT) => IH _. by rewrite big_par2_cons /= IH.
Qed.

Lemma par2_assoc G1 G2 G3 : 
  par2 (par2 G1 G2) G3 ≈ par2 G1 (par2 G2 G3).
Admitted.

Lemma big_par2_cat r1 r2 : 
  big_par2 (r1 ++ r2) ≈ par2 (big_par2 r1) (big_par2 r2).
Proof. 
  rewrite /big_par2 big_cat_nested. 
  elim: r1 => [|G r1 IH].
  - by rewrite !big_nil par2_idL.
  - by rewrite !big_cons IH par2_assoc.
Qed.

Lemma big_par2_congr (T:finType) (s : seq T) (g1 g2 : T -> graph2) :
  (forall x, x \in s -> g1 x ≈ g2 x) -> 
  big_par2 [seq g1 x | x <- s] ≈ big_par2 [seq g2 x | x <- s].
Proof. 
  elim: s => //= a s IH. admit.
Admitted.



Lemma big_par2_congrs (T:finType) (s : {set T}) (g1 g2 : T -> graph2) :
  (forall x, x \in s -> g1 x ≈ g2 x) -> 
  big_par2 [seq g1 x | x in s] ≈ big_par2 [seq g2 x | x in s].
Proof. 
  move => A. apply: big_par2_congr => x. by rewrite mem_enum => /A.
Qed.

Section SplitParallel.
Variable (G : graph2).
Let E := @edges G g_in g_out :|: edges g_out g_in.
Let P := components (@sinterval (skeleton G) g_in g_out).

Definition G_rest := big_par2 [seq component C | C in P].

Lemma setU22 (T:finType) (x y :T) : y \in [set x;y].
Proof. by rewrite !inE eqxx. Qed.

Lemma split_edge e : e \in E -> consistent [set g_in;g_out] [set e].
Admitted.

Definition G_edge (e : edge G) := sym2 (label e).
Definition G_edgeC (e : edge G) := cnv2 (sym2 (label e)).

Definition G_edges := big_par2 ([seq G_edge e | e in edges g_in g_out] ++ 
                                [seq G_edgeC e | e in edges g_out g_in]).

(* Definition G_edges := *)
(*   @point (subgraph_for split_edges)  *)
(*          (Sub g_in (setU11 _ _))  *)
(*          (Sub g_out (setU22 _ _)). *)


(* TOTHINK: What is the general decomposition lemma? (partition
overlapping only at IO?) *)
Lemma split_io : G ≈ par2 G_rest G_edges.
Admitted.
End SplitParallel.

Lemma sintervalxx (G : sgraph) (x : G) : sinterval x x = [set~ x].
Admitted.

Theorem term_of_iso (G : graph2) : 
  CK4F G -> iso2 G (graph_of_term (term_of G)).
Proof.
  elim: (wf_leq term_of_measure G) => {G} G _ IH CK4F_G.
  rewrite term_of_eq // /term_of_rec. 
  case: ifP => C1.
  - (* selfloops / io-redirect *)
    rewrite /= {1}[G]split_io. apply: par2_congr.
    + rewrite /G_rest -(eqP C1) sintervalxx. 
      admit.
    + admit.
  - case: ifP => C2.
    + (* parallel split *)
      rewrite -big_par2_map; last first.
      { admit. }
      rewrite map_cat big_par2_cat {1}[G]split_io.
      apply: par2_congr. 
      * rewrite -map_comp. apply: big_par2_congrs. 
        move => C HC. apply: IH. 
        -- exact: measure_lens. 
        -- exact: CK4F_lens. 
      * rewrite /G_edges /tmEs map_cat -!map_comp. 
        rewrite big_par2_cat. reflexivity.
        (* the complexity is in [split_io] *)
    + (* sequential split *) 
      admit.
Admitted.

(** * Minor Exclusion Corollaries *)

Corollary minor_exclusion_2p (G : graph2) :
  connected [set: skeleton G] -> 
  K4_free (sskeleton G) <-> 
  exists (T:tree) (B : T -> {set G}), [/\ decomp T G B, width B <= 3 & compatible B].
Proof.
  move => conn_G. split => [K4F_G|[T [B [B1 B2 B3]]]].
  - have [T [B] [B1 B2 B3]] := (graph_of_TW2 (term_of G)).
    have [i hom_i bij_i] := term_of_iso (conj conn_G K4F_G).
    exists T. exists (fun t => [set x | i.1 x \in B t]). 
    (* lift decomposition along isomorphim *) 
    admit.
  - apply: (TW2_K4_free (G := sskeleton G)) B2.
    exact: decomp_sskeleton.
Admitted.

Lemma inverse_sskeleton (G : sgraph) : 
  exists G', sg_iso (sskeleton G') G /\ sg_iso (skeleton G') G.
Proof. (* for evert pair x -- y in G add a 0-edge *) Admitted.

Corollary sminor_exclusion (G : sgraph) :
  connected [set: G] -> 
  K4_free G <-> 
  exists (T:tree) (B : T -> {set G}), sdecomp T G B /\ width B <= 3.
Proof.
  move => conn_G.
  have [G' [iso_Gs iso_G]] := inverse_sskeleton G.
  have conn_G' : connected [set: skeleton G'].
  { admit. (* lift along iso *) }
  have M := minor_exclusion_2p conn_G'.  
  split => [K4F_G|].
  - have/M [T [B [B1 B2 B3]]] : K4_free (sskeleton G'). 
    { admit. (* lift along iso *) }
    exists T. 
    have: sdecomp T (sskeleton G') B by exact: decomp_sskeleton. 
    admit. (* lift along iso *)
  - move => [T [B [B1 B2]]]. 
    suff: K4_free (sskeleton G'). { admit. (* iso *)}
    apply/M. 
    (* need to construct decomposition for the multigraph G' *)
Admitted.
