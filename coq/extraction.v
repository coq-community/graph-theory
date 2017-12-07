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

(* Isomorphim of graphs *)

Definition bijective2 (G1 G2 : graph) (h : h_ty G1 G2) := 
  bijective h.1 /\ bijective h.2.

Definition iso2 (G1 G2 : graph2) : Prop := 
  exists2 h : h_ty G1 G2, hom_g2 h & bijective2 h.

Notation "G ≈ H" := (iso2 G H) (at level 45).

Lemma consistentT (G : graph) (E : {set edge G}) : consistent setT E.
Proof. by []. Qed.
Arguments consistentT [G] E.



(* not used - should not change vertex type *)
Definition remove_edges2 (G : graph2) (E : {set edge G}) :=
  @point (subgraph_for (consistentT (~:E))) 
         (Sub g_in (in_setT _)) 
         (Sub g_in (in_setT _)).


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

(* TODO: proper name? *)
Lemma measure_subgraph (G : graph2) V E (con : @consistent G V E) x y e : 
  e \notin E -> measure (@point (subgraph_for con) x y) < measure G.
Proof.
  (* [subgraph_for] does not invent edges *)
Admitted.

Lemma measure_node (G : graph2) V E (con : @consistent G V E) v x y : 
  connected [set: skeleton G] -> 
  v \notin V -> measure (@point (subgraph_for con) x y) < measure G.
Proof.
  (* v is a node in a connected graph different from x (and y)
     Hence, v has some adjacent edge that cannot be in the (V,E) subgraph 
     use previous lemma *)
Admitted.


  

(** ** Subroutines *)

Notation IO := ([set g_in; g_out]).


Definition lens (G : graph2) := 
  [&& @petal G IO g_in  == [set g_in ],
      @petal G IO g_out == [set g_out]&
      @link_rel G g_in g_out].


Arguments cp : clear implicits.
Arguments Path : clear implicits.

Definition CK4F (G : graph2) := 
  connected [set: skeleton G] /\ K4_free (sskeleton G).

Definition components (G : graph) (H : {set G}) : {set {set G}} := 
  equivalence_partition (connect (restrict (mem H) (@sedge (skeleton G)))) H.

(** This is one fundamental property underlying the term extraction *)
Lemma split_K4_nontrivial (G : graph2) : 
  g_in != g_out :> G -> 
  lens G -> 
  ~~ @adjacent G g_in g_out -> 
  CK4F G ->
  1 < #|components (@sinterval (skeleton G) g_in g_out)|.
Proof.
  move => A B C [D E]. 
  apply/equivalence_partition_gt1P.
  - move => x y z _ _ _.  exact: (sedge_in_equiv (G := skeleton G)).
  - set H := sinterval _ _. apply/(@connected2 (skeleton G)).
    apply: ssplit_K4_nontrivial => //.
    + by rewrite -adjacentE A.
    + by case/and3P : B.
    + apply/eqP. by  case/and3P : B.
Qed.

(* TOTHINK: do we need [split_par] to be maximal, i.e., such that the
parts do not have non-trivial splits *)

Fixpoint pairs (T : Type) (s : seq T) {struct s} : seq (T * T) := 
  if s isn't x::s' then [::] 
  else if s' is y :: s'' then (x,y):: pairs s' else [::].

Eval simpl in pairs [:: 1].
Eval simpl in pairs [:: 1;2].
Eval simpl in pairs [:: 1;2;3].
Eval simpl in pairs [:: 1;2;3;4].

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
Admitted.

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

Definition big_tmI : seq term -> term.
Admitted.

(* graph induced by [{i,o} ∪ H] without io-edges *) 
Definition component (G : graph2) (H : {set G}) : graph2.
Admitted.

Definition tmEs (G : graph2) : seq term := 
  [seq tmA (label e) | e in @edges G g_in g_out] ++
  [seq tmC (tmA (label e)) | e in @edges G g_out g_in].

(* NOTE: we assume the input to be connected and K4-free *)
Definition term_of_rec (term_of : graph2 -> term) (G : graph2) := 
  if g_in == g_out :> G
  then (* input equals output *)
    let P := @components G [set~ g_in] in
    (\big[tmS/tm1]_(e in @edges G g_in g_in) tm1 :||: tmA (label e)) :o:
    (\big[tmS/tm1]_(C in P) dom (term_of (redirect C)))
  else (* distinct input and output *)
    if lens G
    then (* no checkpoints and no petals on i and o *)
      let P := components (@sinterval (skeleton G) g_in g_out) in
      big_tmI ([seq term_of (component C) | C in P] ++ tmEs G)
    else (* at least one nontrivial petal or checkpoint *)
      @check_point_term term_of G.


Definition term_of := Fix tmT term_of_measure term_of_rec.

Definition check_point_wf (f g : graph2 -> term) (G : graph2) : 
  CK4F G -> 
  g_in != g_out :> G ->
  ~~ lens G -> 
  (forall H : graph2, CK4F H -> measure H < measure G -> f H = g H) -> 
  check_point_term f G = check_point_term g G.
Proof. 
  move => [G_conn G_K4F] Dio not_lens Efg.
  congr tmS.
  - apply: Efg.
    + admit.
    + apply: (measure_node (v := g_out)) => //. admit.
  - (* All pairs are edges in CP({i,o}), so all involved subgraphs are CK4F.
       All petals are smaller since none can contain both i and o.
       For the measure there are two cases: 
       - z first proper checkpoint between x and y:
         Then y is not in the first interval and x is in none of the others:
       - no proper checkpoints between x and y:
         then one of the two petals contains a node z other than i or o.
         z is not in the interval. *)
Admitted.

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
  lens G -> C \in components (@sinterval (skeleton G) g_in g_out) -> 
  CK4F (component C).
Proof.
  (* Follows since all components are subgraphs of G (with same input and output *)
Admitted. 

Lemma measure_lens (G : graph2) C : 
  lens G -> C \in components (@sinterval (skeleton G) g_in g_out) -> 
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
  - congr tmS. apply: eq_big => // C HC. rewrite Efg //.
    + exact: CK4F_redirect.
    + exact: measure_redirect.
  - case: (boolP (lens G)) => [deg_G|ndeg_G].
    + congr big_tmI. congr cat. apply eq_in_map => C. 
      rewrite mem_enum => HC. apply: Efg.
      * exact: CK4F_lens.
      * exact: measure_lens. 
    + exact: check_point_wf.
Qed.

Theorem term_of_iso (G : graph2) : 
  connected [set: skeleton G] ->  
  K4_free (sskeleton G) -> 
  iso2 G (graph_of_term (term_of G)).
Proof.
Admitted.
