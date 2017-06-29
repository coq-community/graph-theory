From mathcomp Require Import all_ssreflect.
Require Import finite_quotient preliminaries sgraph multigraph subalgebra skeleton bounded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition dom t := tmI (tmS t tmT) tm1.

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

Lemma measure_card (G' G : graph2) : 
  #|edge G'| < #|edge G| -> measure G' < measure G.
Admitted.

Lemma measure_io (G' G : graph2) : 
  (g_in == g_out :> G) -> (g_in != g_out :> G') -> #|edge G'| <= #|edge G| -> 
  measure G' < measure G.
Admitted.

(** ** Subroutines *)

(** Splitting intro parallel components *)

Fact split_proof1 (T : finType) (A : {set T}) x y : x \in A :|: [set x; y].
Proof. by rewrite !inE eqxx ?orbT. Qed.

Fact split_proof2 (T : finType) (A : {set T}) x y : y \in A :|: [set x; y].
Proof. by rewrite !inE eqxx ?orbT. Qed.

Definition parcomp (G : graph2) (A : {set G}) := 
  @point (induced (A :|: [set g_in; g_out]))
         (Sub g_in (split_proof1 A g_in g_out))
         (Sub g_in (split_proof1 A g_in g_out)).

(* NOTE: This only does the right thing if (skeleton G) is connected
and i and o are not adjacent *)
Definition split_par (G : graph2) : seq graph2 := 
  let H := ~: [set g_in; g_out] in 
  let P := equivalence_partition (connect (@sedge (skeleton G))) H in 
  if #|P| == 1 then [:: G] 
  else [seq parcomp A | A <- enum P].

(** Take the graphs induced by "{i,o} ∪ H" with H being the components of "G\{i,o}" *)

(* FIXME: [top2] is not connected; how to state this for connected
graphs only *)

Lemma split_iso (G : graph2) :
  \big[par2/top2]_(H <- split_par G) H ≈ G.
Admitted.

Lemma split_inhab (G : graph2) : 0 < size (split_par G).
Admitted.

(* WARN: we do not have decidable equality on graphs, this might become problematic? *)
Lemma split_nontrivial (G H : graph2) : 
  0 < #|edge G| -> List.In H (split_par G) -> 0 < #|edge H|.
Admitted.

Lemma split_subgraph (G H : graph2) : 
  List.In H (split_par G) -> subgraph H G.
Admitted.

Lemma split2 (G : graph2) : 
  connected [set: skeleton G] -> 
  1 < #|edge G| -> 
  #|@CP (skeleton G) [set g_in; g_out]| == 2 -> 
  1 < size (split_par G).
Admitted.

(* TOTHINK: do we need [split_par] to be maximal, i.e., such that the
parts do not have non-trivial splits *)

(** Sequence of checkpoints going from x to y *)
Definition ch_seq (G : graph) (x y : G) : seq G.
Admitted.

(* FIXME: this should use the bag graphs not the interval graphs *)
Definition degenerate (G : graph2) := 
  [&& #|edge (@pgraph G [set g_in;g_out] g_in )| == 0,
      #|edge (@pgraph G [set g_in;g_out] g_out)| == 0&
      #|@CP (skeleton G) [set g_in; g_out]| == 2].

Fixpoint pairs (T : Type) (x : T) (s : seq T) := 
  if s is y::s' then (x,y) :: pairs y s' else nil.

(** list of checkpoint bewteen x and y (excluding x) *)
Definition checkpoint_seq (G : graph) (x y : G) : seq G.
Admitted.

Notation IO := ([set g_in; g_out]).

Definition check_point_term (t : graph2 -> term) (G : graph2) (x y : G) :=
  let c := checkpoint_seq x y in
  tmS (t (pgraph IO x)) (\big[tmS/tm1]_(p <- pairs x c) tmS (t(igraph p.1 p.2)) (t(pgraph IO p.2))).

Definition check_point_wf (F1 F2 : graph2 -> term) (G : graph2) (x y : G) : 
  g_in != g_out :> G ->
  ~~ degenerate G -> 
  (forall H, measure H < measure G -> F1 H = F2 H) -> 
  check_point_term F1 x y = check_point_term F2 x y.
Admitted.


(* NOTE: we assume the input to be connected *)
Definition term_of_rec (term_of : graph2 -> term) (G : graph2) := 
  if g_in == g_out :> G
  then (* input equals output *)
    let E := [set e : edge G | (source e == g_in) && (target e == g_in)] in
    if 0 <= #|E| 
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
    if degenerate G
    then (* no checkpoints and no petals on i and o *)
      let Eio := [set e : edge G | (source e == g_in) && (target e == g_out)] in
      let Eoi := [set e : edge G | (source e == g_out) && (target e == g_in)] in
      if 0 < #|Eio :|: Eoi|
      then (* i and o are adjacent an we can remove some direct edges *)
        tmI (tmI (\big[tmI/tmT]_(e in Eio) tmA (label e))
                 (\big[tmI/tmT]_(e in Eio) tmC (tmA (label e))))
            (term_of (remove_edges (Eio :|: Eoi)))
      else (* i and o not adjacent - no progress unless G is K4-free *)
        \big[tmI/tmT]_(H <- split_par G) term_of H
    else (* at least one nontrivial petal or checkpoint *)
      @check_point_term term_of G g_in g_out
.


Definition term_of := Fix tmT term_of_measure term_of_rec.

Lemma term_of_eq (G : graph2) : 
  (* connected [set: skeleton G] -> K4_free (skeleton G) -> *)
  term_of G = term_of_rec term_of G.
Proof.
  (* move => con_G free_G. *)
  (* FIXME: Fix_eq needs to allow for conditions on the argument *)
  apply: Fix_eq => {G} F1 F2 G H.
  rewrite /term_of_rec. case: ifP.
Admitted.


Lemma term_of_iso (G : graph2) : 
  connected [set: skeleton G] ->  
  K4_free (sskeleton G) -> 
  iso2 G (graph_of_term (term_of G)).
Proof.
Admitted.
