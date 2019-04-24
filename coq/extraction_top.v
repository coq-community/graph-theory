Require Import RelationClasses Morphisms Setoid Omega.

From mathcomp Require Import all_ssreflect.

Require Import edone finite_quotient preliminaries.
Require Import digraph sgraph minor checkpoint.
Require Import equiv multigraph ptt_graph ptt_algebra subalgebra skeleton.
Require Import bounded extraction_def extraction_iso.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs". 

Local Hint Resolve partition_components.

Definition component_of (G : sgraph) (x : G) := pblock (components [set: G]) x.

Lemma in_component_of (G : sgraph) (x : G) : x \in component_of x.
Proof. by rewrite mem_pblock (cover_partition (D := setT)). Qed.

Lemma component_of_components (G : sgraph) (x : G) : 
  component_of x \in components [set: G].
Proof. by rewrite pblock_mem // (cover_partition (D := setT)). Qed.
  
Definition component1 (G : graph) (x : G) := 
  point (induced (@component_of (skeleton G) x)) 
        (Sub x (@in_component_of (skeleton G) x)) 
        (Sub x (@in_component_of (skeleton G) x)).

Definition graph2_of_set (G : graph) (C : {set G}) : graph2 := 
  if [pick x in C] is Some x then component1 x else one2.

Lemma edge_component (G : graph) (e : edge G) :
  @component_of (skeleton G) (source e) = @component_of (skeleton G) (target e).
Proof. 
  apply: same_pblock => //.
  admit.
  admit.
Admitted.

Notation induced2 := component.

Definition term_of_rec' (t : graph2 -> term sym) (G : graph2) := 
  if [pick C in components [set: skeleton G] | (g_in \notin C) && (g_out \notin C)] is Some C 
  then top · (term_of (graph2_of_set C) · top) ∥ t (induced2 (~: C))
  else 
    if @component_of G g_in != @component_of G g_out 
    then term_of (@component1 G g_in) · (top · term_of (@component1 G g_out))
    else term_of G.

Lemma component_induced (G : graph2) (C : {set G}) (iC : g_in \in C) (oC : g_out \in C) : 
  component C = point (induced C) (Sub g_in iC) (Sub g_out oC).
Admitted.

Definition term_of' := Fix top (fun G : graph2 => #|G|) term_of_rec'.

Lemma term_of_rec_eq' (f g : graph2 -> term sym) (G : graph2) :
  (forall H : graph2, #|H| < #|G| -> f H = g H) -> term_of_rec' f G = term_of_rec' g G.
Proof.
  move => Efg. rewrite /term_of_rec'. case: pickP => [C /and3P [C1 C2 C3]|//].
  - admit.
Admitted.

Lemma term_of_eq' G : term_of' G = term_of_rec' term_of' G.
Proof. 
  apply Fix_eq with (fun _ => True) => // f g x _ H. 
  by apply: term_of_rec_eq'; auto. 
Qed.

Opaque merge.

Arguments unl [G H] x : simpl never.
Arguments unr [G H] x : simpl never.

Require Import set_tac.

Lemma component_closed (G : sgraph) (C U : {set G}) x y:
  C \in components U -> x \in C -> y \in U -> x -- y -> y \in C.
Admitted.

Lemma edge_set_component (G : graph) (U C : {set skeleton G}) (e : edge G) : 
  C \in components U -> (source e \in C) = (target e \in C).
Admitted.
Arguments edge_set_component [G U C e].

(* if C is a component, this becomes an equivalence *)
Lemma edge_setN (G : graph) (C : {set G}) (e : edge G):
  e \in edge_set C -> e \notin edge_set (~: C).
Admitted.

Lemma edge_comp (G : graph) (C : {set G}) (e : edge G):
  C \in components [set: skeleton G] ->
  (e \in edge_set C) + (e \in edge_set (~: C))%type.
Proof. 
  move => comp_C. case: (boolP (source e \in C)) => p; [left|right].
  - by rewrite inE -(edge_set_component comp_C) p.
  - by rewrite !inE -(edge_set_component comp_C) p.
Qed.

Section IsoComponents.
Variables (G : graph) (C : {set G}).
(* TODO: suffices that there is no edge between [C] and [~:C] *)
Hypothesis comp_C : C \in components [set: skeleton G].
Let G1 := induced C.
Let G2 := induced (~: C).

Lemma decC z : (z \in C) + (z \in ~: C)%type. 
Proof. case: (boolP (z \in C)) => p; [by left|right]. by rewrite inE p. Qed.

Lemma decE (e : edge G) : (e \in edge_set C) + (e \in edge_set (~: C)).
Proof. exact: edge_comp. Qed.

Definition component_v (x : union G1 G2) := match x with inl x => val x | inr x => val x end.
Definition component_v' (z : G) : union G1 G2 := 
    match decC z with inl p => inl (Sub z p) | inr p => inr (Sub z p) end.

Definition component_e (e : edge (union G1 G2)) := match e with inl e => val e | inr e => val e end.
Definition component_e' (e : edge G) : edge (union G1 G2) := 
    match decE e with inl p => inl (Sub e p) | inr p => inr (Sub e p) end.

Lemma component_can_v : cancel component_v component_v'.
Proof.
  case => a; rewrite /component_v/component_v'; case: (decC _) => p. 
  - congr inl. exact: val_inj.
  - exfalso. move: (valP a) => /= X. by rewrite inE X in p.
  - exfalso. move: (valP a) => /=. by rewrite inE p.
  - congr inr. exact: val_inj.
Qed.

Lemma component_can_v' : cancel component_v' component_v.
Proof. by move => x; rewrite /component_v/component_v'; case: (decC x). Qed.

Lemma component_can_e : cancel component_e component_e'.
Proof. 
  case => e; rewrite /component_e/component_e'; case: (decE _) => p.
  - congr inl. exact: val_inj.
  - exfalso. move: (valP e) => /= /edge_setN X. by contrab.
  - exfalso. move: (valP e) => /= X. move/edge_setN in p. by rewrite X in p.
  - congr inr. exact: val_inj. 
Qed.

Lemma component_can_e' : cancel component_e' component_e.
Proof. move => x; rewrite /component_e/component_e'; by case (decE _). Qed.

Lemma component_hom : is_hom component_v component_e.
Proof. repeat split; by case. Qed.

Definition iso_component : iso (union (induced C) (induced (~: C))) G := 
  Eval hnf in Iso' component_can_v component_can_v' component_can_e component_can_e' component_hom.

End IsoComponents.

Definition topR := A11'.
Lemma topL (F : graph2) : 
  top·F ≡ (point (union F unit_graph)) (unr (tt:unit_graph)) (unl g_out).
Admitted.

Lemma iso_two_swap : iso two_graph two_graph.
apply (@Iso' two_graph two_graph negb negb (fun e => match e with end) (fun e => match e with end)). 
all: try abstract by case. 
abstract (repeat split; case).
Defined.

Lemma topC : top2 ≡ top°.
Proof. rewrite /top2. by rewrite -> (iso_iso2 iso_two_swap). Admitted.

Lemma iso2TGT (G : graph2) : top · G · top ≈ point (union G top2) (inr g_in) (inr g_out).
Proof. 
  rewrite -> topL, topR => /=. 
  rewrite -> (iso_iso2 (iso_sym (union_A _ _ _))) => /=.
  rewrite -> (iso_iso2 (union_iso iso_id (iso_sym (iso_two_graph)))).
  by rewrite -> (iso_iso2 (union_iso iso_id (iso_two_swap))).
Qed.

Arguments merge_union_K_ll [F K i o h] k.

Lemma par_component (G : graph) (H : graph2) :
  par2 (point (union G top2) (inr g_in) (inr g_out)) H ≈ point (union G H) (inr g_in) (inr g_out).
Proof.
  rewrite -> parC. 
  rewrite /=/par2/=.
  rewrite -> (merge_iso2 (union_A _ _ _)) =>/=.
  pose k (x : two_graph) : union H G := if ~~ x then (unl g_in) else (unl g_out).
  apply: iso2_comp. apply: (merge_union_K_ll k). 
  - by case. 
  - move => [|]; rewrite /k/=; apply/eqquotP; eqv. 
  - rewrite /k /=. 
    apply: iso2_comp. apply: merge_nothing; first by repeat constructor.
    by rewrite -> (iso_iso2 (union_C _ _)).
Qed.

Lemma component1E (G : graph) (C : {set G}) x (xC :  x \in C) :
  C \in components [set: skeleton G] -> 
  component1 x = point (induced C) (Sub x xC) (Sub x xC).
Admitted.

Lemma iso2_disconnected_component (G : graph2) (C : {set G}) x : 
  C \in components [set: skeleton G] -> g_in \in ~: C -> g_out \in ~: C -> x \in C ->
  G ≈ par2 (dot2 top2 (dot2 (component1 x) top2)) (component (~: C)).
Proof. 
  move => comp_C iC oC xC. symmetry.
  rewrite (component_induced iC oC).
  rewrite (component1E xC comp_C).
  set G1 := point _ _ _. set G2 := point _ _ _.
  rewrite -> dot2A,iso2TGT. rewrite -> par_component.
  rewrite /G1 /G2 /=.
  apply: iso2_comp. apply: (iso_iso2 (iso_component comp_C)).
  rewrite /=. by rewrite -point_io.
Qed.

Lemma iso2_GTG (G H : graph2) : 
  G · top · H ≈ point (union G H) (unl g_in) (unr g_out).
Proof.
  rewrite -> topR. 
  rewrite /=/dot2/=. 
  rewrite -> (merge_iso2 (iso_sym (union_A _ _ _))) => /=.
  rewrite -> (merge_iso2 (union_iso iso_id (union_C _ _))) => /=.
  rewrite -> (merge_iso2 (union_A _ _ _)) => /=.
  apply: iso2_comp. apply: (merge_union_K_ll (fun _ : unit_graph => unr g_in)). 
  - done.
  - case. apply/eqquotP. by eqv.
  - rewrite /=. apply: merge_nothing. by repeat constructor.
Qed.

Lemma iso_disconnected_io (G : graph2) : 
  (forall C, C \in components [set: skeleton G] -> (g_in \in C) || (g_out \in C)) ->
  @component_of G g_in != @component_of G g_out ->
  G ≈ dot2 (@component1 G g_in) (dot2 top2 (@component1 G g_out)). 
Proof.
  move => no_comp dis_io. symmetry.
  rewrite -> dot2A. rewrite -> iso2_GTG. 
  rewrite {1}/component1. rewrite /=.
  move: (in_component_of _) => I1. move: (in_component_of _) => I2.
  have E : @component_of (skeleton G) g_out = ~: @component_of (skeleton G) g_in.
  { admit. }
  rewrite E in I2 *. 
  move: (@component_of_components G g_in) => comp_i.
  rewrite -> (iso_iso2 (iso_component comp_i)) => /=. 
  by rewrite -point_io.
Admitted.

Lemma CK4F_component (G : graph2) (x : G) :  
  K4_free (sskeleton G) -> CK4F (component1 x).
Admitted.

Lemma components_nonempty (G : sgraph) (U C : {set G}) :
  C \in components U -> exists x, x \in C.
Admitted.

Lemma connected_one_component (G : sgraph) (U C : {set G}) :
  C \in components U -> U \subset C -> connected U.
Admitted.

Theorem term_of_iso' (G : graph2) : 
  K4_free (sskeleton G) -> G ≈ graph_of_term (term_of' G).
Proof.
  pattern G. apply: (nat_size_ind (f := fun G : graph2 => #|G|)) => {G} G IH K4F_G.
  rewrite term_of_eq' /term_of_rec'. case: pickP => [C /and3P [C1 C2 C3]|H].
  - rewrite /=. rewrite <- term_of_iso, <- IH.
   + rewrite /graph2_of_set. 
     case: pickP => [x xC|/=]; first apply: iso2_disconnected_component.
     all: rewrite ?inE //.
     move => H. exfalso. 
     case: (components_nonempty C1) => x inC. move/(_ x) : H. by rewrite inC.
   + rewrite /= card_sub. apply: proper_card. apply/properP; split => //. 
     * exact/subsetP. 
     * case: (components_nonempty C1) => x inC. exists x => //. rewrite !inE inC orbF.
       by apply: contraTN inC => /orP[] /eqP ->.
   + rewrite /induced2. apply: subgraph_K4_free K4F_G. 
     exact: sskeleton_subgraph_for. 
   + rewrite /graph2_of_set. case: pickP => [x inC|_].
     * exact: CK4F_component.
     * exact: CK4F_one.
  - case: ifP.
    + rewrite /=. rewrite <- !term_of_iso; first apply: iso_disconnected_io.
      * move => C comp_C. move/(_ C): H. rewrite comp_C. 
        apply: contraFT. by rewrite negb_or.
      * exact: CK4F_component.
      * exact: CK4F_component.
    + move/negbFE/eqP => E. apply: term_of_iso. split => //.
      apply: connected_one_component (@component_of_components G g_in) _.
      apply/subsetP => x _. apply: wlog_neg => W. exfalso.
      move/(_ (component_of x)) : H. rewrite component_of_components.
      (* a graph with only one component is connected ... *) admit.
Admitted.

(*
(** TODO: This is literally half of the proof of dot2A, use the lemma there *)
Lemma dot2_flatten_r (F G H : graph2) :
  F·(G·H)
≈ point (merge_seq (union F (union G H)) [:: (unl g_out,unr (unl g_in)) ; (unr (unl g_out), unr (unr g_in)) ])
        (\pi (unl g_in)) (\pi (unr (unr g_out))).
Admitted. (* works but slow *)
Proof.
  rewrite /=/dot2/=.
  rewrite -> (merge_iso2 (union_merge_r _ _)) =>/=.
  rewrite !union_merge_rEl !union_merge_rEr.
  rewrite -> (merge_merge (G:=union F (union G H))
                       (k:=[::(unl g_out,unr (unl g_in))])) =>//.
  apply merge_seq_same' => /=.
  apply eqv_clot_eq; leqv.
Qed.
*)