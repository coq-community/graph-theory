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

Lemma iso2_disconnected_component_aux (G : graph2) (C : {set G}) (x : G) (iC : g_in \in ~: C) (oC : g_out \in ~: C) : 
  C \in components [set: skeleton G] -> x \in C ->
  point (union (component1 x) (induced (~: C))) 
        (inr (Sub g_in iC)) (inr (Sub g_out oC)) ≈ G.
Proof.
  (* should follow with the lemma above -- if needed *)
Admitted.  

(** TODO: This is literally half of the proof of dot2A, use the lemma there *)
Lemma dot2_flatten_r (F G H : graph2) :
  F·(G·H)
≈ point (merge_seq (union F (union G H)) [:: (unl g_out,unr (unl g_in)) ; (unr (unl g_out), unr (unr g_in)) ])
        (\pi (unl g_in)) (\pi (unr (unr g_out))).
Proof.
  rewrite /=/dot2/=.
  rewrite -> (merge_iso2 (union_merge_r _ _)) =>/=.
  rewrite !union_merge_rEl !union_merge_rEr.
  rewrite -> (merge_merge (G:=union F (union G H))
                       (k:=[::(unl g_out,unr (unl g_in))])) =>//.
  apply merge_seq_same' => /=.
  apply eqv_clot_eq; leqv.
Qed.



Lemma iso2_disconnected_component (G : graph2) (C : {set G}) x : 
  C \in components [set: skeleton G] -> g_in \in ~: C -> g_out \in ~: C -> x \in C ->
  G ≈ par2 (dot2 top2 (dot2 (component1 x) top2)) (component (~: C)).
Proof. 
  move => comp_C iC oC xC. symmetry. rewrite (component_induced iC oC).
  pose i2 : two_graph := false.
  pose o2 : two_graph := true.
  
  move def_G1 : (_ x) => G1.
  move def_G2 : (point _ _ _) => G2. 
  rewrite /dot2/top2. 
  setoid_rewrite (merge_iso2 (union_merge_r _ _)). 
  rewrite !union_merge_rEl !union_merge_rEr.
  set TGT := union _ (union G1 _). 
  pose k : pairs TGT := [:: (unl o2, unr (unl g_in))].  
  setoid_rewrite (merge_merge (G := TGT) (k := k)).
  2:{ by rewrite /= !union_merge_rEl union_merge_rEr. }
  simpl map_pairs. rewrite /k. simpl cat.
  rewrite /par2. 
  setoid_rewrite (merge_iso2 (union_merge_l _ _)).
  simpl map_pairs. rewrite /= !union_merge_lEl !union_merge_lEr.
  set k1 := [:: _ ; _ ]. 
  set k2 := [:: _ ; _ ]. 
  set TGT2 := union TGT G2. 
  clear k.
  pose k : pairs TGT2 := [:: (unl (unl i2), unr g_in); (unl (unr (unr o2)), unr g_out)].
  apply: iso2_comp;[exact:(merge_merge (G := TGT2) (k := k))|]. (* setoid rewrite fails here *)
  rewrite /k1 /k /TGT2 /TGT /=.
  apply: iso2_comp. apply: (merge_iso2 (iso_sym (@union_A _ _ _))).
  rewrite /union_A /=.
  apply: iso2_comp. apply: (merge_iso2 (iso_sym (@union_C _ _))).
  rewrite /union_C /=. clear k.
  pose k (x : two_graph) : union (union G1 two_graph) G2 := 
    if ~~ x then unr g_in else unl (unl g_in).
  apply: iso2_comp. apply: merge_union_K_rl => //. instantiate (1 := k).
  { case; apply/eqquotP; rewrite /i2 /o2 /=; eqv. }
  apply: iso2_comp. apply: (merge_iso2 (iso_sym (@union_C _ _))).
  rewrite /union_C /=. clear k.
  apply: iso2_comp. apply: (merge_iso2 (@union_A _ _ _)).
  rewrite /union_A /=. 
  pose k (x : two_graph) : union G2 G1 := 
    if ~~ x then unr g_out else unl g_out.
  apply: iso2_comp. apply: merge_union_K_lr => //=. instantiate (1 := k).
  { case; apply/eqquotP; rewrite /i2 /o2 /=; eqv. }
  rewrite /k /=. 
  apply: iso2_comp. apply: (@merge_nothing (union G2 G1) _ (unl g_in) (unl g_out)).
  - repeat constructor.
  - setoid_rewrite (iso_iso2 (union_C _ _)) => //=.
    rewrite -def_G1 -def_G2.
    exact: iso2_disconnected_component_aux.
Qed.


Lemma iso_disconnected_io (G : graph2) : 
  (forall C, C \in components [set: skeleton G] -> (g_in \in C) || (g_out \in C)) ->
  @component_of G g_in != @component_of G g_out ->
  G ≈ dot2 (@component1 G g_in) (dot2 top2 (@component1 G g_out)). 
Admitted.

Lemma CK4F_component (G : graph2) (x : G) :  
  K4_free (sskeleton G) -> CK4F (component1 x).
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
     admit. (* partition blocks are nonempty *)
   + (* partition blocks are nonempty *) admit.
   + (* this is a subgraph of the input graph *) admit.
   + (* this is a subgraph of the input graph *) admit.
  - case: ifP.
    + rewrite /=. rewrite <- !term_of_iso; first apply: iso_disconnected_io.
      * move => C. admit. (* trivial *)
      * exact: CK4F_component.
      * exact: CK4F_component.
    + move/negbFE/eqP => E. apply: term_of_iso.
      (* a graph with only one component is connected ... *) admit.
Admitted.
