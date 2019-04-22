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

Opaque merge_def merge_seq.

Arguments unl [G H] x : simpl never.
Arguments unr [G H] x : simpl never.

Instance: RewriteRelation iso2.

Lemma iso_disconnected_component (G : graph2) (C : {set G}) (x : G) (iC : g_in \in ~: C) (oC : g_out \in ~: C) : 
  C \in components [set: skeleton G] -> x \in C ->
  point (union (component1 x) (induced (~: C))) 
        (inr (Sub g_in iC)) (inr (Sub g_out oC)) ≈ G.
Proof.
  move => comp_C xC.
  set G1 := _ x. set G2 := induced _. set GU := point _ _ _.
  pose hv (x : union G1 G2) := match x with inl x => val x | inr x => val x end.
  pose he (e : edge (union G1 G2)) := match e with inl e => val e | inr e => val e end.
  have decC z : (z \in @component_of G x) + (z \in ~: C)%type. 
  { admit. }
  pose gv (z : G) : GU := 
    match decC z with inl p => inl (Sub z p) | inr p => inr (Sub z p) end.
  have decE (e : edge G) :
    (e \in edge_set (@component_of G x)) + (e \in edge_set (~: C))%type.
  { admit. }
  pose ge (e : edge G) : edge GU := 
    match decE e with inl p => inl (Sub e p) | inr p => inr (Sub e p) end.
  apply: (@Iso2'' GU G hv gv he ge).
Admitted.  

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
  rewrite !h_union_merge_rEl !h_union_merge_rEr.
  set TGT := union _ (union G1 _). 
  pose k : pairs TGT := [:: (unl o2, unr (unl g_in))].  
  setoid_rewrite (merge_merge (G := TGT) (k := k)).
  2:{ by rewrite /= !h_union_merge_rEl h_union_merge_rEr. }
  simpl map_pairs. rewrite /k. simpl cat.
  rewrite /par2. 
  setoid_rewrite (merge_iso2 (union_merge_l _ _)).
  simpl map_pairs. rewrite /= !h_union_merge_lEl !h_union_merge_lEr.
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
    exact: iso_disconnected_component.
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
