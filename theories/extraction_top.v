Require Import RelationClasses Morphisms Setoid Omega.

From mathcomp Require Import all_ssreflect.

Require Import edone finite_quotient preliminaries set_tac.
Require Import digraph sgraph treewidth minor checkpoint.
Require Import equiv structures pttdom ptt mgraph mgraph2 ptt mgraph2_tw2 skeleton.
Require Import bounded extraction_def extraction_iso.
Require Import excluded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs". 

Section ExtractionTop.
Variable sym : Type.
Notation graph := (graph (flat_labels sym)).
Notation graph2 := (graph2 (flat_labels sym)).
Open Scope ptt_ops.


(** * Extraction from Disconnected Graphs *)

Arguments iso_id {L G}.
Arguments merge_union_K_l [L F K i o h] k.

Lemma iso2_TGT (G : graph2) : top · G · top ≃2 point (G ⊎ g2_top _) (inr input) (inr output).
Proof. 
  rewrite-> topL, topR => /=. 
  Iso2 (iso_sym (union_A _ _ _)).
Qed.

Lemma iso2_GTG (G H : graph2) : 
  G · top · H ≃2 point (G ⊎ H) (unl input) (unr output).
Proof.
  rewrite-> topR. 
  setoid_rewrite-> (merge_iso2 (iso_sym (union_A _ _ _))) => /=.
  setoid_rewrite-> (merge_iso2 (union_iso iso_id (union_C _ _))) => /=.
  rewrite-> (merge_iso2 (union_A _ _ _)) => /=.
  rewrite-> (merge_union_K_l (fun _ => unr input))=>//. 
  2: case; apply/eqquotP; by eqv.
  apply: merge_nothing. by repeat constructor.
Qed.

Lemma par_component (G : graph) (H : graph2) :
  point (G ⊎ g2_top _) (inr input) (inr output) ∥ H ≃2 point (G ⊎ H) (inr input) (inr output).
Proof.
  rewrite-> par2C. 
  setoid_rewrite-> (merge_iso2 (union_A _ _ _)) =>/=.
  rewrite-> (merge_union_K_l (fun x: two_graph _ _ => if x then unl input else unl output))=>//=.
  setoid_rewrite-> (merge_iso2 (union_C _ _)) =>/=.
  apply merge_nothing. by repeat constructor. by case.
  move => [[]|[]] /=; apply/eqquotP; eqv. 
Qed.

Notation induced2 := component.

Lemma component_induced (G : graph2) (C : {set G}) (iC : input \in C) (oC : output \in C) : 
  component C = point (induced C) (Sub input iC) (Sub output oC).
Proof.
  rewrite /induced2. move: (setU11 _ _) => A. move: (setU1r _ _) => B. move: A B.
  rewrite (setU1_mem oC) (setU1_mem iC) => A B. 
  by rewrite (bool_irrelevance A iC) (bool_irrelevance B oC).
Qed.

Definition component1 (G : graph) (x : G) := 
  point (induced (@component_of (skeleton G) x)) 
        (Sub x (@in_component_of (skeleton G) x)) 
        (Sub x (@in_component_of (skeleton G) x)).


Lemma iso2_disconnected_component (G : graph2) x : 
  input \in ~: @component_of G x -> output \in ~: @component_of G x -> 
  G ≃2 top · (component1 x · top) ∥ component (~: @component_of G x).
Proof. 
  move => iC oC. symmetry.
  rewrite (component_induced iC oC).
  set C := component_of _.
  rewrite /component1.
  set G1 := point _ _ _. set G2 := point _ _ _.
  rewrite -> dot2A,iso2_TGT. simpl. setoid_rewrite -> par_component.
  rewrite /G1 /G2 /=.
  have comp_C : C \in @components G [set: G]. apply: component_of_components.
  Iso2 (iso_component comp_C).
Qed.

Lemma iso_disconnected_io (G : graph2) : 
  (forall x : G, (x \in @component_of G input) || (x \in @component_of G output)) -> 
  output \notin @component_of G input ->
  G ≃2 @component1 G input · (top · @component1 G output). 
Proof.
  move => no_comp dis_io. symmetry.
  rewrite -> dot2A. rewrite -> iso2_GTG. 
  rewrite {1}/component1. rewrite /=.
  move: (in_component_of _) => I1. move: (in_component_of _) => I2.
  have E : @component_of G output = ~: @component_of G input.
  { apply/setP => z. rewrite inE. apply/idP/idP.
    - move => Z1. apply: contraNN dis_io => Z2.  
      by rewrite -(same_component Z2) (same_component Z1).
    - move/(_ z) : no_comp. by case: (z \in _). }
  rewrite E in I2 *. 
  move: (@component_of_components G input) => comp_i.
  Iso2 (iso_component comp_i).
Qed.

Lemma CK4F_component (G : graph2) (x : G) :  
  K4_free (sskeleton G) -> CK4F (component1 x).
Proof.
  move => K4F_G. split => //. 
  - apply: connected_induced. exact: connected_component_of.
  - apply: subgraph_K4_free (sub_pointxx _) _. exact: induced_K4_free.
Qed.

Definition term_of_rec' (t : graph2 -> term sym) (G : graph2) := 
  if [pick x | (input \notin @component_of G x) && (output \notin @component_of G x)] is Some x
  then top · (term_of (component1 x) · top) ∥ t (induced2 (~: component_of x))
  else 
    if output \in @component_of G input 
    then term_of G
    else term_of (@component1 G input) · (top · term_of (@component1 G output)).

Definition term_of' := Fix top (fun G : graph2 => #|G|) term_of_rec'.

Lemma induced2_compN_small (G : graph2) (x : G) :
  input \notin @component_of G x -> output \notin @component_of G x -> 
  #|induced2 (~: @component_of G x)| < #|G|.
Proof.
  move => X1 X2. rewrite /= card_sub. apply: proper_card. apply/properP; split => //. 
  - exact/subsetP. 
  - exists x => //. rewrite !inE (@in_component_of G) orbF. 
    apply/negP => /orP[] /eqP ?; subst; by rewrite (@in_component_of G) in X1 X2.
Qed.

Lemma term_of_rec_eq' (f g : graph2 -> term sym) (G : graph2) :
  (forall H : graph2, #|H| < #|G| -> f H = g H) -> term_of_rec' f G = term_of_rec' g G.
Proof.
  move => Efg. rewrite /term_of_rec'. case: pickP => [x /andP [X1 X2]|//].
  rewrite Efg //. exact: induced2_compN_small. 
Qed.

Lemma term_of_eq' G : term_of' G = term_of_rec' term_of' G.
Proof. 
  apply Fix_eq with (fun _ => True) => // f g x _ H. 
  by apply: term_of_rec_eq'; auto. 
Qed.

Theorem term_of_iso' (G : graph2) : 
  K4_free (sskeleton G) -> G ≃2 graph_of_term (term_of' G).
Proof.
  elim/card_ind : G => G IH K4F_G.
  rewrite term_of_eq' /term_of_rec'. case: pickP => [x /andP [X1 X2]|H].
  - rewrite /=. rewrite <- term_of_iso, <- IH.
   + apply: iso2_disconnected_component; by rewrite inE.
   + exact: induced2_compN_small. 
   + apply: subgraph_K4_free K4F_G. exact: sskeleton_subgraph_for. 
   + exact: CK4F_component.
  - case: ifP; last first.
    + move/negbT => io.
      rewrite /=. rewrite <- !term_of_iso; first apply: iso_disconnected_io => //.
      * move => x. move/(_ x) : H. apply: contraFT. rewrite negb_or.
        by rewrite !(@component_exchange G x).
      * exact: CK4F_component.
      * exact: CK4F_component.
    + move => E. apply: term_of_iso. split => //.
      apply: connected_one_component (@component_of_components G input) _.
      apply/subsetP => x _. move/(_ x) : H. apply: contraFT => H.
      rewrite !(component_exchange x) H /=. by rewrite (same_component E).
Qed.

Corollary minor_exclusion_2p (G : graph2) :
  K4_free (sskeleton G) <-> 
  exists (T : forest) (B : T -> {set G}), [/\ sdecomp T (sskeleton G) B & width B <= 3].
Proof.
  split => [K4F_G|[T [B [B1 B2 B3]]]].
  - have [T [B] [B1 B2]] := (graph_of_TW2 (term_of' G)).
    have I := term_of_iso' K4F_G. symmetry in I. apply sskel_iso2 in I.
    have [D D1 D2] := decomp_iso B1 I.
    exists T. exists D. by rewrite D2.
  - exact: TW2_K4_free B1 B2 B3. 
Qed.

End ExtractionTop.

(** Remark: contrary to the textbook definition, we do not substract 1
in the definition of treewidth. Consequently, [width <= 3] means
treewidth two. *) 

Corollary graph_minor_TW2 (G : sgraph) :
  K4_free G <-> 
  exists (T : forest) (B : T -> {set G}), sdecomp T G B /\ width B <= 3.
Proof.
  split=> [| [T][B][]]; last exact: TW2_K4_free.
  case: (posnP #|G|) =>[G_empty | /card_gt0P[x _]].
  { exists tunit; exists (fun _ => [set: G]). split; first exact: triv_sdecomp.
    apply: leq_trans (width_bound _) _. by rewrite G_empty. }
  move=>HG.
  have [G' [iso_G _]] := flesh_out (L:=flat_labels nat) 0 tt x.
  apply (iso_K4_free iso_G) in HG.
  apply minor_exclusion_2p in HG as (T&B&D&W).
  case: (decomp_iso D iso_G) => B' D' W'.
  exists T. exists B'. by rewrite W'.
Qed.

Print Assumptions graph_minor_TW2.
