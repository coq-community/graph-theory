Require Import RelationClasses Morphisms Setoid Omega.

From mathcomp Require Import all_ssreflect.

Require Import edone finite_quotient preliminaries set_tac.
Require Import digraph sgraph minor checkpoint.
Require Import equiv mgraph_jar mgraph2_jar ptt mgraph2_tw2 skeleton.
Require Import bounded extraction_def extraction_iso.
Require Import separators.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs". 

Section ExtractionTop.
Variable sym : eqType.
Notation graph := (@graph sym).
Notation graph2 := (@graph2 sym).
Open Scope ptt_ops.


(** * Extraction from Disconnected Graphs *)

Arguments top2 [sym].
Arguments iso_id [sym G].
Arguments iso_two_swap [sym].
Arguments merge_union_K_ll [sym F K i o h] k.

Lemma iso2_TGT (G : graph2) : top · G · top ≈ point (union G top2) (inr g_in) (inr g_out).
Proof. 
  rewrite -> topL, topR => /=. 
  rewrite -> (iso_iso2 (iso_sym (union_A _ _ _))) => /=.
  rewrite -> (iso_iso2 (union_iso iso_id (iso_sym (iso_two_graph)))).
  by rewrite -> (iso_iso2 (union_iso iso_id (iso_two_swap))).
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


Lemma par_component (G : graph) (H : graph2) :
  par2 (point (union G top2) (inr g_in) (inr g_out)) H ≈ point (union G H) (inr g_in) (inr g_out).
Proof.
  rewrite -> parC. 
  rewrite /=/par2/=.
  rewrite -> (merge_iso2 (union_A _ _ _)) =>/=.
  pose k (x : @two_graph sym) : union H G := if ~~ x then (unl g_in) else (unl g_out).
  apply: iso2_comp. apply: (merge_union_K_ll k). 
  - by case. 
  - move => [|]; rewrite /k/=; apply/eqquotP; eqv. 
  - rewrite /k /=. 
    apply: iso2_comp. apply: merge_nothing; first by repeat constructor.
    by rewrite -> (iso_iso2 (union_C _ _)).
Qed.

Notation induced2 := component.

Lemma component_induced (G : graph2) (C : {set G}) (iC : g_in \in C) (oC : g_out \in C) : 
  component C = point (induced C) (Sub g_in iC) (Sub g_out oC).
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
  g_in \in ~: @component_of G x -> g_out \in ~: @component_of G x -> 
  G ≈ par2 (dot2 top2 (dot2 (component1 x) top2)) (component (~: @component_of G x)).
Proof. 
  move => iC oC. symmetry.
  rewrite (component_induced iC oC).
  set C := component_of _.
  rewrite /component1.
  set G1 := point _ _ _. set G2 := point _ _ _.
  change (top·(G1·top)∥G2 ≈ G). (* wasn't necessary before adding abstracting sym *)
  rewrite -> dot2A,iso2_TGT. simpl. rewrite -> par_component.
  rewrite /G1 /G2 /=.
  have comp_C : C \in @components G [set: G]. apply: component_of_components.
  apply: iso2_comp. apply: (iso_iso2 (iso_component comp_C)).
  rewrite /=. by rewrite -point_io.
Qed.

Lemma iso_disconnected_io (G : graph2) : 
  (forall x : G, (x \in @component_of G g_in) || (x \in @component_of G g_out)) -> 
  g_out \notin @component_of G g_in ->
  G ≈ dot2 (@component1 G g_in) (dot2 top2 (@component1 G g_out)). 
Proof.
  move => no_comp dis_io. symmetry.
  change ((@component1 G g_in)·(top2·(@component1 G g_out)) ≈ G).
  rewrite -> dot2A. rewrite -> iso2_GTG. 
  rewrite {1}/component1. rewrite /=.
  move: (in_component_of _) => I1. move: (in_component_of _) => I2.
  have E : @component_of G g_out = ~: @component_of G g_in.
  { apply/setP => z. rewrite inE. apply/idP/idP.
    - move => Z1. apply: contraNN dis_io => Z2.  
      by rewrite -(same_component Z2) (same_component Z1).
    - move/(_ z) : no_comp. by case: (z \in _). }
  rewrite E in I2 *. 
  move: (@component_of_components G g_in) => comp_i.
  rewrite -> (iso_iso2 (iso_component comp_i)) => /=. 
  by rewrite -point_io.
Qed.

Lemma CK4F_component (G : graph2) (x : G) :  
  K4_free (sskeleton G) -> CK4F (component1 x).
Proof.
  move => K4F_G. split => //. 
  - apply: connected_induced. exact: connected_component_of.
  - apply: subgraph_K4_free (sub_pointxx _) _. exact: induced_K4_free.
Qed.

Definition term_of_rec' (t : graph2 -> term sym) (G : graph2) := 
  if [pick x | (g_in \notin @component_of G x) && (g_out \notin @component_of G x)] is Some x
  then top · (term_of (component1 x) · top) ∥ t (induced2 (~: component_of x))
  else 
    if g_out \in @component_of G g_in 
    then term_of G
    else term_of (@component1 G g_in) · (top · term_of (@component1 G g_out)).


Definition term_of' := Fix top (fun G : graph2 => #|G|) term_of_rec'.

Lemma induced2_compN_small (G : graph2) (x : G) :
  g_in \notin @component_of G x -> g_out \notin @component_of G x -> 
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
  K4_free (sskeleton G) -> G ≈ graph_of_term (term_of' G).
Proof.
  pattern G. apply: (nat_size_ind (f := fun G : graph2 => #|G|)) => {G} G IH K4F_G.
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
      apply: connected_one_component (@component_of_components G g_in) _.
      apply/subsetP => x _. move/(_ x) : H. apply: contraFT => H.
      rewrite !(component_exchange x) H /=. by rewrite (same_component E).
Qed.

End ExtractionTop.
