From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries.
Require Import digraph sgraph minor.
Require Import multigraph ptt_algebra subalgebra ptt_graph skeleton.
Require Import extraction_def extraction_iso.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

(** * Second Proof of Excluded-Minor Characterization *)

(** TODO: This file should use extraction_top *)

Corollary minor_exclusion_2p (G : graph2) :
  connected [set: skeleton G] -> 
  K4_free (sskeleton G) <-> 
  exists (T : forest) (B : T -> {set G}), [/\ sdecomp T (sskeleton G) B & width B <= 3].
Proof.
  move => conn_G. split => [K4F_G|[T [B [B1 B2 B3]]]].
  - have [T [B] [B1 B2]] := (graph_of_TW2 (term_of G)).
    have I := term_of_iso (conj conn_G K4F_G). symmetry in I. apply sskel_iso2 in I.
    have [D D1 D2] := decomp_iso B1 I.
    exists T. exists D. by rewrite D2.
  - exact: TW2_K4_free B1 B2 B3. 
Qed.

(** Remark: contrary to the textbook definition, we do not substract 1
in the definition of treewidth. Consequently, [width <= 3] means
treewidth two. *) 

Theorem graph_minor_TW2 (G : sgraph) :
  K4_free G <-> 
  exists (T : forest) (B : T -> {set G}), sdecomp T G B /\ width B <= 3.
Proof.
  split=> [| [T][B][]]; last exact: TW2_K4_free.
  move: G. apply: (nat_size_ind (f := fun G : sgraph => #|G|)).
  move => G IH K4F_G. 
  case: (boolP (connectedb [set: G])) => /connectedP conn_G.
  - case: (posnP #|G|) =>[G_empty | /card_gt0P[x _]].
    { exists tunit; exists (fun _ => [set: G]). split; first exact: triv_sdecomp.
      apply: leq_trans (width_bound _) _. by rewrite G_empty. }
    have [G' [iso_Gs iso_G]] := flesh_out x.
    have conn_G' : connected [set: skeleton G'].
    { exact: iso_connected conn_G. }
    have M := minor_exclusion_2p conn_G'.  
    have K4F_G' : K4_free (sskeleton G').
    { exact: iso_K4_free K4F_G. }
    case/M : K4F_G' => T [B] [B1 B2]. 
    case: (decomp_iso B1 iso_Gs) => D D1 D2. exists T. exists D. by rewrite D2.
  - case/disconnectedE : conn_G => x [y] [_ _]. 
    rewrite restrictE; last by move => ?;rewrite !inE. move => Hxy.
    pose V := [set z | connect sedge x z].
    pose G1 := sgraph.induced V.
    pose G2 := sgraph.induced (~:V).
    have G_iso : diso (sjoin G1 G2) G.
    { apply: ssplit_disconnected => a b. rewrite !inE => H1. apply: contraNN => H2.
      apply: connect_trans H1 _. exact: connect1. }
    have [T1 [B1 [dec1 W1]]] : 
      exists (T : forest) (B : T -> {set G1}), sdecomp T G1 B /\ width B <= 3.
    { apply: IH. 
      - rewrite card_sig. apply: (card_ltnT (x := y)) => /=. by rewrite inE.
      - apply: subgraph_K4_free K4F_G. exact: sgraph.induced_sub. }
    have [T2 [B2 [dec2 W2]]] : 
      exists (T : forest) (B : T -> {set G2}), sdecomp T G2 B /\ width B <= 3.
    { apply: IH. 
      - rewrite card_sig. apply: (card_ltnT (x := x)) => /=. 
        by rewrite !inE negbK connect0.
      - apply: subgraph_K4_free K4F_G. exact: sgraph.induced_sub. }
    exists (tjoin T1 T2). 
    pose B' := (decompU B1 B2).
    have dec' := join_decomp dec1 dec2.
    have [B dec W] := decomp_iso dec' G_iso.
    exists B. rewrite W. split => //. 
    apply: leq_trans (join_width _ _) _. by rewrite geq_max W1 W2.
Qed.

Print Assumptions graph_minor_TW2.
