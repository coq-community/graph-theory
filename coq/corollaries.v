From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries.
Require Import digraph sgraph minor.
Require Import mgraph_jar ptt mgraph2_tw2 mgraph2_jar skeleton.
Require Import extraction_def extraction_top.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

(** * Second Proof of Excluded-Minor Characterization *)

Corollary minor_exclusion_2p (sym : eqType) (G : graph2 sym) :
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

(** Remark: contrary to the textbook definition, we do not substract 1
in the definition of treewidth. Consequently, [width <= 3] means
treewidth two. *) 

Theorem graph_minor_TW2 (G : sgraph) :
  K4_free G <-> 
  exists (T : forest) (B : T -> {set G}), sdecomp T G B /\ width B <= 3.
Proof.
  split=> [| [T][B][]]; last exact: TW2_K4_free.
  case: (posnP #|G|) =>[G_empty | /card_gt0P[x _]].
  { exists tunit; exists (fun _ => [set: G]). split; first exact: triv_sdecomp.
    apply: leq_trans (width_bound _) _. by rewrite G_empty. }
  move=>HG.
  have [G' [iso_G _]] := flesh_out 0 x.
  apply (iso_K4_free iso_G) in HG.
  apply minor_exclusion_2p in HG as (T&B&D&W).
  case: (decomp_iso D iso_G) => B' D' W'.
  exists T. exists B'. by rewrite W'.
Qed.

Print Assumptions graph_minor_TW2.
