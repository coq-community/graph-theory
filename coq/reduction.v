Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries bij equiv.
Require Export rewriting.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

Section s.
Variable X: pttdom.
Notation test := (test X). 
Notation graph := (graph (pttdom_labels X)).
Notation graph2 := (graph2 (pttdom_labels X)).
Notation step := (@step X).
Notation steps := (@steps X).


(* algebraic operations preserve rewriting steps *)

Lemma step_to_steps f:
  Proper (iso2prop ==> iso2prop) f -> Proper (step ==> steps) f -> Proper (steps ==> steps) f.
Proof.
  intros If Sf G G' S.
  induction S as [G G' I|G G' F H' I S Ss IH].
  - by apply isop_step, If.
  - etransitivity. apply isop_step, If. exists. apply I.
    etransitivity. apply Sf, S. apply IH. 
Qed.

Instance cnv_steps: Proper (steps ==> steps) (@cnv _).
Proof.
  apply step_to_steps. simpl. by apply cnv_eqv.
  move=>F G S. eapply one_step. destruct S.
  * apply (@step_v0 _ (point G output input) alpha).
  * apply (@step_v1 _ (point G output input) x u alpha).
  * apply (@step_v2 _ (point G output input) x y u alpha v).
  * apply (@step_e0 _ (point G output input) x u).
  * apply (@step_e2 _ (point G output input) x y u v).
Qed.

Instance dom_steps: Proper (steps ==> steps) (@dom _).
Proof.
  apply step_to_steps. by apply dom_eqv.
  move=>F G S. eapply one_step. destruct S.
  * apply (@step_v0 _ (point G input input) alpha).
  * apply (@step_v1 _ (point G input input) x u alpha).
  * apply (@step_v2 _ (point G input input) x y u alpha v).
  * apply (@step_e0 _ (point G input input) x u).
  * apply (@step_e2 _ (point G input input) x y u v).
Qed.

Lemma dot_steps_l G G' H: steps G G' -> steps (G·H) (G'·H).
Proof.
  apply (step_to_steps (f:=fun G => G·H)) => {G G'}.
  - move=> ?? E. apply dot_eqv=>//. 
  - move => G G' GG'. etransitivity. (* apply: (@steps_merge G') => //=. *)
    (* + rewrite /admissible_l/=. by rewrite !inE eqxx. *)
    (* + by rewrite /replace_ioL/= eqxx.  *)
Admitted.

Lemma dot_steps_r G G' H: steps G G' -> steps (H·G) (H·G').
Proof.
  move => GG'. rewrite dotcnv. transitivity ((G'°·H°)°). 
    by apply cnv_steps, dot_steps_l, cnv_steps.
    by rewrite -dotcnv. 
Qed.

Instance dot_steps: Proper (steps ==> steps ==> steps) (@dot _).
Proof.
  repeat intro. by etransitivity; [apply dot_steps_l | apply dot_steps_r].
Qed.

Lemma par_steps_l G G' H: steps G G' -> steps (G∥H) (G'∥H).
Proof.
  apply (step_to_steps (f:=fun G => (G∥H)))  => {G G'}. 
  - move => G G' I. apply par_eqv=>//. 
  - move => G G' step_G_G'. 
    (* etransitivity. apply: (@steps_merge G') => //=. *)
    (* + by rewrite /admissible_l/= !inE !eqxx. *)
    (* + rewrite /replace_ioL/= !eqxx. case: ifP => [E|//]. *)
    (*   rewrite (step_IO step_G_G') in E. *)
    (*   by rewrite -[in (inl output,inr input)](eqP E).  *)
Admitted.

Lemma par_steps_r G G' H: steps G G' -> steps (H∥G) (H∥G').
Proof.
  intro. rewrite parC. etransitivity. apply par_steps_l. eassumption.
  by rewrite parC. 
Qed.

Instance par_steps: Proper (steps ==> steps ==> steps) (@par _).
Proof.
  repeat intro. by etransitivity; [apply par_steps_l | apply par_steps_r].
Qed.


End s.

Section s'.
Variable A: Type.
Notation term := (term A).  
Notation nf_term := (nf_term A).  
Notation test := (test (tm_pttdom A)). 
Notation graph := (graph (pttdom_labels (tm_pttdom A))).
Notation graph2 := (graph2 (pttdom_labels (tm_pttdom A))).
Notation step := (@step (tm_pttdom A)).
Notation steps := (@steps (tm_pttdom A)).


(* TODO: get rid of this hack... *)
Canonical Structure tm_labels :=
  @Labels (pttdom_test_setoid (tm_pttdom A)) (tst_one (tm_pttdom A)) (@tst_dot (tm_pttdom A))
         (@tst_dot_eqv (tm_pttdom A)) (@tst_dotA (tm_pttdom A)) (@tst_dotC (tm_pttdom A))
         (@tst_dotU (tm_pttdom A)) (tm_setoid A) (@eqv' (tm_pttdom A))
         (@eqv'_sym (tm_pttdom A)) (@eqv10 (tm_pttdom A)) (@eqv01 (tm_pttdom A)) (@eqv11 (tm_pttdom A)).
(* Eval hnf in pttdom_labels (tm_pttdom A). *)
(* Check erefl: tm_setoid A = le _. *)
(* Check erefl: tm_setoid A = setoid_of_bisetoid _.   *)

(* graphs of terms and normal forms *)
Definition graph_of_term: term -> graph2 := eval (fun a: A => g2_var (tm_var a)). 

Definition graph_of_nf_term (t: nf_term): graph2 :=
  match t with
  | nf_test a => unit_graph2 a
  | nf_conn a u b => edge_graph2 a u b
  end.


(* Some of these isomorphism lemma could be slight generalisations of lemmas
   used to get the pttdom laws on graph2 *)
Lemma ldotunit (G: graph2) a: G · unit_graph2 a ≃2p G [tst output <- a].
Admitted.

Lemma lunitdot (G: graph2) a: unit_graph2 a · G ≃2p G [tst input <- a].
Admitted.

Lemma lparunitunit (a b: test): unit_graph2 a ∥ unit_graph2 b ≃2p unit_graph2 [a·b].
Admitted.

Lemma lparedgeunit (u: term) (a b c: test): edge_graph2 a u b ∥ unit_graph2 c ≃2p unit_graph2 [c∥a·u·b].
Admitted.
       
Lemma add_test_point (a c: test) (x: unit): unit_graph2 a [tst x <- c] ≃2p unit_graph2 [a·c].
Admitted.                       (* could be inlined for now *)

Lemma add_test_edge (u: term) (a b c: test) (x: unit+unit):
  edge_graph2 a u b [tst x <- c] ≃2p edge_graph2 (if x then [c·a] else a) u (if x then b else [b·c]).
Admitted.

(* reduction lemma *)
Proposition reduce (u: term): steps (graph_of_term u) (graph_of_nf_term (nf u)).
Proof.
  induction u=>//=.
  - etransitivity. apply dot_steps; [apply IHu1|apply IHu2].
    case (nf u1)=>[a|a u b];
    case (nf u2)=>[c|c v d]=>/=.
    * apply isop_step.
      rewrite ldotunit. simpl.
      apply add_test_point. 
    * apply isop_step.
      rewrite lunitdot. simpl.
      apply add_test_edge. 
    * apply isop_step.
      rewrite ldotunit. simpl.
      apply add_test_edge. 
    * etransitivity. apply isop_step.
      2: etransitivity.
      2: apply one_step, (step_v2 (G:=two_graph2 a d) (inl tt) (inr tt) u [b·c] v).
      2: apply isop_step.
      exists.
      rewrite /g2_dot.
      etransitivity. apply (merge_iso2 (union_add_edge_l _ _ _ _)).
      etransitivity. apply (merge_iso2 (add_edge_iso (union_add_edge_r _ _ _ _) _ _ _)).
      etransitivity. apply (iso_iso2 (merge_add_edge _ _ _ _)).
      (* 2: liso_step (bij_sym unit_option_void)=>/=. *)
      (* 2: liso bij_id bij_id (fun _ => false)=>//= _; by rewrite !dotA. *)
      (* liso_step merge43=>/=.  *)
      (* liso_step two_option_option_void=>/=. *)
      (* liso bij_id bij_id (fun _ => false)=>//=; *)
      (*      (repeat case)=>//=; *)
      (*      rewrite ?merge43E ?merge43E' //=. *)
      admit.
      admit.
      
  - etransitivity. apply par_steps; [apply IHu1|apply IHu2].
    case (nf u1)=>[a|a u b];
    case (nf u2)=>[c|c v d]=>/=.
    * apply isop_step. apply lparunitunit.
    * apply isop_step. rewrite parC. apply lparedgeunit.
    * apply isop_step. apply lparedgeunit.
    * etransitivity. apply isop_step.
      2: etransitivity.
      2: apply one_step, (step_e2 (G:=two_graph2 [a·c] [b·d]) (inl tt) (inr tt) u v).
      admit.
      apply isop_step.
      (* liso_step (bij_sym unit_option_void)=>/=.  *)
      (* liso bij_id bij_id (fun _ => false)=>//. *)
      admit.
      
  - etransitivity. apply cnv_steps, IHu. 
    case (nf u)=>[a|a v b]=>//=.
    apply isop_step.
    (* rewrite /lcnv/=. liso bool_swap bij_id (fun _ => true)=>//=. *)
    (*   by case. *)
    (*   move=>_. apply cnvI. *)
    admit.
      
  - etransitivity. apply dom_steps, IHu. 
    case (nf u)=>[a|a v b]=>//=.
    etransitivity. apply iso_step.
    2: etransitivity. 2: apply one_step, (@step_v1 _ (unit_graph2 a) tt v b).
    (* liso_step bool_option_unit=>/=.  *)
    (* liso_step unit_option_void=>/=. *)
    (* liso bij_id bij_id (fun _ => false)=>//=; case=>//. *)
    (* apply liso_step. *)
    (* liso bij_id bij_id (fun _ => false)=>//=; case=>//. *)
    (* apply dotC.  *)
Admitted.

End s'.
