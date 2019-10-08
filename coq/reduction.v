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
Notation graph := (graph test (car (setoid_of_ops (ops X)))).
Notation graph2 := (graph2 test (car (setoid_of_ops (ops X)))).
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
Notation graph := (graph test term).
Notation graph2 := (graph2 test term).
Notation step := (@step (tm_pttdom A)).
Notation steps := (@steps (tm_pttdom A)).


(* TODO: get rid of this hack... *)
Canonical Structure tm_bisetoid :=
  @BiSetoid (tm_setoid A) (@eqv' (tm_pttdom A))
            (@eqv'_sym (tm_pttdom A))
            (@eqv10 (tm_pttdom A)) (@eqv01 (tm_pttdom A)) (@eqv11 (tm_pttdom A)).
(* we would be slightly happier with the following declaration, but Eval hnf does not simplify enough... *)
(* Canonical Structure tm_bisetoid := Eval hnf in pttdom_bisetoid (tm_pttdom A). *)
(* following command should work 
   Check erefl: tm_setoid A = setoid_of_bisetoid _.  
 *)

(* graphs of terms and normal forms *)
Definition graph_of_term: term -> graph2 := eval (fun a => g2_var _ (tm_var a)). 

Definition graph_of_nf_term (t: nf_term): graph2 :=
  match t with
  | nf_test a => point (unit_graph _ a) tt tt
  | nf_conn a u b => point (edge_graph a u b) false true
  end.


(* Some of these isomorphism lemma could be slight generalisations of lemmas
   used to get the pttdom laws on graph2 *)
Lemma ldotunit (G: graph2) a: G · point (unit_graph _ a) tt tt ≃2p G [tst output <- a].
Admitted.

Lemma lunitdot (G: graph2) a: point (unit_graph _ a) tt tt · G ≃2p G [tst input <- a].
Admitted.

Lemma lparunitunit (a b: test):
  point (unit_graph term a) tt tt ∥ point (unit_graph _ b) tt tt
  ≃2p point (unit_graph _ [a·b]) tt tt.
Admitted.

Lemma lparedgeunit (u: term) (a b c: test):
  point (edge_graph a u b) false true ∥ point (unit_graph _ c) tt tt
  ≃2p point (unit_graph _ [c∥a·u·b]) tt tt.
Admitted.
       
Lemma add_test_point (a c: test):
  point (unit_graph term a) tt tt [tst tt <- c]
  ≃2p point (unit_graph _ [a·c]) tt tt.
Admitted.                       (* could be inlined for now *)

Lemma add_test_edge (x: bool) (u: term) (a b c: test):
  point (edge_graph a u b) false true [tst x <- c]
  ≃2p point (edge_graph (if x then a else [c·a]) u (if x then [b·c] else b)) false true.
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
      2: apply one_step, (step_v2 (G:=point (two_graph _ a d) false true) false true u [b·c] v).
      2: apply isop_step.
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
      2: apply one_step, (step_e2 (G:=point (two_graph _ [a·c] [b·d]) false true) false true u v).
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
    2: etransitivity. 2: apply one_step, (@step_v1 _ (point (unit_graph _ a) tt tt) tt v b).
    (* liso_step bool_option_unit=>/=.  *)
    (* liso_step unit_option_void=>/=. *)
    (* liso bij_id bij_id (fun _ => false)=>//=; case=>//. *)
    (* apply liso_step. *)
    (* liso bij_id bij_id (fun _ => false)=>//=; case=>//. *)
    (* apply dotC.  *)
Admitted.

End s'.
