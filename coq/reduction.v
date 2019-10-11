Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries bij equiv.
Require Export rewriting.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

(* preliminary isomorphisms (on arbitrary graphs) *)
Section prelim.
Variable L: labels.
Notation Le := (le L).
Notation Lv := (lv L). 
Notation graph := (graph L).  
Notation graph2 := (graph2 L).  

Lemma merge43 (a b c d: Lv):
  merge_seq (two_graph a b ⊎ two_graph c d) [:: (inl (inr tt), inr (inl tt))] ≃ two_graph2 a d ∔ mon2 b c.
Proof.
  etransitivity. refine (merge_iso (iso_sym (union_A _ _ _)) _).
  etransitivity. refine (merge_iso (union_iso iso_id (union_A _ _ _)) _). 
  etransitivity. refine (merge_iso (union_iso iso_id (union_C _ _)) _). 
  etransitivity. refine (merge_iso (union_A _ _ _) _).
  etransitivity. symmetry. refine (union_merge_r _ (G:=two_graph b c) [:: (inl tt, inr tt)]).
  apply union_iso. reflexivity. apply merge_two.
Defined.

Lemma union_merge_rE' (F G: graph) (l: pairs G) x:
  (@union_merge_r _ F G l)^-1 (\pi x) = match x with inl x => inl x | inr x => inr (\pi x) end.
Proof. case x=>?. Admitted.     (* not needed for now *)

Lemma merge43E a b c d x:
  merge43 a b c d (\pi x) =
  (match x with
   | inl (inl _) => inl (inl tt)
   | inr (inl _) => inr tt
   | inl (inr _) => inr tt
   | inr (inr _) => inl (inr tt)
   end).
Admitted.                       (* not needed for now (direct approach seems better) *)
Opaque merge43.

Lemma merge42 (a b c d: Lv):
  merge_seq (two_graph a b ⊎ two_graph c d)
            [:: (inl (inl tt), inr (inl tt)); (inl (inr tt), inr (inr tt))]
≃ two_graph2 (mon2 a c) (mon2 b d).
Proof.
  etransitivity. refine (merge_iso (iso_sym (union_A _ _ _)) _).
  etransitivity. refine (merge_iso (union_iso iso_id (union_C _ _)) _). 
  etransitivity. refine (merge_iso (union_iso iso_id (iso_sym (union_A _ _ _))) _). 
  etransitivity. refine (merge_iso (union_A _ _ _) _).
  etransitivity. refine (merge_iso (union_iso iso_id (union_C _ _)) _).
  simpl.
  etransitivity. symmetry. refine (@mgraph.merge_merge_seq _ _ [:: _] [:: _] _ _). reflexivity. simpl.
  etransitivity. symmetry. etransitivity. apply (merge_iso (union_merge_l (two_graph b d) (F:=two_graph a c) [:: (inl tt, inr tt)]) [:: (inr (inl tt), inr (inr tt))]).
  simpl. by rewrite !union_merge_lEr.
  etransitivity. symmetry. refine (union_merge_r _ (G:=two_graph b d) [:: (inl tt, inr tt)]).
  apply union_iso; apply merge_two. 
Defined.
Lemma merge42E a b c d x:
  merge42 a b c d (\pi x) = (match x with inl y | inr y => y end).
Proof.
  (* case x; case; case=>/=. *)
Admitted.                       (* not needed for now (direct approach seems better) *)
Opaque merge42.

Lemma two_edges (a b c d: Lv) (u v: Le):
  edge_graph a u b ⊎ edge_graph c v d
≃ (two_graph a b ⊎ two_graph c d) ∔ [inl (inl tt), u, inl (inr tt)] ∔ [inr (inl tt), v, inr (inr tt)].
Proof.
  etransitivity. apply (union_add_edge_l _ _ _ _). 
  etransitivity. apply (add_edge_iso (union_add_edge_r _ _ _ _) _ _ _).
  apply add_edge_C.
Defined.

Definition two_option_void: bij (option (void+void) + option (void+void)) (option (option ((void+void)+void))).
Proof.
  etransitivity. apply sum_option_r. apply option_bij.
  etransitivity. apply sum_bij. reflexivity. apply sumxU.
  etransitivity. apply sumxU. apply option_bij.
  symmetry. apply sumxU. 
Defined.

Lemma dot_edges (a b c d: Lv) (u v: Le):
  point (merge_seq (edge_graph a u b ⊎ edge_graph c v d) [:: (inl (inr tt), inr (inl tt))])
        (\pi inl (inl tt)) (\pi (inr (inr tt)))
≃2 two_graph2 a d ∔ mon2 b c ∔ [inl (inl tt), u, inr tt] ∔ [inr tt, v, inl (inr tt)].
Proof.
  unshelve Iso2
  (@merge_surj _
     (edge_graph a u b ⊎ edge_graph c v d) _
     (two_graph2 a d ∔ _ ∔ [_, u, _] ∔ [_, v, _])
     (fun x =>
        match x with
        | inl (inl _) => inl (inl tt)
        | inr (inr _) => inl (inr tt)
        | _ => inr tt
        end)
     (fun x =>
        match x with
        | inl (inl _) => inl (inl tt)
        | inl (inr _) => inr (inr tt)
        | inr tt => inl (inr tt)
        end)
     (two_option_void)
     _ _ _ _ _).
  6,7: apply merge_surjE.
  - apply kernel_eqv_clot.
    * by repeat constructor.
    * case=>[[[]|[]]|[[]|[]]]; case=>[[[]|[]]|[[]|[]]]//= _; eqv.
  - by repeat case. 
  - by repeat case.
  - by repeat case.
  - case; [case; case | case].
  (* Damien to Christian: how to let the bigops just compute? *)
Admitted.

(* same as [dot_edge], but with a compositional/convoluted proof 
   looks appealing, but the complexity is hidden in [merge43] and I still don't know how to prove [merge43E]
 *)
Lemma dot_edges' (a b c d: Lv) (u v: Le):
  point (merge_seq (edge_graph a u b ⊎ edge_graph c v d) [:: (inl (inr tt), inr (inl tt))])
        (\pi inl (inl tt)) (\pi (inr (inr tt)))
≃2 two_graph2 a d ∔ mon2 b c ∔ [inl (inl tt), u, inr tt] ∔ [inr tt, v, inl (inr tt)].
Proof.
  etransitivity. apply (merge_iso2 (two_edges _ _ _ _ _ _)). 
  etransitivity. apply (iso_iso2 (merge_add_edge _ _ _ _)). rewrite /= !merge_add_edgeE.
  etransitivity. apply (iso_iso2 (add_edge_iso (merge_add_edge _ _ _ _) _ _ _)). rewrite /= !merge_add_edgeE.
  etransitivity. apply (iso_iso2 (add_edge_iso (add_edge_iso (merge43 _ _ _ _) _ _ _) _ _ _)).
  by rewrite /= !merge43E.
Qed.    


Definition two_option_void': bij (option (void+void) + option (void+void)) (option (option (void+void))).
Proof.
  etransitivity. apply sum_option_r. apply option_bij.
  etransitivity. apply sum_bij. reflexivity. apply sumxU.
  apply sumxU. 
Defined.

Lemma par_edges (a b c d: Lv) (u v: Le):
  point (merge_seq (edge_graph a u b ⊎ edge_graph c v d)
                   [:: (inl (inl tt), inr (inl tt)); (inl (inr tt), inr (inr tt))])
        (\pi inl (inl tt)) (\pi (inr (inr tt)))
≃2 two_graph2 (mon2 a c) (mon2 b d) ∔ [inl tt, u, inr tt] ∔ [inl tt, v, inr tt].
Proof.
  unshelve Iso2
  (@merge_surj _
     (edge_graph a u b ⊎ edge_graph c v d) _
     (two_graph2 (mon2 a c) (mon2 b d) ∔ [_, u, _] ∔ [_, v, _])
     (fun x =>
        match x with
        | inl y => y
        | inr y => y
        end)
     (inl)
     (two_option_void')
     _ _ _ _ _ ).
  6,7: apply merge_surjE.
  - apply kernel_eqv_clot.
    * by repeat constructor.
    * case=>[[[]|[]]|[[]|[]]]; case=>[[[]|[]]|[[]|[]]]//= _; eqv.
  - by repeat case. 
  - by repeat case.
  - by repeat case.
  - case; case. 
  (* Damien to Christian: how to let the bigops just compute? *)
Admitted.

(* idem: same as [par_edges] with a compositional/convoluted proof *)
Lemma par_edges' (a b c d: Lv) (u v: Le):
  point (merge_seq (edge_graph a u b ⊎ edge_graph c v d)
                   [:: (inl (inl tt), inr (inl tt)); (inl (inr tt), inr (inr tt))])
        (\pi inl (inl tt)) (\pi (inr (inr tt)))
≃2 two_graph2 (mon2 a c) (mon2 b d) ∔ [inl tt, u, inr tt] ∔ [inl tt, v, inr tt].
Proof.
  etransitivity. apply (merge_iso2 (two_edges _ _ _ _ _ _)). 
  etransitivity. apply (iso_iso2 (merge_add_edge _ _ _ _)). rewrite /= !merge_add_edgeE.
  etransitivity. apply (iso_iso2 (add_edge_iso (merge_add_edge _ _ _ _) _ _ _)). rewrite /= !merge_add_edgeE.
  etransitivity. apply (iso_iso2 (add_edge_iso (add_edge_iso (merge42 _ _ _ _) _ _ _) _ _ _)).
  by rewrite /= !merge42E.
Qed.

End prelim.


(* algebraic operations preserve rewriting steps (for every pttdom algebra) *)
Section s.
Variable X: pttdom.
Notation test := (test X). 
Notation graph := (graph (pttdom_labels X)).
Notation graph2 := (graph2 (pttdom_labels X)).
Notation step := (@step X).
Notation steps := (@steps X).

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


(* reduction lemma (in the initial pttdom algebra of terms) *)
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

(* reduction lemma *)
Proposition reduce (u: term): steps (graph_of_term u) (graph_of_nf_term (nf u)).
Proof.
  induction u=>//=.
  - etransitivity. apply dot_steps; [apply IHu1|apply IHu2].
    case (nf u1)=>[a|a u b];
    case (nf u2)=>[c|c v d]=>/=.
    * apply isop_step. exists.
      etransitivity. apply dot2unit_r. apply add_vlabel2_unit. 
    * apply isop_step. exists.
      etransitivity. apply dot2unit_l.
      etransitivity. apply add_vlabel2_edge.
      apply edge_graph2_iso=>//. apply monC.
    * apply isop_step. exists. 
      etransitivity. apply dot2unit_r. apply add_vlabel2_edge. 
    * etransitivity. apply isop_step.
      2: etransitivity.
      2: apply one_step, (step_v2 (G:=two_graph2 a d) (inl tt) (inr tt) u [b·c] v).
      exists. apply dot_edges. 
      apply isop_step. exists.
      apply (add_edge2_iso' iso2_id).
      apply dot_eqv=>//. rewrite dotA. apply dot_eqv=>//. 

  - etransitivity. apply par_steps; [apply IHu1|apply IHu2].
    case (nf u1)=>[a|a u b];
    case (nf u2)=>[c|c v d]=>/=.
    * apply isop_step. exists. apply par2unitunit.
    * etransitivity. apply isop_step.
      2: etransitivity.
      2: apply one_step, (step_e0 (G:=unit_graph2 [c·(d·a)]) tt v).
      rewrite parC. exists. apply par2edgeunit.
      apply isop_step. exists.
      etransitivity. apply add_vlabel2_unit. apply unit_graph2_iso.
      admit.                    (* algebraic *)
    * etransitivity. apply isop_step.
      2: etransitivity.
      2: apply one_step, (step_e0 (G:=unit_graph2 [a·(b·c)]) tt u).
      exists. apply par2edgeunit.
      apply isop_step. exists.
      etransitivity. apply add_vlabel2_unit. apply unit_graph2_iso.
      admit.                    (* algebraic *)
    * etransitivity. apply isop_step.
      2: etransitivity.
      2: apply one_step, (step_e2 (G:=two_graph2 [a·c] [b·d]) (inl tt) (inr tt) u v).
      2: reflexivity. 
      exists. apply par_edges. 
      
  - etransitivity. apply cnv_steps, IHu. 
    case (nf u)=>[a|a v b]=>//=.
    apply isop_step. exists.
    etransitivity. refine (iso_iso2 (add_edge_rev _ _ _) _ _).
    simpl. rewrite /eqv'/=. symmetry. apply cnvI.
    simpl. symmetry. etransitivity. apply (add_edge2_iso (iso_iso2 (union_C _ _) _ _)).
    reflexivity. 
      
  - etransitivity. apply dom_steps, IHu. 
    case (nf u)=>[a|a v b]=>//=.
    etransitivity. apply one_step, (@step_v1 _ (unit_graph2 a) tt v b).
    apply isop_step. exists. 
    etransitivity. apply add_vlabel2_unit. apply unit_graph2_iso.
    admit.               (* algebraic *)
Admitted.

End s'.
