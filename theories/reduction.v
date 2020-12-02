Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries bij equiv.
Require Import setoid_bigop structures pttdom mgraph mgraph2 rewriting.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

(** * Reducibility for the rewrite system *)

(** ** Preliminary isomorphisms (on arbitrary graphs) *)
Section prelim.
Variable (Lv : comMonoid) (Le : elabelType).
Notation graph := (graph Lv Le).  
Notation graph2 := (graph2 Lv Le).
Local Open Scope cm_scope.

Lemma two_edges (a b c d: Lv) (u v: Le):
  edge_graph a u b ⊎ edge_graph c v d
≃ (two_graph a b ⊎ two_graph c d) 
  ∔ [inl (inl tt), u, inl (inr tt)] 
  ∔ [inr (inl tt), v, inr (inr tt)].
Proof.
  etransitivity. apply (union_add_edge_l _ _ _ _). 
  etransitivity. apply (add_edge_iso (union_add_edge_r _ _ _ _) _ _ _).
  apply add_edge_C.
Defined.

Definition two_option_void: 
  bij (option (void+void) + option (void+void)) (option (option ((void+void)+void))).
Proof.
  etransitivity. apply sum_option_r. apply option_bij.
  etransitivity. apply sum_bij. reflexivity. apply sumxU.
  etransitivity. apply sumxU. apply option_bij.
  symmetry. apply sumxU. 
Defined.


Lemma dot_edges (a b c d: Lv) (u v: Le):
  point (merge_seq (edge_graph a u b ⊎ edge_graph c v d) [:: (inl (inr tt), inr (inl tt))])
        (\pi inl (inl tt)) (\pi (inr (inr tt)))
≃2 two_graph2 a d ∔ (b⊗c) ∔ [inl (inl tt), u, inr tt] ∔ [inr tt, v, inl (inr tt)].
Proof.
  set G := (_ ⊎ _)%G.
  set H := (_ ∔ [_, _, _] ∔ [_,_,_])%G2.
  pose f (x : G) : H := match x with
        | inl (inl _) => inl (inl tt)
        | inr (inr _) => inl (inr tt)
        | _ => inr tt
        end.
  unshelve Iso2
  (@merge_surj _ _ G _ H f
     (fun x =>
        match x with
        | inl (inl _) => inl (inl tt)
        | inl (inr _) => inr (inr tt)
        | inr tt => inl (inr tt)
        end)
     (two_option_void) 
     xpred0 _ _ _).
  4,5: apply merge_surjE.
  - apply kernel_eqv_clot.
    * by repeat constructor.
    * case=>[[[]|[]]|[[]|[]]]; case=>[[[]|[]]|[[]|[]]]//= _; eqv.
  - by repeat case. 
  - split. 
    + by repeat case.
    + move => y. rewrite !big_sumType !big_unitType.
      by case: y ; [case; case | case]; rewrite /= ?monUl ?monU.
    + by repeat case.
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
≃2 two_graph2 (a⊗c) (b⊗d) ∔ [inl tt, u, inr tt] ∔ [inl tt, v, inr tt].
Proof.
  unshelve Iso2
  (@merge_surj _ _
     (edge_graph a u b ⊎ edge_graph c v d) _
     (two_graph2 (a⊗c) (b⊗d) ∔ [_, u, _] ∔ [_, v, _])
     (fun x =>
        match x with
        | inl y => y
        | inr y => y
        end)
     (inl)
     (two_option_void')
     xpred0 _ _ _ ).
  4,5: apply merge_surjE.
  - apply kernel_eqv_clot.
    * by repeat constructor.
    * case=>[[[]|[]]|[[]|[]]]; case=>[[[]|[]]|[[]|[]]]//= _; eqv.
  - by repeat case. 
  - split.
    + by repeat case.
    + move => y. rewrite !big_sumType !big_unitType.
      by case: y => [[]|[]] /=; rewrite ?monU ?monUl.
    + by repeat case.
Qed.

End prelim.


(** ** preservation of steps under algebraic operations *)
(* (for every pttdom algebra) *)
Section s.
Variable X: pttdom.
Notation test := (test X). 
Notation graph := (graph test X).
Notation graph2 := (graph2 test X).
Notation step := (@step X).
Notation steps := (@steps X).

(* preliminaries to obtain the technical Lemma 6.3 *)

Definition mentions (A: eqType) (l: pairs A) :=
  flatten [seq [::x.1;x.2] | x <- l].

Definition admissible_l (G: graph2) (H: eqType) (e : pairs (G+H)) :=
  all (fun x => if x is inl z then z \in IO else true) (mentions e).

Definition replace_ioL (G G': graph2) (H: eqType) (e : pairs (G+H)) : pairs (G'+H) := 
  map_pairs (fun x =>
               match x with 
               | inl z => if z == output then inl output else inl input
               | inr z => inr z
               end) e.
Arguments replace_ioL [G G' H].

Lemma replace_ioE vT eT1 eT2 st1 st2 lv1 lv2 le1 le2 i o H e : admissible_l e -> 
   @replace_ioL (point (@Graph _ _ vT eT1 st1 lv1 le1) i o) 
                (point (@Graph _ _ vT eT2 st2 lv2 le2) i o) H e = e.
Proof.
  elim: e => //=. case => [[a|a] [b|b]] l /= IH. 
  all: rewrite /admissible_l /=. all: first [case/and3P|case/andP|idtac].
  all: repeat (case/set2P => ->). all: move => HA; rewrite ?IH ?eqxx //.
  all: by case: (altP (i =P o)) => [->|?].
Qed.

Lemma cons_iso_steps G G' H : steps G' H -> G ≃2 G' -> steps G H.
Proof. intros E F. etransitivity. apply iso_step, F. assumption. Qed.

Lemma cons_step_steps G G' H : steps G' H -> step G G' -> steps G H.
Proof. intros E F. by setoid_rewrite F. Qed.

Lemma merge_add_edgeL (G H : graph) x y u l i o : 
   point (merge_seq (G ∔ [x,u,y] ⊎ H) l) (\pi i) (\pi o)
≃2 point (merge_seq (G ⊎ H) l) (\pi i) (\pi o) ∔ [\pi inl x,u,\pi inl y].
Proof.
  eapply iso2_comp.
  apply (iso_iso2' (h:=merge_iso (union_add_edge_l _ _ _ _) _)).
  1,2: by rewrite merge_isoE.
  eapply iso2_comp.
  refine (iso_iso2' (h:=merge_add_edge _ _ _ _) _ _).
  1,2: by rewrite merge_add_edgeE.
  unshelve refine (iso_iso2' (h:=add_edge_iso'' (h:=mgraph.merge_same _) _ _ _) _ _)=>/=.
  4: reflexivity. 
  by rewrite map_pairs_id.
  all: by rewrite merge_sameE. 
Defined.

(* TOFIX: even with Opaque merge_iso h_merge, the rewrite merge_add_edgeE 
   succeeds by unfolding if we don't do the rewrite merge_isoE first. *)
Lemma merge_add_edgeLE G H x y u l i o z:
  @merge_add_edgeL G H x y u l i o (\pi z) = (\pi z).
Proof.
  rewrite /merge_add_edgeL/=.
  rewrite (@merge_isoE _ _ _ _ (union_add_edge_l H x u y) l).
  rewrite merge_add_edgeE.
  by rewrite merge_sameE.
Qed.

Section a.
Variables (G H : graph2) (a: test) (l: pairs (add_vertex2 G a ⊎ H)%G).
Hypothesis A: admissible_l l. 
Lemma admissible_map  :
  map_pairs sumA (map_pairs (sumf id sumC) (map_pairs sumA' l)) =
  map_pairs inl (replace_ioL l).
Proof.
  rewrite 2!map_map_pairs. induction l as [|[a1 a2] q IH]=>//.
  simpl. move: A =>/andP[/=A1 /andP[/=A2 Q]]. f_equal. f_equal.
  destruct a1 as [[x|[]]|x]=>//=.
  case/set2P : A1 => [] [->]; rewrite sum_eqE ?eqxx //. by case: (altP (input =P output)) => [->|].
  exfalso. clear -A1. by rewrite !inE in A1.
  destruct a2 as [[x|[]]|x]=>//=.
  case/set2P : A2 => [] [->]; rewrite sum_eqE ?eqxx //. by case: (altP (input =P output)) => [->|].
  exfalso. clear -A2. by rewrite !inE in A2. 
  apply IH, Q. 
Qed.

Lemma merge_add_vertexL:
   point (merge_seq (G ∔ a ⊎ H) l) (\pi (inl (inl input))) (\pi (unr output))
≃2 point (merge_seq (G ⊎ H) (replace_ioL l)) (\pi (unl input)) (\pi (unr output)) ∔ a.
Proof.
  eapply iso2_comp.
  apply (iso_iso2' (h:=merge_iso (iso_sym (union_A _ _ _)) _)).
  1,2: rewrite merge_isoE//.
  eapply iso2_comp.
  refine (iso_iso2' (h:=merge_iso (union_iso iso_id (union_C _ _)) _) _ _).
  1,2: rewrite merge_isoE//.
  eapply iso2_comp.
  refine (iso_iso2' (h:=merge_iso (union_A _ _ _) _) _ _).
  1,2: rewrite merge_isoE//.
  eapply iso2_sym.
  eapply iso2_comp.
  refine (iso_iso2' (h:=union_merge_l _ _) _ _).
  1,2: rewrite union_merge_lEl//.
  eapply iso2_sym.  (* just so that [merge_add_vertexLE] gets easier below... *)
  apply merge_same'.
  by rewrite admissible_map.
Defined.

Lemma merge_add_vertexLE x:
  merge_add_vertexL (\pi (inl x)) =
  match x with inl x => inl (\pi inl x) | _ => inr tt end. 
Proof.
  simpl.
  rewrite (@merge_isoE _ _ _ _ (iso_sym (union_A G (unit_graph a) H)) l).
  rewrite (@merge_isoE _ _ _ _ (union_iso iso_id (union_C (unit_graph a) H)) _).
  rewrite (@merge_isoE _ _ _ _ (union_A G H (unit_graph a)) _).
  rewrite merge_same'E.
  rewrite union_merge_lE'. 
  by case x=>[y|[]].
Qed.

End a.

Definition merge_add_vlabelL (G H: graph2) x a l i o : 
   point (merge_seq (G[tst x <- a] ⊎ H) l) (\pi i) (\pi o)
≃2 point (merge_seq (G ⊎ H) l) (\pi i) (\pi o) [tst \pi inl x <- a].
Proof.
  eapply iso2_comp.
  apply (iso_iso2' (h:=merge_iso (union_add_vlabel_l _ _ _) _)).
  1,2: rewrite merge_isoE//.
  eapply iso2_comp.  
  refine (iso_iso2' (h:=merge_add_vlabel _ _ _) _ _).
  1,2: by rewrite merge_add_vlabelE.
  unshelve refine (iso_iso2' (h:=add_vlabel_iso'' (h:=mgraph.merge_same _) _ _) _ _)=>/=.
  3: reflexivity. 
  by rewrite map_pairs_id.
  all: by rewrite merge_sameE.
  (* this proof could be made simpler since we don't need to Defined it *)
Qed.

(** *** Lemma 6.3 *)
Lemma merge_step (G' G H: graph2) (l : pairs (G+H)) : 
  admissible_l l -> step G G' -> 
  steps (point (merge_seq (G ⊎ H) l) (\pi (unl input)) (\pi (unr output)))
        (point (merge_seq (G' ⊎ H) (replace_ioL l)) (\pi (unl input)) (\pi (unr output))).
Proof.
  move => A B. destruct B.
  - refine (cons_iso_steps _ (merge_add_vertexL A)).
    apply (one_step (step_v0 _ _)).
    
  - refine (cons_iso_steps _ (merge_add_edgeL _ _ _)).
    refine (cons_iso_steps _ (add_edge2_iso (merge_add_vertexL A) _ _ _)).
    rewrite 2!merge_add_vertexLE.
    refine (cons_step_steps _ (step_v1 _ _ _)).
    apply iso_step.
    symmetry. apply merge_add_vlabelL. 

  - refine (cons_iso_steps _ (merge_add_edgeL _ _ _)).
    refine (cons_iso_steps _ (add_edge2_iso (merge_add_edgeL _ _ _) _ _ _)).
    rewrite !merge_add_edgeLE.
    refine (cons_iso_steps _ (add_edge2_iso (add_edge2_iso (merge_add_vertexL A) _ _ _) _ _ _)).
    do 4 rewrite {1}merge_add_vertexLE.
    refine (cons_step_steps _ (step_v2 _ _ _ _ _)).
    apply iso_step.
    symmetry. apply merge_add_edgeL. 

  - refine (cons_iso_steps _ (merge_add_edgeL _ _ _)).
    refine (cons_step_steps _ (step_e0 _ _)).
    apply iso_step.
    etransitivity. symmetry. apply merge_add_vlabelL.
    by rewrite replace_ioE.
      
  - refine (cons_iso_steps _ (merge_add_edgeL _ _ _)).
    refine (cons_iso_steps _ (add_edge2_iso (merge_add_edgeL _ _ _) _ _ _)).
    rewrite !merge_add_edgeLE.
    refine (cons_step_steps _ (step_e2 _ _ _ _)).
    apply iso_step.
    etransitivity. symmetry. apply (merge_add_edgeL (u:=u∥v)).
    by rewrite replace_ioE.
Qed.

Lemma step_IO G G': step G G' -> (input == output :> G) = (input == output :> G').
Proof. by case. Qed.

Lemma step_to_steps f:
  Proper (eqv ==> eqv) f -> Proper (step ==> steps) f -> Proper (steps ==> steps) f.
Proof.
  intros If Sf G G' S.
  induction S as [G G' I|G G' F H' I S Ss IH].
  - by apply isop_step, If.
  - etransitivity. apply isop_step, If. exists. apply I.
    etransitivity. apply Sf, S. apply IH. 
Qed.


(** *** Lemma 6.2 *)

Instance cnv_steps: Proper (steps ==> steps) (cnv : graph2 -> graph2).
Proof.
  apply: step_to_steps.
  move=>F G S. eapply one_step. destruct S.
  * apply (@step_v0 _ (point G output input) alpha).
  * apply (@step_v1 _ (point G output input) x u alpha).
  * apply (@step_v2 _ (point G output input) x y u alpha v).
  * apply (@step_e0 _ (point G output input) x u).
  * apply (@step_e2 _ (point G output input) x y u v).
Qed.

Instance dom_steps: Proper (steps ==> steps) (@dom _).
Proof.
  apply: step_to_steps. 
  move=>F G S. eapply one_step. destruct S.
  * apply (@step_v0 _ (point G input input) alpha).
  * apply (@step_v1 _ (point G input input) x u alpha).
  * apply (@step_v2 _ (point G input input) x y u alpha v).
  * apply (@step_e0 _ (point G input input) x u).
  * apply (@step_e2 _ (point G input input) x y u v).
Qed.

Lemma dot_steps_l G G' H: steps G G' -> steps (G·H) (G'·H).
Proof.
  apply: (step_to_steps (f:=fun G => G·H)) => {G G'}. 
  - move => F G E. exact: dot_eqv.
  - move => G G' GG'. etransitivity. apply (@merge_step G') => //=.
    + rewrite /admissible_l/=. by rewrite !inE eqxx.
    + by rewrite /replace_ioL/= eqxx.
Qed.

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
  - move => G G' I; exact: par_eqv. 
  - move => G G' step_G_G'. 
    etransitivity. apply: (@merge_step G') => //=.
    + by rewrite /admissible_l/= !inE !eqxx.
    + rewrite /replace_ioL/= !eqxx. case: ifP => [E|//].
      rewrite (step_IO step_G_G') in E.
      by rewrite -[in (inl output,inr input)](eqP E).
Qed.

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

Lemma eqvEcnv (X : pttdom) (x y : X) : x ≡' y <-> x ≡ y°. 
Proof. done. Qed.

From HB Require Import structures.

(** ** reduction lemma *)
(* (in the initial pttdom algebra of terms) *)
Section s'.
Variable A: Type. 
Notation term := (pttdom.term A).  
Notation nterm := (pttdom.nterm A).
Notation test := (test (term_is_a_Pttdom A)). 
Notation tgraph2 := (graph2 test term).
Notation graph := (graph unit (flat A)).
Notation graph2 := (graph2 unit (flat A)).
Notation step := (@step (term_is_a_Pttdom A)).
Notation steps := (@steps (term_is_a_Pttdom A)).

(** *** graphs of terms and normal terms *)

(* function g^A from the end of Section 5 *)
Definition graph_of_term: term -> graph2 := pttdom.eval (fun a: flat A => g2_var _ a). 

(* function g^T from the end of Section 5 *)
Definition tgraph_of_term: term -> tgraph2 := pttdom.eval (fun a: A => g2_var _ (pttdom.tm_var a)).

Definition tgraph_of_nterm (t: nterm): tgraph2 :=
  match t with
  | nt_test a => unit_graph2 a
  | nt_conn a u b => edge_graph2 a u b
  end.

(* reduction lemma (Proposition 7.2) *)
Proposition reduce (u: term): steps (tgraph_of_term u) (tgraph_of_nterm (nt u)).
Proof.
  induction u=>//=.
  - etransitivity. apply dot_steps; [apply IHu1|apply IHu2].
    case (nt u1)=>[a|a u b];
    case (nt u2)=>[c|c v d]=>/=.
    * apply iso_step. 
      etransitivity. apply dot2unit_r. apply add_vlabel2_unit. 
    * apply iso_step. 
      etransitivity. apply dot2unit_l.
      etransitivity. apply add_vlabel2_edge.
      apply edge_graph2_iso=>//=. by apply: monC.
    * apply iso_step. 
      etransitivity. apply dot2unit_r. apply add_vlabel2_edge. 
    * etransitivity. apply isop_step.
      2: etransitivity.
      2: apply one_step, (step_v2 (G:=two_graph2 a d) (inl tt) (inr tt) u [elem_of b·elem_of c] v).
      exists. apply: dot_edges. 
      apply isop_step. exists.
      apply: (add_edge2_iso' iso2_id).
      by rewrite !dotA. 

  - etransitivity. apply par_steps; [apply IHu1|apply IHu2].
    case (nt u1)=>[a|a u b];
    case (nt u2)=>[c|c v d]=>/=.
    * apply isop_step. exists. apply par2unitunit.
    * etransitivity. apply isop_step.
      2: etransitivity.
      2: apply one_step, (step_e0 (G:=unit_graph2 (c⊗(d⊗a))%CM) tt v).
      rewrite parC. exists. apply: par2edgeunit. 
      apply isop_step. exists.
      etransitivity. apply add_vlabel2_unit. apply unit_graph2_iso.
      exact: reduce_shuffle.
    * etransitivity. apply isop_step.
      2: etransitivity.
      2: apply one_step, (step_e0 (G:=unit_graph2 (a⊗(b⊗c))%CM) tt u).
      exists. apply: par2edgeunit.
      apply isop_step. exists.
      etransitivity. apply add_vlabel2_unit. apply unit_graph2_iso.
      exact: reduce_shuffle.
    * etransitivity. apply isop_step.
      2: etransitivity.
      2: apply one_step, (step_e2 (G:=two_graph2 (a⊗c)%CM (b⊗d)%CM) (inl tt) (inr tt) u v).
      2: reflexivity. 
      exists. apply: par_edges. 
      
  - etransitivity. apply cnv_steps, IHu. 
    case (nt u)=>[a|a v b]=>//=.
    apply isop_step. exists.
    etransitivity. refine (iso_iso2 (add_edge_rev _ _ _) _ _). 
    rewrite eqvEcnv. symmetry. apply cnvI.
    simpl. symmetry. etransitivity. apply: (add_edge2_iso (iso_iso2 (union_C _ _) _ _)).
    reflexivity. 
      
  - etransitivity. apply dom_steps, IHu. 
    case (nt u)=>[a|a v b]=>//=.
    etransitivity. apply one_step, (@step_v1 _ (unit_graph2 a) tt v b).
    apply isop_step. exists. 
    etransitivity. apply add_vlabel2_unit. apply unit_graph2_iso.
    done. (* reflexivity fails ... *)
Qed.

End s'.
