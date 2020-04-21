
(* Resolution of the Upper Weighted Irredundant Problem *)

From mathcomp Require Import all_ssreflect.
Require Import preliminaries digraph sgraph dom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


(** * Homomorphisms, isomorphisms and subgraphs. All "induced"! *)
(* TODO: Use the tools provided by sgraph.v instead of reinventing the wheel :)  *)

Section Basic_Facts_Induced_Homomorphism_Isomorphism.

Definition induced_hom (G1 G2 : sgraph) (h : G1 -> G2) :=
          forall x y : G1, x -- y <-> h x -- h y.

Definition induced_subgraph (G1 G2 : sgraph) :=
          exists2 h : G1 -> G2, injective h & induced_hom h.

Lemma induced_S_is_sub : forall (G : sgraph) (S : {set G}), induced_subgraph (induced S) G.
Proof.
  move=> G S.
  rewrite /induced_subgraph /induced_hom.
  exists val => // ; exact: val_inj.
Qed.

Definition isomorphic (G1 G2 : sgraph) := 
          exists2 f : G1 -> G2, (exists2 g : G2 -> G1, cancel f g & cancel g f) & induced_hom f.

Variables G1 G2 : sgraph.
Hypothesis iso_G1_G2 : isomorphic G1 G2.

Lemma sub_G1_G2 : induced_subgraph G1 G2.
Proof.
  elim: iso_G1_G2 => f.
  elim=> g can_f_g can_g_f hom_f.
  rewrite /induced_subgraph.
  exists f => //.
  exact: (can_inj can_f_g).
Qed.

Lemma iso_G2_G1 : isomorphic G2 G1.
Proof.
  elim: iso_G1_G2 => f.
  elim=> g can_f_g can_g_f hom_f.
  rewrite /isomorphic.
  exists g.
  exists f => //.
  rewrite /induced_hom => x y.
  set x' := g x.
  set y' := g y.
  by rewrite -(can_g_f x) -(can_g_f y) -/x' -/y' hom_f.
Qed.

Lemma induced_hom_bijective : exists h : G1 -> G2, bijective h.
Proof.
  elim: iso_G1_G2 => h.
  elim=> invh can_h_invh can_invh_h _.
  exists h.
  by exists invh.
Qed.

End Basic_Facts_Induced_Homomorphism_Isomorphism.

Lemma sub_G2_G1 : forall G1 G2 : sgraph, isomorphic G1 G2 -> induced_subgraph G2 G1.
Proof. move=> G1 G2 /iso_G2_G1 ; exact: sub_G1_G2. Qed.


(**********************************************************************************)
Section Newgraph_construction.

Variable G : sgraph.

Local Definition V' := [set x : G * G | x.1 -*- x.2].

Definition newgraph_type := sig [eta mem V'].

Definition newgraph_rel := [rel x y : newgraph_type | (val x != val y)
                                                   && (((val y).1 -*- (val x).2)
                                                   || ((val y).2 -*- (val x).1))].

Lemma newgraph_sym : symmetric newgraph_rel.
Proof.
  rewrite /symmetric /newgraph_rel /=.
  move=> x y.
  rewrite eq_sym.
  apply: andb_id2l => _.
  rewrite cl_sg_sym orbC.
  apply: orb_id2r => _.
  by rewrite cl_sg_sym.
Qed.

Lemma newgraph_irrefl : irreflexive newgraph_rel.
Proof. rewrite /irreflexive /newgraph_rel /= ; move=> x ; rewrite eq_refl //. Qed.

Definition newgraph := SGraph newgraph_sym newgraph_irrefl.

End Newgraph_construction.


(**********************************************************************************)
Section Upper_Weighted_Irredundant_Problem.

Variable G : sgraph.
Variable weight : G -> nat.
Hypothesis positive_weights : forall v : G, weight v > 0.

Let G' := newgraph G.
Let weight' := fun x : G' => weight (val x).1.

Lemma positive_weights' : forall v : G', weight' v > 0.
Proof. by rewrite /weight'. Qed.

Lemma G'_vertex_def : forall x : G', (exists u v : G, u -*- v).
Proof.
  move=> /= [x xinV'].
  exists x.1.
  exists x.2.
  move: xinV'.
  by rewrite in_set.
Qed.

Lemma G'_edge_def : forall x y : G', x -- y -> (exists u v w r : G,
          ([set u; v] != [set w; r]) /\ ((v -*- w) \/ (r -*- u))).
Proof.
  move=> [x xinV'] [y yinV'] /andP /= [x_neq_y /orP cond2_newgraph_rel].
  have pair_neq: (x.1 != y.1) \/ (x.2 != y.2).
  apply/orP; move: x_neq_y; apply/contraR.
  rewrite negb_or => /andP [/negPn/eqP x1_eq /negPn/eqP x2_eq].
  by apply/eqP/injective_projections.
  case: (boolP ((x.1 == y.2) && (x.2 == y.1))) => [/andP [/eqP x1_eq /eqP x2_eq] | neg_perm].
  - exists x.1.
  exists y.2.
  exists y.1.
  exists x.2.
  split.
  + case: pair_neq => [x1_neq | x2_neq].
  * rewrite -x1_eq x2_eq !pair_absorb.
  move: x1_neq; apply: contra_neq => set_eq.
  by apply/set1P; rewrite -set_eq in_set1.
  * rewrite x1_eq -x2_eq !pair_absorb.
  move: x2_neq; apply: contra_neq => set_eq.
  by apply/set1P; rewrite set_eq in_set1.
  + by left; rewrite /= in_set cl_sg_sym in yinV'.
  - exists x.1.
  exists x.2.
  exists y.1.
  exists y.2.
  split.
  + apply/contraT => doubleton_eq.
  move/doubleton_eq_iff: (eqP (negPn doubleton_eq)) => doubleton_eq_equiv.
  case: doubleton_eq_equiv => [[x1_eq x2_eq] | [x1_eq x2_eq]].
  * by case: pair_neq => [x1_neq | x2_neq]; [rewrite x1_eq eq_refl in x1_neq | rewrite x2_eq eq_refl in x2_neq].
  * by rewrite x1_eq x2_eq !eq_refl in neg_perm.
  + by case: cond2_newgraph_rel => [? | ?]; [left; rewrite cl_sg_sym | right].
Qed.

(* Alternative lemmas, not sure if necessary but gives an idea on how to manipulate things *)
Lemma G'_vertex_def' : forall x : G', (val x).1 -*- (val x).2.
Proof.
  move=> /= [x xinV'] /=.
  move: xinV'.
  by rewrite in_set.
Qed.

Lemma G'_edge_def' : forall x y : G', x -- y -> (val x != val y) /\
          ((val y).1 -*- (val x).2 \/ (val y).2 -*- (val x).1).
Proof. by move=> [x _] [y _] /andP /= [x_neq_y /orP cond2_newgraph_rel]. Qed.






(* Function h_vv maps a vertex v in G to its counterpart vv in G' *)
Section h_counterpart_definition.

  Variable v : G.

  Lemma vv_in_V' : (v, v) \in V' G.
  Proof. by rewrite /V' in_set /fst /snd cl_sg_refl. Qed.

  Definition h_vv := Sub (v, v) vv_in_V' : G'. (* i.e. {x : G * G | x \in V' G} *)

  Lemma h_vv1 : (val h_vv).1 = v.
  Proof. by rewrite /=. Qed.

  Lemma h_vv2 : (val h_vv).2 = v.
  Proof. by rewrite /=. Qed.

End h_counterpart_definition.

Theorem subgraph_G_G' : induced_subgraph G G'.
Proof.
  rewrite /induced_subgraph.
  exists h_vv.
  (* h_vv is injective *)
  rewrite /injective.
  move=> x y H1.
  move: (h_vv1 x) <-.
  move: (h_vv1 y) <-.
  by rewrite H1.
  (* h_vv is an induced homomorphism *)
  rewrite /induced_hom.
  move=> x y.
  set x' := h_vv x.
  set y' := h_vv y.
  rewrite /iff ; split.
  (* case x -- y -> x' -- y' *)
  move=> adjxy.
  suff: ((x, x) != (y, y)) && (y -*- x || y -*- x) by rewrite /=.
  apply/andP ; split.
  move: (negbT (sg_edgeNeq adjxy)).
  apply: contra => /eqP.
  rewrite pair_equal_spec => [[xeqy _]].
  by move: xeqy->.
  by rewrite orbb cl_sg_sym /cl_sedge adjxy orTb.
  (* case x' -- y' -> x -- y *)
  move=> adjx'y'.
  have H2: ((x, x) != (y, y)) && (y -*- x || y -*- x) by exact: adjx'y'.
  move/andP: H2 => [x'neqy'].
  rewrite orbb cl_sg_sym /cl_sedge => xdomy.
  have xneqy: x != y.
  move: x'neqy'.
  apply: contra.
  by move/eqP->.
  by rewrite (aorbNb xdomy xneqy).

(* Prueba de induced homomorphism de Mauricio:
  rewrite/iff ; split.
  (* first case: -> *)
  move=> adjxy.
  have H: newgraph_rel (h_vv x) (h_vv y).
  rewrite /newgraph_rel /=.
  apply/andP ; split.
  rewrite abeqcd negb_and orbb.
  move/sg_edgeNeq: adjxy.
  rewrite -[in X in X = false -> _](negbK (x == y)). (* Esto me costó bastante. Se puede simplificar? *)
  exact: negbFE.
  rewrite orbb /cl_sedge ; apply/orP/or_introl.
  by rewrite sg_sym.
  exact: H.
  (* second case: <- *)
  move=> h_xxadjh_yy.
  have H: newgraph_rel (h_vv x) (h_vv y) by exact: h_xxadjh_yy.
  rewrite /newgraph_rel /= in H.
  move: H => /andP [xneqy ydomx].
  rewrite abeqcd negb_and orbb in xneqy.
  rewrite orbb in ydomx.
  rewrite cl_sg_sym /cl_sedge in ydomx.
  move/aorbNb in ydomx.
  exact: (ydomx xneqy). *)
Qed.


(* Function h_vw maps a vertex v in D (an irredundant set) to (v,w) where w is one of its
 * private vertices *)
Section h_vertex_and_its_private_definition.

  Variable D : {set G}. 

  Hypothesis Dirr : irredundant D.

  Variable v : G.

  Hypothesis vinD : v \in D.

(* Alternative (that uses "pick"):

  Let w_opt := [pick u | private D v u].
  Let w := if w_opt is Some u then u else v.

  Local Lemma w_is_private : private D v w.
  Proof.
    rewrite /w /w_opt.
    case: pickP => [? ? | private_eq_pred0]; first by done.
    move/irredundantP: Dirr => /(_ v vinD) /(private_set_not_empty vinD).
    elim => u.
    by rewrite private_eq_pred0.
  Qed. *)


  Local Lemma w_exists : exists w : G, private D v w.
  Proof. by  move/irredundantP: Dirr => /(_ v vinD) /(private_set_not_empty vinD).
  Qed.

  Let w : G := xchoose w_exists.
  Let w_is_private : private D v w := xchooseP w_exists.

  Lemma vw_in_V' : (v, w) \in V' G.
  Proof.
    rewrite /V' in_set /=.
    move: w_is_private.
    rewrite /private.
    by move/andP=> [ vdomw _ ].
  Qed.

  Definition h_vw := Sub (v, w) vw_in_V' : G'. (* i.e. {x : G * G | x \in V' G} *)

  Lemma h_vw1 : (val h_vw).1 = v.
  Proof. by rewrite /=. Qed.

  Lemma h_vw2 : private D v (val h_vw).2.
  Proof. by rewrite /= w_is_private. Qed.

End h_vertex_and_its_private_definition.


(* For a given irredundant set D of G, there exists a stable set of G' such that w(D) = w'(G') *)
Theorem irred_G_to_stable_G' : forall D : {set G}, irredundant D ->
          exists2 S : {set G'}, stable S & weight_set weight D = weight_set weight' S.
Admitted.

(* For a given stable set S of G', there exists an irredundant set D of G such that w(D) = w'(G') *)
Theorem stable_G'_to_irred_G : forall S : {set G'}, stable S ->
          exists2 D : {set G}, irredundant D & weight_set weight D = weight_set weight' S.
Admitted.

(* Main theorem: the construction works! *)
Theorem IR_w_G_is_alpha_w_G' : IR_w G weight = alpha_w G' weight'.
Proof.
  apply/eqP; rewrite eqn_leq ; apply/andP ; split.
  (* case IR_w(G) <= alpha_w(G'):
     let F be an irredundant set of maximum weight, say M, i.e. M=IR_w(G)
     there exists a stable set S of weight M, then alpha_w(G') >= M *)
  set F := maximum_set weight (irredundant (G:=G)) set0.
  move: (@maximum_set_p G weight (irredundant (G:=G)) set0 (irr_empty G)).
  rewrite /alpha_w /IR_w -/F => Firr.
  move: (irred_G_to_stable_G' Firr).
  elim=> S Sst ->.
  move: (@maximum_set_welldefined G' weight' (stable (G:=G')) set0 (st_empty G')).
  move/maximumP => [_ set_is_max].
  exact: (set_is_max S Sst).

  (* case alpha_w(G') <= IR_w(G):
     let F be a stable set of maximum weight, say M, i.e. M=alpha_w(G')
     there exists an irred. set D of weight M, then IR_w(G) >= M *)
  set F := maximum_set weight' (stable (G:=G')) set0.
  move: (@maximum_set_p G' weight' (stable (G:=G')) set0 (st_empty G')).
  rewrite /alpha_w /IR_w -/F => Fst.
  move: (stable_G'_to_irred_G Fst).
  elim=> D Dirr <-.
  move: (@maximum_set_welldefined G weight (irredundant (G:=G)) set0 (irr_empty G)).
  move/maximumP => [_ set_is_max].
  exact: (set_is_max D Dirr).
Qed.

End Upper_Weighted_Irredundant_Problem.
