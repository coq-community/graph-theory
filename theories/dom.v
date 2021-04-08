From mathcomp Require Import all_ssreflect.
Require Import preliminaries digraph sgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(**********************************************************************************)
(** * Domination Theory                                                           *)
(**********************************************************************************)
(** ** Hereditary and superhereditary properties *)
Section Hereditary.
Variable (T : finType).

Implicit Types (p : pred {set T}) (F D : {set T}).

Definition hereditary p : bool := [forall (D : {set T} | p D), forall (F : {set T} | F \subset D), p F].

Definition superhereditary p : bool := hereditary [pred D | p (~: D)].

Proposition hereditaryP p : 
  reflect (forall D F : {set T}, (F \subset D) -> p D -> p F) (hereditary p).
Proof.
  apply: (iffP forall_inP) => [H1 D F FsubD pD|H2 D pD].
  - exact: (forall_inP (H1 _ pD)).
  - apply/forall_inP => F FsubD; exact: H2 pD.
Qed.

Proposition superhereditaryP (p : pred {set T}) : 
  reflect (forall D F : {set T}, (D \subset F) -> p D -> p F) (superhereditary p).
Proof.
  apply: (iffP (hereditaryP _)) => /= sh_p D F.
  all: by rewrite -setCS => /sh_p; rewrite ?setCK; auto.
Qed.

Proposition maximal_indsysP p D : hereditary p ->
  reflect (p D /\ forall v : T, v \notin D -> ~~ p (v |: D)) (maxset p D).
Proof. 
  move/hereditaryP => p_hereditary; apply: (iffP maxset_properP).
  - case => pD maxD; split => // v vD. apply: maxD.
    by rewrite setUC properUl // sub1set. 
  - case => pD max1D; split => // A /properP [subA [v vA /max1D vD]].
    apply: contraNN vD; apply: p_hereditary; by rewrite subUset sub1set vA.
Qed.

Proposition minimal_indsysP p D : superhereditary p ->
  reflect (p D /\ forall v : T, v \in D -> ~~ p (D :\ v)) (minset p D).
Proof.
  rewrite minmaxset => sh_p; apply: (iffP (maximal_indsysP _ _)) => //=.
  all: rewrite ?setCK => -[pD H]; split => // v; move: (H v).
  all: by rewrite !inE ?setCU ?setCK ?negbK setDE setIC.
Qed.

End Hereditary.

(** ** Weighted Sets *)

Section Weighted_Sets.
Variables (T : finType) (weight : T -> nat).
Implicit Types (A B S : {set T}) (p : pred {set T}).

Definition weight_set (S : {set T}) := \sum_(v in S) weight v.
Let W := weight_set.

Lemma leqwset A B : A \subset B -> W A <= W B.
Proof. move=> AsubB ; by rewrite [X in _ <= X](big_setID A) /= (setIidPr AsubB) leq_addr. Qed.

Hypothesis positive_weights : forall v : T, weight v > 0.

Lemma wset0 A : (A == set0) = (W A == 0).
Proof.
  apply/eqP/eqP.
  - move=> Dempty ; rewrite /weight_set.
    move: Dempty ->. exact: big_set0.
  - move=> /eqP weightzero.
    apply/eqP ; move: weightzero.
    apply: contraLR => /set0Pn. elim=> x xinD.
    apply: lt0n_neq0 ; rewrite /W /weight_set (bigD1 x) //=.
    exact/ltn_addr/positive_weights.
Qed.

Lemma ltnwset A B :  A \proper B -> W A < W B.
Proof.
  move => /properP [AsubB].
  elim=> x xinB xnotinA.
  rewrite {2}/W /weight_set (big_setID A) /= (setIidPr AsubB).
  rewrite -[X in X <= _]addn0 addSn -addnS leq_add2l lt0n.
  rewrite -/(weight_set _) -wset0. 
  by apply/set0Pn; exists x; apply/setDP.
Qed.

(* Sets of minimum/maximum weight *)

Lemma maxweight_maxset p A : p A -> (forall B, p B -> W B <= W A) -> maxset p A.
Proof.
  move => pA maxA. apply/maxset_properP; split => // B /ltnwset; rewrite ltnNge.
  exact/contraNN/maxA.
Qed.

Lemma minweight_minset p A : p A -> (forall B, p B -> W A <= W B) -> minset p A.
Proof.
  move => pA minA; apply/minset_properP; split => // B /ltnwset; rewrite ltnNge.
  exact/contraNN/minA.
Qed.

Lemma arg_maxset p A : p A -> maxset p (arg_max A p W).
Proof. by move => pA; apply/maxweight_maxset; case: arg_maxnP. Qed.

Lemma arg_minset p A : p A -> minset p (arg_min A p W).
Proof. by move => pA ; apply/minweight_minset; case: arg_minnP. Qed.

End Weighted_Sets.


Section Domination_Theory.

Variable G : sgraph.

(** ** Stable, Dominating and Irredundant Sets *)
Section Stable_Set.

Variable S : {set G}.

Definition stable : bool := [disjoint NS(S) & S].

Local Lemma stableP_alt :
  reflect {in S&, forall u v, ~~ u -- v} [forall u in S, forall v in S, ~~ (u -- v)].
Proof. apply: equivP (in11_in2 S S). do 2 (apply: forall_inPP => ?). exact: idP. Qed.

Lemma stableEedge : stable = [forall u in S, forall v in S, ~~ (u -- v)].
Proof.
  symmetry ; rewrite /stable ; apply/stableP_alt/disjointP => stS.
  - move => x /bigcupP [y yS adjyx] xS. 
    move: adjyx. rewrite in_opn. apply/negP. by apply: stS.
  - move => x y xS yS. apply/negP => adjxy.
    exact: (stS y (mem_opns xS adjxy) yS).
Qed.

Proposition stableP : reflect {in S&, forall u v, ~~ u -- v} stable.
Proof. rewrite stableEedge ; exact: stableP_alt. Qed.

Proposition stablePn : reflect (exists x y, [/\ x \in S, y \in S & x -- y]) (~~ stable).
Proof.
  rewrite stableEedge.
  set E := exists _, _.
  have EE : (exists2 x, x \in S & exists2 y, y \in S & x -- y) <-> E by firstorder.
  rewrite !negb_forall_in; apply: equivP EE; apply: exists_inPP => x.
  rewrite negb_forall_in; apply: exists_inPP => y. exact: negPn.
Qed.

End Stable_Set.

(* the empty set is stable *)
Lemma stable0 : stable set0.
Proof. by apply/stableP=> ? ? ; rewrite in_set0. Qed.

(* if D is stable, any subset of D is also stable *)
Lemma st_hereditary : hereditary stable.
Proof.
  apply/hereditaryP.
  move=> D F FsubD /stableP Dstable.
  apply/stableP => u v uinF vinF.
  move: (subsetP FsubD u uinF) => uinD.
  move: (subsetP FsubD v vinF) => vinD.
  exact: Dstable.
Qed.


(**********************************************************************************)
Section Dominating_Set.

Variable D : {set G}.

Definition dominating : bool := [forall v, v \in NS[D]].

Local Lemma dominatingP_alt : reflect
  (forall v : G, v \notin D -> exists2 u : G, u \in D & u -- v)
  [forall (v | v \notin D), exists u in D, u -- v].
Proof. apply: forall_inPP => v; exact: exists_inP. Qed.

Lemma dominatingEedge : dominating = [forall (v | v \notin D), exists u in D, u -- v].
Proof.
  apply/forallP/forall_inP => [H v vND |H v].
  - have [u udomv] := bigcupP (H v).
    rewrite in_cln; case/predU1P => [?|uv]; first by subst;contrab.
    by apply/exists_inP; exists u.
  - case: (boolP (v \in D)) => [|/H/exists_inP[u uD uv]]; last exact: mem_clns uv.
    exact/subsetP/set_sub_clns.
Qed.

Proposition dominatingP : reflect
  (forall v : G, v \notin D -> exists2 u : G, u \in D & u -- v) dominating.
Proof. rewrite dominatingEedge; apply/dominatingP_alt. Qed.

Lemma dominatingPn : 
  reflect (exists2 v : G, v \notin D & {in D, forall u, ~~ u -- v}) (~~ dominating).
Proof.
  rewrite dominatingEedge negb_forall_in.
  apply: exists_inPP => x; exact: exists_inPn.
Qed.

End Dominating_Set.

(* V(G) is dominating *)
Lemma domT : dominating [set: G].
Proof. apply/forallP => x. exact: (subsetP (set_sub_clns _)). Qed.

(* if D is dominating, any supraset of D is also dominating *)
Lemma dom_superhereditary : superhereditary dominating.
Proof.
  apply/superhereditaryP => D F /subsetP DsubF /dominatingP Ddom.
  apply/dominatingP => v vnotinF. 
  have/Ddom [w winD wv]: v \notin D by apply: contraNN vnotinF; exact: DsubF.
  exists w => //; exact: DsubF.
Qed.

(**********************************************************************************)
Section Irredundant_Set.

Variable D : {set G}.
Implicit Types x y v w : G.

Definition private_set (v : G) := N[v] :\: NS[D :\ v].

Lemma privateP v w : 
  reflect (v -*- w /\ {in D, forall u, u -*- w -> u = v}) (w \in private_set v).
Proof. 
  apply: (iffP setDP); rewrite !in_cln => -[v_dom_w H]; split => //.
  - move => u inD u_dom_w; apply: contraNeq H => uDv.
    apply/bigcupP; exists u; by [exact/setD1P|rewrite in_cln].
  - apply/negP => /bigcupP [u /setD1P [uDv /H]]. rewrite in_cln => X {}/X.
    exact/eqP.
Qed.

Definition irredundant : bool := [forall v : G, (v \in D) ==> (private_set v != set0)].

Proposition irredundantP: reflect {in D, forall v, (private_set v != set0)} irredundant.
Proof.
  rewrite /irredundant ; apply: (iffP forallP).
  - move=> H1 v vinD. by move/implyP: (H1 v) => /(_ vinD).
  - move=> H2 v. apply/implyP=> vinD. by move: (H2 v vinD).
Qed.

Proposition irredundantPn : reflect (exists2 v, v \in D & private_set v == set0) (~~ irredundant).
Proof.
  rewrite /irredundant ; apply: (iffP forall_inPn) ; last first.
  - case => x xinD H1. by exists x ; rewrite ?xinD ?H1.
  - case => x xinD H2; rewrite negbK in H2. by exists x.
Qed.

End Irredundant_Set.

(* the empty set is irredundant *)
Lemma irr0 : irredundant set0.
Proof. apply/irredundantP => v ; by rewrite in_set0. Qed.

(* if D is irredundant, any subset of D is also irredundant *)
Lemma irr_hereditary : hereditary irredundant.
Proof.
  apply/hereditaryP.
  move=> D F FsubD /irredundantP Dirr.
  apply/irredundantP => v vinF.
  move: (subsetP FsubD v vinF) => vinD.
  move: (Dirr v vinD).
  case/set0Pn => x /privateP [vdomx H1]. apply/set0Pn; exists x.
  apply/privateP ; split=> //.
  move=> u uinF udomx. move: (subsetP FsubD u uinF) => uinD.
  exact: (H1 u uinD udomx).
Qed.

(** ** Fundamental facts about Domination Theory *)
Section Relations_between_stable_dominating_irredundant_sets.

Variable D : {set G}.

(* A stable set D is maximal iff D is stable and dominating
 * See Prop. 3.5 of Fundamentals of Domination *)
Theorem maximal_st_iff_st_dom : maxset stable D <-> (stable D /\ dominating D).
Proof.
  rewrite -(rwP (maximal_indsysP _ st_hereditary)).
  rewrite /iff ; split ; last first.
  - move=> [ stableD /dominatingP dominatingD].
    split => // v vnotinD.
    have [w winD adjwv] := dominatingD _ vnotinD.
    apply/stablePn; exists v; exists w.
    by rewrite !inE eqxx winD sgP adjwv orbT.
  - move => [stableD H1]; split=> //.
    apply/dominatingP => x xnotinD.
    have/stablePn [w [z [winDcupx zinDcupx adjwz]]] := H1 x xnotinD.
    case: (eqVneq z x) => [zisx|zisnotx].
    + by subst z; exists w => //; rewrite !inE (sg_edgeNeq adjwz) in winDcupx.
    + have zinD : z \in D by rewrite !inE (negbTE zisnotx) /= in zinDcupx.
      exists z => //.
      move: winDcupx; rewrite in_setU in_set1.
      case/predU1P => [|winD]; first by move<- ; rewrite sg_sym adjwz.
      have := stableP D stableD w z winD zinD.
      apply: contraR. by rewrite adjwz.
Qed.

(* A maximal stable set is minimal dominating
 * See Prop. 3.6 of Fundamentals of Domination *)
Theorem maximal_st_is_minimal_dom : maxset stable D -> minset dominating D.
Proof.
  rewrite maximal_st_iff_st_dom => -[/stableP stableD dominatingD].
  apply/(minimal_indsysP _ dom_superhereditary); split=> // x xinD.
  apply/dominatingPn ; exists x ; first by rewrite in_setD1 eqxx andFb.
  move=> y /setD1P [_ yinD]. exact: stableD.
Qed.

(* A dominating set D is minimal iff D is dominating and irredundant
 * See Prop. 3.8 of Fundamentals of Domination *)
Theorem minimal_dom_iff_dom_irr : minset dominating D <-> (dominating D /\ irredundant D).
Proof.
  rewrite -(rwP (minimal_indsysP _ dom_superhereditary)); split ; last first.
  - move=> [dominatingD /irredundantP irredundantD]; split => // v vinD.
    have/set0Pn [w /privateP [vdomw H1]] := irredundantD v vinD.
    apply/dominatingPn; exists w.
    + rewrite in_setD1 negb_and negbK orbC.
      case: (boolP (w \in D)) => //= /H1 -> //. exact: dominates_refl.
    + move=> u /setD1P [uneqv uinD]. 
      apply: contra_neqN uneqv => uv. 
      by apply: H1 => //; rewrite /dominates uv orbT.
  - move => [dominatingD H2] ; split=> //.
    apply/irredundantP => v vinD.
    have/dominatingPn[w wnotinDminusv H3] := H2 v vinD.
    apply/set0Pn; exists w; apply/privateP ; split ; last first.
    + move=> u uinD udomw.
      apply: contraTeq udomw => uneqv.
      have uinDminusv : u \in D :\ v by rewrite in_setD1 uneqv uinD.
      rewrite /dominates negb_or (H3 u uinDminusv) andbT.
      by apply: contraNneq wnotinDminusv => <-.
    + rewrite /dominates ; case: (boolP (v == w)) => //= vneqw. 
      move: wnotinDminusv ; rewrite in_setD1 eq_sym vneqw andTb => wnotinD.
      have [u uinD] := dominatingP _ dominatingD w wnotinD.
      case: (boolP (u == v)) => [|uneqv] ; first by move/eqP->.
      have uinDminusv : u \in D :\ v by rewrite in_setD1 uneqv uinD.
      by rewrite (negbTE (H3 u uinDminusv)). 
Qed.

(* A minimal dominating set is maximal irredundant
 * See Prop. 3.9 of Fundamentals of Domination *)
Theorem minimal_dom_is_maximal_irr : minset dominating D -> maxset irredundant D.
Proof.
  rewrite minimal_dom_iff_dom_irr -(rwP (maximal_indsysP _ irr_hereditary)).
  move=> [dominatingD irredundantD]; split=> // v vnotinD.
  apply/irredundantPn; exists v; first by rewrite in_setU1 eqxx.
  apply: contraNT vnotinD => /set0Pn [x /privateP [vdomx xpriv]].
  have/bigcupP [u uinD udomx] := forallP dominatingD x.
  by rewrite -[v](xpriv u) -?in_cln // inE uinD orbT.
Qed.

End Relations_between_stable_dominating_irredundant_sets.


(**********************************************************************************)
Section Existence_of_stable_dominating_irredundant_sets.

(* Definitions of "maximal stable", "minimal dominating" and "maximal irredundant" sets *)

Definition max_st := maxset stable.

Definition min_dom := minset dominating.

Definition max_irr := maxset irredundant.

(* Inhabitants that are "maximal stable", "minimal dominating" and "maximal irredundant"
 * Recall that ex_minimal and ex_maximal requires a proof of an inhabitant of "stable",
 * "dominating" and "irredudant" to be able to generate the maximal/minimal set. *)

Definition inhb_max_st := s2val (maxset_exists stable0).

Definition inhb_min_dom := s2val (minset_exists domT).

Definition inhb_max_irr := s2val (maxset_exists irr0).

Lemma inhb_max_st_is_maximal_stable : max_st inhb_max_st.
Proof. exact: (s2valP (maxset_exists stable0)). Qed.

Lemma inhb_min_dom_is_minimal_dominating : min_dom inhb_min_dom.
Proof. exact: (s2valP (minset_exists domT)). Qed.

Lemma inhb_max_irr_is_maximal_irredundant : max_irr inhb_max_irr.
Proof. exact: (s2valP (maxset_exists irr0)). Qed.

End Existence_of_stable_dominating_irredundant_sets.


(**********************************************************************************)
Section Weighted_domination_parameters.

Variable weight : G -> nat.
Hypothesis positive_weights : forall v : G, weight v > 0.

Let W := weight_set weight.

(* Definition of weighted parameters. *)

Definition ir_w : nat := W (arg_min inhb_max_irr max_irr W).

Fact ir_min D : max_irr D -> ir_w <= W D.
Proof.
  rewrite /ir_w.
  by case: (arg_minnP W inhb_max_irr_is_maximal_irredundant) => A _ ; apply.
Qed.

Fact ir_witness : exists2 D, max_irr D & W D = ir_w.
Proof.
  rewrite /ir_w.
  case: (arg_minnP W inhb_max_irr_is_maximal_irredundant) => D.
  by exists D.
Qed.

Fact ir_minset D : max_irr D -> W D = ir_w -> minset max_irr D.
Proof.
  move => max_irrD irD; apply: minweight_minset => // A.
  rewrite -/W irD; exact: ir_min.
Qed.

Definition gamma_w : nat := W (arg_min setT dominating W).

Fact gamma_min D : dominating D -> gamma_w <= W D.
Proof. rewrite /gamma_w. case: (arg_minnP W domT) => A _ ; apply. Qed.

Fact gamma_witness : exists2 D, dominating D & W D = gamma_w.
Proof.
  rewrite /gamma_w.
  case: (arg_minnP W domT) => D.
  by exists D.
Qed.

Fact gamma_minset D : dominating D -> W D = gamma_w -> minset dominating D.
Proof.
  move => domD gammaD; apply: minweight_minset => // A.
  rewrite -/W gammaD; exact: gamma_min.
Qed.

Definition ii_w : nat := W (arg_min inhb_max_st max_st W).

Fact ii_min S : max_st S -> ii_w <= W S.
Proof.
  rewrite /ii_w.
  by case: (arg_minnP W inhb_max_st_is_maximal_stable) => A _ ; apply.
Qed.

Fact ii_witness : exists2 S, max_st S & W S = ii_w.
Proof.
  rewrite /ii_w.
  case: (arg_minnP W inhb_max_st_is_maximal_stable) => S.
  by exists S.
Qed.

Fact ii_minset D : max_st D -> W D = ii_w -> minset max_st D.
Proof.
  move => max_stD iiD; apply: minweight_minset => // A.
  rewrite -/W iiD; exact: ii_min.
Qed.

Definition alpha_w : nat := W (arg_max set0 stable W).

Fact alpha_max S : stable S -> W S <= alpha_w.
Proof. by move: S; rewrite /alpha_w; case: (arg_maxnP W stable0). Qed.

Fact alpha_witness : exists2 S, stable S & W S = alpha_w.
Proof. by rewrite /alpha_w; case: (arg_maxnP W stable0) => A; exists A. Qed.

Fact alpha_maxset S : stable S -> W S = alpha_w -> maxset stable S.
Proof.
  move => stS alphaS; apply: maxweight_maxset => // A.
  rewrite -/W alphaS; exact: alpha_max.
Qed.

Definition Gamma_w : nat := W (arg_max inhb_min_dom min_dom W).

Fact Gamma_max D : min_dom D -> W D <= Gamma_w.
Proof. 
  move: D ; rewrite /Gamma_w.
  by case: (arg_maxnP W inhb_min_dom_is_minimal_dominating).
Qed.

Fact Gamma_witness : exists2 D, min_dom D & W D = Gamma_w.
Proof.
  rewrite /Gamma_w.
  case: (arg_maxnP W inhb_min_dom_is_minimal_dominating) => D.
  by exists D.
Qed.

Fact Gamma_maxset D : min_dom D -> W D = Gamma_w -> maxset min_dom D.
Proof.
  move => min_domD GammaD; apply: maxweight_maxset => // A.
  rewrite -/W GammaD; exact: Gamma_max.
Qed.

Definition IR_w : nat := W (arg_max set0 irredundant W).

Fact IR_max D : irredundant D -> W D <= IR_w.
Proof. by move: D; rewrite /IR_w; case: (arg_maxnP W irr0). Qed.

Fact IR_witness : exists2 D, irredundant D & W D = IR_w.
Proof. by rewrite /IR_w; case: (arg_maxnP W irr0) => D; exists D. Qed.

Fact IR_maxset D : irredundant D -> W D = IR_w -> maxset irredundant D.
Proof.
  move => irrD IRD; apply: maxweight_maxset => // A.
  rewrite -/W IRD; exact: IR_max.
Qed.

(** ** Weighted version of the Cockayne-Hedetniemi domination chain. *)

Proposition ir_w_leq_gamma_w : ir_w <= gamma_w.
Proof.
  rewrite /gamma_w.
  have [D domD minWD] := arg_minnP W domT.
  have min_domD := minweight_minset positive_weights domD minWD.
  have max_irrD := minimal_dom_is_maximal_irr min_domD.
  exact: ir_min.
Qed.

Proposition gamma_w_leq_ii_w : gamma_w <= ii_w.
Proof.
  rewrite /ii_w.
  have [S max_stS _] := arg_minnP W inhb_max_st_is_maximal_stable.
  have domS := minsetp (maximal_st_is_minimal_dom max_stS).
  exact: gamma_min.
Qed.

Proposition ii_w_leq_alpha_w : ii_w <= alpha_w.
Proof.
  rewrite /alpha_w.
  have [S stS maxWS] := arg_maxnP W stable0.
  have max_stS := maxweight_maxset positive_weights stS maxWS.
  exact: ii_min.
Qed.

Proposition alpha_w_leq_Gamma_w : alpha_w <= Gamma_w.
Proof.
  rewrite /alpha_w.
  have [S stS maxWS] := arg_maxnP W stable0.
  have max_stS := maxweight_maxset positive_weights stS maxWS.
  have min_domS := maximal_st_is_minimal_dom max_stS.
  exact: Gamma_max.
Qed.

Proposition Gamma_w_leq_IR_w : Gamma_w <= IR_w.
Proof.
  rewrite /Gamma_w.
  have [D min_domD _] := arg_maxnP W inhb_min_dom_is_minimal_dominating.
  have irrD := maxsetp (minimal_dom_is_maximal_irr min_domD).
  exact: IR_max.
Qed.

Theorem Cockayne_Hedetniemi_chain_w: 
  sorted leq [:: ir_w; gamma_w; ii_w; alpha_w; Gamma_w; IR_w].
Proof. 
rewrite /sorted /= ir_w_leq_gamma_w gamma_w_leq_ii_w ii_w_leq_alpha_w.
by rewrite alpha_w_leq_Gamma_w Gamma_w_leq_IR_w.
Qed.

(* Usage: [apply: (Cockayne_Hedetniemi_w i j)] with i,j concrete
indices into the above list [i < j] *)
Notation Cockayne_Hedetniemi_w i j := 
  (@sorted_leq_nth _ Cockayne_Hedetniemi_chain_w i j erefl erefl erefl).

(** Example *)
Let gamma_w_leq_Gamma_w: gamma_w <= Gamma_w. 
Proof. exact: (Cockayne_Hedetniemi_w 1 4). Qed.

End Weighted_domination_parameters.

(* "argument" policy:
   every weighted parameter requires a graph, the weight vector and a proof that their
   components are positive *)
Arguments ir_w : clear implicits.
Arguments gamma_w : clear implicits.
Arguments ii_w : clear implicits.
Arguments alpha_w : clear implicits.
Arguments Gamma_w : clear implicits.
Arguments IR_w : clear implicits.

(** ** Classic (unweighted) parameters (use cardinality instead of weight)        *)

Section Classic_domination_parameters.

Definition ones : (G -> nat) := (fun _ => 1).

Let W1 : ({set G} -> nat) := (fun A => #|A|).

Lemma cardwset1 (A : {set G}) : #|A| = weight_set ones A.
Proof. by rewrite /weight_set sum1dep_card cardsE. Qed.

Local Notation eq_arg_min := (eq_arg_min _ (frefl _) cardwset1).
Local Notation eq_arg_max := (eq_arg_max _ (frefl _) cardwset1).

(** Definition of unweighted parameters and its conversion to weighted ones. *)


Definition ir : nat := #|arg_min inhb_max_irr max_irr W1|.

Fact eq_ir_ir1 : ir = ir_w ones.
Proof. by rewrite /ir /ir_w -cardwset1 eq_arg_min. Qed.

Definition gamma : nat := #|arg_min setT dominating W1|.

Fact eq_gamma_gamma1 : gamma = gamma_w ones.
Proof. by rewrite /gamma /gamma_w -cardwset1 eq_arg_min. Qed.

Definition ii : nat := #|arg_min inhb_max_st max_st W1|.

Fact eq_ii_ii1 : ii = ii_w ones.
Proof. by rewrite /ii /ii_w -cardwset1 eq_arg_min. Qed.

Definition alpha : nat := #|arg_max set0 stable W1|.

Fact eq_alpha_alpha1 : alpha = alpha_w ones.
Proof. by rewrite /alpha /alpha_w -cardwset1 eq_arg_max. Qed.

Definition Gamma : nat := #|arg_max inhb_min_dom min_dom W1|.

Fact eq_Gamma_Gamma1 : Gamma = Gamma_w ones.
Proof. by rewrite /Gamma /Gamma_w -cardwset1 eq_arg_max. Qed.

Definition IR : nat := #|arg_max set0 irredundant W1|.

Fact eq_IR_IR1 : IR = IR_w ones.
Proof. by rewrite /IR /IR_w -cardwset1 eq_arg_max. Qed.

(** ** Classic Cockayne-Hedetniemi domination chain. *)

Corollary ir_leq_gamma : ir <= gamma.
Proof. by rewrite eq_ir_ir1 eq_gamma_gamma1 ir_w_leq_gamma_w. Qed.

Corollary gamma_leq_ii : gamma <= ii.
Proof. by rewrite eq_gamma_gamma1 eq_ii_ii1 gamma_w_leq_ii_w. Qed.

Corollary ii_leq_alpha : ii <= alpha.
Proof. by rewrite eq_ii_ii1 eq_alpha_alpha1 ii_w_leq_alpha_w. Qed.

Corollary alpha_leq_Gamma : alpha <= Gamma.
Proof. by rewrite eq_alpha_alpha1 eq_Gamma_Gamma1 alpha_w_leq_Gamma_w. Qed.

Corollary Gamma_leq_IR : Gamma <= IR.
Proof. by rewrite eq_Gamma_Gamma1 eq_IR_IR1 Gamma_w_leq_IR_w. Qed.

Corollary Cockayne_Hedetniemi_chain: 
  sorted leq [:: ir; gamma; ii; alpha; Gamma; IR].
Proof. 
rewrite /sorted /= ir_leq_gamma gamma_leq_ii ii_leq_alpha.
by rewrite alpha_leq_Gamma Gamma_leq_IR.
Qed.

Notation Cockayne_Hedetniemi i j := 
  (@sorted_leq_nth _ Cockayne_Hedetniemi_chain i j erefl erefl erefl).

End Classic_domination_parameters.

End Domination_Theory.

Arguments ir_w : clear implicits.
Arguments gamma_w : clear implicits.
Arguments ii_w : clear implicits.
Arguments alpha_w : clear implicits.
Arguments Gamma_w : clear implicits.
Arguments IR_w : clear implicits.
Arguments ir : clear implicits.
Arguments gamma : clear implicits.
Arguments ii : clear implicits.
Arguments alpha : clear implicits.
Arguments Gamma : clear implicits.
Arguments IR : clear implicits.
