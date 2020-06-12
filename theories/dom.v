
(* New version of the Domination Theory in Graphs *)

From mathcomp Require Import all_ssreflect.
Require Import preliminaries digraph sgraph connectivity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


(**********************************************************************************)
(** * Basic facts about graphs *)
Section Neighborhoods_definitions.

Variable G : diGraph.

Definition open_neigh (u : G) := [set v | u -- v].
Local Notation "N( x )" := (open_neigh x) (at level 0, x at level 99, format "N( x )").

Definition closed_neigh (u : G) := u |: N(u).
Local Notation "N[ x ]" := (closed_neigh x) (at level 0, x at level 99, format "N[ x ]").

Definition cl_sedge (u v : G) : bool := (u == v) || (u -- v).

Variable D : {set G}.

Definition open_neigh_set : {set G} := \bigcup_(w in D) N(w).

Definition closed_neigh_set : {set G} := \bigcup_(w in D) N[w].

End Neighborhoods_definitions.

Notation "x -*- y" := (cl_sedge x y) (at level 30).
Notation "E( G )" := (edges G) (at level 0, G at level 99, format "E( G )").

Notation "N( x )" := (@open_neigh _ x) 
   (at level 0, x at level 99, format "N( x )").
Notation "N[ x ]" := (@closed_neigh _ x) 
   (at level 0, x at level 99, format "N[ x ]").
Notation "N( G ; x )" := (@open_neigh G x)
   (at level 0, G at level 99, x at level 99, format "N( G ; x )", only parsing).
Notation "N[ G ; x ]" := (@closed_neigh G x)
   (at level 0, G at level 99, x at level 99, format "N[ G ; x ]", only parsing).
   
Notation "NS( G ; D )" := (@open_neigh_set G D) 
   (at level 0, G at level 99, D at level 99, format "NS( G ; D )", only parsing).
Notation "NS( D )" := (open_neigh_set D) 
   (at level 0, D at level 99, format "NS( D )").
Notation "NS[ G ; D ]" := (@closed_neigh_set G D) 
   (at level 0, G at level 99, D at level 99, format "NS[ G ; D ]", only parsing).
Notation "NS[ D ]" := (closed_neigh_set D) 
   (at level 0, D at level 99, format "NS[ D ]").


(**********************************************************************************)
Section Basic_Facts_Neighborhoods.

(* TOTHINK: naming conventions that make these lemmas acutally useful
(i.e., names shorter than inlining their proofs)

Conventions: 
opn : open_neigh
cln : closed_neigh
opns : open_neigh_set
clns : closed_neigh_set
in_? : canonical [(x \in ?) = _ ] lemma (could be part of inE)
mem_? : other lemmas about (x \in ?)
prv : private
prvs : private_set
wset : weighted sets

some suggestions below *)

Variable G : sgraph.
Implicit Types (u v : G).

Lemma in_opn u v : u \in N(v) = (v -- u).
Proof. by rewrite /open_neigh in_set. Qed.

Lemma v_notin_opneigh v : v \notin N(v).
Proof. by rewrite in_opn sg_irrefl. Qed.

Lemma in_cln u v : u \in N[v] = (v -*- u). 
Proof. by rewrite /closed_neigh in_setU1 eq_sym in_opn. Qed.

Lemma cl_sg_sym : symmetric (@cl_sedge G). (* cl_sedge u v = cl_sedge v u *)
Proof. rewrite /symmetric /cl_sedge /closed_neigh => x y ; by rewrite sg_sym eq_sym. Qed.

Lemma cl_sg_refl : reflexive (@cl_sedge G). (* cl_sedge u u = true *)
Proof. by move => x; rewrite /cl_sedge eqxx. Qed.

Lemma v_in_clneigh v : v \in N[v].
Proof. by rewrite in_cln cl_sg_refl. Qed.

Lemma opn_proper_cln v : N(v) \proper N[v].
Proof. 
  apply/properP; rewrite subsetUr; split => //.
  by exists v; rewrite !inE ?eqxx sgP.
Qed.

Lemma in_edges u v : [set u; v] \in E(G) = (u -- v).
Proof. 
  apply/edgesP/idP => [[x] [y] []|]; last by exists u; exists v.
  by case/doubleton_eq_iff => -[-> ->] //; rewrite sgP.
Qed.

Lemma opns0 : NS(G;set0) = set0. 
Proof. by rewrite /open_neigh_set big_set0. Qed.

Lemma clns0 : NS[G;set0] = set0.
Proof. by rewrite /closed_neigh_set big_set0. Qed.

Variables D1 D2 : {set G}.

Lemma opn_sub_opns : {in D1, forall v, N(v) \subset NS(D1)}.
Proof. move=> v vinD1; exact: bigcup_sup. Qed.

Lemma cln_sub_clns : {in D1, forall v, N[v] \subset NS[D1]}.
Proof. move=> v vinD1; exact: bigcup_sup. Qed.

Lemma set_sub_clns : D1 \subset NS[D1].
Proof.
  apply/subsetP => x xinD1. 
  apply/bigcupP; exists x => //. exact: v_in_clneigh.
Qed.

Lemma mem_opns u v : u \in D1 -> u -- v -> v \in NS(D1).
Proof. move=> uinD1 adjuv. apply/bigcupP ; exists u => // ; by rewrite in_opn. Qed.

Lemma opns_sub_clns : NS(D1) \subset NS[D1].
Proof.
  apply/subsetP => u.
  rewrite /open_neigh_set /closed_neigh_set.
  move/bigcupP.
  elim=> v vinD1 uinNv.
  apply/bigcupP.
  exists v => [// | ].
  by rewrite /closed_neigh in_setU uinNv orbT.
Qed.

Lemma mem_clns u v : u \in D1 -> u -- v -> v \in NS[D1].
Proof.
  move=> uinD1 adjuv.
  apply: (subsetP opns_sub_clns v).
  exact: mem_opns adjuv.
Qed.

Lemma subset_clns : D1 \subset D2 -> NS[D1] \subset NS[D2].
Proof.
  move=> D1subD2.
  rewrite /closed_neigh_set.
  apply/subsetP => x /bigcupP.
  elim=> i iinD1 xinNi.
  apply/bigcupP.
  exists i.
  exact: subsetP D1subD2 i iinD1.
  exact: xinNi.
Qed.

End Basic_Facts_Neighborhoods.


(**********************************************************************************)
(** * Domination Theory *)
Section Domination_Theory.

Variable G : sgraph.


(**********************************************************************************)
(** * Maximal and minimal sets *)

Proposition maxsetP' (p : pred {set G}) (D : {set G}) :
  reflect (p D /\ (forall F : {set G}, D \proper F -> ~~ p F)) (maxset p D).
Proof.
  apply: (iffP maxsetP) => -[pD maxD]; split => // E.
  - rewrite properEneq => /andP [DnE DsubE].
    apply: contra_neqN DnE => pE; exact/esym/maxD.
  - move => pE SsubE; apply: contraTeq pE => EnD; apply: maxD.
    by rewrite properEneq eq_sym EnD.
Qed.
Arguments maxsetP' {p D}.

Proposition minsetP' (p : pred {set G}) (D : {set G}) :
  reflect (p D /\ (forall F : {set G}, F \proper D -> ~~ p F)) (minset p D).
Proof.
  rewrite minmaxset; apply (iffP maxsetP'); rewrite /= setCK => -[pD H]; split => // E.
  all: by rewrite properC ?setCK => /H; rewrite ?setCK.
Qed.
Arguments minsetP' {p D}.


(**********************************************************************************)
Section MaxMin_sets_existence.

Variable p : pred {set G}.     (* p : {set G} -> bool *)
Variable F : {set G}.          (* some set satisfying p *)
Hypothesis pF : p F.           (* the proof that F satisfies p *)

Definition ex_maximal : {set G} := s2val (maxset_exists pF).

Definition ex_minimal : {set G} := s2val (minset_exists pF).

Fact maximal_exists : maxset p ex_maximal.
Proof. exact: s2valP (maxset_exists pF). Qed.

Fact minimal_exists : minset p ex_minimal.
Proof. exact: s2valP (minset_exists pF). Qed.

End MaxMin_sets_existence.


(**********************************************************************************)
(** * Independence systems, hereditary and superhereditary properties *)
Section Independence_system_definitions.

Implicit Types (p : pred {set G}) (F D : {set G}).

Definition hereditary p : bool := [forall D : {set G}, forall (F : {set G} | F \subset D), p D ==> p F].

Definition superhereditary p : bool := hereditary [pred D | p (~: D)].

Proposition hereditaryP p : 
  reflect (forall D F : {set G}, (F \subset D) -> p D -> p F) (hereditary p).
Proof.
  rewrite /hereditary ; apply: (iffP forallP).
  - move=> H1 D F FsubD pD. move: (H1 D).
    move/forallP=> /(_ F).
    by rewrite FsubD pD !implyTb.
  - move=> H2 D.
    apply/forall_inP => F FsubD. apply/implyP.
    exact: H2.
Qed.

Proposition superhereditaryP (p : pred {set G}) : 
  reflect (forall D F : {set G}, (D \subset F) -> p D -> p F) (superhereditary p).
Proof.
  apply: (iffP (hereditaryP _)) => /= sh_p D F.
  all: by rewrite -setCS => /sh_p; rewrite ?setCK; auto.
Qed.

Proposition maximal_indsysP p D : hereditary p ->
  reflect (p D /\ forall v : G, v \notin D -> ~~ p (v |: D)) (maxset p D).
Proof. 
  move/hereditaryP => p_hereditary; apply: (iffP maxsetP').
  - case => pD maxD; split => // v vD. apply: maxD.
    by rewrite setUC properUl // sub1set. 
  - case => pD max1D; split => // A /properP [subA [v vA /max1D vD]].
    apply: contraNN vD; apply: p_hereditary; by rewrite subUset sub1set vA.
Qed.

Proposition minimal_indsysP p D : superhereditary p ->
  reflect (p D /\ forall v : G, v \in D -> ~~ p (D :\ v)) (minset p D).
Proof.
  rewrite minmaxset => sh_p; apply: (iffP (maximal_indsysP _ _)) => //=.
  all: rewrite ?setCK => -[pD H]; split => // v; move: (H v).
  all: by rewrite !inE ?setCU ?setCK ?negbK setDE setIC.
Qed.

End Independence_system_definitions.


(**********************************************************************************)
(** * Basic definitions about positive weighted sets and parameters *)
Section Weighted_Sets.

Variable weight : G -> nat.
Hypothesis positive_weights : forall v : G, weight v > 0.

Definition weight_set (S : {set G}) := \sum_(v in S) weight v.
Let W := weight_set.

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

Lemma leqwset (A B : {set G}) : A \subset B -> W A <= W B.
Proof. move=> AsubB ; by rewrite [X in _ <= X](big_setID A) /= (setIidPr AsubB) leq_addr. Qed.

Lemma ltnwset (A B : {set G}) :  A \proper B -> W A < W B.
Proof.
  move => /properP [AsubB].
  elim=> x xinB xnotinA.
  rewrite {2}/W /weight_set (big_setID A) /= (setIidPr AsubB).
  rewrite -[X in X <= _]addn0 addSn -addnS leq_add2l lt0n.
  rewrite -/(weight_set _) -wset0. 
  by apply/set0Pn; exists x; apply/setDP.
Qed.

End Weighted_Sets.


(**********************************************************************************)
(** * Definitions of stable, dominating and irredundant sets *)
Section Stable_Set.

Variable S : {set G}.

Definition stable : bool := [forall u in S, forall v in S, ~~ (u -- v)].

Definition stable_alt : bool := NS(S) :&: S == set0.

(* TO DO: @chdoc suggests to add:
Proposition stableF : stable -> {in S&, forall u v, u -- v = false}.
*)

Proposition stableP : reflect {in S&, forall u v, ~~ u -- v} stable.
Proof. apply: equivP (in11_in2 S S). do 2 (apply: forall_inPP => ?). exact: idP. Qed.

Proposition stablePn : reflect (exists x y, [/\ x \in S, y \in S & x -- y]) (~~ stable).
Proof. 
  set E := exists _, _.
  have EE : (exists2 x, x \in S & exists2 y, y \in S & x -- y) <-> E by firstorder.
  rewrite /stable !negb_forall_in; apply: equivP EE; apply: exists_inPP => x.
  rewrite negb_forall_in; apply: exists_inPP => y. exact: negPn.
Qed.

Theorem stable_eq_stable_alt : stable = stable_alt. 
Proof. 
  rewrite /stable_alt setI_eq0; apply/stableP/disjointP => stS.
  - move => x /bigcupP [y yS adjyx] xS. 
    move: adjyx. rewrite in_opn. apply/negP. by apply: stS.
  - move => x y xS yS. apply/negP => adjxy.
    exact: (stS y (mem_opns xS adjxy) yS).
Qed.

End Stable_Set.

(* the empty set is stable *)
Lemma stable0 : stable set0.
Proof. apply/stableP ; by move=> u v ; rewrite in_set0. Qed.

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

Definition dominating : bool := [forall v : G, (v \notin D) ==> [exists u : G, (u \in D) && (u -- v)]].

Definition dominating_alt : bool := [set: G] == NS[D].

Proposition dominatingP : reflect
  (forall v : G, v \notin D -> exists2 u : G, u \in D & u -- v) dominating.
Proof.
  rewrite /dominating ; apply: (iffP forallP).
  - move=> H1 v vnotinD.
    move/implyP: (H1 v) => H2.
    move/existsP: (H2 vnotinD). elim=> x /andP [xinD adjxv]. by exists x.
  - move=> H3 x.
    apply/implyP=> xnotinD.
    move: (H3 x xnotinD).
    elim=> u uinD adjux. apply/existsP. exists u. by apply/andP.
Qed.

Proposition dominatingPn : reflect
  (exists v : G, {in D, forall u, ~~ (u -*- v)}) (~~ dominating).
Proof.
  rewrite /dominating ; apply (iffP existsP).
  - elim=> x H1. exists x. move: H1.
    case: (boolP (x \in D)) ; first by rewrite negb_imply andFb.
    move=> xnotinD ; rewrite negb_imply andTb negb_exists.
    move/forallP => H2 y yinD. 
    move: (H2 y). rewrite yinD andTb /cl_sedge.
    apply: contra ; case/predU1P => [ | //].
    move=> yeqx. rewrite yeqx in yinD. by move/negP: xnotinD ; contradiction.
  - elim=> v H3. exists v. rewrite negb_imply negb_exists ; apply/andP ; split.
    + move: (H3 v). rewrite cl_sg_refl. by move/(@contraL (v \in D) true) ->.
    + apply/forallP=> u.
      case: (boolP (u \in D)) ; last by rewrite andFb.
      move=> /(H3 u). by rewrite andTb /cl_sedge negb_or => /andP [_].
Qed.

Theorem dominating_eq_dominating_alt : dominating <-> dominating_alt.
Proof.
  rewrite /dominating /dominating_alt /iff ; split.
  - move/forallP=> H1.
    rewrite eqEsubset subsetT andbT.
    (* it is enough to prove V(G) \subset N[D] *)
    apply/subsetP => x _. 
    case: (boolP (x \in D)); first exact/subsetP/set_sub_clns.
    move => xnotinD.
    move/implyP: (H1 x) => H2.
    move/existsP: (H2 xnotinD).
    elim=> u /andP [uinD adjux].
    exact: mem_clns uinD adjux.
  - move=> VisND.
    apply/dominatingP => v vnotinD.
    move/eqP: VisND (in_setT v) -> => /bigcupP.
    elim=> [x xinD vinNx].
    rewrite /closed_neigh in_setU /open_neigh !inE in vinNx.
    case/predU1P : vinNx => [visx|adjxv]; last by exists x.
    by subst; contrab.
Qed.

End Dominating_Set.

(* V(G) is dominating *)
Lemma domT : dominating [set :G].
Proof.
  rewrite dominating_eq_dominating_alt /dominating_alt eqEsubset subsetT andbT.
  exact: set_sub_clns.
Qed.

(* if D is dominating, any supraset of D is also dominating *)
Lemma dom_superhereditary : superhereditary dominating.
Proof.
  apply/superhereditaryP.
  move=> D F DsubF /dominatingP Ddom.
  apply/dominatingP => v vnotinF.
  have vinVminusF: v \in [set: G] :\: F by rewrite in_setD in_setT andbT.
  (* if D is contained in F, then some v in V(G)-F also belongs to V(G)-D *)
  move: (subsetP (setDS setT DsubF)).
  move=> /(_ v vinVminusF).
  rewrite in_setD in_setT andbT => vinVminusD.
  elim: (Ddom v vinVminusD) => w winD adjwv.
  exists w ; last by rewrite adjwv. exact: (subsetP DsubF) w winD.
Qed.


(**********************************************************************************)
Section Irredundant_Set.

Variable D : {set G}.

Definition private_set (v : G) := N[v] :\: NS[D :\: [set v]].

(* private v w = w is a private vertex of v (assuming v \in D) *)
Definition private (v w : G) : bool := v -*- w && [forall u : G, (u \in D) ==> (u -*- w) ==> (u == v)].

Proposition privateP : forall v w : G, reflect 
  (v -*- w /\ {in D, forall u, u -*- w -> u = v}) (private v w).
Proof.
  move=> v w. rewrite /private ; apply: (iffP andP).
  - move=> [vdomw /forallP H1] ; split=> //.
    move=> u uinD udomw. move: (H1 u).
    rewrite uinD implyTb udomw implyTb. by move/eqP->.
  - move=> [vdomw H2] ; split=> //.
    apply/forall_inP => u uinD. apply/implyP=> udomw.
    move: (H2 u uinD udomw). by move->.
Qed.

Theorem mem_prv_prvs (v w : G) : (private v w) <-> (w \in private_set v).
Proof.
  rewrite /private_set /iff ; split.
  - move/privateP => [vdomw H1].
    rewrite in_setD /closed_neigh_set.
    apply/andP.
    split ; last by rewrite in_cln.
    apply/bigcupP.
    elim=> x xinDminusv winNx.
    move: xinDminusv.
    rewrite in_setD in_set1 => /andP [xnotv xinD].
    move: winNx.
    rewrite in_cln => xdomw.
    move: (H1 x xinD xdomw).
    move/eqP: xnotv.
    contradiction.
  - rewrite in_setD /closed_neigh_set.
    move=> /andP [wnotincup winNv].
    apply/privateP ; split ; first by rewrite -in_cln.
    move=> u uinD udomw.
    apply/eqP.
    move: wnotincup.
    apply: contraR => unotv.
    apply/bigcupP.
    exists u ; last by rewrite in_cln.
    by rewrite /= in_setD uinD andbT in_set1.
Qed.

Lemma prvs0n : {in D, forall v, (private_set v != set0) <-> (exists w : G, private v w)}.
Proof.
  move=> v.
  rewrite /private_set /iff ; split.
  - move/set0Pn. elim=> w H2.
    exists w. by rewrite mem_prv_prvs.
  - elim=> w. rewrite mem_prv_prvs => H1.
    apply/set0Pn. by exists w.
Qed.

(* This alternative definition of private_set contemplates cases where v \notin D.
 * If v belongs to D, it returns the set of private vertices; otherwise, it returns an empty set. *)
Definition private_set' (v : G) := NS[D :&: [set v]] :\: NS[D :\: [set v]].

Lemma eq_prvs_prvs' (v : G) : v \in D -> private_set' v == private_set v.
Proof.
  move=> vinD ; rewrite /private_set /private_set'.
  suff: N[v] = NS[D :&: [set v]] by move->.
  rewrite (setIidPr _) ?sub1set //.
  apply/eqP ; rewrite eqEsubset ; apply/andP ; split.
  - apply: cln_sub_clns. by rewrite in_set1.
  - apply/subsetP => x. move/bigcupP. elim=> z ; rewrite in_set1. by move/eqP->.
Qed.

Lemma eq0prvs' (v : G) : v \notinD -> (private_set' v == set0).
Proof.
  move=> vnotinD.
  rewrite /private_set' disjoint_setI0 1?disjoint_sym ?disjoints1 //.
  by rewrite clns0 set0D.
Qed.

Definition irredundant : bool := [forall v : G, (v \in D) ==> (private_set v != set0)].

Proposition irredundantP: reflect {in D, forall v, (private_set v != set0)} irredundant.
Proof.
  rewrite /irredundant ; apply: (iffP forallP).
  - move=> H1 v vinD. by move/implyP: (H1 v) => /(_ vinD).
  - move=> H2 v. apply/implyP=> vinD. by move: (H2 v vinD).
Qed.

Proposition irredundantPn : reflect (exists2 v, v \in D & private_set' v == set0) (~~ irredundant).
Proof.
  rewrite /irredundant ; apply: (iffP existsP) ; last first.
  - elim=> x xinD. rewrite (eqP (eq_prvs_prvs' xinD)) => H1.
    by exists x ; rewrite xinD H1.
  - elim=> x H2.
    suff privx_empty: private_set' x == set0.
    { by exists x ; move: H2 ; rewrite negb_imply negbK => /andP [xinD ?]. }
    case: (boolP (x \in D)) ; last exact: eq0prvs'.
    move=> xinD ; move: H2.
    by rewrite xinD implyTb negbK (eqP (eq_prvs_prvs' xinD)).
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
  rewrite (prvs0n vinD) (prvs0n vinF).
  elim=> x /privateP [vdomx H1]. exists x.
  apply/privateP ; split=> //.
  move=> u uinF udomx. move: (subsetP FsubD u uinF) => uinD.
  exact: (H1 u uinD udomx).
Qed.


(**********************************************************************************)
(** * Fundamental facts about Domination Theory *)
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
  - move => [stableD H1].
    split=> //. apply/dominatingP => x xnotinD.
    move: (H1 x).
    move=> /(_ xnotinD). 
    move/stablePn => [w] [z] [winDcupx zinDcupx adjwz].
    case: (boolP (z == x)).
    (* case z = x *)
    + move/eqP=> zisx.
      move: adjwz.
      rewrite zisx => adjwx.
      exists w ; last by rewrite adjwx.
      move: winDcupx.
      rewrite in_setU in_set1.
      by move: (sg_edgeNeq adjwx) ->.
    (* case z != x *)
    + move=> zisnotx.
      have zinD: z \in D.
      { move: zinDcupx.
        rewrite in_setU in_set1.
        by move/negbTE: zisnotx ->. }
      exists z.
      rewrite zinD; split => //.
      move: winDcupx.
      rewrite in_setU in_set1.
      case/predU1P ; first by move<- ; rewrite sg_sym adjwz.
      move=> winD. move/stableP: stableD.
      move=> /(_ w z winD zinD).
      apply: contraR. by rewrite adjwz.
Qed.

(* A maximal stable set is minimal dominating
 * See Prop. 3.6 of Fundamentals of Domination *)
Theorem maximal_st_is_minimal_dom : maxset stable D -> minset dominating D.
Proof.
  rewrite maximal_st_iff_st_dom.
  move=> [stableD dominatingD].
  rewrite -(rwP (minimal_indsysP _ dom_superhereditary)).
  split=> // x xinD.
  apply/dominatingPn.
  exists x => y.
  rewrite in_setD1 => /andP [yneqx yinD].
  rewrite /cl_sedge negb_or yneqx andTb.
  move/stableP: stableD ; by move=> /(_ y x yinD xinD).
Qed.

(* A dominating set D is minimal iff D is dominating and irredundant
 * See Prop. 3.8 of Fundamentals of Domination *)
Theorem minimal_dom_iff_dom_irr : minset dominating D <-> (dominating D /\ irredundant D).
Proof.
  rewrite -(rwP (minimal_indsysP _ dom_superhereditary)).
  rewrite /iff ; split ; last first.
  - move=> [dominatingD /irredundantP irredundantD].
    split => // v vinD.
    apply/dominatingPn.
    move: (irredundantD v vinD).
    rewrite (prvs0n vinD).
    elim=> w.
    rewrite /private => /andP [vdomw /forall_inP H1].
    exists w => u.
    rewrite in_setD1 => /andP [uneqv uinD].
    move: (H1 u uinD).
    move/implyP/(@contra (u -*- w) (u == v)).
    by move=> /(_ uneqv).
  - move => [dominatingD H2] ; split=> //.
    apply/irredundantP => v vinD.
    move: (H2 v) => /(_ vinD).
    move/dominatingPn.
    elim=> w H3.
    rewrite (prvs0n vinD).
    exists w.
    apply/privateP ; split ; last first.
    + move=> u uinD udomw.
      apply/eqP.
      move: udomw.
      apply/contraLR => uneqv.
      have uinDminusv : u \in D :\ v by rewrite in_setD1 uneqv uinD.
      by rewrite (H3 u uinDminusv).
    + case: (boolP (w == v)) ; first by move/eqP-> ; rewrite cl_sg_refl.
      move=> wneqv.
      case: (boolP (w \in D)).
      * move=> winD.
        move: (H3 w).
        rewrite in_setD1 wneqv andTb.
        move=> /(_ winD) /negP.
        move: (cl_sg_refl w).
        contradiction.
      * move=> wnotinD.
        move/dominatingP: dominatingD.
        move=> /(_ w wnotinD).
        elim=> u.
        case: (boolP (u == v)) ; first by move/eqP-> => _ adjvw ; rewrite /cl_sedge adjvw orbT.
        move=> uneqv uinD.
        have uinDminusv : u \in D :\ v by rewrite in_setD1 uneqv uinD.
        move: (H3 u uinDminusv).
        rewrite /cl_sedge negb_or => /andP [_].
        move/negP.
        contradiction.
Qed.

(* A minimal dominating set is maximal irredundant
 * See Prop. 3.9 of Fundamentals of Domination *)
Theorem minimal_dom_is_maximal_irr : minset dominating D -> maxset irredundant D.
Proof.
  rewrite minimal_dom_iff_dom_irr.
  rewrite -(rwP (maximal_indsysP _ irr_hereditary)).
  move=> [dominatingD irredundantD].
  split=>// v vnotinD.
  rewrite /irredundant.
  rewrite negb_forall.
  apply/existsP.
  exists v.
  have vinDcupv : v \in D :|: [set v] by rewrite in_setU set11 orbT.
  rewrite setUC negb_imply vinDcupv andTb.
  apply/negP.
  rewrite (prvs0n vinDcupv).
  elim=> x.
  rewrite /private ; move/andP => [vdomx].
  case: (boolP (x \in D)) => [xinD | xnotinD].
  (* case when x is in D (x dominates itself) *)
  - have xinDcupv: x \in D :|: [set v] by rewrite in_setU xinD orTb.
    move/forallP=> /(_ x).
    move/implyP=> /(_ xinDcupv).
    rewrite cl_sg_refl implyTb.
    move/eqP=> xeqv ; rewrite -xeqv in vnotinD.
    by move/negP in vnotinD.
  (* case when x is not in D (some u in D dominates x) *)
  - move: dominatingD.
    move/dominatingP=> /(_ x xnotinD).
    elim=> u uinD adjux.
    have uinDcupv: u \in D :|: [set v] by rewrite in_setU uinD orTb.
    move/forallP=> /(_ u).
    move/implyP=> /(_ uinDcupv).
    rewrite /cl_sedge adjux orbT implyTb.
    move/eqP=> ueqv ; rewrite -ueqv in vnotinD.
    by move/negP in vnotinD.
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

Definition inhb_max_st := ex_maximal stable0.

Definition inhb_min_dom := ex_minimal domT.

Definition inhb_max_irr := ex_maximal irr0.

Lemma inhb_max_st_is_maximal_stable : max_st inhb_max_st.
Proof. exact: maximal_exists. Qed.

Lemma inhb_min_dom_is_minimal_dominating : min_dom inhb_min_dom.
Proof. exact: minimal_exists. Qed.

Lemma inhb_max_irr_is_maximal_irredundant : max_irr inhb_max_irr.
Proof. exact: maximal_exists. Qed.

End Existence_of_stable_dominating_irredundant_sets.


(**********************************************************************************)
Section Weighted_domination_parameters.

Variable weight : G -> nat.
Hypothesis positive_weights : forall v : G, weight v > 0.

(* Sets of minimum/maximum weight *)

Let W := weight_set weight.
Let properW := ltnwset positive_weights.

(* The following lemmas state that if a set is maximum (i.e. has a maximum weight),
 * then it is maximal, and if a set is minimum, then it is minimal. Note: in maxweight_maxset,
 * "A" is the maximum set, but in arg_maxset, "A" is an inhabitant of the property. *)
Lemma maxweight_maxset (p : pred {set G}) (A : {set G}) : 
  p A -> (forall B, p B -> W B <= W A) -> maxset p A.
Proof.
  move => pA maxA. apply/maxsetP'; split => // B /properW; rewrite ltnNge.
  exact/contraNN/maxA.
Qed.

Lemma arg_maxset (p : pred {set G}) (A : {set G}) : p A -> maxset p (arg_max A p W).
Proof. by move => pA; apply/maxweight_maxset; case: arg_maxP. Qed.

Lemma minweight_minset (p : pred {set G}) (A : {set G}) : 
  p A -> (forall B, p B -> W A <= W B) -> minset p A.
Proof.
  move => pA minA; apply/minsetP'; split => // B /properW; rewrite ltnNge.
  exact/contraNN/minA.
Qed.

Lemma arg_minset (p : pred {set G}) (A : {set G}) : p A -> minset p (arg_min A p W).
Proof. by move => pA ; apply/minweight_minset; case: arg_minP. Qed.

(* Definition of weighted parameters. *)

Definition ir_w : nat := W (arg_min inhb_max_irr max_irr W).

Fact ir_min D : max_irr D -> ir_w <= W D.
Proof.
  rewrite /ir_w.
  by case: (arg_minP W inhb_max_irr_is_maximal_irredundant) => A _ ; apply.
Qed.

Fact ir_witness : exists2 D, max_irr D & W D = ir_w.
Proof.
  rewrite /ir_w.
  case: (arg_minP W inhb_max_irr_is_maximal_irredundant) => D.
  by exists D.
Qed.

Fact ir_minset D : max_irr D -> W D = ir_w -> minset max_irr D.
Proof.
  move => max_irrD irD; apply: minweight_minset => // A.
  rewrite irD; exact: ir_min.
Qed.

Definition gamma_w : nat := W (arg_min setT dominating W).

Fact gamma_min D : dominating D -> gamma_w <= W D.
Proof. rewrite /gamma_w. case: (arg_minP W domT) => A _ ; apply. Qed.

Fact gamma_witness : exists2 D, dominating D & W D = gamma_w.
Proof.
  rewrite /gamma_w.
  case: (arg_minP W domT) => D.
  by exists D.
Qed.

Fact gamma_minset D : dominating D -> W D = gamma_w -> minset dominating D.
Proof.
  move => domD gammaD; apply: minweight_minset => // A.
  rewrite gammaD; exact: gamma_min.
Qed.

(* longer variant with only one use of [arg_*P]
Proposition gamma_def: 
  (forall A, dominating A -> gamma_w <= W A) /\ (exists2 A, dominating A & W A = gamma_w).
Proof. 
rewrite /gamma_w; case: (arg_minP _ domT) => A A1 A2; split => //; by exists A.
Qed.
Definition gamma_min := proj1 gamma_def.
Definition gamma_witness := proj2 gamma_def. *)

Definition ii_w : nat := W (arg_min inhb_max_st max_st W).

Fact ii_min S : max_st S -> ii_w <= W S.
Proof.
  rewrite /ii_w.
  by case: (arg_minP W inhb_max_st_is_maximal_stable) => A _ ; apply.
Qed.

Fact ii_witness : exists2 S, max_st S & W S = ii_w.
Proof.
  rewrite /ii_w.
  case: (arg_minP W inhb_max_st_is_maximal_stable) => S.
  by exists S.
Qed.

Fact ii_minset D : max_st D -> W D = ii_w -> minset max_st D.
Proof.
  move => max_stD iiD; apply: minweight_minset => // A.
  rewrite iiD; exact: ii_min.
Qed.

Definition alpha_w : nat := W (arg_max set0 stable W).

Fact alpha_max S : stable S -> W S <= alpha_w.
Proof. by move: S; rewrite /alpha_w; case: (arg_maxP W stable0). Qed.

Fact alpha_witness : exists2 S, stable S & W S = alpha_w.
Proof. by rewrite /alpha_w; case: (arg_maxP W stable0) => A; exists A. Qed.

Fact alpha_maxset S : stable S -> W S = alpha_w -> maxset stable S.
Proof.
  move => stS alphaS; apply: maxweight_maxset => // A.
  rewrite alphaS; exact: alpha_max.
Qed.

Definition Gamma_w : nat := W (arg_max inhb_min_dom min_dom W).

Fact Gamma_max D : min_dom D -> W D <= Gamma_w.
Proof. 
  move: D ; rewrite /Gamma_w.
  by case: (arg_maxP W inhb_min_dom_is_minimal_dominating).
Qed.

Fact Gamma_witness : exists2 D, min_dom D & W D = Gamma_w.
Proof.
  rewrite /Gamma_w.
  case: (arg_maxP W inhb_min_dom_is_minimal_dominating) => D.
  by exists D.
Qed.

Fact Gamma_maxset D : min_dom D -> W D = Gamma_w -> maxset min_dom D.
Proof.
  move => min_domD GammaD; apply: maxweight_maxset => // A.
  rewrite GammaD; exact: Gamma_max.
Qed.

Definition IR_w : nat := W (arg_max set0 irredundant W).

Fact IR_max D : irredundant D -> W D <= IR_w.
Proof. by move: D; rewrite /IR_w; case: (arg_maxP W irr0). Qed.

Fact IR_witness : exists2 D, irredundant D & W D = IR_w.
Proof. by rewrite /IR_w; case: (arg_maxP W irr0) => D; exists D. Qed.

Fact IR_maxset D : irredundant D -> W D = IR_w -> maxset irredundant D.
Proof.
  move => irrD IRD; apply: maxweight_maxset => // A.
  rewrite IRD; exact: IR_max.
Qed.

(* Weighted version of the Cockayne-Hedetniemi domination chain. *)

Theorem ir_w_leq_gamma_w : ir_w <= gamma_w.
Proof.
  rewrite /gamma_w.
  have [D domD minWD] := arg_minP W domT.
  have min_domD := minweight_minset domD minWD.
  have max_irrD := minimal_dom_is_maximal_irr min_domD.
  exact: ir_min.
Qed.

Theorem gamma_w_leq_ii_w : gamma_w <= ii_w.
Proof.
  rewrite /ii_w.
  have [S max_stS _] := arg_minP W inhb_max_st_is_maximal_stable.
  have domS := minsetp (maximal_st_is_minimal_dom max_stS).
  exact: gamma_min.
Qed.

Theorem ii_w_leq_alpha_w : ii_w <= alpha_w.
Proof.
  rewrite /alpha_w.
  have [S stS maxWS] := arg_maxP W stable0.
  have max_stS := maxweight_maxset stS maxWS.
  exact: ii_min.
Qed.

Theorem alpha_w_leq_Gamma_w : alpha_w <= Gamma_w.
Proof.
  rewrite /alpha_w.
  have [S stS maxWS] := arg_maxP W stable0.
  have max_stS := maxweight_maxset stS maxWS.
  have min_domS := maximal_st_is_minimal_dom max_stS.
  exact: Gamma_max.
Qed.

Theorem Gamma_w_leq_IR_w : Gamma_w <= IR_w.
Proof.
  rewrite /Gamma_w.
  have [D min_domD _] := arg_maxP W inhb_min_dom_is_minimal_dominating.
  have irrD := maxsetp (minimal_dom_is_maximal_irr min_domD).
  exact: IR_max.
Qed.

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


(**********************************************************************************)
(** * Classic (unweighted) parameters (use cardinality instead of weight) *)
Section Classic_domination_parameters.

Definition ones : (G -> nat) := (fun _ => 1).

Let W1 : ({set G} -> nat) := (fun A => #|A|).

Lemma cardwset1 (A : {set G}) : #|A| = weight_set ones A.
Proof. by rewrite /weight_set sum1dep_card cardsE. Qed.

Lemma maxcardwset1 (p : pred {set G}) (A : {set G}) :
  p A -> #|arg_max A p W1| = #|arg_max A p (weight_set ones)|.
Proof.
  move => pA.
  case: arg_maxP => // B pB maxB.
  case: arg_maxP => // C pC maxC.
  have geqBC := maxB C pC.
  have geqCB := maxC B pB.
  rewrite /W1 /= in geqBC.
  rewrite -!cardwset1 /= in geqCB.
  by apply/eqP ; rewrite eqn_leq geqBC geqCB.
Qed.

Lemma mincardwset1 (p : pred {set G}) (A : {set G}) :
  p A -> #|arg_min A p W1| = #|arg_min A p (weight_set ones)|.
Proof.
  move => pA.
  case: arg_minP => // B pB minB.
  case: arg_minP => // C pC minC.
  have leqBC := minB C pC.
  have leqCB := minC B pB.
  rewrite /W1 /= in leqBC.
  rewrite -!cardwset1 /= in leqCB.
  by apply/eqP ; rewrite eqn_leq leqBC leqCB.
Qed.

(* The following lemmas state that if a set is maximum (i.e. has maximum cardinality), then
 * it is maximal, and if a set is minimum, then it is minimal. *)
Lemma maxcards_maxset (p : pred {set G}) (A : {set G}):
  p A -> (forall B, p B -> #|B| <= #|A|) -> maxset p A.
Proof.
  move => pA maxA. apply/maxsetP'; split => // B /proper_card; rewrite ltnNge.
  exact/contraNN/maxA.
Qed.

Lemma arg_maxcards (p : pred {set G}) (A : {set G}) : p A -> maxset p (arg_max A p W1).
Proof. by move => pA ; apply/maxcards_maxset ; case: arg_maxP. Qed.

Lemma mincards_minset (p : pred {set G}) (A : {set G}):
  p A -> (forall B, p B -> #|A| <= #|B|) -> minset p A.
Proof.
  move => pA minA. apply/minsetP'; split => // B /proper_card; rewrite ltnNge.
  exact/contraNN/minA.
Qed.

Lemma arg_mincards (p : pred {set G}) (A : {set G}) : p A -> minset p (arg_min A p W1).
Proof. by move => pA ; apply/mincards_minset ; case: arg_minP. Qed.

(* Definition of unweighted parameters and its conversion to weighted ones. *)

Definition ir : nat := #|arg_min inhb_max_irr max_irr W1|.

Fact eq_ir_ir1 : ir = ir_w ones.
Proof. by rewrite /ir /ir_w -cardwset1 (mincardwset1 inhb_max_irr_is_maximal_irredundant). Qed.

Definition gamma : nat := #|arg_min setT dominating W1|.

Fact eq_gamma_gamma1 : gamma = gamma_w ones.
Proof. by rewrite /gamma /gamma_w -cardwset1 (mincardwset1 domT). Qed.

Definition ii : nat := #|arg_min inhb_max_st max_st W1|.

Fact eq_ii_ii1 : ii = ii_w ones.
Proof. by rewrite /ii /ii_w -cardwset1 (mincardwset1 inhb_max_st_is_maximal_stable). Qed.

Definition alpha : nat := #|arg_max set0 stable W1|.

Fact eq_alpha_alpha1 : alpha = alpha_w ones.
Proof. by rewrite /alpha /alpha_w -cardwset1 (maxcardwset1 stable0). Qed.

Definition Gamma : nat := #|arg_max inhb_min_dom min_dom W1|.

Fact eq_Gamma_Gamma1 : Gamma = Gamma_w ones.
Proof. by rewrite /Gamma /Gamma_w -cardwset1 (maxcardwset1 inhb_min_dom_is_minimal_dominating). Qed.

Definition IR : nat := #|arg_max set0 irredundant W1|.

Fact eq_IR_IR1 : IR = IR_w ones.
Proof. by rewrite /IR /IR_w -cardwset1 (maxcardwset1 irr0). Qed.

(* Classic Cockayne-Hedetniemi domination chain. *)

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


(**********************************************************************************)
Section Weighted_degree.

(* TOTHINK: This is currently unused, delete or move elsewhere? *)

Variable G : sgraph.
Variable weight : G -> nat.
Hypothesis positive_weights : forall v : G, weight v > 0.

Let W := weight_set weight.

Definition deg_w (v : G) := W N(v).

Lemma ltn_deg_w_subwsetT1 (v : G) : deg_w v <= W setT - 1.
Proof.
  suff: deg_w v < W setT by move=> H ; rewrite (pred_Sn (deg_w v)) -subn1 (leq_sub2r 1 H).
  rewrite /deg_w ; apply: (ltnwset positive_weights).
  rewrite properT ; apply/negP => /eqP H1.
  move: (in_setT v) ; rewrite -H1 ; move/negP: (v_notin_opneigh v) ; contradiction.
Qed.

(* Minimum and maximum weighted degree of a graph. *)

(* x is a vertex of G (i.e. G is a non-empty graph) *)
Hypothesis x : G.

Let some_vertex_with_neighborhood (S : {set G}) := [exists v, S == N(v)].

Local Fact Nx_is_neighborhood_x : some_vertex_with_neighborhood N(x).
Proof. by rewrite /some_vertex_with_neighborhood ; apply/existsP ; exists x. Qed.

Definition delta_w := W (arg_min N(x) some_vertex_with_neighborhood W).

Fact delta_min (v : G) : delta_w <= deg_w v.
Proof.
  rewrite /delta_w ; case: (arg_minP W Nx_is_neighborhood_x) => A _ ; apply.
  by rewrite /some_vertex_with_neighborhood ; apply/existsP ; exists v.
Qed.

Fact delta_witness : exists v, deg_w v = delta_w.
Proof.
  rewrite /delta_w ; case: (arg_minP W Nx_is_neighborhood_x) => S exS _.
  move/existsP: exS => [u] /eqP SeqNu ; exists u ; by rewrite /deg_w SeqNu.
Qed.

Definition Delta_w := W (arg_max N(x) some_vertex_with_neighborhood W).

Fact Delta_max (v : G) : deg_w v <= Delta_w.
Proof.
  rewrite /Delta_w ; case: (arg_maxP W Nx_is_neighborhood_x) => A _ ; apply.
  by rewrite /some_vertex_with_neighborhood ; apply/existsP ; exists v.
Qed.

Fact Delta_witness : exists v, deg_w v = Delta_w.
Proof.
  rewrite /Delta_w ; case: (arg_maxP W Nx_is_neighborhood_x) => S exS _.
  move/existsP: exS => [u] /eqP SeqNu ; exists u ; by rewrite /deg_w SeqNu.
Qed.

End Weighted_degree.

Section Degree_of_vertices.

Variable G : sgraph.

Definition deg (v : G) := #|N(v)|.

Fact eq_deg_deg1 (v : G) : deg v = deg_w (@ones G) v.
Proof. by rewrite /deg /deg_w -cardwset1. Qed.

Lemma ltn_deg_subn1 (v : G) : deg v <= #|G| - 1.
Proof. by rewrite eq_deg_deg1 -cardsT (cardwset1 setT) ; exact: ltn_deg_w_subwsetT1. Qed.

(* Minimum and maximum weighted degree of a graph. *)

(* x is a vertex of G (i.e. G is a non-empty graph) *)
Hypothesis x : G.

Let some_vertex_with_degree (n : nat) := [exists v, deg v == n].

Local Fact degx_has_deg_x : exists (n : nat), some_vertex_with_degree n.
Proof. by rewrite /some_vertex_with_degree ; exists (deg x) ; apply/existsP ; exists x. Qed.

Local Fact ltn_someu_degu_subn1 (n : nat) : some_vertex_with_degree n -> n <= #|G| - 1.
Proof.
  rewrite /some_vertex_with_degree ; move/existsP => [u].
  move/eqP<- ; exact: ltn_deg_subn1.
Qed.

Definition delta := ex_minn degx_has_deg_x.

Lemma eq_delta_delta1 : delta = delta_w (@ones G) x.
Proof.
  rewrite /delta.
  have [n some_n n_min] := ex_minnP.
  apply/eqP ; rewrite eqn_leq ; apply/andP ; split.
  - apply: n_min ; rewrite /some_vertex_with_degree.
    apply/existsP ; elim: (delta_witness (@ones G) x) => u.
    move<- ; exists u ; apply/eqP.
    exact: eq_deg_deg1.
  - move: some_n.
    rewrite /some_vertex_with_degree.
    move/existsP => [u] /eqP <-.
    rewrite eq_deg_deg1.
    exact: delta_min.
Qed.

Definition Delta := ex_maxn degx_has_deg_x ltn_someu_degu_subn1.

Lemma eq_Delta_Delta1 : Delta = Delta_w (@ones G) x.
Proof.
  rewrite /Delta.
  have [n some_n n_max] := ex_maxnP.
  apply/eqP ; rewrite eqn_leq ; apply/andP ; split.
  - move: some_n.
    rewrite /some_vertex_with_degree.
    move/existsP => [u] /eqP <-.
    rewrite eq_deg_deg1.
    exact: Delta_max.
  - apply: n_max ; rewrite /some_vertex_with_degree.
    apply/existsP ; elim: (Delta_witness (@ones G) x) => u.
    move<- ; exists u ; apply/eqP.
    exact: eq_deg_deg1.
Qed.

End Degree_of_vertices.

Arguments deg_w : clear implicits.
Arguments delta_w : clear implicits.
Arguments Delta_w : clear implicits.
Arguments deg : clear implicits.
Arguments delta : clear implicits.
Arguments Delta : clear implicits.
