
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

Notation "N( G ; x )" := (@open_neigh G x) (at level 0, G at level 99, x at level 99).
Notation "N[ G ; x ]" := (@closed_neigh G x) (at level 0, G at level 99, x at level 99).
Notation "N( x )" := (open_neigh x) (at level 0, x at level 99, only parsing).
Notation "N[ x ]" := (closed_neigh x) (at level 0, x at level 99, only parsing).
Notation "x -*- y" := (cl_sedge x y) (at level 30).
Notation "V( G )" := (setT : {set G}) (at level 0, G at level 99).
Notation "E( G )" := (edges G) (at level 0, G at level 99).
Notation "NS( G ; D )" := (@open_neigh_set G D) (at level 0, G at level 99, D at level 99).
Notation "NS( D )" := (open_neigh_set D) (at level 0, D at level 99).
Notation "NS[ G ; D ]" := (@closed_neigh_set G D) (at level 0, G at level 99, D at level 99).
Notation "NS[ D ]" := (closed_neigh_set D) (at level 0, D at level 99).


(**********************************************************************************)
Section Basic_Facts_Neighborhoods.

Variable G : sgraph.
Implicit Types (u v : G).

Lemma sg_opneigh u v : (u -- v) = (u \in N(v)).
Proof. by rewrite /open_neigh in_set sg_sym. Qed.

Lemma v_notin_opneigh v : v \notin N(v).
Proof. by rewrite -sg_opneigh sg_irrefl. Qed.

Lemma clsg_clneigh u v : (u -*- v) = (u \in N[v]).
Proof. by rewrite /closed_neigh in_set in_set1 -sg_opneigh. Qed.

Lemma cl_sg_sym : symmetric (@cl_sedge G). (* cl_sedge u v = cl_sedge v u *)
Proof. rewrite /symmetric /cl_sedge /closed_neigh => x y ; by rewrite sg_sym eq_sym. Qed.

Lemma cl_sg_refl : reflexive (@cl_sedge G). (* cl_sedge u u = true *)
Proof. by move => x; rewrite /cl_sedge eqxx. Qed.

Lemma v_in_clneigh v : v \in N[v].
Proof. by rewrite -clsg_clneigh cl_sg_refl. Qed.

Lemma opneigh_proper_clneigh v : N(v) \proper N[v].
Proof. 
  apply/properP; rewrite subsetUr; split => //.
  by exists v; rewrite !inE ?eqxx sgP.
Qed.

Proposition sg_in_edge_set u v : [set u; v] \in E(G) = (u -- v).
Proof. 
  apply/edgesP/idP => [[x] [y] []|]; last by exists u; exists v.
  by case/doubleton_eq_iff => -[-> ->] //; rewrite sgP.
Qed.

Proposition empty_open_neigh : NS(set0 : {set G}) = set0.
Proof. by rewrite /open_neigh_set big_set0. Qed.

Proposition empty_closed_neigh : NS[set0 : {set G}] = set0.
Proof. by rewrite /closed_neigh_set big_set0. Qed.

Variables D1 D2 : {set G}.

Proposition neigh_in_open_neigh : {in D1, forall v, N(v) \subset NS(D1)}.
Proof.
  move=> v vinD1.
  apply/subsetP => x xinD1.
  rewrite /open_neigh_set.
  apply/bigcupP.
  by exists v.
Qed.

Proposition neigh_in_closed_neigh : {in D1, forall v, N[v] \subset NS[D1]}.
Proof.
  move=> v vinD1.
  apply/subsetP => x xinD1.
  rewrite /closed_neigh_set.
  apply/bigcupP.
  by exists v.
Qed.

Proposition D_in_closed_neigh_set : D1 \subset NS[D1].
Proof.
  apply/subsetP => x xinD1.
  rewrite /closed_neigh_set.
  apply/bigcupP.
  exists x.
  by rewrite xinD1.
  exact: v_in_clneigh.
Qed.

Proposition dominated_belongs_to_open_neigh_set u v : u \in D1 -> u -- v -> v \in NS(D1).
Proof.
  move=> uinD1 adjuv.
  apply/bigcupP.
  exists u => //.
  by rewrite -sg_opneigh sg_sym.
Qed.

Proposition open_neigh_set_subset_closed_neigh_set : NS(D1) \subset NS[D1].
Proof.
  apply/subsetP => u.
  rewrite /open_neigh_set /closed_neigh_set.
  move/bigcupP.
  elim=> v vinD1 uinNv.
  apply/bigcupP.
  exists v => [// | ].
  by rewrite /closed_neigh in_setU uinNv orbT.
Qed.

Proposition dominated_belongs_to_closed_neigh_set u v : u \in D1 -> u -- v -> v \in NS[D1].
Proof.
  move=> uinD1 adjuv.
  apply: (subsetP open_neigh_set_subset_closed_neigh_set v).
  exact: dominated_belongs_to_open_neigh_set adjuv.
Qed.

Proposition closed_neigh_set_subset : D1 \subset D2 -> NS[D1] \subset NS[D2].
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
Section Degree_of_vertices.

Variable G : sgraph.

Definition deg (v : G) := #|N(v)|.

Lemma max_deg_ltn_n_minus_one (v : G) : deg v <= #|V(G)| - 1.
Proof.
  rewrite cardsT.
  suff: deg v < #|G| by move=> H ; rewrite (pred_Sn (deg v)) -subn1 (leq_sub2r 1 H).
  have H1: #|N[v]| <= #|G| by rewrite max_card.
  rewrite /deg.
  exact: leq_trans (proper_card (opneigh_proper_clneigh v)) H1.
Qed.

Hypothesis G_not_empty : V(G) != set0.

Let some_vertex_with_degree (n : nat) := [exists v, deg v == n].

Local Lemma some_degree_exists : exists (n : nat), some_vertex_with_degree n.
Proof.
  move/set0Pn: G_not_empty.
  elim=> w _.
  exists (deg w).
  rewrite /some_vertex_with_degree.
  apply/existsP.
  by exists w.
Qed.

Local Lemma some_degree_ltn_n_minus_one (n : nat) : some_vertex_with_degree n -> n <= #|V(G)| - 1.
Proof.
  move/existsP.
  elim=> w.
  rewrite eq_sym.
  move/eqP->.
  exact: max_deg_ltn_n_minus_one.
Qed.

Definition minimum_deg := ex_minn some_degree_exists.

Definition maximum_deg := ex_maxn some_degree_exists some_degree_ltn_n_minus_one.

Lemma minimum_deg_is_minimum (v : G) : deg v >= minimum_deg.
Proof.
  have H1: some_vertex_with_degree (deg v).
  rewrite /some_vertex_with_degree.
  apply/existsP.
  by exists v.
  move: (ex_minnP some_degree_exists).
  rewrite -/minimum_deg.
  move=> [n _ n_is_minimum].
  exact: (n_is_minimum (deg v) H1).
Qed.

Lemma maximum_deg_is_minimum (v : G) : deg v <= maximum_deg.
Proof.
  have H1: some_vertex_with_degree (deg v).
  rewrite /some_vertex_with_degree.
  apply/existsP.
  by exists v.
  move: (ex_maxnP some_degree_exists some_degree_ltn_n_minus_one).
  rewrite -/maximum_deg.
  move=> [n _ n_is_maximum].
  exact: (n_is_maximum (deg v) H1).
Qed.

Lemma maximum_deg_ltn_n_minus_one : maximum_deg <= #|V(G)| - 1.
Proof.
  (* we first obtain the vertex "w" such that deg w = meximum_deg *)
  move: (ex_maxnP some_degree_exists some_degree_ltn_n_minus_one).
  rewrite -/maximum_deg.
  move=> [n n_is_from_someone _].
  move/existsP: n_is_from_someone.
  elim=> w.
  move/eqP<-.
  exact: (max_deg_ltn_n_minus_one w).
Qed.

End Degree_of_vertices.


(**********************************************************************************)
(** * Domination Theory *)
Section Domination_Theory.

Variable G : sgraph.


(**********************************************************************************)
(** * Maximal and minimal sets *)
Section MaxMin_sets.

Variable p : pred {set G}.     (* p : {set G} -> bool *)
Variable D : {set G}.

Definition maximal : bool := p D && [forall F : {set G}, (D \proper F) ==> ~~ p F].

Definition minimal : bool := p D && [forall F : {set G}, (F \proper D) ==> ~~ p F].

Proposition maximalP : reflect (p D /\ (forall F : {set G}, D \proper F -> ~ p F)) maximal.
Proof.
  rewrite /maximal.
  apply: (iffP andP).
  (* first case: -> *)
  move=> [pD /forallP H1].
  split=> //.
  move=> F.
  move: (H1 F).
  move=> /implyP H2 DproperF.
  move: (H2 DproperF).
  by apply/negP.
  (* second case: -> *)
  move=> [pD H3].
  split=> //.
  apply/forallP => F.
  apply/implyP => DproperF.
  move: (H3 F DproperF).
  by move/negP.
Qed.

Proposition minimalP : reflect (p D /\ (forall F : {set G}, F \proper D -> ~ p F)) minimal.
Proof.
  rewrite /minimal.
  apply: (iffP andP).
  (* first case: -> *)
  move=> [pD /forallP H1].
  split=> //.
  move=> F.
  move: (H1 F).
  move=> /implyP H2 FproperD.
  move: (H2 FproperD).
  by apply/negP.
  (* second case: -> *)
  move=> [pD H3].
  split=> //.
  apply/forallP => F.
  apply/implyP => FproperD.
  move: (H3 F FproperD).
  by move/negP.
Qed.

Lemma maximal_eq_maxset : maximal <-> (maxset p D).
Proof.
  rewrite /iff ; split.
  (* first case: -> *)
  move/maximalP=> [pD H1].
  apply/maxsetP ; split => //.
  move=> F pF DsubF.
  symmetry ; apply/eqP.
  rewrite eqEproper DsubF andTb.
  move: pF.
  apply: contraL.
  move=> DproperF.
  apply/negP.
  exact: (H1 F DproperF).
  (* second case: <- *)
  move/maxsetP=> [pD H2].
  rewrite /maximal.
  apply/andP ; split => //.
  apply/forallP => F.
  rewrite implybN /proper negb_and -implybE negbK.
  apply/implyP => pF.
  apply/implyP => DsubF.
  by move: (H2 F pF DsubF)->.
Qed.

Lemma minimal_eq_minset : minimal <-> (minset p D).
Proof.
  rewrite /minimal /iff ; split.
  (* first case: -> *)
  move/minimalP=> [pD H1].
  apply/minsetP ; split => //.
  move=> F pF FsubD.
  apply/eqP.
  rewrite eqEproper FsubD andTb.
  move: pF.
  apply: contraL.
  move=> FproperD.
  apply/negP.
  exact: (H1 F FproperD).
  (* second case: <- *)
  move=> /minsetP [pD H2].
  rewrite /minimal.
  apply/andP ; split => //.
  apply/forallP => F.
  rewrite implybN /proper negb_and -implybE negbK.
  apply/implyP => pF.
  apply/implyP => FsubD.
  by move: (H2 F pF FsubD)->.
Qed.

End MaxMin_sets.


(**********************************************************************************)
Section MaxMin_sets_existence.

Variable p : pred {set G}.     (* p : {set G} -> bool *)
Variable F : {set G}.          (* some set satisfying p *)
Hypothesis pF : p F.           (* the proof that F satisfies p *)

Definition ex_maximal : {set G} := s2val (maxset_exists pF).

Definition ex_minimal : {set G} := s2val (minset_exists pF).

Lemma maximal_exists : maximal p ex_maximal.
Proof. rewrite maximal_eq_maxset ; exact: s2valP (maxset_exists pF). Qed.

Lemma minimal_exists : minimal p ex_minimal.
Proof. rewrite minimal_eq_minset. exact: s2valP (minset_exists pF). Qed.

End MaxMin_sets_existence.

(* "argument" policy:
   ex_maximal and ex_minimal requires the following arguments:
     the property, a set satisfying the property and a proof of that
   in order to apply maximal_exists and minimal_exists, it is required the same things as before. *)
Arguments ex_maximal : clear implicits.
Arguments ex_minimal : clear implicits.
Arguments maximal_exists : clear implicits.
Arguments minimal_exists : clear implicits.


(**********************************************************************************)
(** * Independence systems, hereditary and superhereditary properties *)
Section Independence_system_definitions.

Variable p : pred {set G}.     (* p : {set G} -> bool *)

Definition hereditary : bool :=
          [forall D : {set G}, forall F : {set G}, (F \subset D) ==> p D ==> p F].

Definition superhereditary : bool :=
          [forall D : {set G}, forall F : {set G}, (D \subset F) ==> p D ==> p F].

Proposition hereditaryP : reflect
          (forall D F : {set G}, (F \subset D) -> p D -> p F) hereditary.
Proof.
  rewrite /hereditary.
  apply: (iffP forallP).
  (* first case: -> *)
  move=> H1 D F FsubD pD.
  move: (H1 D).
  move/forallP=> /(_ F).
  by rewrite FsubD pD !implyTb.
  (* second case: -> *)
  move=> H2 D.
  apply/forallP => F.
  apply/implyP => FsubD.
  apply/implyP.
  exact: (H2 D F FsubD).
Qed.

Proposition superhereditaryP : reflect
          (forall D F : {set G}, (D \subset F) -> p D -> p F) superhereditary.
Proof.
  rewrite /superhereditary.
  apply: (iffP forallP).
  (* first case: -> *)
  move=> H1 D F DsubF pD.
  move: (H1 D).
  move/forallP=> /(_ F).
  by rewrite DsubF pD !implyTb.
  (* second case: -> *)
  move=> H2 D.
  apply/forallP => F.
  apply/implyP => DsubF.
  apply/implyP.
  exact: (H2 D F DsubF).
Qed.

Variable D : {set G}.

Theorem maximal_altdef : hereditary ->
          (maximal p D <-> (p D && [forall v : G, (v \notin D) ==> ~~ p (D :|: [set v])])).
Proof.
  move=> p_hereditary.
  rewrite /iff ; split.
  (* first case: -> *)
  - rewrite /maximal.
    move=> /andP [pD /forallP H1].
    rewrite pD andTb.
    apply/forallP => v.
    apply/implyP => vnotinD.
    move/implyP: (H1 (D :|: [set v]))-> => [ // | ].
    (* it is enough to prove that D \proper D cup {v} *)
    by rewrite properUl // sub1set vnotinD.
  (* second case: <- *)
  - move=> /andP [pD /forallP H2].
    apply/maximalP ; split=> //.
    move=> F /properP [DsubF].
    elim=> v vinF.
    move=> vnotinD.
    apply/negP.
    move/implyP: (H2 v) => /(_ vnotinD).
    apply: contra.
    (* in order to apply the hereditary property, we first prove that
       D cup {v} is contained in F. *)
    have DcupvsubF: D :|: [set v] \subset F.
    { apply/subsetP => x.
      rewrite in_setU.
      case/orP => [ |xisv].
      + exact: (subsetP DsubF).
      + rewrite in_set1 in xisv.
        by move/eqP: xisv ->. }
    move/hereditaryP: p_hereditary.
    by move=> /(_ F (D :|: [set v]) DcupvsubF).
Qed.

Theorem minimal_altdef : superhereditary ->
          (minimal p D <-> (p D && [forall v : G, (v \in D) ==> ~~ p (D :\: [set v])])).
Proof.
  move=> p_superhereditary.
  rewrite /minimal /iff ; split.
  (* first case: -> *)
  - move=> /andP [pD /forallP H1].
    rewrite pD andTb.
    apply/forallP => v.
    apply/implyP => vinD.
    move/implyP: (H1 (D :\: [set v]))-> => [ // | ].
    (* it is enough to prove that D - {v} \proper D *)
    exact: properD1.
  (* second case: <- *)
  - move=> /andP [pD /forallP H2].
    rewrite pD andTb.
    apply/forallP => F.
    apply/implyP => /properP [FsubD].
    elim=> v vinD.
    move/implyP: (H2 v) => H3 vnotinF.
    move: (H3 vinD).
    apply: contra.
    (* in order to apply the superhereditary property, we first prove that
       F is contained in D - {v}. *)
    have FsubDminusv: F \subset D :\: [set v].
    { apply/subsetP => x xinF.
      rewrite in_setD (subsetP FsubD x xinF) andbT.
      move: vnotinF.
      apply: contra => xisv.
      rewrite in_set1 in xisv.
      by move/eqP: xisv <-. }
    move/superhereditaryP: p_superhereditary.
    by move=> /(_ F (D :\: [set v]) FsubDminusv).
Qed.

End Independence_system_definitions.


(**********************************************************************************)
(** * Basic definitions about positive weighted sets and parameters *)
Section Weighted_Sets.

Variable weight : G -> nat.
Hypothesis positive_weights : forall v : G, weight v > 0.
Variable p : pred {set G}.     (* p : {set G} -> bool *)
Variable D : {set G}.

Definition weight_set (S : {set G}) := \sum_(v in G | v \in S) weight v.

Lemma weight_set_natural : forall A : {set G}, weight_set A >= 0.
Proof. move=> A ; exact: leq0n. Qed.

Lemma empty_set_zero_weight : D = set0 <-> weight_set D = 0.
Proof.
  rewrite /iff ; split.
  (* first case: -> *)
  move=> Dempty.
  rewrite /weight_set.
  move: Dempty ->.
  exact: big_set0.
  (* second case: <- *)
  move=> /eqP weightzero.
  apply/eqP.
  move: weightzero.
  apply: contraLR => /set0Pn.
  elim=> x xinD.
  rewrite /weight_set.
  rewrite (eq_bigl (fun v => v \in ((D :\: [set x]) :|: [set x]))) ; last first.
  move=> i ; by rewrite [in X in X = _](set_minus_union1 xinD).
  rewrite lt0n_neq0 //.
  (* now, we need to prove that the summation over (D - {x}) cup {x} is positive *)
  rewrite sum_disjoint_union ; last by rewrite set_minus_disjoint.
  rewrite big_set1 addnC ltn_addr => [// | ].
  exact: positive_weights x.
Qed.

Lemma subsets_weight : forall A B : {set G}, A \subset B -> weight_set A <= weight_set B.
Proof.
  move=> A B AsubB.
  rewrite /weight_set.
  rewrite [in X in _ <= X](eq_bigl (fun v => v \in ((B :\: A) :|: A))) ; last first.
  move=> i ; by rewrite [in X in X = _](set_minus_union AsubB).
  rewrite (sum_disjoint_union weight (set_minus_disjoint B A)).
  exact: leq_addl.
Qed.

Lemma proper_sets_weight : forall A B : {set G}, A \proper B -> weight_set A < weight_set B.
Proof.
  move=> A B /properP [AsubB].
  elim=> x xinB xnotinA.
  have AinBminusx: A \subset B :\: [set x].
  { apply/subsetP => v vinA.
    move: (subsetP AsubB v vinA) => vinB.
    apply/setD1P.
    split=> [ | //].
    move: xnotinA.
    apply: contra => visx.
    by move/eqP: visx <-. }
  move: (subsets_weight AinBminusx) => wAleqwBminusx.
  suff wBminusxleqwB: weight_set (B :\: [set x]) < weight_set B by
    exact: leq_ltn_trans wAleqwBminusx wBminusxleqwB.
  (* it is enough to prove weight_set (B - {x}) < weight_set B *)
  rewrite /weight_set.
  rewrite [in X in _ < X](eq_bigl (fun v => v \in ((B :\: [set x]) :|: [set x]))) ; last first.
  move=> i ; by rewrite [in X in X = _](set_minus_union1 xinB).
  rewrite sum_disjoint_union ; last exact: set_minus_disjoint.
  rewrite big_set1.
  rewrite -[in X in X < _](addn0 (\sum_(v in G | v \in (B :\: [set x])) weight v)).
  rewrite ltn_add2l.
  exact: positive_weights x.
Qed.

Definition maximum : bool := p D && [forall F : {set G}, p F ==> (weight_set F <= weight_set D)].

Definition minimum : bool := p D && [forall F : {set G}, p F ==> (weight_set D <= weight_set F)].

Proposition maximumP : reflect
          (p D /\ (forall F : {set G}, p F -> weight_set F <= weight_set D)) maximum.
Proof.
  rewrite /maximum.
  apply: (iffP andP).
  (* first case: -> *)
  move=> [pD /forallP H1].
  split=> //.
  move=> F pF.
  move: (H1 F).
  by move/implyP=> /(_ pF).
  (* second case: <- *)
  move=> [pD H2].
  split=> //.
  apply/forallP=> F.
  apply/implyP.
  exact: (H2 F).
Qed.

Proposition minimumP : reflect
          (p D /\ (forall F : {set G}, p F -> weight_set D <= weight_set F)) minimum.
Proof.
  rewrite /minimum.
  apply: (iffP andP).
  (* first case: -> *)
  move=> [pD /forallP H1].
  split=> //.
  move=> F pF.
  move: (H1 F).
  by move/implyP=> /(_ pF).
  (* second case: <- *)
  move=> [pD H2].
  split=> //.
  apply/forallP=> F.
  apply/implyP.
  exact: (H2 F).
Qed.

Lemma maximum_is_maximal : maximum -> maximal p D.
Proof.
  move/maximumP=> [pD H1].
  apply/maximalP.
  split=> //.
  move=> F DproperF pF.
  move: (H1 F pF).
  move: (proper_sets_weight DproperF).
  rewrite ltnNge => /negP.
  contradiction.
Qed.

Lemma minimum_is_minimal : minimum -> minimal p D.
Proof.
  move/minimumP=> [pD H1].
  apply/minimalP.
  split=> //.
  move=> F FproperD pF.
  move: (H1 F pF).
  move: (proper_sets_weight FproperD).
  rewrite ltnNge => /negP.
  contradiction.
Qed.

End Weighted_Sets.


(**********************************************************************************)
Section Argument_weighted_sets.

Variable weight : G -> nat.
Variable p : pred {set G}.     (* p : {set G} -> bool *)
Variable F : {set G}.          (* some set satisfying p *)
Hypothesis pF : p F.           (* the proof that F satisfies p *)

Definition maximum_set : {set G} := [arg max_(D > F | p D) weight_set weight D].

Definition minimum_set : {set G} := [arg min_(D < F | p D) weight_set weight D].

Lemma maximum_set_p : p maximum_set.
Proof. rewrite /maximum_set ; by case: (arg_maxP (fun D => weight_set weight D) pF). Qed.

Lemma minimum_set_p : p minimum_set.
Proof. rewrite /minimum_set ; by case: (arg_minP (fun D => weight_set weight D) pF). Qed.

Lemma maximum_set_welldefined : maximum weight p maximum_set.
Proof.
  rewrite /maximum_set.
  case: (arg_maxP (fun D => weight_set weight D) pF).
  move=> D pD H1.
  apply/maximumP.
  by split.
Qed.

Lemma minimum_set_welldefined : minimum weight p minimum_set.
Proof.
  rewrite /minimum_set.
  case: (arg_minP (fun D => weight_set weight D) pF).
  move=> D pD H1.
  apply/minimumP.
  by split.
Qed.

End Argument_weighted_sets.

(* "argument" policy:
   maximum_set and minimum_set requires the following arguments:
     the weight vector, the property and a set (should satisfies the property)
   in order to apply maximum_set_welldefined and minimum_set_welldefined, it is required:
     the weight vector, the property, a set satisfying the property and a proof of that *)
Arguments maximum_set_welldefined : clear implicits.
Arguments minimum_set_welldefined : clear implicits.


(**********************************************************************************)
(** * Definitions of stable, dominating and irredundant sets *)
Section Stable_Set.

Variable S : {set G}.

Definition stable : bool := [forall u : G, forall v : G, (u \in S) ==> (v \in S) ==> ~~ (u -- v)].

Definition stable_alt : bool := NS(S) :&: S == set0.

(* TO DO: @chdoc suggests to replace by:

Proposition stableP : reflect {in S&, forall u v, ~~ u -- v} stable.
Proposition stableF : stable -> {in S&, forall u v, u -- v = false}.

The rationale is that boolean negations on boolean atoms are quite well
behaved (e.g., rewriting the boolean makes the negation simplify). *)

Proposition stableP : reflect {in S&, forall u v, ~ u -- v} stable.
Proof.
  rewrite /stable.
  apply: (iffP forallP).
  move=> H1 u v uinS vinS.
  move/forallP: (H1 u) => H2.
  apply/negP.
  by rewrite (implyP ((implyP (H2 v)) uinS) vinS).
  move=> H2 u.
  apply/forallP => v.
  apply/implyP => uinS.
  apply/implyP => vinS.
  apply/negP.
  exact: H2.
Qed.

Theorem stable_eq_stable_alt : stable <-> stable_alt.
Proof.
  rewrite /stable /stable_alt /iff ; split.
  apply: contraLR.
  (* first case: -> *)
  - move/set0Pn.
    elim=> u.
    rewrite in_setI => [/andP[uinNS uinS] ].
    move/bigcupP: uinNS.
    elim=> v vinS.
    rewrite -sg_opneigh => adjuv.
    rewrite negb_forall.
    apply/existsP.
    exists u.
    rewrite negb_forall.
    apply/existsP.
    exists v.
    rewrite negb_imply uinS andTb.
    by rewrite negb_imply vinS andTb adjuv.
  (* second case: <- *)
  - rewrite eqEsubset => /andP [NScapSsub0 _].
    apply/stableP.
    move=> u v uinS vinS adjuv.
    have vinNScapS: v \in NS(S) :&: S.
    { move: (dominated_belongs_to_open_neigh_set uinS adjuv) => vinNS.
      by rewrite in_setI vinNS vinS. }
    move: (subsetP NScapSsub0 v vinNScapS).
    by rewrite in_set0.
Qed.

End Stable_Set.

(* the empty set is stable *)
Lemma st_empty : stable set0.
Proof. apply/stableP ; by move=> u v ; rewrite in_set0. Qed.

(* if D is stable, any subset of D is also stable *)
Lemma st_hereditary : hereditary stable.
Proof.
  apply/hereditaryP.
  move=> D F FsubD /stableP Dstable.
  apply/stableP => u v uinF vinF.
  move: (subsetP FsubD u uinF) => uinD.
  move: (subsetP FsubD v vinF) => vinD.
  exact: Dstable u v uinD vinD.
Qed.


(**********************************************************************************)
Section Dominating_Set.

Variable D : {set G}.

Definition dominating : bool := [forall v : G, (v \notin D) ==> [exists u : G, (u \in D) && (u -- v)]].

Definition dominating_alt : bool := V(G) == NS[D].

Proposition dominatingP : reflect
          (forall v : G, v \notin D -> exists u : G, u \in D /\ u -- v) dominating.
Proof.
  rewrite /dominating.
  apply: (iffP forallP).
  (* first case: -> *)
  move=> H1 v vnotinD.
  move/implyP: (H1 v) => H2.
  move/existsP: (H2 vnotinD).
  elim=> x /andP [xinD adjxv].
  by exists x.
  (* second case: <- *)
  move=> H3 x.
  apply/implyP=> xnotinD.
  move: (H3 x xnotinD).
  elim=> u [uinD adjux].
  apply/existsP.
  exists u.
  by apply/andP.
Qed.

Theorem dominating_eq_dominating_alt : dominating <-> dominating_alt.
Proof.
  rewrite /dominating /dominating_alt /iff ; split.
  (* first case: -> *)
  move/forallP=> H1.
  rewrite eqEsubset subsetT andbT.
  (* it is enough to prove V(G) \subset N[D] *)
  apply/subsetP => x.
  move: (set_minus_union (subsetT D)) ->.
  rewrite in_setU.
  case/orP ; [ | apply/subsetP ; exact: D_in_closed_neigh_set].
  (* case when x \notin D *)
  rewrite in_setD => /andP [xnotinD _].
  move/implyP: (H1 x) => H2.
  move/existsP: (H2 xnotinD).
  elim=> u /andP [uinD adjux].
  exact: dominated_belongs_to_closed_neigh_set uinD adjux.
  (* second case: <- *)
  move=> VisND.
  apply/dominatingP => v vnotinD.
  move/eqP: VisND (in_setT v) -> => /bigcupP.
  elim=> [x xinD vinNx].
  rewrite /closed_neigh in_setU /open_neigh !inE in vinNx.
  case/predU1P : vinNx => [visx|adjxv]; last by exists x.
  by subst; contrab.
Qed.

End Dominating_Set.

(* V(G) is dominating *)
Lemma dom_VG : dominating V(G).
Proof.
  rewrite dominating_eq_dominating_alt.
  rewrite /dominating_alt eqEsubset subsetT andbT.
  exact: D_in_closed_neigh_set.
Qed.

(* if D is dominating, any supraset of D is also dominating *)
Lemma dom_superhereditary : superhereditary dominating.
Proof.
  apply/superhereditaryP.
  move=> D F DsubF /dominatingP Ddom.
  apply/dominatingP => v vnotinF.
  have vinVminusF: v \in V(G) :\: F by rewrite in_setD in_setT andbT.
  (* if D is contained in F, then some v in V(G)-F also belongs to V(G)-D *)
  move: (subsetP (setDS setT DsubF)).
  move=> /(_ v vinVminusF).
  rewrite in_setD in_setT andbT => vinVminusD.
  elim: (Ddom v vinVminusD) => w [winD adjwv].
  exists w.
  split=> [ | //].
  exact: (subsetP DsubF) w winD.
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
  move=> v w.
  rewrite /private.
  apply: (iffP andP).
  (* first case: -> *)
  move=> [vdomw /forallP H1] ; split=> //.
  move=> u uinD udomw.
  move: (H1 u).
  rewrite uinD implyTb udomw implyTb.
  by move/eqP->.
  (* second case: <- *)
  move=> [vdomw H2] ; split=> //.
  apply/forallP => u.
  apply/implyP=> uinD.
  apply/implyP=> udomw.
  move: (H2 u uinD udomw).
  by move->.
Qed.

Theorem private_belongs_to_private_set : forall v w : G, (private v w) <-> (w \in private_set v).
Proof.
  rewrite /private_set /iff ; split.
  (* first case: -> *)
  - move/privateP => [vdomw H1].
    rewrite in_setD /closed_neigh_set.
    apply/andP.
    split ; [ | by rewrite -clsg_clneigh cl_sg_sym ].
    apply/bigcupP.
    elim=> x xinDminusv winNx.
    move: xinDminusv.
    rewrite in_setD in_set1 => /andP [xnotv xinD].
    move: winNx.
    rewrite -clsg_clneigh cl_sg_sym => xdomw.
    move: (H1 x xinD xdomw).
    move/eqP: xnotv.
    contradiction.
  (* second case: <- *)
  - rewrite in_setD /closed_neigh_set.
    move=> /andP [wnotincup winNv].
    apply/privateP ; split ; [ by rewrite cl_sg_sym clsg_clneigh | ].
    move=> u uinD udomw.
    apply/eqP.
    move: wnotincup.
    apply: contraR => unotv.
    apply/bigcupP.
    exists u.
    + by rewrite /= in_setD uinD andbT in_set1.
    + by rewrite -clsg_clneigh cl_sg_sym.
Qed.

Lemma private_set_not_empty : {in D, forall v, (private_set v != set0) <-> (exists w : G, private v w)}.
Proof.
  move=> v.
  rewrite /private_set /iff  ; split.
  (* first case: -> *)
  move/set0Pn.
  elim=> w H2.
  exists w.
  by rewrite private_belongs_to_private_set.
  (* second case: <- *)
  elim=> w.
  rewrite private_belongs_to_private_set => H1.
  apply/set0Pn.
  by exists w.
Qed.

(* This alternative definition of private_set contemplates cases where v \notin D.
 * If v belongs to D, it returns the set of private vertices; otherwise, it returns an empty set. *)
Definition private_set' (v : G) := NS[D :&: [set v]] :\: NS[D :\: [set v]].

Lemma private_set'_equals_private_set : {in D, forall v, private_set' v == private_set v}.
Proof.
  move=> v vinD.
  rewrite /private_set /private_set'.
  suff: N[v] = NS[D :&: [set v]] by move->.
  move: (set_intersection_singleton vinD)->.
  apply/eqP ; rewrite eqEsubset ; apply/andP ; split.
  - apply: neigh_in_closed_neigh.
    by rewrite in_set1.
  - apply/subsetP => x.
    move/bigcupP.
    elim=> z ; rewrite in_set1.
    by move/eqP->.
Qed.

Lemma private_set'_equals_empty : forall v : G, v \notinD -> (private_set' v == set0).
Proof.
  move=> v vnotinD.
  rewrite /private_set'.
  move: (set_intersection_empty vnotinD)->.
  move: empty_closed_neigh->.
  apply/eqP.
  exact: set0D.
Qed.

Definition irredundant : bool := [forall v : G, (v \in D) ==> (private_set v != set0)].

Proposition irredundantP: reflect {in D, forall v, (private_set v != set0)} irredundant.
Proof.
  rewrite /irredundant.
  apply: (iffP forallP).
  (* first case: -> *)
  move=> H1 v vinD.
  by move/implyP: (H1 v) => /(_ vinD).
  (* second case: <- *)
  move=> H2 v.
  apply/implyP=> vinD.
  by move: (H2 v vinD).
Qed.

End Irredundant_Set.

(* the empty set is irredundant *)
Lemma irr_empty : irredundant set0.
Proof. apply/irredundantP => v ; by rewrite in_set0. Qed.

(* if D is irredundant, any subset of D is also irredundant *)
Lemma irr_hereditary : hereditary irredundant.
Proof.
  apply/hereditaryP.
  move=> D F FsubD /irredundantP Dirr.
  apply/irredundantP => v vinF.
  move: (subsetP FsubD v vinF) => vinD.
  move: (Dirr v vinD).
  rewrite (private_set_not_empty vinD) (private_set_not_empty vinF).
  elim=> x /privateP [vdomx H1].
  exists x.
  apply/privateP.
  split=> //.
  move=> u uinF udomx.
  move: (subsetP FsubD u uinF) => uinD.
  exact: (H1 u uinD udomx).
Qed.


(**********************************************************************************)
(** * Fundamental facts about Domination Theory *)
Section Relations_between_stable_dominating_irredundant_sets.

Variable D : {set G}.

(* A stable set D is maximal iff D is stable and dominating
 * See Prop. 3.5 of Fundamentals of Domination *)
Theorem maximal_st_iff_st_dom : maximal stable D <-> (stable D /\ dominating D).
Proof.
  rewrite maximal_altdef ; last exact: st_hereditary.
  rewrite /iff ; split ; last first.
  (* second case: <- *)
  - move=> [ stableD /dominatingP dominatingD].
    rewrite stableD andTb.
    apply/forallP => v.
    apply/implyP => vnotinD.
    rewrite /stable.
    rewrite negb_forall.
    apply/existsP.
    exists v.
    rewrite negb_forall.
    apply/existsP.
    move: (dominatingD v vnotinD).
    elim=> w [winD adjwv].
    exists w.
    rewrite negb_imply.
    apply/andP ; split.
    + by rewrite set1Ur.
    + rewrite negb_imply.
      rewrite negbK sg_sym adjwv andbT.
      by rewrite set1Ul.
  (* first case: -> *)
  - move/andP=> [stableD /forallP H1].
    split=> //.
    rewrite /dominating.
    apply/forallP.
    move=> x.
    apply/implyP.
    move=> xnotinD.
    apply/existsP.
    move/implyP: (H1 x).
    move=> /(_ xnotinD).
    rewrite /stable negb_forall.
    move/existsP.
    elim=> w.
    rewrite negb_forall.
    move/existsP.
    elim=> z.
    rewrite negb_imply negb_imply negbK.
    move=> /andP [winDcupx /andP [zinDcupx adjwz]].
    case: (boolP (z == x)).
    (* case z = x *)
    + move/eqP=> zisx.
      move: adjwz.
      rewrite zisx => adjwx.
      exists w.
      rewrite adjwx andbT.
      move: winDcupx.
      rewrite in_setU in_set1.
      move: (sg_edgeNeq adjwx) ->.
      by rewrite orbF.
    (* case z != x *)
    + move=> zisnotx.
      have zinD: z \in D.
      { move: zinDcupx.
        rewrite in_setU in_set1.
        move/negbTE: zisnotx ->.
        by rewrite orbF. }
      exists z.
      rewrite zinD andTb.
      move: winDcupx.
      rewrite in_setU in_set1.
      case/orP ; last first.
      (* case w == x *)
      * move/eqP=> wisx.
        by rewrite sg_sym -wisx.
      (* case w \in D *)
      * move=> winD.
        move/stableP: stableD.
        move=> /(_ w z winD zinD).
        contradiction.
Qed.

(* A maximal stable set is minimal dominating
 * See Prop. 3.6 of Fundamentals of Domination *)
Theorem maximal_st_is_minimal_dom : maximal stable D -> minimal dominating D.
Proof.
  rewrite maximal_st_iff_st_dom.
  move=> [stableD dominatingD].
  rewrite minimal_altdef ; last apply dom_superhereditary.
  apply/andP ; split=>//.
  apply/forallP.
  move=> x.
  apply/implyP=> xinD.
  rewrite /dominating.
  rewrite negb_forall.
  apply/existsP.
  exists x.
  rewrite negb_imply.
  apply/andP ; split ; [ by rewrite in_setD1 eq_refl andFb | ].
  rewrite negb_exists.
  apply/forallP=> y.
  rewrite negb_and.
  rewrite -implybE.
  apply/implyP.
  rewrite in_setD1 => /andP [_ yinD].
  rewrite sg_sym.
  apply/negP.
  move/stableP: stableD.
  by move=> /(_ x y xinD yinD).
Qed.

(* A dominating set D is minimal iff D is dominating and irredundant
 * See Prop. 3.8 of Fundamentals of Domination *)
Theorem minimal_dom_iff_dom_irr : minimal dominating D <-> (dominating D /\ irredundant D).
Proof.
  rewrite minimal_altdef ; last apply dom_superhereditary.
  rewrite /iff ; split ; last first.
  (* second case: <- *)
  - move=> [dominatingD /irredundantP irredundantD].
    rewrite dominatingD andTb.
    apply/forallP=> v.
    apply/implyP=> vinD.
    rewrite /dominating negb_forall.
    apply/existsP.
    move: (irredundantD v vinD).
    rewrite (private_set_not_empty vinD).
    elim=> w /privateP [vdomw H3].
    exists w.
    rewrite negb_imply; apply/andP ; split.
    + rewrite in_setD1 negb_and negbK orbC -implybE.
      apply/implyP=> winD.
      by move: (H3 w winD (cl_sg_refl w))->.
    + rewrite negb_exists.
      apply/forallP=> y.
      rewrite negb_and.
      rewrite orbC -implybE.
      apply/implyP=> adjyw.
      rewrite in_setD1 negb_and orbC -implybE negbK.
      apply/implyP=> yinD.
      have ydomw: y -*- w by rewrite /cl_sedge adjyw orbT.
      move: (H3 y yinD ydomw).
      by move->.
  (* first case: -> *)
  - move/andP=> [dominatingD /forallP H1] ; split=> //.
    rewrite /irredundant.
    apply/forallP=> v.
    apply/implyP=> vinD.
    move/implyP: (H1 v) => /(_ vinD).
    rewrite /dominating negb_forall.
    move/existsP.
    elim=> w.
    rewrite negb_imply negb_exists => /andP [wnotinDcupv /forallP H2].
    rewrite (private_set_not_empty vinD).
    exists w.
    (* We need this result to show that if there is a private vertice of v, should be w *)
    have wprivatev: {in D, forall u, u -*- w -> u = v}.
    { move=> u uinD udomw.
      apply/eqP. 
      move: (H2 u).
      rewrite negb_and.
      case/orP ; [ by rewrite in_setD1 uinD negb_and negbK orbF | ].
      move=> noadjuw.
      have uisw : u == w by move: udomw noadjuw ; rewrite /cl_sedge orbC ; apply: aorbNa.
      move: wnotinDcupv.
      by rewrite -(eqP uisw) in_setD1 uinD andbT negbK. }
    apply/privateP.
    split ; [ | exact: wprivatev].
    move: wnotinDcupv.
    rewrite in_setD1 negb_and.
    case/orP ; [ by rewrite negbK (eq_sym w v) /cl_sedge=> -> | ].
    move=> wnotinD ; move/dominatingP: dominatingD.
    move=> /(_ w wnotinD).
    elim=> b [binD adjbw].
    have bdomw: b -*- w by rewrite /cl_sedge adjbw orbT.
    by move: (wprivatev b binD bdomw) <-.
Qed.

(* A minimal dominating set is maximal irredundant
 * See Prop. 3.9 of Fundamentals of Domination *)
Theorem minimal_dom_is_maximal_irr : minimal dominating D -> maximal irredundant D.
Proof.
  rewrite minimal_dom_iff_dom_irr.
  rewrite maximal_altdef ; last apply irr_hereditary.
  move=> [dominatingD irredundantD].
  apply/andP ; split=>//.
  apply/forallP=> v.
  apply/implyP=> vnotinD.
  rewrite /irredundant.
  rewrite negb_forall.
  apply/existsP.
  exists v.
  have vinDcupv : v \in D :|: [set v] by rewrite in_setU set11 orbT.
  rewrite negb_imply vinDcupv andTb.
  apply/negP.
  rewrite (private_set_not_empty vinDcupv).
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
    elim=> u [uinD adjux].
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

Definition max_st := maximal stable.

Definition min_dom := minimal dominating.

Definition max_irr := maximal irredundant.

(* Inhabitants that are "maximal stable", "minimal dominating" and "maximal irredundant"
 * Recall that ex_minimal and ex_maximal requires a proof of an inhabitant of "stable",
 * "dominating" and "irredudant" to be able to generate the maximal/minimal set.
 * In the call to ex_minimal and ex_maximal, the type of set is implicit. *)

Definition inhb_max_st := ex_maximal stable set0 st_empty.

Definition inhb_min_dom := ex_minimal dominating V(G) dom_VG.

Definition inhb_max_irr := ex_maximal irredundant set0 irr_empty.

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

Let minimum_maximal_irr : {set G} := minimum_set weight max_irr inhb_max_irr.

Let minimum_dom : {set G} := minimum_set weight dominating V(G).

Let minimum_maximal_st : {set G} := minimum_set weight max_st inhb_max_st.

Let maximum_st : {set G} := maximum_set weight stable set0.

Let maximum_minimal_dom : {set G} := maximum_set weight min_dom inhb_min_dom.

Let maximum_irr : {set G} := maximum_set weight irredundant set0.

(* Definitions of parameters: basically, they measure the weight of the previous sets *)

Definition ir_w : nat := weight_set weight minimum_maximal_irr.

Definition gamma_w : nat := weight_set weight minimum_dom.

Definition ii_w : nat := weight_set weight minimum_maximal_st.

Definition alpha_w : nat := weight_set weight maximum_st.

Definition Gamma_w : nat := weight_set weight maximum_minimal_dom.

Definition IR_w : nat := weight_set weight maximum_irr.

(* Weighted version of the Cockayne-Hedetniemi domination chain. *)

Theorem ir_w_leq_gamma_w : ir_w <= gamma_w.
Proof.
  (* we generate "set_is_min" which says that any maximal irredundant F has weight >= ir(G) *)
  move: (minimum_set_welldefined weight max_irr inhb_max_irr inhb_max_irr_is_maximal_irredundant).
  move/minimumP => [_ set_is_min].
  (* we provide an F that is minimal dominating *)
  set F := minimum_dom.
  move: (minimum_set_welldefined weight dominating V(G) dom_VG) => Fminimum_dom.
  rewrite -/minimum_dom -/F in Fminimum_dom.
  move: (minimum_is_minimal positive_weights Fminimum_dom) => Fminimal_dom.
  (* and, therefore, F is maximal irredundant *)
  move: (minimal_dom_is_maximal_irr Fminimal_dom) => Fmaximal_irr.
  by move: (set_is_min F Fmaximal_irr).
Qed.

Theorem gamma_w_leq_ii_w : gamma_w <= ii_w.
Proof.
  (* we generate "set_is_min" which says that any dominating set F has weight >= gamma_w(G) *)
  move: (minimum_set_welldefined weight dominating V(G) dom_VG).
  move/minimumP => [_ set_is_min].
  (* we provide a maximal stable F which is also dominating *)
  set F := minimum_maximal_st.
  move: (minimum_set_p weight inhb_max_st_is_maximal_stable) => Fminimum_max_st.
  rewrite -/minimum_maximal_st -/F /max_st in Fminimum_max_st.
  have: stable F /\ dominating F by rewrite -(maximal_st_iff_st_dom F).
  move=> [_ Fdom].
  by move: (set_is_min F Fdom).
Qed.

Theorem ii_w_leq_alpha_w : ii_w <= alpha_w.
Proof.
  (* we generate "set_is_max" which says that any stable set F has weight <= alpha_w(G) *)
  move: (maximum_set_welldefined weight stable set0 st_empty).
  move/maximumP => [_ set_is_max].
  (* we provide a maximal stable F *)
  set F := minimum_maximal_st.
  move: (minimum_set_p weight inhb_max_st_is_maximal_stable).
  rewrite -/minimum_maximal_st -/F /max_st.
  (* in particular, it only matters if F is stable *)
  move/maximalP=> [Fst _].
  by move: (set_is_max F Fst).
Qed.

Theorem alpha_w_leq_Gamma_w : alpha_w <= Gamma_w.
Proof.
  (* we generate "set_is_max" which says that any minimal dom. set F has weight <= Gamma_w(G) *)
  move: (maximum_set_welldefined weight min_dom inhb_min_dom inhb_min_dom_is_minimal_dominating).
  move/maximumP => [_ set_is_max].
  (* we provide an F that F maximal stable ... *)
  set F := maximum_st.
  move: (maximum_set_welldefined weight stable set0 st_empty) => Fmaximum_st.
  rewrite -/maximum_st -/F in Fmaximum_st.
  move: (maximum_is_maximal positive_weights Fmaximum_st) => Fmaximal_st.
  (* and, therefore, F is minimal dominating *)
  move: (maximal_st_is_minimal_dom Fmaximal_st) => Fminimal_dom.
  by move: (set_is_max F Fminimal_dom).
Qed.

Theorem Gamma_w_leq_IR_w : Gamma_w <= IR_w.
Proof.
  (* we generate "set_is_max" which says that any irredundant F has weight <= IR_w(G) *)
  move: (maximum_set_welldefined weight irredundant set0 irr_empty).
  move/maximumP => [_ set_is_max].
  (* we provide an F that is maximal irredundant *)
  set F := maximum_minimal_dom.
  move: (maximum_set_p weight inhb_min_dom_is_minimal_dominating).
  rewrite -/maximum_minimal_dom -/F /min_dom => Fminimal_dom.
  move: (minimal_dom_is_maximal_irr Fminimal_dom).
  (* in particular, it only matters if F is irredundant *)
  move/maximalP=> [Firr _].
  by move: (set_is_max F Firr).
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
(** * Unweighted sets and parameters *)
Section Unweighted_Sets.

Variable p : pred {set G}.     (* p : {set G} -> bool *)
Variable D : {set G}.

Definition ones : (G -> nat) := (fun _ => 1).

Definition maximum_card : bool := p D && [forall F : {set G}, p F ==> (#|F| <= #|D|)].

Definition minimum_card : bool := p D && [forall F : {set G}, p F ==> (#|D| <= #|F|)].

Proposition maximum_cardP : reflect (p D /\ (forall F : {set G}, p F -> #|F| <= #|D|)) maximum_card.
Proof.
  rewrite /maximum_card.
  apply: (iffP andP).
  (* first case: -> *)
  move=> [pD /forallP H1].
  split=> //.
  move=> F pF.
  move: (H1 F).
  by rewrite pF implyTb.
  (* second case: <- *)
  move=> [pD H2].
  split=> //.
  apply/forallP => F.
  apply/implyP => pF.
  exact: (H2 F pF).
Qed.

Proposition minimum_cardP : reflect (p D /\ (forall F : {set G}, p F -> #|D| <= #|F|)) minimum_card.
Proof.
  rewrite /minimum_card.
  apply: (iffP andP).
  (* first case: -> *)
  move=> [pD /forallP H1].
  split=> //.
  move=> F pF.
  move: (H1 F).
  by rewrite pF implyTb.
  (* second case: <- *)
  move=> [pD H2].
  split=> //.
  apply/forallP => F.
  apply/implyP => pF.
  exact: (H2 F pF).
Qed.

Lemma card_weight_1 : forall S : {set G}, #|S| = weight_set ones S.
Proof. move=> S ; by rewrite /weight_set /ones sum1_card. Qed.

Lemma maximum1 : maximum_card <-> maximum ones p D.
Proof.
  rewrite /iff ; split.
  (* first case: -> *)
  move/maximum_cardP => [pD H1].
  apply/maximumP.
  split => //.
  move=> F pF.
  rewrite -!card_weight_1.
  exact: (H1 F pF).
  (* second case: <- *)
  move/maximumP=> [pD H2].
  apply/maximum_cardP.
  split => //.
  move=> F pF.
  rewrite !card_weight_1.
  exact: (H2 F pF).
Qed.

Lemma minimum1 : minimum_card <-> minimum ones p D.
Proof.
  rewrite /iff ; split.
  (* first case: -> *)
  move/minimum_cardP => [pD H1].
  apply/minimumP.
  split => //.
  move=> F pF.
  rewrite -!card_weight_1.
  exact: (H1 F pF).
  (* second case: <- *)
  move/minimumP=> [pD H2].
  apply/minimum_cardP.
  split => //.
  move=> F pF.
  rewrite !card_weight_1.
  exact: (H2 F pF).
Qed.

Proposition maximum_card_is_maximal : maximum_card -> maximal p D.
Proof. rewrite maximum1 ; exact: maximum_is_maximal. Qed.

Proposition minimum_card_is_minimal : minimum_card -> minimal p D.
Proof. rewrite minimum1 ; exact: minimum_is_minimal. Qed.

End Unweighted_Sets.


(**********************************************************************************)
Section Argument_unweighted_sets.

Variable p : pred {set G}.     (* p : {set G} -> bool *)
Variable F : {set G}.          (* some set satisfying p *)
Hypothesis pF : p F.           (* the proof that F satisfies p *)

Definition maximum_set_card : {set G} := [arg max_(D > F | p D) #|D|].

Definition minimum_set_card : {set G} := [arg min_(D < F | p D) #|D|].

Lemma max_card_weight_1 : #|maximum_set_card| = #|maximum_set ones p F|.
Proof.
  rewrite /maximum_set_card.
  case: (arg_maxP (fun D : {set G} => #|D|) pF).
  move=> D1 pD1 H1.
  rewrite /maximum_set.
  case: (arg_maxP (fun D => weight_set ones D) pF).
  move=> D2 pD2 H2.
  apply/eqP ; rewrite eqn_leq ; apply/andP ; split.
  move: (H2 D1 pD1).
  by rewrite -!card_weight_1.
  exact: (H1 D2 pD2).
Qed.

Lemma min_card_weight_1 : #|minimum_set_card| = #|minimum_set ones p F|.
Proof.
  rewrite /minimum_set_card.
  case: (arg_minP (fun D : {set G} => #|D|) pF).
  move=> D1 pD1 H1.
  rewrite /minimum_set.
  case: (arg_minP (fun D => weight_set ones D) pF).
  move=> D2 pD2 H2.
  apply/eqP ; rewrite eqn_leq ; apply/andP ; split.
  exact: (H1 D2 pD2).
  move: (H2 D1 pD1).
  by rewrite -!card_weight_1.
Qed.

End Argument_unweighted_sets.

(* "argument" policy:
   maximum_set_card and minimum_set_card requires the following arguments:
     the property and a set (should satisfies the property) 
   max_card_weight1 and min_card_weight1 requires:
     the property, a set satisfying the property and a proof of that *)
Arguments max_card_weight_1 : clear implicits.
Arguments min_card_weight_1 : clear implicits.


(**********************************************************************************)
Section Classic_domination_parameters.

(* Sets of minimum/maximum cardinal *)

Let minimum_maximal_irr : {set G} := minimum_set_card max_irr inhb_max_irr.

Let minimum_dom : {set G} := minimum_set_card dominating V(G).

Let minimum_max_st : {set G} := minimum_set_card max_st inhb_max_st.

Let maximum_st : {set G} := maximum_set_card stable set0.

Let maximum_minimal_dom : {set G} := maximum_set_card min_dom inhb_min_dom.

Let maximum_irr : {set G} := maximum_set_card irredundant set0.

(* Definitions of classic parameters *)

Definition ir : nat := #|minimum_maximal_irr|.

Definition gamma : nat := #|minimum_dom|.

Definition ii : nat := #|minimum_max_st|.

Definition alpha : nat := #|maximum_st|.

Definition Gamma : nat := #|maximum_minimal_dom|.

Definition IR : nat := #|maximum_irr|.

(* Conversion between classic and weighted parameters *)

Lemma ir_is_ir1 : ir = ir_w ones.
Proof.
  rewrite /ir /ir_w /minimum_maximal_irr.
  rewrite (min_card_weight_1 max_irr inhb_max_irr inhb_max_irr_is_maximal_irredundant).
  exact: card_weight_1.
Qed.

Lemma gamma_is_gamma1 : gamma = gamma_w ones.
Proof. 
  rewrite /gamma /gamma_w /minimum_dom.
  rewrite (min_card_weight_1 dominating V(G) dom_VG).
  exact: card_weight_1.
Qed.

Lemma ii_is_ii1 : ii = ii_w ones.
Proof.
  rewrite /ii /ii_w /minimum_max_st.
  rewrite (min_card_weight_1 max_st inhb_max_st inhb_max_st_is_maximal_stable).
  exact: card_weight_1.
Qed.

Lemma alpha_is_alpha1 : alpha = alpha_w ones.
Proof. 
  rewrite /alpha /alpha_w /maximum_st.
  rewrite (max_card_weight_1 stable set0 st_empty).
  exact: card_weight_1.
Qed.

Lemma Gamma_is_Gamma1 : Gamma = Gamma_w ones.
Proof.
  rewrite /Gamma /Gamma_w /maximum_minimal_dom.
  rewrite (max_card_weight_1 min_dom inhb_min_dom inhb_min_dom_is_minimal_dominating).
  exact: card_weight_1.
Qed.

Lemma IR_is_IR1 : IR = IR_w ones.
Proof.
  rewrite /IR /IR_w /maximum_irr.
  rewrite (max_card_weight_1 irredundant set0 irr_empty).
  exact: card_weight_1.
Qed.

(* Classic Cockayne-Hedetniemi domination chain. *)

Corollary ir_leq_gamma : ir <= gamma.
Proof. by rewrite ir_is_ir1 gamma_is_gamma1 ir_w_leq_gamma_w. Qed.

Corollary gamma_leq_ii : gamma <= ii.
Proof. by rewrite gamma_is_gamma1 ii_is_ii1 gamma_w_leq_ii_w. Qed.

Corollary ii_leq_alpha : ii <= alpha.
Proof. by rewrite ii_is_ii1 alpha_is_alpha1 ii_w_leq_alpha_w. Qed.

Corollary alpha_leq_Gamma : alpha <= Gamma.
Proof. by rewrite alpha_is_alpha1 Gamma_is_Gamma1 alpha_w_leq_Gamma_w. Qed.

Corollary Gamma_leq_IR : Gamma <= IR.
Proof. by rewrite Gamma_is_Gamma1 IR_is_IR1 Gamma_w_leq_IR_w. Qed.

End Classic_domination_parameters.

End Domination_Theory.


Arguments deg : clear implicits.
Arguments minimum_deg : clear implicits.
Arguments maximum_deg : clear implicits.
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

