Require Import RelationClasses Setoid.
From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries digraph sgraph minor multigraph skeleton.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 


Implicit Types (G H : graph) (U : sgraph) (T : forest).

Open Scope implicit_scope.

(** * Subalgebra of Tree-Width 2 Graphs *)

(** ** Closure Properties for operations *)

Arguments sdecomp T G B : clear implicits.

Definition compatible (T : forest) (G : graph2) (B : T -> {set G}) := 
  exists t, (g_in \in B t) && (g_out \in B t).

Lemma sdecomp_sskel (T : forest) (G : graph2) (B : T -> {set G}) :
  sdecomp T (sskeleton G) B <-> (sdecomp T G B /\ compatible B).
Proof.
  split. 
  - case => [D1 D2 D3]. split. split => //. 
    + move => x y /= xy. apply: D2. by rewrite /edge_rel/= xy. 
    + case: (altP (g_in =P g_out :> skeleton G)) => E. 
      * case: (D1 g_in) => t Ht. exists t. by rewrite -E !Ht.
      * suff: (g_in : sskeleton G) -- g_out by apply: D2. by rewrite /edge_rel/= E !eqxx.
  - move => [[D1 D2 D3] C]. split => //= x y. case/or3P; first exact: D2.
    + case/and3P => ? /eqP E1 /eqP E2. by subst. 
    + case/and3P => ? /eqP E1 /eqP E2. subst. 
      case: C => t. rewrite andbC. by exists t.
Qed.

Lemma hom_eqL (V : finType) (e1 e2 : rel V) (G : sgraph) (h : V -> G) 
      (e1_sym : symmetric e1) (e1_irrefl : irreflexive e1) 
      (e2_sym : symmetric e2) (e2_irrefl : irreflexive e2):
  e1 =2 e2 ->
  @hom_s (SGraph e1_sym e1_irrefl) G h -> 
  @hom_s (SGraph e2_sym e2_irrefl) G h.
Proof. move => E hom_h x y. rewrite /edge_rel/= -E. exact: hom_h. Qed.


Lemma skel_union_join (G1 G2 : graph) : sk_rel (union G1 G2) =2 @join_rel G1 G2.
Proof.
  move => [x|x] [y|y] /=. 
  - rewrite /edge_rel/= sum_eqE. 
    case: (boolP (x == y)) => //= E. apply/existsP/existsP. 
    + move => [[e|e]]; rewrite !inE //= !sum_eqE. by exists e; rewrite !inE.
    + move => [e] H. exists (inl e). by rewrite !inE /= !sum_eqE in H *. 
  - apply: contraTF isT => /existsP [[e|e]]; by rewrite !inE //= andbC.
  - apply: contraTF isT => /existsP [[e|e]]; by rewrite !inE //= andbC.
  - rewrite /edge_rel/= sum_eqE. 
    case: (boolP (x == y)) => //= E. apply/existsP/existsP. 
    + move => [[e|e]]; rewrite !inE //= !sum_eqE. by exists e; rewrite !inE.
    + move => [e] H. exists (inr e). by rewrite !inE /= !sum_eqE in H *. 
Qed.

Section Quotients. 
  Variables (G1 G2 : graph2).
  
  Let P : {set union G1 G2} := [set inl g_in; inl g_out; inr g_in; inr g_out].

  Definition admissible (eqv : rel (union G1 G2)) := 
    forall x y, eqv x y -> x = y \/ [set x;y] \subset P. 
 
  Lemma decomp_quot (T1 T2 : forest) D1 D2 (e : equiv_rel (union G1 G2)): 
    sdecomp T1 (sskeleton G1) D1 -> sdecomp T2 (sskeleton G2) D2 -> 
    width D1 <= 3 -> width D2 <= 3 ->
    admissible e -> #|[set \pi_{eq_quot e} x | x in P]| <= 3 ->
    exists T D, [/\ sdecomp T (skeleton (merge_def _ e)) D, 
              width D <= 3 & exists t, 
              D t = [set \pi_{eq_quot e} x | x in P]].
  Proof using. 
    move => /sdecomp_sskel [dec1 comp1] /sdecomp_sskel [dec2 comp2] W1 W2 adm_e collapse_P.
    move: comp1 comp2 => [t1 /andP[t1_in t1_out]] [t2 /andP[t2_in t2_out]].
    pose T := tjoin T1 T2.
    pose D : tjoin T1 T2 -> {set sjoin G1 G2}:= decompU D1 D2.
    have dec_D: sdecomp T (sjoin G1 G2) D by exact: join_decomp. 
    have dis_t1_t2 : ~~ connect (@sedge T)(inl t1) (inr t2) by rewrite join_disc.
    have dis_T12 : {in [set inl t1;inr t2] &, forall x y, x != y -> ~~ connect (@sedge T) x y}.
    { move => [?|?] [?|?] /setUP[] /set1P-> /setUP[]/set1P ->. 
      all: by rewrite ?eqxx // => _; rewrite sconnect_sym. }
    pose T' := @tlink T _ dis_T12.
    pose D' := decompL D P : _ -> {set sjoin G1 G2}.
    have dec_D' : sdecomp T' (sjoin G1 G2) D'.
    { apply: decomp_link => //.
      apply/subsetP => x.
      rewrite !inE -!orbA => /or4P [] /eqP->.
      all: apply/bigcupP; solve 
        [ by exists (inl t1) => //; rewrite ?inE ?mem_imset ?eqxx 
        | by exists (inr t2) => //; rewrite ?inE ?mem_imset ?eqxx]. }
    pose h := \pi_{eq_quot e} : skeleton (union G1 G2) -> skeleton (merge_def _ e).
    exists T'. exists (rename D' h); split; last by exists None.
    - apply: rename_decomp => //. 
      + apply: hom_eqL (pi_hom e). exact: skel_union_join.
      + exact: emb_surj.
      + move => x y. move/sk_rel_mergeE => [? [x0] [y0] /= [? ? ?]]. 
        exists x0;exists y0. split => //. by rewrite /edge_rel/= -skel_union_join.
      + move => x y. move/eqmodP => /=. case/adm_e => [<-|A].
        * case: (sbag_cover dec_D' x) => t Ht. left. exists t. by rewrite Ht.
        * left. exists None. by rewrite /= -!sub1set -subUset. 
    - rewrite /width (bigID (pred1 None)).
      rewrite big_pred1_eq. rewrite geq_max. apply/andP;split => //.
      + rewrite (reindex Some) /=.
        * apply: (@leq_trans (maxn (width D1) (width D2))); last by rewrite geq_max W1 W2.
          apply: leq_trans (join_width _ _). 
          apply: max_mono => t. exact: leq_imset_card.
        * apply: subon_bij; last by (apply bij_on_codom => //; exact: (inl t1)). 
          by move => [x|]; rewrite !in_simpl // codom_f. 
  Qed.

  Definition par2_eqv : rel (union G1 G2) :=
    fun x y => (x == y) ||
      if (g_in != g_out :> G1) && (g_in != g_out :> G2)
      then [set x; y] \in [set [set inl g_in; inr g_in]; [set inl g_out; inr g_out]]
      else [set x; y] \subset [set inl g_in; inl g_out; inr g_in; inr g_out].

  Definition par2_eqv_refl : reflexive par2_eqv.
  Proof. by move=> ?; rewrite /par2_eqv eqxx. Qed.

  Lemma par2_eqv_sym : symmetric par2_eqv.
  Proof. move=> x y. by rewrite /par2_eqv [[set y; x]]setUC [y == x]eq_sym. Qed.

  Definition par2_eqv_trans : transitive par2_eqv.
  Proof using.
    move=> y x z. rewrite /par2_eqv.
    case/altP: (x =P y) => [<-//|xNy/=]. case/altP: (y =P z) => [<-->//|yNz/=].
    case/boolP: ((g_in != g_out :> G1) && (g_in != g_out :> G2)).
    - rewrite !inE -(implyNb (x == z)).
      case/andP=> /negbTE iNo1 /negbTE iNo2 Hxy Hyz. apply/implyP=> xNz.
      move: Hxy xNy. rewrite 2!eqEcard 2!subUset 4!sub1set !inE.
      case/orP => /andP[]/andP[] /orP[]/eqP ? /orP[]/eqP ? _; subst=> // _.
      all: move: Hyz xNz yNz; rewrite 2!eqEcard 2!subUset 4!sub1set !inE.
      all: rewrite ?eqxx ?sum_eqE ?[g_out == g_in]eq_sym ?iNo1 ?iNo2 ?orbT ?orbF /=.
      all: case/andP => /orP[]/eqP-> _; by rewrite !eqxx.
    - rewrite -implyNb => _ Hxy Hyz. apply/implyP=> xNz.
      rewrite subUset !sub1set. apply/andP; split.
      + apply: (subsetP Hxy). by rewrite !inE eqxx.
      + apply: (subsetP Hyz). by rewrite !inE eqxx.
  Qed.

  Canonical par2_eqv_equivalence :=
    EquivRel par2_eqv par2_eqv_refl par2_eqv_sym par2_eqv_trans.

  Lemma par2_eqv_io :
    (par2_eqv (inl g_in) (inr g_in)) * (par2_eqv (inl g_out) (inr g_out)).
  Proof.
    rewrite /par2_eqv/=. case: ifP => _.
    - by rewrite !inE !eqxx.
    - by rewrite !subUset !sub1set !inE !eqxx.
  Qed.

  Definition par2_eq (x y : union G1 G2) :=
    match x,y with
    | inl x, inr y => (x == g_in) && (y == g_in) || (x == g_out) && (y == g_out)
    | _,_ => false
    end.

  Lemma set2_in_sym (T : finType) (x y a b : T) (e : rel T) :  
    x != y -> symmetric e -> e a b -> [set x;y] == [set a;b] -> e x y.
  Proof.
    move => xDy sym_e e_ab E. move: E xDy. rewrite eqEsubset !subUset !sub1set -andbA.
    case/and3P => /set2P[->|->] /set2P[->|->] _; by rewrite ?eqxx // sym_e.
  Qed.

  Lemma equiv_of_sub (T : finType) (e1 e2 : rel T) :
    subrel e1 e2 -> reflexive e2 -> symmetric e2 -> transitive e2 -> subrel (equiv_of e1) e2.
  Proof. 
    move => sub2 refl2 sym2 trans2 x y. case/connectP => p. 
    elim: p x => [x _ -> //|a p IHp x] /= /andP [/orP H] pth lst.
    apply: trans2 _ (IHp _ pth lst). case: H; last rewrite sym2; exact: sub2.
  Qed.

  Hint Resolve equiv_of_sym.
  Ltac sub := apply: sub_equiv_of => /=; by rewrite !eqxx.

  Lemma par2_equiv_of : par2_eqv =2 equiv_of par2_eq.
  Proof using.
    move=> x y. apply/idP/idP.
    - rewrite /par2_eqv. case/altP: (x =P y) => [<- _|xNy]/=; first exact: equiv_of_refl.
      case: ifP => [_|/negbT].
      + rewrite !inE. case/orP; apply: set2_in_sym => //; sub.
      + rewrite negb_and 2!negbK. case/orP=> [/eqP Eio1|/eqP Eio2].
        * rewrite -Eio1 setUid => Exy.
          have Rio2 : equiv_of par2_eq (inr g_out) (inr g_in). 
          { apply: (@equiv_of_trans _ _ (inl g_in)); first rewrite equiv_of_sym Eio1; sub. }
          move: Exy xNy; rewrite subUset 2!sub1set !inE -2!orbA.
          case/andP=> /or3P[]/eqP-> /or3P[]/eqP->.
          all: rewrite ?eqxx // ?[equiv_of _ _ (inl _)]equiv_of_sym => _.
          all: try solve [apply: (@sub_equiv_of _ _ (inl _));
                          by rewrite /par2_eq -?Eio1 !eqxx].
          by rewrite equiv_of_sym.
        * rewrite -setUA -Eio2 setUid => Exy.
          have Rio2 : equiv_of par2_eq (inl g_out) (inl g_in).
          { apply: (@equiv_of_trans _ _ (inr g_out)); last rewrite equiv_of_sym -Eio2;
            by apply: sub_equiv_of; rewrite /par2_eq !eqxx. }
          move: Exy xNy; rewrite subUset 2!sub1set !inE -2!orbA.
          case/andP=> /or3P[]/eqP-> /or3P[]/eqP->.
          all: rewrite ?eqxx // ?[equiv_of _ (inr _) _]equiv_of_sym => _.
          all: try solve [apply: (@sub_equiv_of _ _ (inl _));
                          by rewrite /par2_eq -?Eio2 !eqxx].
          by rewrite equiv_of_sym.
    - apply: equiv_of_sub; auto using par2_eqv_refl,par2_eqv_sym,par2_eqv_trans.
      move => {x y} [x|x] [y|y] => //=. 
      by case/orP; case/andP => /eqP-> /eqP->; rewrite par2_eqv_io.
  Qed.

  Lemma par2_eqv_ii x y : 
    x = g_in :> G1 -> y = g_in :> G2 ->
    par2_eqv (inl x) (inr y).
  Proof.
    move => -> ->. rewrite par2_equiv_of. apply: sub_equiv_of.
      by rewrite /par2_eq !eqxx. 
  Qed.
  
  Lemma par2_eqv_oo x y : 
    x = g_out :> G1 -> y = g_out :> G2 ->
    par2_eqv (inl x) (inr y).
  Proof.
    move => -> ->. rewrite par2_equiv_of. apply: sub_equiv_of.
      by rewrite /par2_eq !eqxx. 
  Qed.

  Definition par2 := 
    {| graph_of := merge (union G1 G2) par2_eqv ;
       g_in := \pi_{eq_quot par2_eqv} (inl g_in);
       g_out := \pi_{eq_quot par2_eqv} (inl g_out) |}.

  Lemma par2_eqvP : admissible par2_eqv.
  Proof using. 
    move=> x y. case/orP=> [/eqP|]; first by left. case: ifP; last by right.
    rewrite !inE => _ /orP[]/eqP->; by right; rewrite subUset !sub1set !inE !eqxx.
  Qed.

  Lemma decomp_par2 (T1 T2 : forest) D1 D2 : 
    sdecomp T1 (sskeleton G1) D1 -> sdecomp T2 (sskeleton G2) D2 -> 
    width D1 <= 3 -> width D2 <= 3 ->
    exists T D, [/\ sdecomp T (sskeleton (par2)) D & width D <= 3].
  Proof using.
    move => dec1 dec2 W1 W2.
    case: (decomp_quot (e:= [equiv_rel of par2_eqv]) dec1 dec2 W1 W2 _ _).
    - exact: par2_eqvP.
    - pose P' : {set union G1 G2} := [set inl g_in; inl g_out].
      apply: (@leq_trans #|P'|); last by rewrite cards2; by case (_ != _).
      apply: (@leq_trans #|[set (\pi x : par2) | x in P']|); last exact: leq_imset_card.
      apply: subset_leq_card.
      apply/subsetP => ? /imsetP [x H1 ->]. case/setUP : H1 => H1; first case/setUP : H1 => H1.
      * by rewrite mem_imset.
      * move/set1P : H1 => ->. apply/imsetP. exists (inl g_in); first by rewrite !inE eqxx ?orbT.
        apply/eqmodP. by rewrite equiv_sym /= par2_eqv_io.
      * move/set1P : H1 => ->. apply/imsetP. exists (inl g_out); first by rewrite !inE eqxx ?orbT.
        apply/eqmodP. by rewrite equiv_sym /= par2_eqv_io.
    - move => T [D] [A B [t C]]. exists T. exists D. split => //. 
      apply/sdecomp_sskel. split => //. 
      exists t. by rewrite C !mem_imset // !inE ?eqxx ?orbT.
  Qed.

  Definition seq2_eqv : rel (union G1 G2) :=
    fun x y => (x == y) || ([set x; y] == [set inl g_out; inr g_in]).

  Definition seq2_eqv_refl : reflexive seq2_eqv.
  Proof. by move=> ?; rewrite /seq2_eqv eqxx. Qed.

  Lemma seq2_eqv_sym : symmetric seq2_eqv.
  Proof. move=> x y. by rewrite /seq2_eqv [[set y; x]]setUC [y == x]eq_sym. Qed.

  Definition seq2_eqv_trans : transitive seq2_eqv.
  Proof using.
    move=> y x z. rewrite /seq2_eqv.
    case/altP: (x =P y) => [<-//|/= xNy Exy].
    case/altP: (y =P z) => [<-|/= yNz Eyz]; first by rewrite Exy.
    case/altP: (x =P z) => //= xNz.
    have := eq_refl #|[set inl (@g_out G1); inr (@g_in G2)]|.
    rewrite -{1}(setUid [set _; _]) -{1}(eqP Exy) -{1}(eqP Eyz).
    rewrite set2C -setUUr (cardsU1 y) !cards2 !inE.
    by rewrite (eq_sym y x) negb_or xNy yNz xNz.
  Qed.

  Canonical seq2_eqv_equivalence :=
    EquivRel seq2_eqv seq2_eqv_refl seq2_eqv_sym seq2_eqv_trans.

  Lemma seq2_eqv_io : seq2_eqv (inl g_out) (inr g_in).
  Proof. by rewrite /seq2_eqv/=. Qed.

  Definition seq2_eq : simpl_rel (union G1 G2) :=
    [rel a b | (a == inl g_out) && (b == inr g_in)].

  Lemma seq2_equiv_of : seq2_eqv =2 equiv_of seq2_eq.
  Proof using.
    move=> x y. apply/idP/idP.
    - rewrite/seq2_eqv. case/altP: (x =P y) => [<- _|xNy]; first exact: equiv_of_refl.
      apply: set2_in_sym => //. sub.
    - apply: equiv_of_sub; auto using seq2_eqv_refl,seq2_eqv_sym,seq2_eqv_trans.
      move => {x y} [x|x] [y|y] //=; case/andP => /eqP -> /eqP ->; by rewrite seq2_eqv_io.
  Qed.

  Definition seq2 :=
    {| graph_of := merge (union G1 G2) seq2_eqv ;
       g_in := \pi_{eq_quot seq2_eqv} (inl g_in);
       g_out := \pi_{eq_quot seq2_eqv} (inr g_out) |}.

  Lemma seq2_eqvP : admissible seq2_eqv.
  Proof. 
    move=> x y. case/orP => /eqP->; [by left | right].
    by rewrite subUset !sub1set !inE !eqxx.
  Qed.

  Lemma decomp_seq2 (T1 T2 : forest) D1 D2 : 
    sdecomp T1 (sskeleton G1) D1 -> sdecomp T2 (sskeleton G2) D2 -> 
    width D1 <= 3 -> width D2 <= 3 ->
    exists T D, [/\ sdecomp T (sskeleton seq2) D & width D <= 3].
  Proof using.
    move => dec1 dec2 W1 W2.
    case: (decomp_quot (e:= [equiv_rel of seq2_eqv]) dec1 dec2 W1 W2 _ _).
    - exact: seq2_eqvP.
    - pose P' : {set union G1 G2} := [set inl g_in; inl g_out; inr g_out].
      apply: (@leq_trans #|P'|); last apply cards3.
      apply: (@leq_trans #|[set (\pi x : seq2) | x in P']|); last exact: leq_imset_card.
      apply: subset_leq_card.
      apply/subsetP => ? /imsetP [x H1 ->]. move: H1. 
      rewrite /P -!setUA [[set _;_]]setUC !setUA. case/setUP => H1.
      * by rewrite mem_imset.
      * move/set1P : H1 => ->. apply/imsetP. exists (inl g_out); first by rewrite !inE eqxx ?orbT.
        apply/eqmodP. by rewrite equiv_sym /= seq2_eqv_io.
    - move => T [D] [A B [t C]]. exists T. exists D. split => //. 
      apply/sdecomp_sskel. split => //. 
      exists t. by rewrite C !mem_imset // !inE ?eqxx ?orbT.
  Qed.

End Quotients.

Definition cnv2 (G : graph2) :=
  {| graph_of := G; g_in := g_out; g_out := g_in |}.

Lemma decomp_cnv (G : graph2) T D : 
  sdecomp T (sskeleton G) D -> sdecomp T (sskeleton (cnv2 G)) D.
Proof. 
  move/sdecomp_sskel => [dec cmp]. apply/sdecomp_sskel; split => //. 
  move: cmp => [t] H. exists t => /=. by rewrite andbC.
Qed.

Definition dom2 (G : graph2) := 
  {| graph_of := G; g_in := g_in; g_out := g_in |}.

Lemma decomp_dom (G : graph2) T D : 
  sdecomp T (sskeleton G) D -> sdecomp T (sskeleton (dom2 G)) D.
Proof. 
  move/sdecomp_sskel => [dec cmp]. apply/sdecomp_sskel; split => //. 
  move: cmp => [t] /andP [H _]. exists t => /=. by rewrite !H. 
Qed.

Definition triv_decomp (G : sgraph) :
  sdecomp tunit G (fun _ => [set: G]).
Proof. 
  split => [x|e|x [] [] _ _]; try by exists tt; rewrite !inE.
  exact: connect0.
Qed.

Notation vfun := (fun x : void => match x with end).  
Definition unit_graph := @Graph [finType of unit] _ vfun vfun vfun.

Definition one2 := {| graph_of := unit_graph; g_in := tt; g_out := tt |}.

Definition two_graph := @Graph [finType of bool] _ vfun vfun vfun.

Definition top2 := {| graph_of := two_graph; g_in := false; g_out := true |}.

Definition edge_graph (a : sym) := 
  Graph (fun _ : unit => false) (fun _ => true) (fun _ => a).                           

Definition sym2 a := {| graph_of := edge_graph a; g_in := false; g_out := true |}.

Lemma decomp_small (G : graph2) : #|G| <= 3 -> 
  exists T D, [/\ sdecomp T (sskeleton G) D & width D <= 3].
Proof. 
  exists tunit; exists (fun => setT). split.
  - exact: triv_decomp.
  - by rewrite /width (big_pred1 tt _) // cardsT. 
Qed.

(** ** Terms and tree-width 2 property *)

Inductive term := 
| tmA of sym
| tm1 
| tmT 
| tmC of term
| tmS of term & term
| tmI of term & term
| tmD of term
.

Fixpoint graph_of_term (u:term) {struct u} : graph2 := 
  match u with
  | tmA a => sym2 a
  | tm1 => one2
  | tmT => top2
  | tmC u => cnv2 (graph_of_term u)
  | tmS u v => seq2 (graph_of_term u) (graph_of_term v)
  | tmI u v => par2 (graph_of_term u) (graph_of_term v)
  | tmD u => dom2 (graph_of_term u)
  end.

Theorem graph_of_TW2 (u : term) : 
  exists T D, [/\ sdecomp T (sskeleton (graph_of_term u)) D & width D <= 3].
Proof.
  elim: u => [a| | | u IHu | u IHu v IHv | u IHu v IHv | u IHu ].
  - apply: decomp_small. by rewrite card_bool.
  - apply: decomp_small. by rewrite card_unit.
  - apply: decomp_small. by rewrite card_bool.
  - move: IHu => [T] [D] [D1 D2]. exists T. exists D. split => //. 
    exact: decomp_cnv. 
  - move: IHu IHv => [T1] [D1] [? ?] [T2] [D2] [? ?].
    simpl graph_of_term. exact: (decomp_seq2 (D1 := D1) (D2 := D2)).
  - move: IHu IHv => [T1] [D1] [? ?] [T2] [D2] [? ?].
    simpl graph_of_term. exact: (decomp_par2 (D1 := D1) (D2 := D2)).
  - move: IHu => [T] [D] [D1 D2]. exists T. exists D. split => //. 
    exact: decomp_dom. 
Qed.

Lemma sskel_K4_free (u : term) : K4_free (sskeleton (graph_of_term u)).
Proof.
  case: (graph_of_TW2 u) => T [B] [B1 B2]. 
  exact: TW2_K4_free B1 B2.
Qed.

Lemma skel_K4_free (u : term) : K4_free (skeleton (graph_of_term u)).
Proof.
  apply: minor_K4_free (@sskel_K4_free u).
  exact: sub_minor (skel_sub _).
Qed.

Opaque merge_def merge_seq union.



(* laws of 2p algebra *)

Definition par2' (F G: graph2) :=
  point (merge_seq (union F G) [::(unl g_in,unr g_in); (unl g_out,unr g_out)])
        (\pis (unl g_in)) (\pis (unl g_out)).

Definition seq2' (F G: graph2) :=
  point (merge_seq (union F G) [::(unl g_out,unr g_in)])
        (\pis (unl g_in)) (\pis (unr g_out)).

Definition cnv2' (F: graph2) :=
  point F g_out g_in.

Definition dom2' (F: graph2) :=
  point F g_in g_in.

Lemma par2C (F G: graph2): par2' F G ≈ par2' G F.
Proof.
  rewrite /par2'.
  rewrite (merge_iso (iso_union_C _ _)) /=.
  apply merge_same.
  apply eqv_clot_eq. leqv. leqv. 
  eqv. 
  eqv. 
Qed.

Lemma par2top (F: graph2): par2' F top2 ≈ F.
Proof.
  rewrite /par2' (merge_union_K2_ll (K:=top2) _ _ (k:=fun b => if b then g_out else g_in)).
  apply merge_nothing.
  repeat (constructor =>//=).
  by [].
  intros [|]; apply /eqquotP; eqv. 
Qed.

Lemma par2A (F G H: graph2): par2' F (par2' G H) ≈ par2' (par2' F G) H.
Proof.
  rewrite /par2'/=.
  rewrite (merge_iso (iso_union_merge_r _ _)) /=.
  rewrite (merge_iso (iso_union_merge_l _ _)) /=.
  rewrite 2!h_union_merge_rEl 2!h_union_merge_lEl.
  rewrite 2!h_union_merge_rEr 2!h_union_merge_lEr.
  rewrite (merge_merge_seq2 (G:=union F (union G H))
                            (k:=[::(unl g_in,unr (unl g_in)); (unl g_out,unr (unl g_out))])) =>//.
  rewrite (merge_merge_seq2 (G:=union (union F G) H)
                            (k:=[::(unl (unl g_in),unr g_in); (unl (unl g_out),unr g_out)])) =>//.
  rewrite (merge_iso (iso_union_A _ _ _)) /=.
  apply merge_same'.
  apply eqv_clot_eq.
   constructor. apply eqv_clot_trans with (unl (unl (g_in))); eqv. 
   constructor. apply eqv_clot_trans with (unl (unl (g_out))); eqv.
   leqv.

   constructor. eqv. 
   constructor. eqv. 
   constructor. apply eqv_clot_trans with (unl (unr g_in)); eqv. 
   constructor. apply eqv_clot_trans with (unl (unr g_out)); eqv. 
   leqv.
Qed.


Lemma seq2one (F: graph2): seq2' F one2 ≈ F.
Proof.
  rewrite /seq2' (merge_union_K2_lr (F:=_) (K:=_) _ _ (h:=_)
                                    (k:=fun _ => g_out)).
  destruct F. apply merge_nothing.
  repeat (constructor =>//=).
  by [].
  intros []; apply /eqquotP; eqv.
Qed.

Lemma seq2A (F G H: graph2): seq2' F (seq2' G H) ≈ seq2' (seq2' F G) H.
Proof.
  rewrite /seq2'/=.
  rewrite (merge_iso (iso_union_merge_r _ _)) /=.
  rewrite (merge_iso (iso_union_merge_l _ _)) /=.
  rewrite 2!h_union_merge_rEl 2!h_union_merge_lEl.
  rewrite 2!h_union_merge_rEr 2!h_union_merge_lEr.
  rewrite (merge_merge_seq2 (G:=union F (union G H))
                            (k:=[::(unl g_out,unr (unl g_in))])) =>//.
  rewrite (merge_merge_seq2 (G:=union (union F G) H)
                            (k:=[::(unl (unr g_out),unr g_in)])) =>//. 
  rewrite (merge_iso (iso_union_A _ _ _)) /=.
  apply merge_same'.
  apply eqv_clot_eq; leqv.
Qed.

Lemma cnv2I (F: graph2): cnv2' (cnv2' F) ≈ F.
Proof. by destruct F. Qed.

Lemma cnv2par (F G: graph2): cnv2' (par2' F G) ≈ par2' (cnv2' F) (cnv2' G).
Proof.
  rewrite /cnv2'/par2'. simpl.
  apply merge_same'.
  apply eqv_clot_eq; simpl; leqv.
Qed.

Lemma cnv2seq (F G: graph2): cnv2' (seq2' F G) ≈ seq2' (cnv2' G) (cnv2' F).
Proof.
  rewrite /cnv2'/seq2'. simpl.
  rewrite (merge_iso (iso_union_C _ _)) /=.
  apply merge_same'.
  apply eqv_clot_eq; simpl; leqv.
Qed.

Lemma par2oneone: par2' one2 one2 ≈ one2.
Proof.
  rewrite /par2'.
  rewrite (merge_union_K2_ll (K:=one2) _ _ (k:=fun _ => g_in)).
  simpl. apply merge_nothing.
  repeat (constructor =>//=).
  by [].
  intros []; apply /eqquotP; eqv.
Qed.

Lemma dom2'E (F: graph2): dom2' F ≈ par2' (seq2' F top2) one2.
Proof.
  rewrite /dom2'/par2'/seq2'/=.
  rewrite (merge_iso (iso_union_merge_l _ _)) /=.
  rewrite 2!h_union_merge_lEl 1!h_union_merge_lEr.
  rewrite (merge_merge_seq2 (G:=union (union F two_graph) unit_graph)
                            (k:=[::(unl (unl g_in),unr (tt: unit_graph)); (unl (unr (true: two_graph)),unr (tt: unit_graph))])) =>//.
  rewrite (merge_iso (iso_union_A' _ _ _)) /=.
  rewrite (merge_union_K2_lr (K:=union two_graph unit_graph) _ _ 
                             (k:=fun x => match x with inl false => g_out | _ => g_in end)).
  symmetry. apply merge_nothing. 
  repeat (constructor =>//=).
  by intros [|].
  intros [[|]|[]]; apply /eqquotP; try eqv.
  apply eqv_clot_trans with (unr (unr (tt: unit_graph))); eqv. 
Qed.

Lemma A10 (F G: graph2): par2' (seq2' F G) one2 ≈ dom2' (par2' F (cnv2' G)).
Proof.
  rewrite /par2'/seq2'/dom2'/cnv2'.
  rewrite (merge_iso (iso_union_merge_l _ _)) /=.
  rewrite 2!h_union_merge_lEl 1!h_union_merge_lEr.
  rewrite (merge_merge_seq2 (G:=union (union F G) unit_graph)
                            (k:=[::(unl (unl g_in),unr (tt: unit_graph)); (unl (unr g_out),unr (tt: unit_graph))])) =>//.
  rewrite (merge_union_K2_ll (F:=union F G) _ _ 
                             (k:=fun x => unl g_in)).
  2: by []. 2: intros []; apply /eqquotP; simpl; eqv.
  apply merge_same; simpl.
  apply eqv_clot_eq; simpl; leqv.
  eqv.
  eqv.
Qed.

Lemma A12' (F G: graph2): @g_in F = @g_out F -> seq2' F G ≈ par2' (seq2' F top2) G.
Proof.
  intro H. 
  rewrite /par2'/seq2'/=.
  rewrite (merge_iso (iso_union_merge_l _ _)) /=.
  rewrite 2!h_union_merge_lEl 2!h_union_merge_lEr.
  rewrite (merge_merge_seq2 (G:=union (union F two_graph) G)
                            (k:=[::(unl (unl g_in),unr g_in);(unl (unr (true: two_graph)),unr g_out)])) =>//.
  rewrite (merge_iso (iso_union_C (union _ _) _)) /=.
  rewrite (merge_iso (iso_union_A _ _ _)) /=.
  rewrite (merge_union_K2_lr (F:=union G F) (K:=two_graph) _ _ 
                             (k:=fun x => if x then unl g_out else unr g_in)).
  2: intros []. 2: intros []; apply /eqquotP; rewrite H; eqv.
  rewrite (merge_iso (iso_union_C _ _)) /=.
  apply merge_same'. rewrite H. apply eqv_clot_eq; leqv.
Qed.

Lemma A12 (F G: graph2): seq2' (par2' F one2) G ≈ par2' (seq2' (par2' F one2) top2) G.
Proof.
  apply A12'.
  apply /eqquotP. apply eqv_clot_trans with (unr (tt: unit_graph)); eqv.
Qed.

Lemma iso_two_graph: @iso_g two_graph (union unit_graph unit_graph)
                                 ((fun x: bool => if x then unl (tt: unit_graph) else unr (tt: unit_graph)),
                                  (fun x: void => match x with end)).
Proof.
  split. split. split; intros []. intros []. 
  split.
    by exists (fun x => match x with inl _ => true | _ => false end); [intros [|] | intros [[]|[]]].
    by exists (fun x => match x with inl x | inr x => x end); [intros [] | intros [|]].
Qed.

Lemma A11' (F: graph2): seq2' F top2 ≈ point (union F unit_graph) (unl g_in) (unr (tt: unit_graph)).
Proof.
  rewrite /seq2'/=.
  rewrite (merge_iso (union_iso_g iso_id iso_two_graph))/=. 
  rewrite (merge_iso (iso_union_A _ _ _))/=. 
  rewrite (merge_union_K2_ll (F:=union F _) _ _ (k:=fun x => unl g_out))//=.
  apply merge_nothing. by constructor. 
  intros []. apply /eqquotP. eqv. 
Qed.

Lemma A11 (F: graph2): seq2' F top2 ≈ seq2' (dom2' F) top2.
Proof. by rewrite 2!A11'. Qed.
