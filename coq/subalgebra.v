From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries sgraph multigraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 

Implicit Types (G H : graph) (U : sgraph) (T : tree).

(** * Tree decompositions (Muligraphs) *)

(** Covering is not really required, but makes the renaming theorem easier to state *)
Record decomp (T:tree) (G : graph) (bag : T -> {set G}) := Decomp
  { bag_cover x : exists t, x \in bag t; 
    bag_edge (e : edge G) : exists t, (source e \in bag t) && (target e \in bag t);
    bag_conn x t1 t2  : x \in bag t1 -> x \in bag t2 ->
      connect (restrict [pred t | x \in bag t] sedge) t1 t2}.


Definition compatible (T:tree) (G : graph2) (B : T -> {set G}) := 
  exists t, (g_in \in B t) && (g_out \in B t).

(** ** Renaming *)

Lemma rename_decomp (T : tree) (G H : graph) D (dec_D : decomp D) (h : h_ty G H) : 
  surjective2 h -> hom_g h -> 
  (forall x y, h.1 x = h.1 y -> exists t, (x \in D t) && (y \in D t)) -> 
  @decomp T _ (rename D h.1).
Proof.
  move => [sur1 sur2] hom_h comp_h. 
  split.
  - move => x. pose x0 := cr sur1 x. case: (bag_cover dec_D x0) => t Ht.
    exists t. apply/imsetP. exists x0; by rewrite ?crK. 
  - move => e. pose e0 := cr sur2 e. case: (bag_edge dec_D e0) => t /andP [t1 t2].
    exists t. apply/andP;split. 
    + apply/imsetP. exists (source e0) => //. by rewrite hom_h crK.
    + apply/imsetP. exists (target e0) => //. by rewrite hom_h crK.
  - move => x t1 t2 bg1 bg2. 
    case/imsetP : (bg1) (bg2) => x0 A B /imsetP [x1 C E]. subst. rewrite E in bg2.
    case: (comp_h _ _ E) => t /andP [F I]. 
    apply: (connect_trans (y := t)). 
    + apply: connect_mono (bag_conn dec_D A F) => u v /= /andP [/andP [X Y] Z]. 
      rewrite Z andbT. apply/andP;split; by apply/imsetP;exists x0.
    + apply: connect_mono (bag_conn dec_D I C) => u v /= /andP [/andP [X Y] Z]. 
      rewrite E Z andbT. apply/andP;split; by apply/imsetP;exists x1.
Qed.

Lemma rename_width (T:tree) (G : graph) (D : T -> {set G}) (G' : finType) (h : G -> G') :
  width (rename D h) <= width D.
Proof. rewrite max_mono // => t. exact: leq_imset_card. Qed.

(** ** Disjoint Union *)

Section JoinT.
  Variables (T1 T2 : tree).

  (* This could be rephrased as "codom inl is a subtree" *)
  Lemma sub_inl (a b : T1) (p : seq (sjoin T1 T2)) : 
    @upath (sjoin T1 T2) (inl a) (inl b) p -> {subset p <= codom inl}.
  Proof. 
    elim: p a => // c p IH a. rewrite upath_cons. case: c => // c /and3P [? ? ?].
    apply/subset_cons. split;eauto. by rewrite codom_f. 
  Qed.

  Lemma sub_inr (a b : T2) (p : seq (sjoin T1 T2)) : 
    @upath (sjoin T1 T2) (inr a) (inr b) p -> {subset p <= codom inr}.
  Proof. 
    elim: p a => // c p IH a. rewrite upath_cons. case: c => // c /and3P [? ? ?].
    apply/subset_cons. split;eauto. by rewrite codom_f. 
  Qed.

  Arguments inl_inj [A B].
  Prenex Implicits inl_inj.

  Lemma join_tree_axiom : tree_axiom (sjoin T1 T2).
  Proof.
    move => [a|a] [b|b].
    - move => p q Up Uq.
      case: (lift_upath _ _ Up (sub_inl Up)) => //; first exact: inl_inj. 
      case: (lift_upath _ _ Uq (sub_inl Uq)) => //; first exact: inl_inj. 
      move => p0 [P0 P1] q0 [Q0 Q1]. 
      suff E: p0 = q0 by congruence. 
      exact: (@treeP _ a b).
    - move => p q U. suff: connect sedge (inl a : sjoin T1 T2) (inr b) by rewrite join_disc. 
      apply/upathP; by exists p.
    - move => p q U. suff: connect sedge (inl b : sjoin T1 T2) (inr a) by rewrite join_disc. 
      rewrite connect_symI; last exact: join_rel_sym. apply/upathP. by exists p.
    - move => p q Up Uq.
      case: (lift_upath _ _ Up (sub_inr Up)) => //; first exact: inr_inj. 
      case: (lift_upath _ _ Uq (sub_inr Uq)) => //; first exact: inr_inj. 
      move => p0 [P0 P1] q0 [Q0 Q1]. 
      suff E: p0 = q0 by congruence. 
      exact: (@treeP _ a b).
  Qed.
      
  Definition tjoin := @Tree (sjoin T1 T2) join_tree_axiom.

  Definition decompU G1 G2 (D1 : T1 -> {set G1}) (D2 : T2 -> {set G2}) : tjoin -> {set union G1 G2} := 
    [fun a => match a with 
          | inl a => [set inl x | x in D1 a]
          | inr a => [set inr x | x in D2 a]
          end].

  Lemma join_decomp G1 G2 (D1 : T1 -> {set G1}) (D2 : T2 -> {set G2})  :
    decomp D1 -> decomp D2 -> decomp (decompU D1 D2).
  Proof.
    move => dec1 dec2. split.
    - move => [x|x]. 
      + case: (bag_cover dec1 x) => t Ht. exists (inl t) => /=. by rewrite mem_imset.
      + case: (bag_cover dec2 x) => t Ht. exists (inr t) => /=. by rewrite mem_imset.
    - move => [e|e]. 
      + case: (bag_edge dec1 e) => t /andP [H1 H2]. exists (inl t) => /=. by rewrite !mem_imset.
      + case: (bag_edge dec2 e) => t /andP [H1 H2]. exists (inr t) => /=. by rewrite !mem_imset.
    - have inl_inr x t : inl x \in decompU D1 D2 (inr t) = false.
      { rewrite /decompU /=. apply/negbTE/negP. by case/imsetP. }
      have inr_inl x t : inr x \in decompU D1 D2 (inl t) = false.
      { rewrite /decompU /=. apply/negbTE/negP. by case/imsetP. }
      move => [x|x] [t1|t1] [t2|t2] /=  ; rewrite ?inl_inr ?inr_inl // => A B. 
      + pose e := restrict [pred t | x \in D1 t] sedge.
        apply: (connect_img (e:= e) (f := inl)).
        * move => a b. rewrite /e /= !in_simpl -andbA => /and3P[? ? ?].  
          by rewrite !mem_imset.
        * apply: bag_conn => //. 
          move: A. by case/imsetP => ? ? [->].
          move: B. by case/imsetP => ? ? [->].
      + pose e := restrict [pred t | x \in D2 t] sedge.
        apply: (connect_img (e:= e) (f := inr)).
        * move => a b. rewrite /e /= !in_simpl -andbA => /and3P[? ? ?].  
          by rewrite !mem_imset.
        * apply: bag_conn => //. 
          move: A. by case/imsetP => ? ? [->].
          move: B. by case/imsetP => ? ? [->].
  Qed.

  Lemma join_width G1 G2 (D1 : T1 -> {set G1}) (D2 : T2 -> {set G2}) (t1 : T1) (t2 : T2) : 
    width (decompU D1 D2) <= maxn (width D1) (width D2).
  Proof. 
    pose p := mem (codom inl) : pred tjoin.
    rewrite /width. rewrite (bigID p) /= geq_max. apply/andP; split.
    - apply: leq_trans (leq_maxl _ _). apply: eq_leq.
      rewrite (reindex inl) /=. 
      + apply eq_big => x; first by rewrite /p /= codom_f.
        move => _. rewrite /decompU /= card_imset //. exact: inl_inj.
      + apply: bij_on_codom t1. exact: inl_inj.
    - apply: leq_trans (leq_maxr _ _). apply: eq_leq.
      rewrite (reindex inr) /=. 
      + apply eq_big => x; first by apply/negP => /mapP [?]. 
        move => _. rewrite /decompU /= card_imset //. exact: inr_inj.
      + exists (fun x => if x is inr y then y else t2) => //= [[x0|//]]. 
        by rewrite in_simpl /p /= codom_f.
  Qed.

End JoinT.

(** ** Link Construction *)

Section Link. 
  Variables (T : tree) (t1 t2 : T).
  
  Hypothesis disconn_t1_t2 : ~~ connect sedge t1 t2.

  Definition link_rel a b := 
    match a,b with 
    | Some x,None => (x == t1) || (x == t2) 
    | None, Some x => (x == t1) || (x == t2)
    | Some x,Some y => x -- y
    | None,None => false
    end.

  Lemma link_rel_sym : symmetric link_rel.
  Proof. move => [x|] [y|] //=; by rewrite sg_sym. Qed.
  
  Lemma link_rel_irrefl : irreflexive link_rel.
  Proof. move => [x|] //=; by rewrite sg_irrefl. Qed.
  
  Definition link := SGraph link_rel_sym link_rel_irrefl. 

  Lemma lift_link_rel (x y : T) p : 
    @upath link (Some x) (Some y) p -> None \notin p -> 
    exists2 p0, upath x y p0 & p = map Some p0.
  Proof. 
    move => A B. case: (lift_upath _ _ A (codom_Some B))=> // [|p0 [? ?]].
    - exact: Some_inj.
    - by exists p0.
  Qed.

  Lemma lift_link_spath (x y : T) p : 
    @spath link (Some x) (Some y) p -> None \notin p -> 
    exists2 p0, spath x y p0 & p = map Some p0.
  Proof. 
    move => A B. case: (lift_spath _ _ A (codom_Some B))=> // [|p0 [? ?]]. 
    - exact: Some_inj.
    - by exists p0.
  Qed.

  Lemma unique_Some_aux x y : 
    unique (fun p => @upath link (Some x) (Some y) p /\ None \notin p).
  Proof.
    move => p q [p1 p2] [q1 q2].
    case: (lift_link_rel p1 p2) => p0 Up ->. 
    case: (lift_link_rel q1 q2) => q0 Uq ->. 
    by rewrite (treeP Up Uq).
  Qed.

  Lemma diamond x (p q : seq link) :
    @spath link (Some t1) (Some x) p -> 
    @spath link (Some t2) (Some x) q -> 
    None \notin p -> None \notin q -> False.
  Proof.
    move => pth_p pth_q Np Nq. 
    apply: (negP disconn_t1_t2). apply: (connect_trans (y := x)). 
    - case: (lift_link_spath pth_p Np) => p0 [P0 ?];subst.
      apply/spathP. by exists p0.
    - case: (lift_link_spath pth_q Nq) => p0 [P0 ?];subst.
      rewrite connect_symI; last exact: sg_sym. 
      apply/spathP. by exists p0.
  Qed.
        
  Lemma unique_None x : unique (@upath link None x).
  Proof.
    case: x => [x|]; last by move => p q /upath_nil -> /upath_nil ->. 
    case => [|a p] [|b q] //; try by [case|move => _ []].
    rewrite !upath_cons. case: b => // b. case: a => //= a. 
    move => /and3P [H1 /notin_tail H2 H3] /and3P [H4 /notin_tail H5 H6].
    suff/eqP ? : a == b. { subst b. congr cons. exact: (@unique_Some_aux a x). }
    case/orP : H1 => /eqP ?; case/orP : H4 => /eqP ?; subst => //; exfalso.
    - apply: (@diamond x p q) => //; exact: upathW.
    - apply: (@diamond x q p) => //; exact: upathW.
  Qed.
    
  Lemma unique_None' x : unique (@upath link x None).
  Proof. apply: (upath_sym (G := link)). exact: unique_None. Qed.

  Lemma upath_None_Some x p : 
    @upath link None (Some x) p ->  exists a p', p = Some a :: p' /\ a \in [set t1;t2].
  Proof. 
    case: p => // [[a|//]] p'. rewrite upath_cons /= => /and3P [H _ _]. 
    exists a. exists p'. by rewrite !inE. 
  Qed.

  Lemma link_none x y p q : 
    @upath link (Some x) (Some y) p -> @upath link (Some x) (Some y) q -> 
    None \in p -> None \in q.
  Proof.
    move => Up Uq in_p. apply: contraT => in_q. exfalso.
    case: (usplitP (G := link) (mem_tail _ in_p) Up) => {in_p Up p} p1 p2 Upl Upr.
    move/(rev_upath (G := link)) : (Upl) => Upl'.
    rewrite (eq_disjoint (srev_nodes (upathW Upl))) => D'.
    case: (upath_None_Some Upr) => a [p] [? H]. subst. 
    case: (upath_None_Some Upl') => b [p'] [E H']. rewrite E in Upl' D' => {E Upl p1}.
    case/upath_consE : Upr => _ /notin_tail P1 P2.
    case/upath_consE : Upl' => _ /notin_tail Q1 Q2.
    have {D'} X: a != b. 
    { apply/negP => /eqP ?;subst. by rewrite !disjoint_cons mem_head /= andbF in D'. }
    have [s S1 S2] : exists2 s, @spath link (Some b) (Some y) s & None \notin s.
    { exists (p'++q); first by spath_tac;eapply spath_concat; eassumption. (* TODO: fix spath_tac *)
      by rewrite mem_cat (negbTE in_q) (negbTE Q1). }
    rewrite !inE in H H'. case/orP : H; case/orP : H' => /eqP ? /eqP ?; 
      subst; try by rewrite eqxx in X.
    - apply: (@diamond y p s) => //. exact: upathW.
    - apply: (@diamond y s p) => //. exact: upathW.
  Qed.

  Lemma link_tree_axiom : tree_axiom link.
  Proof.
    move => [x|] [y|]; try solve [apply: unique_None]. 
    2: by apply: (upath_sym (G := link)) ; apply: unique_None.
    move => p q.  case: (boolP (None \in p)) => in_p Up Uq.
    - have in_q : None \in q by apply: link_none Uq in_p.
      case:(usplitP (G := link) (mem_tail _ in_p) Up) => pl pr Upl Upr _.
      case:(usplitP (G := link) (mem_tail _ in_q) Uq) => ql qr Uql Uqr _.
      by rewrite (unique_None Upr Uqr) (unique_None' Upl Uql).
    - have in_q : None \notin q. apply: contraNN in_p. exact: link_none Up.
      exact: (@unique_Some_aux x y). 
  Qed.

  Definition tlink := @Tree link link_tree_axiom.

  Definition decompL G (D : T -> {set G}) A a := 
    match a with Some x => D x | None => A end.

  
  Lemma decomp_link (G : graph) (D : T -> {set G}) (A  : {set G}) : 
    A \subset D t1 :|: D t2 ->
    decomp D -> @decomp tlink G (decompL D A).
  Proof.
    move => HA decD. split => //.
    - move => x. case: (bag_cover decD x) => t Ht. by exists (Some t). 
    - move => e. case: (bag_edge decD e) => t Ht. by exists (Some t).
    - have X x a : x \in D a -> x \in A -> 
        connect (restrict [pred t | x \in decompL D A t] link_rel) (Some a) None.
      { move => H1 H2.  move/(subsetP HA) : (H2). case/setUP => H3.
        - apply: (connect_trans (y := Some t1)). 
          + move: (bag_conn decD H1 H3). exact: connect_img.
          + apply: connect1 => /=; by rewrite !in_simpl H2 H3 !eqxx.
        - apply: (connect_trans (y := Some t2)). 
          + move: (bag_conn decD H1 H3). exact: connect_img.
          + apply: connect1 => /=. by rewrite !in_simpl H2 H3 !eqxx orbT. }
      move => x [a|] [b|] /= H1 H2; last exact: connect0. 
      + move: (bag_conn decD H1 H2). exact: connect_img. 
      + exact: X.
      + rewrite connect_symI; first exact: X. apply: symmetric_restrict. exact: link_rel_sym.
  Qed.

  Lemma width_link (G : graph) (D : T -> {set G}) (A  : {set G}) : 
    width (decompL D A) <= maxn (width D) #|A|.
  Proof.
    rewrite /width (bigID (pred1 None)) /= geq_max. apply/andP;split.
    - apply: leq_trans (leq_maxr _ _). by rewrite big_pred1_eq. 
    - rewrite (reindex Some) /= ?leq_maxl //.
      exists (fun x => if x is Some y then y else t1) => // x0. by case: x0.
  Qed.

End Link.


(** * Subalgebra of Tree-Width 2 Graphs *)

(** ** Closure Properties for operations *)

Arguments decomp T G bag : clear implicits.

Section Quotients. 
  Variables (G1 G2 : graph2).
  
  Let P : {set union G1 G2} := [set inl g_in; inl g_out; inr g_in; inr g_out].

  Definition admissible (eqv : rel (union G1 G2)) := 
    forall x y, eqv x y -> x = y \/ [set x;y] \subset P. 
 
  Lemma decomp_quot (T1 T2 : tree) D1 D2 (e : equiv_rel (union G1 G2)): 
    decomp T1 G1 D1 -> decomp T2 G2 D2 -> 
    compatible D1 -> compatible D2 ->
    width D1 <= 3 -> width D2 <= 3 ->
    admissible e -> #|(hom_of e).1 @: P| <= 3 ->
    exists T D, [/\ decomp T (merge (union G1 G2) e) D, 
              width D <= 3 & exists t, 
              D t = (hom_of e).1 @: P].
  Proof.
    move => dec1 dec2 [t1 /andP [comp1_in comp1_out]] [t2 /andP [comp2_in comp2_out]] W1 W2.
    move => adm_e collapse_P.
    pose T := tjoin T1 T2.
    pose D := decompU D1 D2.
    have dec_D : decomp T (union G1 G2) D by exact: join_decomp. 
    have dis_t1_t2 : ~~ connect (@sedge T)(inl t1) (inr t2) by rewrite join_disc.
    pose T' := tlink dis_t1_t2.
    pose D' := decompL D P.
    have dec_D' : decomp T' (union G1 G2) D'.
    { apply: decomp_link => //. apply/subsetP => x.
      rewrite !inE -!orbA => /or4P [] /eqP->; by rewrite mem_imset ?orbT. }
    pose h := @hom_of (union G1 G2) e : h_ty _ (merge (union G1 G2) e).
    exists T'. exists (rename D' h.1); split; last by exists None.
    - apply: rename_decomp => //; first exact: hom_of_surj.
      move => x y. move/eqmodP => /=. case/adm_e => [<-|A].
      + case: (bag_cover dec_D' x) => t Ht. exists t. by rewrite Ht.
      + exists None. rewrite /= -!sub1set -subUset. done.
    - rewrite /width (bigID (pred1 None)).
      rewrite big_pred1_eq. rewrite geq_max. apply/andP;split => //.
      + rewrite (reindex Some) /=.
        * apply: (@leq_trans (maxn (width D1) (width D2))); last by rewrite geq_max W1 W2.
          apply: leq_trans (join_width _ _ t1 t2). 
          apply: max_mono => t. exact: leq_imset_card.
        * apply: subon_bij; last by apply bij_on_codom; [exact: Some_inj|exact: (inl t1)]. 
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
  Admitted.

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

  Lemma par2_equiv_of : par2_eqv =2 equiv_of par2_eq.
  Admitted.

  Definition par2 := 
    {| graph_of := merge (union G1 G2) par2_eqv ;
       g_in := \pi_{eq_quot par2_eqv} (inl g_in);
       g_out := \pi_{eq_quot par2_eqv} (inl g_out) |}.

  Lemma par2_eqvP : admissible par2_eqv.
  Proof. 
    move=> x y. case/orP=> [/eqP|]; first by left. case: ifP; last by right.
    rewrite !inE => _ /orP[]/eqP->; by right; rewrite subUset !sub1set !inE !eqxx.
  Qed.

  Lemma decomp_par2 (T1 T2 : tree) D1 D2 : 
    decomp T1 G1 D1 -> decomp T2 G2 D2 -> 
    compatible D1 -> compatible D2 ->
    width D1 <= 3 -> width D2 <= 3 ->
    exists T D, [/\ decomp T (par2) D, compatible D & width D <= 3].
  Proof.
    move => dec1 dec2 comp1 comp2 W1 W2.
    case: (decomp_quot (e:= [equiv_rel of par2_eqv]) dec1 dec2 comp1 comp2 W1 W2 _ _).
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
    - move => T [D] [A B [t C]]. exists T. exists D. split => //. exists t. 
      by rewrite C !mem_imset // !inE ?eqxx ?orbT.
  Qed.

  Definition seq2_eqv : rel (union G1 G2) :=
    fun x y => (x == y) || ([set x; y] == [set inl g_out; inr g_in]).

  Definition seq2_eqv_refl : reflexive seq2_eqv.
  Proof. by move=> ?; rewrite /seq2_eqv eqxx. Qed.

  Lemma seq2_eqv_sym : symmetric seq2_eqv.
  Proof. move=> x y. by rewrite /seq2_eqv [[set y; x]]setUC [y == x]eq_sym. Qed.

  Definition seq2_eqv_trans : transitive seq2_eqv.
  Admitted.

  Canonical seq2_eqv_equivalence :=
    EquivRel seq2_eqv seq2_eqv_refl seq2_eqv_sym seq2_eqv_trans.

  Lemma seq2_eqv_io : seq2_eqv (inl g_out) (inr g_in).
  Proof. by rewrite /seq2_eqv/=. Qed.

  Definition seq2_eq : rel (union G1 G2) :=
    [rel a b | (a == inl g_out) && (b == inr g_in)].

  Lemma seq2_equiv_of : seq2_eqv =2 equiv_of seq2_eq.
  Admitted.

  Definition seq2 :=
    {| graph_of := merge (union G1 G2) seq2_eqv ;
       g_in := \pi_{eq_quot seq2_eqv} (inl g_in);
       g_out := \pi_{eq_quot seq2_eqv} (inr g_out) |}.

  Lemma seq2_eqvP : admissible seq2_eqv.
  Proof. 
    move=> x y. case/orP => /eqP->; [by left | right].
    by rewrite subUset !sub1set !inE !eqxx.
  Qed.

  Lemma decomp_seq2 (T1 T2 : tree) D1 D2 : 
    decomp T1 G1 D1 -> decomp T2 G2 D2 -> 
    compatible D1 -> compatible D2 ->
    width D1 <= 3 -> width D2 <= 3 ->
    exists T D, [/\ decomp T seq2 D, compatible D & width D <= 3].
  Proof.
    move => dec1 dec2 comp1 comp2 W1 W2.
    case: (decomp_quot (e:= [equiv_rel of seq2_eqv]) dec1 dec2 comp1 comp2 W1 W2 _ _).
    - exact: seq2_eqvP.
    - pose P' : {set union G1 G2} := [set inl g_in; inl g_out; inr g_out].
      apply: (@leq_trans #|P'|); last apply cards3.
      apply: (@leq_trans #|[set (\pi x : seq2) | x in P']|); last exact: leq_imset_card.
      apply: subset_leq_card.
      apply/subsetP => ? /imsetP [x H1 ->]. move: H1. 
      rewrite /P -!setUA [[set _;_]]setUC !setUA. case/setUP => H1.
      * by rewrite mem_imset.
      * case/set1P : H1 => ->. apply/imsetP. exists (inl g_out); first by rewrite !inE eqxx ?orbT.
        apply/eqmodP. by rewrite equiv_sym /= seq2_eqv_io.
    - move => T [D] [A B [t C]]. exists T. exists D. split => //. exists t. 
      by rewrite C !mem_imset // !inE ?eqxx ?orbT.
  Qed.

End Quotients.

Definition cnv2 (G : graph2) :=
  {| graph_of := G; g_in := g_out; g_out := g_in |}.

Lemma decomp_cnv (G : graph2) T D : 
  decomp T G D -> decomp T (cnv2 G) D.
Proof. done. Qed.

Lemma compat_cnv (G : graph2) T (D : T -> {set G}) : 
  compatible D -> compatible (G := cnv2 G) D.
Proof. move => [t] H. exists t => /=. by rewrite andbC. Qed.

Definition dom2 (G : graph2) := 
  {| graph_of := G; g_in := g_in; g_out := g_in |}.

Lemma decomp_dom (G : graph2) T D : 
  decomp T G D -> decomp T (dom2 G) D.
Proof. done. Qed.

Lemma compat_dom (G : graph2) T (D : T -> {set G}) : 
  compatible D -> compatible (G := dom2 G) D.
Proof. 
  move => [t] /andP [H _]. exists t => /=. by rewrite !H. 
Qed.

Definition triv_decomp (G : graph) :
  decomp tunit G (fun _ => [set: G]).
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
  exists T D, [/\ decomp T G D, compatible D & width D <= 3].
Proof. 
  exists tunit; exists (fun => setT). split.
  - exact: triv_decomp.
  - exists tt. by rewrite !inE.
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
  exists T D, [/\ decomp T (graph_of_term u) D, compatible D & width D <= 3].
Proof.
  elim: u => [a| | | u IHu | u IHu v IHv | u IHu v IHv | u IHu ].
  - apply: decomp_small. by rewrite card_bool.
  - apply: decomp_small. by rewrite card_unit.
  - apply: decomp_small. by rewrite card_bool.
  - move: IHu => [T] [D] [D1 D2 D3]. exists T. exists D. split => //. 
    exact: compat_cnv. (* FIXME: Hidden argument *)
  - move: IHu IHv => [T1] [D1] [? ? ?] [T2] [D2] [? ? ?].
    simpl graph_of_term. exact: (decomp_seq2 (D1 := D1) (D2 := D2)).
  - move: IHu IHv => [T1] [D1] [? ? ?] [T2] [D2] [? ? ?].
    simpl graph_of_term. exact: (decomp_par2 (D1 := D1) (D2 := D2)).
  - move: IHu => [T] [D] [D1 D2 D3]. exists T. exists D. split => //. 
    exact: compat_dom. (* FIXME: Hidden argument *)
Qed.
