From mathcomp Require Import all_ssreflect.
Require Import finite_quotient preliminaries sgraph multigraph.

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

(** Non-standard: we do not substract 1 *)
Definition width (T G : finType) (D : T -> {set G}) := \max_(t:T) #|D t|.

Definition compatible (T:tree) (G : graph2) (B : T -> {set G}) := 
  exists t, (g_in \in B t) && (g_out \in B t).

Definition rename (T G G' : finType) (B: T -> {set G}) (h : G -> G') := [fun x => h @: B x].

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

  (** The following lemmas use [subset_upath] though this is not needed *)
  Lemma sub_inl (a b : T1) (p : seq (sjoin T1 T2)) : 
    upath join_rel (inl a) (inl b) p -> {subset p <= codom inl}.
  Proof. 
    case => p1 p2 p3.
    apply: subset_upath p2 p3 p1; try solve [exact: join_rel_sym|by rewrite codom_f].
    apply: empty_uniqe => [[x|x]] [[H [[y|y]]]] [B C] => //;
      rewrite ?codom_f ?inr_codom_inl // in H B. 
  Qed.

  Lemma sub_inr (a b : T2) (p : seq (sjoin T1 T2)) : 
    upath join_rel (inr a) (inr b) p -> {subset p <= codom inr}.
  Proof. 
    case => p1 p2 p3.
    apply: subset_upath p2 p3 p1; try solve [exact: join_rel_sym|by rewrite codom_f].
    apply: empty_uniqe => [[x|x]] [[H [[y|y]]]] [B C] => //;
      rewrite ?codom_f ?inl_codom_inr // in H B. 
  Qed.

  Lemma join_tree_axiom : tree_axiom (@join_rel T1 T2).
  Proof.
    move => [a|a] [b|b].
    - move => p q Up Uq.
      case: (lift_upath (e := sedge) _ (@inl_inj _ _) Up (sub_inl Up)) => // p0 [P0 P1].
      case: (lift_upath (e := sedge) _ (@inl_inj _ _) Uq (sub_inl Uq)) => // q0 [Q0 Q1]. 
      suff E: p0 = q0 by congruence. 
      exact: (@treeP _ a b).
    - move => p q [p1 p2 p3] _. suff: connect join_rel (inl a) (inr b) by rewrite join_disc.
      apply/connectP. by exists p.
    - move => p q [p1 p2 p3] _. suff: connect join_rel (inl b) (inr a) by rewrite join_disc.
      rewrite connect_symI; last exact: join_rel_sym. apply/connectP. by exists p.
    - move => p q Up Uq.
      case: (lift_upath (e := sedge) _ (@inr_inj _ _) Up (sub_inr Up)) => // p0 [P0 P1].
      case: (lift_upath (e := sedge) _ (@inr_inj _ _) Uq (sub_inr Uq)) => // q0 [Q0 Q1]. 
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
    upath link_rel (Some x) (Some y) p -> None \notin p -> 
    exists2 p0, upath sedge x y p0 & p = map Some p0.
  Proof. 
    move => A B. case: (lift_upath (e:= sedge) _ _ A (codom_Some B)) => // [|p0 [? ?]].
    - exact: Some_inj.
    - by exists p0.
  Qed.

  Lemma unique_Some_aux x y : 
    unique (fun p => upath link_rel (Some x) (Some y) p /\ None \notin p).
  Proof.
    move => p q [p1 p2] [q1 q2].
    case: (lift_link_rel p1 p2) => p0 Up ->. 
    case: (lift_link_rel q1 q2) => q0 Uq ->. 
    by rewrite (treeP Up Uq).
  Qed.

  Lemma diamond x p q :
    path link_rel (Some t1) p -> last (Some t1) p = Some x -> 
    path link_rel (Some t2) q -> last (Some t2) q = Some x ->
    None \notin p -> None \notin q -> False.
  Proof.
    move => pth_p lst_p pth_q lst_q Np Nq. apply: (negP disconn_t1_t2).
    apply: (connect_trans (y := x)). 
    - case: (lift_path (e:= sedge) _ pth_p (codom_Some Np)) => // p0 [P0 ?];subst. 
      apply/connectP. exists p0 => //. move/esym: lst_p. rewrite last_map. exact: Some_inj.
    - rewrite connect_symI; last exact: sg_sym. 
      case: (lift_path (e:= sedge) _ pth_q (codom_Some Nq)) => // q0 [Q0 ?];subst. 
      apply/connectP. exists q0 => //. move/esym: lst_q. rewrite last_map. exact: Some_inj.
  Qed.
        
  Lemma unique_None x : unique (upath link_rel None x).
  Proof.
    case: x => [x|]; last by move => p q /upath_nil -> /upath_nil ->. 
    case => [|a p] [|b q] //; try by [case|move => _ []].
    case/upath_cons. case: a => //= a => H1 _ H2 H3.
    case/upath_cons. case: b => //= b => H4 _ H5 H6.
    suff/eqP ? : a == b. { subst b. congr cons. exact: (@unique_Some_aux a x). }
    case/orP : H1 => /eqP ?; case/orP : H4 => /eqP ?; subst => //; exfalso.
    - by apply: (@diamond x p q) => //; firstorder.
    - by apply: (@diamond x q p) => //; firstorder.
  Qed.
    
  Lemma unique_None' x : unique (upath link_rel x None).
  Proof. apply: (upath_sym (G := link)). exact: unique_None. Qed.

  Lemma upath_None_Some x p : 
    upath link_rel None (Some x) p ->  exists a p', p = Some a :: p' /\ a \in [set t1;t2].
  Proof. 
    case: p => [[//]|[a|] p']; last by case. 
    case => /= [_ /andP[A ?] _]. exists a. exists p'. by rewrite !inE. 
  Qed.

  Lemma link_none x y p q : 
    upath link_rel (Some x) (Some y) p -> upath link_rel (Some x) (Some y) q -> 
    None \in p -> None \in q.
  Proof.
    move => Up Uq in_p. apply/negP => in_q. 
    case: (path.splitP in_p) Up => pl pr /upath_split [/(rev_upath (G := link)) Upl Upr D].
    move => {p in_p}. 
    move: Upl. rewrite belast_rcons rev_cons. move E : (rcons _ _) => pl' Upl'.
    have {D E} D' : [disjoint pl' & pr]. 
    { apply: disjoint_trans D. apply/subsetP => a. rewrite -E ?(mem_rcons,in_cons,mem_rev). 
      case/orP => -> //. by rewrite !orbT. }
    case: (upath_None_Some Upr) => a [p] [? H]. subst. 
    case: (upath_None_Some Upl') => b [p'] [? H']. subst.
    case/upath_cons : Upr => _ _ P1 [_ P2 P3].
    case/upath_cons : Upl' => _ _ Q1 [_ Q2 Q3].
    case: Uq => _ pth_q lst_q. 
    have Q1': None \notin p'++q. rewrite mem_cat (negbTE Q1) /=. by apply/negP.
    have Q2': path link_rel (Some b) (p'++q) by rewrite cat_path Q2 Q3. 
    have {Q1 Q2 Q3 pth_q lst_q} Q3': last (Some b) (p'++q) = Some y by rewrite last_cat Q3.   
    have {D'} X: a != b. 
    { apply/negP => /eqP ?;subst. rewrite disjoint_subset in D'. move/subsetP/subset_cons : D'.
      rewrite !inE !eqxx //=. by case. (* FIXME: done should split conjunctions *) }
    rewrite !inE in H H'. case/orP : H; case/orP : H' => /eqP ? /eqP ?; 
      subst; try by rewrite eqxx in X.
    - exact: (@diamond y p (p'++q)).
    - exact: (@diamond y (p'++q) p).
  Qed.

  Lemma link_tree_axiom : tree_axiom link_rel.
  Proof.
    move => [x|] [y|]; try solve [apply: unique_None]. 
    2: by apply: (upath_sym (G := link)) ; apply: unique_None.
    move => p q.  case: (boolP (None \in p)) => in_p Up Uq.
    - have in_q : None \in q by apply: link_none Uq in_p.
      case: (path.splitP in_p) Up => {p in_p} pl pr. 
      case/upath_split => Upl Upr _.
      case: (path.splitP in_q) Uq => {q in_q} ql qr. 
      case/upath_split => Uql Uqr _.
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

  Lemma admissibleI (e : rel (union G1 G2)) : 
    (forall x y, e x y -> [set x;y] \subset P) -> admissible (equiv_of e).
  Proof.
    move => H x y. 
    have sub_P p a : path (sc e) a p -> {subset p <= P}.
    { elim: p a => //= b p IH a /andP [A B]. 
      apply/subset_cons; split;eauto.
      by case/orP : A => /H; rewrite subUset !sub1set => /andP[]. }
    case/connectP => p. case: p => /= [_ <- |]; first by left.
    rewrite -/(sc e). move => a p /andP[A B] C. 
    have [C1 C2] : x \in P /\ a \in P. 
    { case/orP : A => /H; by rewrite subUset !sub1set => /andP[]. } 
    right. rewrite subUset !sub1set C1 /= C. 
    move: (mem_last a p). rewrite inE. case/predU1P => [->//|] /=. 
    exact: sub_P B _.
  Qed.
 
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

  Definition eq_par2 (x y : union G1 G2) := 
    match x,y with
    | inl x, inr y => (x == g_in) && (y == g_in) || (x == g_out) && (y == g_out)
    | _,_ => false
    end.

  Definition eqv_par2 := equiv_of eq_par2.

  Definition par2 := 
    {| graph_of := merge (union G1 G2) eqv_par2 ;
       g_in := \pi_{eq_quot eqv_par2} (inl g_in);
       g_out := \pi_{eq_quot eqv_par2} (inl g_out) |}.

  Lemma eqv_par2P : admissible eqv_par2.
  Proof. 
    apply: admissibleI => [[x|x] [y|y]] //= /orP [] /andP[/eqP-> /eqP->]; 
      by rewrite subUset !sub1set !inE ?eqxx ?orbT.
  Qed.

  Lemma decomp_par2 (T1 T2 : tree) D1 D2 : 
    decomp T1 G1 D1 -> decomp T2 G2 D2 -> 
    compatible D1 -> compatible D2 ->
    width D1 <= 3 -> width D2 <= 3 ->
    exists T D, [/\ decomp T (par2) D, compatible D & width D <= 3].
  Proof.
    move => dec1 dec2 comp1 comp2 W1 W2.
    case: (decomp_quot (e:= [equiv_rel of eqv_par2]) dec1 dec2 comp1 comp2 W1 W2 _ _).
    - exact: eqv_par2P.
    - pose P' : {set union G1 G2} := [set inl g_in; inl g_out].
      apply: (@leq_trans #|P'|); last by rewrite cards2; by case (_ != _).
      apply: (@leq_trans #|[set (\pi x : par2) | x in P']|); last exact: leq_imset_card.
      apply: subset_leq_card.
      apply/subsetP => ? /imsetP [x H1 ->]. case/setUP : H1 => H1; first case/setUP : H1 => H1.
      * by rewrite mem_imset.
      * case/set1P : H1 => ->. apply/imsetP. exists (inl g_in); first by rewrite !inE eqxx ?orbT.
        apply/eqmodP. apply: sub_connect. by rewrite /= !eqxx.
      * case/set1P : H1 => ->. apply/imsetP. exists (inl g_out); first by rewrite !inE eqxx ?orbT.
        apply/eqmodP. apply: sub_connect. by rewrite /= !eqxx orbT.
    - move => T [D] [A B [t C]]. exists T. exists D. split => //. exists t. 
      by rewrite C !mem_imset // !inE ?eqxx ?orbT.
  Qed.

  Definition eq2 (T : finType) (x y : T) :=
    [rel a b | (a == x) && (b == y)].

  Definition eq_seq2 : rel (union G1 G2) := eq2 (inl g_out) (inr g_in).
  Definition eqv_seq2 := equiv_of eq_seq2.

  Definition seq2 :=
    {| graph_of := merge (union G1 G2) eqv_seq2 ;
       g_in := \pi_{eq_quot eqv_seq2} (inl g_in);
       g_out := \pi_{eq_quot eqv_seq2} (inr g_out) |}.

  Lemma eqv_seq2P : admissible eqv_seq2.
  Proof. 
    apply: admissibleI => [[x|x] [y|y]] //= /andP[/eqP-> /eqP->]; 
      by rewrite subUset !sub1set !inE ?eqxx ?orbT.
  Qed.

  Lemma decomp_seq2 (T1 T2 : tree) D1 D2 : 
    decomp T1 G1 D1 -> decomp T2 G2 D2 -> 
    compatible D1 -> compatible D2 ->
    width D1 <= 3 -> width D2 <= 3 ->
    exists T D, [/\ decomp T seq2 D, compatible D & width D <= 3].
  Proof.
    move => dec1 dec2 comp1 comp2 W1 W2.
    case: (decomp_quot (e:= [equiv_rel of eqv_seq2]) dec1 dec2 comp1 comp2 W1 W2 _ _).
    - exact: eqv_seq2P.
    - pose P' : {set union G1 G2} := [set inl g_in; inl g_out; inr g_out].
      apply: (@leq_trans #|P'|); last apply cards3.
      apply: (@leq_trans #|[set (\pi x : seq2) | x in P']|); last exact: leq_imset_card.
      apply: subset_leq_card.
      apply/subsetP => ? /imsetP [x H1 ->]. move: H1. 
      rewrite /P -!setUA [[set _;_]]setUC !setUA. case/setUP => H1.
      * by rewrite mem_imset.
      * case/set1P : H1 => ->. apply/imsetP. exists (inl g_out); first by rewrite !inE eqxx ?orbT.
        apply/eqmodP. apply: sub_connect. by rewrite /eq_seq2 /= !eqxx.
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

Definition sunit := @SGraph [finType of unit] rel0 rel0_sym rel0_irrefl.

Definition unit_tree_axiom : tree_axiom (@sedge sunit).
Proof. by move => [] [] p q /upath_nil -> /upath_nil -> . Qed.

Definition tunit := Tree unit_tree_axiom.

Definition triv_decomp (G : graph2) :
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
| tmI of term & term.

Fixpoint graph_of_term (u:term) {struct u} : graph2 := 
  match u with
  | tmA a => sym2 a
  | tm1 => one2
  | tmT => top2
  | tmC u => cnv2 (graph_of_term u)
  | tmS u v => seq2 (graph_of_term u) (graph_of_term v)
  | tmI u v => par2 (graph_of_term u) (graph_of_term v)
  end.

Theorem graph_of_TW2 (u : term) : 
  exists T D, [/\ decomp T (graph_of_term u) D, compatible D & width D <= 3].
Proof.
  elim: u => [a| | | u IHu | u IHu v IHv | u IHu v IHv ].
  - apply: decomp_small. by rewrite card_bool.
  - apply: decomp_small. by rewrite card_unit.
  - apply: decomp_small. by rewrite card_bool.
  - move: IHu => [T] [D] [D1 D2 D3]. exists T. exists D. split => //. 
    exact: compat_cnv. (* FIXME: Hidden argument *)
  - move: IHu IHv => [T1] [D1] [? ? ?] [T2] [D2] [? ? ?].
    simpl graph_of_term. exact: (decomp_seq2 (D1 := D1) (D2 := D2)).
  - move: IHu IHv => [T1] [D1] [? ? ?] [T2] [D2] [? ? ?].
    simpl graph_of_term. exact: (decomp_par2 (D1 := D1) (D2 := D2)).
Qed.

  