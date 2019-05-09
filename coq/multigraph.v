Require Import Setoid CMorphisms.
From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries finite_quotient equiv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

(** * Directed Multigraphs *)

(** We define finite directed multigraphs with labels from a fixed
type [sym] (i.e., an encapuslated copy of [nat]. We define a number of
constructions on these graphs: *)

(** [union G H] : disjoint union of the graphs [G] and [H]. *)

(** [merge G e] : the quotent graph with verticies quotiented by [e:equiv_rel]. *)

(* FIXME: Properly abstract this *)
Lemma _symbols : { sym : eqType & sym }. exists [eqType of nat]; exact: 0. Qed.
Definition sym : eqType := projT1 _symbols.
Definition sym0 : sym := projT2 _symbols.


Record graph := Graph { vertex :> finType;
                        edge: finType;
                        source : edge -> vertex;
                        target : edge -> vertex;
                        label : edge -> sym }.

Notation vfun := (fun x : void => match x with end).  
Definition unit_graph := @Graph [finType of unit] _ vfun vfun vfun.
Definition two_graph := @Graph [finType of bool] _ vfun vfun vfun.
Definition edge_graph (a : sym) := Graph (fun _ : unit => false) (fun _ => true) (fun _ => a).                           

(** *** Edge sets *)

Definition edges (G : graph) (x y : G) :=
  [set e | (source e == x) && (target e == y)].

Definition edge_set (G:graph) (S : {set G}) :=
  [set e | (source e \in S) && (target e \in S)].

Lemma edge_set1 (G : graph) (x : G) : edge_set [set x] = edges x x.
Proof. apply/setP=> e. by rewrite !inE. Qed.

Lemma edge_in_set (G : graph) e (A : {set G}) x y :
  x \in A -> y \in A -> e \in edges x y -> e \in edge_set A.
Proof. move => Hx Hy. rewrite !inE => /andP[/eqP->/eqP->]. by rewrite Hx. Qed.

(** ** Disjoint Union *)

Definition union (G1 G2 : graph) : graph :=
  {| vertex := [finType of G1 + G2];
     edge := [finType of edge G1 + edge G2];
     source := sumf (@source G1) (@source G2);
     target := sumf (@target G1) (@target G2);
     label e := match e with inl e => label e | inr e => label e end |}.

Definition unl {G H: graph} (x: G): union G H := inl x.
Definition unr {G H: graph} (x: H): union G H := inr x.

(** ** Homomorphisms *)


Class is_hom (F G: graph) (hv: F -> G) (he: edge F -> edge G): Prop := Hom
  { source_hom: forall e, source (he e) = hv (source e);
    target_hom: forall e, target (he e) = hv (target e);
    label_hom: forall e, label (he e) = label e }.

Lemma hom_id G: @is_hom G G id id.
Proof. by split. Qed.

Lemma hom_comp F G H hv he kv ke:
  @is_hom F G hv he -> @is_hom G H kv ke -> is_hom (kv \o hv) (ke \o he).
Proof.
  intros E E'. split; intro e=>/=.
  by rewrite 2!source_hom. 
  by rewrite 2!target_hom. 
  by rewrite 2!label_hom. 
Qed.

Lemma hom_sym (F G: graph) (hv: bij F G) (he: bij (edge F) (edge G)):
  is_hom hv he -> 
  is_hom hv^-1 he^-1.
Proof.
  intro H. split=>e/=.
  by rewrite -{2}(bijK' he e) source_hom bijK. 
  by rewrite -{2}(bijK' he e) target_hom bijK. 
  by rewrite -{2}(bijK' he e) label_hom. 
Qed.

Lemma Hom' (F G: graph) (hv: F -> G) (he: edge F -> edge G) :
  (forall e, [/\ hv (source e) = source (he e),
              hv (target e) = target (he e) &
              label (he e) = label e]) -> is_hom hv he.
Proof. move=>H. split=> e; by case: (H e). Qed.
  
(** ** Quotient Graphs *)

Definition merge (G : graph) (r : equiv_rel G) :=
  {| vertex := quot r;
     edge := (edge G);
     source e := \pi (source e);
     target e := \pi (target e);
     label e := label e |}.

Arguments merge: clear implicits.


(** ** Subgraphs and Induced Subgraphs *)

Definition subgraph (H G : graph) := 
  exists hv he, @is_hom H G hv he /\ injective hv /\ injective he.

Section Subgraphs.
  Variables (G : graph) (V : {set G}) (E : {set edge G}).
  Definition consistent := forall e, e \in E -> source e \in V /\ target e \in V.
  Hypothesis in_V : consistent.
  
  Definition sub_vertex := sig [eta mem V].
  Definition sub_edge := sig [eta mem E].

  Fact source_proof (e : sub_edge) : source (val e) \in V.
  Proof. by move: (svalP e) => /in_V []. Qed.

  Fact target_proof (e : sub_edge) : target (val e) \in V.
  Proof. by move: (svalP e) => /in_V []. Qed.

  Definition subgraph_for := 
    {| vertex := [finType of sub_vertex];
       edge := [finType of sub_edge];
       source e := Sub (source (val e)) (source_proof e);
       target e := Sub (target (val e)) (target_proof e);
       label e := label (val e) |}.

  Lemma subgraph_sub : subgraph subgraph_for G.
  Proof. exists val, val. split => //=. split; exact: val_inj. Qed.
End Subgraphs.

(** Frequently used consistent sets of vertices and edges *)

Lemma consistentT (G : graph) (E : {set edge G}) : consistent setT E.
Proof. by []. Qed.
Arguments consistentT [G] E.

Lemma consistentTT (G : graph) : consistent [set: G] [set: edge G].
Proof. done. Qed.
Arguments consistentTT : clear implicits.


Definition induced_proof (G: graph) (S : {set G}) : consistent S (edge_set S).
Proof. move => e. by rewrite inE => /andP. Qed.

Definition induced (G: graph) (S : {set G}) := 
  subgraph_for (@induced_proof G S).

Lemma induced_sub (G: graph) (S : {set G}) : subgraph (induced S) G.
Proof. exact: subgraph_sub. Qed.


(** ** Isomorphim Properties *)

(** We define isomorphims as a record in [Type], with projections to
the bijections on vertices and edges. Making isomorphims computational
objects (rather than formalizing mereley the notion of two graphs
being isomorphic) makes it possible to reason about isomorphisms of of
graphs constructed from disjoint unions and quotients in a
compositional manner *)

Record iso (F G: graph): Type := Iso
  { iso_v:> bij F G;
    iso_e: bij (edge F) (edge G);
    iso_hom: is_hom iso_v iso_e }.

Notation "h '.e'" := (iso_e h) (at level 2, left associativity). 
Existing Instance iso_hom.

Lemma source_iso F G (h: iso F G) e: source (h.e e) = h (source e).
Proof. by rewrite source_hom. Qed.

Lemma target_iso F G (h: iso F G) e: target (h.e e) = h (target e).
Proof. by rewrite target_hom. Qed.

Lemma label_iso F G (h: iso F G) e: label (h.e e) = label e.
Proof. by rewrite label_hom. Qed.

Definition iso_id {G}: iso G G := @Iso _ _ bij_id bij_id (hom_id G). 

Definition iso_sym F G: iso F G -> iso G F.
Proof.
  move => f. 
  apply Iso with (bij_sym f) (bij_sym (iso_e f)) =>/=.
  apply hom_sym, f. 
Defined.

Definition iso_comp F G H: iso F G -> iso G H -> iso F H.
Proof.
  move => f g. 
  apply Iso with (bij_comp f g) (bij_comp (iso_e f) (iso_e g)) =>/=.
  apply hom_comp. apply f. apply g.
Defined.

Instance iso_Equivalence: Equivalence iso.
constructor. exact @iso_id. exact @iso_sym. exact @iso_comp. Defined.

Lemma source_iso' F G (h: iso F G) e: source (h.e^-1 e) = h^-1 (source e).
Proof. apply (source_iso (iso_sym h)). Qed.

Lemma target_iso' F G (h: iso F G) e: target (h.e^-1 e) = h^-1 (target e).
Proof. apply (target_iso (iso_sym h)). Qed.

Lemma label_iso' F G (h: iso F G) e: label (h.e^-1 e) = label e.
Proof. apply (label_iso (iso_sym h)). Qed.

Definition Iso' (F G: graph)
           (fv: F -> G) (fv': G -> F)
           (fe: edge F -> edge G) (fe': edge G -> edge F):
  cancel fv fv' -> cancel fv' fv ->
  cancel fe fe' -> cancel fe' fe ->
  is_hom fv fe -> iso F G.
Proof. move=> fv1 fv2 fe1 fe2 E. exists (Bij fv1 fv2) (Bij fe1 fe2). apply E. Defined.

Lemma iso_two_graph: iso two_graph (union unit_graph unit_graph).
Proof.
  apply Iso' with
      (fun x: bool => if x then inl tt else inr tt)
      (fun x => match x with inl _ => true | _ => false end)
      (vfun)
      (fun x => match x with inl x | inr x => x end).
all: abstract (repeat first [case|split]).
Defined.

Lemma iso_two_swap : iso two_graph two_graph.
apply (@Iso' two_graph two_graph 
             negb negb 
             (fun e => match e with end) (fun e => match e with end)). 
all: abstract by (repeat split; case). 
Defined.

(** ** Specific isomorphisms about union and merge *)

Global Instance union_iso: Proper (iso ==> iso ==> iso) union.
Proof.
  intros F F' f G G' g.
  exists (sum_bij f g) (sum_bij f.e g.e).
  abstract by split; case=>e/=; rewrite ?source_iso ?target_iso ?label_iso.
Defined.

Lemma union_C G H: iso (union G H) (union H G).
Proof. exists bij_sumC bij_sumC. abstract by split; case. Defined.

Lemma union_A F G H: iso (union F (union G H)) (union (union F G) H).
Proof. exists bij_sumA bij_sumA. abstract by split; case=>[|[|]]. Defined.

Section h_merge_nothing'.
 Variables (F: graph) (r: equiv_rel F).
 Hypothesis H: forall x y: F, r x y -> x=y.
 Lemma merge_nothing': iso (merge F r) F.
 Proof.
   exists (quot_id H: bij (merge F r) F) bij_id.
   abstract by split=>e; rewrite /=?quot_idE?H.
 Defined.
End h_merge_nothing'.


Section merge_merge.
  Variables (F: graph) (e: equiv_rel F) (e': equiv_rel (merge F e)).
  Lemma hom_merge_merge: is_hom (quot_quot e': merge _ e' -> merge F _) bij_id.
  Proof. split=> a//; by rewrite /=-equiv_comp_pi. Qed.
  Lemma merge_merge: iso (merge (merge F e) e') (merge F (equiv_comp e')).
  Proof. eexists. eapply hom_merge_merge. Defined.
End merge_merge.


Notation merge_seq G l := (merge G (eqv_clot l)).

Section merge.
  Variables (F G: graph) (h: iso F G) (l: pairs F).
  Definition h_merge: bij (merge_seq F l) (merge_seq G (map_pairs h l)).
    eapply bij_comp. apply (quot_bij h). apply quot_same. apply eqv_clot_iso.
  Defined. 
  Lemma h_mergeE (x: F): h_merge (\pi x) = \pi h x.
  Proof. by rewrite /=quot_bijE quot_sameE. Qed.
  Lemma merge_hom: is_hom h_merge h.e.
  Proof.
    split=>e. 
    - rewrite /= source_iso. symmetry. apply h_mergeE. 
    - rewrite /= target_iso. symmetry. apply h_mergeE. 
    - by rewrite /= label_iso.
  Qed.
  Definition merge_iso: iso (merge_seq F l) (merge_seq G (map_pairs h l)) := Iso merge_hom.
  Lemma merge_isoE (x: F): merge_iso (\pi x) = \pi h x.
  Proof. apply h_mergeE. Qed.
End merge.
Global Opaque h_merge merge_iso.

Section merge_same'.
 Variables (F: graph) (h k: equiv_rel F).
 Hypothesis H: h =2 k. 
 Lemma merge_same'_hom: is_hom (quot_same H: merge _ h -> merge _ k) bij_id.
 Proof. split=>e//; rewrite /=; apply/eqquotP; rewrite -H; apply: piK'. Qed.
 Definition merge_same': iso (merge F h) (merge F k) := Iso merge_same'_hom.
 Lemma merge_same'E (x: F): merge_same' (\pi x) = \pi x.
 Proof. apply quot_sameE. Qed.
End merge_same'.
Global Opaque merge_same'.

Section merge_same.
 Variables (F: graph) (h k: pairs F).
 Hypothesis H: eqv_clot h =2 eqv_clot k.
 Definition merge_same: iso (merge_seq F h) (merge_seq F k) := merge_same' H. 
 Definition merge_sameE (x: F): merge_same (\pi x) = \pi x := merge_same'E H x. 
End merge_same.
Global Opaque merge_same.


Section merge_nothing.
 Variables (F: graph) (h: pairs F).
 Hypothesis H: List.Forall (fun p => p.1 = p.2) h.
 Definition merge_nothing: iso (merge_seq F h) F.
 Proof. apply merge_nothing', eqv_clot_nothing', H. Defined.
 Lemma merge_nothingE (x: F): merge_nothing (\pi x) = x.
 Proof. apply quot_idE. Qed.
End merge_nothing.
Global Opaque merge_nothing.

Section merge_merge_seq.
  Variables (F: graph) (h k: pairs F) (k': pairs (merge_seq F h)).
  Hypothesis kk': k' = map_pairs (pi (eqv_clot h)) k.
  Definition h_merge_merge_seq: bij (merge_seq (merge_seq F h) k') (merge_seq F (h++k)).
  Proof.
    eapply bij_comp. apply quot_quot. apply quot_same.
    rewrite kk'. apply eqv_clot_cat.
  Defined.
  Lemma hom_merge_merge_seq: is_hom h_merge_merge_seq bij_id.
  Proof. split=>e//; by rewrite /=quot_quotE quot_sameE. Qed.
  Definition merge_merge_seq: iso (merge_seq (merge_seq F h) k') (merge_seq F (h++k)) :=
    Iso hom_merge_merge_seq.
  Lemma merge_merge_seqE (x: F): merge_merge_seq (\pi (\pi x)) = \pi x.
  Proof. by rewrite /=quot_quotE quot_sameE. Qed.
End merge_merge_seq.
Global Opaque merge_merge_seq.

Lemma eqv_clot_map_lr (F G : finType) (l : pairs F) x y : 
  eqv_clot (map_pairs inl l) (@inl F G x) (@inr F G y) = false.
Proof. rewrite (@eqv_clot_mapF _) ?inr_codom_inl //. exact: inl_inj. Qed.

Lemma union_equiv_l_eqv_clot (A B: finType) (l: pairs A):
  union_equiv_l B (eqv_clot l) =2 eqv_clot (map_pairs inl l).
Proof.
  rewrite /union_equiv_l/=/union_equiv_l_rel. move => [x|x] [y|y].
  + rewrite (@eqv_clot_map _ _  _ _ _ (@inl A B)) //. exact: inl_inj.
  + by rewrite eqv_clot_map_lr.
  + by rewrite equiv_sym eqv_clot_map_lr. 
  + by rewrite eqv_clot_map_eq ?sum_eqE // inr_codom_inl.
Qed.

Section union_merge_l.
  Variables (F G: graph) (l: pairs F).
  Definition h_union_merge_l: bij (union (merge_seq F l) G) (merge_seq (union F G) (map_pairs unl l)).
  Proof. eapply bij_comp. apply union_quot_l. apply quot_same. apply union_equiv_l_eqv_clot. Defined.
  Lemma hom_union_merge_l: is_hom h_union_merge_l bij_id.
  Proof. by split; move=>[e|e]//=; rewrite ?union_quot_lEl ?union_quot_lEr quot_sameE. Qed.
  Definition union_merge_l: iso (union (merge_seq F l) G) (merge_seq (union F G) (map_pairs unl l)) :=
    Iso hom_union_merge_l.
  Lemma union_merge_lEl (x: F): union_merge_l (inl (\pi x)) = \pi unl x.
  Proof. by rewrite /=union_quot_lEl quot_sameE. Qed.
  Lemma union_merge_lEr (x: G): union_merge_l (unr x) = \pi unr x.
  Proof. by rewrite /=union_quot_lEr quot_sameE. Qed.
End union_merge_l.  
Global Opaque union_merge_l.

Lemma map_map_pairs {A B C} (f: A -> B) (g: B -> C) l: map_pairs g (map_pairs f l) = map_pairs (g \o f) l.
Proof. by rewrite /map_pairs -map_comp. Qed.

Section union_merge_r.
  Variables (F G: graph) (l: pairs G).
  Lemma union_merge_r: iso (union F (merge_seq G l)) (merge_seq (union F G) (map_pairs unr l)).
  Proof.
    eapply iso_comp. apply union_C.
    eapply iso_comp. apply union_merge_l.
    eapply iso_comp. apply (merge_iso (union_C _ _)).
    apply merge_same. abstract by rewrite map_map_pairs. 
  Defined.
  Lemma union_merge_rEr (x: G): union_merge_r (inr (\pi x)) = \pi (unr x).
  Proof.
    (* BUG: the second rewrite hangs if F and x are not given *)
    rewrite /=. rewrite (union_merge_lEl F _ x).
    rewrite (merge_isoE (union_C G F) _ (unl x)).
    by rewrite merge_sameE. 
  Qed.
  Lemma union_merge_rEl (x: F): union_merge_r (unl x) = \pi (unl x).
  Proof.
    rewrite /=. rewrite (union_merge_lEr _ x) .
    rewrite (merge_isoE (union_C G F) _ (unr x)).
    by rewrite merge_sameE. 
  Qed.
End union_merge_r.  
Global Opaque union_merge_r.

Section merge_union_K.
  Variables (F K: graph) (h: pairs (F+K)) (k: K -> F).
  Definition union_K_pairs := map_pairs (fun x => match x with inl x => x | inr x => k x end) h.

  Hypothesis kh: forall x: K, unr x = unl (k x) %[mod (eqv_clot h)].

  Lemma equiv_clot_Kl: union_K_equiv (eqv_clot h) =2 eqv_clot union_K_pairs.
  Proof.
    move=> x y. rewrite /union_K_equiv map_equivE. 
    rewrite !eqv_clotE. set e1 := rel_of_pairs _. set e2 := rel_of_pairs _. 
    pose j := (fun x => match x with inl x => x | inr x => k x end).
    apply/idP/idP. 
    - suff S u v : equiv_of e1 u v -> equiv_of e2 (j u) (j v) by apply: S. 
      apply: equiv_ofE => {u v} [[u|u] [u'|u']] /= H. 
      all: rewrite /e2 /j; apply: sub_equiv_of; apply/mapP. 
      + by exists (unl u,unl u').
      + by exists (unl u,unr u').
      + by exists (unr u,unl u').
      + by exists (unr u,unr u').
    - apply: equiv_ofE => {x y} x x' xx'. 
      have kh' z : equiv_of e1 (unr z) (unl (k z)).
      { rewrite -eqv_clotE. apply/eqquotP. exact: kh. }
      case/mapP : xx' => [[[u|u] [v|v]] H] /= [-> ->] {x x'}.
      + exact: sub_equiv_of.
      + apply: equiv_trans => /=. 2: exact: (kh' v). exact: sub_equiv_of.
      + apply: equiv_trans => /=. rewrite equiv_sym /=. exact: kh'. exact: sub_equiv_of.
      + apply: equiv_trans. 2: exact: kh'. apply: equiv_trans. 
        rewrite equiv_sym. exact: kh'. exact: sub_equiv_of.
  Qed.
  
  Definition h_merge_union_K: bij (merge_seq (union F K) h) (merge_seq F union_K_pairs).
    eapply bij_comp. apply quot_union_K with k. apply kh.
    apply quot_same. apply equiv_clot_Kl. 
  Defined.

  Hypothesis ke: edge K -> False.

  Definition h_merge_union_Ke1 (e: edge (merge_seq (union F K) h)): edge (merge_seq F union_K_pairs) :=
    match e with inl e => e | inr e => match ke e with end end.

  Definition h_merge_union_Ke: bij (edge (merge_seq (union F K) h)) (edge (merge_seq F union_K_pairs)).
    exists h_merge_union_Ke1 inl=>x//. by case x.
  Defined.

  Lemma hom_merge_union_K: is_hom h_merge_union_K h_merge_union_Ke.
  Proof. split; move => [e//=|//]; by rewrite ?quot_union_KEl ?quot_union_KEr quot_sameE. Qed.

  Definition merge_union_K: iso (merge_seq (union F K) h) (merge_seq F union_K_pairs) :=
    Iso hom_merge_union_K.
  Lemma merge_union_KEl (x: F): merge_union_K (\pi (unl x)) = \pi x.
  Proof. by rewrite /=quot_union_KEl quot_sameE. Qed.
  Lemma merge_union_KEr (x: K): merge_union_K (\pi (unr x)) = \pi k x.
  Proof. by rewrite /=quot_union_KEr quot_sameE. Qed.
End merge_union_K.
Global Opaque merge_union_K.




Section BijT.
Variables (T : finType) (P : pred T).
Hypothesis inP : forall x, P x.
Definition subT_bij : bij {x : T | P x} T.
Proof. exists val (fun x => Sub x (inP x)). 
       abstract (case => x Px; exact: val_inj).
       abstract done.
Defined.
End BijT.

Definition setT_bij (T : finType) : bij {x : T | x \in setT} T := 
  Eval hnf in subT_bij (@in_setT T).
Arguments setT_bij [T].

Lemma setT_bij_hom (G : graph) : @is_hom (subgraph_for (@consistentTT G)) G setT_bij setT_bij. 
Proof. by []. Qed.

Definition iso_subgraph_forT (G : graph) : iso (subgraph_for (consistentTT G)) G := 
  Eval hnf in Iso (setT_bij_hom G).


(** ** Merging Subgraphs *)

(** This construction allows transforming a quotient on [G[V1,E1] + G[V2,E2]] 
    into a quotient on [G[V1 :|: V2, E1 :|: E2]], provided the edge sets are
    disjoint and the quotient merges all duplicated verices (i.e., those
    occurring both in [V1] and in [V2]. The underlying function on vertices from 
    [G[V1,E1] + G[V2,E2]] to [G[V1 :|: V2, E1 :|: E2]] simply drops the inl/inr.
    For the converse direction, we inject into [G[V1,E1]] if possible and otherwise 
    into [G[V1,E2]]. Note that this only yields a bijection after quotienting. *)

Section MergeSubgraph.
  Variables (G : graph) (V1 V2 : {set G}) (E1 E2 : {set edge G}) 
            (con1 : consistent V1 E1) (con2 : consistent V2 E2)
            (h : pairs (union (subgraph_for con1) (subgraph_for con2))).

  Lemma consistentU : consistent (V1 :|: V2) (E1 :|: E2).
  Proof using con1 con2. 
    move => e. case/setUP => E. 
    - case: (con1 E) => H1 H2. by rewrite !inE H1 H2.
    - case: (con2 E) => H1 H2. by rewrite !inE H1 H2. 
  Qed.    

  Hypothesis eqvI : forall x (inU : x \in V1) (inV : x \in V2), 
      inl (Sub x inU) = inr (Sub x inV) %[mod eqv_clot h].

  Hypothesis disE : [disjoint E1 & E2].

  Local Notation G1 := (subgraph_for con1).
  Local Notation G2 := (subgraph_for con2).
  Local Notation G12 := (subgraph_for consistentU).

  Definition h' := map_pairs (@union_bij_fwd _ _ _) h.
  Lemma eqv_clot_union_rel : merge_union_rel (eqv_clot h) =2 eqv_clot h'.
  Proof.
    move => x y. rewrite /merge_union_rel /h' map_equivE. apply/idP/idP.
    - have aux z : union_bij_fwd (union_bij_bwd z) = z %[mod eqv_clot (map_pairs (@union_bij_fwd _ _ _) h)].
      { apply/eqquotP. case: union_bij_bwdP => *; apply: eq_equiv; by apply: val_inj. }
      move => H. apply/eqquotP. rewrite -[_ x]aux -[_ y]aux. apply/eqquotP.
      move: H. apply: eqv_clot_map'.
    - rewrite eqv_clotE. apply: equiv_ofE => /= {x y} x y. 
      rewrite /rel_of_pairs/=. case/mapP => /= [[u v]] in_h [-> ->].
      apply/eqquotP. rewrite 2!(union_bij_fwd_can' eqvI). apply/eqquotP.
      exact: eqv_clot_pair.
  Qed.

  Definition merge_subgraph_v : bij (merge_seq (union G1 G2) h) (merge_seq G12 h') :=
    Eval hnf in (bij_comp (merge_union_bij eqvI) (quot_same eqv_clot_union_rel)).

  Definition merge_subgraph_e : bij (edge G1 + edge G2) (edge G12) := 
    union_bij disE.

  Lemma merge_subgraph_hom : is_hom merge_subgraph_v merge_subgraph_e.
  Proof.
    rewrite /merge_subgraph_e /merge_subgraph_v. 
    split; case => x //=.
    all: rewrite merge_unionE quot_sameE. 
    all: congr pi; try exact: val_inj.
  Qed.

  Definition merge_subgraph_iso : iso (merge_seq (union G1 G2) h) (merge_seq G12 h') := 
    Iso merge_subgraph_hom.

End MergeSubgraph.

