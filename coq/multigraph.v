Require Import RelationClasses Setoid Morphisms.

From mathcomp Require Import all_ssreflect.
Require Import finite_quotient preliminaries equiv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 

(** * Directed Multigraphs *)

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

Definition funU {A B C D} (f: A -> B) (g: C -> D) (x: A+C): B+D :=
  match x with inl a => inl (f a) | inr c => inr (g c) end. 

Definition union (G1 G2 : graph) : graph :=
  {| vertex := [finType of G1 + G2];
     edge := [finType of edge G1 + edge G2];
     source := funU (@source G1) (@source G2);
     target := funU (@target G1) (@target G2);
     label e := match e with inl e => label e | inr e => label e end |}.

Definition unl {G H: graph} (x: G): union G H := inl x. 
Definition unr {G H: graph} (x: H): union G H := inr x.

(** ** Homomorphisms *)

Definition h_ty (G1 G2 : graph) := ((vertex G1 -> vertex G2)*(edge G1 -> edge G2))%type.

Definition hom_g G1 G2 (h : h_ty G1 G2) : Prop :=
 ((forall e : edge G1, h.1 (source e) = source (h.2 e))
 *(forall e : edge G1, h.1 (target e) = target (h.2 e))
 *(forall e : edge G1, label (h.2 e) = label e))%type.

Definition injective2 G H (h : h_ty G H) := (injective h.1 * injective h.2)%type.
Definition surjective2 G H (h : h_ty G H) := (surjective h.1 * surjective h.2)%type.
Definition bijective2 G H (h : h_ty G H) := bijective h.1 /\ bijective h.2.

Lemma hom_id {G: graph}: @hom_g G G (id,id).
Proof. by []. Qed.

Lemma hom_comp (F G H: graph) f g:
  @hom_g F G f -> @hom_g G H g -> @hom_g F H (g.1 \o f.1,g.2 \o f.2).
Proof.
  intros Hf Hg. (repeat split; intro); last rewrite /=Hg Hf//; rewrite /=Hf Hg//.
Qed.

(** ** Quotient Graphs *)

Definition merge_def (G : graph) (r : equiv_rel G) :=
  {| vertex := [finType of {eq_quot r}];
     edge := (edge G);
     source e := \pi_{eq_quot r} (source e);
     target e := \pi_{eq_quot r} (target e);
     label e := label e |}.

Arguments merge_def : clear implicits.

Notation merge G r := (merge_def G [equiv_rel of r]).

Definition hom_of (G : graph) (e : equiv_rel G) : h_ty G (merge G e) := 
  (fun x : G => \pi x, id).

Lemma hom_of_surj (G : graph) (e : equiv_rel G) : 
  surjective2 (hom_of e).
Proof. split; [exact: emb_surj|exact: id_surj]. Qed.

(** ** Subgraphs and Induced Subgraphs *)

Definition subgraph (H G : graph) := 
  exists2 h : h_ty H G, hom_g h & injective2 h.

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
  Proof. exists (val,val); split => //=; exact: val_inj. Qed.
End Subgraphs.

Definition induced_proof (G: graph) (S : {set G}) : consistent S (edge_set S).
Proof. move => e. by rewrite inE => /andP. Qed.

Definition induced (G: graph) (S : {set G}) := 
  subgraph_for (@induced_proof G S).

Lemma induced_sub (G: graph) (S : {set G}) : subgraph (induced S) G.
Proof. exact: subgraph_sub. Qed.


(** ** Isomorphim Properties *)


Local Open Scope quotient_scope.

Definition iso_g (F G : graph) (h : h_ty F G) := hom_g h /\ bijective2 h.

Lemma iso_id {G: graph}: @iso_g G G (id,id).
Proof. split. apply hom_id. split; apply id_bij. Qed.

Lemma iso_comp (F G H: graph) f g:
  @iso_g F G f -> @iso_g G H g -> @iso_g F H (g.1 \o f.1,g.2 \o f.2).
Proof.
  intros Hf Hg. split.
  apply hom_comp; [apply Hf | apply Hg].
  split; (apply bij_comp; [apply Hg | apply Hf]). 
Qed.

Definition iso (F G: graph) := exists h: h_ty F G, iso_g h. 

Instance iso_Equivalence: Equivalence iso.
Proof.
  constructor.
  - intro G. exists (id,id). apply iso_id. 
  - intros F G [h [H [[g1 H1 G1] [g2 H2 G2]]]].
    exists (g1,g2). (repeat split)=> /= [e|e|e||].
    by rewrite -{1}(G2 e) -H H1.
    by rewrite -{1}(G2 e) -H H1.
    by rewrite -H G2.
    by eexists. 
    by eexists. 
  - intros F G H [f Hf] [g Hg].
    eexists. apply (iso_comp Hf Hg).
Qed.

Lemma iso_two_graph:
  @iso_g two_graph (union unit_graph unit_graph)
         ((fun x: bool => if x then unl (tt: unit_graph) else unr (tt: unit_graph)),
          (fun x: void => match x with end)).
Proof.
  split. split. split; intros []. intros []. 
  split.
    by exists (fun x => match x with inl _ => true | _ => false end); [intros [|] | intros [[]|[]]].
    by exists (fun x => match x with inl x | inr x => x end); [intros [] | intros [|]].
Qed.

(** ** Specific isomorphisms about union and merge *)

Lemma bij_funU {A B C D} (f: A -> B) (g: C -> D):
  bijective f -> bijective g -> bijective (funU f g).
Proof. intros [f' F F'] [g' G G']. by exists (funU f' g'); intros [?|?]; simpl; f_equal. Qed.

Section h_union.
 Variables (F F': graph) (f: h_ty F F') (G G': graph) (g: h_ty G G').
 Definition h_union: h_ty (union F G) (union F' G') := (funU f.1 g.1,funU f.2 g.2).
 Lemma hom_union: hom_g f -> hom_g g -> hom_g h_union.
 Proof. intros Hf Hg. (repeat split); intros [?|?]; rewrite /= ?Hf ?Hg //. Qed.
 Lemma iso_union: iso_g f -> iso_g g -> iso_g h_union.
 Proof.
   intros H H'. split. apply hom_union. apply H. apply H'.
   split; (apply bij_funU; [apply H|apply H']).
 Qed.
End h_union.
Instance union_iso: Proper (iso ==> iso ==> iso) union.
Proof. intros F F' [f Hf] G G' [g Hg]. eexists. apply iso_union; eassumption. Qed.


Definition sumC {A B} (x: A + B): B + A := match x with inl x => inr x | inr x => inl x end.
Lemma bij_sumC A B: bijective (@sumC A B).
Proof. by exists sumC; intros [|]. Qed.

Definition h_union_C (G H: graph): h_ty (union G H) (union H G) := (sumC,sumC).

Lemma hom_union_C G H: hom_g (h_union_C G H).
Proof. by split; first split; intros [e|e]. Qed.

Lemma bij_union_C G H: bijective2 (h_union_C G H).
Proof. by split; apply bij_sumC. Qed.

Lemma iso_union_C G H: iso_g (h_union_C G H).
Proof. split. apply hom_union_C. apply bij_union_C. Qed.

Lemma union_C G H: iso (union G H) (union H G).
Proof. exists (h_union_C G H). apply iso_union_C. Qed.



Definition sumA {A B C} (x: A + (B + C)): (A + B) + C :=
  match x with inl x => inl (inl x) | inr (inl x) => inl (inr x) | inr (inr x) => inr x end.
Definition sumA' {A B C} (x: (A + B) + C): A + (B + C) :=
  match x with inr x => inr (inr x) | inl (inr x) => inr (inl x) | inl (inl x) => inl x end.
Lemma bij_sumA A B C: bijective (@sumA A B C).
Proof. by exists sumA'; [intros [|[|]] | intros [[|]|]]. Qed.
Lemma bij_sumA' A B C: bijective (@sumA' A B C).
Proof. by exists sumA; [intros [[|]|] | intros [|[|]]]. Qed.

Definition h_union_A (F G H: graph): h_ty (union F (union G H)) (union (union F G) H) := (sumA,sumA).

Lemma hom_union_A F G H: hom_g (h_union_A F G H).
Proof. by split; first split; intros [|[|]]. Qed.

Lemma bij_union_A F G H: bijective2 (h_union_A F G H).
Proof. by split; apply bij_sumA. Qed.

Lemma iso_union_A F G H: iso_g (h_union_A F G H).
Proof. split. apply hom_union_A. apply bij_union_A. Qed.

Lemma union_A F G H: iso (union F (union G H)) (union (union F G) H).
Proof. exists (h_union_A F G H). apply iso_union_A. Qed.


Definition h_union_A' (F G H: graph): h_ty (union (union F G) H) (union F (union G H)) := (sumA',sumA').

Lemma hom_union_A' F G H: hom_g (h_union_A' F G H).
Proof. by split; first split; intros [[|]|]. Qed.

Lemma bij_union_A' F G H: bijective2 (h_union_A' F G H).
Proof. by split; apply bij_sumA'. Qed.

Lemma iso_union_A' F G H: iso_g (h_union_A' F G H).
Proof. split. apply hom_union_A'. apply bij_union_A'. Qed.


Section h_merge_nothing'.
 Variables (F: graph) (r: equiv_rel F).
 Hypothesis H: forall x: F, generic_quotient.repr (\pi_{eq_quot r} x) = x.
 Definition h_merge_nothing': h_ty (merge_def F r) F := (fun x => generic_quotient.repr x, id).
 Lemma merge_nothing'_hom: hom_g h_merge_nothing'.
 Proof. by repeat split; intro e; simpl; rewrite H. Qed.
 Lemma merge_nothing'_iso: iso_g h_merge_nothing'.
 Proof.
   split. apply merge_nothing'_hom. split. 2: apply id_bij.
   exists (fun x => \pi_{eq_quot r} x); intro; simpl. apply reprK. apply H. 
 Qed.
End h_merge_nothing'.


Section merge_merge.
  Variables (F: graph) (e: equiv_rel F) (e': equiv_rel (merge_def F e)).
  Definition h_merge_merge1 (x: merge_def (merge_def F e) e'): merge_def F (equiv_comp_rel e') :=
    \pie (repr (repr x)).
  Definition h_merge_merge: h_ty _ _ := (h_merge_merge1,id).
  Lemma hom_merge_merge: hom_g h_merge_merge.
  Proof.
    repeat split. (* TODO: intro lemma abstracting over source/target *)
    - move => a. rewrite /=/h_merge_merge1. by rewrite -equiv_comp_pi.
    - move => a. rewrite /=/h_merge_merge1. by rewrite -equiv_comp_pi.
  Qed.
  Lemma bij_merge_merge: bijective2 h_merge_merge.
  Proof.
    split; last apply id_bij. 
    pose h (x : merge_def F (equiv_comp_rel e')) : merge_def (merge_def F e) e' :=
      \pie (\pie (repr x)).
    exists h => x. 
    + rewrite /=/h_merge_merge1/h. case: piP  => /= y /eqquotP /= Hy. 
      rewrite -[x]reprK /=. apply/eqquotP. by rewrite reprK equiv_sym in Hy. (* Lemma *)
    + rewrite /=/h_merge_merge1/h. by rewrite -equiv_comp_pi reprK.
  Qed.
  Lemma iso_merge_merge: iso_g h_merge_merge.
  Proof. split. apply hom_merge_merge. apply bij_merge_merge. Qed.
  Lemma merge_merge: iso (merge_def (merge_def F e) e') (merge_def F (equiv_comp_rel e')).
  Proof. eexists. apply iso_merge_merge. Qed.
End merge_merge.

Definition merge_seq (G: graph) l := merge_def G (eqv_clot l).
Arguments merge_seq G l: clear implicits. 

Definition pi (G: graph) (h: pairs G) (x: G): merge_seq G h := \pie x.
Definition repr (G: graph) (h: pairs G) (x: merge_seq G h): G := repr x.
Notation "\pis x"  := (pi _ x) (at level 36).

Lemma reprsK (G : graph) (h : pairs G) : cancel (@repr _ h) (@pi _ h).
Proof. exact: reprK. Qed.

Lemma eqv_clot_subset (T : finType) (l1 l2 : pairs T) : 
  {subset l1 <= l2} -> subrel (eqv_clot l1) (eqv_clot l2).
Proof. 
  move => H x y. rewrite !eqv_clotE. apply: equiv_of_transfer => u v.
  move => R. apply: sub_equiv_of. exact: rel_of_pairs_mono R.
Qed.       
Arguments eqv_clot_subset [T] l1 [l2].

Lemma subset_catL (T : eqType) (h k : seq T) : {subset h <= h ++ k}.
Proof. move => x H. by rewrite mem_cat H. Qed.
Lemma subset_catR (T : eqType) (h k : seq T) : {subset k <= h ++ k}.
Proof. move => x H. by rewrite mem_cat H orbT. Qed.
Hint Resolve subset_catL subset_catR.

(* this should be eqv_clot_map, the other lemma should use the _inj suffix *)
Lemma eqv_clot_map' (aT rT : finType) (f : aT -> rT) (l : pairs aT) x y : 
  eqv_clot l x y -> eqv_clot (map_pairs f l) (f x) (f y).
Proof.
  rewrite !eqv_clotE /=. apply: equiv_of_transfer => {x y} x y H.
  apply: sub_equiv_of. by apply/mapP; exists (x,y).
Qed.

Section h_merge.
  Variables (F G: graph) (h: h_ty F G) (l: pairs F).
  Definition h_merge: h_ty (merge_seq F l) (merge_seq G (map_pairs h.1 l)) := 
    (fun x => \pis h.1 (repr x), h.2).
  Lemma h_mergeE (x: F): h_merge.1 (\pis x) = \pis h.1 x.
  Proof.
    symmetry. apply/eqquotP. exact: eqv_clot_map' (eq_piK _ _).
  Qed.
  
  Lemma merge_hom: hom_g h -> hom_g h_merge.
  Proof.
    move => hom_h. repeat split.
    - move => e. symmetry. rewrite /= -hom_h. apply/eqquotP. 
      exact: eqv_clot_map' (eq_piK _ _). 
    - move => e. symmetry. rewrite /= -hom_h. apply/eqquotP. 
      exact: eqv_clot_map' (eq_piK _ _). 
    - move => e. by rewrite /= -hom_h.
  Qed.

  Lemma merge_iso: iso_g h -> iso_g h_merge.
  Proof.
    case => hom_h [[g1 C1 C2] bij_h2].
    split => //; first exact: merge_hom. split => //.
    have L : l = map_pairs g1 (map_pairs h.1 l).
    { rewrite /map_pairs -map_comp map_id_in // => x /= _. 
      by rewrite !C1 -surjective_pairing. }
    pose g (x : (merge_seq G (map_pairs h.1 l))) : (merge_seq F l) := 
      \pis g1 (repr x).
    exists g => x. 
    - rewrite /g/=. rewrite -{2}[x]reprsK. apply/eqquotP. set y := repr x. 
      rewrite -[y]C1 {1}L. apply: eqv_clot_map'. rewrite C1 equiv_sym. exact: eq_piK.
    - rewrite /g/=. rewrite -{2}[x]reprsK. apply/eqquotP. set y := repr x. 
      rewrite -[y]C2. apply: eqv_clot_map'. rewrite C2 equiv_sym. exact: eq_piK.
  Qed.
End h_merge.

Section h_merge_same.
 Variables (F: graph) (h k: pairs F).
 Hypothesis H: eqv_clot h =2 eqv_clot k. 
 Definition h_merge_same: h_ty (merge_seq F h) (merge_seq F k) := (fun x => \pis (repr x), id).
 Lemma h_merge_sameE (x: F): h_merge_same.1 (\pis x) = \pis x.
 Proof. rewrite /=. apply/eqquotP. rewrite -H equiv_sym. exact: eq_piK. Qed.

 Lemma merge_same_hom: hom_g h_merge_same.
 Proof.
   repeat split.
   - move => e. rewrite /=. apply/eqquotP. rewrite -H equiv_sym. exact: eq_piK. 
   - move => e. rewrite /=. apply/eqquotP. rewrite -H equiv_sym. exact: eq_piK. 
 Qed.

 Lemma merge_same_iso: iso_g h_merge_same.
 Proof.
   split. apply merge_same_hom. split. 2: apply id_bij.
   exists (fun x => \pis (repr x)) => x /=.
   - rewrite -{2}[x]reprsK. apply/eqquotP. rewrite H equiv_sym. exact: eq_piK. 
   - rewrite -{2}[x]reprsK. apply/eqquotP. rewrite -H equiv_sym. exact: eq_piK. 
 Qed.

End h_merge_same.

Lemma eqv_clot_noting (T : finType) (h : pairs T) :
  List.Forall (fun p => p.1 = p.2) h -> eqv_clot h =2 eq_op.
Proof.
  move => H x y. rewrite eqv_clotE /=.
Admitted.

Section h_merge_nothing.
 Variables (F: graph) (h: pairs F).
 Hypothesis H: List.Forall (fun p => p.1 = p.2) h.
 Definition h_merge_nothing: h_ty (merge_seq F h) F := (fun x => repr x, id).
 Lemma h_merge_nothingE (x: F): h_merge_nothing.1 (\pis x) = x.
 Proof. 
   rewrite /=/repr. case: piP => y /= /eqquotP. 
   by rewrite eqv_clot_noting // => /eqP->.
 Qed.

 Lemma merge_nothing_hom: hom_g h_merge_nothing.
 Proof. apply merge_nothing'_hom. apply h_merge_nothingE. Qed. 
 Lemma merge_nothing_iso: iso_g h_merge_nothing.
 Proof. apply merge_nothing'_iso. apply h_merge_nothingE. Qed. 
End h_merge_nothing.




Section merge_merge_seq.
  Variables (F: graph) (h k: pairs F) (k': pairs (merge_seq F h)).
  Definition h_merge_merge_seq1 (x: merge_seq (merge_seq F h) k'): merge_seq F (h++k) :=
    \pis (repr (repr x)).
  Definition h_merge_merge_seq: h_ty _ _ := (h_merge_merge_seq1,id).
  (* ideally: derive properties from [merge_merge] *)
  Hypothesis kk': k' = map_pairs (pi h) k.
  Lemma eqv_clot_cat: eqv_clot (h++k) =2 equiv_comp_rel (eqv_clot k').
  Proof.
    move => x y. rewrite /equiv_comp_rel/equiv_comp/= {}kk' !eqv_clotE /=. 
    set e1 := rel_of_pairs _. set e2 := rel_of_pairs _. apply/idP/idP. 
    - apply: equiv_of_transfer => {x y} u v. 
      rewrite /e1/rel_of_pairs/= mem_cat. case/orP => H.
      + apply: eq_equiv. apply/eqquotP. rewrite eqv_clotE. exact: sub_equiv_of.
      + apply: sub_equiv_of. apply/mapP. by exists (u,v).
    - suff S (u v : {eq_quot (eqv_clot h)}):
        equiv_of e2 u v -> equiv_of e1 (repr u) (repr v).
      { move/S => H.  
        apply: equiv_trans (equiv_trans _ _). 2: exact: H.
        rewrite /= -eqv_clotE. exact: (eqv_clot_subset h) (eq_piK _ _). 
        rewrite /= -eqv_clotE equiv_sym. exact: (eqv_clot_subset h) (eq_piK _ _). }
      apply: equiv_of_transfer => {u v} u v /mapP [[u0 v0] H0] [-> ->].
      apply: equiv_trans (equiv_trans _ _). 
      2:{ rewrite /= -eqv_clotE. apply: (eqv_clot_subset k) _. done. 
          rewrite eqv_clotE. apply: sub_equiv_of. exact: H0. }
      rewrite equiv_sym. all: rewrite /= -eqv_clotE; exact: (eqv_clot_subset h) (eq_piK _ _).
  Qed.
  
  Lemma h_merge_merge_seqE (x: F): h_merge_merge_seq1 (\pis (\pis x)) = \pis x.
  Proof. 
    rewrite /h_merge_merge_seq1/=. apply: mod_exchange eqv_clot_cat _.
    apply/esym. exact: equiv_comp_pi.
  Qed.

  Lemma hom_merge_merge_seq: hom_g h_merge_merge_seq.
  Proof.
    repeat split. 
    - move => e. rewrite /=/h_merge_merge_seq1. apply: mod_exchange eqv_clot_cat _.
      by rewrite -equiv_comp_pi.
    - move => e. rewrite /=/h_merge_merge_seq1. apply: mod_exchange eqv_clot_cat _.
      by rewrite -equiv_comp_pi.
  Qed.

  Lemma bij_merge_merge_seq: bijective2 h_merge_merge_seq.
  Proof.
    split; last apply id_bij. 
    pose f (x : merge_seq F (h++k)) : merge_seq (merge_seq F h) k' :=
      \pis (\pis (repr x)).
    exists f => x.
    + rewrite /=/h_merge_merge_seq1/f/pi/repr. case: piP  => /= y /eqquotP /= Hy. 
      rewrite eqv_clot_cat /= reprK in Hy. 
      rewrite -[x]reprK /=. apply/eqquotP. by rewrite equiv_sym.
    + rewrite /=/h_merge_merge_seq1/f. 
      rewrite -{2}[x]reprK /=. apply: mod_exchange eqv_clot_cat _.
      by rewrite -equiv_comp_pi.
  Qed.

  Lemma iso_merge_merge_seq: iso_g h_merge_merge_seq.
  Proof. split. apply hom_merge_merge_seq. apply bij_merge_merge_seq. Qed.
  Lemma merge_merge_seq: iso (merge_seq (merge_seq F h) k') (merge_seq F (h++k)).
  Proof. eexists. apply iso_merge_merge_seq. Qed.
End merge_merge_seq.

Lemma eqv_clot_map_lr (F G : graph) (l : pairs F) x y : 
  eqv_clot (map_pairs inl l) (unl x : union F G) (unr y) = false.
Proof. rewrite (@eqv_clot_mapF (union F G)) ?inr_codom_inl //. exact: inl_inj. Qed.

Section union_merge_l.
  Variables (F G: graph) (l: pairs F).
  Definition h_union_merge_l1 (x: union (merge_seq F l) G): merge_seq (union F G) (map_pairs unl l) :=
    \pis (match x with inl x => unl (repr x) | inr x => unr x end).
  Definition h_union_merge_l: h_ty _ _ := (h_union_merge_l1,id).
  Lemma h_union_merge_lEl (x: F): h_union_merge_l1 (unl (\pis x)) = \pis (unl x).
  Proof. 
    rewrite /h_union_merge_l1/=. apply/eqmodP. 
    rewrite (@eqv_clot_map (union F G)) 1?equiv_sym. exact: eq_piK. exact: inl_inj. 
  Qed.

  Lemma h_union_merge_lEr (x: G): h_union_merge_l1 (unr x) = \pis (unr x).
  Proof. by []. Qed.

  Lemma hom_union_merge_l: hom_g h_union_merge_l.
  Proof.
    repeat split. 
    - move => [e|e]. 
      + by rewrite /= h_union_merge_lEl.
      + by rewrite /= h_union_merge_lEr.
    - move => [e|e]. 
      + by rewrite /= h_union_merge_lEl.
      + by rewrite /= h_union_merge_lEr.
  Qed.

  Local Notation g := h_union_merge_l1.

  Lemma bij_union_merge_l: bijective2 h_union_merge_l.
  Proof.
    split; last apply id_bij. 
    pose h (x : merge_seq (union F G) (map_pairs unl l)) : union (merge_seq F l) G :=
      match repr x with inl x => unl (\pis x) | inr x => unr x end.
    exists h => [x|x].
    - rewrite /=. 
      case: x => [x'|x']. rewrite /h.
      + suff [z Z1 Z2] : exists2 z : F, repr (g (unl x')) = inl z & \pis z = x'.
        { by rewrite Z1 Z2. }
        rewrite /g/=. case E : (repr _) => [z|z].
        * exists z => //. move/(congr1 (@pi (union F G) (map_pairs inl l))) : E.
          rewrite reprsK. move/eqquotP. rewrite eqv_clot_map => [E|]; last exact: inl_inj.
          rewrite -[x']reprsK. apply:esym. exact/eqquotP.
        * move/(congr1 (@pi (union F G) (map_pairs inl l))) : E.
          rewrite reprsK. move/eqquotP. by rewrite eqv_clot_map_lr.
      + rewrite h_union_merge_lEr /h /repr. case: piP => /= [[y|y]].
        * move/eqquotP. by rewrite equiv_sym eqv_clot_map_lr.
        * move/eqquotP. rewrite (@eqv_clot_map_eq (union F G)) ?inr_codom_inl //.
          by move/eqP=>[->].
    - rewrite /=/h/g. case E: (repr x) => [y|y] /=. 
      + rewrite -[x]reprK -/(repr _)/= {}E. apply/eqquotP. 
        rewrite (@eqv_clot_map (union F G)) 1?equiv_sym. exact: eq_piK. exact: inl_inj.
      + by rewrite /unr -E reprsK.
  Qed.
  Lemma iso_union_merge_l: iso_g h_union_merge_l.
  Proof. split. apply hom_union_merge_l. apply bij_union_merge_l. Qed.
  Lemma union_merge_l: iso (union (merge_seq F l) G) (merge_seq (union F G) (map_pairs inl l)).
  Proof. eexists. apply iso_union_merge_l. Qed.
End union_merge_l.  

Section union_merge_r.
  Variables (F G: graph) (l: pairs G).
  Definition h_union_merge_r1 (x: union F (merge_seq G l)): merge_seq (union F G) (map_pairs unr l) :=
    \pis (match x with inl x => unl x | inr x => unr (repr x) end).
  Definition h_union_merge_r: h_ty _ _ := (h_union_merge_r1,id).
  (* ideally: derive properties from [union_merge_l] and [union_C] *)
  Lemma h_union_merge_rEl (x: F): h_union_merge_r1 (unl x) = \pis (unl x).
  Admitted.
  Lemma h_union_merge_rEr (x: G): h_union_merge_r1 (unr (\pis x)) = \pis (unr x).
  Admitted.
  Lemma hom_union_merge_r: hom_g h_union_merge_r.
  Admitted.
  Lemma bij_union_merge_r: bijective2 h_union_merge_r.
  Proof.
    split; last apply id_bij. 
  Admitted.
  Lemma iso_union_merge_r: iso_g h_union_merge_r.
  Proof. split. apply hom_union_merge_r. apply bij_union_merge_r. Qed.
  Lemma union_merge_r: iso (union F (merge_seq G l)) (merge_seq (union F G) (map_pairs unr l)).
  Proof. eexists. apply iso_union_merge_r. Qed.
End union_merge_r.  

Section merge_union_K.
  Variables (F K: graph) (h: pairs (F+K)) (k: K -> F).
  Definition union_K_pairs := map_pairs (fun x => match x with inl x => x | inr x => k x end) h.
  Definition h_merge_union_K1 (x: merge_seq (union F K) h): merge_seq F union_K_pairs :=
    \pis (match repr x with inl x => x | inr x => k x end).

  Local Notation f := h_merge_union_K1.

  Hypothesis kh: forall x: K, unr x = unl (k x) %[mod_eq (eqv_clot h)].

  (* TOTHINK: can this be factorized to use a general lemma about [equiv_of],
  similar to [equiv_of_ff] ?*)
  Lemma equiv_clot_Kl (x y : F) :
    (eqv_clot h) (unl x) (inl y) = (eqv_clot union_K_pairs) x y.
  Proof.
    rewrite !eqv_clotE. set e1 := rel_of_pairs _. set e2 := rel_of_pairs _. 
    pose j := (fun x => match x with inl x => x | inr x => k x end).
    apply/idP/idP. 
    suff S u v : equiv_of e1 u v -> equiv_of e2 (j u) (j v) by apply: S. (* abstract? *)
    - case/connectP => p. elim: p u => /= [|u' p IH] u.
      + move => _ ->. done.
      + case/andP => uu' pth_p lst_p. apply: equiv_trans (IH _ pth_p lst_p) => /=.
        wlog uu' : u u' {uu' pth_p lst_p} / e1 u u'. 
        { case/orP : uu' => uu'. 2:rewrite equiv_sym. all: by apply. }
        destruct u as [u|u]; destruct u' as [u'|u']. 
        all: rewrite /j; apply: sub_equiv_of; apply/mapP.
        * by exists (inl u,inl u').
        * by exists (inl u,inr u').
        * by exists (inr u,inl u').
        * by exists (inr u,inr u').
    - case/connectP => p. elim: p x => /= [|x' p IH] x.
      + by move => _ ->. 
      + case/andP => xx' pth_p lst_p. apply: equiv_trans (IH _ pth_p lst_p) => /=.
        wlog xx' : x x' {xx' pth_p lst_p} / e2 x x'. 
        { case/orP : xx' => xx'. 2:rewrite equiv_sym. all: by apply. }
        have kh' z : equiv_of e1 (unr z) (unl (k z)).
        { rewrite -eqv_clotE. apply/eqquotP. exact: kh. }
        case/mapP : xx' => [[[u|u] [v|v]] H] /= [-> ->] {x x'}.
        * exact: sub_equiv_of.
        * apply: equiv_trans => /=. 2: exact: (kh' v). exact: sub_equiv_of.
        * apply: equiv_trans => /=. rewrite equiv_sym /=. exact: kh'. exact: sub_equiv_of.
        * apply: equiv_trans. 2: exact: kh'. apply: equiv_trans. 
          rewrite equiv_sym. exact: kh'. exact: sub_equiv_of.
  Qed.

  Lemma h_merge_union_KEl (x: F): h_merge_union_K1 (\pis (unl x)) = \pis x.
  Proof. 
    rewrite /f. case E : (repr _) => [y|y].
    - move/(congr1 (@pi (union F K) h)) : E. rewrite reprsK => /eqquotP E.
      apply/eqquotP. by rewrite equiv_sym -equiv_clot_Kl.
    - move/(congr1 (@pi (union F K) h)) : E. rewrite reprsK -/(unr _).
      rewrite /pi kh /=. move/eqmodP. rewrite equiv_clot_Kl equiv_sym => H.
      exact/eqquotP.
  Qed.

  Lemma h_merge_union_KEr (x: K): h_merge_union_K1 (\pis (unr x)) = \pis (k x).
  Proof. 
    rewrite /f. case E : (repr _) => [y|y].
    - move/(congr1 (@pi (union F K) h)) : E. rewrite reprsK /pi kh. 
      move/eqquotP. rewrite equiv_clot_Kl equiv_sym => ?. exact/eqquotP.
    - move/(congr1 (@pi (union F K) h)) : E. rewrite reprsK /pi !kh.
      move/eqquotP. rewrite equiv_clot_Kl equiv_sym => ?. exact/eqquotP.
  Qed.

  Hypothesis ke: edge K -> False.
  Definition h_merge_union_K2 (e: edge (merge_seq (union F K) h)): edge (merge_seq F union_K_pairs) :=
    match e with inl e => e | inr e => match ke e with end end.
  Definition h_merge_union_K: h_ty _ _ := (h_merge_union_K1,h_merge_union_K2).
  Lemma hom_merge_union_K: hom_g h_merge_union_K.
  Proof.
    repeat split; move => [e//=|//]; by rewrite h_merge_union_KEl. 
  Qed.

  Lemma bij_merge_union_K: bijective2 h_merge_union_K.
  Proof.
    split; last by exists inl =>//; move =>[|]//=. 
    pose g (x : merge_seq F union_K_pairs) : merge_seq (union F K) h :=
      \pis (unl (repr x)).
    exists g => x.
    - rewrite /g/=. rewrite -[x]reprsK. case E : (repr x) => [y|y].
      + rewrite h_merge_union_KEl. apply/eqquotP. rewrite equiv_clot_Kl equiv_sym. exact: eq_piK.
      + rewrite h_merge_union_KEr. rewrite /pi kh. symmetry. 
        apply/eqquotP. rewrite equiv_clot_Kl. exact: eq_piK.
    - rewrite /g/=. by rewrite h_merge_union_KEl reprsK.
  Qed.
  Lemma iso_merge_union_K: iso_g h_merge_union_K.
  Proof. split. apply hom_merge_union_K. apply bij_merge_union_K. Qed.
  Lemma merge_union_K: iso (merge_seq (union F K) h) (merge_seq F union_K_pairs).
  Proof. eexists. apply iso_merge_union_K. Qed.
End merge_union_K.

