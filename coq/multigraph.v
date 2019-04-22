Require Import Setoid CMorphisms.
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

(*
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
*)
  
(** ** Quotient Graphs *)

Definition merge_def (G : graph) (r : equiv_rel G) :=
  {| vertex := [finType of {eq_quot r}];
     edge := (edge G);
     source e := \pi_{eq_quot r} (source e);
     target e := \pi_{eq_quot r} (target e);
     label e := label e |}.

Arguments merge_def : clear implicits.

Notation merge G r := (merge_def G [equiv_rel of r]).

(*
Definition hom_of (G : graph) (e : equiv_rel G) : h_ty G (merge G e) := 
  (fun x : G => \pi x, id).

Lemma hom_of_surj (G : graph) (e : equiv_rel G) : 
  surjective2 (hom_of e).
Proof. split; [exact: emb_surj|exact: id_surj]. Qed.
*)
                                                  
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

Definition induced_proof (G: graph) (S : {set G}) : consistent S (edge_set S).
Proof. move => e. by rewrite inE => /andP. Qed.

Definition induced (G: graph) (S : {set G}) := 
  subgraph_for (@induced_proof G S).

Lemma induced_sub (G: graph) (S : {set G}) : subgraph (induced S) G.
Proof. exact: subgraph_sub. Qed.


(** ** Isomorphim Properties *)

Local Open Scope quotient_scope.

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

Lemma hom_gI (G1 G2: graph) (hv: G1 -> G2) (he: edge G1 -> edge G2) :
  (forall e, [/\ hv (source e) = source (he e),
              hv (target e) = target (he e) &
              label (he e) = label e]) -> is_hom hv he.
Proof. move=>H. split=> e; by case: (H e). Qed.

Lemma iso_two_graph: iso two_graph (union unit_graph unit_graph).
Proof.
  apply Iso' with
      (fun x: bool => if x then unl (tt: unit_graph) else unr (tt: unit_graph))
      (fun x => match x with inl _ => true | _ => false end)
      (vfun)
      (fun x => match x with inl x | inr x => x end).
  abstract by intros [|].
  abstract by intros [[]|[]].
  abstract by intros [].
  abstract by intros [[]|[]].
  abstract by split; intros []. 
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
 Hypothesis H: forall x: F, generic_quotient.repr (\pi_{eq_quot r} x) = x.
 Definition h_merge_nothing': bij (merge_def F r) F.
   exists (fun x => generic_quotient.repr x) (fun x => \pi_{eq_quot r} x).
   apply reprK. apply: H.
 Defined.
 Lemma merge_nothing': iso (merge_def F r) F.
 Proof.
   exists h_merge_nothing' bij_id.
   abstract by split=>e; rewrite /=?H.
 Defined.
End h_merge_nothing'.


Section merge_merge.
  Variables (F: graph) (e: equiv_rel F) (e': equiv_rel (merge_def F e)).
  Definition h_merge_merge: bij (merge_def (merge_def F e) e') (merge_def F (equiv_comp_rel e')).
    exists (fun x => \pie (repr (repr x))) (fun x => \pie (\pie (repr x))) => x.
    (* TODO: abstract the two proofs below *)
    + rewrite /=. case: piP  => /= y /eqquotP /= Hy. 
      rewrite -[x]reprK /=. apply/eqquotP. by rewrite reprK equiv_sym in Hy. (* Lemma *)
    + rewrite /=. by rewrite -equiv_comp_pi reprK.
  Defined.
  Lemma hom_merge_merge: is_hom h_merge_merge id.
  Proof. split=> a//; by rewrite /=-equiv_comp_pi. Qed.
  Lemma merge_merge: iso (merge_def (merge_def F e) e') (merge_def F (equiv_comp_rel e')).
  Proof. exists h_merge_merge bij_id. apply hom_merge_merge. Defined.
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
  Variables (F G: graph) (h: iso F G) (l: pairs F).
  Definition h_merge: bij (merge_seq F l) (merge_seq G (map_pairs h l)).
    exists (fun x => \pis h (repr x)) (fun x => \pis h^-1 (repr x))=> x.
    (* TODO: abstract proofs *)
    - have L : l = map_pairs h^-1 (map_pairs h l).
      { rewrite /map_pairs -map_comp map_id_in // => y /= _. 
          by rewrite !bijK -surjective_pairing. }
      rewrite /=. rewrite -{2}[x]reprsK. apply/eqquotP. set y := repr x. 
      rewrite -(bijK h y) {1}L. apply: eqv_clot_map'. rewrite bijK equiv_sym. exact: eq_piK.
    - rewrite /=. rewrite -{2}[x]reprsK. apply/eqquotP. set y := repr x. 
      rewrite -(bijK' h y). apply: eqv_clot_map'. rewrite bijK' equiv_sym. exact: eq_piK.
  Defined.
  Lemma h_mergeE (x: F): h_merge (\pis x) = \pis h x.
  Proof. symmetry. apply/eqquotP. apply eqv_clot_map', eq_piK. Qed.
  Lemma merge_hom: is_hom h_merge h.e.
  Proof.
    split=>e. 
    - rewrite /= source_iso. symmetry. apply h_mergeE. 
    - rewrite /= target_iso. symmetry. apply h_mergeE. 
    - by rewrite /= label_iso.
  Qed.
  Definition merge_iso: iso (merge_seq F l) (merge_seq G (map_pairs h l)) := Iso merge_hom.
End h_merge.
Global Opaque h_merge.

Section h_merge_same'.
 Variables (F: graph) (h k: equiv_rel F).
 Hypothesis H: h =2 k. 
 Definition h_merge_same': bij (merge_def F h) (merge_def F k).
   exists (fun x => \pie (generic_quotient.repr x)) (fun x => \pie (generic_quotient.repr x)) => x.
    (* TODO: abstract proofs *)
   - rewrite -{2}[x]reprK. apply/eqquotP. rewrite H equiv_sym. exact: eq_piK. 
   - rewrite -{2}[x]reprK. apply/eqquotP. rewrite -H equiv_sym. exact: eq_piK. 
 Defined.   
 Lemma h_merge_same'E (x: F): h_merge_same' (\pie x) = \pie x.
 Proof. rewrite /=. apply/eqquotP. rewrite -H equiv_sym. exact: eq_piK. Qed.
 Lemma merge_same'_hom: is_hom h_merge_same' bij_id.
 Proof. split=>e//; rewrite /=; apply/eqquotP; rewrite -H; apply: eq_piK. Qed.
 Definition merge_same': iso (merge_def F h) (merge_def F k) := Iso merge_same'_hom. 
End h_merge_same'.
Global Opaque h_merge_same'.

Section h_merge_same.
 Variables (F: graph) (h k: pairs F).
 Hypothesis H: eqv_clot h =2 eqv_clot k.
 Definition h_merge_same: bij (merge_seq F h) (merge_seq F k) := h_merge_same' H.
 Definition merge_same: iso (merge_seq F h) (merge_seq F k) := merge_same' H. 
 Definition h_merge_sameE (x: F): h_merge_same (\pis x) = \pis x := h_merge_same'E H x. 
End h_merge_same.
Global Opaque merge_same.

Lemma eq_equiv_class (T : eqType) : equiv_class_of (@eq_op T). 
Proof. split => //. exact: eq_op_trans. Qed.
Canonical eqv_equiv (T : eqType) := EquivRelPack (@eq_equiv_class T).

Lemma eqv_clot_nothing (T : finType) (h : pairs T) :
  List.Forall (fun p => p.1 = p.2) h -> eqv_clot h =2 eq_op.
Proof.
  move => /ForallE H x y. rewrite eqv_clotE /= in H *. 
  apply/idP/idP; last by move/eqP->.
  by apply: equiv_ofE => /= u v /H /= ->.
Qed.

Section h_merge_nothing.
 Variables (F: graph) (h: pairs F).
 Hypothesis H: List.Forall (fun p => p.1 = p.2) h.
 Lemma h_merge_nothingE_ (x: F): repr (pi h x) = x.
 Proof.
   rewrite /=/repr. case: piP => y /= /eqquotP. 
   by rewrite eqv_clot_nothing // => /eqP->.
 Qed.
 Definition h_merge_nothing:= h_merge_nothing' h_merge_nothingE_.
 Lemma h_merge_nothingE (x: F): h_merge_nothing (\pis x) = x.
 Proof. apply h_merge_nothingE_. Qed.
 Lemma merge_nothing: iso (merge_seq F h) F.
 Proof. apply merge_nothing', h_merge_nothingE_. Defined. 
End h_merge_nothing.
Global Opaque h_merge_nothing.

Section merge_merge_seq.
  (* ideally: derive properties from [merge_merge] *)
  Variables (F: graph) (h k: pairs F) (k': pairs (merge_seq F h)).
  Hypothesis kk': k' = map_pairs (pi h) k.
  Definition h_merge_merge_seq1 (x: merge_seq (merge_seq F h) k'): merge_seq F (h++k) :=
    \pis (repr (repr x)).
  Definition h_merge_merge_seq1' (x: merge_seq F (h++k)): merge_seq (merge_seq F h) k' :=
    \pis (\pis (repr x)).
    
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

  Definition h_merge_merge_seq: bij (merge_seq (merge_seq F h) k') (merge_seq F (h++k)).
    exists h_merge_merge_seq1 h_merge_merge_seq1' => x.
    + rewrite /=/h_merge_merge_seq1/h_merge_merge_seq1'/pi/repr. case: piP  => /= y /eqquotP /= Hy. 
      rewrite eqv_clot_cat /= reprK in Hy. 
      rewrite -[x]reprK /=. apply/eqquotP. by rewrite equiv_sym.
    + rewrite /=/h_merge_merge_seq1/h_merge_merge_seq1'. 
      rewrite -{2}[x]reprK /=. apply: mod_exchange eqv_clot_cat _.
      by rewrite -equiv_comp_pi.
  Defined.
  
  Lemma h_merge_merge_seqE (x: F): h_merge_merge_seq1 (\pis (\pis x)) = \pis x.
  Proof. 
    rewrite /h_merge_merge_seq1/=. apply: mod_exchange eqv_clot_cat _.
    apply/esym. exact: equiv_comp_pi.
  Qed.

  Lemma hom_merge_merge_seq: is_hom h_merge_merge_seq bij_id.
  Proof.
    split=>e//. 
    - rewrite /=/h_merge_merge_seq1. apply: mod_exchange eqv_clot_cat _.
      by rewrite -equiv_comp_pi.
    - rewrite /=/h_merge_merge_seq1. apply: mod_exchange eqv_clot_cat _.
      by rewrite -equiv_comp_pi.
  Qed.
  Definition merge_merge_seq: iso (merge_seq (merge_seq F h) k') (merge_seq F (h++k)) :=
    Iso hom_merge_merge_seq. 
End merge_merge_seq.
Global Opaque h_merge_merge_seq1.

Lemma eqv_clot_map_lr (F G : graph) (l : pairs F) x y : 
  eqv_clot (map_pairs inl l) (unl x : union F G) (unr y) = false.
Proof. rewrite (@eqv_clot_mapF (union F G)) ?inr_codom_inl //. exact: inl_inj. Qed.

Section union_merge_l.
  Variables (F G: graph) (l: pairs F).
  Definition h_union_merge_l1 (x: union (merge_seq F l) G): merge_seq (union F G) (map_pairs unl l) :=
    \pis (match x with inl x => unl (repr x) | inr x => unr x end).
  Definition h_union_merge_l1' (x: merge_seq (union F G) (map_pairs unl l)): union (merge_seq F l) G :=
    match repr x with inl x => unl (\pis x) | inr x => unr x end.

  Lemma h_union_merge_lEl (x: F): h_union_merge_l1 (unl (\pis x)) = \pis (unl x).
  Proof. 
    rewrite /h_union_merge_l1/=. apply/eqmodP. 
    rewrite (@eqv_clot_map (union F G)) 1?equiv_sym. exact: eq_piK. exact: inl_inj. 
  Qed.

  Lemma h_union_merge_lEr (x: G): h_union_merge_l1 (unr x) = \pis (unr x).
  Proof. by []. Qed.

  Definition h_union_merge_l: bij (union (merge_seq F l) G) (merge_seq (union F G) (map_pairs unl l)).
    exists h_union_merge_l1 h_union_merge_l1'=>x.
    (* TODO: abstract proofs *)
    - case: x => [x'|x']. 
      + suff [z Z1 Z2] : exists2 z : F, repr (h_union_merge_l1 (unl x')) = inl z & \pis z = x'.
        { by rewrite /h_union_merge_l1' Z1 Z2. }
        rewrite /h_union_merge_l1/=. case E : (repr _) => [z|z].
        * exists z => //. move/(congr1 (@pi (union F G) (map_pairs inl l))) : E.
          rewrite reprsK. move/eqquotP. rewrite eqv_clot_map => [E|]; last exact: inl_inj.
          rewrite -[x']reprsK. apply:esym. exact/eqquotP.
        * move/(congr1 (@pi (union F G) (map_pairs inl l))) : E.
          rewrite reprsK. move/eqquotP. by rewrite eqv_clot_map_lr.
      + rewrite h_union_merge_lEr /h_union_merge_l1' /repr. case: piP => /= [[y|y]].
        * move/eqquotP. by rewrite equiv_sym eqv_clot_map_lr.
        * move/eqquotP. rewrite (@eqv_clot_map_eq (union F G)) ?inr_codom_inl //.
          by move/eqP=>[->].
    - rewrite /=/h_union_merge_l1/h_union_merge_l1'. case E: (repr x) => [y|y] /=. 
      + rewrite -[x]reprK -/(repr _)/= {}E. apply/eqquotP. 
        rewrite (@eqv_clot_map (union F G)) 1?equiv_sym. exact: eq_piK. exact: inl_inj.
      + by rewrite /unr -E reprsK.
  Defined.
  Lemma hom_union_merge_l: is_hom h_union_merge_l bij_id.
  Proof. by split; move=>[e|e]//=; rewrite h_union_merge_lEl. Qed.
  Definition union_merge_l: iso (union (merge_seq F l) G) (merge_seq (union F G) (map_pairs inl l)) :=
    Iso hom_union_merge_l. 
End union_merge_l.  
Global Opaque h_union_merge_l1.

Lemma map_map_pairs {A B C} (f: A -> B) (g: B -> C) l: map_pairs g (map_pairs f l) = map_pairs (g \o f) l.
Proof. by rewrite /map_pairs -map_comp. Qed.

Section union_merge_r.
  Variables (F G: graph) (l: pairs G).
  Lemma union_merge_r: iso (union F (merge_seq G l)) (merge_seq (union F G) (map_pairs unr l)).
  Proof.
    eapply iso_comp. apply union_C.
    eapply iso_comp. apply union_merge_l.
    eapply iso_comp. apply (merge_iso (union_C _ _)).
    apply merge_same. by rewrite map_map_pairs. 
  Defined.
  Lemma h_union_merge_rEl (x: F): union_merge_r (unl x) = \pis (unl x).
  Proof.
    rewrite /= h_union_merge_lEr.
    rewrite (h_mergeE _ _ (unr x)).
    by rewrite h_merge_sameE. 
  Qed.
  Lemma h_union_merge_rEr (x: G): union_merge_r (unr (\pis x)) = \pis (unr x).
  Proof.
    rewrite /= h_union_merge_lEl.
    rewrite (h_mergeE _ _ (unl x)).
    by rewrite h_merge_sameE. 
  Qed.
End union_merge_r.  
Global Opaque union_merge_r.

Section merge_union_K.
  Variables (F K: graph) (h: pairs (F+K)) (k: K -> F).
  Definition union_K_pairs := map_pairs (fun x => match x with inl x => x | inr x => k x end) h.
  Definition h_merge_union_K1 (x: merge_seq (union F K) h): merge_seq F union_K_pairs :=
    \pis (match repr x with inl x => x | inr x => k x end).
  Definition h_merge_union_K1' (x: merge_seq F union_K_pairs): merge_seq (union F K) h :=
    \pis (unl (repr x)).

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
  
  Definition h_merge_union_K: bij (merge_seq (union F K) h) (merge_seq F union_K_pairs).
    exists h_merge_union_K1 h_merge_union_K1'=> x. 
    - rewrite /h_merge_union_K1'/=. rewrite -[x]reprsK. case E : (repr x) => [y|y].
      + rewrite h_merge_union_KEl. apply/eqquotP. rewrite equiv_clot_Kl equiv_sym. exact: eq_piK.
      + rewrite h_merge_union_KEr. rewrite /pi kh. symmetry. 
        apply/eqquotP. rewrite equiv_clot_Kl. exact: eq_piK.
    - rewrite /h_merge_union_K1'/=. by rewrite h_merge_union_KEl reprsK.
  Defined.

  Hypothesis ke: edge K -> False.

  Definition h_merge_union_Ke1 (e: edge (merge_seq (union F K) h)): edge (merge_seq F union_K_pairs) :=
    match e with inl e => e | inr e => match ke e with end end.

  Definition h_merge_union_Ke: bij (edge (merge_seq (union F K) h)) (edge (merge_seq F union_K_pairs)).
    exists h_merge_union_Ke1 inl=>x//. by case x.
  Defined.

  Lemma hom_merge_union_K: is_hom h_merge_union_K h_merge_union_Ke.
  Proof. split; move => [e//=|//]; by rewrite h_merge_union_KEl. Qed.

  Definition merge_union_K: iso (merge_seq (union F K) h) (merge_seq F union_K_pairs) :=
    Iso hom_merge_union_K. 
End merge_union_K.
Global Opaque h_merge_union_K1.
