Require Import RelationClasses Setoid.

From mathcomp Require Import all_ssreflect.
Require Import finite_quotient preliminaries.

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

Record graph2 := Graph2 { graph_of :> graph;
                          g_in : graph_of;
                          g_out : graph_of }.

Arguments g_in [g].
Arguments g_out [g].

(** Disjoint Union *)

Definition funU (aT1 aT2 rT1 rT2 : Type) (f : aT1 -> rT1) (g : aT2 -> rT2) :=
  [fun x => match x with inl a => inl (f a) | inr a => inr (g a) end].

Definition union (G1 G2 : graph) : graph :=
  {| vertex := [finType of G1 + G2];
     edge := [finType of edge G1 + edge G2];
     source := funU (@source G1) (@source G2);
     target := funU (@target G1) (@target G2);
     label e := match e with inl e => label e | inr e => label e end |}.

(** ** Homomorphisms *)

Definition h_ty (G1 G2 : graph) := ((vertex G1 -> vertex G2)*(edge G1 -> edge G2))%type.

Definition hom_g G1 G2 (h : h_ty G1 G2) : Prop :=
 ((forall e : edge G1, h.1 (source e) = source (h.2 e))
 *(forall e : edge G1, h.1 (target e) = target (h.2 e))
 *(forall e : edge G1, label (h.2 e) = label e))%type.

Definition hom_g2 (G1 G2:graph2) (h : h_ty G1 G2) : Prop :=
   (hom_g h * (h.1 g_in = g_in) * (h.1 g_out = g_out))%type.

Definition injective2 G H (h : h_ty G H) := (injective h.1 * injective h.2)%type.
Definition surjective2 G H (h : h_ty G H) := (surjective h.1 * surjective h.2)%type.

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

(** Equivalence Closure *)

Section Equivalence.

Variables (T : finType) (e : rel T).

Definition sc (T : Type) (e : rel T) := [rel x y | e x y || e y x].

Definition equiv_of  := connect (sc e).

Definition equiv_of_refl : reflexive equiv_of.
Proof. exact: connect0. Qed.

Lemma equiv_of_sym : symmetric equiv_of.
Proof. apply: connect_symI => x y /=. by rewrite orbC. Qed.
  
Definition equiv_of_trans : transitive equiv_of.
Proof. exact: connect_trans. Qed.

Canonical equiv_of_equivalence :=
  EquivRel equiv_of equiv_of_refl equiv_of_sym equiv_of_trans.

End Equivalence.

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

Definition edge_set (G:graph) (S : {set G}) := 
  [set e | (source e \in S) && (target e \in S)].

Definition induced_proof (G:graph) (S : {set G}) : consistent S (edge_set S).
Proof. move => e. by rewrite inE => /andP. Qed.

Definition induced (G:graph) (S : {set G}) := 
  subgraph_for (@induced_proof G S).

Lemma induced_sub (G:graph) (S : {set G}) : subgraph (induced S) G.
Proof. exact: subgraph_sub. Qed.


(** ** Isomorphim Properties *)

Definition point (G : graph) (x y : G) := 
  Eval hnf in @Graph2 G x y.

Arguments point : clear implicits.

Local Open Scope quotient_scope.

(* Isomorphim of graphs *)

Definition bijective2 (G1 G2 : graph) (h : h_ty G1 G2) := 
  bijective h.1 /\ bijective h.2.

Definition iso (G1 G2 : graph) := 
  exists2 h : h_ty G1 G2, hom_g h & bijective2 h.

Definition iso2 (G1 G2 : graph2) : Prop := 
  exists2 h : h_ty G1 G2, hom_g2 h & bijective2 h.

Notation "G ≈ H" := (iso2 G H) (at level 45).

Lemma iso2_of_iso (G1 G2 : graph2) (h : h_ty G1 G2) :
  hom_g h -> bijective2 h -> h.1 g_in = g_in -> h.1 g_out = g_out -> 
  G1 ≈ G2.
Admitted. (* check for usage *)

Lemma iso_of_iso2 (G1 G2 : graph2) : G1 ≈ G2 -> iso G1 G2.
Admitted. (* check for usage *)

Lemma iso2_trans : Transitive iso2.
Admitted.

Lemma iso2_sym : Symmetric iso2.
Admitted.

Lemma iso2_refl G : G ≈ G.
Admitted.
Hint Resolve iso2_refl.

Lemma iso2_inv_in (G1 G2 : graph2) (h : h_ty G1 G2) x : 
  hom_g2 h -> bijective2 h -> (h.1 x == g_in) = (x == g_in).
Proof. 
  move => H1 [[g H2 H3] H4]. rewrite -[g_in]H1 inj_eq //. 
  exact: can_inj H2.  
Qed.

Lemma iso2_inv_out (G1 G2 : graph2) (h : h_ty G1 G2) x : 
  hom_g2 h -> bijective2 h -> (h.1 x == g_out) = (x == g_out).
Proof.
  move => H1 [[g H2 H3] H4]. rewrite -[g_out]H1 inj_eq //. 
  exact: can_inj H2.  
Qed.

Lemma iso2_point (G1 G2 : graph) (i1 o1 :G1) (i2 o2 : G2) :
  (exists h, [/\ hom_g h, bijective2 h, h.1 i1 = i2 & h.1 o1 = o2]) ->
  point G1 i1 o1 ≈ point G2 i2 o2.
Admitted. (* check for usage / use in merge_congr? *)

Lemma iso2_union (G1 G2 G1' G2' : graph2) (f : h_ty G1 G1') (g : h_ty G2 G2') :
  hom_g2 f -> bijective2 f ->
  hom_g2 g -> bijective2 g ->
  exists h : h_ty (union G1 G2) (union G1' G2'),
    [/\ hom_g h, bijective2 h, 
       forall x : G1, h.1 (inl x) = inl (f.1 x)
     & forall x : G2, h.1 (inr x) = inr (g.1 x)].
Proof.
  move => f1 f2 g1 g2.
  pose h1 p := 
    match p with 
    | inl x => inl (f.1 x) 
    | inr x => inr (g.1 x)
    end.
  pose h2 p := 
    match p with 
    | inl x => inl (f.2 x) 
    | inr x => inr (g.2 x)
    end.
  exists (h1,h2). split => //.
  - (repeat split) => [] [e|e] /=; by rewrite ?f1 ?g1.
  - split. admit.
Admitted.

Lemma union_congr (G1 G2 G1' G2' : graph) : 
  iso G1 G1' -> iso G2 G2' -> iso (union G1 G2) (union G1' G2').
Admitted. (* check for usage *)


Lemma lift_equiv (T1 T2 : finType) (E1 : rel T1) (E2 : rel T2) h :
  bijective h -> (forall x y, E1 x y = E2 (h x) (h y)) ->
  (forall x y, equiv_of E1 x y = equiv_of E2 (h x) (h y)).
Proof.
Admitted.

(* requires point *)
Lemma merge_congr (G1 G2 : graph) (E1 : rel G1) (E2 : rel G2) 
  (i1 o1 : G1) (i2 o2 : G2) (h : h_ty G1 G2) : 
  hom_g h -> bijective2 h ->
  h.1 i1 = i2 -> h.1 o1 = o2 ->
  (forall x y, E1 x y = E2 (h.1 x) (h.1 y)) ->
  point (merge G1 (equiv_of E1)) 
        (\pi_({eq_quot (equiv_of E1)}) i1)
        (\pi_({eq_quot (equiv_of E1)}) o1) ≈ 
  point (merge G2 (equiv_of E2)) 
        (\pi_({eq_quot (equiv_of E2)}) i2)
        (\pi_({eq_quot (equiv_of E2)}) o2).
Proof.
  set M1 := merge G1 _. set M2 := merge G2 _.
  move => hom_h bij_h hi ho hE.
  have hEq x y  : equiv_of E1 x y = equiv_of E2 (h.1 x) (h.1 y).
  { apply: lift_equiv => //. by apply bij_h. }
  apply: iso2_point.
  pose h1 (x : M1) : M2 := \pi_({eq_quot (equiv_of E2)}) (h.1 (repr x)).
  exists (h1,h.2). split => //=.
  - (repeat split) => e /=.
    + rewrite /h1 -hom_h. case: piP => /= x. 
      move/eqmodP => /=. rewrite hEq. by move/eqmodP.
    + admit. (* as above *)
    + by rewrite hom_h.
  - split => //=; last apply bij_h. 
    admit.
  - rewrite /h1. case: piP => /= x /eqmodP /=.
    by rewrite hEq hi => /eqmodP /= ->.
Admitted.

(** Set up setoid rewriting for iso2 *)

Instance iso2_Equivalence : Equivalence iso2.
Proof. split. exact: iso2_refl. exact: iso2_sym. exact: iso2_trans. Qed.

