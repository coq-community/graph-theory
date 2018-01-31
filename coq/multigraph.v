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

Lemma hom_gI G1 G2 (h : h_ty G1 G2) :
  (forall e : edge G1, [/\ h.1 (source e) = source (h.2 e),
                           h.1 (target e) = target (h.2 e) &
                           label (h.2 e) = label e]) -> hom_g h.
Proof. move=> H. (repeat split)=> e; by case: (H e). Qed.

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

Definition edge_set (G:graph) (S : {set G}) := 
  [set e | (source e \in S) && (target e \in S)].

Definition induced_proof (G:graph) (S : {set G}) : consistent S (edge_set S).
Proof. move => e. by rewrite inE => /andP. Qed.

Definition induced (G:graph) (S : {set G}) := 
  subgraph_for (@induced_proof G S).

Lemma induced_sub (G:graph) (S : {set G}) : subgraph (induced S) G.
Proof. exact: subgraph_sub. Qed.

Definition point (G : graph) (x y : G) := 
  Eval hnf in @Graph2 G x y.

Lemma point_io (G : graph2) : G = @point G g_in g_out.
Proof. by case: G. Qed.

Arguments point : clear implicits.

Definition induced2 (G : graph2) (V :{set G}) := 
  match @idP (g_in \in V), @idP (g_out \in V) with 
  | ReflectT p, ReflectT q => point (induced V) (Sub g_in p) (Sub g_out q)
  | _,_ => G
  end.

Lemma induced2_induced (G : graph2) (V :{set G}) (iV : g_in \in V) (oV :g_out \in V) : 
  induced2 V = point (induced V) (Sub g_in iV) (Sub g_out oV).
Proof.
  rewrite /induced2. 
  case: {-}_ / idP; last by rewrite iV.
  case: {-}_ / idP; last by rewrite oV.
  move => p q. by rewrite (bool_irrelevance p oV) (bool_irrelevance q iV).
Qed.

(** ** Isomorphim Properties *)


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
Proof.
  move=> G1 G2 G3 [f] f_hom [f1_bij f2_bij] [g] g_hom [g1_bij g2_bij].
  exists (g.1 \o f.1, g.2 \o f.2); last by split; exact: bij_comp.
  (repeat split)=> /= [e|e|e||]; first 3 [by rewrite g_hom f_hom];
  by rewrite f_hom g_hom.
Qed.

Lemma iso2_sym : Symmetric iso2.
Proof.
  move=> G1 G2 [f] f_hom [[f1inv] f1K f1invK [f2inv] f2K f2invK].
  exists (f1inv, f2inv); last by split=> /=; [exists f.1 | exists f.2].
  (repeat split)=> /= [e|e|e||].
  - by rewrite -{1}(f2invK e) -f_hom f1K.
  - by rewrite -{1}(f2invK e) -f_hom f1K.
  - by rewrite -f_hom f2invK.
  - by rewrite -(f1K g_in) f_hom.
  - by rewrite -(f1K g_out) f_hom.
Qed.

Lemma iso2_refl G : G ≈ G.
Proof. by exists (id, id); repeat split; exists id. Qed.
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
Proof. case=> h [hom_h bij_h hi ho]. by exists h. Qed.

Lemma iso2_union (G1 G2 G1' G2' : graph2) (f : h_ty G1 G1') (g : h_ty G2 G2') :
  hom_g2 f -> bijective2 f ->
  hom_g2 g -> bijective2 g ->
  exists h : h_ty (union G1 G2) (union G1' G2'),
    [/\ hom_g h, bijective2 h, 
       forall x : G1, h.1 (inl x) = inl (f.1 x)
     & forall x : G2, h.1 (inr x) = inr (g.1 x)].
Proof.
  move => f1 f2 g1 g2.
  pose h1 p := funU f.1 g.1 p.
  pose h2 p := funU f.2 g.2 p.
  exists (h1,h2).
  split=> //; first by (repeat split) => [] [e|e]; rewrite /h1/h2/= ?f1 ?g1.
  case: f2 => - [f1inv f1K f1invK] [f2inv f2K f2invK].
  case: g2 => - [g1inv g1K g1invK] [g2inv g2K g2invK].
  split.
  - exists (funU f1inv g1inv) => -[x|x]; by rewrite /h1/= ?f1K ?f1invK ?g1K ?g1invK.
  - exists (funU f2inv g2inv) => -[x|x]; by rewrite /h2/= ?f2K ?f2invK ?g2K ?g2invK.
Qed.

Lemma union_congr (G1 G2 G1' G2' : graph) : 
  iso G1 G1' -> iso G2 G2' -> iso (union G1 G2) (union G1' G2').
Admitted. (* check for usage *)

(* requires point *)
Lemma merge_congr (G1 G2 : graph) (E1 : equiv_rel G1) (E2 : equiv_rel G2)
  (i1 o1 : G1) (i2 o2 : G2) (h : h_ty G1 G2) : 
  hom_g h -> bijective2 h ->
  h.1 i1 = i2 -> h.1 o1 = o2 ->
  (forall x y, E1 x y = E2 (h.1 x) (h.1 y)) ->
  point (merge_def G1 E1) (\pi_({eq_quot E1}) i1) (\pi_({eq_quot E1}) o1) ≈
  point (merge_def G2 E2) (\pi_({eq_quot E2}) i2) (\pi_({eq_quot E2}) o2).
Proof.
  set M1 := merge_def G1 _. set M2 := merge_def G2 _.
  move => hom_h bij_h hi ho hEq.
  apply: iso2_point.
  pose h1 (x : M1) : M2 := \pi_({eq_quot E2}) (h.1 (repr x)).
  exists (h1,h.2). split => //=.
  - (repeat split) => e /=.
    + rewrite /h1 -hom_h. case: piP => /= x. 
      move/eqmodP => /=. rewrite hEq. by move/eqmodP.
    + rewrite /h1 -hom_h. case: piP => /= x.
      move/eqmodP => /=. rewrite hEq. by move/eqmodP.
    + by rewrite hom_h.
  - split => //=; last apply bij_h. 
    case: bij_h => -[h1inv] _ h1invK _.
    pose h1inv' (x : M2) : M1 := \pi_({eq_quot E1}) (h1inv (repr x)).
    exists h1inv' => x; rewrite /h1/h1inv'; case: piP => /= y /eqmodP/=.
    + by rewrite -{1}(h1invK y) -hEq =>/eqmodP<-; rewrite reprK.
    + by rewrite hEq h1invK =>/eqmodP<-; rewrite reprK.
  - rewrite /h1. case: piP => /= x /eqmodP /=.
    by rewrite hEq hi => /eqmodP /= ->.
  - rewrite /h1. case: piP => /= x /eqmodP /=.
    by rewrite hEq ho => /eqmodP /= ->.
Qed.

Lemma subgraph_for_iso (G : graph2) V1 V2 E1 E2 i1 i2 o1 o2
  (C1 : @consistent G V1 E1) (C2: consistent V2 E2) :
  V1 = V2 -> E1 = E2 -> val i1 = val i2 -> val o1 = val o2 ->
  point (subgraph_for C1) i1 o1 ≈ point (subgraph_for C2) i2 o2.
Proof.
  move => eq_V eq_E eq_i eq_o. subst.
  move/val_inj : eq_i => ->. move/val_inj : eq_o => ->.
  exists (id,id) => //; last (split;exact: id_bij).
  + (repeat split) => //= e.
    * by rewrite (bool_irrelevance (source_proof C1 e) (source_proof C2 e)).
    * by rewrite (bool_irrelevance (target_proof C1 e) (target_proof C2 e)).
Qed.


(** Set up setoid rewriting for iso2 *)

Instance iso2_Equivalence : Equivalence iso2.
Proof. split. exact: iso2_refl. exact: iso2_sym. exact: iso2_trans. Qed.

