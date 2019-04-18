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

Definition iso_g (G1 G2 : graph) (h : h_ty G1 G2) := hom_g h /\ bijective2 h.

(* TODO: use iso_g *)
Definition iso (G1 G2 : graph) := 
  exists2 h : h_ty G1 G2, hom_g h & bijective2 h.

Definition iso2 (G1 G2 : graph2) : Prop := 
  exists2 h : h_ty G1 G2, hom_g2 h & bijective2 h.

Notation "G ≈ H" := (iso2 G H) (at level 45).

Lemma iso2_of_iso (G1 G2 : graph2) (h : h_ty G1 G2) :
  hom_g h -> bijective2 h -> h.1 g_in = g_in -> h.1 g_out = g_out -> 
  G1 ≈ G2.
Abort.

Lemma iso_of_iso2 (G1 G2 : graph2) : G1 ≈ G2 -> iso G1 G2.
Abort.

Lemma iso2_trans : Transitive iso2.
Proof.
  move=> G1 G2 G3 [f] f_hom [f1_bij f2_bij] [g] g_hom [g1_bij g2_bij].
  exists (g.1 \o f.1, g.2 \o f.2); last by split; exact: bij_comp.
  (repeat split)=> /= [e|e|e||]; first 3 [by rewrite g_hom f_hom];
  by rewrite f_hom g_hom.
Qed.

Lemma iso2_inv (G1 G2 : graph2) (h : h_ty G1 G2) (g : h_ty G2 G1) :
  cancel h.1 g.1 -> cancel h.2 g.2 -> cancel g.1 h.1 -> cancel g.2 h.2 ->
  hom_g2 h -> hom_g2 g.
Proof.
  move => hg1K hg2K gh1K gh2K hom_h.
  (repeat split)=> /= [e|e|e||].
  - by rewrite -{1}(gh2K e) -hom_h hg1K.
  - by rewrite -{1}(gh2K e) -hom_h hg1K.
  - by rewrite -hom_h gh2K.
  - by rewrite -(hg1K g_in) hom_h.
  - by rewrite -(hg1K g_out) hom_h.
Qed.

Lemma iso2_sym : Symmetric iso2.
Proof.
  move=> G1 G2 [f] f_hom [[f1inv] f1K f1invK [f2inv] f2K f2invK].
  exists (f1inv, f2inv); last by split=> /=; [exists f.1 | exists f.2].
  exact: iso2_inv f_hom.
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
Abort. 

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


Lemma iso_iso2 (F G: graph) (i o: F) (h: h_ty F G):
  iso_g h -> point F i o ≈ point G (h.1 i) (h.1 o).
Proof. intro H. exists h. split. split. apply H. by []. by []. apply H. Qed.

Lemma iso_iso2' (F G: graph) (i o: F) (i' o': G) (h: h_ty F G):
  iso_g h -> i' = h.1 i -> o' = h.1 o -> point F i o ≈ point G i' o'.
Proof. intros H -> ->. by apply iso_iso2. Qed.

(** Specific isomorphisms about union and merge *)

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
Proof. exists (h_union_C G H). apply hom_union_C. apply bij_union_C. Qed.

Lemma union_C2 (F G: graph) (i o: F+G):
  point (union F G) i o ≈ point (union G F) (sumC i) (sumC o).
Proof. by eapply iso_iso2'; first apply iso_union_C. Qed.



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
Proof. exists (h_union_A F G H). apply hom_union_A. apply bij_union_A. Qed.

Lemma union_A2 (F G H: graph) (i o: F+(G+H)):
  point (union F (union G H)) i o ≈ point (union (union F G) H) (sumA i) (sumA o).
Proof. by eapply iso_iso2'; first apply iso_union_A. Qed.


Definition h_union_A' (F G H: graph): h_ty (union (union F G) H) (union F (union G H)) := (sumA',sumA').

Lemma hom_union_A' F G H: hom_g (h_union_A' F G H).
Proof. by split; first split; intros [[|]|]. Qed.

Lemma bij_union_A' F G H: bijective2 (h_union_A' F G H).
Proof. by split; apply bij_sumA'. Qed.

Lemma iso_union_A' F G H: iso_g (h_union_A' F G H).
Proof. split. apply hom_union_A'. apply bij_union_A'. Qed.

Lemma union_A2' (F G H: graph) (i o: (F+G)+H):
  point (union (union F G) H) i o ≈ point (union F (union G H)) (sumA' i) (sumA' o).
Proof. by eapply iso_iso2'; first apply iso_union_A'. Qed.



Section equiv_comp.
  Variables (T: choiceType) (e: equiv_rel T) (e': equiv_rel {eq_quot e}).
  Definition equiv_comp: rel T := fun x y => e' (\pi x) (\pi y).
  Lemma equiv_comp_class: equiv_class_of equiv_comp.
  Admitted.
  Canonical Structure equiv_comp_rel := EquivRelPack equiv_comp_class.
  Lemma equiv_comp_pi (x: T):
    x = repr (repr (\pi_{eq_quot e'} (\pi_{eq_quot e} x)))
             %[mod_eq equiv_comp_rel].
  Admitted.
End equiv_comp.

Notation "\pi x" := (\pi_{eq_quot _} x) (at level 30). 

Section merge_merge.
  Variables (F: graph) (e: equiv_rel F) (e': equiv_rel (merge_def F e)).
  Definition h_merge_merge1 (x: merge_def (merge_def F e) e'): merge_def F (equiv_comp_rel e') :=
    \pi (repr (repr x)).
  Definition h_merge_merge: h_ty _ _ := (h_merge_merge1,id).
  Lemma hom_merge_merge: hom_g h_merge_merge.
  Admitted.
  Lemma bij_merge_merge: bijective2 h_merge_merge.
  Proof.
    split; last apply id_bij. 
  Admitted.
  Lemma iso_merge_merge: iso_g h_merge_merge.
  Proof. split. apply hom_merge_merge. apply bij_merge_merge. Qed.
  Lemma merge_merge: iso (merge_def (merge_def F e) e') (merge_def F (equiv_comp_rel e')).
  Proof. eexists. apply hom_merge_merge. apply bij_merge_merge. Qed.
End merge_merge.

Definition pairs A := seq (A*A).
Definition map_pairs A B (f: A -> B): pairs A -> pairs B := map (fun x => (f x.1,f x.2)). 
Parameter eqv_clot: forall T, pairs T -> equiv_rel T.
Definition merge_seq (G: graph) l := merge_def G (eqv_clot l).
Arguments merge_seq G l: clear implicits. 

Section merge_merge_seq.
  Variables (F: graph) (h k: pairs F) (k': pairs (merge_seq F h)).
  Definition h_merge_merge_seq1 (x: merge_seq (merge_seq F h) k'): merge_seq F (h++k) :=
    \pi (repr (repr x)).
  Definition h_merge_merge_seq: h_ty _ _ := (h_merge_merge_seq1,id).
  (* ideally: derive properties from [merge_merge] *)
  Hypothesis kk': k' = map_pairs [eta \pi_{eq_quot _}] k.
  Lemma eqv_clot_cat: forall x y, eqv_clot (h++k) x y = equiv_comp (eqv_clot k') x y.
  Admitted.
  Lemma h_merge_merge_seqE (x: F): h_merge_merge_seq1 (\pi (\pi x)) = \pi x.
    (* should be derivable from [eqv_clot_cat], [equiv_comp_pi] and lemmas from the quotient lib *)
  Admitted.
  Lemma hom_merge_merge_seq: hom_g h_merge_merge_seq.
  Admitted.
  Lemma bij_merge_merge_seq: bijective2 h_merge_merge_seq.
  Proof.
    split; last apply id_bij. 
  Admitted.
  Lemma iso_merge_merge_seq: iso_g h_merge_merge_seq.
  Proof. split. apply hom_merge_merge_seq. apply bij_merge_merge_seq. Qed.
  Lemma merge_merge_seq: iso (merge_seq (merge_seq F h) k') (merge_seq F (h++k)).
  Proof. eexists. apply hom_merge_merge_seq. apply bij_merge_merge_seq. Qed.
End merge_merge_seq.

Lemma merge_merge_seq2 (G: graph) (h k: pairs G) (k': pairs (merge_seq G h)) (i o: G):
  k' = map_pairs [eta \pi_{eq_quot _}] k ->
  point (merge_seq (merge_seq G h) k') (\pi (\pi i)) (\pi (\pi o))
≈ point (merge_seq G (h++k)) (\pi i) (\pi o).
Proof.
  intro K. eapply iso_iso2'; first apply iso_merge_merge_seq=>//; by rewrite /=h_merge_merge_seqE. 
Qed.


Section union_merge_l.
  Variables (F G: graph) (l: pairs F).
  Definition h_union_merge_l1 (x: union (merge_seq F l) G): merge_seq (union F G) (map_pairs inl l) :=
    \pi (match x with inl x => inl (repr x) | inr x => inr x end).
  Definition h_union_merge_l: h_ty _ _ := (h_union_merge_l1,id).
  Lemma h_union_merge_lEl (x: F): h_union_merge_l1 (inl (\pi x)) = \pi (inl x).
  Admitted.
  Lemma h_union_merge_lEr (x: G): h_union_merge_l1 (inr x) = \pi (inr x).
  Admitted.
  Lemma hom_union_merge_l: hom_g h_union_merge_l.
  Admitted.
  Lemma bij_union_merge_l: bijective2 h_union_merge_l.
  Proof.
    split; last apply id_bij. 
  Admitted.
  Lemma iso_union_merge_l: iso_g h_union_merge_l.
  Proof. split. apply hom_union_merge_l. apply bij_union_merge_l. Qed.
  Lemma union_merge_l: iso (union (merge_seq F l) G) (merge_seq (union F G) (map_pairs inl l)).
  Proof. eexists. apply hom_union_merge_l. apply bij_union_merge_l. Qed.
End union_merge_l.  

Lemma union_merge_l2_ll (F G: graph) (i o: F) (h: pairs F):
  point (union (merge_seq F h) G) (inl (\pi i)) (inl (\pi o))
≈ point (merge_seq (union F G) (map_pairs inl h)) (\pi (inl i)) (\pi (inl o)).
Proof. eapply iso_iso2'; first apply iso_union_merge_l; by rewrite /=h_union_merge_lEl. Qed.

Lemma union_merge_l2_lr (F G: graph) (i: F) (o: G) (h: pairs F):
  point (union (merge_seq F h) G) (inl (\pi i)) (inr o)
≈ point (merge_seq (union F G) (map_pairs inl h)) (\pi (inl i)) (\pi (inr o)).
Proof.
  eapply iso_iso2'; first apply iso_union_merge_l.
    by rewrite /=h_union_merge_lEl.
    by rewrite /=h_union_merge_lEr.
Qed.

Lemma union_merge_l2_rl (F G: graph) (i: G) (o: F) (h: pairs F):
  point (union (merge_seq F h) G) (inr i) (inl (\pi o))
≈ point (merge_seq (union F G) (map_pairs inl h)) (\pi (inr i)) (\pi (inl o)).
Proof.
  eapply iso_iso2'; first apply iso_union_merge_l.
    by rewrite /=h_union_merge_lEr.
    by rewrite /=h_union_merge_lEl.
Qed.

Lemma union_merge_l2_rr (F G: graph) (i o: G) (h: pairs F):
  point (union (merge_seq F h) G) (inr i) (inr o)
≈ point (merge_seq (union F G) (map_pairs inl h)) (\pi (inr i)) (\pi (inr o)).
Proof. eapply iso_iso2'; first apply iso_union_merge_l; by rewrite /=h_union_merge_lEr. Qed.


Section union_merge_r.
  Variables (F G: graph) (l: pairs G).
  Definition h_union_merge_r1 (x: union F (merge_seq G l)): merge_seq (union F G) (map_pairs inr l) :=
    \pi (match x with inl x => inl x | inr x => inr (repr x) end).
  Definition h_union_merge_r: h_ty _ _ := (h_union_merge_r1,id).
  (* ideally: derive properties from [union_merge_l] and [union_C] *)
  Lemma h_union_merge_rEl (x: F): h_union_merge_r1 (inl x) = \pi (inl x).
  Admitted.
  Lemma h_union_merge_rEr (x: G): h_union_merge_r1 (inr (\pi x)) = \pi (inr x).
  Admitted.
  Lemma hom_union_merge_r: hom_g h_union_merge_r.
  Admitted.
  Lemma bij_union_merge_r: bijective2 h_union_merge_r.
  Proof.
    split; last apply id_bij. 
  Admitted.
  Lemma iso_union_merge_r: iso_g h_union_merge_r.
  Proof. split. apply hom_union_merge_r. apply bij_union_merge_r. Qed.
  Lemma union_merge_r: iso (union F (merge_seq G l)) (merge_seq (union F G) (map_pairs inr l)).
  Proof. eexists. apply hom_union_merge_r. apply bij_union_merge_r. Qed.
End union_merge_r.  

Lemma union_merge_r2_ll (F G: graph) (i o: F) (h: pairs G):
  point (union F (merge_seq G h)) (inl i) (inl o)
≈ point (merge_seq (union F G) (map_pairs inr h)) (\pi (inl i)) (\pi (inl o)).
Proof. eapply iso_iso2'; first apply iso_union_merge_r; by rewrite /=h_union_merge_rEl. Qed.

Lemma union_merge_r2_lr (F G: graph) (i: F) (o: G) (h: pairs G):
  point (union F (merge_seq G h)) (inl i) (inr (\pi o))
≈ point (merge_seq (union F G) (map_pairs inr h)) (\pi (inl i)) (\pi (inr o)).
Proof.
  eapply iso_iso2'; first apply iso_union_merge_r.
    by rewrite /=h_union_merge_rEl.
    by rewrite /=h_union_merge_rEr.
Qed.

Lemma union_merge_r2_rl (F G: graph) (i: G) (o: F) (h: pairs G):
  point (union F (merge_seq G h)) (inr (\pi i)) (inl o)
≈ point (merge_seq (union F G) (map_pairs inr h)) (\pi (inr i)) (\pi (inl o)).
Proof.
  eapply iso_iso2'; first apply iso_union_merge_r.
    by rewrite /=h_union_merge_rEr.
    by rewrite /=h_union_merge_rEl.
Qed.

Lemma union_merge_r2_rr (F G: graph) (i o: G) (h: pairs G):
  point (union F (merge_seq G h)) (inr (\pi i)) (inr (\pi o))
≈ point (merge_seq (union F G) (map_pairs inr h)) (\pi (inr i)) (\pi (inr o)).
Proof. eapply iso_iso2'; first apply iso_union_merge_r; by rewrite /=h_union_merge_rEr. Qed.


Section merge_union_K.
  Variables (F K: graph) (h: pairs (F+K)) (k: K -> F).
  Definition union_K_pairs := map_pairs (fun x => match x with inl x => x | inr x => k x end) h.
  Definition h_merge_union_K1 (x: merge_seq (union F K) h): merge_seq F union_K_pairs :=
    \pi (match repr x with inl x => x | inr x => k x end).
  Lemma h_merge_union_KEl (x: F): h_merge_union_K1 (\pi (inl x)) = \pi x.
  Admitted.
  Lemma h_merge_union_KEr (x: K): h_merge_union_K1 (\pi (inr x)) = \pi (k x).
  Admitted.
  Hypothesis ke: edge K -> False.
  Definition h_merge_union_K2 (e: edge (merge_seq (union F K) h)): edge (merge_seq F union_K_pairs) :=
    match e with inl e => e | inr e => match ke e with end end.
  Definition h_merge_union_K: h_ty _ _ := (h_merge_union_K1,h_merge_union_K2).
  Hypothesis kh: forall x: K, inr x = inl (k x) %[mod_eq (eqv_clot h)].
  Lemma hom_merge_union_K: hom_g h_merge_union_K.
  Admitted.
  Lemma bij_merge_union_K: bijective2 h_merge_union_K.
  Proof.
    split. admit.
    exists inl =>//. move =>[|]//=. 
  Admitted.
  Lemma iso_merge_union_K: iso_g h_merge_union_K.
  Proof. split. apply hom_merge_union_K. apply bij_merge_union_K. Qed.
  Lemma merge_union_K: iso (merge_seq (union F K) h) (merge_seq F union_K_pairs).
  Proof. eexists. apply hom_merge_union_K. apply bij_merge_union_K. Qed.
End merge_union_K.

Lemma merge_union_K2_ll (F K: graph) (i o: F) (h: pairs (F+K)) (k: K -> F)
      (ke: edge K -> False)
      (kh: forall x: K, inr x = inl (k x) %[mod_eq (eqv_clot h)]):
  point (merge_seq (union F K) h) (\pi (inl i)) (\pi (inl o))
≈ point (merge_seq F (union_K_pairs h k)) (\pi i) (\pi o).
Proof.
  eapply iso_iso2'; first (by apply (iso_merge_union_K ke)); by rewrite /=h_merge_union_KEl.
Qed.

Lemma merge_union_K2_lr (F K: graph) (i: F) (o: K) (h: pairs (F+K)) (k: K -> F)
      (ke: edge K -> False)
      (kh: forall x: K, inr x = inl (k x) %[mod_eq (eqv_clot h)]):
  point (merge_seq (union F K) h) (\pi (inl i)) (\pi (inr o))
≈ point (merge_seq F (union_K_pairs h k)) (\pi i) (\pi (k o)).
Proof.
  eapply iso_iso2'; first (by apply (iso_merge_union_K ke)).
   by rewrite /=h_merge_union_KEl.
   by rewrite /=h_merge_union_KEr.
Qed.

Lemma merge_union_K2_rl (F K: graph) (i: K) (o: F) (h: pairs (F+K)) (k: K -> F)
      (ke: edge K -> False)
      (kh: forall x: K, inr x = inl (k x) %[mod_eq (eqv_clot h)]):
  point (merge_seq (union F K) h) (\pi (inr i)) (\pi (inl o))
≈ point (merge_seq F (union_K_pairs h k)) (\pi (k i)) (\pi o).
Proof.
  eapply iso_iso2'; first (by apply (iso_merge_union_K ke)).
   by rewrite /=h_merge_union_KEr.
   by rewrite /=h_merge_union_KEl.
Qed.

Lemma merge_union_K2_rr (F K: graph) (i o: K) (h: pairs (F+K)) (k: K -> F)
      (ke: edge K -> False)
      (kh: forall x: K, inr x = inl (k x) %[mod_eq (eqv_clot h)]):
  point (merge_seq (union F K) h) (\pi (inr i)) (\pi (inr o))
≈ point (merge_seq F (union_K_pairs h k)) (\pi (k i)) (\pi (k o)).
Proof.
  eapply iso_iso2'; first (by apply (iso_merge_union_K ke)); by rewrite /=h_merge_union_KEr.
Qed.
