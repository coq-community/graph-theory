(* TEMPORARY FILE: 
   lemmas that where in multigraph.v while talking about [graph2], 
   which are not yet in ptt_graph.v (waiting to see what is needed to import subalgebra.v and so on) 
*)

Require Import RelationClasses Setoid Morphisms.

From mathcomp Require Import all_ssreflect.
Require Import finite_quotient preliminaries equiv multigraph ptt_graph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 


Lemma hom_gI G1 G2 (h : h_ty G1 G2) :
  (forall e : edge G1, [/\ h.1 (source e) = source (h.2 e),
                           h.1 (target e) = target (h.2 e) &
                           label (h.2 e) = label e]) -> hom_g h.
Proof. move=> H. (repeat split)=> e; by case: (H e). Qed.


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

Lemma iso2_of_iso (G1 G2 : graph2) (h : h_ty G1 G2) :
  hom_g h -> bijective2 h -> h.1 g_in = g_in -> h.1 g_out = g_out -> 
  G1 ≈ G2.
Abort.


Definition hom_g2 (F G: graph2) (h: h_ty F G): Prop := 
  (hom_g h * (h.1 g_in = g_in) * (h.1 g_out = g_out))%type.


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
       forall x : G1, h.1 (unl x) = unl (f.1 x)
     & forall x : G2, h.1 (unr x) = unr (g.1 x)].
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
  pose h1 (x : M1) : M2 := \pi_({eq_quot E2}) (h.1 (generic_quotient.repr x)).
  exists (h1,h.2). split => //=.
  - (repeat split) => e /=.
    + rewrite /h1 -hom_h. case: piP => /= x. 
      move/eqmodP => /=. rewrite hEq. by move/eqmodP.
    + rewrite /h1 -hom_h. case: piP => /= x.
      move/eqmodP => /=. rewrite hEq. by move/eqmodP.
    + by rewrite hom_h.
  - split => //=; last apply bij_h. 
    case: bij_h => -[h1inv] _ h1invK _.
    pose h1inv' (x : M2) : M1 := \pi_({eq_quot E1}) (h1inv (generic_quotient.repr x)).
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
  exists (id,id). ((repeat split); try exact: id_bij)=> /= e. 
    * by rewrite (bool_irrelevance (source_proof C1 e) (source_proof C2 e)).
    * by rewrite (bool_irrelevance (target_proof C1 e) (target_proof C2 e)).
Qed.
