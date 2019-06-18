Require Import Setoid CMorphisms Morphisms.
From mathcomp Require Import all_ssreflect.

Require Import edone set_tac finite_quotient preliminaries bij equiv.
Require Import multigraph_new liso.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

Notation IO := [set input; output].

Section multigraph_plus.
Variables (Lv Le : setoid) (G : graph Le Lv).
Implicit Types (x y : G).

Definition incident x e := x \in [set source e; target e].
Definition edges_at x := [set e | incident x e].

Lemma consistentD V : consistent (~: V) (~: \bigcup_(x in V) edges_at x).
Admitted.

Lemma consistentD1 x : consistent [set~ x] (~: edges_at x).
Admitted.

(** We treat [remove_edges] separately from [subgraph_for] since
removing only edges allows us to avoid the sigma-type on for the
vertices. See skeleton.v *)
Definition remove_edges (E : {set edge G}) := 
  {| vertex := G;
     edge := [finType of { e : edge G | e \notin E }];
     source e := source (val e);
     target e := target (val e);
     elabel e := elabel (val e);
     vlabel x := vlabel x |}.

End multigraph_plus.

Arguments edges_at [Lv Le G] x, [Lv Le] G x.

Definition arc (G : lgraph) (e : edge G) x u y := 
  [/\ source e = x, target e = y & elabel e ≡ u] \/
  [/\ source e = y, target e = x & elabel e ≡ u°].

Section lgraph_plus.
Variable (G : lgraph).


Lemma arcC (e : edge G) x y u : 
  arc e x u y <-> arc e y u x.
Admitted.

Lemma add_edge_arc x y u : @arc (add_edge G x y u) None x u y.
Admitted.

Lemma edges_at_add_edgeT x u y z: z \in [set x;y] -> 
  edges_at (add_edge G x y u) z = None |: Some @: edges_at z.
Admitted.

Lemma edges_at_add_edgeN x u y z: z \notin [set x;y] -> 
  edges_at (add_edge G x y u) z = Some @: edges_at z.
Admitted.

End lgraph_plus.


Arguments consistentD1 [Lv Le G] x.
Arguments consistentD [Lv Le G] V.
Arguments consistentT [Lv Le G] E.

Section DelVertices.
Variable (G : lgraph) (V : {set G}).
Hypothesis (HV : [disjoint V & IO]).

Lemma sub_input  : input \in ~: V. Admitted.
Lemma sub_output : output \in ~: V. Admitted.

Definition del_vertices := 
  point (subgraph_for (consistentD V)) (Sub input sub_input) (Sub output sub_output).

End DelVertices.

Arguments del_vertices [G] V _.

Section DelVertex.
Variables (G : lgraph) (x : G) (Hx : x \notin IO).

Lemma del_vertex_proof : [disjoint [set x] & IO].
Admitted.

Definition del_vertex := del_vertices [set x] del_vertex_proof.

Lemma edges_at_del_vertices z : 
  edges_at del_vertex z = [set e | val e \notin edges_at x].
Admitted.

Lemma edges_at_del_vertices0 z : edges_at (val z) \subset edges_at x ->
  edges_at del_vertex z = set0.
Proof. rewrite edges_at_del_vertices. 
Admitted.

End DelVertex.

Arguments del_vertex : clear implicits.


Definition del_edges (G : lgraph) (E : {set edge G}) := 
  point (remove_edges E) input output.
Arguments del_edges : clear implicits.

Notation del_edge G e := (del_edges G [set e]).


Universe S.

Variant Rule := RULE_V1 | RULE_V2 | RULE_E1 | RULE_E2.

(* TOTHINK: Put the the add_test below the del_vertex to avoid the dependency? *)
Inductive step : lgraph -> lgraph -> Type@{S} := 
| step_v1 G x z e (Hz : z \notin IO) (Hx : x \in [set~ z]) u:  
    arc e x u z -> edges_at z = [set e] ->
    step G (add_test (del_vertex G z Hz) (Sub x Hx) [dom(u·vlabel z)])
| step_v2 G x y z e1 e2 (Hz : z \notin IO) (Hx : x \in [set~ z]) (Hy : y \in [set~ z]) u v : 
    arc e1 x u z -> arc e2 z v y -> edges_at z = [set e1;e2] -> e1 != e2 ->
    step G (add_edge (del_vertex G z Hz) (Sub x Hx) (Sub y Hy) (u·vlabel z·v))
| step_e1 G e x : 
    source e = x -> target e = x -> 
    step G (add_test (del_edge G e) x [1∥elabel e])
| step_e2 G e1 e2 x y u v : 
    arc e1 x u y -> arc e2 x v y -> x != y ->
    step G (add_edge (del_edges G [set e1;e2]) x y (u∥v))
.

Definition step_order G H (s: step G H): nat :=
  match s with
  (* | step_v0 _ _ => 0 *)
  | step_v1 _ _ _ _ _ _ _ _ _ => 1
  | step_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 2
  | step_e1 _ _ _ _ _ => 3
  | step_e2 _ _ _ _ _ _ _ _ _ _ => 4
  end.

(** It is crucial that we name the universe steps resides in. Without
the explicit name, the inferred universe is a max-universe, causing
setoid rewite underneath of steps to fail with the anomaly: "Unable to
handle arbitrary u+k <= v constraints." *)
Inductive steps: lgraph -> lgraph -> Type@{S} :=
  | liso_step:    CRelationClasses.subrelation liso steps
  | step_step:    CRelationClasses.subrelation step steps
  | trans_steps : CRelationClasses.Transitive steps.


Notation "'Σ' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p%type)) ..))
  (at level 200, x binder, y binder, right associativity).

Ltac GlGr :=
  match goal with 
    |- context[(steps ?G _ * steps ?H _)%type] => set Gl := G; set Gr := H
  end.

Require Import set_tac.

Lemma local_confluence (G Gl Gr: lgraph) : 
  step G Gl -> step G Gr -> Σ Hl Hr, steps Gl Hl * steps Gr Hr * liso Hl Hr.
Proof.
  move => S S'.
  wlog: Gl Gr S S' / step_order S <= step_order S'.
  { move => W. case/orb_sum: (leq_total (step_order S) (step_order S')) => SS. 
    - exact: W SS. 
    - case: (W _ _ _ _ SS) => Hr [Hl] [[Sr Sl] l]. 
      exists Hl; exists Hr. split => //. exact: liso_sym. }
  destruct S as [G x z e Hz Hx u Ae Iz|*|*|*]; 
  destruct S' as [*|G' x' y' z' e1' e2' Hz' Hx' Hy' u' v' Ae1' Ae2' Iz' D|*|*]; try done; move => _; GlGr.
  - (* Case V1 / V1 *) admit.
  - (* Case V1 / V2 *) 
    case: (altP (z =P y')) => [?|xDy'].
    + subst y'. 
      have [? ?] : e2' = e /\ z' = x ; subst. admit. 
      do 2 eexists; repeat split. 
      * apply step_step. (* x is preserved and its only incident edge in Gl is  e1' *)
      * apply step_step. apply step_v1 with None. apply add_edge_arc. 
        rewrite edges_at_add_edgeT ?inD //. 
        rewrite edges_at_del_vertices0 ?imset0 ?setU0 //= Iz Iz'. admit.
      * admit.
  - (* Case V1 / E1 *) admit.
  - (* Case V1 / E2 *) admit.
  - (* Case V2 / V2 *) admit.
  - (* Case V2 / E1 *) admit.
  - (* Case V2 / E2 *) admit.
  - (* Case E1 / E1 *) admit.
  - (* Case E1 / E2 *) admit.
  - (* Case E2 / E2 *) admit.
Admitted.

