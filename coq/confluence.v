Require Import Setoid CMorphisms Morphisms.
From mathcomp Require Import all_ssreflect.

Require Import edone set_tac finite_quotient preliminaries bij equiv.
Require Import multigraph_new liso.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

Lemma set2_Sub (T : finType) (p : pred T) (x y : T) (Hx : p x) (Hy : p y) :
  [set Sub x Hx ; Sub y Hy] = [set z | val z \in [set x;y]] :> {set sig p}.
Proof. apply/setP=>k. rewrite !inE -!val_eqE. done. Qed.

Notation "'Σ' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p%type)) ..))
  (at level 200, x binder, y binder, right associativity).

Notation IO := [set input; output].

Section multigraph_plus.
Variables (Lv Le : setoid) (G : graph Le Lv).
Implicit Types (x y : G).

Definition incident x e := x \in [set source e; target e].
Definition edges_at x := [set e | incident x e].

Definition edges_in (V : {set G}) := \bigcup_(x in V) edges_at x.

Lemma consistentD V : consistent (~: V) (~: edges_in V).
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
  arc e x u y <-> arc e y u° x.
Proof. 
  rewrite /arc; split; move => [[-> -> A]|[-> -> A]].
Admitted.

Lemma add_edge_arc x y u : @arc (add_edge G x y u) None x u y.
Admitted.

Lemma add_edge_arc' x y x' y' u u' e : 
  @arc G e x u y -> @arc (add_edge G x' u' y') (Some e) x u y.
Admitted.

Lemma edges_at_add_edgeT x u y z: z \in [set x;y] -> 
  edges_at (add_edge G x y u) z = None |: Some @: edges_at z.
Admitted.

Lemma edges_at_add_edgeN x u y z: z \notin [set x;y] -> 
  edges_at (add_edge G x y u) z = Some @: edges_at z.
Admitted.

Lemma edges_in1 (x : G) : edges_in [set x] = edges_at x. 
Proof. by rewrite /edges_in big_set1. Qed.

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
Variables (G : lgraph) (z : G) (Hz : z \notin IO).

Lemma del_vertex_proof : [disjoint [set z] & IO].
Admitted.

Definition del_vertex := del_vertices [set z] del_vertex_proof.


Lemma edges_at_del_vertices (x : del_vertex) :
  edges_at del_vertex x = [set e : edge del_vertex | val e \in edges_at (val x)].
Admitted.

Lemma edges_at_del_vertices0 x : edges_at (val x) \subset edges_at z ->
  edges_at del_vertex x = set0.
Proof. rewrite edges_at_del_vertices. 
Admitted.

Lemma del_vertex_IO x (Hx : x \in [set~ z]) : x \notin IO -> (Sub x Hx : del_vertex) \notin IO.
Proof. by rewrite !inE -!val_eqE /=. Qed.

Lemma del_vertex_IO' (x : del_vertex) : x \notin IO -> val x \notin IO.
Admitted.

Lemma del_vertex_arc x y u e (Hx : x \in [set~ z]) (Hy : y \in [set~ z]) (He : e \in ~: edges_in [set z] ):
  arc e x u y -> @arc del_vertex (Sub e He) (Sub x Hx) u (Sub y Hy). 
Admitted.

End DelVertex.

Arguments arc : clear implicits.
Arguments del_vertex : clear implicits.

Definition del_edges (G : lgraph) (E : {set edge G}) := 
  point (remove_edges E) input output.
Arguments del_edges : clear implicits.

Notation del_edge G e := (del_edges G [set e]).



Lemma add_test_arc (G : lgraph) (e : edge G) x y z u a :
  arc G e x u y -> arc (add_test G z a) e x u y.
Admitted.

Lemma edges_at_test (G : lgraph) a (x y : G) :
  @edges_at _ _ (add_test G x a) y = edges_at y.
Admitted.

Arguments add_test_arc [G e x y z u a].

Universe S.

Variant Rule := RULE_V1 | RULE_V2 | RULE_E1 | RULE_E2.

(* TOTHINK: Put the the add_test below the del_vertex to avoid the dependency? *)
Inductive step : lgraph -> lgraph -> Type@{S} := 
| step_v1 G x z e (Hz : z \notin IO) (Hx : (* x \in [set~ z]) *) x != z) u:  
    arc G e x u z -> edges_at z = [set e] ->
    step G (del_vertex (add_test G x [dom(u·vlabel z)]) z Hz)
    (* step G (add_test (del_vertex G z Hz) (Sub x Hx) [dom(u·vlabel z)]) *)
| step_v2 G x y z e1 e2 (Hz : z \notin IO) (Hx : x \in [set~ z]) (Hy : y \in [set~ z]) u v : 
    arc G e1 x u z -> arc G e2 z v y -> edges_at z = [set e1;e2] -> e1 != e2 ->
    (* step G (del_vertex (add_edge G x y (u·vlabel z·v)) z Hz). *)
    step G (add_edge (del_vertex G z Hz) (Sub x Hx) (Sub y Hy) (u·vlabel z·v))
| step_e1 G e x : 
    source e = x -> target e = x -> 
    step G (add_test (del_edge G e) x [1∥elabel e])
| step_e2 G e1 e2 x y u v : 
    arc G e1 x u y -> arc G e2 x v y -> x != y ->
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


Ltac GlGr :=
  match goal with 
    |- context[(steps ?G _ * steps ?H _)%type] => set Gl := G; set Gr := H
  end.

Require Import set_tac.

(* Ltac confluence_tac := *)

(* Set Printing Existential Instances. *)

Tactic Notation "inst" := 
  unshelve instantiate (1 := ltac: (apply: id)); first try assumption.
Tactic Notation "inst" tactic(tac) := 
  inst; first match goal with 
                |- ?G => let S := fresh "S" in have S : G; [abstract by tac| exact: S]
              end.
Tactic Notation "h_abstract" tactic(tac) := 
       match goal with 
         |- ?G => let S := fresh "S" in have S : G; [abstract by tac| exact: S]
       end.

(** liso lemmas *)

Notation "G  \  [ x , Hx ]" := (del_vertex G x Hx) (at level 29,left associativity).
Notation "G ≅ H" := (liso G H) (at level 45).

Lemma cnvtst (u : test) : u° ≡ u.
Admitted.

Arguments del_vertex_IO [G z Hz x Hx].
Arguments del_vertex_IO' [G z Hz x].

Lemma del_vertex_val (G : lgraph) z Hz (z' : G \ [z,Hz]) : z \in [set~ val z'].
Admitted.
Arguments del_vertex_val [G z Hz z'].

Set Nested Proofs Allowed.

Section liso.
  Variable (G : lgraph).

  Lemma liso_add_edge_congr H (l : G ≅ H) x u y : G ∔ [x, u, y] ≅ H ∔ [l x, u, l y].
  Admitted.

  Lemma del_vertexC z Hz (z' : G \ [z,Hz]) Hz' : 
    G \ [z,Hz] \ [z', Hz'] ≅ G \ [val z', del_vertex_IO' Hz'] \ [Sub z del_vertex_val, del_vertex_IO Hz]. 
  Admitted.
  
    
  Lemma sub1 (z x : G) Hz (z' : G \ [z, Hz]) Hx (Hx' : Sub x Hx \in [set~ z']) : x \in [set~ sval z'].
  Admitted.

  Lemma sub2 (z x : G) Hz (z' : G \ [z, Hz]) Hz' Hx (Hx' : Sub x Hx \in [set~ z']) :
    (Sub x (sub1 Hx') : G \ [val z', del_vertex_IO' Hz']) \in [set~ Sub z del_vertex_val].
  Admitted.

  Lemma del_vertexCE z Hz z' Hz' x Hx Hx' : 
    @del_vertexC z Hz z' Hz' (Sub (Sub x Hx) Hx') = Sub (Sub x (sub1 Hx')) (sub2 Hz' Hx') . 
  Admitted.
  
  Lemma liso_del_tst x Hx y Hy a :
    liso (add_test (G \ [x,Hx]) (Sub y Hy) a) (add_test G y a \ [x,Hx]).
  Admitted.

  Lemma liso_add_edgeC x y u : liso (add_edge G x y u) (add_edge G y x u°).
  Admitted.

  Lemma liso_add_edge_weq x y u v : u ≡ v -> liso (add_edge G x y u) (add_edge G x y v).
  Admitted.
End liso.

Arguments edges_at [Lv Le] G _.
Arguments edges_in [Lv Le] G _.

Local Notation "[prf  X ]" := (ssr_have X _ _).
Local Notation "⌈ x ⌉" := (Sub x _) (format "⌈ x ⌉") : sub_scope.
Local Notation "G  \  x" := (del_vertex G x _) (at level 30) : sub_scope.

Lemma liso_delv_adde {G z Hz x y Hx Hy u} : 
  G \ [z,Hz] ∔ [Sub x Hx,u,Sub y Hy] ≅ G ∔ [x,u,y] \ [z,Hz]. 
Admitted.

Lemma liso_adde_addt {G z a x y u} :
  G[tst z <- a] ∔ [x,u,y] ≅ G ∔ [x,u,y] [tst z <- a].
Admitted.
Lemma liso_adde_addtE {G z a x y u} k :
  (@liso_adde_addt G z a x y u k = k)*((@liso_adde_addt G z a x y u)^-1 k = k).
Admitted.  

Lemma liso_delv_proof {G H z} {l : G ≅ H} : z \notin IO -> l z \notin IO. 
Admitted.
Lemma liso_delv_congr {G H z Hz} (l : G ≅ H) :
  G \ [z,Hz] ≅ H \ [l z, liso_delv_proof Hz].
Admitted.

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
  destruct S' as [*|G x' y' z' e1' e2' Hz' Hx' Hy' u' v' Ae1' Ae2' Iz' D'|*|*]; try done; move => _.
  - (* Case V1 / V1 *) admit.
  - (* Case V1 / V2 *) 
    have Dz : z != z' by admit. (* different degree *)
    case: (boolP (z \in [set x';y'])) => [z_xy'|xD'].
    + wlog ? : x' y' Hx' Hy' e1' e2' u' v' Ae1' Ae2' Iz' D' {z_xy'} / z = y'. 
      { move => W. rewrite !inE in z_xy'. case/orb_sum : z_xy' => /eqP ?; subst z.
        - move/(_ _ _ Hy' Hx' e2' e1' v'° u'°) in W. 
          case: W; rewrite -?arcC // 1?setUC 1?eq_sym //. 
          move => Hl [Hr] [[steps_l steps_r] liso_lr].
          exists Hl; exists Hr. repeat split => //. apply: trans_steps steps_r. 
          apply: liso_step. rewrite -> liso_add_edgeC. apply: liso_add_edge_weq. 
          by rewrite !cnvdot cnvtst dotA.
        - exact: W Iz' _ _ . }
      subst z. 
      have [? ?] : e2' = e /\ z' = x ; subst. admit. 
      do 2 eexists; repeat split. 
      * (* x is preserved and its only incident edge in Gl is  e1' *)
        apply step_step. apply: step_v1. 
        3: apply: del_vertex_arc. 6:apply: add_test_arc Ae1'.
        inst (move: (Hy'); rewrite !inE eq_sym).
        exact: del_vertex_IO.
        by rewrite -val_eqE /= -in_set1 -in_setC. 
        admit. 
        admit.
        rewrite edges_at_del_vertices edges_at_test /= Iz'. admit. 
      * (* the x'z-edge is now the only edge incident at z *)
        apply step_step. apply step_v1 with None. 2:apply add_edge_arc. admit.
        rewrite edges_at_add_edgeT ?inD //. 
        rewrite edges_at_del_vertices0 ?imset0 ?setU0 //= Iz Iz'. apply: subsetUr. 
      * inst (exact: del_vertex_IO). 
        (* repeat match goal with |- context [Sub _ (?x ?y)] => let S := fresh "sub" in set S := x y end. *)
        (* set X := _ _ _ _ _ _ _ _ _ _. *)
        (* erewrite -> liso_del_tst. *) admit.
    + (* the independent case *)
      have He1 : e1' \in ~: edges_in (G[tst x <- [dom (u·vlabel z)]]) [set z]. admit.
      have He2 : e2' \in ~: edges_in (G[tst x <- [dom (u·vlabel z)]]) [set z]. admit.
      have He : e \in ~: edges_in G [set z']. admit.
      have D : x != z'. admit. (* both edges at z' lead to vertices distinct from z *)
      do 2 eexists; repeat split.
      * apply step_step. apply: step_v2. 
        4,5: apply: del_vertex_arc; last apply: add_test_arc.
        7: apply Ae1'. 9: apply Ae2'.
        (* side conditions - should be automatable *)
        inst (rewrite !inE eq_sym).  
        h_abstract exact: del_vertex_IO.
        inst set_tac.
        h_abstract (rewrite !inE -val_eqE /=; set_tac).
        inst set_tac. 
        h_abstract (rewrite !inE -val_eqE /=; by set_tac). 
        done.
        done.
        h_abstract (by rewrite edges_at_del_vertices edges_at_test /= Iz' set2_Sub).
        by rewrite -val_eqE. 
      * apply: step_step. apply: step_v1. 
        3: apply: add_edge_arc'; last apply: del_vertex_arc; last apply Ae.
        inst set_tac.
        h_abstract exact: del_vertex_IO.
        inst set_tac. 
        h_abstract by rewrite -val_eqE. 
        assumption.
        admit.
      * Open Scope sub_scope.
        apply: liso_comp. apply: liso_add_edge_congr. apply: del_vertexC.
        rewrite del_vertexCE. rewrite del_vertexCE. rewrite [val _]/=.
        apply: liso_comp. apply: liso_delv_adde.
        apply: liso_comp _ (liso_sym _). 
        2:{. apply: liso_delv_congr. apply: liso_sym. apply liso_adde_addt. }
        rewrite ![liso_sym _ _]/=. Close Scope sub_scope.
        (* hrmpf *) move: (liso_delv_proof _). 
        

          
  - (* Case V1 / E1 *) admit.
  - (* Case V1 / E2 *) admit.
  - (* Case V2 / V2 *) admit.
  - (* Case V2 / E1 *) admit.
  - (* Case V2 / E2 *) admit.
  - (* Case E1 / E1 *) admit.
  - (* Case E1 / E2 *) admit.
  - (* Case E2 / E2 *) admit.
Admitted.

