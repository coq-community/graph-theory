Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries finite_quotient bij equiv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

Require Import digraph.

(** * Directed Multigraphs *)

Record p2_mixin_of (V : Type) := P2Mixin { input_ : V; output_ : V }.

Module mgraph.
Section ClassDef.

Record mixin_of (V E : Type) := EdgeMixin { source : E -> V; target : E -> V }.

Record class_of (V E : Type) := Class { vbase : Finite.class_of V ; 
                                        ebase : Finite.class_of E ;
                                        mixin : mixin_of V E }.

Structure type := Pack { vertex ; edge ; _ : class_of vertex edge }.
Local Coercion vertex : type >-> Sortclass. 
Variables (V E : Type) (cT : type).
Definition class := let: Pack _ _ c as cT' := cT return class_of (vertex cT') (edge cT') in c.
Definition clone c of phant_id class c := @Pack V E c.

(* Let xT := let: Pack T _ := cT in T. *)
(* Notation xclass := (class : class_of xT). *)

(* Definition pack m := *)
(*   fun b bT & phant_id (Finite.class bT) b => Pack (@Class T b m). *)

Definition eqType := @Equality.Pack cT (vbase class).
Definition choiceType := @Choice.Pack cT (vbase class).
Definition finType := @Finite.Pack cT (vbase class).
Definition EeqType := @Equality.Pack (edge cT) (ebase class).
Definition EchoiceType := @Choice.Pack (edge cT) (ebase class).
Definition EfinType := @Finite.Pack (edge cT) (ebase class).

End ClassDef.

Module Import Exports.
Coercion vertex : type >-> Sortclass. 
Coercion vbase : class_of >-> Finite.class_of.
Coercion mixin : class_of >-> mixin_of.
Canonical eqType.
Canonical choiceType.
Canonical finType.
Canonical EeqType.
Canonical EchoiceType.
Canonical EfinType.
Notation mGraph := type.
Notation edge := edge.
Notation vertex := vertex.
Notation EdgeMixin := EdgeMixin.
End Exports.
End mgraph.
Import mgraph.Exports.

Definition source (G : mGraph) := mgraph.source (mgraph.class G).
Definition target (G : mGraph) := mgraph.target (mgraph.class G).


(** Test: Defining concepts for mgraphs *)

Section Walk.
Variable (G : mGraph).
Implicit Types (x y z : G) (e : edge G) (w : seq (edge G)).

Fixpoint walk x y w := 
  if w is e :: w' then (source e == x) && walk (target e) y w' else x == y.

Definition eseparates x y (E : {set edge G}) := 
  forall w, walk x y w -> exists2 e, e \in E & e \in w.

Definition line_graph := digraph.DiGraph [rel e1 e2 : edge G | target e1 == source e2].

Lemma walk_of_line e1 e2 (p : @Path line_graph e1 e2) :
  walk (source e1) (target e2) (nodes p).
Proof.
  case: p => p pth_p. rewrite nodesE /= eqxx /=. 
  elim: p e1 pth_p => [e1 pth_p|e w IHw e1]. 
  - by rewrite (pathp_nil pth_p) /= eqxx.
  - by rewrite pathp_cons /edge_rel /= eq_sym => /andP [-> /IHw].
Qed.

Lemma line_of_walk x y w : walk x y w -> ~~ nilp w -> 
  exists e1 e2 (p : @Path line_graph e1 e2), [/\ source e1 = x, target e2 = y & nodes p = w].
Proof.
  elim: w x => //= e [|e' w] IH x /andP[src_e walk_w] _. 
  - exists e. exists e. exists (@idp line_graph e). 
    rewrite nodesE /idp /= (eqP src_e). split => //. exact/eqP.
  - case: (IH _ walk_w _) => // e1 [e2] [p] [P1 P2 P3].
    have ee1 : @edge_rel line_graph e e1 by apply/eqP; rewrite P1.
    exists e. exists e2. exists (pcat (edgep ee1) p). rewrite (eqP src_e) P2. split => //.
    rewrite !nodesE /= in P3 *. case: P3 => ? ?. by subst.
Qed.

(* Definition mgraph_rel (G : mGraph) : rel G :=  *)
(*   fun x y => [exists e, (source e == x) && (target e == y)]. *)

(* Definition mgraph_relType (G : mGraph) := DiGraph (@mgraph_rel G). *)
(* Coercion mgraph_relType : mGraph >-> diGraph. *)

End Walk. 


(** Constructions on mgraphs *)

Definition MGraph (V E : finType) (s t : E -> V) : mGraph := Eval hnf in
 mgraph.Pack (mgraph.Class (Finite.class V) (Finite.class E) (EdgeMixin s t)).

Definition add_vertex (G : mGraph) : mGraph := 
  Eval hnf in MGraph (Some \o @source G) (Some \o @target G).

Definition add_edge (G : mGraph) (x y : G) : mGraph := 
  Eval hnf in MGraph (fun e => if e is Some e' then @source G e' else x)
                     (fun e => if e is Some e' then @target G e' else y).

Definition del_edge (G : mGraph) (e : edge G) : mGraph := 
  Eval hnf in MGraph (fun e' : { e' | e' != e } => source (val e'))
                     (fun e' : { e' | e' != e } => target (val e')).

Lemma add_vertex_isolated (G : mGraph) (e : edge (add_vertex G)) : 
  source e != None. 
Proof. by []. Qed.

Section DelVertex.
Variables (G : mGraph) (z : G).
Let V := { x : G | x != z }.
Let E := { e : edge G | (source e != z) && (target e != z) }.

Lemma del_vertex_source (e : E) : source (val e) != z.
Proof. by case/andP : (valP e). Qed.

Lemma del_vertex_target (e : E) : target (val e) != z.
Proof. by case/andP : (valP e). Qed.


Definition del_vertex : mGraph := 
  MGraph (fun e : E => Sub (source (val e)) (del_vertex_source e) : V)
         (fun e : E => Sub (target (val e)) (del_vertex_target e) : V).

End DelVertex.

Module lmgraph.
Section ClassDef.
Variables (Lv Le : Type).

Record mixin_of (V E : Type) := Mixin { vlabel : V -> Lv; elabel : E -> Le }.

Record class_of (V E : Type) := Class { base : mgraph.class_of V E ; 
                                        mixin : mixin_of V E }.

Record type := Pack { vertex ; edge ; _ : class_of vertex edge }.
Local Coercion vertex : type >-> Sortclass. 
Variables (V E : Type) (cT : type).
Definition class := let: Pack _ _ c as cT' := cT return class_of (vertex cT') (edge cT') in c.
Definition clone c of phant_id class c := @Pack V E c.

(* Let xT := let: Pack T _ := cT in T. *)
(* Notation xclass := (class : class_of xT). *)

(* TOTHINK *)
(* Definition pack m := *)
(*   fun b bT & phant_id (mgraph.class bT) b => Pack (@Class T b m). *)

Definition eqType := @Equality.Pack cT (base class).
Definition choiceType := @Choice.Pack cT (base class).
Definition finType := @Finite.Pack cT (base class).
Definition mGraph := @mgraph.Pack cT (edge cT) (base class).
(* TOTHINK: do we want to repeat the edge-type instances? *)

End ClassDef.

Module Import Exports.
Coercion vertex : type >-> Sortclass. 
Coercion base : class_of >-> mgraph.class_of.
Coercion mixin : class_of >-> mixin_of.
Canonical eqType.
Canonical choiceType.
Canonical finType.
Canonical mGraph.
Coercion mGraph : type >-> mgraph.type. (* enables writing [edge G] for labeled graphs *)
Notation lmgraph := type.
Notation LabelMixin := Mixin.
End Exports.
End lmgraph.
Import lmgraph.Exports.

Section SubGraph.
Variables (G : mGraph) (V : {set G}) (E : {set edge G}).

Definition consistent := forall e, e \in E -> (source e \in V) * (target e \in V).
Hypothesis con : consistent.

Lemma sub_source_proof e : e \in E -> source e \in V. by case/con. Qed.
Lemma sub_target_proof e : e \in E -> target e \in V. by case/con. Qed.

Definition subgraph_for : mGraph := Eval hnf in
  MGraph (fun e : { e | e \in E } => Sub (source (val e)) (sub_source_proof (valP e)) : { x | x \in V })
         (fun e => Sub (target (val e)) (sub_target_proof (valP e))).


(* Definition subgraph_for : mGraph := Eval hnf in  *)
(*   @MGraph [finType of { x | x \in V }] *)
(*           [finType of { e | e \in E }] *)
(*           (fun e => Sub (source (val e)) (sub_source_proof (valP e))) *)
(*           (fun e => Sub (target (val e)) (sub_target_proof (valP e))). *)

End SubGraph.


Section lmgraph_theory.
Variables Lv Le : Type.

Definition vlabel (G : lmgraph Lv Le) : G -> Lv := lmgraph.vlabel (lmgraph.mixin (lmgraph.class G)).
Definition elabel (G : lmgraph Lv Le) : edge G -> Le := lmgraph.elabel (lmgraph.mixin (lmgraph.class G)).

Definition edge_word_of (G : lmgraph Lv Le) (x y : G) p (w : walk x y p) : seq Le := 
  [seq elabel e | e <- p].

Definition LMGraph (G : mGraph) (lv : G -> Lv) (le : edge G -> Le) : lmgraph Lv Le := 
  lmgraph.Pack (lmgraph.Class (mgraph.class G) (LabelMixin lv le)).

Definition LMGraph_ (V E : finType) (s t : E -> V) (lv : V -> Lv) (le : E -> Le) : lmgraph Lv Le := 
  @LMGraph (MGraph s t) lv le.
  
Definition add_lvertex (G : lmgraph Lv Le) (a : Lv) : lmgraph Lv Le := Eval hnf in
  @LMGraph (add_vertex G) 
           (fun x : add_vertex G => if x is Some x' then vlabel x' else a) 
           (fun e : edge (add_vertex G) => elabel e).

Definition add_ledge (G : lmgraph Lv Le) (x y : G) (u : Le) : lmgraph Lv Le := Eval hnf in
  @LMGraph (add_edge x y) 
           (@vlabel _)
           (fun e => if e is Some e' then elabel e' else u).

Definition del_ledge (G : lmgraph Lv Le) (e : edge G) : lmgraph Lv Le := Eval hnf in
  @LMGraph (del_edge e) (@vlabel _) (fun e' => elabel (val e')).

Definition sublgraph_for (G : lmgraph Lv Le) V E (con : @consistent G V E) : lmgraph Lv Le := Eval hnf in
  (@LMGraph (subgraph_for con) 
            (fun x => vlabel (val x)) 
            (fun e => elabel (val e))).

Definition del_lvertex (G : lmgraph Lv Le) (x : G) := 
  @LMGraph (del_vertex x) (fun x => vlabel (val x)) (fun e => elabel (val e)).

Definition update_vlabel (G : lmgraph Lv Le) (z:G) a := Eval hnf in
  @LMGraph G (fun x => if x == z then a else vlabel x) (@elabel _).


End lmgraph_theory.

Arguments LMGraph [Lv Le] G _ _.
Notation Vlabel := (@vlabel _ _ _) (only parsing).
Notation Elabel := (@elabel _ _ _) (only parsing).



Definition lgraph_of (G : mGraph) := Eval hnf in @LMGraph _ _ G (fun _ => tt) (fun _ => tt).


(* Disjoint Union *)

Definition union (G1 G2 : mGraph) : mGraph := Eval hnf in
  @MGraph [finType of G1 + G2]
          [finType of edge G1 + edge G2]
          (sumf (@source G1) (@source G2))
          (sumf (@target G1) (@target G2)).

Definition sumfc (A B C : Type) (f : A -> C) (g : B -> C) := 
  fun z : A + B => match z with inl x => f x | inr x => g x end.

Definition lunion Lv Le (G1 G2 : lmgraph Lv Le) : lmgraph Lv Le :=
  LMGraph (union G1 G2) (sumfc Vlabel Vlabel) (sumfc Elabel Elabel).

Class is_hom (F G : mGraph) (hv: F -> G) (he: edge F -> edge G): Prop := Hom
  { source_hom: forall e, source (he e) = hv (source e);
    target_hom: forall e, target (he e) = hv (target e) }.

Record iso (F G: mGraph): Type := Iso
  { iso_v:> bij F G;
    iso_e: bij (edge F) (edge G);
    iso_hom: is_hom iso_v iso_e }.

Notation "h '.e'" := (iso_e h) (at level 2, left associativity). 
Existing Instance iso_hom.

Class respects_labels Lv Le (F G : lmgraph Lv Le) (h : iso F G) : Prop := LHom
  { vlabel_hom: forall x, vlabel (h x) = vlabel x ;
    elabel_hom: forall e, elabel (h.e e) = elabel e }.

Record liso Lv Le (F G: lmgraph Lv Le): Type := LIso
  { iso_of_liso :> iso F G ;
    liso_respects : respects_labels iso_of_liso }.


Section EdgeLabeled.
Variable (sym : eqType).
Definition Graph V E s t l : lmgraph [eqType of unit] sym := 
  @LMGraph_ [eqType of unit] sym V E s t (fun => tt) l.


Notation vfun := (fun x : void => match x with end).  
Definition unit_graph := Eval simpl in @Graph [finType of unit] _ vfun vfun vfun.
Definition two_graph := @Graph [finType of bool] _ vfun vfun vfun.
Definition edge_graph (a : sym) := Graph (fun _ : unit => false) (fun _ => true) (fun _ => a).

Check (forall x : unit_graph, x = x).

(** TOTHINK: is there a proper way to make this canonical ? *)
(* Canonical lgraph_of. *)
(* Coercion lgraph_of : mGraph >-> lmgraph. *)
(* Fail Goal (forall (G : mGraph) (x : G), vlabel x = tt). *)
(* Goal (forall (G : mGraph) (x : G), @vlabel _ _ (lgraph_of G) x = tt). done. Qed. *)

End EdgeLabeled.

Module p2graph.
Section ClassDef.
Variables (Lv Le : Type).

Record mixin_of (V : Type) := Mixin { input : V ; output : V }.

Record class_of (V E : Type) := Class { base : lmgraph.class_of Lv Le V E ; 
                                        mixin : mixin_of V }.

Record type := Pack { vertex ; edge ; _ : class_of vertex edge }.
Local Coercion vertex : type >-> Sortclass. 
Variables (V E : Type) (cT : type).
Definition class := let: Pack _ _ c as cT' := cT return class_of (vertex cT') (edge cT') in c.
Definition clone c of phant_id class c := @Pack V E c.

Definition eqType := @Equality.Pack cT (base class).
Definition choiceType := @Choice.Pack cT (base class).
Definition finType := @Finite.Pack cT (base class).
Definition mGraph := @mgraph.Pack cT (edge cT) (base class).
Definition lmgraph := @lmgraph.Pack Lv Le cT (edge cT) (base class).

(* TOTHINK: do we want to repeat the edge-type instances? *)
End ClassDef.

Module Import Exports.
Coercion vertex : type >-> Sortclass. 
Coercion base : class_of >-> lmgraph.class_of.
Coercion mixin : class_of >-> mixin_of.
Canonical eqType.
Coercion eqType : type >-> Equality.type.
Canonical choiceType.
Canonical finType.
Canonical mGraph.
Canonical lmgraph.
Coercion mGraph : type >-> mgraph.type. (* enables writing [edge G] for labeled graphs *)
Coercion lmgraph : type >-> lmgraph.type.
Notation p2graph := type.
Notation PointMixin := Mixin.
End Exports.
End p2graph.
Import p2graph.Exports.

Definition input Lv Le (G : p2graph Lv Le) := p2graph.input (p2graph.class G).
Definition output Lv Le (G : p2graph Lv Le) := p2graph.output (p2graph.class G).
Definition point Lv Le (G : lmgraph Lv Le) (x y : G) : p2graph Lv Le := 
  p2graph.Pack (p2graph.Class (lmgraph.class G) (PointMixin x y)).

Arguments input [Lv Le G].
Arguments output [Lv Le G].
Arguments point [Lv Le] G x y.

Notation IO := [set input; output].

(** Experiments *)

Require Import term.


Section s.
Variable sym : eqType.
Notation term := (term sym).
Notation test := (test sym).

Definition tl2_graph := p2graph test term.

Definition cnv' (b: bool) (u: term): term :=
  if b then u° else u.
Definition elabel' (G: tl2_graph) (b: bool) (e: edge G): term :=
  cnv' b (elabel e).
Definition source' (G: tl2_graph) (b: bool) (e: edge G): G :=
  if b then target e else source e.
Definition target' (G: tl2_graph) (b: bool) (e: edge G): G :=
  if b then source e else target e.

Universe L.
Record wiso (F G: tl2_graph): Type@{L} :=
  Wiso {
      wiso_v:> bij F G;
      wiso_e: bij (edge F) (edge G);
      wiso_dir: edge F -> bool;
      vlabel_wiso: forall v, term_of (vlabel (wiso_v v)) ≡ vlabel v;
      elabel_wiso: forall e, elabel' (wiso_dir e) (wiso_e e) ≡ elabel e;
      source_wiso: forall e, source' (wiso_dir e) (wiso_e e) = wiso_v (source e);
      target_wiso: forall e, target' (wiso_dir e) (wiso_e e) = wiso_v (target e);
      wiso_input: wiso_v input = input;
      wiso_output: wiso_v output = output }.

Notation "h '.e'" := (wiso_e h) (at level 2, left associativity, format "h '.e'"). 
Notation "h '.d'" := (wiso_dir h) (at level 2, left associativity, format "h '.d'"). 

Instance liso_Equivalence: CRelationClasses.Equivalence wiso. Admitted.

Section DelVertex2.
Variables (G : tl2_graph) (z : G) (Hz : z \notin IO).

Definition del_vertex_input : input != z.
Admitted.

Definition del_vertex_output : output != z.
Admitted.

Definition del_vertex2 : tl2_graph := Eval hnf in 
  point (del_lvertex z) (Sub input del_vertex_input) (Sub output del_vertex_output).

Definition Sub_delv2 x (Hx : x != z) : del_vertex2 := Sub x Hx.

Lemma del_vertex_IO x (Hx : x != z) : x \notin IO -> @Sub_delv2 x Hx \notin IO.
Proof. by rewrite !inE -!val_eqE /=. Qed.

Lemma del_vertex_IO' (x : del_vertex2) : x \notin IO -> val x \notin IO.
Admitted.

End DelVertex2.

Definition add_vertex2 (G : tl2_graph) (a : test) := Eval hnf in
  point (add_lvertex G a) (Some input) (Some output).

Definition add_edge2 (G : tl2_graph) (x y : G) u := Eval hnf in
  point (add_ledge x y u) input output.

Definition add_test2 (G : tl2_graph) (x :G) (a : test) := Eval hnf in
  point (update_vlabel x [vlabel x·a]) input output.


Arguments Sub_delv2 [G z Hz] x Hx.
Arguments del_vertex2 : clear implicits.
Arguments add_vertex2 : clear implicits.
Arguments add_edge2 : clear implicits.
Arguments add_test2 : clear implicits.

Notation "G  \  [ x , Hx ]" := (del_vertex2 G x Hx) (at level 29,left associativity).
Notation "G ∔ [ x , u , y ]" := (add_edge2 G x y u) (at level 20,left associativity).
Notation "G ∔ a" := (add_vertex2 G a) (at level 20, left associativity).
Notation "G [tst x <- a ]" := (add_test2 G x a) (at level 20, left associativity, format "G [tst  x  <-  a ]").
Notation "G ≅ H" := (wiso G H) (at level 45).

Lemma del_vertex_val (G : tl2_graph) z Hz (z' : G \ [z,Hz]) : z != val z'.
Admitted.

Arguments del_vertex_val [G z Hz z'].
Arguments del_vertex_IO [G z Hz x Hx].
Arguments del_vertex_IO' [G z Hz x].

Definition atv (G : tl2_graph) (x : G) (a : test) (y : G) : G[tst x <- a] := y.
Arguments atv [G x a] y.
Definition aev (G : tl2_graph) (x y : G) (u : term) (z : G) : G ∔ [x,u,y] := z.
Arguments aev [G x y u] z.



Section wiso_props.
Variable (G : tl2_graph).

Lemma sub1 (z x : G) Hz (z' : G \ [z, Hz]) Hx (Hx' : Sub_delv2 x Hx != z') : x != sval z'.
Admitted.

Lemma sub2 (z x : G) Hz (z' : G \ [z, Hz]) Hz' Hx (Hx' : Sub x Hx != z') :
  (Sub_delv2 x (sub1 Hx') : G \ [val z', del_vertex_IO' Hz']) != Sub_delv2 z del_vertex_val.
Admitted.

Definition delv2C (z : G) (Hz : z \notin IO) (z' : del_vertex2 G z Hz) (Hz' : z' \notin IO) : 
  G \ [z, Hz] \ [z', Hz'] 
≅ G \ [val z', del_vertex_IO' Hz'] \ [Sub_delv2 z del_vertex_val, del_vertex_IO Hz].
Admitted.

Lemma delv2CE z Hz z' Hz' x Hx Hx' : 
  @delv2C z Hz z' Hz' (Sub_delv2 (Sub_delv2 x Hx) Hx') = Sub_delv2 (Sub_delv2 x (sub1 Hx')) (sub2 Hz' Hx'). 
Admitted.

Definition delv2_tst' x Hx y Hy a :
  G \ [x,Hx] [tst Sub_delv2 y Hy <- a] ≅ G [tst y <- a] \ [x,Hx].
Admitted.

Definition delv2_tst x Hx y Hy a :
  G \ [x,Hx] [tst Sub_delv2 y Hy <- a] ≅ G [tst y <- a] \ [atv x,Hx].
Admitted.

(* Hz only checks up to conversion *)
Lemma delv2_tstE x Hx y Hy a z Hz : 
  @delv2_tst x Hx y Hy a (atv (Sub_delv2 z Hz)) = Sub_delv2 (atv z) Hz.
Admitted.


(* congruence lemmas *)

Lemma adde2_cong (H : tl2_graph) (h : G ≅ H) (x y : G) u : 
  add_edge2 G x y u ≅ add_edge2 H (h x) (h y) u.
Admitted.

Lemma adde2_congE H h x y u z: 
  @adde2_cong H h x y u (aev z) = (aev (h z)).
Admitted.

Lemma wiso_IOn H (h : G ≅ H) (x : G) : x \notin IO -> h x \notin IO. Admitted.
Lemma wisoD H (h : G ≅ H) x y : x != y -> h x != h y. Admitted.

Lemma delv2_cong (H : tl2_graph) (h : G ≅ H) (z : G) Hz :
  G \ [z, Hz] ≅ H \ [h z, wiso_IOn h Hz].
Admitted.

Lemma delv2_congE H h z Hz x Hx : 
  @delv2_cong H h z Hz (Sub_delv2 x Hx) = Sub_delv2 (h x) (wisoD h Hx).
Admitted.

Lemma addt2_cong (H : tl2_graph) (h : G ≅ H) (z : G) a :
  G [tst z <- a] ≅ H [tst h z <- a].
Admitted.

End wiso_props.

Arguments adde2_cong [G H] h [x y u].
Arguments delv2_cong [G H] h [z Hz].
Arguments addt2_cong [G H] h [z a].

Section IsoTest.
Variable (G : tl2_graph).

Goal forall z Hz x Hx a z' Hz1' Hz2' Hz3' (x':G) Hx1' Hx2' Hx3' w (y' : G) Hy1' Hy2' Hy3' Hz2 Hz3 Hx2 Hx3, 
  G \ [z, Hz] [tst Sub_delv2 x Hx <- a] \ [atv (Sub_delv2 z' Hz1'),Hz2'] 
    ∔ [Sub_delv2 (atv (Sub_delv2 x' Hx1')) Hx2', w, Sub_delv2 (atv (Sub_delv2 y' Hy1')) Hy2' ]
≅ G \ [z',Hz3'] ∔ [Sub_delv2 x' Hx3',w,Sub_delv2 y' Hy3'] \ [aev (Sub_delv2 z Hz2),Hz3] 
   [tst Sub_delv2 (aev (Sub_delv2 x Hx2)) Hx3 <- a].
Abort.

(* Notation SUB x := (Sub_delv2 x _). *)

Lemma test_cast:
  forall (z : G) (Hz : z \notin IO) (x : G) (Hx : x != z) (a : test) (z' : G) (Hz1' : z' != z)
    (Hz2' : atv (Sub_delv2 z' Hz1') \notin IO) (Hz3' : z' \notin IO) (x' : G) (Hx1' : x' != z)
    (Hx2' : atv (Sub_delv2 x' Hx1') != atv (Sub_delv2 z' Hz1')) (Hx3' : x' != z') (w : term) 
    (y' : G) (Hy1' : y' != z) (Hy2' : atv (Sub_delv2 y' Hy1') != atv (Sub_delv2 z' Hz1')) 
    (Hy3' : y' != z') (Hz2 : z != z') (Hz3 : aev (Sub_delv2 z Hz2) \notin IO) (Hx2 : x != z')
    (Hx3 : aev (Sub_delv2 x Hx2) != aev (Sub_delv2 z Hz2)),
    ((G \ [z, Hz])[tst Sub_delv2 x Hx <- a] \ [atv (Sub_delv2 z' Hz1'), Hz2'])
      ∔ [Sub_delv2 (atv (Sub_delv2 x' Hx1')) Hx2', w, Sub_delv2 (atv (Sub_delv2 y' Hy1')) Hy2']
  ≅ ((G \ [z', Hz3']) ∔ [Sub_delv2 x' Hx3', w, Sub_delv2 y' Hy3'] \ [aev (Sub_delv2 z Hz2), Hz3])
  [tst Sub_delv2 (aev (Sub_delv2 x Hx2)) Hx3 <- a].
Proof.
  intros z Hz x Hx a z' Hz1' Hz2' Hz3' x' Hx1' Hx2' Hx3' w y' Hy1' Hy2' Hy3' Hz2 Hz3 Hx2 Hx3.
  rewrite -> (adde2_cong (delv2_cong (delv2_tst _ _ _))). 
  rewrite 2!delv2_congE. 
Abort.

Lemma test_cast:
  forall (z : G) (Hz : z \notin IO) (x : G) (Hx : x != z) (a : test) (z' : G) (Hz1' : z' != z)
    (Hz2' : atv (Sub_delv2 z' Hz1') \notin IO) (Hz3' : z' \notin IO) (x' : G) (Hx1' : x' != z)
    (Hx2' : atv (Sub_delv2 x' Hx1') != atv (Sub_delv2 z' Hz1')) (Hx3' : x' != z') (w : term) 
    (y' : G) (Hy1' : y' != z) (Hy2' : atv (Sub_delv2 y' Hy1') != atv (Sub_delv2 z' Hz1')) 
    (Hy3' : y' != z') (Hz2 : z != z') (Hz3 : aev (Sub_delv2 z Hz2) \notin IO) (Hx2 : x != z')
    (Hx3 : aev (Sub_delv2 x Hx2) != aev (Sub_delv2 z Hz2)),
    ((G \ [z, Hz])[tst Sub_delv2 x Hx <- a] \ [atv (Sub_delv2 z' Hz1'), Hz2'])
      ∔ [Sub_delv2 (atv (Sub_delv2 x' Hx1')) Hx2', w, Sub_delv2 (atv (Sub_delv2 y' Hy1')) Hy2']
  ≅ ((G \ [z', Hz3']) ∔ [Sub_delv2 x' Hx3', w, Sub_delv2 y' Hy3'] \ [aev (Sub_delv2 z Hz2), Hz3])
  [tst Sub_delv2 (aev (Sub_delv2 x Hx2)) Hx3 <- a].
Proof.

Timeout 10 Lemma test_wo_cast:
  forall (z : G) (Hz : z \notin IO) (x : G) (Hx : x != z) (a : test) (z' : G) (Hz1' : z' != z)
    (Hz2' : (Sub_delv2 z' Hz1') \notin IO) (Hz3' : z' \notin IO) (x' : G) (Hx1' : x' != z)
    (Hx2' : (Sub_delv2 x' Hx1') != (Sub_delv2 z' Hz1')) (Hx3' : x' != z') (w : term) 
    (y' : G) (Hy1' : y' != z) (Hy2' : (Sub_delv2 y' Hy1') != (Sub_delv2 z' Hz1')) 
    (Hy3' : y' != z') (Hz2 : z != z') (Hz3 : (Sub_delv2 z Hz2) \notin IO) (Hx2 : x != z')
    (Hx3 : (Sub_delv2 x Hx2) != (Sub_delv2 z Hz2)),
    ((G \ [z, Hz])[tst Sub_delv2 x Hx <- a] \ [(Sub_delv2 z' Hz1'), Hz2'])
      ∔ [Sub_delv2 ((Sub_delv2 x' Hx1')) Hx2', w, Sub_delv2 ((Sub_delv2 y' Hy1')) Hy2']
  ≅ ((G \ [z', Hz3']) ∔ [Sub_delv2 x' Hx3', w, Sub_delv2 y' Hy3'] \ [(Sub_delv2 z Hz2), Hz3])
  [tst Sub_delv2 ((Sub_delv2 x Hx2)) Hx3 <- a].
Proof.
  intros z Hz x Hx a z' Hz1' Hz2' Hz3' x' Hx1' Hx2' Hx3' w y' Hy1' Hy2' Hy3' Hz2 Hz3 Hx2 Hx3.
Abort.


Set Printing All.
  


