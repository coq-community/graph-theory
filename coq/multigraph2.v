Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries finite_quotient bij equiv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

Require Import digraph.

(** * Directed Multigraphs *)

Record edge_mixin_of (V : Type) := EdgeMixin { edge_ : finType; source_ : edge_ -> V; target_ : edge_ -> V }.
Record p2_mixin_of (V : Type) := P2Mixin { input_ : V; output_ : V }.

Module mgraph.
Section ClassDef.

Record class_of (V: Type) := Class { base : Finite.class_of V ; mixin : edge_mixin_of V }.

Structure type := Pack { vertex ; _ : class_of vertex }.
Local Coercion vertex : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun b bT & phant_id (Finite.class bT) b => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT (base class).
Definition choiceType := @Choice.Pack cT (base class).
Definition finType := @Finite.Pack cT (base class).

End ClassDef.

Module Import Exports.
Coercion vertex : type >-> Sortclass. 
Coercion base : class_of >-> Finite.class_of.
Coercion mixin : class_of >-> edge_mixin_of.
Canonical eqType.
Canonical choiceType.
Canonical finType.
Notation mGraph := type.
End Exports.
End mgraph.
Import mgraph.Exports.

Definition edge (G : mGraph) := edge_ (mgraph.mixin (mgraph.class G)).
Definition source (G : mGraph) (e : edge G) : G := source_ e.
Definition target (G : mGraph) (e : edge G) : G := target_ e.


(** Defining concepts for mgraphs *)


(* Definition mgraph_rel (G : mGraph) : rel G :=  *)
(*   fun x y => [exists e, (source e == x) && (target e == y)]. *)

(* Definition mgraph_relType (G : mGraph) := DiGraph (@mgraph_rel G). *)
(* Coercion mgraph_relType : mGraph >-> diGraph. *)

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

End Walk. 

Definition MGraph (V E : finType) (s t : E -> V) : mGraph := Eval hnf in
 mgraph.Pack (mgraph.Class (Finite.class V) (EdgeMixin s t)).

Definition add_vertex (G : mGraph) : mGraph := 
  Eval hnf in MGraph (Some \o @source G) (Some \o @target G).

Lemma add_vertex_isolated (G : mGraph) (e : edge (add_vertex G)) : 
  source e != None. 
Proof. by []. Qed.

Module lmgraph.
Section ClassDef.
Variables (Lv Le : Type).

Record mixin_of (V E : Type) := Mixin { vlabel : V -> Lv; elabel : E -> Le }.

Record class_of (V: Type) := Class { base : mgraph.class_of V ; 
                                     mixin : mixin_of V (edge (mgraph.Pack base)) }.

Structure type := Pack { vertex ; _ : class_of vertex }.
Local Coercion vertex : type >-> Sortclass. 
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

(* TOTHINK *)
(* Definition pack m := *)
(*   fun b bT & phant_id (mgraph.class bT) b => Pack (@Class T b m). *)


Definition eqType := @Equality.Pack cT (base class).
Definition choiceType := @Choice.Pack cT (base class).
Definition finType := @Finite.Pack cT (base class).
Definition mGraph := @mgraph.Pack cT (base class).

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

Definition subgraph_for : mGraph := 
  @MGraph [finType of { x | x \in V }]
          [finType of { e | e \in E }]
          (fun e => Sub (source (val e)) (sub_source_proof (valP e)))
          (fun e => Sub (target (val e)) (sub_target_proof (valP e))).

End SubGraph.


Section lmgraph_theory.
Variables Lv Le : Type.

Definition vlabel (G : lmgraph Lv Le) : G -> Lv := lmgraph.vlabel (lmgraph.mixin (lmgraph.class G)).
Definition elabel (G : lmgraph Lv Le) : edge G -> Le := lmgraph.elabel (lmgraph.mixin (lmgraph.class G)).

Definition edge_word_of (G : lmgraph Lv Le) (x y : G) p (w : walk x y p) : seq Le := 
  [seq elabel e | e <- p].

Definition LMGraph_ (G : mGraph) (lv : G -> Lv) (le : edge G -> Le) : lmgraph Lv Le := 
  lmgraph.Pack (lmgraph.Class (LabelMixin lv le)).

Definition LMGraph (V E : finType) (s t : E -> V) (lv : V -> Lv) (le : E -> Le) : lmgraph Lv Le := 
  @LMGraph_ (MGraph s t) lv le.
  
Definition add_lvertex (G : lmgraph Lv Le) (a : Lv) : lmgraph Lv Le := Eval hnf in
  @LMGraph_ (add_vertex G) 
            (fun x : add_vertex G => if x is Some x' then vlabel x' else a) 
            (fun e : edge (add_vertex G) => elabel e).

Definition sublgraph_for (G : lmgraph Lv Le) V E (con : @consistent G V E) : lmgraph Lv Le := Eval hnf in
  (@LMGraph_ (subgraph_for con) 
             (fun x => vlabel (val x)) 
             (fun e => elabel (val e))).
