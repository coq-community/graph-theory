From mathcomp Require Import all_ssreflect.
Require Import finite_quotient preliminaries sgraph multigraph subalgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 

(** * Skeletons *)

Definition sk_rel (G : graph) : rel G := 
  sc [rel x y | (x != y) && [exists e, (source e == x) && (target e == y)]].

Arguments sk_rel G _ _ : clear implicits.

Lemma sk_rel_sym (G : graph) : symmetric (sk_rel G).
Proof. move => x y. by rewrite /sk_rel /sc /= orbC. Qed.

Lemma sk_rel_irrefl (G : graph) : irreflexive (sk_rel G).
Proof. move => x. by rewrite /sk_rel /sc /= !eqxx. Qed.

Definition skeleton (G : graph) := 
  SGraph (@sk_rel_sym G) (@sk_rel_irrefl G).

Lemma skelP (G : graph) (P : G -> G -> Prop) : 
  Symmetric P -> 
  (forall e : edge G, P (source e) (target e)) -> 
  (forall x y : G,  sk_rel _ x y -> P x y).
Proof. 
  move => S H x y. 
  case/orP => /= /andP [_] /existsP [e] /andP [/eqP<- /eqP <-] //.
  exact: S.
Qed.

Lemma decomp_skeleton (G : graph) (T : tree) (D : T -> {set G}) :
  decomp T G D -> sdecomp T (skeleton G) D.
Proof. 
  case => D1 D2 D3. split => //. apply: skelP => // x y. 
  move => [t] A. exists t. by rewrite andbC.
Qed.

Definition ssk_rel (G : graph2) := 
  relU (sk_rel G) (sc [rel x y | [&& x != y, x == g_in & y == g_out]]).

Lemma relU_sym' (T : Type) (e e' : rel T) :
  symmetric e -> symmetric e' -> symmetric (relU e e').
Proof. move => sym_e sym_e' x y /=. by rewrite sym_e sym_e'. Qed.

Lemma sc_sym (T : Type) (e : rel T) : symmetric (sc e).
Proof. move => x y /=. by rewrite orbC. Qed.

Definition add_edge_rel (G:sgraph) (i o : G) := 
  relU (@sedge G) (sc [rel x y | [&& x != y, x == i & y == o]]).

Lemma add_edge_sym (G:sgraph) (i o : G) : symmetric (add_edge_rel i o).
Proof. apply: relU_sym'. exact: sg_sym. exact: sc_sym. Qed.

Lemma add_edge_irrefl (G:sgraph) (i o : G) : irreflexive (add_edge_rel i o).
Proof. move => x /=. by rewrite sg_irrefl eqxx. Qed.

Definition add_edge (G:sgraph) (i o : G) :=
  {| svertex := G;
     sedge := add_edge_rel i o;
     sg_sym := add_edge_sym i o;
     sg_irrefl := add_edge_irrefl i o |}.

Definition sskeleton (G : graph2) := @add_edge (skeleton G) g_in g_out.

(* Lemma ssk_sym (G : graph2) : symmetric (ssk_rel G). *)
(* Proof. apply: relU_sym' (@sk_rel_sym _) _. exact: sc_sym. Qed. *)

(* Lemma ssk_irrefl (G : graph2) : irreflexive (ssk_rel G). *)
(* Proof. move => x /=. by rewrite sk_rel_irrefl eqxx. Qed. *)

(* Definition sskeleton (G : graph2) := SGraph (@ssk_sym G) (@ssk_irrefl G). *)

Lemma sskelP (G : graph2) (P : G -> G -> Prop) : 
  Symmetric P -> 
  (forall e : edge G, P (source e) (target e)) -> 
  (g_in != g_out :> G -> P g_in g_out) ->
  (forall x y : sskeleton G, x -- y -> P x y).
Proof. 
  move => S H IO x y. case/orP. exact: skelP. 
  case/orP => /= /and3P [A /eqP ? /eqP ?];subst; first exact: IO.
  apply: S. exact: IO.
Qed.

Lemma decomp_sskeleton (G : graph2) (T : tree) (D : T -> {set G}) :
  decomp T G D -> compatible D -> sdecomp T (sskeleton G) D.
Proof. 
  case => D1 D2 D3 C. split => //. apply: sskelP  => // x y. 
  move => [t] A. exists t. by rewrite andbC.
Qed.

Lemma sskel_K4_free (u : term) : K4_free (sskeleton (graph_of_term u)).
Proof.
  case: (graph_of_TW2 u) => T [B] [B1 B2 B3].
  exact: TW2_K4_free (decomp_sskeleton B1 B2) _.
Qed.

Lemma skel_sub (G : graph2) : sgraph.subgraph (skeleton G) (sskeleton G).
Proof.
  (* FIXME: This is really obsucre due to the abbiguity of [x -- y] *)
  exists id => //= x y H. right. exact: subrelUl. 
Qed.

Lemma minor_K4_free (G H : sgraph) : 
  minor G H -> K4_free G -> K4_free H.
Proof. move => M F C. apply: F. exact: minor_trans C. Qed.

Lemma skel_K4_free (u : term) : K4_free (skeleton (graph_of_term u)).
Proof. 
  apply: minor_K4_free (@sskel_K4_free u).
  exact: sub_minor (skel_sub _).  
Qed.

(** ** Intervals and Petals *)

(** TOTHINK: define intervals and petals on graph or sgraph, i.e.,
where to add theskeleton casts? *)

Definition sinterval (G : sgraph) (x y : G) := 
  [set z in ~: [set x; y] | 
   connect (restrict (predC1 y) (@sedge G)) x z && 
   connect (restrict (predC1 x) (@sedge G)) y z ].

Definition interval (G : sgraph) (x y : G) := 
  [set x;y] :|: sinterval x y.

Definition point (G : graph) (x y : G) := 
  Eval hnf in @Graph2 G x y.

Fact intervalL (G : sgraph) (x y : G) : 
  x \in interval x y.
Proof. by rewrite !inE eqxx. Qed.

Fact intervalR (G : sgraph) (x y : G) : 
  y \in interval x y.
Proof. by rewrite !inE eqxx !orbT. Qed.

Definition igraph (G : graph) (x y : skeleton G) := 
  @point (induced (interval x y)) 
         (Sub x (intervalL x y)) 
         (Sub y (intervalR x y)).


Definition petal (G : sgraph) (U : {set G}) (x:G) :=
  [set z | [forall y in CP U, x \in cp z y]].

Lemma petal_id (G : sgraph) (U : {set G}) x : x \in petal U x.
Proof. rewrite inE. apply/forall_inP => y _. exact: mem_cpl. Qed.

Definition pgraph (G : graph) (U : {set G}) (x:G) :=
  @point (induced (@petal (skeleton G) U x))
         (Sub x (@petal_id (skeleton G) U x))
         (Sub x (@petal_id (skeleton G) U x)).
