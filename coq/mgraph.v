Require Import Morphisms RelationClasses.
Require CMorphisms CRelationClasses. (* To be used explicitly *)
From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries bij equiv.
Require Export structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

(** * Directed Labeled Multigraphs *)

(** ** labeled directed multigraphs and their operations *)

(* this file subsumes mgraph_jar.v : 
   the notion of multigraph defined here allows labels on vertices and edge-fliping isomorphisms 
   we can recover multigraphs without vertex-labels and non-flipping isomophisms using the [flat_labels] structure
 *)

Section s.
    
Variable L: labels.
Notation Lv := (lv L).  
Notation Le := (le L).
Local Open Scope labels.

(* labelled directed multigraphs (not pointed, Definition 4.4) *)
Set Primitive Projections.
Record graph: Type :=
  Graph {
      vertex:> finType;
      edge: finType;
      endpoint: bool -> edge -> vertex; (* source and target functions *)
      vlabel: vertex -> Lv;
      elabel: edge -> Le }.
Unset Primitive Projections.
Notation source := (endpoint false).
Notation target := (endpoint true).
(* note: 
   - we need everything to be finite to get a terminating rewrite system
   - elsewhere we don't care that the edge type is a finType, it could certainly just be a Type
   - the vertex type has to be an eqType at various places since we regularly compare vertices (e.g., [add_vlabel])
   - the vertex type has to be a finType for the [merge] operation, but only in order to express the new vertex labeling function... we could imagine a [finitary_merge] operation that would not impose this restriction
   - the vertex type has to be finite also when we go to open graphs (although maybe countable would suffice)
 *)

(** ** Basic Operations *)

(* empty graph *)
Definition void_graph := Graph (fun _ => vfun) vfun vfun.

(* graph with a single vertex *)
Definition unit_graph a := Graph (fun _ => vfun) (fun _: unit => a) vfun.

(* adding an edge to a graph *)
Definition add_edge (G: graph) (x y: G) (u: Le): graph :=
  @Graph (vertex G) [finType of option (edge G)]
         (fun b e => match e with Some e => endpoint b e | None => if b then y else x end)
         (@vlabel G)
         (fun e => match e with Some e => elabel e | None => u end).
Notation "G ∔ [ x , u , y ]" := (@add_edge G x y u) (at level 20, left associativity).

(* adding a label to a vertex (cumulative w.r.t existing label) *)
Definition add_vlabel (G: graph) (x: G) (a: Lv): graph :=
  @Graph (vertex G) (edge G)
         (@endpoint G)
         (fun v => if v==x then a⊗vlabel v else vlabel v)
         (@elabel G).
Notation "G [tst  x <- a ]" := (@add_vlabel G x a) (at level 20, left associativity).


(** ** Disjoint Union and Quotients of graphs *)

(* disjoint union (Definition 4.5)*)
Definition union (F G : graph) : graph :=
  {| vertex := [finType of F + G];
     edge := [finType of edge F + edge G];
     endpoint b := sumf (@endpoint F b) (@endpoint G b);
     vlabel e := match e with inl e => vlabel e | inr e => vlabel e end;
     elabel e := match e with inl e => elabel e | inr e => elabel e end;
  |}.
Infix "⊎" := union (at level 50, left associativity).

Definition unl {G H: graph} (x: G): G ⊎ H := inl x.
Definition unr {G H: graph} (x: H): G ⊎ H := inr x.

(* quotient (Definition 4.6): merging vertices according to an equivalence relation *)
Definition merge (G: graph) (r : equiv_rel G) :=
  {| vertex := quot r;
     edge := (edge G);
     endpoint b e := \pi (endpoint b e);
     vlabel c := \big[mon2/mon0]_(w | \pi w == c) vlabel w;
     elabel e := elabel e |}.
Arguments merge _ _: clear implicits. 
Notation merge_seq G l := (merge G (eqv_clot l)).

(* derived operations (Definition 4.7) *)
Definition two_graph a b := unit_graph a ⊎ unit_graph b.
Definition edge_graph a u b := two_graph a b ∔ [inl tt, u, inr tt].                           
Definition add_vertex G a := G ⊎ unit_graph a.
Notation "G ∔ a" := (add_vertex G a) (at level 20, left associativity).

(** ** Homomorphisms *)

(* Definition 4.8  *)
Class is_hom (F G: graph) (hv: F -> G) (he: edge F -> edge G) (hd: edge F -> bool): Prop := Hom
  { endpoint_hom: forall e b, endpoint b (he e) = hv (endpoint (hd e (+) b) e);
    vlabel_hom: forall v, vlabel (hv v) ≡ vlabel v;
    elabel_hom: forall e, elabel (he e) ≡[hd e] elabel e;
  }.
(* note: 
   - when using [flat_labels] for L, the edge swapping funcion [hd] 
     may only be constantly false
   - when the edge swapping function [hd] is constantly false, the
     types of [endpoint_hom] and [elabel_hom] in the above definition
     simplify to the simple, non swapping, notion of homomorphism *)
(* TOTHINK: actually, vlabel_hom should use a bigop, like in lemma [merge_surj]
   -> would be a more natural notion of homomorphism
   -> we would have the equivalence with the current definition when hv is injective (and thus, for isomorphisms)
   -> lemma [merge_surj] would just asssume a homormophism which is vertex surjective and edge bijective
   (not done for now since we do not really use general homomorphisms, only isomorphisms) *)

Lemma hom_id G: @is_hom G G id id xpred0.
Proof. by split. Qed.

Lemma hom_comp F G H hv he hd kv ke kd :
  @is_hom F G hv he hd -> @is_hom G H kv ke kd -> is_hom (kv \o hv) (ke \o he) (fun e => hd e (+) kd (he e)).
Proof.
  intros E E'. split.
  move=>e b=>/=. by rewrite 2!endpoint_hom addbA.
  move=>x/=. by rewrite 2!vlabel_hom. 
  move=>e/=.
  generalize (@elabel_hom _ _ _ _ _ E e). 
  generalize (@elabel_hom _ _ _ _ _ E' (he e)).
  case (hd e); case (kd (he e)); simpl.
  - apply eqv11. 
  - apply eqv01. 
  - apply eqv10.
  - apply transitivity. 
Qed.

Lemma hom_sym (F G: graph) (hv: bij F G) (he: bij (edge F) (edge G)) hd:
  is_hom hv he hd -> 
  is_hom hv^-1 he^-1 (hd \o he^-1).
Proof.
  intro H. split.
  move=>e b=>/=. by rewrite -{3}(bijK' he e) endpoint_hom bijK addbA addbb. 
  move=>x/=. by rewrite -{2}(bijK' hv x) vlabel_hom.
  move=>e/=. generalize (@elabel_hom _ _ _ _ _ H (he^-1 e)). rewrite -{3}(bijK' he e) bijK'. by symmetry. 
Qed.

(** ** Isomorphisms *)

(* Definition 4.8 *)
Universe S.
Set Primitive Projections.
Record iso (F G: graph): Type@{S} :=
  Iso { iso_v:> bij F G;
        iso_e: bij (edge F) (edge G);
        iso_d: edge F -> bool;
        iso_hom: is_hom iso_v iso_e iso_d }.
Infix "≃" := iso (at level 79).
Notation "h '.e'" := (iso_e h) (at level 2, left associativity, format "h '.e'"). 
Notation "h '.d'" := (iso_d h) (at level 2, left associativity, format "h '.d'"). 
Global Existing Instance iso_hom.

Lemma endpoint_iso F G (h: iso F G) b e: endpoint b (h.e e) = h (endpoint (h.d e (+) b) e).
Proof. apply endpoint_hom. Qed.

Lemma vlabel_iso F G (h: iso F G) v: vlabel (h v) ≡ vlabel v.
Proof. apply vlabel_hom. Qed.

Lemma elabel_iso F G (h: iso F G) e: elabel (h.e e) ≡[h.d e] elabel e.
Proof. apply elabel_hom. Qed.

Definition iso_id {G}: G ≃ G := @Iso _ _ bij_id bij_id _ (hom_id G). 
Hint Resolve iso_id : core.    (* so that [by] gets it... *)

Definition iso_sym F G: F ≃ G -> G ≃ F.
Proof.
  move => f. 
  eapply Iso with (bij_sym f) (bij_sym f.e) _ =>/=.
  apply hom_sym, f. 
Defined.

Definition iso_comp F G H: F ≃ G -> G ≃ H -> F ≃ H.
Proof.
  move => f g. 
  eapply Iso with (bij_comp f g) (bij_comp f.e g.e) _=>/=.
  apply hom_comp. apply f. apply g.
Defined.

(* Fact 4.9 *)
Global Instance iso_Equivalence: CEquivalence iso.
Proof. constructor. exact @iso_id. exact @iso_sym. exact @iso_comp. Defined.

Lemma endpoint_iso' F G (h: iso F G) b e: endpoint b (h.e^-1 e) = h^-1 (endpoint (h.d (h.e^-1 e) (+) b) e).
Proof. apply (endpoint_iso (iso_sym h)). Qed.

Lemma vlabel_iso' F G (h: iso F G) v: vlabel (h^-1 v) ≡ vlabel v.
Proof. apply (vlabel_iso (iso_sym h)). Qed.

Lemma elabel_iso' F G (h: iso F G) e: elabel (h.e^-1 e) ≡[h.d (h.e^-1 e)] elabel e.
Proof. apply (elabel_iso (iso_sym h)). Qed.

Definition Iso' (F G: graph)
           (fv: F -> G) (fv': G -> F)
           (fe: edge F -> edge G) (fe': edge G -> edge F) fd:
  cancel fv fv' -> cancel fv' fv ->
  cancel fe fe' -> cancel fe' fe ->
  is_hom fv fe fd -> F ≃ G.
Proof. move=> fv1 fv2 fe1 fe2 E. exists (Bij fv1 fv2) (Bij fe1 fe2) fd. apply E. Defined.

Tactic Notation "Iso" uconstr(f) uconstr(g) uconstr(h) :=
  match goal with |- ?F ≃ ?G => apply (@Iso F G f g h) end.


(** ** isomorphisms about local and global operations *)

(* Lemmas 4.10, 4.11, 4.12 and more *)

(** *** isomorphisms about [unit_graph] *)

Global Instance unit_graph_iso: CProper (eqv ==> iso) unit_graph.
Proof.
  intros a b ab. Iso bij_id bij_id xpred0.
  abstract by split=>//=;symmetry.
Defined.


(** *** isomorphisms about [add_edge] *)

Lemma add_edge_iso'' F G (h: F ≃ G) x x' (ex: h x = x') y y' (ey: h y = y') u v (e: u ≡ v):
  F ∔ [x, u, y] ≃ G ∔ [x', v, y'].
Proof.
  Iso (iso_v h) (option_bij (h.e)) (fun e => match e with Some e => h.d e | None => false end).
  abstract by split; rewrite -?ex -?ey; repeat first [apply h|symmetry; apply e|case].
Defined.

Lemma add_edge_iso' F G (h: F ≃ G) x u v y (e: u ≡ v): F ∔ [x, u, y] ≃ G ∔ [h x, v, h y].
Proof. by eapply add_edge_iso''. Defined.

Lemma add_edge_iso F G (h: F ≃ G) x u y: F ∔ [x, u, y] ≃ G ∔ [h x, u, h y].
Proof. by apply add_edge_iso'. Defined.

Lemma add_edge_C F x u y z v t: F ∔ [x, u, y] ∔ [z, v, t] ≃ F ∔ [z, v, t] ∔ [x, u, y].
Proof.
  Iso bij_id option2_swap xpred0.
  abstract by split; repeat case.
Defined.

Lemma add_edge_rev F x u v y (e: u ≡' v): F ∔ [x, u, y] ≃ F ∔ [y, v, x].
Proof.
  Iso bij_id bij_id (fun x => match x with Some _ => false | None => true end).
  abstract (split; (repeat case)=>//=; by apply Eqv'_sym). 
Defined.

Lemma add_edge_vlabel F x a y u z: F [tst x <- a] ∔ [y, u, z] ≃ F ∔ [y, u, z] [tst x <- a].
Proof. reflexivity. Defined.


Lemma add_vlabel_iso'' F G (h: F ≃ G) x x' (ex: h x = x') a b (e: a ≡ b): F [tst x <- a] ≃ G [tst x' <- b].
Proof.
  Iso h h.e h.d.
  split; try apply h.
  move=>v/=. rewrite -ex inj_eq=>/=. 2: by apply bij_injective.
  by case eq_op; rewrite ?e vlabel_iso. 
Defined.

Lemma add_vlabel_iso' F G (h: F ≃ G) x a b (e: a ≡ b): F [tst x <- a] ≃ G [tst h x <- b].
Proof. by eapply add_vlabel_iso''. Defined.

Lemma add_vlabel_iso F G (h: F ≃ G) x a: F [tst x <- a] ≃ G [tst h x <- a].
Proof. by apply add_vlabel_iso'. Defined.

Lemma add_vlabel_C F x a y b: F [tst x <- a] [tst y <- b] ≃ F [tst y <- b] [tst x <- a].
Proof.
  Iso bij_id bij_id xpred0.
  split=>//=. move=>v.
  case eq_op; case eq_op=>//.
  by rewrite 2!monA (monC a b).
Defined.

Lemma add_vlabel_unit a x b: unit_graph a [tst x <- b] ≃ unit_graph (a⊗b).
Proof. apply (unit_graph_iso (monC b a)). Defined.

Lemma add_vlabel_mon0 G x: G [tst x <- 1] ≃ G.
Proof.
  Iso bij_id bij_id xpred0. 
  split=>//=. move=>v.
  case eq_op=>//. by rewrite monC monU.
Defined.

(** *** isomorphisms about [union] *)

Global Instance union_iso: CProper (iso ==> iso ==> iso) union.
Proof.
  intros F F' f G G' g.
  exists (sum_bij f g) (sum_bij f.e g.e) (fun e => match e with inl e => f.d e | inr e => g.d e end).
  abstract (split; [
              move=>[e|e] b/=; by rewrite endpoint_iso |
              case=>x/=; apply vlabel_iso |
              case=>e/=; apply elabel_iso ]).
Defined.

Lemma union_C G H: G ⊎ H ≃ H ⊎ G.
Proof.
  exists bij_sumC bij_sumC xpred0.
  abstract by split; case. 
Defined.

Lemma union_A F G H: F ⊎ (G ⊎ H) ≃ F ⊎ G ⊎ H.
Proof.
  exists bij_sumA bij_sumA xpred0.
  abstract by split; repeat case. 
Defined.
 
Lemma union_add_edge_l F G x u y: F ∔ [x, u, y] ⊎ G ≃ (F ⊎ G) ∔ [unl x, u, unl y].
Proof.
  Iso bij_id (@sum_option_l _ _) xpred0.
  abstract by split; repeat case.
Defined.

Lemma union_add_edge_r F G x u y: F ⊎ G ∔ [x, u, y] ≃ (F ⊎ G) ∔ [unr x, u, unr y].
Proof.
  etransitivity. apply union_C. 
  etransitivity. apply union_add_edge_l.
  etransitivity. apply (add_edge_iso (union_C _ _)).
  reflexivity.
Defined.

Lemma union_add_vlabel_l F G x a: F [tst x <- a] ⊎ G ≃ (F ⊎ G) [tst unl x <- a].
Proof. 
  Iso bij_id bij_id xpred0.
  abstract by split; repeat case.
Defined.

Lemma union_add_vlabel_r F G x a: F ⊎ G [tst x <- a] ≃ (F ⊎ G) [tst unr x <- a].
Proof.
  etransitivity. apply union_C. 
  etransitivity. apply union_add_vlabel_l.
  etransitivity. apply (add_vlabel_iso (union_C _ _)).
  reflexivity.
Defined.

Lemma add_vlabel_two a b (x: unit+unit) c:
  two_graph a b [tst x <- c] ≃ two_graph (if x then a⊗c else a) (if x then b else b⊗c).
Proof.
  case x; case=>/=. 
  etransitivity. apply iso_sym. apply union_add_vlabel_l. apply union_iso=>//. apply add_vlabel_unit. 
  etransitivity. apply iso_sym. apply union_add_vlabel_r. apply union_iso=>//. apply add_vlabel_unit.
Defined.  

Lemma add_vlabel_edge a u b (x: unit+unit) c:
  edge_graph a u b [tst x <- c] ≃ edge_graph (if x then a⊗c else a) u (if x then b else b⊗c).
Proof.
  etransitivity. apply iso_sym. apply add_edge_vlabel.
  etransitivity. apply (add_edge_iso (add_vlabel_two a b x c)).
  by case x; case.
Defined.


(** *** isomorphisms about [merge] *)

(* remove if no longer used below *)
Lemma eq_eqv {X: setoid} (x y: X): x = y -> x ≡ y.
Proof. by move=>->. Qed.

Section merge_surj.
 Variable (G: graph) (r: equiv_rel G).
 Variable (H: graph) (fv: G -> H) (fv': H -> G).
 Variable (fe: bij (edge G) (edge H)).
 Hypothesis Hr: forall x y, reflect (kernel fv x y) (r x y).
 Hypothesis Hsurj: cancel fv' fv.
 Hypothesis Hendpoints: forall b e, fv (endpoint b e) = endpoint b (fe e).
 Hypothesis Helabel: forall e, elabel (fe e) ≡ elabel e.
 Hypothesis Hvlabel: forall y, vlabel y ≡ \big[mon2/mon0]_(x | fv x == y) vlabel x.
 
 (* Lemma 4.13 *)
 Lemma merge_surj: merge G r ≃ H.
 Proof.
   Iso (quot_kernel Hr Hsurj) fe xpred0. split; intros=>/=.
   - rewrite -Hendpoints=>/=. by rewrite surj_repr_pi. 
   - rewrite Hvlabel.
     (* TOCLEAN *)
     apply eq_eqv, eq_bigl=>x.
     apply /idP/idP =>/eqP E.
     * apply /eqP. move:E=>/Hr/eqquotP E. rewrite E. apply reprK. 
     * rewrite -E surj_repr_pi=>//.
   - apply Helabel.
 Defined.
 Lemma merge_surjE (x: G): merge_surj (\pi x) = fv x.
 Proof. by rewrite /=surj_repr_pi. Qed.
End merge_surj.
Global Opaque merge_surj.

Section h_merge_nothing'.
 Variables (F: graph) (r: equiv_rel F).
 Hypothesis H: forall x y: F, r x y -> x=y.
 Lemma merge_nothing': merge F r ≃ F.
 Proof.
   apply merge_surj with id id bij_id=>//.
   - intros. apply Bool.iff_reflect.
     split. intros ->. by rewrite equiv_refl.
     intro E. apply H. by rewrite E.
   - intro.
     (* TOCLEAN *)
     rewrite -big_filter filter_index_enum /=.
     rewrite enum1 big_cons big_nil/=.
     by rewrite monU. 
 Defined.
 Lemma merge_nothing'E x: merge_nothing' (\pi x) = x.
 Proof. by rewrite /=merge_surjE. Qed.
End h_merge_nothing'.
Global Opaque merge_nothing'.

Section merge_merge.
  Variables (F: graph) (e: equiv_rel F) (e': equiv_rel (merge F e)).
  Lemma hom_merge_merge: is_hom (quot_quot e': merge _ e' -> merge F _) bij_id xpred0.
  Proof.
    split; intros=>//=; first by rewrite -equiv_comp_pi.
    rewrite [X in X ≡ _](partition_big (fun x => \pi x) (fun w => \pi w == v)). 
    - apply: eqv_bigr => w pw. apply: eqv_big => x //. 
      case: (altP (\pi x =P w)) => // ?. subst w. by rewrite -(eqP pw) quot_quotE eqxx.
    - move => x. by rewrite -[v]reprK -[repr v]reprK quot_quotE !eqmodE.
  Qed.
  Lemma merge_merge: merge (merge F e) e' ≃ merge F (equiv_comp e').
  Proof. eexists. eapply hom_merge_merge. Defined.
  Lemma merge_mergeE x: merge_merge (\pi (\pi x)) = \pi x.
  Proof. apply quot_quotE. Qed.
End merge_merge.
Global Opaque merge_merge.


Section merge.
  Variables (F G: graph) (h: iso F G) (l: pairs F).
  Definition h_merge: bij (merge_seq F l) (merge_seq G (map_pairs h l)).
    eapply bij_comp. apply (quot_bij h). apply quot_same. apply eqv_clot_iso.
  Defined. 
  Lemma h_mergeE (x: F): h_merge (\pi x) = \pi h x.
  Proof. by rewrite /=quot_bijE quot_sameE. Qed.
  Lemma merge_hom: is_hom h_merge h.e h.d.
  Proof.
    split; intros=>/=. 
    - rewrite endpoint_iso. symmetry. apply h_mergeE. 
    - rewrite quot_sameE. symmetry.
     (* TOCLEAN *)
      apply: (eqv_big_bij (f := h)). exact: bij_perm_enum.
      + move=>x. rewrite eqmodE eqv_clot_map. 2: apply bij_injective.
        apply /idP/idP. move=>/eqP E. rewrite -E. apply piK'.
        intro. apply /eqP. rewrite -(reprK v). by apply /eqquotP.
      + move=> x _. by rewrite vlabel_iso.
    - apply elabel_iso.        
  Qed.
  Definition merge_iso: merge_seq F l ≃ merge_seq G (map_pairs h l) := Iso merge_hom.
  Lemma merge_isoE (x: F): merge_iso (\pi x) = \pi h x.
  Proof. apply h_mergeE. Qed.
End merge.
Global Opaque h_merge merge_iso.

Section merge_same'.
 Variables (F: graph) (h k: equiv_rel F).
 Hypothesis H: h =2 k. 
 Lemma merge_same'_hom: is_hom (quot_same H: merge _ h -> merge _ k) bij_id xpred0.
 Proof.
   split; intros=>//; try (rewrite /=; apply/eqquotP; rewrite -H; apply: piK').
   (* TOCLEAN *)
   apply (eqv_big_bij (f := id))=>//.
   apply (bij_perm_enum bij_id).
   intro. by rewrite -(reprK v) quot_sameE 2!eqmodE H.
 Qed.
 Definition merge_same': merge F h ≃ merge F k := Iso merge_same'_hom.
 Lemma merge_same'E (x: F): merge_same' (\pi x) = \pi x.
 Proof. apply quot_sameE. Qed.
End merge_same'.
Global Opaque merge_same'.

Section merge_same.
 Variables (F: graph) (h k: pairs F).
 Hypothesis H: eqv_clot h =2 eqv_clot k.
 Definition merge_same: iso (merge_seq F h) (merge_seq F k) := merge_same' H. 
 Definition merge_sameE (x: F): merge_same (\pi x) = \pi x := merge_same'E H x. 
End merge_same.
Global Opaque merge_same.


Section merge_nothing.
 Variables (F: graph) (h: pairs F).
 Hypothesis H: List.Forall (fun p => p.1 = p.2) h.
 Definition merge_nothing: merge_seq F h ≃ F.
 Proof. apply merge_nothing', eqv_clot_nothing', H. Defined.
 Lemma merge_nothingE (x: F): merge_nothing (\pi x) = x.
 Proof. apply merge_nothing'E. Qed.
End merge_nothing.
Global Opaque merge_nothing.

Section merge_merge_seq.
  Variables (F: graph) (h k: pairs F) (k': pairs (merge_seq F h)).
  Hypothesis kk': k' = map_pairs (pi (eqv_clot h)) k.
  Definition merge_merge_seq: merge_seq (merge_seq F h) k' ≃ merge_seq F (h++k).
    eapply iso_comp. apply merge_merge. apply merge_same'.
    abstract by rewrite kk'; apply eqv_clot_cat.
  Defined.
  Lemma merge_merge_seqE (x: F): merge_merge_seq (\pi (\pi x)) = \pi x.
  Proof. by rewrite /=merge_mergeE merge_same'E. Qed.
End merge_merge_seq.
Global Opaque merge_merge_seq.

Lemma eqv_clot_map_lr (F G : finType) (l : pairs F) x y : 
  eqv_clot (map_pairs inl l) (@inl F G x) (@inr F G y) = false.
Proof. rewrite (@eqv_clot_mapF _) ?inr_codom_inl //. exact: inl_inj. Qed.

Lemma union_equiv_l_eqv_clot (A B: finType) (l: pairs A):
  union_equiv_l B (eqv_clot l) =2 eqv_clot (map_pairs inl l).
Proof.
  rewrite /union_equiv_l/=/union_equiv_l_rel. move => [x|x] [y|y].
  + rewrite (@eqv_clot_map _ _  _ _ _ (@inl A B)) //. exact: inl_inj.
  + by rewrite eqv_clot_map_lr.
  + by rewrite equiv_sym eqv_clot_map_lr.
  + by rewrite eqv_clot_map_eq ?sum_eqE // inr_codom_inl.
Qed.

Lemma merge_add_edge (G: graph) (r: equiv_rel G) x u y: merge (G ∔ [x, u, y]) r ≃ merge G r ∔ [\pi x, u, \pi y].
Proof. Iso bij_id bij_id xpred0. split=>//. case=>//. by case. Defined.
Lemma merge_add_edgeE (G: graph) (r: equiv_rel G) x u y (z: G): @merge_add_edge G r x u y (\pi z) = \pi z.
Proof. by []. Qed.
Global Opaque merge_add_edge.

Lemma merge_add_vlabel (G: graph) (r: equiv_rel G) x a: merge (G [tst x <- a]) r ≃ merge G r [tst \pi x <- a].
Proof.
  Iso bij_id bij_id xpred0. split=>//= v. case: (altP (v =P \pi x)) => [-> {v}|D].
  - rewrite (bigD1 x) // [in X in _ ≡ X](bigD1 x) // ?eqxx monA. apply: mon_eqv => //.
    apply: eqv_bigr => y /andP [_ H]. by rewrite (negbTE H).
  - apply: (eqv_big_bij (f := bij_id)) => //. 
    + exact: bij_perm_enum.
    + move => /= y /eqP ?. case: (altP (y =P x)) => // ?; subst. by rewrite eqxx in D.
Defined.
Lemma merge_add_vlabelE (G: graph) (r: equiv_rel G) x a (z: G): @merge_add_vlabel G r x a (\pi z) = \pi z.
Proof. by []. Qed.
Global Opaque merge_add_vlabel.


(** *** isomorphisms about [union] and [merge] (Lemma 4.11) *)


Section union_merge_l.
  Variables (F G: graph) (l: pairs F).
  Definition h_union_merge_l: bij (merge_seq F l ⊎ G) (merge_seq (F ⊎ G) (map_pairs unl l)).
  Proof. eapply bij_comp. apply union_quot_l. apply quot_same. apply union_equiv_l_eqv_clot. Defined.
  Lemma hom_union_merge_l: is_hom h_union_merge_l bij_id xpred0.
  Proof.
    split; try by case; intros=>//=; rewrite ?union_quot_lEl ?union_quot_lEr quot_sameE //.
    move=> x. rewrite /=quot_sameE. case:x=>[x|x].
    have x0 := repr x.
    - pose f (z : F + G) := if z is inl z' then z' else x0.
      etransitivity. apply: (reindex_onto (@inl _ _) f) => /=.
      + move => [i|i] //=.
        by rewrite eq_sym eqmodE eqv_clot_map_lr.
      + rewrite [X in X ≡ _]big_mkcond [X in _ ≡ X]big_mkcond.
        (* TOCLEAN *)
        apply: eqv_bigr => z _ => /=.
        rewrite eqmodE eqv_clot_map. 2: apply inl_inj.
        rewrite eqxx andbT -{2}(reprK x) eqmodE//. 
    - apply (big_pred1 (inr x))=>y.
      rewrite eqmodE. case y=>z.
      + by rewrite eqv_clot_map_lr.
      + apply eqv_clot_map_eq. by rewrite inr_codom_inl.
  Qed.
  Definition union_merge_l: merge_seq F l ⊎ G ≃ merge_seq (F ⊎ G) (map_pairs unl l) :=
    Iso hom_union_merge_l.
  Lemma union_merge_lEl (x: F): union_merge_l (@unl (merge_seq F l) _ (\pi x)) = \pi unl x.
  Proof. by rewrite /=union_quot_lEl quot_sameE. Qed.
  Lemma union_merge_lEr (x: G): union_merge_l (unr x) = \pi unr x.
  Proof. by rewrite /=union_quot_lEr quot_sameE. Qed.
  Lemma union_merge_l'E (x: F+G):
    union_merge_l^-1 (\pi x) =
    match x with inl y => @unl (merge_seq F l) _ (\pi y) | inr y => unr y end.
  Proof. by rewrite /=quot_sameE union_quot_l'E. Qed.
End union_merge_l.  
Global Opaque union_merge_l.

Lemma map_map_pairs {A B C} (f: A -> B) (g: B -> C) l: map_pairs g (map_pairs f l) = map_pairs (g \o f) l.
Proof. by rewrite /map_pairs -map_comp. Qed.

Lemma map_pairs_id {A} (l: pairs A): map_pairs id l = l.
Proof. elim l=>//=[[a a'] q]/=. congruence. Qed.

Section union_merge_r.
  Variables (F G: graph) (l: pairs G).
  Lemma union_merge_r: F ⊎ merge_seq G l ≃ merge_seq (F ⊎ G) (map_pairs unr l).
  Proof.
    eapply iso_comp. apply union_C.
    eapply iso_comp. apply union_merge_l.
    eapply iso_comp. apply (merge_iso (union_C _ _)).
    apply merge_same. abstract by rewrite map_map_pairs. 
  Defined.
  Lemma union_merge_rEr (x: G): union_merge_r (@unr _ (merge_seq G l) (\pi x)) = \pi (unr x).
  Proof.
    (* BUG: the second rewrite hangs if F and x are not given *)
    rewrite /=. rewrite (union_merge_lEl F _ x).
    rewrite (merge_isoE (union_C G F) _ (unl x)).
    by rewrite merge_sameE. 
  Qed.
  Lemma union_merge_rEl (x: F): union_merge_r (unl x) = \pi (unl x).
  Proof.
    rewrite /=. rewrite (union_merge_lEr _ x) .
    rewrite (merge_isoE (union_C G F) _ (unr x)).
    by rewrite merge_sameE. 
  Qed.
End union_merge_r.  
Global Opaque union_merge_r.

Section merge_union_K.
  Variables (F K: graph) (h: pairs (F+K)) (k: K -> F).
  Definition union_K_pairs := map_pairs (sum_left k) h.

  Hypothesis kv: forall x: K, vlabel x = 1%lbl.
  Hypothesis kh: forall x: K, unr x = unl (k x) %[mod (eqv_clot h)].

  Lemma equiv_clot_Kl: union_K_equiv (eqv_clot h) =2 eqv_clot union_K_pairs.
  Proof.
    move=> x y. rewrite /union_K_equiv map_equivE. 
    rewrite !eqv_clotE. set e1 := rel_of_pairs _. set e2 := rel_of_pairs _. 
    apply/idP/idP. 
    - suff S u v : equiv_of e1 u v -> equiv_of e2 (sum_left k u) (sum_left k v) by apply: S. 
      apply: equiv_ofE => {u v} [[u|u] [u'|u']] /= H. 
      all: rewrite /e2 /sum_left; apply: sub_equiv_of; apply/mapP. 
      + by exists (unl u,unl u').
      + by exists (unl u,unr u').
      + by exists (unr u,unl u').
      + by exists (unr u,unr u').
    - apply: equiv_ofE => {x y} x x' xx'. 
      have kh' z : equiv_of e1 (unr z) (unl (k z)).
      { rewrite -eqv_clotE. apply/eqquotP. exact: kh. }
      case/mapP : xx' => [[[u|u] [v|v]] H] /= [-> ->] {x x'}.
      + exact: sub_equiv_of.
      + etransitivity. 2: apply kh'. by apply sub_equiv_of. 
      + etransitivity. symmetry; apply kh'. by apply sub_equiv_of. 
      + etransitivity. 2: apply kh'. etransitivity. symmetry; apply kh'. by apply sub_equiv_of.
  Qed.
  
  Definition h_merge_union_K: bij (merge_seq (union F K) h) (merge_seq F union_K_pairs).
    eapply bij_comp. apply quot_union_K with k. apply kh.
    apply quot_same. apply equiv_clot_Kl. 
  Defined.

  Hypothesis ke: edge K -> False.

  Definition h_merge_union_Ke1 (e: edge (merge_seq (union F K) h)): edge (merge_seq F union_K_pairs) :=
    match e with inl e => e | inr e => match ke e with end end.

  Definition h_merge_union_Ke: bij (edge (merge_seq (union F K) h)) (edge (merge_seq F union_K_pairs)).
    exists h_merge_union_Ke1 inl=>x//. by case x.
  Defined.

  Lemma hom_merge_union_K: is_hom h_merge_union_K h_merge_union_Ke xpred0.
  Proof.
    split; try (case; intros =>//=; by rewrite ?quot_union_KEl ?quot_union_KEr quot_sameE).
    move=> v/=.
    rewrite quot_sameE/=.  
    have x0 : F. { case: (repr v). exact: id. exact k. }
    etransitivity. apply: (reindex_onto (sum_left (fun _ : K => x0)) (@inl _ _)) => //.
    rewrite /= [X in X ≡ _]big_mkcond [X in _ ≡ X]big_mkcond /=.
    apply: eqv_bigr => [[x|x]] /= _.
    - rewrite eqxx andbT eqmodE. rewrite -{2}(reprK v) eqmodE.
      rewrite -equiv_clot_Kl. simpl. rewrite /map_equiv_rel/=.
      set (r := repr _). case r=>//= w.
      generalize (kh w). rewrite -eqmodE. move <-. by rewrite eqmodE.
    - rewrite andbC kv -[X in X ≡ _]/1. by case: ifP.
  Qed.

  Definition merge_union_K: merge_seq (F ⊎ K) h ≃ merge_seq F union_K_pairs :=
    Iso hom_merge_union_K.
  Lemma merge_union_KE (x: F+K): merge_union_K (\pi x) = \pi (sum_left k x).
  Proof. by rewrite /=quot_union_KE quot_sameE. Qed.
End merge_union_K.
Global Opaque merge_union_K.

(* used only in unused proofs in reduction.v *)
Lemma merge_two a b: merge_seq (unit_graph a ⊎ unit_graph b) [:: (inl tt,inr tt)] ≃ unit_graph (a⊗b).
Admitted.
Lemma merge_twoE a b x: merge_two a b x = tt.
Admitted.  

(* other isomorphisms on concrete graphs *)

Lemma two_graph_swap a b: two_graph a b ≃ two_graph b a.
Proof. apply union_C. Defined.

Global Instance add_vertex_iso : CProper (iso ==> eqv ==> iso) add_vertex.
Proof. move => F G h a b ab. apply (union_iso h (unit_graph_iso ab)). Defined.


(** ** Subgraphs and Induced Subgraphs *)

Definition subgraph (H G : graph) := 
  exists hv he hd, @is_hom H G hv he hd /\ injective hv /\ injective he.

Section Subgraphs.
  Variables (G : graph) (V : {set G}) (E : {set edge G}).
  Definition consistent := forall e b, e \in E -> endpoint b e \in V.
  Hypothesis in_V : consistent.
  
  Definition sub_vertex := sig [eta mem V].
  Definition sub_edge := sig [eta mem E].

  Definition subgraph_for := 
    {| vertex := [finType of sub_vertex];
       edge := [finType of sub_edge];
       endpoint b e := Sub (endpoint b (val e)) (in_V b (valP e)); 
       vlabel x := vlabel (val x);
       elabel e := elabel (val e);
    |}.

  Lemma subgraph_sub : subgraph subgraph_for G.
  Proof. exists val, val, xpred0. split => //=. split; exact: val_inj. Qed.

  (* edge deletion is treated as a special case, because this avoids the change in the vertex type *)
  Definition del_edges := 
    {| vertex := [finType of G];
       edge := [finType of {e | e \in ~: E}];
       endpoint b e := endpoint b (val e); 
       vlabel x := vlabel x;
       elabel e := elabel (val e); |}.

  Lemma del_edges_sub : subgraph del_edges G.
  Proof. exists id, val, xpred0. split => //=. split. apply inj_id. apply val_inj. Qed.
  
End Subgraphs.

Section Edges.
Variables (G : graph).
Implicit Types (x y : G).

Definition edges x y :=
  [set e | (source e == x) && (target e == y)].

Definition edge_set (S : {set G}) :=
  (* DPtoCD: forall b, endpoint b e \in S *)
  [set e | (source e \in S) && (target e \in S)].

Lemma edge_set1 x : edge_set [set x] = edges x x.
Proof. apply/setP=> e. by rewrite !inE. Qed.

Lemma edge_in_set e (A : {set G}) x y :
  x \in A -> y \in A -> e \in edges x y -> e \in edge_set A.
Proof. move => Hx Hy. rewrite !inE => /andP[/eqP->/eqP->]. by rewrite Hx. Qed.

Definition incident x e := [exists b, endpoint b e == x].
Definition edges_at x := [set e | incident x e].

Definition edges_in (V : {set G}) := (\bigcup_(x in V) edges_at x)%SET.

Lemma edges_in1 (x : G) : edges_in [set x] = edges_at x. 
Proof. by rewrite /edges_in big_set1. Qed.

End Edges.
Arguments edges_at [G] x, G x.

(* Frequently used consistent sets of vertices and edges *)

Lemma consistentT (G : graph) (E : {set edge G}) : consistent setT E.
Proof. by []. Qed.
Arguments consistentT [G] E.

Lemma consistentTT (G : graph) : consistent [set: G] [set: edge G].
Proof. done. Qed.
Arguments consistentTT : clear implicits.


Definition induced_proof (G: graph) (S : {set G}) : consistent S (edge_set S).
Proof. move => e b; rewrite inE=>/andP[? ?]; by case b. Qed.

Definition induced (G: graph) (S : {set G}) := 
  subgraph_for (@induced_proof G S).


Lemma induced_sub (G: graph) (S : {set G}) : subgraph (induced S) G.
Proof. exact: subgraph_sub. Qed.


Lemma consistent_del1 (G : graph) (x : G) : consistent [set~ x] (~: edges_at x).
Proof. move => e b. rewrite !inE. apply: contraNneq => <-. by existsb b. Qed.

(* Commonly used subgraphs *)
Definition del_vertex (G : graph) (z : G) : graph := 
  subgraph_for (@consistent_del1 G z).

(** *** isomorphisms about subgraphs *)
(* not neded for now *)

Lemma incident_iso (F G : graph) (h : F ≃ G) (x : F) (e : edge F) : 
  incident x e = incident (h x) (h.e e).
Proof. 
  rewrite /incident. apply/existsP/existsP => [] [b] E; exists (h.d e (+) b).
  - by rewrite endpoint_iso addbA addbb addFb (eqP E).
  - by rewrite endpoint_iso bij_eq in E. 
Qed.

Lemma edges_at_iso (F G : graph) (h : F ≃ G) (x : F) :
  edges_at (h x) = [set h.e e | e in edges_at x].
Proof. 
  apply/setP => e. by rewrite -[e](bijK' h.e) bij_mem_imset !inE (incident_iso h).
Qed.

Lemma subgraph_for_iso' G H (h : G ≃ H) 
  (VG :{set G}) (VH : {set H}) (EG : {set edge G}) (EH : {set edge H})
  (con1 : consistent VG EG) (con2 : consistent VH EH) :
  VH = h @: VG -> EH = h.e @: EG ->
  subgraph_for con1 ≃ subgraph_for con2.
Proof. 
  move => eq_V eq_E. 
  Iso (subset_bij eq_V) (subset_bij eq_E) (fun e => h.d (val e)).
  split.
  - case => e He b. apply: val_inj => /=. exact: endpoint_iso.
  - case => v Hv /=. exact: vlabel_iso.
  - case => e He /=. exact: elabel_iso.
Defined.

Lemma subgraph_for_isoE' G H (h : G ≃ H) 
  (VG :{set G}) (VH : {set H}) (EG : {set edge G}) (EH : {set edge H})
  (con1 : consistent VG EG) (con2 : consistent VH EH) 
  (eq_V : VH = h @: VG) (eq_E : EH = h.e @: EG) x p q :
  subgraph_for_iso' con1 con2 eq_V eq_E (Sub x p) = (Sub (h x) q).
Proof. exact: val_inj. Qed.
Section BijT.
Variables (T : finType) (P : pred T).
Hypothesis inP : forall x, P x.
Definition subT_bij : bij {x : T | P x} T.
Proof. exists val (fun x => Sub x (inP x)). 
       abstract (case => x Px; exact: val_inj).
       abstract done.
Defined.
End BijT.

Definition setT_bij (T : finType) : bij {x : T | x \in setT} T := 
  Eval hnf in subT_bij (@in_setT T).
Arguments setT_bij {T}.

Lemma setT_bij_hom (G : graph) : @is_hom (subgraph_for (@consistentTT G)) G setT_bij setT_bij xpred0. 
Proof. by []. Qed.

Definition iso_subgraph_forT (G : graph) : subgraph_for (consistentTT G) ≃ G := 
  Eval hnf in Iso (setT_bij_hom G).

Lemma del_vertex_iso' F G (h : F ≃ G) (z : F) (z' : G) : 
  h z = z' -> del_vertex z ≃ del_vertex z'.
Proof.
  move => h_z. apply: (subgraph_for_iso' (h := h)). 
  - abstract(by rewrite -h_z -bij_imsetC /= imset_set1).
  - abstract(by rewrite -h_z -bij_imsetC /= edges_at_iso). 
Defined.

Lemma del_vertex_proof (F G : graph) (h : F ≃ G) (z : F) (z' : G) x : 
  h z = z' -> x \in [set~ z] -> h x \in [set~ z'].
Proof. move => E. by rewrite -E !inE bij_eq. Qed.
  
Lemma del_vertex_isoE' F G (h : F ≃ G) (z : F) (z' : G) E x p : 
  @del_vertex_iso' F G h z z' E (Sub x p) = Sub (h x) (del_vertex_proof E p).
Proof. exact: val_inj. Qed.

Lemma del_edges_iso' F G (h : F ≃ G) (A : {set edge F}) (B : {set edge G}) : 
  ~: B = (h.e @: ~: A) -> del_edges A ≃ del_edges B.
Proof.
  move => E. Iso h (subset_bij E) (fun e => h.d (val e)). split.
  - case => e He b /=. exact: endpoint_iso.
  - move => v /=. exact: vlabel_iso.
  - case => e He /=. exact: elabel_iso.
Defined.

End s. 

Notation source := (endpoint false).
Notation target := (endpoint true).

(* Declare Scope graph_scope. compat:coq-8.9*)
Bind Scope graph_scope with graph.
Delimit Scope graph_scope with G.

Arguments union {L} F G.
Infix "⊎" := union (at level 50, left associativity) : graph_scope.
Arguments unl {L G H}.
Arguments unr {L G H}.

Arguments add_edge {L} G x y u.
Arguments add_vertex {L} G a.
Arguments add_vlabel {L} G x a.
Notation "G ∔ [ x , u , y ]" := 
  (add_edge G x y u) (at level 20, left associativity) : graph_scope.
Notation "G ∔ a" := 
  (add_vertex G a%lbl) (at level 20, left associativity) : graph_scope.
Notation "G [tst  x <- a ]" :=
  (add_vlabel G x a%lbl) (at level 20, left associativity) : graph_scope.

Arguments merge {L} _ _.
Notation merge_seq G l := (merge G (eqv_clot l)).

Arguments iso {L}.
Arguments iso_id {_ _}.
Infix "≃" := iso (at level 79).
Notation "h '.e'" := (iso_e h) (at level 2, left associativity, format "h '.e'").
Notation "h '.d'" := (iso_d h) (at level 2, left associativity, format "h '.d'"). 

Tactic Notation "Iso" uconstr(f) uconstr(g) uconstr(h) :=
  match goal with |- ?F ≃ ?G => refine (@Iso _ F G f g h _) end.

Global Hint Resolve iso_id : core.  (* so that [by] gets it... *)

Arguments edges_at [L G] x, [L] G x.




(** ** Merging Subgraphs *)

(** This construction allows transforming a quotient on [G[V1,E1] + G[V2,E2]] 
    into a quotient on [G[V1 :|: V2, E1 :|: E2]], provided the edge sets are
    disjoint and the quotient merges all duplicated verices (i.e., those
    occurring both in [V1] and in [V2]. The underlying function on vertices from 
    [G[V1,E1] + G[V2,E2]] to [G[V1 :|: V2, E1 :|: E2]] simply drops the inl/inr.
    For the converse direction, we inject into [G[V1,E1]] if possible and otherwise 
    into [G[V1,E2]]. Note that this only yields a bijection after quotienting. *)

Section MergeSubgraph.
  Variable A: Type.
  Notation graph := (graph (flat_labels A)).
  (* note: the lemma also holds for arbitrarily-labeled graphs when vertices in the intersection are labeled with idempotent elements *)
  Variables (G : graph) (V1 V2 : {set G}) (E1 E2 : {set edge G}) 
            (con1 : consistent V1 E1) (con2 : consistent V2 E2)
            (h : pairs (subgraph_for con1 ⊎ subgraph_for con2)%G).

  Lemma consistentU : consistent (V1 :|: V2) (E1 :|: E2).
  Proof using con1 con2. 
    move => e b. case/setUP => E. 
    - by rewrite !inE con1.
    - by rewrite !inE con2. 
  Qed.    

  Hypothesis eqvI : forall x (inU : x \in V1) (inV : x \in V2), 
      inl (Sub x inU) = inr (Sub x inV) %[mod eqv_clot h].

  Hypothesis disE : [disjoint E1 & E2].

  Local Notation G1 := (subgraph_for con1).
  Local Notation G2 := (subgraph_for con2).
  Local Notation G12 := (subgraph_for consistentU).

  Definition h' := map_pairs (@union_bij_fwd _ _ _) h.
  Lemma eqv_clot_union_rel : merge_union_rel (eqv_clot h) =2 eqv_clot h'.
  Proof.
    move => x y. rewrite /merge_union_rel /h' map_equivE. apply/idP/idP.
    - have aux z : union_bij_fwd (union_bij_bwd z) = z %[mod eqv_clot (map_pairs (@union_bij_fwd _ _ _) h)].
      { apply/eqquotP. case: union_bij_bwdP => *; apply: eq_equiv; by apply: val_inj. }
      move => H. apply/eqquotP. rewrite -[_ x]aux -[_ y]aux. apply/eqquotP.
      move: H. apply: eqv_clot_map'.
    - rewrite eqv_clotE. apply: equiv_ofE => /= {x y} x y. 
      rewrite /rel_of_pairs/=. case/mapP => /= [[u v]] in_h [-> ->].
      apply/eqquotP. rewrite 2!(union_bij_fwd_can' eqvI). apply/eqquotP.
      exact: eqv_clot_pair.
  Qed.

  Definition merge_subgraph_v : bij (merge_seq (G1 ⊎ G2) h) (merge_seq G12 h') :=
    Eval hnf in (bij_comp (merge_union_bij eqvI) (quot_same eqv_clot_union_rel)).

  Definition merge_subgraph_e : bij (edge G1 + edge G2) (edge G12) := 
    union_bij disE.

  Lemma merge_subgraph_hom : is_hom merge_subgraph_v merge_subgraph_e xpred0.
  Proof.
    rewrite /merge_subgraph_e /merge_subgraph_v. 
    split=>//.
    - case=> x b /=; rewrite merge_unionE quot_sameE; congr pi; exact: val_inj.
    - case=> e //.
  Qed.

  Definition merge_subgraph_iso : merge_seq (G1 ⊎ G2) h ≃ merge_seq G12 h' := 
    Iso merge_subgraph_hom.

End MergeSubgraph.

