Require Import Morphisms RelationClasses.
Require CMorphisms CRelationClasses. (* To be used explicitly *)
From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries bij equiv.
Require Export structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

(** Note on Equivalences and Morphisms: This development mixes both
rewriting in Prop (e.g., 2pdom algebras) and rewriting in Type (e.g.,
iso). To facilitate this, we import the Prop versions and introduce
notations for the Type versions. This leads to the follwing usage
patterns: 

- Morphisms and Relation classes should be imported as needed.
- CMorhisms and CRelationClasses should be Required but never imported.
- There are notations CEquivalence and CProper that refer to the Type versions.
- The "_ ==> ..." argumentof CProper is parsed using the respectful from CMorphisms.
*)

Notation CEquivalence := CRelationClasses.Equivalence.
Notation CProper := CMorphisms.Proper.
Delimit Scope csignature with C.
Notation "A ==> B" := (@CMorphisms.respectful _ _ (A%C) (B%C)) : csignature.
Arguments CMorphisms.Proper [A] _%C _.

(* labelled multigraphs and their operations *)

Section s.
    
Variable L: labels.
Notation Lv := (lv L).  
Notation Le := (le L).  

(* labelled multigraphs (not pointed) *)
Record graph: Type :=
  Graph {
      vertex:> finType;
      edge: finType;
      endpoint: bool -> edge -> vertex; (* source and target functions *)
      vlabel: vertex -> Lv;
      elabel: edge -> Le }.

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
         (fun v => if v==x then mon2 a (vlabel v) else vlabel v)
         (@elabel G).
Notation "G [tst  x <- a ]" := (@add_vlabel G x a) (at level 20, left associativity).

(** ** Subgraphs and Induced Subgraphs *)

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
End Subgraphs.


Section Defs.
Variables (G : graph).
Implicit Types (x y : G).

Definition incident x e := [exists b, endpoint b e == x].
Definition edges_at x := [set e | incident x e].

Definition edges_in (V : {set G}) := (\bigcup_(x in V) edges_at x)%SET.

Lemma edges_in1 (x : G) : edges_in [set x] = edges_at x. 
Proof. by rewrite /edges_in big_set1. Qed.
End Defs.

Arguments edges_at [G] x, G x.

Lemma consistent_del1 (G : graph) (x : G) : consistent [set~ x] (~: edges_at x).
Admitted.

(* Commonly used subgraphs *)
Definition del_vertex (G : graph) (z : G) : graph := 
  subgraph_for (@consistent_del1 G z).


(* disjoint union of two graphs *)
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

(* merging vertices according to an equivalence relation *)
Definition merge (G: graph) (r : equiv_rel G) :=
  {| vertex := quot r;
     edge := (edge G);
     endpoint b e := \pi (endpoint b e);
     vlabel c := \big[mon2/mon0]_(w | \pi w == c) vlabel w;
     elabel e := elabel e |}.
Arguments merge _ _: clear implicits. 
Notation merge_seq G l := (merge G (eqv_clot l)).

(* derived operations *)
Definition two_graph a b := unit_graph a ⊎ unit_graph b.
Definition edge_graph a u b := two_graph a b ∔ [inl tt, u, inr tt].                           
Definition add_vertex G a := G ⊎ unit_graph a.
Notation "G ∔ a" := (add_vertex G a) (at level 20, left associativity).


(* xor operation on Booleans, such that [xor false b] is convertible to [b] *)
Lemma addbxx x : x (+) x = false. 
Proof. by rewrite -negb_eqb eqxx. Qed.

(* homomorphisms *)
Class is_hom (F G: graph) (hv: F -> G) (he: edge F -> edge G) (hd: edge F -> bool): Prop := Hom
  { endpoint_hom: forall e b, endpoint b (he e) = hv (endpoint (hd e (+) b) e);
    vlabel_hom: forall v, vlabel (hv v) ≡ vlabel v;
    elabel_hom: forall e, elabel (he e) ≡[hd e] elabel e;
  }.
(* nota: 
   - when using the flat_bisetoid for Le, the edge swapping funcion [hd] 
     may only be constantly false
   - when the edge swapping function [hd] is constantly false, the
     types of [endpoint_hom] and [elabel_hom] in the above definition
     simplify to the simple, non swapping, notion of homomorphism *)

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
  move=>e b=>/=. by rewrite -{3}(bijK' he e) endpoint_hom bijK addbA addbxx. 
  move=>x/=. by rewrite -{2}(bijK' hv x) vlabel_hom.
  move=>e/=. generalize (@elabel_hom _ _ _ _ _ H (he^-1 e)). rewrite -{3}(bijK' he e) bijK'. by symmetry. 
Qed.

(* isomorphisms *)

Record iso (F G: graph): Type :=
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
Hint Resolve iso_id.         (* so that [by] gets it... *)

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


(* isomorphisms about [unit_graph] *)

Lemma unit_graph_eqv a b: a ≡ b -> unit_graph a ≃ unit_graph b.
Proof.
  intro. Iso bij_id bij_id xpred0.
  abstract by split=>//=;symmetry.
Defined.


(* isomorphisms about [add_edge] *)

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


(* isomorphisms about [add_vlabel] *)

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

Lemma add_vlabel_edge F x a y u z: F [tst x <- a] ∔ [y, u, z] ≃ F ∔ [y, u, z] [tst x <- a].
Proof. reflexivity. Defined.

Lemma add_vlabel_unit a x b: unit_graph a [tst x <- b] ≃ unit_graph (mon2 b a).
Proof. reflexivity. Defined.


(* isomorphisms about subgraphs *)

Lemma subgraph_for_iso' G H (h : G ≃ H) 
  (VG :{set G}) (VH : {set H}) (EG : {set edge G}) (EH : {set edge H})
  (con1 : consistent VG EG) (con2 : consistent VH EH) :
  VH = h @: VG -> EH = h.e @: EG ->
  subgraph_for con1 ≃ subgraph_for con2.
Proof.
  move => eq_V eq_E. 
  eapply Iso. 
Admitted.

Lemma del_vertex_iso' F G (h : F ≃ G) (z : F) (z' : G) : 
  h z = z' -> del_vertex z ≃ del_vertex z'.
Proof.
  move => h_z. apply: (subgraph_for_iso' (h := h)). 
  admit.
  admit.
Qed.


(* isomorphisms about [union] *)

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
 
Lemma union_add_edge_l F G x u y: F ∔ [x, u, y] ⊎ G ≃ (F ⊎ G) ∔ [inl x, u, inl y].
Proof.
  Iso bij_id (@sum_option_l _ _) xpred0.
  abstract by split; repeat case.
Defined.

Lemma union_add_edge_r F G x u y: F ⊎ G ∔ [x, u, y] ≃ (F ⊎ G) ∔ [inr x, u, inr y].
Proof.
  etransitivity. apply union_C. 
  etransitivity. apply union_add_edge_l.
  etransitivity. apply (add_edge_iso (union_C _ _)).
  reflexivity.
Defined.

Lemma union_add_vlabel_l F G x a: F [tst x <- a] ⊎ G ≃ (F ⊎ G) [tst inl x <- a].
Proof. 
  Iso bij_id bij_id xpred0.
  abstract by split; repeat case.
Defined.

Lemma union_add_vlabel_r F G x a: F ⊎ G [tst x <- a] ≃ (F ⊎ G) [tst inr x <- a].
Proof.
  etransitivity. apply union_C. 
  etransitivity. apply union_add_vlabel_l.
  etransitivity. apply (add_vlabel_iso (union_C _ _)).
  reflexivity.
Defined.


(* isomorphisms about [merge] *)

Section merge_surj.
 (* this one seems nice, but check that we really need it first *)
 Variable (G: graph) (r: equiv_rel G).
 Variable (H: graph) (fv: G -> H).
 Variable (fe: bij (edge G) (edge H)).
 Hypothesis Hsurj: surjective fv.
 Hypothesis Hendpoints: forall b e, fv (endpoint b e) = endpoint b (fe e).
 Hypothesis Helabel: forall e, elabel (fe e) ≡ elabel e.
 Hypothesis Hvlabel: forall y, vlabel y ≡ \big[mon2/mon0]_(x | fv x == y) vlabel x.
 Lemma merge_surj: merge G r ≃ H.
 Admitted.
 Lemma merge_surjE (x: G): merge_surj (\pi x) = fv x.
 Admitted.
End merge_surj.


Section h_merge_nothing'.
 Variables (F: graph) (r: equiv_rel F).
 Hypothesis H: forall x y: F, r x y -> x=y.
 Lemma merge_nothing': merge F r ≃ F.
 Proof.
   exists (quot_id H: bij (merge F r) F) bij_id xpred0.
   split; intros; rewrite /=?quot_idE?H//.
 Admitted.
End h_merge_nothing'.

Section merge_merge.
  Variables (F: graph) (e: equiv_rel F) (e': equiv_rel (merge F e)).
  Lemma hom_merge_merge: is_hom (quot_quot e': merge _ e' -> merge F _) bij_id xpred0.
  Proof.
    split; intros=>//. by rewrite /=-equiv_comp_pi.
  Admitted.
  Lemma merge_merge: merge (merge F e) e' ≃ merge F (equiv_comp e').
  Proof. eexists. eapply hom_merge_merge. Defined.
End merge_merge.

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
    - rewrite quot_sameE. admit. 
    - apply elabel_iso.
  Admitted.
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
 Admitted.
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
 Admitted.                      (* need Transparent merge_nothing *)
 (* Proof. apply quot_idE. Qed. *)
End merge_nothing.
Global Opaque merge_nothing.

Section merge_merge_seq.
  Variables (F: graph) (h k: pairs F) (k': pairs (merge_seq F h)).
  Hypothesis kk': k' = map_pairs (pi (eqv_clot h)) k.
  Definition h_merge_merge_seq: bij (merge_seq (merge_seq F h) k') (merge_seq F (h++k)).
  Proof.
    eapply bij_comp. apply quot_quot. apply quot_same.
    rewrite kk'. apply eqv_clot_cat.
  Defined.
  Lemma hom_merge_merge_seq: is_hom h_merge_merge_seq bij_id xpred0.
  Proof.
    split; intros=>//; try by rewrite /=quot_quotE quot_sameE.
  Admitted.
  Definition merge_merge_seq: merge_seq (merge_seq F h) k' ≃ merge_seq F (h++k) :=
    Iso hom_merge_merge_seq.
  Lemma merge_merge_seqE (x: F): merge_merge_seq (\pi (\pi x)) = \pi x.
  Proof. by rewrite /=quot_quotE quot_sameE. Qed.
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
Admitted.
Lemma merge_add_edgeE (G: graph) (r: equiv_rel G) x u y (z: G): @merge_add_edge G r x u y (\pi z) = \pi z.
Admitted.

Lemma merge_add_vlabel (G: graph) (r: equiv_rel G) x a: merge (G [tst x <- a]) r ≃ merge G r [tst \pi x <- a].
Admitted.
Lemma merge_add_vlabelE (G: graph) (r: equiv_rel G) x a (z: G): @merge_add_vlabel G r x a (\pi z) = \pi z.
Admitted.



(* isomorphisms about [union] and [merge] *)

Section union_merge_l.
  Variables (F G: graph) (l: pairs F).
  Definition h_union_merge_l: bij (merge_seq F l ⊎ G) (merge_seq (F ⊎ G) (map_pairs unl l)).
  Proof. eapply bij_comp. apply union_quot_l. apply quot_same. apply union_equiv_l_eqv_clot. Defined.
  Lemma hom_union_merge_l: is_hom h_union_merge_l bij_id xpred0.
  Proof.
    try (split; case; intros=>//=; rewrite ?union_quot_lEl ?union_quot_lEr quot_sameE //).
  Admitted.
  Definition union_merge_l: merge_seq F l ⊎ G ≃ merge_seq (F ⊎ G) (map_pairs unl l) :=
    Iso hom_union_merge_l.
  Lemma union_merge_lEl (x: F): union_merge_l (inl (\pi x)) = \pi unl x.
  Proof. by rewrite /=union_quot_lEl quot_sameE. Qed.
  Lemma union_merge_lEr (x: G): union_merge_l (unr x) = \pi unr x.
  Proof. by rewrite /=union_quot_lEr quot_sameE. Qed.
End union_merge_l.  
Global Opaque union_merge_l.

Lemma map_map_pairs {A B C} (f: A -> B) (g: B -> C) l: map_pairs g (map_pairs f l) = map_pairs (g \o f) l.
Proof. by rewrite /map_pairs -map_comp. Qed.

Section union_merge_r.
  Variables (F G: graph) (l: pairs G).
  Lemma union_merge_r: F ⊎ merge_seq G l ≃ merge_seq (F ⊎ G) (map_pairs unr l).
  Proof.
    eapply iso_comp. apply union_C.
    eapply iso_comp. apply union_merge_l.
    eapply iso_comp. apply (merge_iso (union_C _ _)).
    apply merge_same. abstract by rewrite map_map_pairs. 
  Defined.
  Lemma union_merge_rEr (x: G): union_merge_r (inr (\pi x)) = \pi (unr x).
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

  Hypothesis kv: forall x: K, vlabel x = mon0.
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
  Admitted.

  Definition merge_union_K: merge_seq (F ⊎ K) h ≃ merge_seq F union_K_pairs :=
    Iso hom_merge_union_K.
  Lemma merge_union_KE (x: F+K): merge_union_K (\pi x) = \pi (sum_left k x).
  Proof. by rewrite /=quot_union_KE quot_sameE. Qed.
End merge_union_K.
Global Opaque merge_union_K.

Lemma merge_two a b: merge_seq (unit_graph a ⊎ unit_graph b) [:: (inl tt,inr tt)] ≃ unit_graph (mon2 a b).
Admitted.
Lemma merge_twoE a b x: merge_two a b x = tt.
Admitted.  

(* other isomorphisms on concrete graphs *)

Lemma two_graph_swap a b: two_graph a b ≃ two_graph b a.
Proof. apply union_C. Defined.


End s. 

Notation source := (endpoint false).
Notation target := (endpoint true).

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
  (add_vertex G a) (at level 20, left associativity) : graph_scope.
Notation "G [tst  x <- a ]" :=
  (add_vlabel G x a) (at level 20, left associativity) : graph_scope.

Arguments merge {L} _ _.
Notation merge_seq G l := (merge G (eqv_clot l)).

Arguments iso {L}.
Infix "≃" := iso (at level 79).
Notation "h '.e'" := (iso_e h) (at level 2, left associativity, format "h '.e'").
Notation "h '.d'" := (iso_d h) (at level 2, left associativity, format "h '.d'"). 

Global Hint Resolve iso_id.         (* so that [by] gets it... *)

Arguments edges_at [L G] x, [L] G x.
