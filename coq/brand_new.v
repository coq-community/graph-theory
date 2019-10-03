Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries bij equiv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 


(* setoids *)
Structure setoid :=
  Setoid {
      car:> Type;
      eqv: relation car;
      Eqv: Equivalence eqv
    }.
Arguments eqv {_}. 
Infix "≡" := eqv (at level 79).
Existing Instance Eqv.

(* setoids with an involution *)
Structure bisetoid :=
  BiSetoid {
      setoid_of_bisetoid:> setoid;
      eqv': relation setoid_of_bisetoid;
      Eqv'_sym: Symmetric eqv';
      Eqv10: forall x y z, eqv' x y -> eqv  y z -> eqv' x z;
      Eqv01: forall x y z, eqv  x y -> eqv' y z -> eqv' x z;
      Eqv11: forall x y z, eqv' x y -> eqv' y z -> eqv  x z;
    }.
Arguments eqv' {_}.
Infix "≡'" := eqv' (at level 79).
Definition eqv_ (X: bisetoid) (b: bool) (x y: X) := if b then x ≡' y else x ≡ y.
Notation "x ≡[ b ] y" := (eqv_ b x y) (at level 79).
Instance eqv_sym {X: bisetoid} {b}: Symmetric (@eqv_ X b).
Proof. case b=> x y/=. apply Eqv'_sym. by symmetry. Qed.

Program Definition flat_bisetoid (X: Type) := {| setoid_of_bisetoid := {| eqv := @eq X |}; eqv' (_ _: X) := False |}.
Next Obligation. eauto with typeclass_instances. Qed.
Next Obligation. tauto. Qed.

(* (commutative) monoids *)
Structure monoid :=
  Monoid {
      setoid_of_monoid:> setoid;
      mon0: setoid_of_monoid;
      mon2: setoid_of_monoid -> setoid_of_monoid -> setoid_of_monoid;
      mon_eqv: Proper (@eqv _ ==> @eqv _ ==> @eqv _) mon2;
      monA: forall x y z, mon2 x (mon2 y z) ≡ mon2 (mon2 x y) z;
      monC: forall x y, mon2 x y ≡ mon2 y x;
      monU: forall x, mon2 x mon0 ≡ x
    }.
Existing Instance mon_eqv.
Arguments mon0 {_}.
Arguments mon2 {_}.


(* the algebraic structure 2pdom *)
Module pttdom.

Structure ops_ :=
  { setoid_of_ops:> setoid;
    dot: setoid_of_ops -> setoid_of_ops -> setoid_of_ops;
    par: setoid_of_ops -> setoid_of_ops -> setoid_of_ops;
    cnv: setoid_of_ops -> setoid_of_ops;
    dom: setoid_of_ops -> setoid_of_ops;
    one: setoid_of_ops }.

Bind Scope pttdom_ops with setoid_of_ops.
Delimit Scope pttdom_ops with t.
Notation "x ∥ y" := (par x y) (left associativity, at level 40, format "x ∥ y"): pttdom_ops.
Notation "x · y" := (dot x y) (left associativity, at level 25, format "x · y"): pttdom_ops.
Notation "x °"  := (cnv x) (left associativity, at level 5, format "x °"): pttdom_ops.
Notation "1"  := (one _): pttdom_ops.

Local Open Scope pttdom_ops.
Structure pttdom :=
  { ops:> ops_;
    dot_eqv: Proper (eqv ==> eqv ==> eqv) (@dot ops);
    par_eqv: Proper (eqv ==> eqv ==> eqv) (@par ops);
    cnv_eqv: Proper (eqv ==> eqv) (@cnv ops);
    dom_eqv: Proper (eqv ==> eqv) (@dom ops);
    (* domE: forall x: ops, dom x ≡ 1 ∥ x·top; *)
    parA: forall x y z: ops, x ∥ (y ∥ z) ≡ (x ∥ y) ∥ z;
    parC: forall x y: ops, x ∥ y ≡ y ∥ x;
    dotA: forall x y z: ops, x · (y · z) ≡ (x · y) · z;
    dotx1: forall x: ops, x · 1 ≡ x;
    cnvI: forall x: ops, x°° ≡ x;
    cnvpar: forall x y: ops, (x ∥ y)° ≡ x° ∥ y°;
    cnvdot: forall x y: ops, (x · y)° ≡ y° · x°;
    par11: 1 ∥ 1 ≡ one ops;
    A10: forall x y: ops, 1 ∥ x·y ≡ dom (x ∥ y°);
    (* A11: forall x: ops, x · top ≡ dom x · top; *)
    (* A12: forall x ops: X, (x∥1) · y ≡ (x∥1)·top ∥ y *)
    A13: forall x y: ops, dom(x·y) ≡ dom(x·dom y);
    A14: forall x y z: ops, dom x·(y∥z) ≡ dom x·y ∥ z;
  }.
Existing Instances dot_eqv par_eqv cnv_eqv dom_eqv.

Section derived.

 Variable X: pttdom.

 Lemma cnv1: 1° ≡ one X.
 Proof.
  rewrite <-dotx1. rewrite <-(cnvI 1) at 2.
  by rewrite <-cnvdot, dotx1, cnvI.
 Qed.

 Lemma dot1x (x: X): 1·x ≡ x.
 Proof. by rewrite <-cnvI, cnvdot, cnv1, dotx1, cnvI. Qed.

 Lemma cnv_inj (x y: X): x° ≡ y° -> x ≡ y.
 Proof. intro. rewrite <-(cnvI x), <-(cnvI y). by apply cnv_eqv. Qed.

 Lemma dotcnv (x y: X): x·y ≡ (y°·x°)°.
 Proof. apply cnv_inj. by rewrite cnvdot cnvI. Qed.

 Definition eqv' (x y: X) := x ≡ y°.
 Arguments eqv' _ _ /.
 Lemma eqv'_sym: Symmetric eqv'.
 Proof. move=> x y /= H. apply cnv_inj. by rewrite cnvI H. Qed.
 Lemma eqv10 x y z: eqv' x y -> y ≡ z -> eqv' x z.
 Proof. by move=> /= H <-. Qed.
 Lemma eqv01 x y z: x ≡ y -> eqv' y z -> eqv' x z.
 Proof. by move=> /= ->. Qed.
 Lemma eqv11 x y z: eqv' x y -> eqv' y z -> x ≡ z.
 Proof. move=> /= -> ->. apply cnvI. Qed.
 Definition pttdom_bisetoid := BiSetoid eqv'_sym eqv10 eqv01 eqv11. 

 Definition is_test (x: X) := dom x ≡ x.
 Record test := Test{ elem_of:> X ; testE: is_test elem_of }.
 Lemma one_test: is_test 1.
 Admitted.
 Canonical Structure tst_one := Test one_test. 
 Lemma dom_test x: is_test (dom x).
 Admitted.
 Canonical Structure tst_dom x := Test (dom_test x).
 Lemma par_test (a: test) (u: X): is_test (a∥u).
 Admitted.
 Canonical Structure tst_par a u := Test (par_test a u). 
 Lemma dot_test (a b: test): is_test (a·b).
 Admitted.
 Canonical Structure tst_dot a b := Test (dot_test a b).
 Lemma cnv_test (a: test): is_test (a°).
 Admitted.
 Canonical Structure tst_cnv a := Test (cnv_test a).
 Definition infer_test x y (e: elem_of y = x) := y.
 Notation "[ x ]" := (@infer_test x _ erefl).

 Definition eqv_test (a b: test) := a ≡ b.
 Arguments eqv_test _ _ /.
 Lemma eqv_test_equiv: Equivalence eqv_test.
 Admitted. 
 Canonical Structure pttdom_test_setoid := Setoid eqv_test_equiv.
 Lemma tst_dot_eqv: Proper (eqv ==> eqv ==> eqv) tst_dot.
 Proof. intros [a] [b] ? [c] [d] ?. by apply dot_eqv. Qed.
 Lemma tst_dotA: forall a b c: test, [a·[b·c]] ≡ [[a·b]·c].
 Proof. intros [a] [b] [c]. apply dotA. Qed.
 Lemma tst_dotC: forall a b: test, [a·b] ≡ [b·a].
 Admitted.
 Lemma tst_dotU: forall a: test, [a·1] ≡ a.
 Proof. intros [a]. apply dotx1. Qed.
 Canonical Structure pttdom_test_monoid := Monoid tst_dot_eqv tst_dotA tst_dotC tst_dotU.
 
End derived.
Notation "[ x ]" := (@infer_test _ x _ erefl): pttdom_ops.


(* initial algebra of terms *)
Section terms.
 Variable A: Type.
 Inductive term :=
 | tm_dot: term -> term -> term
 | tm_par: term -> term -> term
 | tm_cnv: term -> term
 | tm_dom: term -> term
 | tm_one: term
 | tm_var: A -> term.
 Bind Scope pttdom_ops with term.
 Section e.
 Variable (X: ops_) (f: A -> X).
 Fixpoint eval (u: term): X :=
   match u with
   | tm_dot u v => eval u · eval v
   | tm_par u v => eval u ∥ eval v
   | tm_cnv u => (eval u) °
   | tm_dom u => dom (eval u)
   | tm_one => 1
   | tm_var a => f a
   end.
 End e.
 Definition tm_eqv (u v: term): Prop :=
   forall (X: pttdom) (f: A -> X), eval f u ≡ eval f v.
 Hint Unfold tm_eqv.
 Lemma tm_eqv_equivalence: Equivalence tm_eqv.
 Proof.
   constructor.
     now intro.
     intros ?? H X f. specialize (H X f). by symmetry. 
     intros ??? H H' X f. specialize (H X f). specialize (H' X f). etransitivity. apply H. apply H'.
 Qed.
 Canonical Structure tm_setoid := Setoid tm_eqv_equivalence. 
 Canonical Structure tm_ops_ :=
   {| dot := tm_dot;
      par := tm_par;
      cnv := tm_cnv;
      dom := tm_dom;
      one := tm_one |}.
 Program Definition tm_pttdom: pttdom := {| ops := tm_ops_ |}.
 Next Obligation. repeat intro; simpl. by apply dot_eqv. Qed.
 Next Obligation. repeat intro; simpl. by apply par_eqv. Qed.
 Next Obligation. repeat intro; simpl. by apply cnv_eqv. Qed.
 Next Obligation. repeat intro; simpl. by apply dom_eqv. Qed.
 Next Obligation. repeat intro; simpl. by apply parA. Qed.
 Next Obligation. repeat intro; simpl. by apply parC. Qed.
 Next Obligation. repeat intro; simpl. by apply dotA. Qed.
 Next Obligation. repeat intro; simpl. by apply dotx1. Qed.
 Next Obligation. repeat intro; simpl. by apply cnvI. Qed.
 Next Obligation. repeat intro; simpl. by apply cnvpar. Qed.
 Next Obligation. repeat intro; simpl. by apply cnvdot. Qed.
 Next Obligation. repeat intro; simpl. by apply par11. Qed.
 Next Obligation. repeat intro; simpl. by apply A10. Qed.
 Next Obligation. repeat intro; simpl. by apply A13. Qed.
 Next Obligation. repeat intro; simpl. by apply A14. Qed.
 Canonical tm_pttdom. 
 
 (* Fixpoint is_test (u: term) := *)
 (*   match u with *)
 (*   | tm_dot u v => is_test u && is_test v *)
 (*   | tm_par u v => is_test u || is_test v *)
 (*   | tm_cnv u => is_test u *)
 (*   | tm_dom _ | tm_one => true *)
 (*   | tm_var _ => false *)
 (*   end. *)

 Notation test := (test tm_pttdom).
 
 Inductive nf_term :=
 | nf_test: test -> nf_term
 | nf_conn: test -> term -> test -> nf_term.

 Definition term_of_nf (t: nf_term) :=
   match t with
   | nf_test alpha => elem_of alpha (* why do we need to insert the coercion??? *)
   | nf_conn alpha u gamma => alpha · u · gamma
   end.                                         
 
 Definition nf_one := nf_test [1].
 Definition nf_var a := nf_conn [1] (tm_var a) [1].
 Definition nf_cnv u :=
   match u with
   | nf_test _ => u
   | nf_conn a u b => nf_conn b (u°) a
   end.
 Definition nf_dom u :=
   match u with
   | nf_test _ => u
   | nf_conn a u b => nf_test [a · dom (u·b)]
   end.
 Definition nf_dot u v :=
   match u,v with
   | nf_test a, nf_test b => nf_test [a·b]
   | nf_test a, nf_conn b u c => nf_conn [a·b] u c
   | nf_conn a u b, nf_test c => nf_conn a u [b·c]
   | nf_conn a u b, nf_conn c v d => nf_conn a (u·b·c·v) d
   end.
 Definition nf_par u v :=
   match u,v with
   | nf_test a, nf_test b => nf_test [a·b]
   | nf_test a, nf_conn b u c => nf_test [a ∥ b·u·c]
   | nf_conn a u b, nf_test c => nf_test [c ∥ a·u·b]
   | nf_conn a u b, nf_conn c v d => nf_conn [a·c] (u ∥ v) [b·d]
   end.
 Fixpoint nf (u: term): nf_term :=
   match u with
   | tm_dot u v => nf_dot (nf u) (nf v)
   | tm_par u v => nf_par (nf u) (nf v)
   | tm_cnv u => nf_cnv (nf u) 
   | tm_var a => nf_var a
   | tm_dom u => nf_dom (nf u)
   | tm_one => nf_one
   end.
 
 Proposition nf_correct (u: term): u ≡ term_of_nf (nf u).
 Proof.
   induction u=>//=.
   - rewrite {1}IHu1 {1}IHu2.
     case (nf u1)=>[a|a u b];
     case (nf u2)=>[c|c v d]=>//=; 
     rewrite !dotA//.
   - rewrite {1}IHu1 {1}IHu2.
     case (nf u1)=>[a|a u b];
     case (nf u2)=>[c|c v d]=>//=.
     admit.                      (* ok *)
     apply parC.
     admit.                      (* ok *)
   - rewrite {1}IHu.
     case (nf u)=>[a|a v b]=>//=.
     admit.                      (* ok *)
     rewrite 2!cnvdot dotA.
     admit. (* ok *)
   - rewrite {1}IHu.
     case (nf u)=>[a|a v b]=>//=.
     admit.                      (* ok *)
     admit.                      (* ok *)
   - rewrite dotx1.
     admit.                      (* ok *)
 Admitted.

End terms.
End pttdom.

(* labelled multigraphs (not pointed) *)
Module mgraph.

Section s.
  (* note on sectionning

     for now we have three sections in order to assume the least
     requirements for the various operations/concepts:

     Section s: Lv: Type, Le: Type 
      (basic defs operations not needing anything) 
     Section i: Lv: setoid. Le: bisetoid 
      (notions of homomorphism, isomorphism...)  
     Section m: Lv: comm_monoid. Le: bisetoid 
      (operations needing the monoid structure)

     we might want
     - to put everything in [m] in the end, for the sake of simplicity (in this case, graph2 related things could all be moved to the end) 
     - to be even more general, e.g., by not assuming setoids for operations like dot/par on graph2, which just need mon0 and mon2

  *)
    
Variables Lv Le: Type.
Record graph: Type :=
  Graph {
      vertex:> finType;
      edge: finType;
      endpoint: bool -> edge -> vertex;
      vlabel: vertex -> Lv;
      elabel: edge -> Le }.
Notation source := (endpoint false).
Notation target := (endpoint true).

(* two pointed graphs (related operations are defined only later) *)
Record graph2 :=
  Graph2 {
      graph_of :> graph;
      input : vertex graph_of;
      output : vertex graph_of }.
Arguments input [_].
Arguments output [_].
Notation point G := (@Graph2 G).


(* basic graphs and operations *)
Definition unit_graph a := @Graph [finType of unit] _ (fun _ => vfun) (fun _ => a) vfun.
Definition two_graph a b := @Graph [finType of bool] _ (fun _ => vfun) (fun v => if v then b else a) vfun.
Definition edge_graph a u b := Graph (fun b (_: unit) => b) (fun v => if v then b else a) (fun _ => u).                           

Definition add_vertex (G: graph) (l: Lv): graph :=
  @Graph [finType of option G] (edge G)
         (fun b e => Some (endpoint b e))
         (fun v => match v with Some v => vlabel v | None => l end)
         (@elabel G).

Definition add_vertex2 (G: graph2) (l: Lv): graph2 :=
  point (add_vertex G l) (Some input) (Some output).

Definition add_edge (G: graph) (x y: G) (l: Le): graph :=
  @Graph (vertex G) [finType of option (edge G)]
         (fun b e => match e with Some e => endpoint b e | None => if b then y else x end)
         (@vlabel G)
         (fun e => match e with Some e => elabel e | None => l end).

Definition add_edge2 (G: graph2) (x y: G) (u: Le): graph2 :=
  point (add_edge x y u) input output.

Definition upd_vlabel (G: graph) (x: G) (l: Lv -> Lv): graph :=
  @Graph (vertex G) (edge G)
         (@endpoint G)
         (fun v => if v==x then l (vlabel v) else vlabel v)
         (@elabel G).

Definition union (G1 G2 : graph) : graph :=
  {| vertex := [finType of G1 + G2];
     edge := [finType of edge G1 + edge G2];
     endpoint b := sumf (@endpoint G1 b) (@endpoint G2 b);
     vlabel e := match e with inl e => vlabel e | inr e => vlabel e end;
     elabel e := match e with inl e => elabel e | inr e => elabel e end;
  |}.

Definition unl {G H: graph} (x: G): union G H := inl x.
Definition unr {G H: graph} (x: H): union G H := inr x.

End s.

Bind Scope graph_scope with graph.
Delimit Scope graph_scope with G.

Arguments union {Lv Le} _ _.
Infix "⊎" := union (at level 50, left associativity) : graph_scope.
Arguments unl {_ _ _ _}.
Arguments unr {_ _ _ _}.

Notation "G ∔ [ x , u , y ]" := 
  (add_edge G x y u) (at level 20, left associativity) : graph_scope.
Notation "G ∔ a" := 
  (add_vertex G a) (at level 20, left associativity) : graph_scope.

Bind Scope graph2_scope with graph2.
Delimit Scope graph2_scope with G2.

Arguments input {_ _ _}.
Arguments output {_ _ _}.
Notation point G := (@Graph2 _ _ G).

Notation "G ∔ [ x , u , y ]" := 
  (@add_edge2 _ _ G x y u) (at level 20, left associativity) : graph2_scope.
Notation "G ∔ a" := 
  (add_vertex2 G a) (at level 20, left associativity) : graph2_scope.

Definition merge (Lv: monoid) Le (G : graph Lv Le) (r : equiv_rel G) :=
  {| vertex := quot r;
     edge := (edge G);
     endpoint b e := \pi (endpoint b e);
     vlabel c := \big[mon2/mon0]_(w | \pi w == c) vlabel w;
     elabel e := elabel e |}.
Arguments merge [_ _] _ _.
Notation merge_seq G l := (merge G (eqv_clot l)).

Definition xor b c := if b then negb c else c.
Lemma xorI a : xor a a = false.
Proof. by case a. Qed.
Lemma xorC a b : xor a b = xor b a.
Proof. by case a; case b. Qed.
Lemma xorA a b c : xor a (xor b c) = xor (xor a b) c.
Proof. by case a; case b; case c. Qed.


Section i.
Variable Lv: setoid.
Variable Le: bisetoid.
Notation graph := (graph Lv Le).
Notation graph2 := (graph2 Lv Le).

(* homomorphisms *)

Class is_hom (F G: graph) (hv: F -> G) (he: edge F -> edge G) (hd: edge F -> bool): Prop := Hom
  { endpoint_hom: forall e b, endpoint b (he e) = hv (endpoint (xor (hd e) b) e);
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
  @is_hom F G hv he hd -> @is_hom G H kv ke kd -> is_hom (kv \o hv) (ke \o he) (fun e => xor (hd e) (kd (he e))).
Proof.
  intros E E'. split.
  move=>e b=>/=. by rewrite 2!endpoint_hom xorA.
  move=>x/=. by rewrite 2!vlabel_hom. 
  move=>e/=.
  generalize (@elabel_hom _ _ _ _ _ E e). 
  generalize (@elabel_hom _ _ _ _ _ E' (he e)).
  case (hd e); case (kd (he e)); simpl.
  - apply Eqv11. 
  - apply Eqv01. 
  - apply Eqv10.
  - apply transitivity. 
Qed.

Lemma hom_sym (F G: graph) (hv: bij F G) (he: bij (edge F) (edge G)) hd:
  is_hom hv he hd -> 
  is_hom hv^-1 he^-1 (hd \o he^-1).
Proof.
  intro H. split.
  move=>e b=>/=. by rewrite -{3}(bijK' he e) endpoint_hom bijK xorA xorI. 
  move=>x/=. by rewrite -{2}(bijK' hv x) vlabel_hom.
  move=>e/=. generalize (@elabel_hom _ _ _ _ _ H (he^-1 e)). rewrite -{3}(bijK' he e) bijK'. apply symmetry. 
Qed.

(* isomorphisms *)

Record iso (F G: graph): Type :=
  Iso
    { iso_v:> bij F G;
      iso_e: bij (edge F) (edge G);
      iso_d: edge F -> bool;
      iso_hom: is_hom iso_v iso_e iso_d }.
Infix "≃" := iso (at level 79).
Notation "h '.e'" := (iso_e h) (at level 2, left associativity). 
Notation "h '.d'" := (iso_d h) (at level 2, left associativity). 
Global Existing Instance iso_hom.

(* DAMIEN: I did put [iso2] back in Prop (as well as pttdom equality
   proofs]): I think being in Type is only useful for [iso] (given our
   application, this would no longer be true if we where to build yet
   another notion on top of [iso2] where we would need access to the
   functions) *)
Definition iso2 (F G: graph2): Prop :=
  exists f: iso F G, f input = input /\ f output = output. 
Infix "≃2" := iso2 (at level 79).
    
Lemma endpoint_iso F G (h: iso F G) b e: endpoint b (h.e e) = h (endpoint (xor (h.d e) b) e).
Proof. apply endpoint_hom. Qed.

Lemma vlabel_iso F G (h: iso F G) v: vlabel (h v) ≡ vlabel v.
Proof. apply vlabel_hom. Qed.

Lemma elabel_iso F G (h: iso F G) e: elabel (h.e e) ≡[h.d e] elabel e.
Proof. apply elabel_hom. Qed.

Definition iso_id {G}: G ≃ G := @Iso _ _ bij_id bij_id _ (hom_id G). 

Definition iso_sym F G: F ≃ G -> G ≃ F.
Proof.
  move => f. 
  apply Iso with (bij_sym f) (bij_sym f.e) (f.d \o f.e^-1) =>/=.
  apply hom_sym, f. 
Defined.

Definition iso_comp F G H: F ≃ G -> G ≃ H -> F ≃ H.
Proof.
  move => f g. 
  eapply Iso with (bij_comp f g) (bij_comp f.e g.e) _=>/=.
  apply hom_comp. apply f. apply g.
Defined.

Import CMorphisms.

Global Instance iso_Equivalence: Equivalence iso.
Proof. constructor. exact @iso_id. exact @iso_sym. exact @iso_comp. Defined.

Global Instance iso2_Equivalence: RelationClasses.Equivalence iso2.
Proof.
  split.
  - intro G. by exists iso_id.
  - intros F G (f&fi&fo). exists (iso_sym f). by rewrite /= -fi -fo 2!bijK.
  - intros F G H (f&fi&fo) (g&gi&go). exists (iso_comp f g). 
    by rewrite /= fi fo gi go.
Qed.

Lemma endpoint_iso' F G (h: iso F G) b e: endpoint b (h.e^-1 e) = h^-1 (endpoint (xor (h.d (h.e^-1 e)) b) e).
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


(** isomorphisms about union and merge *)

Global Instance union_iso: Proper (iso ==> iso ==> iso) union.
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
  abstract (split; case=>//=). 
Defined.

Lemma union_A F G H: F ⊎ (G ⊎ H) ≃ F ⊎ G ⊎ H.
Proof.
  exists bij_sumA bij_sumA xpred0.
  abstract by split; case=>[|[|]].
Defined.

End i.
Arguments iso {Lv Le}.
Arguments merge {Lv Le}.
Infix "≃" := iso (at level 79).
Notation "h '.e'" := (iso_e h) (at level 2, left associativity). 
Notation "h '.d'" := (iso_d h) (at level 2, left associativity). 
Arguments iso2 {Lv Le}.
Infix "≃2" := iso2 (at level 79).


Section m.
Variable Lv: monoid.
Variable Le: bisetoid.
Notation graph := (graph Lv Le).
Notation graph2 := (graph2 Lv Le).

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
  + admit.               (* by rewrite equiv_sym eqv_clot_map_lr.  *) (* STRANGE: was working before *)
  + by rewrite eqv_clot_map_eq ?sum_eqE // inr_codom_inl.
Admitted.

Section union_merge_l.
  Variables (F G: graph) (l: pairs F).
  Definition h_union_merge_l: bij (merge_seq F l ⊎ G)%G (merge_seq (F ⊎ G) (map_pairs unl l))%G.
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
  Definition union_K_pairs := map_pairs (fun x => match x with inl x => x | inr x => k x end) h.

  Hypothesis kv: forall x: K, vlabel x = mon0.
  Hypothesis kh: forall x: K, unr x = unl (k x) %[mod (eqv_clot h)].

  Lemma equiv_clot_Kl: union_K_equiv (eqv_clot h) =2 eqv_clot union_K_pairs.
  Proof.
    move=> x y. rewrite /union_K_equiv map_equivE. 
    rewrite !eqv_clotE. set e1 := rel_of_pairs _. set e2 := rel_of_pairs _. 
    pose j := (fun x => match x with inl x => x | inr x => k x end).
    apply/idP/idP. 
    - suff S u v : equiv_of e1 u v -> equiv_of e2 (j u) (j v) by apply: S. 
      apply: equiv_ofE => {u v} [[u|u] [u'|u']] /= H. 
      all: rewrite /e2 /j; apply: sub_equiv_of; apply/mapP. 
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
  Lemma merge_union_KEl (x: F): merge_union_K (\pi (unl x)) = \pi x.
  Proof. by rewrite /=quot_union_KEl quot_sameE. Qed.
  Lemma merge_union_KEr (x: K): merge_union_K (\pi (unr x)) = \pi k x.
  Proof. by rewrite /=quot_union_KEr quot_sameE. Qed.
End merge_union_K.
Global Opaque merge_union_K.

(* two pointed graphs operations *)

Definition g2_par (F G: graph2) :=
  point (merge_seq (F ⊎ G) [::(unl input,unr input); (unl output,unr output)])
        (\pi (unl input)) (\pi (unr output)).

Definition g2_dot (F G: graph2) :=
  point (merge_seq (F ⊎ G) [::(unl output,unr input)])
        (\pi (unl input)) (\pi (unr output)).

Definition g2_cnv (F: graph2) :=
  point F output input.

Definition g2_dom (F: graph2) :=
  point F input input.

Definition g2_one: graph2 :=
  point (unit_graph _ mon0) tt tt.

Definition g2_top: graph2 :=
  point (two_graph _ mon0 mon0) false true.

Definition g2_var a: graph2 :=
  point (edge_graph mon0 a mon0) false true.

Definition add_test (G: graph2) (x: G) (a: Lv): graph2 :=
  point (upd_vlabel x (mon2 a)) input output.

Import pttdom. 

(* Note: maybe nicer to prove that this is a ptt algebra (with top)
  and deduce automatically that this is a pttdom (as we did in the previous version) *)
Canonical Structure g2_setoid: setoid := Setoid (iso2_Equivalence Lv Le). 
Canonical Structure g2_ops: ops_ :=
  {| dot := g2_dot;
     par := g2_par;
     cnv := g2_cnv;
     dom := g2_dom;
     one := g2_one |}.
Program Definition g2_pttdom: pttdom := {| ops := g2_ops |}.
Admit Obligations.
Canonical g2_pttdom.

End m. 
Notation "G [tst x <- a ]" := 
  (@add_test _ _ G x a) (at level 20, left associativity, format "G [tst  x  <-  a ]") : graph2_scope.

End mgraph.


Module rewriting.
Import mgraph pttdom Morphisms.
Section s.
Variable A: Type.
Notation test := (test (tm_pttdom A)). 
Notation term := (term A).
Notation graph := (graph test term).
Notation graph2 := (graph2 test term).

(* HACK: unluckily, declaring [pttdom_bisetoid] as canonical
   does not make it possible to solve [tm_setoid A = setoid_of_bisetoid _]
   which is needed at a few places.
   we solve this by declaring the following instance as canonical *)
Canonical Structure tm_bisetoid :=
  @BiSetoid (tm_setoid A) (@eqv' (tm_pttdom A))
            (@eqv'_sym (tm_pttdom A))
            (@eqv10 (tm_pttdom A)) (@eqv01 (tm_pttdom A)) (@eqv11 (tm_pttdom A)).
(* we would be happier with the following declaration, but Eval hnf does not simplify enough... *)
(* Canonical Structure tm_bisetoid := Eval hnf in pttdom_bisetoid (tm_pttdom A). *)
Check erefl: tm_setoid A = setoid_of_bisetoid _. 

(* Universe S. *)
(* TODO: improve notation scopes *)
Inductive step: graph2 -> graph2 -> Prop (* Type@{S} *) :=
  | step_v0: forall G alpha,
      step
        (G ∔ alpha)
        G
  | step_v1: forall (G: graph2) x u alpha,
      step
        (G ∔ alpha ∔ [Some x, u, None])
        (G [tst x <- [dom (u·alpha)]%t])
  | step_v2: forall G x y u alpha v,
      step
        (G ∔ alpha ∔ [Some x, u, None] ∔ [None, v, Some y])
        (G ∔ [x, (u·alpha·v)%t, y])
  | step_e0: forall G x u,
      step
        (G ∔ [x, u, x])
        (G [tst x <- [1∥u]%t])
  | step_e2: forall G x y u v,
      step
        (G ∔ [x, u, y] ∔ [x, v, y])
        (G ∔ [x, (u∥v)%t, y]).

Inductive steps: relation graph2 :=
  | iso_step: subrelation iso2 steps
  | cons_step: forall F G H H', iso2 F G -> step G H -> steps H H' -> steps F H'.
Existing Instance iso_step.


(* TODO: let reflexivity belong to // again (should work in the two proofs below) *)
Instance PreOrder_steps: PreOrder steps.
Proof.
  split. intro. apply iso_step. reflexivity. 
  intros F G H S S'. induction S as [F G I|F G G' G'' I S _ IH].
  - destruct S' as [F' G' I'|F' G' G'' G''' I' S'].
    apply iso_step. etransitivity; eassumption.
    apply cons_step with G' G''=>//. etransitivity; eassumption.
  - apply cons_step with G G'=>//. by apply IH. 
Qed.

Instance one_step: subrelation step steps.
Proof. intros F G S. apply cons_step with F G=>//. reflexivity. Qed.

Proposition local_confluence G G' H H':
    step G G' -> step H H' -> G ≃2 H -> 
    exists F, steps G' F /\ steps H' F.
Admitted.                       (* through open confluence *)


Definition measure (G: graph2) := #|vertex G| + #|edge G|.

Lemma step_decreases G H: step G H -> measure H < measure G.
Proof.
  rewrite /measure.
  case; intros=>/=; by rewrite !card_option ?addSnnS ?addnS.
Qed.

Lemma iso_stagnates G H: G ≃2 H -> measure H = measure G.
Proof. move=>[l _]. by rewrite /measure (card_bij (iso_v l)) (card_bij (iso_e l)). Qed.

Proposition confluence F: forall G H, steps F G -> steps F H -> exists F', steps G F' /\ steps H F'.
Proof.
  induction F as [F_ IH] using (well_founded_induction_type (Wf_nat.well_founded_ltof _ measure)).
  move=> G H S.
  move: G H S IH => _ H [F G FG|F__ F0 G' G FF0 FG GG] IH FH.
  - exists H; split=>//. by rewrite -FG. 
  - move: H FH IH FF0=> _ [F H FH|F F1 H' H FF1 FH HH] IH FF0. 
      exists G; split=>//. rewrite -FH. eauto using cons_step.
    destruct (local_confluence FG FH) as [M[GM HM]]. by rewrite -FF0. 
    destruct (fun D => IH G' D _ _ GG GM) as [L[GL ML]].
     rewrite /Wf_nat.ltof -(iso_stagnates FF0). apply /ltP. by apply step_decreases.
    have HL: steps H' L by transitivity M. 
    destruct (fun D => IH H' D _ _ HL HH) as [R[LR HR]].
     rewrite /Wf_nat.ltof -(iso_stagnates FF1). apply /ltP. by apply step_decreases.
     exists R. split=>//. by transitivity L.
Qed.

Lemma step_to_steps f:
  Proper (iso2 ==> iso2) f -> Proper (step ==> steps) f -> Proper (steps ==> steps) f.
Proof.
  intros If Sf G G' S.
  induction S as [G G' I|G G' F H' I S Ss IH].
  - by apply iso_step, If.
  - etransitivity. apply iso_step, If, I.
    etransitivity. apply Sf, S. apply IH. 
Qed.

Instance cnv_steps: Proper (steps ==> steps) (@cnv _).
Proof.
  apply step_to_steps. by apply cnv_eqv.
  move=>F G S. eapply one_step. destruct S.
  * apply (@step_v0 (point G output input) alpha).
  * apply (@step_v1 (point G output input) x u alpha).
  * apply (@step_v2 (point G output input) x y u alpha v).
  * apply (@step_e0 (point G output input) x u).
  * apply (@step_e2 (point G output input) x y u v).
Qed.

Instance dom_steps: Proper (steps ==> steps) (@dom _).
Proof.
  apply step_to_steps. by apply dom_eqv.
  move=>F G S. eapply one_step. destruct S.
  * apply (@step_v0 (point G input input) alpha).
  * apply (@step_v1 (point G input input) x u alpha).
  * apply (@step_v2 (point G input input) x y u alpha v).
  * apply (@step_e0 (point G input input) x u).
  * apply (@step_e2 (point G input input) x y u v).
Qed.

Lemma dot_steps_l G G' H: steps G G' -> steps (G·H)%t (G'·H)%t.
Proof.
  apply (step_to_steps (f:=fun G => G·H)%t) => {G G'}.
  - move=> ?? E. apply dot_eqv=>//. reflexivity. 
  - move => G G' GG'. etransitivity. (* apply: (@steps_merge G') => //=. *)
    (* + rewrite /admissible_l/=. by rewrite !inE eqxx. *)
    (* + by rewrite /replace_ioL/= eqxx.  *)
Admitted.

Lemma dot_steps_r G G' H: steps G G' -> steps (H·G)%t (H·G')%t.
Proof.
  move => GG'. rewrite dotcnv. transitivity ((G'°·H°)°)%t. 
    by apply cnv_steps, dot_steps_l, cnv_steps.
    by rewrite -dotcnv. 
Qed.

Instance dot_steps: Proper (steps ==> steps ==> steps) (@dot _).
Proof.
  repeat intro. by etransitivity; [apply dot_steps_l | apply dot_steps_r].
Qed.

Lemma par_steps_l G G' H: steps G G' -> steps (G∥H)%t (G'∥H)%t.
Proof.
  apply (step_to_steps (f:=fun G => (G∥H)%t))  => {G G'}. 
  - move => G G' I. apply par_eqv=>//. reflexivity.
  - move => G G' step_G_G'. 
    (* etransitivity. apply: (@steps_merge G') => //=. *)
    (* + by rewrite /admissible_l/= !inE !eqxx. *)
    (* + rewrite /replace_ioL/= !eqxx. case: ifP => [E|//]. *)
    (*   rewrite (step_IO step_G_G') in E. *)
    (*   by rewrite -[in (inl output,inr input)](eqP E).  *)
Admitted.

Lemma par_steps_r G G' H: steps G G' -> steps (H∥G)%t (H∥G')%t.
Proof.
  intro. rewrite parC. etransitivity. apply par_steps_l. eassumption.
  by rewrite parC. 
Qed.

Instance par_steps: Proper (steps ==> steps ==> steps) (@par _).
Proof.
  repeat intro. by etransitivity; [apply par_steps_l | apply par_steps_r].
Qed.


Definition graph_of_term: term -> graph2 := eval (fun a => g2_var _ (tm_var a)). 

Definition graph_of_nf_term (t: nf_term A): graph2 :=
  match t with
  | nf_test a => point (unit_graph _ a) tt tt
  | nf_conn a u b => point (edge_graph a u b) false true
  end.


(* Some of these isomorphism lemma could be slight generalisations of lemmas
   used to get the pttdom laws on graph2 *)
Lemma ldotunit (G: graph2) a: (G · point (unit_graph _ a) tt tt)%t ≃2 G [tst output <- a].
Admitted.

Lemma lunitdot (G: graph2) a: (point (unit_graph _ a) tt tt · G)%t ≃2 G [tst input <- a].
Admitted.

Lemma lparunitunit (a b: test):
  (par (point (unit_graph term a) tt tt) (point (unit_graph _ b) tt tt))
    ≃2
    point (unit_graph _ [a·b]%t) tt tt.
Admitted.

Lemma lparedgeunit (u: term) (a b c: test):
  (par (point (edge_graph a u b) false true) (point (unit_graph _ c) tt tt))
    ≃2
    point (unit_graph _ [c∥a·u·b]%t) tt tt.
Admitted.
       
Lemma add_test_point (a c: test):
  (point (unit_graph term a) tt tt [tst tt <- c])
    ≃2
    (point (unit_graph _ [a·c]%t) tt tt).
Admitted.                       (* could be inlined for now *)

Lemma add_test_edge (x: bool) (u: term) (a b c: test):
  (point (edge_graph a u b) false true [tst x <- c])
    ≃2
    (point (edge_graph (if x then a else [c·a]) u (if x then [b·c] else b))%t false true).
Admitted.


Proposition reduce (u: term): steps (graph_of_term u) (graph_of_nf_term (nf u)).
Proof.
  induction u=>//=.
  - etransitivity. apply dot_steps; [apply IHu1|apply IHu2].
    case (nf u1)=>[a|a u b];
    case (nf u2)=>[c|c v d]=>/=.
    * apply iso_step.
      rewrite ldotunit. simpl.
      apply add_test_point. 
    * apply iso_step.
      rewrite lunitdot. simpl.
      apply add_test_edge. 
    * apply iso_step.
      setoid_rewrite ldotunit. simpl.
      apply add_test_edge. 
    * etransitivity. apply iso_step.
      2: etransitivity.
      2: apply one_step, (step_v2 (G:=point (two_graph _ a d) false true) false true u [b·c]%t v).
      2: apply iso_step.
      (* 2: liso_step (bij_sym unit_option_void)=>/=. *)
      (* 2: liso bij_id bij_id (fun _ => false)=>//= _; by rewrite !dotA. *)
      (* liso_step merge43=>/=.  *)
      (* liso_step two_option_option_void=>/=. *)
      (* liso bij_id bij_id (fun _ => false)=>//=; *)
      (*      (repeat case)=>//=; *)
      (*      rewrite ?merge43E ?merge43E' //=. *)
      admit.
      admit.
      
  - etransitivity. apply par_steps; [apply IHu1|apply IHu2].
    case (nf u1)=>[a|a u b];
    case (nf u2)=>[c|c v d]=>/=.
    * apply iso_step. apply lparunitunit.
    * apply iso_step. rewrite parC. apply lparedgeunit.
    * apply iso_step. apply lparedgeunit.
    * etransitivity. apply iso_step.
      2: etransitivity.
      2: apply one_step, (step_e2 (G:=point (two_graph _ [a·c] [b·d])%t false true) false true u v).
      admit.
      apply iso_step.
      (* liso_step (bij_sym unit_option_void)=>/=.  *)
      (* liso bij_id bij_id (fun _ => false)=>//. *)
      admit.
      
  - etransitivity. apply cnv_steps, IHu. 
    case (nf u)=>[a|a v b]=>//=.
    apply iso_step.
    (* rewrite /lcnv/=. liso bool_swap bij_id (fun _ => true)=>//=. *)
    (*   by case. *)
    (*   move=>_. apply cnvI. *)
    admit.
      
  - etransitivity. apply dom_steps, IHu. 
    case (nf u)=>[a|a v b]=>//=.
    etransitivity. apply iso_step.
    2: etransitivity. 2: apply one_step, (@step_v1 (point (unit_graph _ a) tt tt) tt v b).
    (* liso_step bool_option_unit=>/=.  *)
    (* liso_step unit_option_void=>/=. *)
    (* liso bij_id bij_id (fun _ => false)=>//=; case=>//. *)
    (* apply liso_step. *)
    (* liso bij_id bij_id (fun _ => false)=>//=; case=>//. *)
    (* apply dotC.  *)
Admitted.

Lemma nf_steps s: forall H, steps (graph_of_nf_term s) H -> graph_of_nf_term s ≃2 H.
Proof.
  suff E: forall G H, steps G H -> G ≃2 graph_of_nf_term s -> G ≃2 H.
    by intros; apply E=>//; reflexivity. 
  destruct 1 as [G H I|G' G H H' I S _ _]=>//L.
  - exfalso. setoid_rewrite I in L. clear -S L. destruct L as [L [Li Lo]]. generalize (card_bij (iso_e L)).
    destruct s; destruct S; simpl in *; (try by rewrite !card_option ?card_unit ?card_void); move=>_.
    * generalize (card_bij (iso_v L)). rewrite card_unit card_option.
      have H: 0 < #|G|. apply /card_gt0P. by exists input.
      revert H. case #|G|; discriminate.
    * revert Li Lo. 
      suff E: input=output :>G by congruence.
      apply (card_le1 (D:=predT))=>//. 
      apply iso_v, card_bij in L. rewrite card_option card_bool in L.
        by injection L=>->.
    * have E: forall y, L None <> L (Some y) by intros y H; generalize (bij_injective (f:=L) H). 
      case_eq (L None).
       generalize (E output). simpl. congruence. 
       generalize (E input). simpl. congruence. 
    * generalize (endpoint_iso L false None). generalize (endpoint_iso L true None).
      case iso_d; simpl; congruence.
Qed.

Lemma iso_nf (s t: nf_term A):
  graph_of_nf_term s ≃2 graph_of_nf_term t ->
  term_of_nf s ≡ term_of_nf t.
Proof.
  case s=>[a|a u b];
  case t=>[c|c v d]=>/=; move=> [h [hi ho]].
  - symmetry. exact (vlabel_iso h tt).
  - exfalso.
    generalize (bijK' h false). generalize (bijK' h true).
    case (h^-1 true). case (h^-1 false). congruence. 
  - exfalso.
    generalize (bijK h false). generalize (bijK h true).
    case (h true). case (h false). congruence.
  - generalize (vlabel_iso h false).
    generalize (vlabel_iso h true).
    simpl in *. 
    rewrite hi ho /=. 
    generalize (elabel_iso h tt).
    generalize (endpoint_iso h (h.d tt) tt).
    case (iso_d h tt)=>/=. by rewrite hi.
    intros. symmetry. apply dot_eqv=>//. apply dot_eqv=>//. 
Qed.

Theorem completeness (u v: term): graph_of_term u ≃2 graph_of_term v -> u ≡ v.
Proof.
  move=>h.
  pose proof (reduce u) as H.
  have H' : steps (graph_of_term u) (graph_of_nf_term (nf v))
    by rewrite h; apply reduce. 
  case (confluence H H')=>F [/nf_steps HF /nf_steps HF'].
  rewrite-> (nf_correct u), (nf_correct v).
  apply iso_nf. by rewrite HF'. 
Qed.

(* Note: now one could go easily one step further and get soundness and completeness w.r.t. letter-labelled graphs
   (using g2_pttdom on the flat bisetoid)
 *)

End s.
End rewriting.

