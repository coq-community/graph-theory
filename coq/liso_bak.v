Require Import Setoid CMorphisms Morphisms.
From mathcomp Require Import all_ssreflect.

Require Import edone set_tac finite_quotient preliminaries bij equiv.
Require Import multigraph_new.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

(** 2pdom terms  *)

Inductive term :=
| dot: term -> term -> term
| par: term -> term -> term
| cnv: term -> term
| dom: term -> term
| one: term
| var: sym -> term.

Bind Scope pttdom_ops with term.
Open Scope pttdom_ops.
Notation "x ∥ y" := (par x y) (left associativity, at level 25, format "x ∥ y"): pttdom_ops.
Notation "x · y" := (dot x y) (left associativity, at level 20, format "x · y"): pttdom_ops.
Notation "x °"  := (cnv x) (left associativity, at level 5, format "x °"): pttdom_ops.
Notation "1"  := (one): pttdom_ops.

Reserved Notation "x ≡ y" (at level 79).

(** 2pdom axioms  *)
(* NOTE: the 2pdom axioms are listed here, while the rest of the code is for 2p + TaT=T
   (to be fixed later)
 *)

Inductive weq: relation term :=
| weq_refl: Reflexive weq
| weq_trans: Transitive weq
| weq_sym: Symmetric weq
| dot_weq: Proper (weq ==> weq ==> weq) dot
| par_weq: Proper (weq ==> weq ==> weq) par
| cnv_weq: Proper (weq ==> weq) cnv
| dom_weq: Proper (weq ==> weq) dom
| parA: forall x y z, x ∥ (y ∥ z) ≡ (x ∥ y) ∥ z
| parC: forall x y, x ∥ y ≡ y ∥ x
| dotA: forall x y z, x · (y · z) ≡ (x · y) · z
| dotx1: forall x, x · 1 ≡ x
| cnvI: forall x, x°° ≡ x
| cnvpar: forall x y, (x ∥ y)° ≡ x° ∥ y°
| cnvdot: forall x y, (x · y)° ≡ y° · x°
| par11: 1 ∥ 1 ≡ 1
| A10: forall x y, 1 ∥ x·y ≡ dom (x ∥ y°)
| A13: forall x y, dom (x·y) ≡ dom (x·dom y)
| A14: forall x y z, dom x·(y ∥ z) ≡ dom x · y ∥ z
where "x ≡ y" := (weq x y).

Instance Equivalence_weq: Equivalence weq.
Proof. split. apply weq_refl. apply weq_sym. apply weq_trans. Qed.
Existing Instance dot_weq.
Existing Instance par_weq.
Existing Instance cnv_weq.
Existing Instance dom_weq.

Canonical Structure term_setoid := Setoid Equivalence_weq.

(** * tests *)

Fixpoint is_test (u: term) :=
  match u with
  | dot u v => is_test u && is_test v
  | par u v => is_test u || is_test v
  | cnv u => is_test u
  | dom _ | one => true
  | var _ => false
  end.

Record test := Test{ term_of:> term ; testE: is_test term_of }.
Definition infer_test x y (e: term_of y = x) := y.
Notation "[ x ]" := (@infer_test x _ erefl).

Canonical Structure tst_one := @Test 1 erefl. 
Canonical Structure tst_dom u := @Test (dom u) erefl.
Lemma par_test (a: test) (u: term): is_test (a∥u).
Proof. by rewrite /=testE. Qed.
Canonical Structure tst_par a u := Test (par_test a u). 
Lemma dot_test (a b: test): is_test (a·b).
Proof. by rewrite /=2!testE. Qed.
Canonical Structure tst_dot a b := Test (dot_test a b).
Lemma cnv_test (a: test): is_test (a°).
Proof. by rewrite /=testE. Qed.
Canonical Structure tst_cnv a := Test (cnv_test a).


(** Some facts about 2pdom algebras *)

Lemma cnvone : 1° ≡ 1.
Proof. rewrite -{1}[1°]dotx1 -{2}[1]cnvI. by rewrite -cnvdot dotx1 cnvI. Qed.

Lemma tstdom' u : 1 ∥ dom u ≡ dom u.
Proof. by rewrite parC -{2}[dom u]dotx1 -{2}par11 A14 dotx1. Qed.

Lemma domtst' u : dom (1 ∥ u) ≡ 1 ∥ u.
Proof. by rewrite parC -{1}cnvone -A10 dotx1 parC. Qed.

Lemma cnvtst' u : (1∥u)° ≡ 1∥u.
Proof. by rewrite -{1}[u]dotx1 cnvpar cnvdot cnvone A10 cnvI domtst'. Qed.

Lemma lifttstL' u v w : (1∥u)·v ∥ w ≡ (1∥u)·(v ∥ w).
Proof. by rewrite -[1∥u]domtst' A14. Qed.

Lemma lifttstR' u v w : v ∥ w·(1∥u) ≡ (v ∥ w)·(1∥u).
Proof. 
  rewrite -[X in X ≡ _]cnvI cnvpar cnvdot cnvtst' parC.
  by rewrite lifttstL' -{1}(cnvtst' u) -cnvpar -cnvdot cnvI parC.
Qed.

Lemma dotpartst' u v : (1∥u)·(1∥v) ≡ (1∥u)∥(1∥v).
Proof. by rewrite -lifttstL' dotx1 parA [_ ∥1]parC parA par11. Qed.

Lemma testP (a : test) : a ≡ 1∥a.
Proof. 
  case: a => a /=. elim: a => [u IHu v IHv|u IHu v IHv|u IHu|u IHu| |a] //=.
  - case/andP => /IHu U /IHv V. by rewrite U V dotpartst' !parA par11.
  - case/orP => [/IHu U | /IHv V]; first by rewrite parA -U. 
    by rewrite parA [1 ∥ _]parC -parA -V.
  - move/IHu => U. by rewrite -{1}cnvone -cnvpar -U.
  - by rewrite tstdom'.
  - by rewrite par11.
Qed.

Lemma lifttstR u v (a:test) : u ∥ v·a ≡ (u ∥ v)·a. 
Proof. by rewrite testP lifttstR'. Qed.

Lemma dotpartst (a b : test) : a·b ≡ a ∥ b.
Proof. by rewrite (testP a) (testP b) dotpartst'. Qed.

Lemma dotC (a b: test): a·b ≡ b·a.
Proof. by rewrite dotpartst parC -dotpartst. Qed.

Definition test_weq (a b: test) := a ≡ b.
Instance Equivalence_test_weq: Equivalence test_weq.
Proof. split. exact: weq_refl. exact: weq_sym. exact: weq_trans. Qed.

Canonical Structure test_setoid := Setoid Equivalence_test_weq.
Instance test_monoid: comm_monoid test_setoid :=
  { mon0 := [1];
    mon2 a b := [a·b] }.
  by intros ??????; apply dot_weq.
  by intros ???; apply dotA.
  apply dotC.   
  by intros ?; apply dotx1.
Defined.

(** * normalisation  *)

Inductive nf_term :=
| nf_test: test -> nf_term
| nf_conn: test -> term -> test -> nf_term.

Definition term_of_nf (t: nf_term): term :=
  match t with
  | nf_test alpha => alpha
  | nf_conn alpha u gamma => alpha · u · gamma
  end.                                         

Definition nf_one := nf_test [1].
Definition nf_var a := nf_conn [1] (var a) [1].
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
  | dot u v => nf_dot (nf u) (nf v)
  | par u v => nf_par (nf u) (nf v)
  | cnv u => nf_cnv (nf u) 
  | var a => nf_var a
  | dom u => nf_dom (nf u)
  | one => nf_one
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


(** * term labelled two-pointed graphs *)

Record lgraph :=
  LGraph { graph_of :> graph test_setoid term_setoid;
           input : vertex graph_of;
           output : vertex graph_of}.
Arguments input [_].
Arguments output [_].
Notation point G := (@LGraph G).

Bind Scope lgraph_scope with lgraph.
Delimit Scope lgraph_scope with L.

Definition label (G: lgraph) (x: vertex G + edge G): term :=
  match x with inl v => vlabel v | inr e => elabel e end.

Definition cnv' (b: bool) (u: term): term :=
  if b then u° else u.
Definition elabel' (G: lgraph) (b: bool) (e: edge G): term :=
  cnv' b (elabel e).
Definition source' (G: lgraph) (b: bool) (e: edge G): G :=
  if b then target e else source e.
Definition target' (G: lgraph) (b: bool) (e: edge G): G :=
  if b then source e else target e.

Definition mkLGraph (V : finType) (E : finType) (s t : E -> V) 
                    (lv : V -> test_setoid) (le : E -> term_setoid) (i o : V) := point (Graph s t lv le) i o.

Import CMorphisms.

Universe L.
Record liso (F G: lgraph): Type@{L} :=
  Liso {
      liso_v:> bij F G;
      liso_e: bij (edge F) (edge G);
      liso_dir: edge F -> bool;
      vlabel_liso: forall v, term_of (vlabel (liso_v v)) ≡ vlabel v;
      elabel_liso: forall e, elabel' (liso_dir e) (liso_e e) ≡ elabel e;
      source_liso: forall e, source' (liso_dir e) (liso_e e) = liso_v (source e);
      target_liso: forall e, target' (liso_dir e) (liso_e e) = liso_v (target e);
      liso_input: liso_v input = input;
      liso_output: liso_v output = output }.

Notation "h '.e'" := (liso_e h) (at level 2, left associativity, format "h '.e'"). 
Notation "h '.d'" := (liso_dir h) (at level 2, left associativity, format "h '.d'"). 

(* TOMOVE (first one) *)
Tactic Notation "iso" uconstr(h) uconstr(k) :=
  match goal with |- iso ?G ?H => apply (@Iso _ _ G H h k) end.
Tactic Notation "liso" uconstr(h) uconstr(k) uconstr(d) :=
  match goal with |- liso ?G ?H => apply (@Liso G H h k d) end.

Lemma src_tgt_liso (F G: lgraph) (h: liso F G) e:
 (  (source' (liso_dir h e) (liso_e h e) = liso_v h (source e))
  * (target' (liso_dir h e) (liso_e h e) = liso_v h (target e)))%type.
Proof. split; apply h. Qed.

Definition liso_id {G: lgraph}: liso G G.
  exists bij_id bij_id (fun _ => false)=>//.
Defined.
Definition liso_comp F G H (f: liso F G) (g: liso G H): liso F H.
  exists (bij_comp f g) (bij_comp (liso_e f) (liso_e g))
       (fun e => liso_dir f e != liso_dir g (liso_e f e))=>//=.
  move=>v. by rewrite->2vlabel_liso.
  move=>e. generalize (elabel_liso f e). generalize (elabel_liso g (liso_e f e)).
  by case liso_dir; case liso_dir=>/= E E'; rewrite<-E',<-E,?cnvI.
  move=>e. generalize (src_tgt_liso f e). generalize (src_tgt_liso g (liso_e f e)).
  by case liso_dir; case liso_dir=>/= E E'; rewrite -E' -E.
  move=>e. generalize (src_tgt_liso f e). generalize (src_tgt_liso g (liso_e f e)).
  by case liso_dir; case liso_dir=>/= E E'; rewrite -E' -E.
  by rewrite->2liso_input. 
  by rewrite->2liso_output.
Defined.
Definition liso_sym F G (f: liso F G): liso G F.
  exists (bij_sym f) (bij_sym (liso_e f))
       (fun e => liso_dir f ((liso_e f)^-1 e))=>//=.
  move=>v. rewrite<-(bijK' f v) at 2. by rewrite->vlabel_liso.
  move=>e. generalize (elabel_liso f ((liso_e f)^-1 e)) =>/=. rewrite bijK'.
  case liso_dir=>/=E. by rewrite <-E, cnvI. by symmetry. 
  move=>e. generalize (src_tgt_liso f ((liso_e f)^-1 e)) =>/=. rewrite bijK'. 
  case liso_dir=>/=E; by apply (@bij_injective _ _ f); rewrite bijK' -E.
  move=>e. generalize (src_tgt_liso f ((liso_e f)^-1 e)) =>/=. rewrite bijK'. 
  case liso_dir=>/=E; by apply (@bij_injective _ _ f); rewrite bijK' -E.
  rewrite<-(bijK f input). by rewrite->liso_input.
  rewrite<-(bijK f output). by rewrite->liso_output.
Defined.
Instance liso_Equivalence: CRelationClasses.Equivalence liso.
Proof. constructor. exact @liso_id. exact @liso_sym. exact @liso_comp. Defined.

Lemma iso_liso (G: lgraph) H (h: iso G H): liso G (point H (h input) (h output)).
Proof. exists (iso_v h) (iso_e h) (fun _ => false)=>//; apply h. Qed.


Definition swap Lv (G: graph Lv term_setoid) (f: edge G -> bool): graph Lv term_setoid :=
  Graph
    (fun e => if f e then target e else source e)
    (fun e => if f e then source e else target e)
    (@vlabel _ _ G)
    (fun e => if f e then (elabel e)° else elabel e).
Arguments swap [Lv] G f. 

Definition lswap (G: lgraph) f := point (swap G f) input output. 
Arguments lswap: clear implicits. 

Lemma swap_liso G f: liso G (lswap G f).
Proof.
  liso bij_id bij_id f=>//= e.
  rewrite /lswap/swap/elabel'/=. case (f e)=>//. apply cnvI. 
  rewrite /lswap/swap/source'/=. case (f e)=>//. 
  rewrite /lswap/swap/target'/=. case (f e)=>//.
Qed.


(** Basic Operations used to express the rewrite system *)

Definition add_vertex (G: lgraph) (a: test): lgraph :=
  point (add_vertex G a) (Some input) (Some output).
Arguments add_vertex : clear implicits.

Definition add_edge (G: lgraph) (x y: G) (u: term): lgraph :=
  point (add_edge G x y u) input output.
Arguments add_edge : clear implicits.

Definition add_test (G: lgraph) (x: G) (a: test): lgraph :=
  point (upd_vlabel G x (fun b => [a·b])) input output.
Arguments add_test : clear implicits.

(** Experimental notations *)
Definition weq_dir (b : bool) (u v : term) := cnv' b u ≡ v.
Notation "u ≡[ b ] v" := 
  (weq_dir b u v) (at level 31, format "u  ≡[ b ]  v").
Notation "G ∔ [ x , u , y ]" := 
  (add_edge G x y u) (at level 20,left associativity) : lgraph_scope.
Notation "G ∔ a" := 
  (add_vertex G a) (at level 20, left associativity) : lgraph_scope.
Notation "G [tst x <- a ]" := 
  (add_test G x a) (at level 20, left associativity, format "G [tst  x  <-  a ]") : lgraph_scope.







(** TOTHINK: How useful are these really? *)
Instance add_vertex_liso: Proper (liso ==> test_weq ==> liso) add_vertex.
Proof.
  move => G H [Iv Ie E Lv Le Is It Ii Io] a b /= weq_ab.
  liso (option_bij Iv) Ie E; try abstract (by rewrite //= ?Ii ?Io).
  - abstract (case => /= [x//|]; by symmetry).
  - abstract (move => e /=; rewrite -Is; by case: (E e)).
  - abstract (move => e /=; rewrite -It; by case: (E e)).
Defined.

Lemma add_vertex_lisoE (G H : lgraph) (l : liso G H ) a b (e : test_weq a b) :
  (add_vertex_liso l e =1 option_bij l) * ((add_vertex_liso l e).e =1 l.e).
Proof. rewrite /add_vertex_liso. by case: l. Qed.
Opaque add_vertex_liso.

(** Commutation Lemmas *)

Tactic Notation "liso_lift" uconstr(l) := 
  abstract (first [move => [?|]|move => ?|idtac]; try done ; apply l).

Lemma add_vertexC G a b: liso (add_vertex (add_vertex G b) a) (add_vertex (add_vertex G a) b).
Proof. 
  liso (option2x_bij bij_id) bij_id (fun _ => false); abstract (solve [by move => [[v|]|]| done]).
Defined.

Lemma add_edgeC G x y u i j v: 
  liso (add_edge (add_edge G x y u) i j v) (add_edge (add_edge G i j v) x y u).
Proof.
  liso bij_id (option2x_bij bij_id) (fun _ => false); abstract (solve [by move => [[e|]|]| done]).
Defined.

Lemma add_testC (G:lgraph) (x y :G) a b : 
  liso (add_test (add_test G x a) y b) (add_test (add_test G y b) x a).
Proof.
  liso bij_id bij_id (fun _ => false); try abstract done. 
  abstract (move => v /=; do 2 case: ifP => //=; by rewrite !dotA dotC).
Defined.

Lemma liso_add_test_edge G x y u z a : 
  liso (add_test (add_edge G x y u) z a) (add_edge (add_test G z a) x y u).
Proof.
  liso bij_id bij_id (fun _ => false); done.
Defined.

Lemma liso_add_test_vertex (G:lgraph) a b x : 
  liso (add_test (add_vertex G a) (Some x) b) (add_vertex (add_test G x b) a).
Proof.
  liso bij_id bij_id (fun _ => false); liso_lift void.
Defined.

(** Context Lemmas *)

Lemma liso_add_edge G G' (l : liso G G') x y u : 
  liso (add_edge G x y u) (add_edge G' (l x) (l y) u).
Proof.
  liso (liso_v l) (option_bij l.e) (fun e => if e is Some e' then liso_dir l e' else false).
  all: liso_lift l.
Defined.

Lemma liso_add_test G G' (l: liso G G') x a : 
  liso (add_test G x a) (add_test G' (l x) a).
Proof. 
  liso l l.e (liso_dir l); try liso_lift l.
  abstract (move => v /=; rewrite bij_eq //; case: ifP => /= _; by rewrite (vlabel_liso l)).
Defined.

