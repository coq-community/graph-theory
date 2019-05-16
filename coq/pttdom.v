Require Import Setoid CMorphisms Morphisms.
From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries equiv multigraph_new.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 


(* 
   strategy:

   1. 2pdom + TaT=T    (with rule G+· --> G)
   2. 2pdom by conservativity
   3. 2p by normalisation and reduction to 2pdom (for nfs u v, G(u)≃G(v) -> G(u[t/T])≃G(v[t/T]))

   alternative is:
   1. 2p
   2. 2pdom by conservativity
   3. 2pdom + TaT by simple analysis
   (boring thing here is that we need 'graphs with a term' for the rewriting system)

 *)


(** TOMOVE  *)

Notation "'Σ' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p%type)) ..))
  (at level 200, x binder, y binder, right associativity).

Lemma bij_bijective A B (f : bij A B) : bijective f.
Proof. case: f => f g can_f can_g. by exists g. Qed.

Lemma bij_bijective' A B (f : bij A B) : bijective f^-1.
Proof. case: f => f g can_f can_g. by exists f. Qed.

Hint Resolve bij_bijective bij_bijective'.

Lemma bij_injective A B (f: bij A B) : injective f.
Proof. exact: bij_inj. Qed.

Lemma bij_injective' A B (f: bij A B) : injective f^-1.
Proof. exact: bij_inj. Qed.

Hint Resolve bij_injective bij_injective'.

Lemma orb_sum (a b : bool) : a || b -> (a + b)%type.
Proof. by case: a => /=; [left|right]. Qed.

Lemma inj_card_leq (A B: finType) (f : A -> B) : injective f -> #|A| <= #|B|.
Proof. move => inj_f. by rewrite -[#|A|](card_codom (f := f)) // max_card. Qed.

Lemma bij_card_eq (A B: finType) (f : A -> B) : bijective f -> #|A| = #|B|.
Proof. 
  case => g can_f can_g. apply/eqP. 
  rewrite eqn_leq (inj_card_leq (f := f)) ?(inj_card_leq (f := g)) //; exact: can_inj.
Qed.

Lemma card_bij (A B: finType) (f : bij A B) : #|A| = #|B|.
Proof. exact: (bij_card_eq (f := f)). Qed.
Arguments card_bij [A B] f.

Definition bool_swap: bij bool bool.
  exists negb negb; by case.
Defined.

Definition bool_option_unit: bij bool (option unit).
  exists (fun b => if b then None else  Some tt)
         (fun o => if o is None then true else false); case=>//; by case.
Defined.

Definition unit_option_void: bij unit (option void).
  exists (fun _ => None)
         (fun _ => tt); by case.
Defined.

Definition option_bij (A B : Type) (f : bij A B) : bij (option A) (option B).
exists (option_map f) (option_map f^-1); abstract (case => //= x; by rewrite ?bijK ?bijK'). 
Defined.

Definition option2x {A B} (f: A -> B): option (option A) -> option (option B) :=
  fun x => match x with Some (Some a) => Some (Some (f a)) | Some None => None | None => Some None end.
Definition option2x_bij A B (f: bij A B): bij (option (option A)) (option (option B)).
  exists (option2x f) (option2x f^-1); move=>[[e|]|]=>//=; do 2 congr Some; apply f.
Defined.

Lemma option_bij_case A B (f: bij (option A) (option B)):
  (Σ f' : bij A B, f =1 option_bij f') +
  (Σ (A' B' : Type) (a : bij A (option A')) (ab : bij A' B') (b : bij (option B') B),
   f =1 bij_comp (option_bij a) (bij_comp (option2x_bij ab) (option_bij b))).
Proof. 
  case_eq (f None)=>[b|] E.
Admitted.


Definition S_option A: bij (unit+A) (option A).
Proof.
  exists (fun x => match x with inr a => Some a | inl _ => None end)
         (fun x => match x with Some a => inr a | None => inl tt end);
    case=>//; case=>//.
Defined.

Definition two_bool: bij (unit+unit) bool.
Proof. etransitivity. apply S_option. symmetry. apply bool_option_unit. Defined.

Definition two_option_option_void: bij (unit+unit) (option (option void)).
Proof.
  etransitivity. apply bij_sumC.
  etransitivity. apply S_option.
  apply option_bij. apply unit_option_void.
Defined.

Definition merge43: bij (quot (eqv_clot [::(inl true,inr false)])) (option bool).
Admitted.
Lemma merge43E:
  ((merge43 (\pi inl false) = Some false) *
   (merge43 (\pi inl true) = None) *
   (merge43 (\pi inr false) = None) *
   (merge43 (\pi inr true) = Some true))%type.
Admitted.
Lemma merge43E':
  ((merge43^-1 (Some false) = \pi inl false) *
   (merge43^-1 None = \pi inl true) *
   (merge43^-1 (Some true) = \pi inr true))%type.
Admitted.


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
Notation "x ∥ y" := (par x y) (left associativity, at level 40, format "x ∥ y"): pttdom_ops.
Notation "x · y" := (dot x y) (left associativity, at level 25, format "x · y"): pttdom_ops.
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

Lemma dotC (a b: test): a·b ≡ b·a.
Admitted.

Definition test_weq (a b: test) := a ≡ b.
Instance Equivalence_test_weq: Equivalence test_weq.
Admitted.
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

Definition add_vertex (G: lgraph) (a: test): lgraph :=
  point (add_vertex G a) (Some input) (Some output).

Instance add_vertex_liso: Proper (liso ==> test_weq ==> liso) add_vertex.
Proof.
  move => G H [Iv Ie E Lv Le Is It Ii Io] a b /= weq_ab.
  liso (option_bij Iv) Ie E; try abstract (by rewrite //= ?Ii ?Io).
  - abstract (case => /= [x//|]; by symmetry).
  - abstract (move => e /=; rewrite -Is; by case: (E e)).
  - abstract (move => e /=; rewrite -It; by case: (E e)).
Qed.

Lemma add_vertexC G a b: liso (add_vertex (add_vertex G b) a) (add_vertex (add_vertex G a) b).
Proof. 
  liso (option2x_bij bij_id) bij_id (fun _ => false); solve [by move => [[v|]|]| done].
Qed.

Definition add_edge (G: lgraph) (x y: G) (u: term): lgraph :=
  point (add_edge G x y u) input output.
Arguments add_edge: clear implicits. 

(* TOTHINK: Maybe this should be a definition *)
Lemma liso_add_edge_plus G G' (l : liso G G') x y u : 
  Σ (g : liso (add_edge G x y u) (add_edge G' (l x) (l y) u)), (g =1 l) * (g.e =1 option_bij l.e).
Admitted.

Lemma liso_add_edge G G' (l : liso G G') x y u : 
  liso (add_edge G x y u) (add_edge G' (l x) (l y) u).
Proof.
  liso (liso_v l) (option_bij l.e) (fun e => if e is Some e' then liso_dir l e' else false).
  all: try done.
Admitted.
(* Should compute *)
Lemma liso_add_edgeE G G' (l : liso G G') x y u :
  (liso_add_edge l x y u =1 l) * ((liso_add_edge l x y u).e =1 option_bij l.e).
Admitted.


Lemma add_edge_liso G G' (I: liso G G') x x' (X: I x = x') y y' (Y: I y = y') u u' (U: u ≡ u'):
  liso (add_edge G x y u) (add_edge G' x' y' u').
Admitted.

Lemma add_edgeC G x y u i j v: liso (add_edge (add_edge G x y u) i j v) (add_edge (add_edge G i j v) x y u).
Admitted.

Definition add_test (G: lgraph) (x: G) (a: test): lgraph :=
  point (upd_vlabel G x (fun b => [a·b])) input output.
Arguments add_test: clear implicits. 

Lemma add_testC (G:lgraph) (x y :G) a b : 
  liso (add_test (add_test G x a) y b) (add_test (add_test G y b) x a).
Admitted.

(* TOTHINK: are the equalities useful, the rest of the statment doesn't depend on g *)
Lemma liso_add_test_plus G G' (l: liso G G') x a : 
  Σ (g : liso (add_test G x a) (add_test G' (l x) a)), (l =1 g) * (l.e =1 g.e).
Admitted.

Lemma liso_add_test G G' (l: liso G G') x a : 
  liso (add_test G x a) (add_test G' (l x) a).
Proof. exact: (projT1 (liso_add_test_plus _ _ _)). Qed.

Lemma add_test_liso G G' (I: liso G G') x x' (X: I x = x') (a a': test) (A: a ≡ a'):
  liso (add_test G x a) (add_test G' x' a').
Proof.
  apply: liso_comp (liso_add_test I x a ) _. rewrite X.
  (* congruence lemma? *)
Admitted.

Lemma add_vertex_vertex G a H b
  (l: liso (add_vertex G a) (add_vertex H b)):
  (liso G H) * (a ≡ b) * (l None = None)
   + (Σ F, liso G (add_vertex F b) * liso H (add_vertex F a) * (l None <> None)).
Admitted.

Lemma add_vertex_vertex' G a H b (l: liso (add_vertex G a) (add_vertex H b)):
 (Σ (l' : liso G H) (e : a ≡ b), l = add_vertex_liso l' e) +
 (Σ (F : lgraph) (l' : liso G (add_vertex F b)) (l'' : liso (add_vertex F a) H),
  l = liso_comp (add_vertex_liso l' (weq_refl a))
                (liso_comp (add_vertexC F a b) (add_vertex_liso l'' (weq_refl b)))).
Admitted.

Definition mkLGraph (V : finType) (E : finType) (s t : E -> V) 
                    (lv : V -> test_setoid) (le : E -> term_setoid) (i o : V) := point (Graph s t lv le) i o.

Definition del_edge (G : lgraph) (e0 : edge G) := Eval hnf in 
  @mkLGraph G [finType of { e : edge G | e != e0}] 
            (fun e => source (val e)) (fun e => target (val e)) (@vlabel _ _ G) (fun e => elabel (val e)) input output.
Arguments del_edge : clear implicits.

Definition strip (A B : Type) (x0 : B) (f : A -> option B) x := 
  if f x is Some z then z else x0.
(* Lemma stripE (A B : Type) (f : A -> option B) (x0 : B) (forall x, f x) x :  *)
(*   strip f x  *)

(* (* Deleting an edge and adding it back *) *)
(* Lemma liso_del_add_edge (G : lgraph) (e : edge G) :  *)
(*   liso (add_edge (del_edge G e) (source e) (target e) (elabel e)) G. *)
(* Admitted. *)

Lemma liso_add_test_edge G x y u z a : 
  liso (add_test (add_edge G x y u) z a) (add_edge (add_test G z a) x y u).
Admitted.

Lemma liso_add_test_vertex (G:lgraph) a b x : 
  liso (add_test (add_vertex G a) (Some x) b) (add_vertex (add_test G x b) a).
Admitted.
(* should compute *)
Lemma liso_add_test_vertexE (G:lgraph) a b (x:G) z: 
  (liso_add_test_vertex a b x) z = z.
Admitted.

Lemma add_vertex_edge G a H x y u (l: liso (add_vertex G a) (add_edge H x y u)):
  Σ (F : lgraph) (x' y' : F) (h : liso H (add_vertex F a)),
  (liso G (add_edge F x' y' u) * (h x = Some x') * (h y = Some y')).
Proof.
  move/liso_sym in l.
  (* pose e0 := liso_e l None. *)
  (* pose F := del_edge G e0.  *)
  (* have [x' Ex'] : { x' | l x = Some x'}. admit. *)
  (* have [y' Ey'] : { y' | l y = Some y'}. admit. *)
  (* exists F. exists x'. exists y'. rewrite /F. rewrite -> liso_del_add_edge. *)
  (* What's a good choice of F here? 
     G without the edge added in H or the vertices of G and the edges of H? *)

  pose s := strip input (fun e : edge H => l (@source' (add_edge H x y u) (liso_dir l (Some e)) (Some e))). 
  pose t := strip input (fun e : edge H => l (@target' (add_edge H x y u) (liso_dir l (Some e)) (Some e))). 
  pose F := @mkLGraph G (edge H) s t (@vlabel _ _ G) (@elabel _ _ H) input output.
  exists F. 
  have @h : liso H (add_vertex F a).
  { rewrite /F. 
Admitted.

Lemma add_vertex_edge' G w H x y u (l: liso (add_vertex G w) (add_edge H x y u)):
  Σ (F : lgraph) (x' y' : F) (h : liso H (add_vertex F w)) (g : liso G (add_edge F x' y' u)),
  (forall x, l (Some x) = h^-1 (Some (g x))) * 
  (l None = h^-1 None) *
  (h x = Some x') * (h y = Some y').
Admitted.



(* TODO: there is a third case with [u ≡ u'°] *)
Lemma add_edge_edge G H x y a b u w (i : liso (add_edge G x y u) (add_edge H a b w)) :
  (Σ (h : liso G H), (u ≡ w) * (i =1 h) * (i.e =1 option_bij h.e))
+ (Σ F a' b' x' y' (g : liso G (add_edge F a' b' w)) (h : liso H (add_edge F x' y' u)), 
   (g x = x') * (g y = y') * (h a = a') * (h b = b')). (* what else? *)
Admitted.
  
Universe S.
Inductive step: lgraph -> lgraph -> Type@{S} :=
  | step_v0: forall G alpha,
      step
        (add_vertex G alpha)
        G
  | step_v1: forall G x u alpha,
      step
        (add_edge (add_vertex G alpha) (Some x) None u)
        (add_test G x (tst_dom (u·alpha)))
  | step_v2: forall G x y u alpha v,
      step
        (add_edge (add_edge (add_vertex G alpha) (Some x) None u) None (Some y) v)
        (add_edge G x y (u·alpha·v))
  | step_e0: forall G x u,
      step
        (add_edge G x x u)
        (add_test G x [1∥u])
  | step_e2: forall G x y u v,
      step
        (add_edge (add_edge G x y u) x y v)
        (add_edge G x y (u∥v)).

(** It is crucial that we name the universe steps resides in. Without
the explicit name, the inferred universe is a max-universe, causing
setoid rewite underneath of steps to fail with the anomaly: "Unable to
handle arbitrary u+k <= v constraints." *)
Inductive steps: lgraph -> lgraph -> Type@{S} :=
  | liso_step: CRelationClasses.subrelation liso steps
  | cons_step: forall F G H H', liso F G -> step G H -> steps H H' -> steps F H'.
Existing Instance liso_step.

Instance PreOrder_steps: CRelationClasses.PreOrder steps.
Proof.
  split. intro. apply liso_step, liso_id.
  intros F G H S S'. induction S as [F G I|F G G' G'' I S _ IH].
  - destruct S' as [F' G' I'|F' G' G'' G''' I' S'].
    apply liso_step. etransitivity; eassumption.
    apply cons_step with G' G''=>//. etransitivity; eassumption.
  - apply cons_step with G G'=>//. by apply IH. 
Qed.

Instance one_step: CRelationClasses.subrelation step steps.
Proof. intros F G S. by apply cons_step with F G. Qed.

Definition step_order G H (s: step G H): nat :=
  match s with
  | step_v0 _ _ => 0
  | step_v1 _ _ _ _ => 1
  | step_v2 _ _ _ _ _ _ => 2
  | step_e0 _ _ _ => 3
  | step_e2 _ _ _ _ _ => 4
  end.

(* Lemmas for manual chaining *)
Lemma steps_lisoL G G' H : steps G' H -> liso G G' -> steps G H.
Admitted.

Lemma steps_stepL G G' H : steps G' H -> step G G' -> steps G H.
Admitted.

Lemma steps_comp F G H : steps F G -> steps G H -> steps F H.
Admitted.

(* TOMOVE *)
Lemma iso_vbij Lv Le (G: graph Lv Le) (V: finType) (h: bij (vertex G) V):
  iso G (@Graph _ _ V (edge G)
                (h \o (@source _ _ G))
                (h \o (@target _ _ G))
                ((@vlabel _ _ G) \o h^-1)
                (@elabel _ _ G)).
Proof. iso h bij_id. by split=>//= v; rewrite bijK. Defined.

Lemma iso_ebij Lv Le (G: graph Lv Le) (E: finType) (h: bij (edge G) E):
  iso G (@Graph _ _ (vertex G) E
                ((@source _ _ G) \o h^-1)
                ((@target _ _ G) \o h^-1)
                (@vlabel _ _ G)
                ((@elabel _ _ G) \o h^-1)).
Proof. iso bij_id h. by split=>//= v; rewrite bijK. Defined.

Lemma liso_vbij (G: lgraph) (V: finType) (h: bij (vertex G) V):
  liso G
       (point (@Graph _ _ V (edge G)
                      (h \o (@source _ _ G))
                      (h \o (@target _ _ G))
                      ((@vlabel _ _ G) \o h^-1)
                      (@elabel _ _ G))
              (h input) (h output)).
Proof. apply (iso_liso (iso_vbij h)). Qed.

Lemma liso_ebij (G: lgraph) (E: finType) (h: bij (edge G) E):
  liso G
       (point (@Graph _ _ (vertex G) E
                ((@source _ _ G) \o h^-1)
                ((@target _ _ G) \o h^-1)
                (@vlabel _ _ G)
                ((@elabel _ _ G) \o h^-1))
              input output).
Proof. apply (iso_liso (iso_ebij h)). Qed.

Tactic Notation "liso_step" uconstr(h) :=
  match goal with
  | |- steps ?G _ => etransitivity;
                     [apply liso_step;
                      first [apply h|apply (@liso_vbij G _ h)|apply (@liso_ebij G _ h)]|]
  | |- liso ?G _ => etransitivity;
                    [first [apply h|apply (@liso_vbij G _ h)|apply (@liso_ebij G _ h)]|]
  end.

Instance steps_proper : Proper (liso ==> liso ==> iffT) steps.
Proof.
  move => G G' g H H' h. split => S. 
  - apply: steps_lisoL (liso_sym g). apply: steps_comp S _. exact: liso_step.
  - apply: steps_lisoL g. apply: steps_comp S _. apply: liso_step. exact: liso_sym.
Qed. 



Proposition local_confluence G G' H H':
    step G G' -> step H H' -> liso G H -> 
    {F & steps G' F * steps H' F}%type.
Proof.
  intros S S'. wlog: G G' H H' S S' / step_order S <= step_order S'.
  { move => L I. case/orb_sum: (leq_total (step_order S) (step_order S')) => SS. 
    - exact: L SS I. 
    - case: (L _ _ _ _ S' S SS (liso_sym I)) => F [F1 F2]. exists F. by split. }
  move:G H S S'=>G0 H0. 
  case=>[G alpha|G x u alpha|G x y u alpha v|G x u|G x y u v];
  case=>[H gamma|H i w gamma|H i j w gamma t|H i w|H i j w t]//_ h.
  - destruct (add_vertex_vertex h) as [[[GH E] _]|[F [[HF GF] _]]].
    exists G. split=>//. apply liso_step. by symmetry.
    exists F. split.
     liso_step HF. apply one_step, step_v0.
     liso_step GF. apply one_step, step_v0.
  - apply add_vertex_edge in h as [F[x[y[HF[[GF X] Y]]]]].
    destruct (add_vertex_vertex HF) as [[[HF' E] HFN]|[F' [[HF' FF'] _]]]. congruence.
    (* exists (add_test F' (HF' i) [dom(w·gamma)]).  *)
    admit.
  - admit.
  - admit.
  - admit.
  - (* pendant rule + pendant rule *)
    case (option_bij_case h).
    * (* exact same instance *)
      move=>[h' E]. eexists. split. reflexivity. apply liso_step.
      case (option_bij_case (liso_e h))=>[[he' E']|].
      symmetry. unshelve eapply add_test_liso.
      liso h' he' (fun e => liso_dir h (Some e)); intros.
        by rewrite -(vlabel_liso h (Some v)) (E (Some v)).
        generalize (elabel_liso h (Some e)). by rewrite (E' (Some e)).
        generalize (source_liso h (Some e)). rewrite (E' (Some e)) (E (Some (source e)))=>/=.
        unfold source'. simpl. by case liso_dir; injection 1. 
        generalize (target_liso h (Some e)). rewrite (E' (Some e)) (E (Some (target e)))=>/=.
        unfold source'. simpl. by case liso_dir; injection 1.
        generalize (liso_input h)=>/=. rewrite E/=. congruence.
        generalize (liso_output h)=>/=. rewrite E/=. congruence.
        simpl. generalize (source_liso h None). simpl. unfold source'. simpl.
        case liso_dir; rewrite E' E/=; congruence.
        apply dom_weq, dot_weq.
        generalize (elabel_liso h None). generalize (source_liso h None).
        case liso_dir; rewrite E' E //=. by symmetry. 
        generalize (vlabel_liso h None). rewrite E. by symmetry.
      move=>[A'[B'[a[ab[b U]]]]]. exfalso.
      generalize (target_liso h None). rewrite E U/=. by case liso_dir.
    * (* distinct target vertices being "pulled in" *)
      intros (G''&H''&bg&bgh&bh&E). eexists. split. admit. admit.
      (* what about the completely independent case? *)
  - (* pendant rule + chain rule *)
    admit.
  - (* pendant rule + loop rule *)
    case: (add_edge_edge h) => [[g] [[A B] C]|].
    + (* contradiction: identical edges *) exfalso. 
      move: (source_liso h None) (target_liso h None). rewrite !B !C /=. 
      case: (liso_dir _ _) => /= ->; by move/(@bij_injective _ _ g).
    + (* distinct edges *)
      move => [F] [a'] [b'] [x'] [y'] [f] [g] [[[A B] C] D].
      move: (add_vertex_edge' f) => [F'] [a''] [b''] [f'] [g'] [[[H1 H2] H3] H4].
      have E: a'' = b'' by congruence. subst b''.
      exists (add_test (add_test F' (g' x) (tst_dom (u·alpha))) a'' [1∥w]). split.
      * subst. 
        rewrite -> (liso_add_test g' x (tst_dom (u·alpha))).
        rewrite -> (liso_add_test_edge _ _).
        exact: steps_stepL (step_e0 _ _). 
      * rewrite -> (liso_add_test g).  
        rewrite -> (liso_add_test (liso_add_edge f' x' y' u)). rewrite !liso_add_edgeE.
        rewrite -> liso_add_test_edge. subst. rewrite C H3 [(f (Some x))]H1 H2 !bijK'. 
        rewrite -> (liso_add_edge (@liso_add_test_vertex F' alpha [1∥w] (a''))). 
        rewrite !liso_add_test_vertexE. 
        apply: steps_stepL (step_v1 _ _ _). by  rewrite -> add_testC. 
Admitted.

Definition measure (G: lgraph) := #|vertex G| + #|edge G|.

Lemma step_decreases G H: step G H -> measure H < measure G.
Proof.
  rewrite /measure.
  case; intros=>/=; by rewrite !card_option ?addSnnS ?addnS.
Qed.

Lemma liso_stagnates G H: liso G H -> measure H = measure G.
Proof. move=>l. by rewrite /measure (card_bij (liso_v l)) (card_bij (liso_e l)). Qed.

Proposition confluence F: forall G H, steps F G -> steps F H -> {F' & steps G F' * steps H F'}%type.
Proof.
  induction F as [F_ IH] using (well_founded_induction_type (Wf_nat.well_founded_ltof _ measure)).
  move=> G H S.
  move: G H S IH=> _ H [F G FG|F__ F0 G' G FF0 FG GG] IH FH.
  - exists H; split=>//. transitivity F=>//. by apply liso_step, liso_sym.
  - move: H FH IH FF0=> _ [F H FH|F F1 H' H FF1 FH HH] IH FF0.
    exists G; split=>//. transitivity F. by apply liso_step, liso_sym. eauto using cons_step.
    destruct (local_confluence FG FH) as [M[GM HM]]. transitivity F=>//. by symmetry.
    destruct (fun D => IH G' D _ _ GG GM) as [L[GL ML]].
     rewrite /Wf_nat.ltof -(liso_stagnates FF0). apply /ltP. by apply step_decreases.
    have HL: steps H' L by transitivity M. 
    destruct (fun D => IH H' D _ _ HL HH) as [R[LR HR]].
     rewrite /Wf_nat.ltof -(liso_stagnates FF1). apply /ltP. by apply step_decreases.
     exists R. split=>//. by transitivity L.
Qed.


(** ** 2pdom-operations on graphs *)

Notation merge_seq G l := (@merge _ _ test_monoid G (eqv_clot l)).

Definition lpar (F G: lgraph) :=
  point (merge_seq (union F G) [::(unl input,unr input); (unl output,unr output)])
        (\pi (unl input)) (\pi (unl output)).

Definition ldot (F G: lgraph) :=
  point (merge_seq (union F G) [::(unl output,unr input)])
        (\pi (unl input)) (\pi (unr output)).

Definition lcnv (F: lgraph) :=
  point F output input.

Definition ldom (F: lgraph) :=
  point F input input.

Definition lone :=
  point (unit_graph [1]) tt tt.

Definition ltop :=
  point (two_graph [1] [1]) false true.

Definition lvar a :=
  point (edge_graph [1] (var a) [1]) false true.

Fixpoint lgraph_of_term (u: term): lgraph :=
  match u with
  | dot u v => ldot (lgraph_of_term u) (lgraph_of_term v)
  | par u v => lpar (lgraph_of_term u) (lgraph_of_term v)
  | cnv u => lcnv (lgraph_of_term u)
  | dom u => ldom (lgraph_of_term u)
  | one => lone
  | var a => lvar a
  end.

Definition lgraph_of_nf_term (t: nf_term): lgraph :=
  match t with
  | nf_test a => point (unit_graph a) tt tt
  | nf_conn a u b => point (edge_graph a u b) false true
  end.

(*
Definition lgraph_of_graph2 (G: graph2): lgraph :=
  LGraph (@multigraph.source G)
         (@multigraph.target G)
         (fun _ => [1])
         (fun e => var (multigraph.label e))
         input
         output.

Lemma lgraph_of_graph2_of_term (u: term): liso (lgraph_of_term u) (lgraph_of_graph2 (graph2_of_term u)).
Admitted. 

Lemma lgraph_of_graph2_iso (G H: graph2):
  G ≈ H -> liso (lgraph_of_graph2 G) (lgraph_of_graph2 H).
Proof.
  move=>h. exists (iso2_v h) h.e (fun _ => false)=>//; try intro; try apply h.
    by rewrite /=(label_iso h).
Qed.
*)


Lemma dot_liso: Proper (liso ==> liso ==> liso) ldot.
Admitted.

Lemma par_liso: Proper (liso ==> liso ==> liso) lpar.
Admitted.

Lemma cnv_liso: Proper (liso ==> liso) lcnv.
Proof. intros F G l. liso (liso_v l) (liso_e l) (liso_dir l); apply l. Qed.

Lemma dom_liso: Proper (liso ==> liso) ldom.
Proof. intros F G l. liso (liso_v l) (liso_e l) (liso_dir l); apply l. Qed.

Lemma step_to_steps f:
  Proper (liso ==> liso) f -> Proper (step ==> steps) f -> Proper (steps ==> steps) f.
Proof.
  intros If Sf G G' S.
  induction S as [G G' I|G G' F H' I S Ss IH].
  - by apply liso_step, If.
  - etransitivity. apply liso_step, If, I.
    etransitivity. apply Sf, S. apply IH. 
Qed.

Lemma dot_steps_l G G' H: steps G G' -> steps (ldot G H) (ldot G' H).
Proof.
  apply (step_to_steps (f:=fun G => ldot G H)).
  apply: (fun _ _ I => dot_liso I liso_id). 
Admitted.
  

Lemma dot_steps_r G G' H: steps G G' -> steps (ldot H G) (ldot H G').
Proof.
  apply step_to_steps. by apply dot_liso.
Admitted.

Instance dot_steps: Proper (steps ==> steps ==> steps) ldot.
Proof.
  repeat intro. by etransitivity; [apply dot_steps_l | apply dot_steps_r].
Qed.

Lemma lparC G H: liso (lpar G H) (lpar H G).
Admitted.

Lemma par_steps_r G G' H: steps G G' -> steps (lpar H G) (lpar H G').
Proof.
  apply step_to_steps. by apply par_liso.
Admitted.

Lemma par_steps_l G G' H: steps G G' -> steps (lpar G H) (lpar G' H).
Proof.
  intro.
  etransitivity. apply liso_step, lparC. 
  etransitivity. 2: apply liso_step, lparC.
  by apply par_steps_r. 
Qed.

Instance par_steps: Proper (steps ==> steps ==> steps) lpar.
Proof.
  repeat intro. by etransitivity; [apply par_steps_l | apply par_steps_r].
Qed.

Instance cnv_steps: Proper (steps ==> steps) lcnv.
Proof.
  apply step_to_steps. by apply cnv_liso.
  move=>F G S. eapply one_step. destruct S.
  * apply (@step_v0 (point G output input) alpha).
  * apply (@step_v1 (point G output input) x u alpha).
  * apply (@step_v2 (point G output input) x y u alpha v).
  * apply (@step_e0 (point G output input) x u).
  * apply (@step_e2 (point G output input) x y u v).
Qed.

Instance dom_steps: Proper (steps ==> steps) ldom.
Proof.
  apply step_to_steps. by apply dom_liso.
  move=>F G S. eapply one_step. destruct S.
  * apply (@step_v0 (point G input input) alpha).
  * apply (@step_v1 (point G input input) x u alpha).
  * apply (@step_v2 (point G input input) x y u alpha v).
  * apply (@step_e0 (point G input input) x u).
  * apply (@step_e2 (point G input input) x y u v).
Qed.

Proposition reduce (u: term): steps (lgraph_of_term u) (lgraph_of_nf_term (nf u)).
Proof.
  induction u=>//=.
  - etransitivity. apply dot_steps; [apply IHu1|apply IHu2].
    case (nf u1)=>[a|a u b];
    case (nf u2)=>[c|c v d]=>/=.
    * apply liso_step.
      rewrite /ldot/=.
      admit.
    * apply liso_step.
      admit. 
    * apply liso_step.
      admit.
    * rewrite /ldot/=.
      etransitivity. apply liso_step.
      2: etransitivity.
      2: apply one_step, (step_v2 (G:=point (two_graph a d) false true) false true u [b·c] v).
      2: apply liso_step.
      2: liso_step (bij_sym unit_option_void)=>/=.
      2: liso bij_id bij_id (fun _ => false)=>//= _; by rewrite !dotA.
      liso_step merge43=>/=. 
      liso_step two_option_option_void=>/=.
      liso bij_id bij_id (fun _ => false)=>//=;
           (repeat case)=>//=;
           rewrite ?merge43E ?merge43E' //=.
      admit.
      admit.
      admit.
      
  - etransitivity. apply par_steps; [apply IHu1|apply IHu2].
    case (nf u1)=>[a|a u b];
    case (nf u2)=>[c|c v d]=>/=.
    * apply liso_step.
      admit.
    * apply liso_step.
      admit. 
    * apply liso_step.
      admit.
    * rewrite /lpar/=.
      etransitivity. apply liso_step.
      2: etransitivity.
      2: apply one_step, (step_e2 (G:=point (two_graph [a·c] [b·d]) false true) false true u v).
      admit.
      apply liso_step.
      liso_step (bij_sym unit_option_void)=>/=. 
      liso bij_id bij_id (fun _ => false)=>//.
      
  - etransitivity. apply cnv_steps, IHu. 
    case (nf u)=>[a|a v b]=>//=.
    apply liso_step.
    rewrite /lcnv/=. liso bool_swap bij_id (fun _ => true)=>//=.
      by case.
      move=>_. apply cnvI.
      
  - etransitivity. apply dom_steps, IHu. 
    case (nf u)=>[a|a v b]=>//=.
    rewrite /ldom/=.
    etransitivity. apply liso_step.
    2: etransitivity. 2: apply one_step, (@step_v1 (point (unit_graph a) tt tt) tt v b).
    simpl.
    liso_step bool_option_unit=>/=. 
    liso_step unit_option_void=>/=.
    liso bij_id bij_id (fun _ => false)=>//=; case=>//.
    apply liso_step.
    liso bij_id bij_id (fun _ => false)=>//=; case=>//.
    apply dotC. 
Admitted.

Lemma nf_steps s: forall H, steps (lgraph_of_nf_term s) H -> liso (lgraph_of_nf_term s) H.
Proof.
  suff E: forall G H, steps G H -> liso G (lgraph_of_nf_term s) -> liso G H
    by intros; apply E. 
  destruct 1 as [G H I|G' G H H' I S _ _]=>//L.
  - exfalso. apply (liso_comp (liso_sym I)) in L. clear -S L. generalize (card_bij (liso_e L)).
    destruct s; destruct S; simpl in *; try by rewrite !card_option ?card_unit ?card_void.
    * admit.                    (* because input must be there in G *)
    * move=>_.
      generalize (liso_input L). generalize (liso_output L). simpl.
      suff E: input=output :>G by congruence.
      apply (card_le1 (D:=predT))=>//. 
      apply liso_v, card_bij in L. rewrite card_option card_bool in L.
        by injection L=>->.
    * admit.
    * move=>_.
      generalize (source_liso L None). generalize (target_liso L None).
      case liso_dir; simpl; congruence.
Admitted.

Lemma liso_nf (s t: nf_term):
  liso (lgraph_of_nf_term s) (lgraph_of_nf_term t) ->
  term_of_nf s ≡ term_of_nf t.
Proof.
  case s=>[a|a u b];
  case t=>[c|c v d]=>/= h.
  - rewrite -(vlabel_liso h tt). by case (h tt). 
  - exfalso.
    generalize (bijK' h false). generalize (bijK' h true).
    case (h^-1 true). case (h^-1 false). congruence. 
  - exfalso.
    generalize (bijK h false). generalize (bijK h true).
    case (h true). case (h false). congruence.
  - rewrite -(vlabel_liso h false).
    rewrite -(vlabel_liso h true).
    rewrite liso_input liso_output /=. 
    generalize (elabel_liso h tt).
    generalize (source_liso h tt).
    case (liso_dir h tt)=>/=. by rewrite liso_input.
    by move=>_ ->. 
Qed.

Theorem completeness (u v: term): liso (lgraph_of_term u) (lgraph_of_term v) -> u ≡ v.
Proof.
  move=>h.
  pose proof (reduce u) as H.
  have H' : steps (lgraph_of_term u) (lgraph_of_nf_term (nf v))
    by liso_step h; apply reduce. 
  case (confluence H H')=>F [/nf_steps HF /nf_steps HF'].
  rewrite-> (nf_correct u), (nf_correct v).
  apply liso_nf. liso_step HF. by symmetry. 
Qed.
