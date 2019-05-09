Require Import Setoid CMorphisms Morphisms.
From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries equiv multigraph_new.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 


(** TOMOVE  *)

Lemma bij_inj A B (f: bij A B) a a': f a = f a' -> a = a'.
Proof. move =>E. by rewrite -(bijK f a) E bijK. Qed.

Lemma bij_inj' A B (f: bij A B) b b': f^-1 b = f^-1 b' -> b = b'.
Proof. move =>E. by rewrite -(bijK' f b) E bijK'. Qed.

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




(* Parameter graph_of_term_iso: forall u v, u ≡ v -> graph_of_term u ≈ graph_of_term v.  *)

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

Definition elabel' (G: lgraph) (b: bool) (e: edge G): term :=
  if b then (elabel e) ° else elabel e.
Definition source' (G: lgraph) (b: bool) (e: edge G): G :=
  if b then target e else source e.
Definition target' (G: lgraph) (b: bool) (e: edge G): G :=
  if b then source e else target e.

Import CMorphisms.

Record liso (F G: lgraph): Type :=
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

Lemma src_tgt_liso (F G: lgraph) (h: liso F G) e:
 (  (source' (liso_dir h e) (liso_e h e) = liso_v h (source e))
  * (target' (liso_dir h e) (liso_e h e) = liso_v h (target e)))%type.
Proof. split; apply h. Qed.

Definition liso_id {G: lgraph}: liso G G.
  apply Liso with bij_id bij_id (fun _ => false)=>//.
Defined.
Definition liso_comp F G H (f: liso F G) (g: liso G H): liso F H.
  apply Liso with (bij_comp f g) (bij_comp (liso_e f) (liso_e g)) (fun e => liso_dir f e != liso_dir g (liso_e f e))=>//=.
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
  apply Liso with (bij_sym f) (bij_sym (liso_e f)) (fun e => liso_dir f ((liso_e f)^-1 e))=>//=.
  move=>v. rewrite<-(bijK' f v) at 2. by rewrite->vlabel_liso.
  move=>e. generalize (elabel_liso f ((liso_e f)^-1 e)) =>/=. rewrite bijK'.
  case liso_dir=>/=E. by rewrite <-E, cnvI. by symmetry. 
  move=>e. generalize (src_tgt_liso f ((liso_e f)^-1 e)) =>/=. rewrite bijK'. 
  case liso_dir=>/=E; by apply (@bij_inj _ _ f); rewrite bijK' -E.
  move=>e. generalize (src_tgt_liso f ((liso_e f)^-1 e)) =>/=. rewrite bijK'. 
  case liso_dir=>/=E; by apply (@bij_inj _ _ f); rewrite bijK' -E.
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
  apply (@Liso G (lswap G f) bij_id bij_id f)=>//= e.
  rewrite /lswap/swap/elabel'/=. case (f e)=>//. apply cnvI. 
  rewrite /lswap/swap/source'/=. case (f e)=>//. 
  rewrite /lswap/swap/target'/=. case (f e)=>//.
Qed.

Definition add_vertex (G: lgraph) (a: test): lgraph :=
  point (add_vertex G a) (Some input) (Some output).

Definition add_edge (G: lgraph) (x y: G) (u: term): lgraph :=
  point (add_edge G x y u) input output.
Arguments add_edge: clear implicits. 

Definition add_test (G: lgraph) (x: G) (a: test): lgraph :=
  point (upd_vlabel G x (fun b => [a·b])) input output.
Arguments add_test: clear implicits. 

Definition optionf {A B} (f: A -> B): option A -> option B :=
  fun x => match x with Some a => Some (f a) | None => None end.
Definition option_bij A B (f: bij A B): bij (option A) (option B).
  exists (optionf f) (optionf f^-1); move=>[e|]=>//=; congr Some; apply f.
Defined.
Definition option2f {A B} (f: A -> B): option (option A) -> option (option B) :=
  fun x => match x with Some (Some a) => Some (Some (f a)) | Some None => None | None => Some None end.
Definition option2_bij A B (f: bij A B): bij (option (option A)) (option (option B)).
  exists (option2f f) (option2f f^-1); move=>[[e|]|]=>//=; do 2 congr Some; apply f.
Defined.
Lemma option_bij_case A B (f: bij (option A) (option B)):
  {f': bij A B | f =1 option_bij f'} +
  {A': Type & {B': Type & {a: bij A (option A') & {ab: bij A' B' & {b: bij (option B') B 
       | f=1 bij_comp (option_bij a) (bij_comp (option2_bij ab) (option_bij b))}}}}}.
Proof.
  case_eq (f None)=>[b|] E.
Admitted.

Inductive step: lgraph -> lgraph -> Type :=
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

Inductive steps: lgraph -> lgraph -> Type :=
  | liso_step: CRelationClasses.subrelation liso steps
  | one_step: CRelationClasses.subrelation step steps
  | steps_trans: CRelationClasses.Transitive steps.

Existing Instances liso_step one_step.
Instance PreOrder_steps: CRelationClasses.PreOrder steps.
Proof. split. intro. apply liso_step, liso_id. exact steps_trans. Qed.

Proposition local_confluence G G' H H':
    step G G' -> step H H' -> liso G H -> 
    {F & steps G' F * steps H' F}%type.
Proof.
  (* the key argument, not so easy with current definition of steps *)
  move:G H=>G0 H0. 
  case=>[G X u alpha|G x y u alpha v|G x u|G x y u v];
  case=>[H i w gamma|H i j w gamma t|H i w|H i j w t] h.
  - case (option_bij_case h).
    * move=>[h' E]. eexists. split. reflexivity. apply liso_step. admit.
    * intros (G''&H''&bg&bgh&bh&E). eexists. split.
Admitted.

Proposition confluence F G H:
  steps F G -> steps F H -> {F' & steps G F' * steps H F'}%type.
Admitted.  (* should follow abstractly from local confluence plus appropriate termination guarantee *)



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


Lemma dot_steps_l G G' H: steps G G' -> steps (ldot G H) (ldot G' H).
Proof.
  induction 1.
  - apply liso_step. admit.
  - apply one_step. admit.
  - etransitivity; eassumption. 
Admitted.

Lemma dot_steps_r G G' H: steps G G' -> steps (ldot H G) (ldot H G').
Proof.
  induction 1.
  - apply liso_step. admit.
  - apply one_step. admit.
  - etransitivity; eassumption. 
Admitted.

Instance dot_steps: Proper (steps ==> steps ==> steps) ldot.
Proof.
  repeat intro. by etransitivity; [apply dot_steps_l | apply dot_steps_r].
Qed.

Lemma lparC G H: liso (lpar G H) (lpar H G).
Admitted.

Lemma par_steps_l G G' H: steps G G' -> steps (lpar G H) (lpar G' H).
Proof.
  induction 1.
  - apply liso_step. admit.
  - apply one_step. admit.
  - etransitivity; eassumption. 
Admitted.

Lemma par_steps_r G G' H: steps G G' -> steps (lpar H G) (lpar H G').
Proof.
  intro.
  etransitivity. apply liso_step, lparC. 
  etransitivity. 2: apply liso_step, lparC.
  by apply par_steps_l. 
Qed.

Instance par_steps: Proper (steps ==> steps ==> steps) lpar.
Proof.
  repeat intro. by etransitivity; [apply par_steps_l | apply par_steps_r].
Qed.

Instance cnv_steps: Proper (steps ==> steps) lcnv.
Proof.
  induction 1.
  - apply liso_step.
    apply (@Liso (lcnv x) (lcnv y) (liso_v l) (liso_e l) (liso_dir l)); apply l. 
  - apply one_step.
    destruct s.
    * apply (@step_v1 (point G output input) x u alpha).
    * apply (@step_v2 (point G output input) x y u alpha v).
    * apply (@step_e0 (point G output input) x u).
    * apply (@step_e2 (point G output input) x y u v).
  - etransitivity; eassumption. 
Qed.

Instance dom_steps: Proper (steps ==> steps) ldom.
Proof.
  induction 1.
  - apply liso_step.
    apply (@Liso (ldom x) (ldom y) (liso_v l) (liso_e l) (liso_dir l)); apply l. 
  - apply one_step.
    destruct s.
    * apply (@step_v1 (point G input input) x u alpha).
    * apply (@step_v2 (point G input input) x y u alpha v).
    * apply (@step_e0 (point G input input) x u).
    * apply (@step_e2 (point G input input) x y u v).
  - etransitivity; eassumption. 
Qed.

(* TOMOVE *)
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

(* TOMOVE *)
Lemma iso_vbij Lv Le (G: graph Lv Le) (V: finType) (h: bij (vertex G) V):
  iso G (@Graph _ _ V (edge G)
                (h \o (@source _ _ G))
                (h \o (@target _ _ G))
                ((@vlabel _ _ G) \o h^-1)
                (@elabel _ _ G)).
Proof.
  apply (@Iso _ _ G (@Graph _ _ V (edge G) _ _ _ _) h bij_id).
  split=>//= v. by rewrite bijK. 
Defined.

Lemma iso_ebij Lv Le (G: graph Lv Le) (E: finType) (h: bij (edge G) E):
  iso G (@Graph _ _ (vertex G) E
                ((@source _ _ G) \o h^-1)
                ((@target _ _ G) \o h^-1)
                (@vlabel _ _ G)
                ((@elabel _ _ G) \o h^-1)).
Proof.
  apply (@Iso _ _ G (@Graph _ _ (vertex G) E _ _ _ _) bij_id h).
  by split=>//= v; rewrite bijK. 
Defined.

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

Proposition reduce (u: term): steps (lgraph_of_term u) (lgraph_of_nf_term (nf u)).
Proof.
  induction u=>//=.
  - etransitivity. apply dot_steps; [apply IHu1|apply IHu2].
    case (nf u1)=>[a|a u b];
    case (nf u2)=>[c|c v d]=>/=.
    admit.
    admit.
    admit.
    admit.
  - etransitivity. apply par_steps; [apply IHu1|apply IHu2].
    case (nf u1)=>[a|a u b];
    case (nf u2)=>[c|c v d]=>/=.
    admit.
    admit.
    admit.
    admit.
  - etransitivity. apply cnv_steps, IHu. 
    case (nf u)=>[a|a v b]=>//=.
    apply liso_step.
    rewrite /lcnv/=.
    apply (@Liso ((point (edge_graph a v b)) true false) ((point (edge_graph b v° a)) false true) bool_swap bij_id (fun _ => true))=>//=.
      by case.
      move=>_. apply cnvI.
  - etransitivity. apply dom_steps, IHu. 
    case (nf u)=>[a|a v b]=>//=.
    rewrite /ldom/=.
    etransitivity. apply liso_step.
    2: etransitivity. 2: apply one_step, (@step_v1 (point (unit_graph a) tt tt) tt v b).
    simpl.
    etransitivity. 
    apply (liso_vbij (G:=((point (edge_graph a v b)) _ _)) bool_option_unit)=>/=.
    etransitivity. 
    apply (liso_ebij (G:=((point (@Graph _ _ _ _ _ _ _ _)) _ _)) unit_option_void)=>/=.
    match goal with |- liso ?G ?H => 
                    apply (@Liso G H bij_id bij_id (fun _ => false))
    end=>//=; case=>//.
    apply liso_step.
    match goal with |- liso ?G ?H => 
                    apply (@Liso G H bij_id bij_id (fun _ => false))
    end=>//=; case=>//.
    apply dotC. 
Admitted.

Lemma nf_steps (s: nf_term) G: steps (lgraph_of_nf_term s) G -> liso (lgraph_of_nf_term s) G.
Admitted.                       (* boring but ok *)

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
  have H' : steps (lgraph_of_term u) (lgraph_of_nf_term (nf v)).
   etransitivity. apply liso_step, h. apply reduce. 
  case (confluence H H')=>F [/nf_steps HF /nf_steps HF'].
  rewrite-> (nf_correct u), (nf_correct v).
  apply liso_nf.
  etransitivity. apply HF. symmetry. apply HF'.
Qed.
