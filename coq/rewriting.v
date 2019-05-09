Require Import Setoid CMorphisms.
From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries equiv ptt_algebra multigraph ptt_graph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

Local Open Scope ptt_ops.

(** TOMOVE  *)

Lemma bij_inj A B (f: bij A B) a a': f a = f a' -> a = a'.
Proof. move =>E. by rewrite -(bijK f a) E bijK. Qed.

Lemma bij_inj' A B (f: bij A B) b b': f^-1 b = f^-1 b' -> b = b'.
Proof. move =>E. by rewrite -(bijK' f b) E bijK'. Qed.

(** * tests *)

Record test A := Test{ term_of:> term A ; testE: dom term_of ≡ term_of }.

Definition tst_1: test sym. Admitted.
Definition tst_dom: term sym -> test sym. Admitted.
Definition tst_conj: test sym -> test sym -> test sym. Admitted.
Definition tst_disc: test sym -> test sym. Admitted.
Definition tst_par1: term sym -> test sym. Admitted.

Parameter weq: forall {A}, term A -> term A -> Type.
Infix "≡" := weq.
Instance Equivalence_weq A: Equivalence (@weq A).
Admitted.
Instance dot_weq A: Proper (weq ==> weq ==> weq) (@tm_dot A). Admitted.
Instance par_weq A: Proper (weq ==> weq ==> weq) (@tm_par A). Admitted.
Instance cnv_weq A: Proper (weq ==> weq) (@tm_cnv A). Admitted.
Lemma cnvI A (x: term A): tm_cnv (tm_cnv x) ≡ x. Admitted.
Parameter graph_of_term_iso: forall u v, u ≡ v -> graph_of_term u ≈ graph_of_term v. 

(** * term labelled two-pointed graphs *)

Record lgraph :=
  LGraph { vertex :> finType;
           edge : finType;
           source: edge -> vertex;
           target: edge -> vertex;
           label_v: vertex -> test sym;
           label_e: edge -> term sym; (* might want to impose that these are non-tests *)
           input : vertex;
           output : vertex }.
Arguments input [_].
Arguments output [_].

Definition label (G: lgraph) (x: vertex G + edge G): term sym :=
  match x with inl v => label_v v | inr e => label_e e end.

Definition glabel (G: lgraph) (x: vertex G + edge G): graph2 :=
  graph_of_term (label x).

Definition label_e' (G: lgraph) (b: bool) (e: edge G): term sym :=
  if b then (label_e e) ° else label_e e.
Definition source' (G: lgraph) (b: bool) (e: edge G): G :=
  if b then target e else source e.
Definition target' (G: lgraph) (b: bool) (e: edge G): G :=
  if b then source e else target e.

Record liso (F G: lgraph) :=
  Liso {
      liso_v:> bij F G;
      liso_e: bij (edge F) (edge G);
      liso_dir: edge F -> bool;
      label_liso_v: forall v, term_of (label_v (liso_v v)) ≡ label_v v;
      label_liso_e: forall e, label_e' (liso_dir e) (liso_e e) ≡ label_e e;
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
  move=>v. by rewrite->2label_liso_v.
  move=>e. generalize (label_liso_e f e). generalize (label_liso_e g (liso_e f e)).
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
  move=>v. rewrite<-(bijK' f v) at 2. by rewrite->label_liso_v.
  move=>e. generalize (label_liso_e f ((liso_e f)^-1 e)) =>/=. rewrite bijK'.
  case liso_dir=>/=E. by rewrite <-E, cnvI. by symmetry. 
  move=>e. generalize (src_tgt_liso f ((liso_e f)^-1 e)) =>/=. rewrite bijK'. 
  case liso_dir=>/=E; by apply (@bij_inj _ _ f); rewrite bijK' -E.
  move=>e. generalize (src_tgt_liso f ((liso_e f)^-1 e)) =>/=. rewrite bijK'. 
  case liso_dir=>/=E; by apply (@bij_inj _ _ f); rewrite bijK' -E.
  rewrite<-(bijK f input). by rewrite->liso_input.
  rewrite<-(bijK f output). by rewrite->liso_output.
Defined.
Instance liso_Equivalence: Equivalence liso.
Proof. constructor. exact @liso_id. exact @liso_sym. exact @liso_comp. Defined.

Definition add_vertex (G: lgraph) (alpha: test sym): lgraph :=
  @LGraph [finType of option G] (edge G)
          (fun e => Some (source e))
          (fun e => Some (target e))
          (fun v => match v with Some v => label_v v | None => alpha end)
          (@label_e G)
          (Some input)
          (Some output).
          
Definition add_edge (G: lgraph) (x y: G) (u: term sym): lgraph :=
  @LGraph (vertex G) [finType of option (edge G)]
          (fun e => match e with Some e => source e | None => x end)
          (fun e => match e with Some e => target e | None => y end)
          (@label_v G)
          (fun e => match e with Some e => label_e e | None => u end)
          input
          output.
Arguments add_edge: clear implicits. 

Definition add_test (G: lgraph) (x: G) (u: test sym): lgraph :=
  @LGraph (vertex G) (edge G)
          (@source G)
          (@target G)
          (fun v => if v==x then tst_conj (label_v v) u else label_v v)
          (@label_e G)
          input
          output.
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
  | step_v0: forall G alpha,
      step
        (add_vertex G alpha)
        (add_test G input (tst_disc alpha))
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
        (add_test G x (tst_par1 u))
  | step_e2: forall G x y u v,
      step
        (add_edge (add_edge G x y u) x y v)
        (add_edge G x y (u∥v)).

Inductive steps: lgraph -> lgraph -> Type :=
  | steps0: forall G H, liso G H -> steps G H
  | steps1: forall G H, step G H -> steps G H
  | stepscat: forall F G H, steps F G -> steps G H -> steps F H.

Proposition local_confluence G G' H H':
    step G G' -> step H H' -> liso G H -> 
    {F & steps G' F * steps H' F}%type.
Proof.
  (* the key argument, not so easy with current definition of steps *)
  move:G H=>G0 H0. 
  case=>[G alpha|G X u alpha|G x y u alpha v|G x u|G x y u v];
  case=>[H gamma|H i w gamma|H i j w gamma t|H i w|H i j w t] h.
  - case (option_bij_case h).
    * move=>[h' E]. eexists. split. apply steps0, liso_id. admit.
    * intros (G''&H''&bg&bgh&bh&E). eexists. split.
      eapply stepscat. apply steps0. 2: apply steps1, step_v0.
Admitted.

Proposition confluence F G H:
  steps F G -> steps F H -> {F' & steps G F' * steps H F'}%type.
Admitted.  (* should follow abstractly from local confluence plus appropriate termination guarantee *)

Definition lgraph_of_graph2 (G: graph2): lgraph :=
  LGraph (@multigraph.source G)
         (@multigraph.target G)
         (fun _ => tst_1)
         (fun e => tm_var (multigraph.label e))
         g_in
         g_out.

Lemma lgraph_of_graph2_iso (G H: graph2):
  G ≈ H -> liso (lgraph_of_graph2 G) (lgraph_of_graph2 H).
Proof.
  move=>h. exists (iso2_v h) h.e (fun _ => false)=>//; try intro; try apply h.
    by rewrite /=(label_iso h).
Qed.

Inductive nf_term :=
| nf_test: test sym -> nf_term
| nf_ntst: test sym -> term sym -> test sym -> nf_term.

Definition nf: term sym -> nf_term.
Admitted.                       (* ok *)

Definition term_of_nf (t: nf_term): term sym :=
  match t with
  | nf_test alpha => alpha
  | nf_ntst alpha u gamma => term_of alpha·u·gamma
  end.                                         

Proposition nf_correct (u: term sym): u ≡ term_of_nf (nf u).
Proof.
  induction u.
Admitted.                       (* ok (algebraic) *)

Definition lgraph_of_nf_term (t: nf_term): lgraph :=
  match t with
  | nf_test alpha =>
    LGraph vfun vfun (fun _ => alpha) vfun tt tt
  | nf_ntst alpha u gamma =>
    LGraph
      (fun _ => false) (fun _ => true)
      (fun b => if b then gamma else alpha)
      (fun _: unit => u) false true
  end. 

Proposition reduce (u: term sym):
  steps (lgraph_of_graph2 (graph_of_term u)) (lgraph_of_nf_term (nf u)).
Proof.
  (* maybe easier with a direct def of lgraph_of_term ? 
     certainly requires some care *)
  induction u.
Admitted.

Lemma nf_steps (s: nf_term) G: steps (lgraph_of_nf_term s) G -> liso (lgraph_of_nf_term s) G.
Admitted.                       (* boring but ok *)

Lemma liso_nf (s t: nf_term):
  liso (lgraph_of_nf_term s) (lgraph_of_nf_term t) ->
  term_of_nf s ≡ term_of_nf t.
Admitted.                       (* easy *)

Theorem completeness (u v: term sym): graph_of_term u ≈ graph_of_term v -> u ≡ v.
Proof.
  move=>h.
  apply lgraph_of_graph2_iso in h.
  pose proof (reduce u) as H.
  have H' : steps (lgraph_of_graph2 (graph_of_term u)) (lgraph_of_nf_term (nf v)).
   eapply stepscat. apply steps0, h. apply reduce.
  case (confluence H H')=>F [/nf_steps HF /nf_steps HF'].
  rewrite-> (nf_correct u), (nf_correct v).
  apply liso_nf.
  etransitivity. apply HF. symmetry. apply HF'.
Qed.









(***** bijections on sigma types *****)


Definition sigTmap X V Y W (f: X -> Y) (g: forall x, V x -> W (f x)) (x: sigT V): sigT W :=
  let (a,b) := x in existT _ (f a) (g a b).

Lemma UIP_eqType (T: eqType) (x y: T) (e f: x = y): e = f.
Admitted.

Definition sigT_bij (X: eqType) V (Y: eqType) W
           (f: bij X Y)
           (g: forall x, bij (V x) (W (f x))):
  bij (sigT V) (sigT W).
  exists (sigTmap (f:=f) g)
         (sigTmap (f:=f^-1) (fun x (w: W x) => (g (f^-1 x))^-1 (eq_rect x W w (f (f^-1 x)) (esym (bijK' f x))))).
  - move=>[x v]; apply eq_existT_uncurried; exists (bijK f x).
    have H: forall y (e: y=x), eq_rect y V ((g y)^-1 (eq_rect (f x) W ((g x) v) (f y) (esym (f_equal f e)))) x e = v.
    move=>y e. destruct e. simpl. apply bijK.
    replace (bijK' f (f x)) with (f_equal f (bijK f x)) by apply UIP_eqType. apply H.
  - move=>[y w]; apply eq_existT_uncurried; exists (bijK' f y).
    generalize (bijK' f y). set y':=(f (f^-1 y)). destruct e. simpl. apply bijK'.  
Defined.

Lemma sigT_bijE (X: eqType) V (Y: eqType) W
      (f: bij X Y)
      (g: forall x, bij (V x) (W (f x))) x v:
  sigT_bij g (existT _ x v) = existT _ (f x) (g x v).
Proof. by []. Qed.

Lemma sigT_bijE' (X: eqType) V (Y: eqType) W
      (f: bij X Y)
      (g: forall x, bij (V x) (W (f x))) x w:
  (sigT_bij g)^-1 (existT _ (f x) w) = existT _  x ((g x)^-1 w).
Admitted.

Opaque sigT_bij.       




(***** expansion of a term-labeled multigraph *****)
(* NOTE: expansion is not needed for completeness! *)


Definition expand_typ (G: lgraph) := { x: vertex G + edge G & glabel x }.
Definition expand_typ' (G: lgraph) := { x: vertex G + edge G & multigraph.edge (glabel x) }.
Definition expand_fun (G: lgraph): expand_typ G -> expand_typ G :=
  fun x =>
      match x with
      | existT (inl _) _ => x
      | existT (inr e) v =>
        if v==g_in then existT _ (inl (source e)) g_in
        else if v==g_out then existT _ (inl (target e)) g_in
        else x
      end.
Definition expand_rel (G: lgraph): rel (expand_typ G) :=
  fun x y => expand_fun x == expand_fun y.
Arguments expand_rel: clear implicits.
Lemma expand_class_of (G: lgraph): equiv_class_of (expand_rel G).
  (* note: for this to be an equivalence relation, 
     one must impose term labeling edges to be non-tests (which is certainly easier than using an equivalence closure) *)
Admitted.
Canonical expand_equivalence (G: lgraph) := EquivRelPack (expand_class_of G).

Definition expand_ (G: lgraph): graph :=
  @Graph (quot (expand_equivalence G))
         [finType of expand_typ' G]
         (fun x => \pi let (x,e) := x in existT _ x (multigraph.source e))
         (fun x => \pi let (x,e) := x in existT _ x (multigraph.target e))
         (fun x => let (x,e) := x in multigraph.label e).
Definition expand (G: lgraph): graph2 :=
  point (expand_ G) (\pi (existT _ (inl input) g_in)) (\pi (existT _ (inl output) g_in)).


Lemma graph_liso_v (F G: lgraph) (h: liso F G) (x: F):
  graph_of_term (label_v x) ≈ graph_of_term (label_v (h x)).
Proof. apply iso2_sym, graph_of_term_iso, label_liso_v. Defined.

Lemma graph_liso_e (F G: lgraph) (h: liso F G) (e: edge F):
  iso (graph_of_term (label_e e)) (graph_of_term (label_e (liso_e h e))).
Proof.
  generalize (iso_sym (graph_of_term_iso (label_liso_e h e))).
  case liso_dir =>//. 
Defined.

Definition liso' (F G: lgraph) (h: liso F G):
  bij (vertex F + edge F) (vertex G + edge G) :=
  sum_bij (liso_v h) (liso_e h).

Lemma glabel_liso (F G: lgraph) (h: liso F G) x: iso (glabel x) (glabel (liso' h x)).
Proof. case: x=>v. apply iso2_iso, graph_liso_v. apply graph_liso_e. Defined.

Definition expand_liso_e (F G: lgraph) (h: liso F G):
  bij (multigraph.edge (expand_ F)) (multigraph.edge (expand_ G)).
  apply (sigT_bij (f:=liso' h)). apply glabel_liso. 
Defined.

Definition expand_liso_v (F G: lgraph) (h: liso F G):
  bij (expand_ F) (expand_ G).
  eapply bij_comp. 2: apply quot_same. unshelve apply finite_quotient.quot_bij.
  apply (sigT_bij (f:=liso' h))=>x. apply glabel_liso.
  move=>[[x|e] v] [[y|f] w]=>/=; rewrite /expand_rel/=.
Admitted.

Proposition expand_liso_ (F G: lgraph) (h: liso F G): iso (expand_ F) (expand_ G).
Proof.
  apply Iso with (expand_liso_v h) (expand_liso_e h).
  split. 
Admitted.

Proposition expand_liso (F G: lgraph) (h: liso F G): expand F ≈ expand G.
Proof.
  apply Iso2' with (expand_liso_ h). 
Admitted.

Proposition expand_step G G': step G G' -> expand G ≈ expand G'.
Proof.
  move:G=>G0. 
  case=>[G alpha|G X u alpha|G x y u alpha v|G x u|G x y u v].
  - admit.
  -
Admitted.                          

Theorem expand_steps G G': steps G G' -> expand G ≈ expand G'.
Proof.
  elim=>[H H' h|H H' s|H H' H'' _ IH _ IH'].
    by apply expand_liso.
    by apply expand_step.
    by transitivity (expand H').
Qed.
