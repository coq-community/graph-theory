Require Import Setoid CMorphisms.
From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries bij equiv ptt_algebra multigraph ptt_graph.

(* attempts on expansion; to be revived and ported to new mgraphs... *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

Local Open Scope ptt_ops.



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
