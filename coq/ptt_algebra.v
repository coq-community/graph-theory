Require Export Setoid Morphisms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Structure ptt_ops :=
  { car:> Type;
    weq: car -> car -> Prop;
    dot: car -> car -> car;
    par: car -> car -> car;
    cnv: car -> car;
    dom: car -> car;
    one: car;
    top: car }.
Arguments top [_].
Arguments weq {_} _ _.

Bind Scope ptt_ops with car.
Notation "x ∥ y" := (par x y) (left associativity, at level 40, format "x ∥ y"): ptt_ops.
Notation "x · y" := (dot x y) (left associativity, at level 25, format "x · y"): ptt_ops.
Notation "x °"  := (cnv x) (left associativity, at level 5, format "x °"): ptt_ops.
Notation "1"  := (one _): ptt_ops.
Infix "≡" := weq (at level 79).

Class ptt_laws (X: ptt_ops) :=
  { weq_Equivalence:> @Equivalence X weq;
    dot_weq:> Proper (weq ==> weq ==> weq) (@dot X);
    par_weq:> Proper (weq ==> weq ==> weq) (@par X);
    cnv_weq:> Proper (weq ==> weq) (@cnv X);
    domE: forall x: X, dom x ≡ 1 ∥ x·top;
    parA: forall x y z: X, x ∥ (y ∥ z) ≡ (x ∥ y) ∥ z;
    parC: forall x y: X, x ∥ y ≡ y ∥ x;
    dotA: forall x y z: X, x · (y · z) ≡ (x · y) · z;
    dotx1: forall x: X, x · 1 ≡ x;
    cnvI: forall x: X, x°° ≡ x;
    cnvpar: forall x y: X, (x ∥ y)° ≡ x° ∥ y°;
    cnvdot: forall x y: X, (x · y)° ≡ y° · x°;
    par11: 1 ∥ 1 ≡ @one X;
    A10: forall x y: X, 1 ∥ x·y ≡ dom (x ∥ y°);
    A11: forall x: X, x · top ≡ dom x · top;
    A12: forall x y: X, (x∥1) · y ≡ (x∥1)·top ∥ y }.

Section derived.
 Context {X} {L:ptt_laws X}.
  
 Global Instance dom_weq: Proper (weq ==> weq) (@dom X).
 Proof. intros ?? H. now rewrite 2domE, H. Qed.

 Lemma cnv1: 1° ≡ @one X.
 Proof.
  rewrite <-dotx1. rewrite <-(cnvI 1) at 2.
  now rewrite <-cnvdot, dotx1, cnvI.
 Qed.

 Lemma dot1x (x: X): 1·x ≡ x.
 Proof. now rewrite <-cnvI, cnvdot, cnv1, dotx1, cnvI. Qed.

 Lemma parxtop (x: X): x ∥ top ≡ x.
 Proof. generalize (A12 1 x). now rewrite par11, 2dot1x,parC. Qed.

 Lemma partopx (x: X): top ∥ x ≡ x.
 Proof. now rewrite parC, parxtop. Qed.

 Lemma cnvtop: top° ≡ @top X.
 Proof.
  rewrite <-parxtop. rewrite <-(cnvI top) at 2.
  now rewrite <-cnvpar, partopx, cnvI.
 Qed.
End derived.

Section terms.
 Variable A: Type.
 Inductive term :=
 | tm_dot: term -> term -> term
 | tm_par: term -> term -> term
 | tm_cnv: term -> term
 | tm_dom: term -> term
 | tm_one: term
 | tm_top: term
 | tm_var: A -> term.
 Section e.
 Variable (X: ptt_ops) (f: A -> X).
 Fixpoint eval (u: term): X :=
   match u with
   | tm_dot u v => eval u · eval v
   | tm_par u v => eval u ∥ eval v
   | tm_cnv u => (eval u) °
   | tm_dom u => dom (eval u)
   | tm_one => 1
   | tm_top => top
   | tm_var a => f a
   end.
 End e.
 Definition tm_weq: relation term :=
   fun u v => forall X (L: ptt_laws X) (f: A -> X), eval f u ≡ eval f v.
 Hint Unfold tm_weq.
 Canonical Structure tm_ops: ptt_ops :=
   {| weq := tm_weq;
      dot := tm_dot;
      par := tm_par;
      cnv := tm_cnv;
      dom := tm_dom;
      one := tm_one;
      top := tm_top |}.
 Global Instance tm_laws: ptt_laws tm_ops.
 Proof.
   constructor.
   - constructor.
     now intro.
     now intros ?? H ???; symmetry; apply H.
     now intros ? y ? H H' ???; transitivity (eval f y); [apply H | apply H'].
   - intros u u' U v v' V X L f; simpl. apply dot_weq. now apply U. now apply V.
   - intros u u' U v v' V X L f; simpl. apply par_weq. now apply U. now apply V.
   - intros u u' U X L f; simpl. apply cnv_weq. now apply U.
   - intros x X L f; simpl. apply domE. 
   - intros x y z X L f; simpl. apply parA. 
   - intros x y X L f; simpl. apply parC. 
   - intros x y z X L f; simpl. apply dotA. 
   - intros x X L f; simpl. apply dotx1. 
   - intros x X L f; simpl. apply cnvI. 
   - intros x y X L f; simpl. apply cnvpar. 
   - intros x y X L f; simpl. apply cnvdot. 
   - intros X L f; simpl. apply par11. 
   - intros x y X L f; simpl. apply A10. 
   - intros x X L f; simpl. apply A11. 
   - intros x y X L f; simpl. apply A12.
 Qed.
End terms.
Bind Scope ptt_ops with term.
