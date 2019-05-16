Require Import Setoid CMorphisms.
Require Relation_Definitions.
From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Bijections between Types  *)

Record bij (A B: Type): Type := Bij
  { bij_fwd:> A -> B;
    bij_bwd: B -> A;
    bijK: cancel bij_fwd bij_bwd;
    bijK': cancel bij_bwd bij_fwd }.
Notation "h '^-1'" := (bij_bwd h). 

(** Facts about Bijections *)

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

Lemma card_bij (A B: finType) (f : bij A B) : #|A| = #|B|.
Proof. exact: (bij_card_eq (f := f)). Qed.
Arguments card_bij [A B] f.

(** Specific Bijections *)

Definition bij_id {A}: bij A A := @Bij A A id id (@erefl A) (@erefl A).

Definition bij_sym {A B}: bij A B -> bij B A.
Proof. move=>f. econstructor; apply f. Defined.

Definition bij_comp {A B C}: bij A B -> bij B C -> bij A C.
Proof.
  move=> f g.
  econstructor; apply can_comp. apply g. apply f. apply f. apply g. 
Defined.

Instance bij_Equivalence: Equivalence bij.
constructor. exact @bij_id. exact @bij_sym. exact @bij_comp. Defined.

Definition sumf {A B C D} (f: A -> B) (g: C -> D) (x: A+C): B+D :=
  match x with inl a => inl (f a) | inr c => inr (g c) end. 

Instance sum_bij: Proper (bij ==> bij ==> bij) sum.
  intros A A' f B B' g.
  exists (sumf f g) (sumf f^-1 g^-1); abstract (by move=>[a|b] /=; rewrite ?bijK ?bijK').
Defined.

Definition sumC {A B} (x: A + B): B + A := match x with inl x => inr x | inr x => inl x end.
Lemma bij_sumC {A B}: bij (A+B) (B+A).
  exists sumC sumC; abstract (by move=>[|]). 
Defined.

Definition sumA {A B C} (x: A + (B + C)): (A + B) + C :=
  match x with inl x => inl (inl x) | inr (inl x) => inl (inr x) | inr (inr x) => inr x end.
Definition sumA' {A B C} (x: (A + B) + C): A + (B + C) :=
  match x with inr x => inr (inr x) | inl (inr x) => inr (inl x) | inl (inl x) => inl x end.
Lemma bij_sumA {A B C}: bij (A+(B+C)) ((A+B)+C).
  exists sumA sumA'.
  abstract (by move=>[|[|]]). 
  abstract (by move=>[[|]|]). 
Defined.


Definition bool_swap: bij bool bool.
  exists negb negb; by case.
Defined.

Definition bool_option_unit: bij bool (option unit).
  exists (fun b => if b then None else  Some tt)
    (fun o => if o is None then true else false); case=>//; by case.
Defined.

Definition unit_option_void: bij unit (option void).
  exists (fun _ => None) (fun _ => tt); by case.
Defined.

Definition option_bij (A B : Type) (f : bij A B) : bij (option A) (option B).
exists (option_map f) (option_map f^-1); abstract (case => //= x; by rewrite ?bijK ?bijK'). 
Defined.



(** Useful to obtain bijections with good simplification properties *)
Lemma bij_same A B (f : A -> B) (f_inv : B -> A) (i : bij A B) :
  f =1 i -> f_inv =1 i^-1 -> bij A B.
Proof.
  move => Hf Hf'.
  exists f f_inv; abstract (move => x; by rewrite Hf Hf' ?bijK ?bijK').
Defined.
Arguments bij_same [A B] f f_inv i _ _.
