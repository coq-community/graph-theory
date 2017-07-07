From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** *** A fixpoint operator for bounded recursion *)

Section Bounded.
  Variables (aT rT : Type) (P : aT -> Prop) (x0 : rT).
  Variables (measure : aT -> nat) (F : (aT -> rT) -> (aT -> rT)).
  
  Hypothesis F_wf : 
    forall f g x, P x -> (forall y, P y -> measure y < measure x -> f y = g y) -> F f x = F g x.

  (** Note: The use of equality here effectively limits this to
  functions in one argument *)
  Fixpoint F_rec (n : nat) (x : aT) :=
    if n is n'.+1 then F (F_rec n') x else x0.

  Lemma F_rec_narrow m n x : 
    P x -> measure x < n -> n <= m -> F_rec m x = F_rec n x.
  Proof.
    elim: n m x => // => n IHn [//|m] x Px A B /=. 
    apply: F_wf => // y Py Hy. apply: IHn => //. exact: leq_trans Hy _. 
  Qed.

  Definition Fix x := F_rec (measure x).+1 x.
  
  Lemma Fix_eq x : P x -> Fix x = F Fix x.
  Proof. 
    rewrite /Fix /= => Px. apply: F_wf => // y Py Hy.
    by rewrite (@F_rec_narrow (measure x) (measure y).+1).
  Qed.

End Bounded.
Arguments Fix_eq [aT rT] P.

(** Example Instances *)

Definition const0_rec (F : nat -> nat) n := if n == 0 then 0 else F (n.-1).

Definition const0 := Fix 1 id const0_rec.

Lemma const0_eq n : const0 n = if n == 0 then 0 else const0 (n.-1).
Proof. 
  apply: (Fix_eq xpredT) => // {n} f g n _. 
  rewrite /const0_rec. case: ifP => // /negbT. 
  case: n => //= n _ Hfg. exact: Hfg.
Qed.

(** The following example shows that one can freely combine bounded
recursion with subroutines and big operators *)

Section Max.
Variable split : nat -> seq nat.
Hypothesis split_lt : forall n m, m \in split n -> m < n.
  
Definition foo_rec F n := 
  if n < 4 then n else \max_(m <- split n) F m.

Definition foo := Fix 0 id foo_rec.

Lemma foo_eq n : foo n = if n < 4 then n else \max_(m <- split n) foo m.
Proof.
  apply: (Fix_eq xpredT) => // {n} g f n _ H.
  rewrite /foo_rec. case: ifP => // _. 
  apply: eq_big_seq => m /split_lt. exact: H.
Qed.
End Max.