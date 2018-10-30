From mathcomp Require Import all_ssreflect.
Require Import preliminaries.

(** * Simple Experimental Tactic for finite sets *)

Lemma setIPn (T : finType) (A B : {set T}) (x:T) : 
  reflect (x \notin A \/ x \notin B) (x \notin A :&: B).
Proof. rewrite !inE negb_and. exact: orP. Qed.

Ltac notHyp b := match goal with [_ : is_true b |- _] => fail 1 | _ => idtac end.

(** NOTE: since Ltac is untyped, we need to provide the coercions
usually hidden, e.g., [is_true] or [SetDef.pred_of_set] *)

Local Notation pos := SetDef.pred_of_set.

Ltac set_tab_step := 
  match goal with 
  (* TODO: subsumption rules *)
  (* non-branching rules *)
  | [H : is_true (_ \in pos (_ :&: _)) |- _] => 
    case/setIP : H => [? ?]
  | [H : is_true (?x \in _ (?A :\: ?B)) |- _] => 
    case/setDP : H => [? ?]
  | [H : is_true (?x \in _ [set ?y]) |- _ ] => 
    move/set1P : H => ?;subst
  | [H : is_true (?x \in ?B), D : is_true [disjoint ?A & ?B] |- _] => 
    notHyp (x \notin A); have ? : x \notin A by rewrite (disjointFl D H)
  | [H : is_true (?x \in ?A), D : is_true [disjoint ?A & ?B] |- _] => 
    notHyp (x \notin B); have ? : x \notin B by rewrite (disjointFr D H)
  | [H : is_true (?x \in ?A), S : is_true (?A \subset ?B) |- _] => 
    notHyp (x \in B); move/(subsetP S) : (H) => ?
  (*branching rules *)
  | [H : is_true (?x \in pos (?A :|: ?B)) |- _] => 
    notHyp (x \in A); notHyp (x \in B); case/setUP : H => [?|?]
  | [ H : is_true (?x \notin pos (?A :&: ?B)) |- _] => 
    notHyp (x \notin A); notHyp (x \notin B); case/setIPn : H => [?|?]
  end.

(** Note that the rules on disjointness and subset do not restricted
to the type [{set _}] *)

Ltac set_init :=
  match goal with
  | [ |- forall _,_ ] => intro;set_init
  | [ |- _ -> _] => intro;set_init
  | [ |- is_true (~~ _) ] => apply/negP => ?
  | [ |- is_true _] => apply: contraTT isT => ?
  end.
                                          
Ltac set_tac := subst; set_init; repeat (first [contrab|set_tab_step]).

(** Use typeclass inference to trigger set_tac using rewrite lemmas *)

Class setBox (P : Prop) : Prop := SetBox { setBoxed : P }.
Hint Extern 0 (setBox _) => apply SetBox; set_tac : typeclass_instances.

Lemma inD (T : finType) (x : T) (A : {set T}) `{setBox (x \in A)} : x \in A. 
Proof. by case: H. Qed.

Lemma notinD (T : finType) (x : T) (A : {set T}) `{setBox (x \notin A)} : x \notin A. 
Proof. by case: H. Qed.

(* examples / unit tests *)

Goal forall (T:finType) (S V1 V2 : {set T}) x b, x \in S -> S = V1 :&: V2 -> b || (x \in V1).
Proof. move => *. by rewrite inD orbT. Qed.

Goal forall (T:finType) (A B : {set T}) x b, x \in B -> B \subset A -> (x \in A) || b.
Proof. move => T A B x b H D. by rewrite inD. Qed.

Goal forall (T:finType) (A B : {set T}) x b, x \in B -> [disjoint A & B] -> (x \notin A) || b.
Proof. move => T A B x b H D. by rewrite notinD. Qed.

Goal forall (T:finType) (A B : {set T}) x b, x \in A -> [disjoint A & B] -> b || (x \notin B).
Proof. move => T A B x b H D. by rewrite notinD orbT. Qed.

Goal forall (T:finType) (A B : {set T}) x b, x \notin A -> x \in A :|: B -> b || (x \in B).
Proof. move => *. by rewrite inD orbT. Qed.

(** NOTE: This does not require backward propagation of \subset since [x \in B] is assumed *)
Goal forall (T:finType) (A B : {set T}) x b, x \notin A -> B \subset A -> (x \notin B) || b.
Proof. move => T A B x b H D. by rewrite notinD. Qed.
