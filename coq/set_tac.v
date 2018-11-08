From mathcomp Require Import all_ssreflect.

Require Import preliminaries.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Simple Experimental Tactic for finite sets *)

Section SetTac.
Variables (T : finType) (A B C : {set T}).

Lemma set_tac_subUl: A :|: B \subset C -> A \subset C /\ B \subset C.
Proof. rewrite subUset. by case/andP. Qed.

Lemma set_tac_subIr: A \subset B :&: C -> A \subset B /\ A \subset C.
Proof. rewrite subsetI. by case/andP. Qed.

Lemma set_tac_subIl x : 
  x \in A -> x \in B -> A :&: B \subset C -> x \in C.
Proof. move => xA xB /subsetP. apply. by rewrite inE xA xB. Qed.

End SetTac.

Lemma setIPn (T : finType) (A B : {set T}) (x:T) : 
  reflect (x \notin A \/ x \notin B) (x \notin A :&: B).
Proof. rewrite !inE negb_and. exact: orP. Qed.

Ltac notHyp b := match goal with [_ : is_true b |- _] => fail 1 | _ => idtac end.

Ltac extend H T := notHyp H; have ? : H by T.

Ltac convertible A B := assert_succeeds (assert (A = B) by reflexivity).

(** NOTE: since Ltac is untyped, we need to provide the coercions
usually hidden, e.g., [is_true] or [SetDef.pred_of_set] *)

  (* lazymatch goal with *)
  (* | [H : is_true (?x \in ?A), S : is_true (?A' \subset ?B) |- _] =>  *)
  (*   convertible A A'; extend (x \in B) ltac:(apply: (subsetP S)) *)
  (* end. *)

Local Notation pos := SetDef.pred_of_set.

(* TODO: subsumption rules ??*)
(* non-branching rules *)
Ltac set_tab_close := 
  match goal with 
  | [H : is_true (?x \in pos (?A :&: ?B)) |- _] => 
    first [notHyp (x \in A)|notHyp(x \in B)]; case/setIP : (H) => [? ?]
  | [H : is_true (?x \in _ (?A :\: ?B)) |- _] => 
    first [notHyp (x \in A)|notHyp(x \notin B)]; case/setDP : (H) => [? ?]
  | [H : is_true (?x \in _ [set ?y]) |- _ ] => 
    assert_fails (have: x = y by []); (* [x = y] is nontrivial and unknown *)
    move/set1P : (H) => ?;subst
  | [H : is_true (?x \in ?B), D : is_true [disjoint ?A & ?B] |- _] => 
    notHyp (x \notin A); have ? : x \notin A by rewrite (disjointFl D H)
  | [H : is_true (?x \in ?A), D : is_true [disjoint ?A & ?B] |- _] => 
    notHyp (x \notin B); have ? : x \notin B by rewrite (disjointFr D H)
  | [H : is_true (?x \in ?A), S : is_true (?A' \subset ?B) |- _] => 
    convertible A A';
    extend (x \in B) ltac:(move/(subsetP S) : (H) => ?)
  | [ H : ?A = ?B :> {set _} |- _] => 
    move/eqP : H; rewrite eqEsubset => /andP [? ?]
  | [ H : is_true (_ (_ :|: _) \subset _) |- _] => 
    case/set_tac_subUl : H => [? ?]
  | [ H : is_true (_ \subset _ (_ :&: _)) |- _] => 
    case/set_tac_subIr : H => [? ?]
  | [ H : is_true (_ [set _] \subset _) |- _] => 
    rewrite sub1set in H 
  | [ xA : is_true (?x \in _ ?A), xB : is_true (?x \in _ ?B), 
    H : is_true (_ (?A :&: ?B) \subset ?D) |- _] =>
    notHyp (x \in D); have ? := set_tac_subIl xA xB H
  end.

(*branching rules *)
Ltac set_tab_branch :=
  match goal with 
  | [H : is_true (?x \in pos (?A :|: ?B)) |- _] => 
    notHyp (x \in A); notHyp (x \in B); case/setUP : (H) => [?|?]
  | [ H : is_true (?x \notin pos (?A :&: ?B)) |- _] => 
    notHyp (x \notin A); notHyp (x \notin B); case/setIPn : (H) => [?|?]
  end.

(** Note that the rules on disjointness and subset do not restricted
to the type [{set _}] *)

Ltac set_init :=
  match goal with
  | [ |- forall _,_ ] => intro;set_init
  | [ |- _ -> _] => intro;set_init
  | [ |- is_true (~~ _) ] => apply/negP => ?
  | [ |- is_true _] => apply: contraTT isT => ?
  | [ |- _ ] => idtac (* nothing to be done here *)
  end.

Ltac clean_mem := 
  repeat match goal with 
           [ H : _ |- _ ] => rewrite !mem_mem in H 
         end; rewrite !mem_mem.

Ltac set_tac_close_plus := fail.
Ltac set_tac_branch_plus := fail.

Ltac eqxx := match goal with
             | [ H : is_true (?x != ?x) |- _ ] => by rewrite eqxx in H
             end.

(** Use theory rules (_plus) before set rules *)
Ltac set_tac_step := first [eqxx
                           |contrab
                           |set_tac_close_plus
                           |set_tab_close
                           |set_tac_branch_plus
                           |set_tab_branch].
                                          
Ltac set_tac := set_init; subst; repeat set_tac_step.

(** Use typeclass inference to trigger set_tac using rewrite lemmas *)

Class setBox (P : Prop) : Prop := SetBox { setBoxed : P }.
Hint Extern 0 (setBox _) => apply SetBox; set_tac : typeclass_instances.

Lemma inD (T : finType) (x : T) (A : pred T) `{setBox (x \in A)} : x \in A. 
Proof. by case: H. Qed.

Lemma inD_debug (T : finType) (x : T) (A : pred T) : (x \in A) -> x \in A. 
Proof. by []. Qed.

Lemma notinD (T : finType) (x : T) (A : pred T) `{setBox (x \notin A)} : x \notin A. 
Proof. by case: H. Qed.

Lemma notinD_debug (T : finType) (x : T) (A : pred T) : (x \notin A) -> x \notin A. 
Proof. by []. Qed.


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


