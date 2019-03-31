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

Lemma setUPn (T : finType) (A B : {set T}) (x:T) : 
  reflect (x \notin A /\ x \notin B) (x \notin A :|: B).
Proof. rewrite !inE negb_or. exact: andP. Qed.

(* Ltac notHyp b := match goal with [_ : is_true b |- _] => fail 1 | _ => idtac end. *)
Ltac notHyp b := assert_fails (assert b by assumption).

Ltac extend H T := notHyp H; have ? : H by T.

Ltac convertible A B := assert_succeeds (assert (A = B) by reflexivity).

(** NOTE: since Ltac is untyped, we need to provide the coercions
usually hidden, e.g., [is_true] or [SetDef.pred_of_set]. *)

(** TOTHINK: For some collective predicates, in particular for paths,
the coercion to a predicates can take several different forms. This
means that rules involving [_ \subset _] should match up to conversion
to not miss instances. Similarly, we need to ensure that the 'notHyp'
test is performed on exactly the same term that ends up on the
branch. Otherwise the same hypotheses gets added ad infinitum *)

(** NOTE: The only rules that introduce hypotheses of the form
[_\subset _] are those eliminating equalities between sets. Since
these remove their hypotheses, the trivial subset assumption 
[[set _] \subset A] can be modified in place *)

Local Notation pos := SetDef.pred_of_set.

(** TODO:
- reverse propagation for subset 
- dealing with setT and set0
- dealing with existential hypotheses 
  + A != B (possibly do the A != set0 case separately)
  + ~~ (A \subset B) (this is never generated, do as init?)

*)

Ltac no_inhabitant A :=
  match goal with [ _ : ?x \in _ A |- _ ] => fail 1 | _ => idtac end.

(* non-branching rules *)
Ltac set_tab_close := 
  match goal with 
  | [H : is_true (?x == ?y) |- _ ] =>
    assert_fails (have: x = y by []); (* [x = y] is nontrivial and unknown *)
    move/eqP : (H) => ?; subst
  | [H : is_true (_ \in _ set0) |- _] => by rewrite in_set0 in H  

  | [H : is_true (?x \in pos (?A :&: ?B)) |- _] => 
    first [notHyp (x \in A)|notHyp(x \in B)]; case/setIP : (H) => [? ?]
  | [H : is_true (?x \in _ (?A :\: ?B)) |- _] => 
    first [notHyp (x \in A)|notHyp(x \notin B)]; case/setDP : (H) => [? ?]
  | [H : is_true (?x \notin _ (?A :|: ?B)) |- _] => 
    first [notHyp (x \notin A)|notHyp(x \notin B)]; case/setUPn : (H) => [? ?]

  | [H : is_true (?x \in _ [set _ in ?p]) |- _ ] => 
    extend (x \in p) ltac:(move: H; rewrite inE)
  | [H : is_true (?x \notin _ [set _ in ?p]) |- _ ] => 
    extend (x \notin p) ltac:(move: H; rewrite inE)

  | [H : is_true (?x \in _ [set ?y]) |- _ ] => 
    assert_fails (have: x = y by []); (* [x = y] is nontrivial and unknown *)
    move/set1P : (H) => ?;subst
  | [H : is_true (?x \notin _ [set ?y]) |- _ ] => 
    extend (x != y) ltac:(move: H ; rewrite inE)

    (* These rules will be tried (and fail) on equalities between non-sets, but
    set types can take many different shapes *)
  | [ H : ?A = ?B |- _] => 
    first [notHyp (A \subset B)|notHyp(B \subset A)];
    have/andP[? ?]: (A \subset B) && (B \subset A) by 
      (move/eqP : (H); rewrite eqEsubset; apply)
  | [ H : is_true (pos (?A :|: ?B) \subset ?C) |- _] => 
    first[notHyp (A \subset C)|notHyp (B \subset C)];
    case/set_tac_subUl : (H) => [? ?]
  | [ H : is_true (?A \subset pos (?B :&: ?C)) |- _] => 
    first[notHyp (A \subset B)|notHyp (A \subset C)];
    case/set_tac_subIr : (H) => [? ?]
  | [ H : is_true (pos [set ?x] \subset ?A) |- _] => 
    extend (x \in A) ltac:(move: (H); rewrite sub1set; apply)

  | [H : is_true (in_mem ?x (mem ?A)), S : is_true (subset (mem ?A') (mem ?B)) |- _] => 
    convertible (mem A) (mem A'); 
    extend (x \in B) ltac:(move/(subsetP S) : (H) => ?)

  | [H : is_true (?x \in ?B), D : is_true [disjoint ?A & ?B] |- _] => 
    notHyp (x \notin A); have ? : x \notin A by rewrite (disjointFl D H)
  | [H : is_true (?x \in ?A), D : is_true [disjoint ?A & ?B] |- _] => 
    notHyp (x \notin B); have ? : x \notin B by rewrite (disjointFr D H)

  | [ H : is_true (?A != set0) |- _] => 
    no_inhabitant A; case/set0Pn : H => [? ?]
                                         
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

(** Use theory rules (plus) before set rules *)
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

Goal forall (T:finType) (A B : {set T}) x,  x \in A -> A = B -> x \in B.
Proof. by set_tac. Qed.

Goal forall (T:finType) (A B : {set T}) x,  x \in A -> A == B -> x \in B.
Proof. by set_tac. Qed.