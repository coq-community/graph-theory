From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.

(** * Preliminaries *)

(** *** Tactics *)

Ltac reflect_eq := 
  repeat match goal with [H : is_true (_ == _) |- _] => move/eqP : H => H end.
Ltac contrab := 
  match goal with 
    [H1 : is_true ?b, H2 : is_true (~~ ?b) |- _] => by rewrite H1 in H2
  end.

(** *** Generic Trivialities *)

Lemma max_mono (I :Type) (r : seq I) P (F G : I -> nat) :
  (forall x, F x <= G x) -> \max_(i <- r | P i) F i <= \max_(i <- r | P i) G i.
Proof.
  move => ?. elim/big_ind2 : _ => // y1 y2 x1 x2 A B.
  by rewrite geq_max !leq_max A B orbT.
Qed.

Lemma leq_subn n m o : n <= m -> n - o <= m.
Proof. move => A. rewrite -[m]subn0. exact: leq_sub. Qed.

Lemma cards3 (T : finType) (a b c : T) : #|[set a;b;c]| <= 3.
Proof. 
  rewrite !cardsU !cards1 !addn1. 
  apply: leq_subn. rewrite ltnS. exact: leq_subn.
Qed.

Lemma card_gt2 (T : finType) (S : pred T) : 
  2 <= #|S| -> exists v v0, [/\ v \in S, v0 \in S & v != v0].
Proof.
  move => A. case/card_gt0P : (ltnW A) => v inS. 
  rewrite (cardD1 v) inS /= ltnS in A. case/card_gt0P : A => v'. 
  rewrite !inE => /andP [? ?]. by exists v'; exists v.
Qed.

Lemma card12 (T : finType) (A : {set T}) :
  0 < #|A| -> #|A| <= 2 -> 
                  (exists x, A = [set x]) \/ exists x y, x != y /\ A = [set x;y].
Proof.
  case/card_gt0P => x xA. rewrite (cardsD1 x) xA add1n ltnS. 
  case (boolP (0 < #|A :\ x|)). 
  - case/card_gt0P => y yA. rewrite (cardsD1 y) yA add1n ltnS leqn0 cards_eq0.
    move => H. right. exists x. exists y. split. 
    + move: yA. rewrite !inE eq_sym. by case/andP.
    + apply/setP => z. by rewrite !inE -(setD1K xA) -(setD1K yA) (eqP H) !inE orbF.
  - rewrite -eqn0Ngt cards_eq0 => H _. left. exists x. 
    by rewrite -(setD1K xA) (eqP H) setU0.
Qed.

Lemma wf_leq X (f : X -> nat) : well_founded (fun x y => f x < f y).
Proof. by apply: (@Wf_nat.well_founded_lt_compat _ f) => x y /ltP. Qed.

Lemma nat_size_ind (X:Type) (P : X -> Type) (f : X -> nat) :
   (forall x, (forall y, (f y < f x) -> P y) -> P x) -> forall x, P x.
Proof. move => H. apply: well_founded_induction_type; last exact H. exact: wf_leq. Qed.

Lemma sub_in11W (T1 : predArgType) (D1 D2 : pred T1) (P1 : T1 -> T1 -> Prop) :
 {subset D1 <= D2} -> {in D2&D2, forall x y : T1, P1 x y} -> {in D1&D1, forall x y: T1, P1 x y}.
Proof. firstorder. Qed.

Definition restrict (T:Type) (A : pred T) (e : rel T) :=
  [rel u v in A | e u v].

Lemma subrel_restrict (T : Type) (e : rel T) (a : pred T) : 
  subrel (restrict a e) e.
Proof. move => x y /=. by do 2 case: (_ \in a). Qed.

Lemma symmetric_restrict (T : Type) (A : pred T) (e : rel T) : 
  symmetric e -> symmetric (restrict A e).
Proof. move => sym_e x y /=. by rewrite sym_e [(x \in A) && _]andbC. Qed.



Inductive void : Type :=.

Lemma void_eqP : @Equality.axiom void [rel _ _ | false].
Proof. by case. Qed.

Canonical void_eqType := EqType void (EqMixin void_eqP).

Lemma void_pcancel : pcancel (fun x : void => match x with end) (fun x:unit => None).
Proof. by case. Qed.

Definition void_choiceMixin := PcanChoiceMixin void_pcancel.
Canonical void_choiceType := ChoiceType void void_choiceMixin.
Definition void_countMixin := PcanCountMixin void_pcancel.
Canonical void_countType := CountType void void_countMixin.

Lemma void_enumP : @Finite.axiom [countType of void] [::].
Proof. by case. Qed.

Canonical void_finType := FinType void (FinMixin void_enumP).


Notation rel0 := [rel _ _ | false].

Fact rel0_irrefl {T:Type} : @irreflexive T rel0.
Proof. done. Qed.

Fact rel0_sym {T:Type} : @symmetric T rel0.
Proof. done. Qed.

Definition surjective aT (rT:eqType) (f : aT -> rT) := forall y, exists x, f x == y.

Lemma id_surj (T : eqType) : surjective (@id T).
Proof. move => y. by exists y. Qed.

Lemma emb_surj (T : finType) (e : equiv_rel T) : surjective (\pi_({eq_quot e})).
Proof. move => y. exists (repr y). by rewrite reprK. Qed.

Definition cr {X : choiceType} {Y : eqType} {f : X -> Y} (Sf : surjective f) y : X :=
  xchoose (Sf y).

Lemma crK {X : choiceType} {Y : eqType} {f : X->Y} {Sf : surjective f} x: f (cr Sf x) = x.
Proof. by rewrite (eqP (xchooseP (Sf x))). Qed.

Lemma fun_decompose (aT rT : finType) (f : aT -> rT) : 
  exists (T:finType) (f1 : aT -> T) (f2 : T -> rT), 
    [/\ (forall x, f2 (f1 x) = f x),surjective f1 & injective f2].
Proof.
  exists [finType of seq_sub (codom f)]. exists (fun x => SeqSub (codom_f f x)). exists val.
  split => //; last exact: val_inj. 
  case => y Hy. case/codomP : (Hy) => x Hx. exists x.  change (f x == y). by rewrite -Hx.
Qed.

Lemma inl_inj (A B : Type) : injective (@inl A B).
Proof. by move => a b []. Qed.

Lemma inr_inj (A B : Type) : injective (@inr A B).
Proof. by move => a b []. Qed.

Lemma inr_codom_inl (T1 T2 : finType) x : inr x \in codom (@inl T1 T2) = false.
Proof. apply/negbTE/negP. by case/mapP. Qed.

Lemma inl_codom_inr (T1 T2 : finType) x : inl x \in codom (@inr T1 T2) = false.
Proof. apply/negbTE/negP. by case/mapP. Qed.

Lemma codom_Some (T : finType) (s : seq (option T)) : 
  None \notin s -> {subset s <= codom Some}.
Proof. move => A [a|] B; by [rewrite codom_f|contrab]. Qed.

(** Unlike Logic.unique, the following does not actually require existence *)
Definition unique X (P : X -> Prop) := forall x y, P x -> P y -> x = y.

Lemma empty_uniqe X (P : X -> Prop) : (forall x, ~ P x) -> unique P.
Proof. firstorder. Qed.


(** *** Sequences and Paths *)

Lemma subset_cons (T : eqType) (a:T) s1 (s2 : pred T) : 
  {subset a::s1 <= s2} <-> {subset s1 <= s2} /\ a \in s2.
Proof. 
  split => [A /=|[A B] x]. 
  - by split => [x B|]; apply A; rewrite inE ?eqxx ?B ?orbT.
  - case/predU1P => [-> //|]. exact: A.
Qed.

Lemma path_restrict (T : eqType) (e : rel T) (a : pred T) x p : 
  path (restrict a e) x p -> {subset p <= a}.
Proof.
  elim: p x => //= b p IH x. rewrite -!andbA => /and4P[H1 H2 H3 H4].
  apply/subset_cons. by split; eauto.
Qed.

Lemma take_find (T : Type) (a : pred T) s : ~~ has a (take (find a s) s).
Proof. elim: s => //= x s IH. case E: (a x) => //=. by rewrite E. Qed.

Lemma rev_inj (T : Type) : injective (@rev T).
Proof. apply: (can_inj (g := rev)). exact: revK. Qed.

Lemma rev_belast (T : Type) (x : T) p q : 
  last x p = last x q  -> rev (belast x p) = rev (belast x q) -> p = q.
Proof. 
  elim/last_ind : p => [|p a _]; elim/last_ind : q => [|q b _] //=; 
    try by rewrite belast_rcons => ? /rev_inj. 
  rewrite !belast_rcons !last_rcons => ? /rev_inj. congruence.
Qed.

Lemma project_path (aT rT : Type) (e : rel aT) (e' : rel rT) (f : aT -> rT) a p : 
  {homo f : x y / e x y >-> e' x y} -> path e a p -> path e' (f a) (map f p).
Proof. move => A. elim: p a => //= b p IHp a /andP [H1 H2]. by rewrite A ?IHp. Qed.

Lemma lift_path (aT : finType) (rT : eqType) (e : rel aT) (e' : rel rT) (f : aT -> rT) a p' : 
  (forall x y, e' (f x) (f y) -> e x y) ->
  path e' (f a) p' -> {subset p' <= codom f} -> exists p, path e a p /\ map f p = p'.
Proof.
  move => f_inv. 
  elim: p' a => /= [|fb p' IH a /andP[A B] /subset_cons[S1 S2]]; first by exists [::].
  case: (codomP S2) => b E. subst. case: (IH _ B S1) => p [] *. 
  exists (b::p) => /=. suff: e a b by move -> ; subst. exact: f_inv.
Qed.

(** Proper Name? *)
Lemma aux (T:Type) x0 (a : pred T) s n : 
  ~~ has a s -> ~~ a x0 -> ~~ a (nth x0 s n).
Proof. by elim: s n => // [|b s IH] [|n] //=; rewrite negb_or => /andP[]; auto. Qed.

(* FIXME: should assume upath *)
Lemma subset_upath (T : eqType) (x y : T) (p : seq T) (A : pred T) (e : rel T) : 
  symmetric e -> 
  unique (fun a => a \in A /\ exists t, (t \notin A) /\ (e a t)) ->
  x \in A -> y \in A -> path e x p -> last x p = y -> uniq (x :: p) -> {subset p <= A}.
Proof.
  move => sym_e uni_e Hx Hy. 
  elim: p x Hx => // a p IH x Hx /= /andP[H1 H2] H3 /and3P[H4 H5 H6]. 
  case: (boolP (a \in A)) => [B|B].
  - apply/subset_cons. split => //. apply: (IH a) => //=. by rewrite H5 H6.
  - exfalso. 
    have X : has (mem A) p. 
    { move: a B H3 Hy {H1 H2 H4 H5 H6 IH}. (* Lemma *)
      elim: p => //= [a H1 <- H2|b p IH a *]; first by rewrite H2 in H1.
      case: (boolP (b \in A)) => //= ?. exact: (IH b). }
    set n := (find (mem A) p).
    set b := nth a p n. 
    have Hb : b \in A by rewrite unfold_in nth_find.
    have E : p = rcons (take n p) b ++ drop n.+1 p. 
    { by rewrite -take_nth ?cat_take_drop // -has_find. }
    have F : last a (take n p) \notin A. 
    { rewrite -(nth_last a) unfold_in. apply: aux => //. exact: take_find. }
    suff S : x = b. subst. by rewrite E !inE mem_cat mem_rcons inE eqxx /= orbT in H4. 
    apply: (uni_e) => //. 
    + split => //. by exists a.
    + split => //. exists (last a (take n p)); split => //. rewrite sym_e.
      move: H2. by rewrite {1}E cat_path rcons_path -andbA => /and3P []. 
Qed.

(** *** Reflexive Transitive Closure *)

Lemma sub_connect (T : finType) (e : rel T) : subrel e (connect e).
Proof. exact: connect1. Qed.
Arguments sub_connect [T] e _ _ _.

Lemma sub_trans (T:Type) (e1 e2 e3: rel T) : 
  subrel e1 e2 -> subrel e2 e3 -> subrel e1 e3.
Proof. firstorder. Qed.

Lemma connect_mono (T : finType) (e1 e2 : rel T) : 
  subrel e1 e2 -> subrel (connect e1) (connect e2).
Proof. move => A. apply: connect_sub. exact: sub_trans (sub_connect e2). Qed.

Lemma sub_restrict_connect (T : finType) (e : rel T) (a : pred T) : 
  subrel (connect (restrict a e)) (connect e).
Proof. apply: connect_mono. exact: subrel_restrict. Qed.

Lemma connect_symI (T : finType) (e : rel T) : symmetric e -> connect_sym e.
Proof.
  move => sym_e. 
  suff S x y : connect e x y -> connect e y x.
  { move => x y. apply/idP/idP; exact: S. }
  case/connectP => p. elim: p x y => /= [x y _ -> //|z p IH x y /andP [A B] C].
  apply: (connect_trans (y := z)) (connect1 _); first exact: IH.
  by rewrite sym_e.
Qed.

Lemma connect_img (aT rT : finType) (e : rel aT) (e' : rel rT) (f : aT -> rT) a b :
  {homo f : x y / e x y >-> e' x y} -> connect e a b -> connect e' (f a) (f b).
Proof. 
  move => A. case/connectP => p p1 p2. apply/connectP. 
  exists (map f p); by [exact: project_path p1|rewrite last_map -p2].
Qed.

Hint Resolve Some_inj inl_inj inr_inj.