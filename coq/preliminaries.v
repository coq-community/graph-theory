Require Relation_Definitions.
From mathcomp Require Import all_ssreflect.
Require Import edone.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.

(** * Preliminaries *)

(** Use capitalized names for Coq.Relation_Definitions *)
Definition Symmetric := Relation_Definitions.symmetric.
Definition Transitive := Relation_Definitions.transitive.

(** *** Tactics *)

Ltac reflect_eq := 
  repeat match goal with [H : is_true (_ == _) |- _] => move/eqP : H => H end.
Ltac contrab := 
  match goal with 
    [H1 : is_true ?b, H2 : is_true (~~ ?b) |- _] => by rewrite H1 in H2
  end.

(** *** Generic Trivialities *)

(** Note: [u : sig_subType P] provides for the decidable equality *)
Lemma sub_val_eq (T : eqType) (P : pred T) (u : sig_subType P) x (Px : x \in P) :
  (u == Sub x Px) = (val u == x).
Proof. by case: (SubP u) => {u} u Pu. Qed.

Lemma Some_eqE (T : eqType) (x y : T) : 
  (Some x == Some y) = (x == y).
Proof. by apply/eqP/eqP => [[//]|->]. Qed.

Lemma inj_omap T1 T2 (f : T1 -> T2) : injective f -> injective (omap f).
Proof. by move=> f_inj [x1|] [x2|] //= []/f_inj->. Qed.

Definition ord1 {n : nat} : 'I_n.+2 := Ordinal (isT : 1 < n.+2).
Definition ord2 {n : nat} : 'I_n.+3 := Ordinal (isT : 2 < n.+3).
Definition ord3 {n : nat} : 'I_n.+4 := Ordinal (isT : 3 < n.+4).

Lemma max_mono (I :Type) (r : seq I) P (F G : I -> nat) :
  (forall x, F x <= G x) -> \max_(i <- r | P i) F i <= \max_(i <- r | P i) G i.
Proof.
  move => ?. elim/big_ind2 : _ => // y1 y2 x1 x2 A B.
  by rewrite geq_max !leq_max A B orbT.
Qed.

Lemma leq_subn n m o : n <= m -> n - o <= m.
Proof. move => A. rewrite -[m]subn0. exact: leq_sub. Qed.

Lemma set1_inj (T : finType) : injective (@set1 T).
Proof. move => x y /setP /(_ y). by rewrite !inE eqxx => /eqP. Qed.

Lemma set2C (T : finType) (x y : T) : [set x;y] = [set y;x].
Proof. apply/setP => z. apply/set2P/set2P; tauto. Qed.

Lemma cards3 (T : finType) (a b c : T) : #|[set a;b;c]| <= 3.
Proof. 
  rewrite !cardsU !cards1 !addn1. 
  apply: leq_subn. rewrite ltnS. exact: leq_subn.
Qed.

Lemma card1P (T : finType) (A : pred T) : 
  reflect (exists x, A =i pred1 x) (#|A| == 1).
Proof.
  rewrite -cardsE. apply: (iffP cards1P).
  - move => [x /setP E]. exists x => y. move: (E y). by rewrite !inE.
  - move => [x E]. exists x. apply/setP => y. by rewrite !inE E.
Qed.

Lemma eq_set1P (T : finType) (A : {set T}) (x : T) : 
  reflect (x \in A /\ forall y, y \in A -> y = x) (A == [set x]).
Proof.
  apply: (iffP eqP).
  - move->. rewrite !inE eqxx. by split => // y /set1P.
  - case => H1 H2. apply/setP => y. apply/idP/set1P;[exact: H2| by move ->].
Qed.

(* This looks rather roundabout *)
Lemma card_le1 (T : finType) (D : pred T) (x y : T) : 
  #|D| <= 1 -> x \in D -> y \in D -> x = y.
Proof.
  case: (posnP #|D|) => A B; first by rewrite (card0_eq A).
  have/card1P [z E] : #|D| == 1 by rewrite eqn_leq B.
  by rewrite !E !inE => /eqP-> /eqP->.
Qed. 


Lemma card_gt1P {T : finType}  {D : pred T} : 
  reflect (exists x y, [/\ x \in D, y \in D & x != y]) (1 < #|D|).
Proof. 
  apply: (iffP idP).
  - move => A. case/card_gt0P : (ltnW A) => v inS. 
    rewrite (cardD1 v) inS /= ltnS in A. case/card_gt0P : A => v'. 
    rewrite !inE => /andP [? ?]. by exists v'; exists v.
  - move => [x] [y] [xD yD xy]. apply: contraNT xy.
    rewrite -leqNgt => A. by rewrite (card_le1 A xD yD).
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

Lemma cardsI (T : finType) (A : {set T}) : #|[pred x in A]| = #|A|.
Proof. exact: eq_card. Qed.

Lemma cardsCT (T : finType) (A : {set T}) : 
  (#|~:A| < #|T|) = (0 < #|A|).
Proof. by rewrite -[#|~: A|]add0n -(cardsC A) ltn_add2r. Qed.

Lemma bigcup_set1 (T I : finType) (i0 : I) (F : I -> {set T}) :
  \bigcup_(i in [set i0]) F i = F i0.
Proof. by rewrite -big_filter filter_index_enum enum_set1 big_seq1. Qed.

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

Lemma restrict_mono (T : Type) (A B : pred T) (e : rel T) : 
  subpred A B -> subrel (restrict A e) (restrict B e).
Proof. move => H x y /= => /andP [/andP [H1 H2] ->]. by rewrite !unfold_in !H. Qed.

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

(** *** Disjointness *)
Lemma disjointE (T : finType) (A B : pred T) x : 
  [disjoint A & B] -> x \in A -> x \in B -> False.
Proof. by rewrite disjoint_subset => /subsetP H /H /negP. Qed.

Lemma disjointFr (T : finType) (A B : pred T) (x:T) : 
  [disjoint A & B] -> x \in A -> x \in B = false.
Proof. move => D L. apply/negbTE. apply/negP. exact: (disjointE D). Qed.

Lemma disjointFl (T : finType) (A B : pred T) (x:T) : 
  [disjoint A & B] -> x \in B -> x \in A = false.
Proof. move => D L. apply/negbTE. apply/negP => ?. exact: (disjointE D) L. Qed.

Lemma disjointNI (T : finType) (A B : pred T) (x:T) : 
  x \in A -> x \in B -> ~~ [disjoint A & B].
Proof. move => ? ?. apply/negP => /disjointE. move/(_ x). by apply. Qed.

Definition disjoint_transL := disjoint_trans.
Lemma disjoint_transR (T : finType) (A B C : pred T) :
 A \subset B -> [disjoint C & B] -> [disjoint C & A].
Proof. rewrite ![[disjoint C & _]]disjoint_sym. exact:disjoint_trans. Qed.

Section Disjoint3.
Variables (T : finType) (A B C : mem_pred T).

CoInductive disjoint3_cases (x : T) : bool -> bool -> bool -> Type :=  
| Dis3In1   of x \in A : disjoint3_cases x true false false
| Dis3In2   of x \in B : disjoint3_cases x false true false
| Dis3In3   of x \in C : disjoint3_cases x false false true
| Dis3Notin of x \notin A & x \notin B & x \notin C : disjoint3_cases x false false false.

Lemma disjoint3P x : 
  [&& [disjoint A & B], [disjoint B & C] & [disjoint C & A]] ->
  disjoint3_cases x (x \in A) (x \in B) (x \in C).
Proof.
  case/and3P => D1 D2 D3.
  case: (boolP (x \in A)) => HA. 
  { rewrite (disjointFr D1 HA) (disjointFl D3 HA). by constructor. }
  case: (boolP (x \in B)) => HB. 
  { rewrite (disjointFr D2 HB). by constructor. }
  case: (boolP (x \in C)) => ?; by constructor.
Qed.
End Disjoint3.

Notation "[ 'disjoint3' A & B & C ]" :=
  ([&& [disjoint A & B], [disjoint B & C] & [disjoint C & A]])
  (format "[ 'disjoint3'  A  &  B  &  C ]" ).



(** *** Sequences and Paths *)

Lemma mem_tail (T : eqType) (x y : T) s : y \in s -> y \in x :: s.
Proof. by rewrite inE => ->. Qed.
Arguments mem_tail [T] x [y s].

Lemma notin_tail (X : eqType) (x y : X) s : y \notin x :: s -> y \notin s.
Proof. apply: contraNN. exact: mem_tail. Qed.

Lemma subset_cons (T : eqType) (a:T) s1 (s2 : pred T) : 
  {subset a::s1 <= s2} <-> {subset s1 <= s2} /\ a \in s2.
Proof. 
  split => [A /=|[A B] x]. 
  - by split => [x B|]; apply A; rewrite inE ?eqxx ?B ?orbT.
  - case/predU1P => [-> //|]. exact: A.
Qed.

Lemma subset_seqR (T : finType) (A : pred T) (s : seq T) : 
  (A \subset s) = (A \subset [set x in s]).
Proof. 
  apply/idP/idP => H; apply: subset_trans H _; apply/subsetP => x; by rewrite inE. 
Qed.

Lemma subset_seqL (T : finType) (A : pred T) (s : seq T) : 
  (s \subset A) = ([set x in s] \subset A).
Proof.
  apply/idP/idP; apply: subset_trans; apply/subsetP => x; by rewrite inE. 
Qed.

Lemma mem_catD (T:finType) (x:T) (s1 s2 : seq T) : 
  [disjoint s1 & s2] -> (x \in s1 ++ s2) = (x \in s1) (+) (x \in s2).
Proof. 
  move => D. rewrite mem_cat. case C1 : (x \in s1) => //=. 
  symmetry. apply/negP. exact: disjointE D _.
Qed.
Arguments mem_catD [T x s1 s2].

Lemma path_restrict (T : eqType) (e : rel T) (a : pred T) x p : 
  path (restrict a e) x p -> {subset p <= a}.
Proof.
  elim: p x => //= b p IH x. rewrite -!andbA => /and4P[H1 H2 H3 H4].
  apply/subset_cons. by split; eauto.
Qed.

Lemma last_take (T : eqType) (x : T) (p : seq T) (n : nat): 
  n <= size p -> last x (take n p) = nth x (x :: p) n.
Proof.
  elim: p x n => [|a p IHp] x [|n] Hn //=.
  by rewrite IHp // (set_nth_default a x). 
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
  - apply/subset_cons. split => //. by apply: (IH a) => //=. 
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

Lemma restrictE (T : finType) (e : rel T) (A : pred T) : 
  A =i predT -> connect (restrict A e) =2 connect e.
Proof. 
  move => H x y. rewrite (eq_connect (e' := e)) //. 
  move => {x y} x y /=. by rewrite !H.
Qed.

Lemma connect_symI (T : finType) (e : rel T) : symmetric e -> connect_sym e.
Proof.
  move => sym_e. 
  suff S x y : connect e x y -> connect e y x.
  { move => x y. apply/idP/idP; exact: S. }
  case/connectP => p. elim: p x y => /= [x y _ -> //|z p IH x y /andP [A B] C].
  apply: (connect_trans (y := z)) (connect1 _); first exact: IH.
  by rewrite sym_e.
Qed.

Lemma equivalence_rel_of_sym (T : finType) (e : rel T) :
  symmetric e -> equivalence_rel (connect e).
Proof. 
  move => sym_e x y z. split => // A. apply/idP/idP; last exact: connect_trans.
  rewrite connect_symI // in A. exact: connect_trans A.
Qed.

Lemma connect_img (aT rT : finType) (e : rel aT) (e' : rel rT) (f : aT -> rT) a b :
  {homo f : x y / e x y >-> e' x y} -> connect e a b -> connect e' (f a) (f b).
Proof. 
  move => A. case/connectP => p p1 p2. apply/connectP. 
  exists (map f p); by [exact: project_path p1|rewrite last_map -p2].
Qed.

Hint Resolve Some_inj inl_inj inr_inj.

(** *** Set image *)
Lemma inj_imset (aT rT : finType) (f : aT -> rT) (A : {set aT}) (x : aT) :
  injective f -> (f x \in f @: A) = (x \in A).
Proof.
  move=> f_inj; apply/imsetP/idP;
  [by case=> [y] ? /f_inj-> | by move=> ?; exists x].
Qed.

(** *** Replacement for partial functions *)

Definition pimset (aT rT : finType) (f : aT -> option rT) (A : {set aT}) := 
  [set x : rT | [exists (x0 | x0 \in A), f x0 == Some x]].

Lemma pimsetP (aT rT : finType) (f : aT -> option rT) (A : {set aT}) x : 
  reflect (exists2 x0, x0 \in A & f x0 == Some x) (x \in pimset f A).
Proof. rewrite inE. exact: (iffP exists_inP). Qed.
      
Lemma pimset_card (aT rT : finType) (f : aT -> option rT) (A : {set aT}) : 
  #|[set x : rT | [exists x0 in A, f x0 == Some x]]| <= #|A|.
Proof.
  apply: (@leq_trans #|[set f x | x in A]|); last exact: leq_imset_card.
  rewrite -[X in X <= _](card_imset _ (@Some_inj _)).
  apply: subset_leq_card. apply/subsetP => ? /imsetP [?] /pimsetP [x0].
  move => H /eqP <- ->. by rewrite mem_imset. 
Qed.


(** *** Partitions *)

Lemma mem_cover (T : finType) (P : {set {set T}}) (x : T) (A : {set T}) : 
  A \in P -> x \in A -> x \in cover P.
Proof. move => HP HA. apply/bigcupP. by exists A. Qed.

(* TOTHINK: This proof appears to complicated/monolithic *)
Lemma equivalence_partition_gt1P (T : finType) (R : rel T) (D : {set T}) :
   {in D & &, equivalence_rel R} ->
   reflect (exists x y, [/\ x \in D, y \in D & ~~ R x y]) (1 < #|equivalence_partition R D|).
Proof.
  move => E. 
  set P := equivalence_partition R D.
  have EP : partition P D by apply: equivalence_partitionP. 
  apply: (iffP card_gt1P). 
  - move => [B1] [B2] [A B C]. 
    have ?: set0 \notin P by case/and3P: EP. 
    case: (set_0Vmem B1) => [?|[x1 inB1]]; first by subst; contrab.
    case: (set_0Vmem B2) => [?|[x2 inB2]]; first by subst; contrab.
    have ? : x1 \in cover P. { apply/bigcupP. by exists B1. }
    have ? : x2 \in cover P. { apply/bigcupP. by exists B2. }
    exists x1; exists x2. split; rewrite -?(cover_partition EP) //. 
    have TP : trivIset P by case/and3P : EP.
    apply:contraNN C => Rxy. 
    rewrite -(def_pblock TP A inB1) -(def_pblock TP B inB2) eq_pblock //.  
    by rewrite pblock_equivalence_partition // -?(cover_partition EP).
  - move => [x] [y] [A B C]. exists (pblock P x). exists (pblock P y). 
    rewrite !pblock_mem ?(cover_partition EP) //. split => //.
    rewrite eq_pblock ?(cover_partition EP) //; last by case/and3P : EP.
    by rewrite pblock_equivalence_partition.
Qed.
