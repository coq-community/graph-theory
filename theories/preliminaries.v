From mathcomp Require Import all_ssreflect.
Require Import edone.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Preliminaries *)

(** Use capitalized names for Coq.Relation_Definitions *)
(* Definition Symmetric := Relation_Definitions.symmetric. *)
(* Definition Transitive := Relation_Definitions.transitive. *)

(** *** Tactics *)

Axiom admitted_case : False.
Ltac admit := case admitted_case.

Ltac reflect_eq := 
  repeat match goal with [H : is_true (_ == _) |- _] => move/eqP : H => H end.
Ltac contrab := 
  match goal with 
    [H1 : is_true ?b, H2 : is_true (~~ ?b) |- _] => by rewrite H1 in H2
  end.
Tactic Notation "existsb" uconstr(x) := apply/existsP;exists x.

Hint Extern 0 (injective Some) => exact: @Some_inj : core.

(** *** Notations *) 

Notation "'Σ' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p%type)) ..))
  (at level 200, x binder, y binder, right associativity).

(** *** Generic Trivialities *)

Lemma enum_sum (T1 T2 : finType) (p : pred (T1 + T2)) :
  enum p = 
  map inl (enum [pred i | p (inl i)]) ++ map inr (enum [pred i | p (inr i)]).
Proof.
by rewrite /enum_mem {1}unlock /= /sum_enum filter_cat !filter_map.
Qed.

Lemma enum_unit (p : pred unit) : enum p = filter p [:: tt].
Proof. by rewrite /enum_mem unlock. Qed.

Lemma contraTnot b (P : Prop) : (P -> ~~ b) -> (b -> ~ P).
Proof. by case: b => //= H _ /H. Qed.

Lemma contraNnot (b : bool) (P : Prop) : (P -> b) -> (~~ b -> ~ P).
Proof. rewrite -{1}[b]negbK. exact: contraTnot. Qed.

Lemma contraPT (P : Prop) (b : bool) : (~~ b -> ~ P) -> P -> b.
Proof. case: b => //= H1 H2. exfalso. exact: H1. Qed.

Lemma contra_notT (b : bool) (P : Prop) : (~~ b -> P) -> ~ P -> b.
Proof. by case: b => //= *; exfalso; auto. Qed.

Lemma contraPN (b : bool) (P : Prop) : (b -> ~ P) -> (P -> ~~ b).
Proof. case: b => //=. by move/(_ isT) => H /H. Qed.

Lemma contraPneq (T:eqType) (a b : T) (P : Prop) : (a = b -> ~ P) -> (P -> a != b).
Proof. move => A. by apply: contraPN => /eqP. Qed.

Lemma contraPeq (T:eqType) (a b : T) (P : Prop) : (a != b -> ~ P) -> (P -> a = b).
Proof. move => H HP. by apply: contraTeq isT => /H /(_ HP). Qed.

Lemma existsPn {T : finType} {P : pred T} : 
  reflect (forall x, ~~ P x) (~~ [exists x, P x]).
Proof. rewrite negb_exists. exact: forallP. Qed.

Lemma forallPn {T : finType} {P : pred T} : 
  reflect (exists x, ~~ P x) (~~ [forall x, P x]).
Proof. rewrite negb_forall. exact: existsP. Qed.

Lemma exists_inPn {T : finType} {A P : pred T} : 
  reflect (forall x, x \in A -> ~~ P x) (~~ [exists x in A, P x]).
Proof. rewrite negb_exists_in. exact: forall_inP. Qed.

Lemma forall_inPn {T : finType} {A P : pred T} : 
  reflect (exists2 x, x \in A & ~~ P x) (~~ [forall x in A, P x]).
Proof. rewrite negb_forall_in. exact: exists_inP. Qed.

Lemma existsb_eq (T : finType) (P Q : pred T) : 
  (forall b, P b = Q b) -> [exists b, P b] = [exists b, Q b].
Proof. move => E. apply/existsP/existsP; case => b Hb; exists b; congruence. Qed.

Lemma existsb_case (P : pred bool) : [exists b, P b] = P true || P false.
Proof. apply/existsP/idP => [[[|] -> //]|/orP[H|H]]; eexists; exact H. Qed.

Lemma all_cons (T : eqType) (P : T -> Prop) a (s : seq T) : 
  (forall x, x \in a :: s -> P x) <-> (P a) /\ (forall x, x \in s -> P x).
Proof.
  split => [A|[A B]]. 
  - by split => [|b Hb]; apply: A; rewrite !inE ?eqxx ?Hb. 
  - move => x /predU1P [-> //|]. exact: B.
Qed.

Lemma subrelP (T : finType) (e1 e2 : rel T) : 
  reflect (subrel e1 e2) ([pred x | e1 x.1 x.2] \subset [pred x | e2 x.1 x.2]).
Proof. apply: (iffP subsetP) => [S x y /(S (x,y)) //|S [x y]]. exact: S. Qed.

Lemma eqb_negR (b1 b2 : bool) : (b1 == ~~ b2) = (b1 != b2).
Proof. by case: b1; case: b2. Qed.

Lemma orb_sum (a b : bool) : a || b -> (a + b)%type.
Proof. by case: a => /=; [left|right]. Qed.

Lemma inj_card_leq (A B: finType) (f : A -> B) : injective f -> #|A| <= #|B|.
Proof. move => inj_f. by rewrite -[#|A|](card_codom (f := f)) // max_card. Qed.

Lemma bij_card_eq (A B: finType) (f : A -> B) : bijective f -> #|A| = #|B|.
Proof. 
  case => g can_f can_g. apply/eqP. 
  rewrite eqn_leq (inj_card_leq (f := f)) ?(inj_card_leq (f := g)) //; exact: can_inj.
Qed.

(** Note: [u : sig_subType P] provides for the decidable equality *)
Lemma sub_val_eq (T : eqType) (P : pred T) (u : sig_subType P) x (Px : x \in P) :
  (u == Sub x Px) = (val u == x).
Proof. by case: (SubP u) => {u} u Pu. Qed.

(** TODO: this should be subsumed by valK' below *)
Lemma valK'' (T : eqType) (P : pred T) (u : sig_subType P) (Px : val u \in P) : 
  Sub (val u) Px = u.
Proof. exact: val_inj. Qed.

Lemma valK' (T : Type) (P : pred T) (sT : subType P) (x : sT) (p : P (val x)) : 
  Sub (val x) p = x.
Proof. apply: val_inj. by rewrite SubK. Qed.

Lemma Some_eqE (T : eqType) (x y : T) : 
  (Some x == Some y) = (x == y).
Proof. by apply/eqP/eqP => [[//]|->]. Qed.

Lemma inl_eqE (A B : eqType) x y : 
  (@inl A B x == @inl A B y) = (x == y).
Proof. by apply/eqP/eqP => [[]|->]. Qed.

Lemma inr_eqE (A B : eqType) x y : 
  (@inr A B x == @inr A B y) = (x == y).
Proof. by apply/eqP/eqP => [[]|->]. Qed.

Definition sum_eqE := (inl_eqE,inr_eqE).


Lemma inj_omap T1 T2 (f : T1 -> T2) : injective f -> injective (omap f).
Proof. by move=> f_inj [x1|] [x2|] //= []/f_inj->. Qed.

Definition ord1 {n : nat} : 'I_n.+2 := Ordinal (isT : 1 < n.+2).
Definition ord2 {n : nat} : 'I_n.+3 := Ordinal (isT : 2 < n.+3).
Definition ord3 {n : nat} : 'I_n.+4 := Ordinal (isT : 3 < n.+4).

Lemma ord_size_enum n (s : seq 'I_n) : uniq s -> n <= size s -> forall k, k \in s.
Proof. 
  move => uniq_s size_s k. 
  rewrite (@uniq_min_size _ _ (enum 'I_n)) ?size_enum_ord ?mem_enum // => z _.
  by rewrite mem_enum.
Qed.

Lemma ord_fresh n (s : seq 'I_n) : size s < n -> exists k : 'I_n, k \notin s.
Proof. 
  move => H. suff: 0 < #|[predC s]|.
  { case/card_gt0P => z. rewrite !inE => ?; by exists z. }
  rewrite -(ltn_add2l #|s|) cardC addn0 card_ord. 
  apply: leq_ltn_trans H. exact: card_size.
Qed.

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

Lemma id_bij T : bijective (@id T).
Proof. exact: (Bijective (g := id)). Qed.

Lemma set2C (T : finType) (x y : T) : [set x;y] = [set y;x].
Proof. apply/setP => z. apply/set2P/set2P; tauto. Qed.

Lemma card_ltnT (T : finType) (p : pred T) x : ~~ p x -> #|p| < #|{: T}|.
Proof. 
  move => A. apply/proper_card. rewrite properE. 
  apply/andP; split; first by apply/subsetP.
  apply/subsetPn. by exists x. 
Qed.

Lemma setU1_mem (T : finType) x (A : {set T}) : x \in A -> x |: A = A.
Proof. 
  move => H. apply/setP => y. rewrite !inE. 
  case: (boolP (y == x)) => // /eqP ->. by rewrite H.
Qed.

Variant picks_spec (T : finType) (A : {set T}) : option T -> Type := 
| Picks x & x \in A : picks_spec A (Some x)
| Nopicks & A = set0 : picks_spec A None.

Lemma picksP (T : finType) (A : {set T}) : picks_spec A [pick x in A].
Proof. 
  case: pickP => /= [|eq0]; first exact: Picks. 
  apply/Nopicks/setP => x. by rewrite !inE eq0.
Qed.

Lemma set10 (T : finType) (e : T) : [set e] != set0.
Proof. apply/set0Pn. exists e. by rewrite inE. Qed.

Lemma setU1_neq (T : finType) (e : T) (A : {set T}) : e |: A != set0.
Proof. apply/set0Pn. exists e. by rewrite !inE eqxx. Qed.

(** TOTHINK: [#|P| <= #|aT|] would suffice, the other direction is
implied. But the same is true for [inj_card_onto]. *)
Lemma inj_card_onto_pred (aT rT : finType) (f : aT -> rT) (P : pred rT) : 
  injective f -> (forall x, f x \in P) -> #|aT| = #|P| -> {in P, forall y, y \in codom f}.
Proof.
  move => f_inj fP E y yP.
  pose rT' := { y : rT | P y}.
  pose f' (x:aT) : rT' := Sub (f x) (fP x).
  have/inj_card_onto f'_inj : injective f'. { move => x1 x2 []. exact: f_inj. }
  rewrite card_sig E in f'_inj. 
  case/mapP : (f'_inj erefl (Sub y yP)) => x _ [] ->. exact: codom_f. 
Qed.

(** TODO: check whether the collection of lemmas on sets/predicates
and their cardinalities can be simplified *)

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

Lemma setN01E (T : finType) A (x:T) : 
  A != set0 -> A != [set x] -> exists2 y, y \in A & y != x.
Proof.
  case/set0Pn => y Hy H1. apply/exists_inP. apply: contraNT H1.
  rewrite negb_exists_in => /forall_inP H. 
  rewrite eqEsubset sub1set (_ : x \in A) ?andbT. 
  - apply/subsetP => z. rewrite !inE => /H. by rewrite negbK.
  - move/H : (Hy) => /negPn/eqP Hy'. by subst.
Qed.

Lemma eq_set1P (T : finType) (A : {set T}) (x : T) : 
  reflect (x \in A /\ forall y, y \in A -> y = x) (A == [set x]).
Proof.
  apply: (iffP eqP).
  - move->. rewrite !inE eqxx. by split => // y /set1P.
  - case => H1 H2. apply/setP => y. apply/idP/set1P;[exact: H2| by move ->].
Qed.

Lemma card_le1 (T : finType) (D : pred T) (x y : T) : 
  #|D| <= 1 -> x \in D -> y \in D -> x = y.
Proof.
  case: (posnP #|D|) => A B; first by rewrite (card0_eq A).
  have/card1P [z E] : #|D| == 1 by rewrite eqn_leq B.
  by rewrite !E !inE => /eqP-> /eqP->.
Qed.

Lemma uniq_take (T : eqType) (s : seq T) n : uniq s -> uniq (take n s).
Proof. 
  elim: n s => /= => [|n IHn] s; first by rewrite take0.
  case: s => [|a s] //= /andP [A B]. rewrite IHn // andbT. 
  apply: contraNN A. exact: mem_take.
Qed.

Lemma card_gtnP {T : finType} {A : pred T} {n} : 
  reflect (exists s, [/\ uniq s, size s = n & {subset s <= A}]) (n <= #|A|).
Proof.
  apply: (iffP idP) => [H|[s] [S1 S2 /subsetP S3]].
  - exists (take n (enum A)). rewrite uniq_take ?enum_uniq // size_take. split => //. 
    + case: (ltnP n (size (enum A))) => // H'. 
      apply/eqP. by rewrite eqn_leq H' -cardE H.
    + move => x /mem_take. by rewrite mem_enum.
  - rewrite -S2 -(card_uniqP S1). exact: subset_leq_card. 
Qed.

Lemma card_gt1P {T : finType}  {D : pred T} : 
  reflect (exists x y, [/\ x \in D, y \in D & x != y]) (1 < #|D|).
Proof. 
  apply: (iffP card_gtnP) => [[s] []|[x] [y]].
  - case: s => [//|a [//|b [|//]]] /=. rewrite inE andbT => A _ B.
    exists a; exists b. by rewrite A !B ?inE ?eqxx.
  - move => [xD yD xy]. exists [:: x;y] => /=. rewrite inE xy.
    split => // z. by rewrite !inE => /orP [] /eqP->.
Qed.

Lemma card_gt2P {T : finType}  {D : pred T} : 
  reflect (exists x y z, [/\ x \in D, y \in D & z \in D] /\ [/\ x!=y, y!=z & z!=x]) (2 < #|D|).
Proof.
  apply: (iffP card_gtnP) => [[s] []|[x] [y] [z]].
  - case: s => [|a [|b [|c [|]]]] //=. rewrite !inE !andbT negb_or -andbA. 
    move => /and3P [A B C] _ S. exists a;exists b;exists c. by rewrite A C eq_sym B !S ?inE ?eqxx.
  - move => [[xD yD zD] [A B C]]. exists [:: x;y;z] => /=. rewrite !inE negb_or A B eq_sym C.
    split => // z'. by rewrite !inE => /or3P [] /eqP->.
Qed.

Lemma card_le1P (T : finType) (A : pred T) : 
  reflect {in A &, forall x y : T, x = y} (#|A| <= 1).
Proof.
  apply: introP => [H x y|]; first exact: card_le1.
  rewrite leqNgt negbK. move/card_gt1P => [x] [y] [xA yA xy] H.
  apply:(negP xy). by rewrite (H y x).
Qed.

Lemma cards2P (T : finType) (A : {set T}): 
  reflect (exists x y : T, x != y /\ A = [set x;y]) (#|A| == 2).
Proof.
  apply: (iffP idP) => [H|[x] [y] [xy ->]]; last by rewrite cards2 xy.
  have/card_gt1P [x [y] [H1 H2 H3]] : 1 < #|A| by rewrite (eqP H).
  exists x; exists y. split => //. apply/setP => z. rewrite !inE.
  apply/idP/idP => [zA|/orP[] /eqP-> //]. apply: contraTT H.
  rewrite negb_or neq_ltn => /andP [z1 z2]. apply/orP;right.
  apply/card_gt2P. exists x;exists y;exists z => //. by rewrite [_ == z]eq_sym. 
Qed.  

Lemma card12 (T : finType) (A : {set T}) :
  0 < #|A| -> #|A| <= 2 -> 
                  (exists x, A = [set x]) \/ exists x y, x != y /\ A = [set x;y].
Proof.
  move => H1 H2. case: (ltnP #|A| 2) => H3.
  - left. apply/cards1P. by rewrite eqn_leq -ltnS H3.
  - right. apply/cards2P. by rewrite eqn_leq H2 H3.
Qed.

Lemma cardsI (T : finType) (A : {set T}) : #|[pred x in A]| = #|A|.
Proof. exact: eq_card. Qed.

Lemma cardsCT (T : finType) (A : {set T}) : 
  (#|~:A| < #|T|) = (0 < #|A|).
Proof. by rewrite -[#|~: A|]add0n -(cardsC A) ltn_add2r. Qed.

Lemma bigcup_set1 (T I : finType) (i0 : I) (F : I -> {set T}) :
  \bigcup_(i in [set i0]) F i = F i0.
Proof. by rewrite (big_pred1 i0) // => i; rewrite inE. Qed.

Lemma wf_leq X (f : X -> nat) : well_founded (fun x y => f x < f y).
Proof. by apply: (@Wf_nat.well_founded_lt_compat _ f) => x y /ltP. Qed.

Lemma nat_size_ind (X:Type) (P : X -> Type) (f : X -> nat) :
   (forall x, (forall y, (f y < f x) -> P y) -> P x) -> forall x, P x.
Proof. move => H. apply: well_founded_induction_type; last exact H. exact: wf_leq. Qed.

(** TODO: this form allows giving f without giving P which allows using [elim/(size_ind f)] *)
Definition size_ind (X : Type) (f : X -> nat) (P : X -> Prop) := @nat_size_ind X P f.
Arguments size_ind [X] f [P].


Lemma wf_proper (T:finType) : well_founded (fun B A : pred T => B \proper A).
Proof. 
  apply: (@Wf_nat.well_founded_lt_compat _ (fun x : pred T => #|x|)) => A B A_proper_B.
  apply/ltP. exact: proper_card.
Qed.

Lemma proper_ind (T: finType) (P : pred T  -> Type) : 
  (forall A : pred T, (forall B : pred T, B \proper A -> P B) -> P A) -> forall A, P A.
Proof. move => H. apply: well_founded_induction_type H. exact: wf_proper. Qed.

Lemma wf_propers (T:finType) : well_founded (fun B A : {set T} => B \proper A).
Proof. 
  apply: (@Wf_nat.well_founded_lt_compat _ (fun x : {set T} => #|x|)) => A B A_proper_B.
  apply/ltP. exact: proper_card.
Qed.

Lemma propers_ind (T: finType) (P : {set T} -> Type) : 
  (forall A : {set T}, (forall B : {set T}, B \proper A -> P B) -> P A) -> forall A, P A.
Proof. move => H. apply: well_founded_induction_type H. exact: wf_propers. Qed.

Definition smallest (T : finType) P (U : {set T}) := P U /\ forall V : {set T}, P V -> #|U| <= #|V|.

Lemma below_smallest (T : finType) P (U V : {set T}) : 
  smallest P U -> #|V| < #|U| -> ~ P V.
Proof. move => [_ small_U] V_leq_U P_V. by rewrite leqNgt ltnS small_U in V_leq_U. Qed.

Definition largest (T : finType) P (U : {set T}) := P U /\ forall V : {set T}, P V -> #|V| <= #|U|.

Lemma above_largest (T : finType) P (U V : {set T}) : 
  largest P U -> #|V| > #|U| -> ~ P V.
Proof. move => [_ large_U] U_leq_V P_V. by rewrite leqNgt ltnS large_U in U_leq_V. Qed.

Inductive maxn_cases n m : nat -> Type := 
| MaxnR of n <= m : maxn_cases n m m
| MaxnL of m < n : maxn_cases n m n.

Lemma maxnP n m : maxn_cases n m (maxn n m).
Proof. 
(* compat:mathcomp-1.10.0 *)
by case: (leqP n m) => H; rewrite ?(maxn_idPr H) ?(maxn_idPl (ltnW H)); constructor.
Qed.

Lemma maxn_eq n m : (maxn n m == n) || (maxn n m == m).
Proof. case: maxnP; by rewrite !eqxx. Qed.

(** TOTHINK: It would suffice if { y | m y <= m x} were enumerable for every [x] *) 
Lemma ex_smallest (T : finType) (p : pred T) (m : T -> nat) x0 : 
  p x0 -> exists2 x, p x & forall y, p y -> m x <= m y.
Proof.
  move: x0. apply: (nat_size_ind (f := m)) => x0 IH p0.
  case: (boolP [exists x in p, m x < m x0]).
  - case/exists_inP => x *. exact: (IH x).
  - move/exists_inPn => H. exists x0 => // y /H. by rewrite -leqNgt.
Qed.

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
Notation vfun := (fun x: void => match x with end).  

Lemma void_eqP : @Equality.axiom void [rel _ _ | false].
Proof. by case. Qed.

Canonical void_eqType := EqType void (EqMixin void_eqP).

Lemma void_pcancel : pcancel vfun (fun x: unit => None).
Proof. by case. Qed.

Definition void_choiceMixin := PcanChoiceMixin void_pcancel.
Canonical void_choiceType := ChoiceType void void_choiceMixin.
Definition void_countMixin := PcanCountMixin void_pcancel.
Canonical void_countType := CountType void void_countMixin.

Lemma void_enumP : @Finite.axiom [countType of void] [::].
Proof. by case. Qed.

Canonical void_finType := FinType void (FinMixin void_enumP).

Lemma card_void : #|{: void}| = 0.
Proof. exact: eq_card0. Qed.

Notation rel0 := [rel _ _ | false].

Fact rel0_irrefl {T:Type} : @irreflexive T rel0.
Proof. done. Qed.

Fact rel0_sym {T:Type} : @symmetric T rel0.
Proof. done. Qed.

Lemma relU_sym' (T : Type) (e e' : rel T) :
  symmetric e -> symmetric e' -> symmetric (relU e e').
Proof. move => sym_e sym_e' x y /=. by rewrite sym_e sym_e'. Qed.


Definition surjective aT (rT:eqType) (f : aT -> rT) := forall y, exists x, f x == y.

Lemma id_surj (T : eqType) : surjective (@id T).
Proof. move => y. by exists y. Qed.

Lemma bij_surj A (B : eqType) (f : A -> B) : bijective f -> surjective f.
Proof. case => g g1 g2 x. exists (g x). by rewrite g2. Qed.

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

Lemma disjointP (T : finType) (A B : pred T):
  reflect (forall x, x \in A -> x \in B -> False) [disjoint A & B].
Proof.
  rewrite disjoint_subset. 
  apply:(iffP subsetP) => H x; by move/H/negP. 
Qed.

Lemma disjointsU (T : finType) (A B C : {set T}):
  [disjoint A & C] -> [disjoint B & C] -> [disjoint A :|: B & C].
Proof.
  move => a b. 
  apply/disjointP => x /setUP[]; by move: x; apply/disjointP.
Qed.

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

Lemma disjoint_exists (T : finType) (A B : pred T) : 
  [disjoint A & B] = ~~ [exists x in A, x \in B].
Proof. rewrite negb_exists_in disjoint_subset. by apply/subsetP/forall_inP; apply. Qed.

Definition disjoint_transL := disjoint_trans.
Lemma disjoint_transR (T : finType) (A B C : pred T) :
 A \subset B -> [disjoint C & B] -> [disjoint C & A].
Proof. rewrite ![[disjoint C & _]]disjoint_sym. exact:disjoint_trans. Qed.

Lemma disjointW (T : finType) (A B C D : pred T) : 
    A \subset B -> C \subset D -> [disjoint B & D] -> [disjoint A & C].
Proof. 
  move => subAB subCD BD. apply: (disjoint_trans subAB). 
  move: BD. rewrite !(disjoint_sym B). exact: disjoint_trans.
Qed.

Lemma disjoints1 (T : finType) (x : T) (A : pred T) : [disjoint [set x] & A] = (x \notin A).
Proof. rewrite (@eq_disjoint1 _ x) // => ?. by rewrite !inE. Qed.


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


(** *** Function Update *)

Section update.
Variables (aT : eqType) (rT : Type) (f : aT -> rT).
Definition update x a := fun z => if z == x then a else f z.

Lemma update_neq x z a : x != z -> update z a x = f x.
Proof. rewrite /update. by case: ifP. Qed.

Lemma update_eq z a : update z a z = a.
Proof. by rewrite /update eqxx. Qed.

End update.
Definition updateE := (update_eq,update_neq).
Notation "f [upd x := y ]" := (update f x y) (at level 2, left associativity, format "f [upd  x  :=  y ]").

Lemma update_same (aT : eqType) (rT : Type) (f : aT -> rT) x a b : 
  f[upd x := a][upd x := b] =1 f[upd x := b].
Proof. rewrite /update => z. by case: (z == x). Qed.

Lemma update_fx (aT : eqType) (rT : Type) (f : aT -> rT) (x : aT):
  f[upd x := f x] =1 f.
Proof. move => y. rewrite /update. by case: (altP (y =P x)) => [->|]. Qed.


(** *** Sequences and Paths *)

Lemma tnth_uniq (T : eqType) n (t : n.-tuple T) (i j : 'I_n) : 
  uniq t -> (tnth t i == tnth t j) = (i == j).
Proof.
  move => uniq_t. 
  rewrite /tnth (set_nth_default (tnth_default t j)) ?size_tuple ?ltn_ord //. 
  by rewrite nth_uniq // size_tuple ltn_ord.
Qed.

Lemma tnth_map_in (T:eqType) rT (s : seq T) (f : T -> rT) e 
  (He : index e s < size [seq f x | x <- s]) : e \in s ->
  tnth (in_tuple [seq f x | x <- s]) (Ordinal He)  = f e.
Proof.
  move => in_s. rewrite /tnth /= (nth_map e) ?nth_index //. 
  apply: leq_trans He _. by rewrite size_map.
Qed.

Lemma tnth_cons (T : Type) a (s : seq T) (i : 'I_(size s).+1) (j : 'I_(size s)) :
  j.+1 = i -> tnth (in_tuple (a :: s)) i = tnth (in_tuple s) j.
Proof. move => E. rewrite /tnth -E /=. exact: set_nth_default. Qed.
Arguments tnth_cons [T a s i j].

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

Lemma restrict_path (T : eqType) (e : rel T) (A : pred T) x p :
  path e x p -> x \in A -> {subset p <= A} -> path (restrict A e) x p.
Proof.
  elim: p x => [//|a p IH] x /= /andP[-> pth_p] -> /subset_cons [? Ha] /=.
  rewrite /= Ha. exact: IH.
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

Lemma last_belast_eq (T : Type) (x : T) p q : 
  last x p = last x q  -> belast x p = belast x q -> p = q.
Proof. 
  elim/last_ind : p => [|p a _]; elim/last_ind : q => [|q b _] //=; 
    try by rewrite belast_rcons => ?.
  rewrite !belast_rcons !last_rcons => ?. congruence.
Qed.

Lemma project_path (aT rT : Type) (e : rel aT) (e' : rel rT) (f : aT -> rT) a p : 
  {homo f : x y / e x y >-> e' x y} -> path e a p -> path e' (f a) (map f p).
Proof. move => A. elim: p a => //= b p IHp a /andP [H1 H2]. by rewrite A ?IHp. Qed.

Lemma lift_path (aT : finType) (rT : eqType) (e : rel aT) (e' : rel rT) (f : aT -> rT) a p' : 
  (forall x y, f x \in f a :: p' -> f y \in f a :: p' -> e' (f x) (f y) -> e x y) ->
  path e' (f a) p' -> {subset p' <= codom f} -> exists p, path e a p /\ map f p = p'.
Proof.
  move => f_inv.
  elim: p' a f_inv => /= [|fb p' IH a H /andP[A B] /subset_cons[S1 S2]]; first by exists [::].
  case: (codomP S2) => b E. subst. case: (IH b) => // => [x y Hx Hy|p [] *]. 
  - by apply: H; rewrite inE ?Hx ?Hy.
  - exists (b::p) => /=. suff: e a b by move -> ; subst. by rewrite H ?inE ?eqxx.
Qed.

(** *** Reflexive Transitive Closure *)

Lemma connectUP (T : finType) (e : rel T) (x y : T) :
  reflect (exists p, [/\ path e x p, last x p = y & uniq (x::p)])
          (connect e x y).
Proof.
  apply: (iffP connectP) => [[p p1 p2]|]; last by firstorder.
  exists (shorten x p). by case/shortenP : p1 p2 => p' ? ? _ /esym ?.
Qed.
Arguments connectUP {T e x y}.

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

Lemma connect_restrict_mono (T : finType) (e : rel T) (A B : pred T) :
  A \subset B -> subrel (connect (restrict A e)) (connect (restrict B e)).
Proof.
  move/subsetP => AB. apply: connect_mono => u v /=.
  rewrite -!andbA => /and3P [? ? ->]. by rewrite !AB.
Qed.

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

Definition sc (T : Type) (e : rel T) := [rel x y | e x y || e y x].

Lemma sc_sym (T : Type) (e : rel T) : symmetric (sc e).
Proof. move => x y /=. by rewrite orbC. Qed.

Lemma sc_eq T T' (e : rel T) (e' : rel T') f x y :
  (forall x y, e' (f x) (f y) = e x y) -> sc e' (f x) (f y) = sc e x y.
Proof. move => H. by rewrite /sc /= !H. Qed.

(** Equivalence Closure *)

Section Equivalence.

Variables (T : finType) (e : rel T).

Definition equiv_of := connect (sc e).

Definition equiv_of_refl : reflexive equiv_of.
Proof. exact: connect0. Qed.

Lemma equiv_of_sym : symmetric equiv_of.
Proof. apply: connect_symI => x y /=. by rewrite orbC. Qed.

Definition equiv_of_trans : transitive equiv_of.
Proof. exact: connect_trans. Qed.

(* Canonical equiv_of_equivalence := *)
(*   EquivRel equiv_of equiv_of_refl equiv_of_sym equiv_of_trans. *)

Lemma sub_equiv_of : subrel e equiv_of.
Proof. move => x y He. apply: connect1 => /=. by rewrite He. Qed.

End Equivalence.

Lemma lift_equiv (T1 T2 : finType) (E1 : rel T1) (E2 : rel T2) h :
  bijective h -> (forall x y, E1 x y = E2 (h x) (h y)) ->
  (forall x y, equiv_of E1 x y = equiv_of E2 (h x) (h y)).
Proof.
  move=> [hinv] hK hinvK hE x y. rewrite /equiv_of. apply/idP/idP.
  - by apply: connect_img => {x y} x y /=; rewrite !hE.
  - rewrite -{2}(hK x) -{2}(hK y).
    by apply: connect_img => {x y} x y /=; rewrite !hE !hinvK.
Qed.

Hint Resolve Some_inj inl_inj inr_inj : core.


(** *** Set preimage *)

Notation "f @^-1 x" := (preimset f (mem (pred1 x))) (at level 24) : set_scope.  

Lemma mem_preim (aT rT : finType) (f : aT -> rT) x y : 
  (f x == y) = (x \in f @^-1 y).
Proof. by rewrite !inE. Qed.

Lemma preim_omap_Some (aT rT : finType) (f : aT -> rT) y :
  (omap f @^-1 Some y) = Some @: (f @^-1 y).
Proof.
  apply/setP => [[x|]] //=; rewrite !inE /= ?Some_eqE.
  - apply/idP/imsetP => E. exists x => //. by rewrite -mem_preim.
    case: E => x0 ? [->]. by rewrite mem_preim.
  - by apply/idP/imsetP => // [[?]] //.
Qed.

Lemma preim_omap_None (aT rT : finType) (f : aT -> rT) :
  (omap f @^-1 None) = [set None].
Proof. apply/setP => x. rewrite -mem_preim !inE. by case: x => [x|]. Qed.


(** *** Set image *)

Lemma inj_imset (aT rT : finType) (f : aT -> rT) (A : {set aT}) (x : aT) :
  injective f -> (f x \in f @: A) = (x \in A).
Proof.
  move=> f_inj; apply/imsetP/idP;
  [by case=> [y] ? /f_inj-> | by move=> ?; exists x].
Qed.

Lemma imset_pre_val (T : finType) (P : pred T) (s : subFinType P) (A : {set T}) :
  A \subset P -> val @: (val @^-1: A : {set s}) = A.
Proof.
  move=> /subsetP A_P. apply/setP=> x; apply/imsetP/idP.
  + case=> y; by rewrite inE => ? ->.
  + move=> x_A; by exists (Sub x (A_P x x_A)); rewrite ?inE SubK.
Qed.

Lemma imset_valT (T : finType) (P : pred T) (s : subFinType P) :
  val @: [set: s] = finset P.
Proof.
  apply/setP=> z; apply/imsetP/idP; rewrite inE.
  + case=> y _ ->; exact: (valP y).
  + move=> z_P; by exists (Sub z z_P); last rewrite SubK.
Qed.

Lemma memKset (T : finType) (A : {set T}) : finset (mem A) = A.
Proof. apply/setP=> x; by rewrite !inE. Qed.

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

Lemma pblock_eqvE (T : finType) (R : rel T) (D : {set T}) x y : 
  {in D & &, equivalence_rel R} ->
  y \in pblock (equivalence_partition R D) x -> [/\ x \in D, y \in D & R x y].
Proof. 
  move => eqv_R.
  move/equivalence_partitionP : (eqv_R) => /and3P [P1 P2 P3].
  rewrite /pblock /=. case: pickP => //=; last by rewrite inE.
  move => B /andP [B1 xB] yB.
  have H: {subset B <= D}. 
  { move => z zB. rewrite -(eqP P1). by apply/bigcupP; exists B. } 
  rewrite -(pblock_equivalence_partition eqv_R) ?H //. 
  rewrite -eq_pblock ?(def_pblock _ _ xB,def_pblock _ _ yB) //.
  by apply/bigcupP; exists B.
Qed.

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

(** Partitions possibly including the empty equivalence class *)
Definition pe_partition (T : finType) (P : {set {set T}}) (D : {set T}) :=
  (cover P == D) && (trivIset P).

Lemma trivIset3 (T : finType) (A B C : {set T}) : 
  [disjoint A & B] -> [disjoint B & C] -> [disjoint A & C] -> 
  trivIset [set A;B;C].
Proof. 
  move => D1 D2 D3. apply/trivIsetP => X Y. rewrite !inE -!orbA.
  do 2 (case/or3P => /eqP->); try by rewrite ?eqxx // 1?disjoint_sym. 
Qed.

(* foldr1 *)

Definition foldr1 (I R : Type) (x0 : R) (op : R -> R -> R) F  := 
  fix foldr1_rec (s : seq I) : R :=
    match s with
    | [::] => x0
    | a :: s' => if nilp s' then F a else op (F a) (foldr1_rec s')
    end.

Section Foldr1.
Variables (I R : Type) (op : R -> R -> R) (F : I -> R).


Lemma foldr1_set_default x0 x1 s : 
  ~~ nilp s -> foldr1 x0 op F s = foldr1 x1 op F s.
Proof. elim: s => //= a s. case: (nilp s) => //= IH. by rewrite IH. Qed.

End Foldr1.

(** Extra Morphism declatations *)

Require Import Setoid Morphisms.

Instance ex2_iff_morphism (A : Type) :  
  Proper (pointwise_relation A iff ==> pointwise_relation A iff ==> iff) (@ex2 A).
Proof. by firstorder. Qed.
