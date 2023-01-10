Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import edone.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Preliminaries *)

(** Use capitalized names for Coq.Relation_Definitions *)
(* Definition Symmetric := Relation_Definitions.symmetric. *)
(* Definition Transitive := Relation_Definitions.transitive. *)

(** *** Tactics *)

(** Coq treats axioms of type [False] specially: the [Print Asssumptions] command
prints the types that are inhabited by an (empty) case analysis on the
axiom. The alternative definition of [admit] below allows closing proofs that
contain admits by [Qed], leading to a more precise tracking of the "holes"
during proof development.

Of course, the axiom makes the global context inconsistent, making it necessary
to check final results using [Print Assumptions] to ensure the axiom is not
acually used. *)

(** The tactics below should be commented out in released and review versions. *)

(* Axiom admitted_case : False. *) 
(* Ltac admit := case admitted_case. *)

Ltac reflect_eq := 
  repeat match goal with [H : is_true (_ == _) |- _] => move/eqP : H => H end.
Ltac contrab := 
  match goal with 
    [H1 : is_true ?b, H2 : is_true (~~ ?b) |- _] => by rewrite H1 in H2
  end.
Tactic Notation "existsb" uconstr(x) := apply/existsP;exists x.

#[export]
Hint Extern 0 (injective Some) => exact: @Some_inj : core.

(** *** Σ-Types *)

Declare Scope sigT_scope.
Open Scope sigT_scope.

Notation "'Σ' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p%type)) ..))
  (at level 200, x binder, y binder, right associativity) : sigT_scope.

Notation "⟨ x , m ⟩" := (existT _ x m) : sigT_scope.

Lemma tagged_eq (T : eqType) (T_ : T -> eqType) (x : T) (u v : T_ x) : 
  (⟨ x , u ⟩ == ⟨ x , v ⟩) = (u == v).
Proof. by rewrite -tag_eqE/tag_eq/= eqxx tagged_asE. Qed.

Lemma tagged_eqF (T : eqType) (T_ : T -> eqType) (x y : T) (u : T_ x) (v : T_ y) : 
  x != y -> (⟨ x , u ⟩ == ⟨ y , v ⟩) = false.
Proof. by rewrite -tag_eqE/tag_eq/= => /negbTE ->. Qed.

(** *** Generic Trivialities *)

Lemma enum_sum (T1 T2 : finType) (p : pred (T1 + T2)) :
  enum p = 
  map inl (enum [pred i | p (inl i)]) ++ map inr (enum [pred i | p (inr i)]).
Proof.
by rewrite /enum_mem {1}unlock /= /sum_enum filter_cat !filter_map.
Qed.

Lemma enum_unit (p : pred unit) : enum p = filter p [:: tt].
Proof. by rewrite /enum_mem unlock. Qed.

(** usage: [rewrite [pat]rwT] replaces [pat] with [true] and creates [pat] as a subgoal *)
Definition rwT (b : bool) := @id (is_true b).
(** [rewrite [pat]rwF] replaces [pat] with [false] and creates [~~ pat] as a subgoal *)
Definition rwF := negbTE.

Lemma forall_imset (aT rT : finType) (f : aT -> rT) (p : {pred aT}) (q : {pred rT}) :
  [forall x in [set f z | z in p], q x] = [forall x in p, q (f x)].
Proof.
apply/forall_inP/forall_inP=>[allQ x xp|]; first by apply: allQ; rewrite imset_f.
by move => allQ ? /imsetP[z zp ->]; apply: allQ.
Qed.

Lemma forall2_imset (aT rT : finType) (f g : aT -> rT) (p : {pred aT}) (q : rel rT) :
  [forall x in [set f z | z in p], forall y in [set g z | z in p], q x y] = 
  [forall x in p, forall y in p, q (f x) (g y)].
Proof.
by rewrite forall_imset; under eq_forallb => y do rewrite forall_imset.
Qed.

Lemma eq_forall_in (T : finType) (A P1 P2 : {pred T}) : 
  {in A, P1 =1 P2} -> [forall x in A, P1 x] = [forall x in A, P2 x].
Proof. move=> eqP. apply/eq_forallb => x; case xA: (x \in A) => //=. exact: eqP. Qed.


Lemma insubdT (T : Type) (P : pred T) (sT : subType P) (d : sT) (x : T) (Px : P x) : 
  insubd d x = Sub x Px.
Proof. by rewrite /insubd insubT. Qed.

Section Val2.
Variables (T : Type) (P : pred T) (sT : subType P) (P' : pred sT) (sT' : subType P').
Definition val2 (x : sT') := val (val x).

Lemma val2_inj : injective val2.
Proof. by apply:inj_comp; apply: val_inj. Qed.
End Val2.
Prenex Implicits val2.

Variant xchoose_spec (T : choiceType) (P : pred T) (E : ex P) : T -> Prop :=
  XChosen x of P x : xchoose_spec E x.

Lemma xchooseP' (T : choiceType) (P : pred T) (E : ex P) : 
  xchoose_spec E (xchoose E).
Proof. constructor; exact: xchooseP. Qed.


Lemma exists_inPnn {T : finType} {D P : pred T} : 
  reflect (forall x : T, x \in D -> P x) (~~ [exists x in D, ~~ P x]).
Proof. 
rewrite negb_exists_in; under eq_forallb => ? do rewrite negbK.
exact: forall_inP.
Qed.

Lemma existsb_case (P : pred bool) : [exists b, P b] = P true || P false.
Proof. apply/existsP/idP => [[[|] -> //]|/orP[H|H]]; eexists; exact H. Qed.

Lemma all_cons (T : eqType) (P : T -> Prop) a (s : seq T) : 
  {in a::s, forall x, P x} <-> P a /\ {in s, forall x, P x}.
Proof.
split => [A|[A B]]; last by move => x /predU1P [-> //|]; apply: B.
by split => [|b Hb]; apply: A; rewrite !inE ?eqxx ?Hb. 
Qed.

Lemma cons_subset (T : eqType) (a:T) s1 (s2 : pred T) : 
  {subset a::s1 <= s2} <-> a \in s2 /\ {subset s1 <= s2}.
Proof. exact: all_cons. Qed.

Lemma subrelP (T : finType) (e1 e2 : rel T) : 
  reflect (subrel e1 e2) ([pred x | e1 x.1 x.2] \subset [pred x | e2 x.1 x.2]).
Proof. apply: (iffP subsetP) => [S x y /(S (x,y)) //|S [x y]]. exact: S. Qed.

Lemma eqb_negR (b1 b2 : bool) : (b1 == ~~ b2) = (b1 != b2).
Proof. by case: b1; case: b2. Qed.

Lemma orb_sum (a b : bool) : a || b -> (a + b)%type.
Proof. by case: a => /=; [left|right]. Qed.

(* should possibly be called [inj_leq] but that's aleady used *)
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

Lemma valK' (T : Type) (P : pred T) (sT : subType P) (x : sT) (p : P (val x)) : 
  Sub (val x) p = x.
Proof. apply: val_inj. by rewrite SubK. Qed.

Lemma inl_inj (A B : Type) : injective (@inl A B).
Proof. by move => a b []. Qed.

Lemma inr_inj (A B : Type) : injective (@inr A B).
Proof. by move => a b []. Qed.

Lemma inr_codom_inl (T1 T2 : finType) x : inr x \in codom (@inl T1 T2) = false.
Proof. apply/negbTE/negP. by case/mapP. Qed.

Lemma inl_codom_inr (T1 T2 : finType) x : inl x \in codom (@inr T1 T2) = false.
Proof. apply/negbTE/negP. by case/mapP. Qed.

Lemma Some_eqE (T : eqType) (x y : T) : (Some x == Some y) = (x == y).
Proof. exact: inj_eq. Qed.

Lemma inl_eqE (A B : eqType) x y : (@inl A B x == @inl A B y) = (x == y).
Proof. exact/inj_eq/inl_inj. Qed.

Lemma inr_eqE (A B : eqType) x y : (@inr A B x == @inr A B y) = (x == y).
Proof. exact/inj_eq/inr_inj. Qed. 

Definition sum_eqE := (inl_eqE,inr_eqE).

Lemma sum_nat_mulnr [I : finType] (A : pred I) (n : nat) (F : I -> nat) :
  (n * \sum_(i in A) F i)%N = \sum_(i in A) n * F i.
Proof.
by elim/big_ind2 : _ => // [|? m1 ? m2 <- <-]; rewrite ?muln0 ?mulnDr.
Qed.

Lemma sum_cardI (T : finType) (A B : {set T}): 
  \sum_(x in A) (x \in B) = #|A :&: B|.
Proof. 
rewrite -sum1_card; under [RHS]eq_bigl do rewrite inE.
by rewrite [RHS]big_mkcondr /=; apply: eq_bigr => i _; case: (_ \in _).
Qed.

Lemma sum_cond1 (I : finType) (r : seq I) (P Q : I -> bool) : 
  \sum_(x <- r | Q x ) P x = \sum_(x <- r | Q x && P x) 1.
Proof.
by rewrite [RHS]big_mkcondr; apply: eq_bigr => x _; case: (P x).
Qed.

Lemma card_gtnE (T : finType) n (p : {pred T}) : n < #|p| -> { x | x \in p }.
Proof. by move=> n_p; apply/sigW/card_gt0P; apply: leq_trans n_p. Qed.

(** getting the "n-th element" of a set of ordinals *)
(** TOTHINK: generalize ot aribtaryy ordered types? *)
Lemma nth_ord (k n : nat) (A : {set 'I_k}) : 
  n < #|A| -> { i : 'I_k | i \in A & #|[set j in A | j < i]| = n}.
Proof.
elim: n A => [|n IHn] A ltA; have [/= i0 i0A] := card_gtnE ltA.
- pose i := [arg min_(i < i0 | i \in A) i].
  exists i; rewrite /i; case: arg_minnP => // j jA min_j. apply/eq_card0 => o.
  by rewrite !inE; apply: contraTF isT => /andP[oA]; rewrite ltnNge min_j.
- pose i := [arg min_(i < i0 | i \in A) i].
  have [iA min_i] : i \in A /\ forall j, j \in A -> i <= j by rewrite /i; case: arg_minnP.
  rewrite (cardsD1 i) iA add1n ltnS in ltA. 
  have [j /setD1P [jDi jA] <-] := IHn _ ltA.
  exists j; rewrite // [in LHS](cardsD1 i) inE iA ltn_neqAle eq_sym jDi min_i //=.
  by rewrite add1n; congr (_.+1); apply/eq_card => o; rewrite !inE -andbA eq_sym.
Qed.

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

Lemma bigmax_leq_pointwise (I :finType) (P : pred I) (F G : I -> nat) :
  {in P, forall x, F x <= G x} -> \max_(i | P i) F i <= \max_(i | P i) G i.
Proof.
move => ?. elim/big_ind2 : _ => // y1 y2 x1 x2 A B.
by rewrite geq_max !leq_max A B orbT.
Qed.

Lemma set1_inj (T : finType) : injective (@set1 T).
Proof. move => x y /setP /(_ y). by rewrite !inE eqxx => /eqP. Qed.

Lemma id_bij T : bijective (@id T).
Proof. exact: (Bijective (g := id)). Qed.

Lemma card_ltnT (T : finType) (p : pred T) x : ~~ p x -> #|p| < #|T|.
Proof. 
  move => A. apply/proper_card. rewrite properE. 
  apply/andP; split; first by apply/subsetP.
  apply/subsetPn. by exists x. 
Qed.

Lemma leq_cardsD1 (T : finType) (a : T) (A : {set T}) : #|A|.-1 <= #|A :\ a|.
Proof. by rewrite (cardsD1 a); case: (a \in A); case: (#|_|). Qed.


Lemma setE (T : finType) (A : {set T}) : [set x in A] = A.
Proof. by apply/setP => ?; rewrite inE. Qed.

Lemma setDK (T : finType) (A B : {set T}) : B \subset A -> (A :\: B :|: B) = A.
Proof. 
by move => subBA; rewrite setDE setUIl (setUidPl subBA) setUC setUCr setIT.
Qed.

(* what's a good name? *)
Lemma setUUC (T : finType) (A B : {set T}) : (A :|: B) :&: (~: A :|: B) = B.
Proof. by apply/setP => z; rewrite !inE; case: (z \in A). Qed.

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
  have/inj_card_onto : injective f' by move => x1 x2 []; exact: f_inj.
  case/(_ _ (Sub y yP))/Wrap => [|/codomP[x]]; first by rewrite card_sig E.
  by move/(congr1 val) => /= ->; exact: codom_f.
Qed.

(** TODO: check whether the collection of lemmas on sets/predicates
and their cardinalities can be simplified *)

Lemma cards3 (T : finType) (a b c : T) : #|[set a;b;c]| <= 3.
Proof. by rewrite -setUA cardsU1 cards2; case:  (_ \in _); case (_ == _). Qed.

Lemma eq_set1P (T : finType) (A : {set T}) (x : T) : 
  reflect (x \in A /\ {in A, all_equal_to x}) (A == [set x]).
Proof.
apply: (iffP eqP) => [->|]; first by rewrite !in_set1; by split => // y /set1P.
case => H1 H2. apply/setP => y. apply/idP/set1P;[exact: H2| by move ->].
Qed.

Lemma setN01E (T : finType) A (x:T) : 
  A != set0 -> A != [set x] -> exists2 y, y \in A & y != x.
Proof.
case/set0Pn => y Hy H1; apply/exists_inP.
apply: contraNT H1 => /exists_inPn => H; apply/eq_set1P.
suff S: {in A, all_equal_to x} by rewrite -{1}(S y).
by move => z /H /negPn/eqP.
Qed.

Lemma sub_filter (T : eqType) (p : {pred T}) (s : seq T) : 
  {subset [seq x <- s | p x] <= s}.
Proof. by move=> x; rewrite mem_filter => /andP[_ ->]. Qed.

Lemma sub_filter_cond (T : eqType) (p : {pred T}) (s : seq T) : 
  {subset [seq x <- s | p x] <= p}.
Proof. by move=> x; rewrite mem_filter => /andP[? _]. Qed.

Lemma subseq_of_subset (T : finType) (A : pred T) (s : seq T) n : 
  uniq s -> {subset A <= s} -> n <= #|A| -> 
  exists p : seq T, [/\ {subset p <= A}, size p = n & subseq p s].
Proof.
move => uniq_s subAs leq_n_A; exists (take n [seq x <- s | x \in A]); split.
- by move=> x /mem_take; rewrite mem_filter => /andP[->].
- rewrite size_takel // -(card_uniqP _) ?filter_uniq //.
  apply: leq_trans leq_n_A _; apply/subset_leq_card/subsetP => x x_A.
  by rewrite mem_filter x_A subAs.
- apply: subseq_trans (take_subseq _ _) _. exact: filter_subseq.
Qed.

Lemma bigcup_set1 (T I : finType) (i0 : I) (F : I -> {set T}) :
  \bigcup_(i in [set i0]) F i = F i0.
Proof. by rewrite (big_pred1 i0) // => i; rewrite inE. Qed.

(** usage: [elim/(size_ind f) : x] *)
Lemma size_ind (X : Type) (f : X -> nat) (P : X -> Type) : 
  (forall x, (forall y, (f y < f x) -> P y) -> P x) -> forall x, P x.
Proof.
move => ind x; have [n] := ubnP (f x); elim: n x => // n IHn x le_n. 
apply: ind => y f_y_x; apply: IHn; exact: leq_trans f_y_x _.
Qed.
Arguments size_ind [X] f [P].

Ltac eqxx := match goal with
             | [ H : is_true (?x != ?x) |- _ ] => by rewrite eqxx in H
             end.

(** use tactics in terms to obtain the argument type when doing
induction on the size of something (e.g., a type, set, or
predicate). This works since at the time where [elim/V] evaluates [V],
the last assumption is [_top_assumption_ : T] with [T] being the type of
the variable one want's to do induction on. Usage: [elim/card_ind] *)
Notation card_ind := 
  (size_ind (fun x : (ltac:(match goal with  [ _ : ?X |- _ ] => exact X end)) => #|x|))
  (only parsing). 

(* TOTHINK: is there a [card_ind] LEMMA that does not require manual
instantiation or Ltac trickery?  The following works for [pred T] but
not for [{set T}]. *)
(*
Lemma card_ind' (T : finType) (pT : predType T) (P : pT -> Type) : 
  (forall x : pT, (forall y : pT, (#|y| < #|x|) -> P y) -> P x) -> forall x : pT, P x. 
Proof. exact: size_ind. Qed. 
*)

Lemma proper_ind (T: finType) (P : pred T  -> Type) : 
  (forall A : pred T, (forall B : pred T, B \proper A -> P B) -> P A) -> forall A, P A.
Proof. 
move => ind; elim/card_ind => A IH.
apply: ind => B /proper_card; exact: IH.
Qed.

Lemma propers_ind (T: finType) (P : {set T} -> Type) : 
  (forall A : {set T}, (forall B : {set T}, B \proper A -> P B) -> P A) -> forall A, P A.
Proof.
move => ind; elim/card_ind => A IH.
apply: ind => B /proper_card; exact: IH.
Qed.


Section Smallest.

Variables (T : finType).
Implicit Types (P : {set T} -> Prop) (p : {set T} -> bool) (U V : {set T}).

Definition smallest P U := P U /\ forall V : {set T}, P V -> #|U| <= #|V|.
Definition largest P U := P U /\ forall V : {set T}, P V -> #|V| <= #|U|.

Lemma below_smallest P U V : smallest P U -> #|V| < #|U| -> ~ P V.
Proof. move => [_ small_U]; rewrite ltnNge; exact/contraNnot/small_U. Qed.

Lemma above_largest P U V : largest P U -> #|V| > #|U| -> ~ P V.
Proof. move => [_ large_U]. rewrite ltnNge; exact/contraNnot/large_U. Qed.

Variables (P : {set T} -> Prop) (p : {set T} -> bool).
Hypothesis PP : forall x, reflect (P x) (p x). 

Lemma smallestPP A : smallest P A <-> smallest p A.
Proof. by split => -[/PP ? H]; split => // ? /PP; apply: H. Qed.

Lemma argmin_smallest A : p A -> smallest p [arg min_(B < A | p B) #|B|].
Proof. by move=> pA; case: arg_minnP. Qed.

Lemma ex_smallest A : P A -> exists B, smallest P B.
Proof. 
move=> /PP PA. exists [arg min_(B < A | p B) #|B|].
exact/smallestPP/argmin_smallest.
Qed.

End Smallest.

Lemma sub_in2W (T1 : predArgType) (D1 D2 D1' D2' : pred T1) (P1 : T1 -> T1 -> Prop) :
 {subset D1 <= D1'} -> {subset D2 <= D2'} -> 
 {in D1' & D2', forall x y : T1, P1 x y} -> {in D1&D2, forall x y: T1, P1 x y}.
Proof. firstorder. Qed.

Definition restrict_mem (T:Type) (A : mem_pred T) (e : rel T) := 
  [rel u v | (in_mem u A) && (in_mem v A) && e u v].
Notation restrict A := (restrict_mem (mem A)).

Lemma sub_restrict (T : Type) (e : rel T) (a : pred T) : 
  subrel (restrict a e) e.
Proof. move => x y /=. by do 2 case: (_ \in a). Qed.

Lemma restrict_mono (T : Type) (A B : {pred T}) (e : rel T) : 
  {subset A <= B} -> subrel (restrict A e) (restrict B e).
Proof. move => H x y /= => /andP [/andP [H1 H2] ->]. by rewrite !H. Qed.

Lemma restrict_irrefl (T : Type) (e : rel T) (A : pred T) : 
  irreflexive e -> irreflexive (restrict A e).
Proof. move => irr_e x /=. by rewrite irr_e. Qed.

Lemma restrict_sym (T : Type) (A : pred T) (e : rel T) : 
  symmetric e -> symmetric (restrict A e).
Proof. move => sym_e x y /=. by rewrite sym_e [(x \in A) && _]andbC. Qed.


Notation vfun := (fun x: void => match x with end).  
Notation rel0 := [rel _ _ | false].
Definition surjective (aT : finType) (rT : eqType) (f : aT -> rT) := forall x, x \in codom f.

Fact rel0_irrefl {T:Type} : @irreflexive T rel0.
Proof. done. Qed.

Fact rel0_sym {T:Type} : @symmetric T rel0.
Proof. done. Qed.

Lemma relU_sym' (T : Type) (e e' : rel T) :
  symmetric e -> symmetric e' -> symmetric (relU e e').
Proof. move => sym_e sym_e' x y /=. by rewrite sym_e sym_e'. Qed.

Lemma codom_Some (T : finType) (s : seq (option T)) : 
  None \notin s -> {subset s <= codom Some}.
Proof. move => A [a|] B; by [rewrite codom_f|contrab]. Qed.

(** Unlike Logic.unique, the following does not actually require existence *)
Definition unique X (P : X -> Prop) := forall x y, P x -> P y -> x = y.

Lemma empty_uniqe X (P : X -> Prop) : (forall x, ~ P x) -> unique P.
Proof. firstorder. Qed.

(** *** Disjointness *)

(* Lemma in mathcomp-1.12 has [A : {set T}] *)
Lemma disjoints1 (T : finType) (A : {pred T}) x : 
  [disjoint [set x] & A] = (x \notin A).
Proof. by rewrite (@eq_disjoint1 _ x) // => y; rewrite !inE. Qed.

Lemma disjoints0 (T : finType) (A : {pred T}) : [disjoint set0 & A].
Proof. by apply/pred0Pn => -[x /=]; rewrite inE. Qed.

Lemma disjointP (T : finType) (A B : pred T):
  reflect (forall x, x \in A -> x \in B -> False) [disjoint A & B].
Proof. by rewrite disjoint_subset; apply:(iffP subsetP) => H x; move/H/negP. Qed.
Arguments disjointP {T A B}.

Definition disjointE (T : finType) (A B : pred T) (x : T) 
  (D : [disjoint A & B]) (xA : x \in A) (xB : x \in B) := disjointP D _ xA xB.

Lemma disjointsU (T : finType) (A B C : {set T}):
  [disjoint A & C] -> [disjoint B & C] -> [disjoint A :|: B & C].
Proof.
  move => a b. 
  apply/disjointP => x /setUP[]; by move: x; apply/disjointP.
Qed.

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

Lemma eq_in_pmap (aT : eqType) rT (f1 f2 : aT -> option rT) (s : seq aT) : 
  {in s, f1 =1 f2} -> pmap f1 s = pmap f2 s.
Proof.
by elim: s => // a s IHs /all_cons [eq_a eq_s]; rewrite /= eq_a (IHs eq_s).
Qed.

(** Variants of [splitP] and [splitPr] that remembers that provides
the information that the split is performed at the first occurrence. *)
Section SplitPlus.
Variables (n0 : nat) (T : eqType).
Implicit Type p : seq T.

Variant split x : seq T -> seq T -> seq T -> Type :=
  Split p1 p2 of x \notin p1 : split x (rcons p1 x ++ p2) p1 p2.

Lemma splitP p x (i := index x p) :
  x \in p -> split x p (take i p) (drop i.+1 p).
Proof. 
rewrite -has_pred1 => /split_find[? ? ? /eqP->]. 
by rewrite has_pred1; constructor. 
Qed.

Variant splitr x : seq T -> Type :=
  Splitr p1 p2 of x \notin p1 : splitr x (p1 ++ x :: p2).

Lemma splitPr p x : x \in p -> splitr x p.
Proof. by case/splitP=> p1 p2; rewrite cat_rcons. Qed.
End SplitPlus.

Lemma tnth_uniq (T : eqType) n (t : n.-tuple T) (i j : 'I_n) : 
  uniq t -> (tnth t i == tnth t j) = (i == j).
Proof. 
  move => uniq_t. 
  rewrite /tnth (set_nth_default (tnth_default t j)) ?size_tuple ?ltn_ord //. 
  by rewrite nth_uniq // size_tuple ltn_ord.
Qed.

Lemma mem_tail (T : eqType) (x y : T) s : y \in s -> y \in x :: s.
Proof. by rewrite inE => ->. Qed.
Arguments mem_tail [T] x [y s].

Lemma in_set_seq (T : finType) (s : seq T) : [set z in s] =i s.
Proof. by move=> z; rewrite inE. Qed.
  
(* inline? *)
Lemma subset_seqR (T : finType) (A : pred T) (s : seq T) : 
  (A \subset s) = (A \subset [set x in s]).
Proof. by rewrite (eq_subset_r (in_set_seq _)). Qed.

Lemma subset_seqL (T : finType) (A : pred T) (s : seq T) : 
  (s \subset A) = ([set x in s] \subset A).
Proof. by rewrite (eq_subset (in_set_seq _)). Qed.

Lemma mem_catD (T:finType) (x:T) (s1 s2 : seq T) : 
  [disjoint s1 & s2] -> (x \in s1 ++ s2) = (x \in s1) (+) (x \in s2).
Proof. 
  move => D. rewrite mem_cat. case C1 : (x \in s1) => //=. 
  symmetry. apply/negP. exact: disjointE D _.
Qed.
Arguments mem_catD [T x s1 s2].

Lemma rpath_sub (T : eqType) (e : rel T) (a : pred T) x p : 
  path (restrict a e) x p -> {subset p <= a}.
Proof.
  elim: p x => //= b p IH x. rewrite -!andbA => /and4P[H1 H2 H3 H4].
  apply/cons_subset. by split; eauto.
Qed.

Lemma closed_path_sub (T : eqType) (e : rel T) (x : T) (s : seq T) (p : {pred T}) :
  (forall z y, e z y -> p z -> p y) -> p x -> path e x s -> {subset s <= p}.
Proof.
move => cl_p; elim: s x => //= y s IHs x /cl_p py /andP[e_xy pth_p]. 
apply/all_cons; split; by [apply: py |apply: IHs (py _ _) pth_p].
Qed.

Lemma path_rpath (T : eqType) (e : rel T) (A : pred T) x p :
  path e x p -> x \in A -> {subset p <= A} -> path (restrict A e) x p.
Proof.
  elim: p x => [//|a p IH] x /= /andP[-> pth_p] -> /cons_subset [Ha ?] /=.
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

Lemma last_mem (T : eqType) (x : T) (s : seq T) : 
  x \in s -> last x s \in s.
Proof. 
by elim/last_ind: s => // s y _ _; rewrite last_rcons mem_rcons mem_head.
Qed.

Lemma last_belast_eq (T : Type) (x : T) p q : 
  last x p = last x q  -> belast x p = belast x q -> p = q.
Proof. 
  elim/last_ind : p => [|p a _]; elim/last_ind : q => [|q b _] //=; 
    try by rewrite belast_rcons => ?.
  rewrite !belast_rcons !last_rcons => ?. congruence.
Qed.

Lemma lift_path (aT : finType) (rT : eqType) (e : rel aT) (e' : rel rT) (f : aT -> rT) a p' : 
  (forall x y, f x \in f a :: p' -> f y \in f a :: p' -> e' (f x) (f y) -> e x y) ->
  path e' (f a) p' -> {subset p' <= codom f} -> exists p, path e a p /\ map f p = p'.
Proof.
  move => f_inv.
  elim: p' a f_inv => /= [|fb p' IH a H /andP[A B] /cons_subset[S1 S2]]; first by exists [::].
  case: (codomP S1) => b E. subst. case: (IH b) => // => [x y Hx Hy|p [] *]. 
  - by apply: H; rewrite inE ?Hx ?Hy.
  - exists (b::p) => /=. suff: e a b by move -> ; subst. by rewrite H ?inE ?eqxx.
Qed.

Lemma mem_bigcup (T1 T2 : finType) (F : T1 -> {set T2}) (P : pred T1) z y : 
  P y -> z \in F y -> z \in \bigcup_(x | P x) F x.
Proof. move => Py zF. by apply/bigcupP; exists y; rewrite ?yA. Qed.
Arguments mem_bigcup [T1 T2 F P z] y _ _.


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
Proof. apply: connect_mono. exact: sub_restrict. Qed.

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

Lemma connect_restrictP (T : finType) (e : rel T) (A : pred T) x y (xDy : x != y) :
  reflect (exists p, [/\ path e x p, last x p = y, uniq (x::p) & {subset x::p <= A}])
          (connect (restrict A e) x y).
Proof.
apply: (iffP connectUP) => [[p] [rpth_p lst_p uniq_p]|[p] [rpth_p lst_p uniq_p sub_p]].
- exists p. rewrite (sub_path _ rpth_p); first split => //; last exact: sub_restrict.
  apply/cons_subset; split; last exact: rpath_sub rpth_p.
  case: p rpth_p lst_p {uniq_p} => /= [_ /eqP E|]; by [rewrite E in xDy| case: (x \in A)].
- by exists p; case/cons_subset : sub_p => ? ?; rewrite path_rpath.
Qed.
Arguments connect_restrictP {T e A x y _}.

Lemma connect_symI (T : finType) (e : rel T) : symmetric e -> connect_sym e.
Proof.
move => sym_e; suff S x y : connect e x y -> connect e y x.
  move => x y. apply/idP/idP; exact: S.
case/connectP => p; elim: p x y => /= [x y _ -> //|z p IH x y /andP [A B] C].
rewrite sym_e in A; apply: connect_trans (connect1 A); exact: IH.
Qed.

Lemma equivalence_rel_of_sym (T : finType) (e : rel T) :
  symmetric e -> equivalence_rel (connect e).
Proof. 
  move => sym_e x y z. split => // A. apply/idP/idP; last exact: connect_trans.
  rewrite connect_symI // in A. exact: connect_trans A.
Qed.

Lemma homo_connect (aT rT : finType) (e : rel aT) (e' : rel rT) (f : aT -> rT) a b :
  {homo f : x y / e x y >-> e' x y} -> connect e a b -> connect e' (f a) (f b).
Proof. 
move => hom_f; case/connectP => p p1 p2; apply/connectP.
exists (map f p); by [exact: homo_path p1|rewrite last_map -p2].
Qed.

Lemma eq_connect_sym (T : finType) (e e' : rel T) : 
  e =2 e' -> connect_sym e -> connect_sym e'.
Proof. by move=> eq_e sym_e x y; rewrite -!(eq_connect eq_e). Qed.

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
  - by apply: homo_connect => {x y} x y /=; rewrite !hE.
  - rewrite -{2}(hK x) -{2}(hK y).
    by apply: homo_connect => {x y} x y /=; rewrite !hE !hinvK.
Qed.

#[export]
Hint Resolve Some_inj inl_inj inr_inj : core.


(** *** Set preimage *)

Notation "f @^-1 x" := (preimset f (mem (pred1 x))) (at level 24) : set_scope.  

Lemma mem_preim (aT rT : finType) (f : aT -> rT) x y : 
  (f x == y) = (x \in f @^-1 y).
Proof. by rewrite !inE. Qed.

Lemma can_preimset (aT rT : finType) (f : aT -> rT) (A : {set rT}) : 
  A \subset codom f -> [set f x | x in f @^-1: A] = A.
Proof. 
move/subsetP => subAi; apply/setP => z; apply/imsetP/idP => [[x]|zA].
  by rewrite inE => ? ->.
by exists (iinv (subAi _ zA)); rewrite ?inE f_iinv.
Qed.
Arguments can_preimset [aT rT] f [A] _.

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

Lemma imset_inj (aT rT : finType) (f : aT -> rT) : 
  injective f -> injective (fun A : {set aT} => f @: A).
Proof.
move=> inj_f A B eq_AB; apply/setP => x.
by rewrite -(mem_imset _ _ inj_f) eq_AB mem_imset.
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

Lemma imset_codom (aT rT : finType) (f : aT -> rT) (A : {set aT}) : 
  [set f x | x in A] \subset codom f.
Proof. apply/subsetP => ? /imsetP[x xA ->]; exact: codom_f. Qed.

Lemma memKset (T : finType) (A : {set T}) : finset (mem A) = A.
Proof. apply/setP=> x; by rewrite !inE. Qed.

Lemma inj_card_preimset (aT rT : finType) (f : aT -> rT) (A : {set rT}) : 
  injective f -> A \subset codom f -> #|f @^-1: A| = #|A|.
Proof. 
move=> inj_f /subsetP => subAf.
have [->|[y yA]] := set_0Vmem A; first by rewrite preimset0 !cards0.
have x0 : aT := (iinv (subAf _ yA)).
pose g (x : rT) : aT := if @idP (x \in codom f) is ReflectT p then iinv p else x0.
apply: on_card_preimset; exists g. 
- by move => x /subAf; rewrite /g; case E : {1}_ / idP; rewrite // iinv_f.
- by move => x /subAf; rewrite /g; case E : {1}_ / idP; rewrite // f_iinv.
Qed.

Lemma inj_imsetS (aT rT : finType) (f : aT -> rT) (A B : {pred aT}) : 
  injective f -> (f @: A \subset f @: B) = (A \subset B).
Proof.
move=> inj_f; apply/subsetP/subsetP => [/= subAB x xA|subAB ? /imsetP[x xA ->]]. 
  by move: (subAB (f x)); rewrite !(mem_imset _ _ inj_f); apply.
by rewrite (mem_imset _ _ inj_f); apply: subAB.
Qed.

Lemma val_subset (T: finType) (H : {set T}) (A B : {set sig [eta mem H]}) :
  (val @: A \subset val @: B) = (A \subset B).
Proof. by rewrite inj_imsetS //; exact: val_inj. Qed.

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
  move => H /eqP <- ->. by rewrite imset_f. 
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

(** Extra Morphism declatations *)

#[export]
Instance ex2_iff_morphism (A : Type) :  
  Proper (pointwise_relation A iff ==> pointwise_relation A iff ==> iff) (@ex2 A).
Proof. by firstorder. Qed.

(** *** Extra Preliminaries used in Domination Theory *)

Section Preliminaries_dom.

Lemma properC (T : finType) (A B : {set T}) : A \proper B = (~: B \proper ~: A).
Proof. rewrite !properEneq setCS [~: _ == _]inj_eq 1?eq_sym //; exact/inv_inj/setCK. Qed.

Lemma in11_in2 (T1 T2 : predArgType) (P : T1 -> T2 -> Prop) (A1 : {pred T1}) (A2 : {pred T2}) : 
  {in A1, forall x, {in A2, forall y,  P x y}} <-> {in A1 & A2, forall x y, P x y}.
Proof. by firstorder. Qed.

Lemma eq_extremum (T : eqType) (I : finType) r x0 (p1 p2 : pred I) (F1 F2 : I -> T) : 
  p1 =1 p2 -> F1 =1 F2 -> extremum r x0 p1 F1 = extremum r x0 p2 F2.
Proof.
move=> eq_p eq_F; rewrite /extremum; apply/f_equal/eq_pick => x.
by rewrite !inE eq_p; under eq_forallb => i do rewrite !eq_p !eq_F.
Qed.

Lemma eq_arg_min (I : finType) (x : I) (p1 p2 : pred I) (w1 w2 : I -> nat) :
  p1 =1 p2 -> w1 =1 w2 -> arg_min x p1 w1 = arg_min x p2 w2.
Proof. exact: eq_extremum. Qed.

Lemma eq_arg_max (I : finType) (x : I) (p1 p2 : pred I) (w1 w2 : I -> nat) :
  p1 =1 p2 -> w1 =1 w2 -> arg_max x p1 w1 = arg_max x p2 w2.
Proof. exact: eq_extremum. Qed.

Variable T : finType.

Proposition maxset_properP (p : pred {set T}) (D : {set T}) :
  reflect (p D /\ (forall F : {set T}, D \proper F -> ~~ p F)) (maxset p D).
Proof.
  apply: (iffP maxsetP) => -[pD maxD]; split => // E.
  - rewrite properEneq => /andP [DnE DsubE].
    apply: contra_neqN DnE => pE; exact/esym/maxD.
  - move => pE SsubE; apply: contraTeq pE => EnD; apply: maxD.
    by rewrite properEneq eq_sym EnD.
Qed.

Proposition minset_properP (p : pred {set T}) (D : {set T}) :
  reflect (p D /\ (forall F : {set T}, F \proper D -> ~~ p F)) (minset p D).
Proof.
  rewrite minmaxset; apply (iffP (maxset_properP _ _)).
  all: rewrite /= setCK => -[pD H]; split => // E.
  all: by rewrite properC ?setCK => /H; rewrite ?setCK.
Qed.

(* not used *)
Lemma largest_maxset (p : pred {set T}) (A : {set T}) :
  largest p A -> maxset p A.
Proof.
  move => [pA maxA]. apply/maxset_properP; split => // B /proper_card; rewrite ltnNge.
  exact/contraNN/maxA.
Qed.

(* not used *)
Lemma smallest_minset (p : pred {set T}) (A : {set T}) : 
  smallest p A -> minset p A.
Proof.
  move => [pA minA]. apply/minset_properP; split => // B /proper_card; rewrite ltnNge.
  exact/contraNN/minA.
Qed.

Lemma doubleton_eq_left (u v w : T) : [set u; v] = [set u; w] <-> v = w.
Proof.
  rewrite /iff ; split ; last by move->.
  apply: contra_eq => vDw; apply/eqP/setP.
  case: (eqVneq v u) => [?|vDu]; subst.
  - by move/(_ w); rewrite !inE eqxx [_ == u]eq_sym (negbTE vDw).
  - by move/(_ v); rewrite !inE eqxx (negbTE vDw) (negbTE vDu).
Qed.

Lemma doubleton_eq_right (u v w : T) : [set u; w] = [set v; w] <-> u = v.
Proof. rewrite ![[set _;w]]setUC; exact: doubleton_eq_left. Qed.

Lemma doubleton_eq_iff (u v w x : T) : [set u; v] = [set w; x] <->
  ((u = w /\ v = x) \/ (u = x /\ v = w)).
Proof.
  split ; last by case => -[-> ->] //; rewrite setUC.
  move=> E; case: (eqVneq u w) => [?|uDw]; subst.
    left; split => //. by move/doubleton_eq_left : E.
  have ? : u = x; subst.
  { move/setP/(_ u) : E. rewrite !inE !eqxx (negbTE uDw) /=.
    by move/esym/eqP. }
  right; split => //. rewrite [RHS]setUC in E.
  by move/doubleton_eq_left : E.
Qed.

End Preliminaries_dom.

Arguments in11_in2 [T1 T2 P] A1 A2.
Arguments maxset_properP {T p D}.
Arguments minset_properP {T p D}.


(** *** Extra Preliminaries from Kuratowski/Wagner development *)

#[export] Hint Extern 0 (injective val) => exact val_inj : core.
#[export] Hint Extern 0 (injective sval) => exact val_inj : core.

Lemma in_setP (T : finType) (p : {pred T}) (x : T) : 
  reflect (p x) (x \in [set y | p y]).
Proof. rewrite inE; exact: idP. Qed.

Lemma Sub_imset (T : finType) (P : {pred T}) (s : subFinType P) {A : {set s}} (x : T) (Px : P x) :
  (Sub x Px \in A) = (x \in val @: A).
Proof. by rewrite -[X in X \in val @: _](SubK s Px) mem_imset. Qed.

Lemma Sub_map (T : eqType) (P : {pred T}) (s : subType P) {A : seq s} (x : T) (Px : P x) :
  (Sub x Px \in A) = (x \in map val A).
Proof. by rewrite -[X in X \in map val _](SubK s Px) mem_map. Qed.


Section AltE.
Variables (T rT : Type) (p : pred T) (x : T) (fT : p x -> rT) (fF : ~~ p x -> rT).

Lemma altT (px : p x) :
  match boolP (p x) with AltTrue b => fT b | AltFalse b => fF b end = fT px.
Proof.
case: {-}_ /boolP => -px'; last by case:notF; rewrite px in px'.
by rewrite (bool_irrelevance px' px).
Qed.

Lemma altF (px : ~~ p x) :
  match boolP (p x) with AltTrue b => fT b | AltFalse b => fF b end = fF px.
Proof.
case: {-}_ /boolP => -px'; first by case:notF; rewrite px' in px.
by rewrite (bool_irrelevance px' px).
Qed.
End AltE.

Arguments card_gt0P {T A}.  

(**The following two lemmas are adapted from their [face] instances in [revsnip.v]. *)
(* TODO: move to preliminaries/mathcomp *)
Lemma fcard0P (T : finType) (A : pred T) f :
  injective f -> fclosed f A -> reflect (exists x, x \in A) (0 < fcard f A).
Proof.
move => injf clfA.
apply: (iffP card_gt0P) => [[x /andP[]]|[x xA]]; first by exists x.
exists (froot f x); rewrite inE roots_root /=; last exact: fconnect_sym.
by rewrite -(closed_connect clfA (connect_root _ x)).
Qed.

Lemma fcard1P (T : finType) (A : pred T) f :
  injective f -> fclosed f A ->
  reflect (exists2 x, x \in A & exists2 y, y \in A & ~~ fconnect f x y)
          (1 < fcard f A).
Proof.
move=> inj_f clAf; pose cfC := fconnect_sym inj_f.
apply: (iffP card_gt1P) => [|[x xA [y yA not_xfy]]]. 
  move => [x] [y] [/andP [/= rfx xA]] /andP[/= rfy yA] xDy.
  by exists x; try exists y; rewrite // -root_connect // (eqP rfx) (eqP rfy).
exists (froot f x), (froot f y); rewrite !inE !roots_root ?root_connect //=.
by split => //; rewrite -(closed_connect clAf (connect_root _ _)).
Qed.

Lemma index_inj (T : eqType) (s : seq T) : {in s &, injective (index^~ s)}.
Proof. by move => u v u_s v_s E; rewrite -[u](nth_index u u_s) E nth_index. Qed.


Section Closure.
Variables (T : finType).
Implicit Types (e : rel T) (a : pred T) (x y : T).

Lemma closureP e a y : 
  reflect (exists2 x, x \in a & connect e y x) (y \in closure e a).
Proof. 
rewrite /closure_mem unfold_in disjoint_sym.
by apply: (iffP pred0Pn) => [[x] /andP[? ?]|[x]]; exists x.
Qed.

Lemma closure_connect e a x y : connect e x y -> y \in closure e a -> x \in closure e a.
Proof. 
move => e_xy /closureP [z z_a c_yz]; apply/closureP ; exists z => //. 
exact: connect_trans c_yz. 
Qed.

Lemma eq_closure e e' a : connect e =2 connect e' -> closure e a =i closure e' a.
Proof.
by move => eq_e z; apply/closureP/closureP => -[x ?]; exists x => //; rewrite ?eq_e // -eq_e.
Qed.

Lemma eq_closure_r e a a': a =i a' -> closure e a =i closure e a'.
Proof. by move => eq_a y; apply/closureP/closureP => -[x ?]; exists x; rewrite // ?eq_a // -eq_a. Qed.

Lemma eq_fclosure (f f' : T -> T) a : f =1 f' -> fclosure f a =i fclosure f' a.
Proof. move => eq_f; apply: eq_closure. exact: eq_fconnect. Qed.

Lemma eq_closed (e e' : rel T) (a : {pred T}) : 
  e =2 e' -> closed e a <-> closed e' a.
Proof. 
rewrite /closed_mem => eq_e. 
by split => cl x y; [rewrite -eq_e|rewrite eq_e]; apply: cl.
Qed.

Lemma eq_closed_r (e : rel T) (a b : {pred T}) : 
  a =i b -> closed e a <-> closed e b.
Proof. 
by rewrite /closed_mem => ab; split => -cl x y /cl; rewrite !ab.
Qed.

Lemma predD_closed (e : rel T) (a b : {pred T}) : 
  connect_sym e -> closed e a -> closed e b -> closed e [predD a & b].
Proof.
move=> sym_e cl_a cl_b; apply: intro_closed => // x y xy.
by rewrite !inE (cl_a _ _ xy) (cl_b _ _ xy).
Qed.

(* TOTHINK: connect_sym should not be necessary with a good def of closure *)
Lemma closure1 e x : connect_sym e -> connect e x =i closure e (pred1 x).
Proof. 
move => sym_e z; apply/idP/idP => [c_x_z|/closureP [x0] /eqP ->]; last by rewrite sym_e.
by apply/closureP; exists x; rewrite ?inE // sym_e. 
Qed.

Lemma closure_pred2 e x y :
  connect_sym e -> 
  closure e (pred2 x y) =i [predU closure e (pred1 x) & closure e (pred1 y)].
Proof.
move => sym_e z; rewrite !inE /= -!closure1 // !inE.  (* why slow ? *)
apply/closureP/idP => [[? /pred2P [->|->]]|/orP[]]; rewrite sym_e; try by move->.
  by exists x; rewrite // !inE eqxx.
by exists y; rewrite // !inE eqxx.
Qed.

Lemma codom_id : codom (@id T) =i predT. 
Proof. by move => x; rewrite -[x]/(id x) codom_f. Qed.

Lemma in_eq_n_comp e e' a : 
  connect_sym e -> connect_sym e' -> closed e a -> closed e' a ->
  {in a &, e =2 e'} -> n_comp e a = n_comp e' a.
Proof. 
move => sym_e sym_e' cl_e cl_e' eq_e.
have adj_e : rel_adjunction id e e' a.
{ apply: strict_adjunction => //=. apply/subsetP => z _; exact: codom_id.
  move => u v u_a. rewrite inE negbK /= in u_a. 
  apply/idP/idP => uv; first by rewrite -eq_e // -(cl_e u v).
  by rewrite eq_e // -(cl_e' u v). }
rewrite [in RHS](eq_n_comp_r (_ : a =i [preim id of a])) //. 
exact: adjunction_n_comp. 
Qed.

End Closure.
Arguments eq_closed [T e e' a].
Arguments eq_closed_r [T e a b].

Section order.
Variables (T : finType) (f : T -> T).

Lemma before_findex x z m : 
  fconnect f x z -> m < findex f x z -> iter m f x != z.
Proof.
elim: m x z => [x z|n IHn x z xCz nz]; first by rewrite lt0n findex_eq0.
have xDz : z != x by apply: contraTneq nz => ->; rewrite findex0.
rewrite iterSr IHn -1?ltnS -?fconnect_findex //.
by rewrite fconnect_eqVf eq_sym (negbTE xDz) in xCz.
Qed.

Lemma order_le_looping m z : looping f z m -> order f z <= m.
Proof. 
apply: contraTT; rewrite -ltnNge -looping_uniq => m_lt_o.
rewrite -(take_traject _ _ m_lt_o); exact: take_uniq (orbit_uniq _ _).
Qed.

Lemma order_le_fix m z : iter m.+1 f z = z -> order f z <= m.+1.
Proof.  
move=> fix_z. apply: order_le_looping.
by rewrite /looping fix_z trajectS mem_head.
Qed.

Lemma iter_looping m z y :
  (forall n, n < m -> iter n f z != y) -> looping f z m -> ~~ fconnect f z y.
Proof.
move => not_y ?; rewrite fconnect_orbit; apply/trajectP => -[k k_lt_o].
apply/eqP; rewrite eq_sym not_y //. 
exact: leq_trans k_lt_o (order_le_looping _).
Qed.

Lemma findex_finv z : findex f z (finv f z) = (order f z).-1.
Proof. by rewrite findex_iter ?orderSpred. Qed.

Lemma index_orbit (x : T) :
  index x (orbit f x) = 0.
Proof. by rewrite /orbit -orderSpred /= eqxx. Qed.

Lemma arc_orbit (x y : T) : 
  fconnect f x y -> arc (orbit f x) x y = traject f x (findex f x y).
Proof.
move=> conn_xy; rewrite /arc index_orbit rot0 /findex; set i := index y _.
suff I : i <= order f x by rewrite -(take_traject _ _ I).
by apply: ltnW; rewrite -size_orbit index_mem -fconnect_orbit.
Qed.

Lemma findex_bound (x y : T) n : iter n f x = y -> findex f x y <= n.
Proof. 
move => iter_n; have f_xy: fconnect f x y by rewrite -iter_n fconnect_iter.
by apply: contra_eqT iter_n; rewrite -ltnNge; apply: before_findex.
Qed.

(** [injective f] could be weakened to [fcycle f (orbit f x)] *)
Lemma findex_f (x y : T) : injective f -> fconnect f x y -> 
  findex f (f x) (f y) = findex f x y.
Proof.
move=> inj_f conn_xy; apply/eqP; rewrite eqn_leq; apply/andP;split.
  by apply: findex_bound; rewrite -iterSr iterS iter_findex.
apply: findex_bound; rewrite -[iter _ _ _](finv_f inj_f) -iterS iterSr.
by rewrite iter_findex ?finv_f // -same_fconnect1 -?same_fconnect1_r.
Qed.

Lemma fconnect_findex_r (x y : T) : 
  injective f -> fconnect f x y -> y != x -> 
  findex f x y = (findex f x (finv f y)).+1.
Proof. 
move=> inj_f con_xy yDx. 
by rewrite -[in RHS]findex_f 1?same_fconnect1_r ?f_finv // fconnect_findex .
Qed.

Lemma orbit_prefix n x :
  n <= order f x -> orbit f x = traject f x n ++ drop n (orbit f x).
Proof.
move => le_n_ox.
by rewrite /orbit -(subnKC le_n_ox) trajectD drop_size_cat // size_traject.
Qed.

(** generalizes [orbit_id] *)
Lemma orbit_fix x : f x = x -> orbit f x = [:: x].
Proof. 
move => fx; rewrite /orbit (_ : order f x = 1) //.
by apply/eqP; rewrite eqn_leq order_gt0 andbT; apply: order_le_fix.
Qed.

Lemma order_f (inj_f : injective f) x: 
  order f (f x) = order f x.
Proof. by apply/(orbitPcycle 1 2); rewrite /= inE -same_fconnect1. Qed.

Lemma orbit_rot1 (inj_f : injective f) x : orbit f (f x) = rot 1 (orbit f x).
Proof.
have [fx_x|fxNx] := eqVneq (f x) x; first by rewrite fx_x orbit_fix.
suff S : index (f x) (orbit f x) = 1.
  rewrite (orbitE (cycle_orbit inj_f x)) ?S //. 
  by rewrite -fconnect_orbit -same_fconnect1_r.
rewrite /orbit -orderSpred /= eq_sym (negPf fxNx). 
by case: (_.-1) => //= n; rewrite eqxx.
Qed.

Lemma orbit_rot_iter n (inj_f : injective f) x o :
  orbit f x = o -> orbit f (iter n f x) = iter n (rot 1) o.
Proof. by move <-; elim: n => // n IHn; rewrite !iterS -IHn orbit_rot1. Qed.

End order.

Arguments eq_closure_r [T e a a'].

Lemma forall_all (T : finType) (p : {pred T}) : [forall x, p x] = all p (enum T).
Proof. apply/forallP/allP => [|H x]; by [firstorder|apply/H/mem_enum]. Qed.

Lemma exists_has (T : finType) (p : {pred T}) : [exists x, p x] = has p (enum T).
Proof. by rewrite -[LHS]negbK negb_exists forall_all all_predC negbK. Qed.

Lemma n_compD (T : finType) (a b : {pred T}) e : 
  n_comp e a = n_comp e [predI a & b] + n_comp e [predD a & b].
Proof.
rewrite -[LHS](cardID b).
by congr (_ + _); apply: eq_card => x; rewrite !inE; case: (roots _ _).
Qed.

Arguments n_compD [T a] b.

Lemma n_comp0 (T : finType) (e : rel T) (a : {pred T}) : 
  a =i pred0 -> n_comp e a = 0.
Proof. 
by move=> a0; rewrite (eq_n_comp_r a0); apply: eq_card0 => x; rewrite !inE andbF.
Qed.

Lemma set_inP (T : finType) (A : {pred T}) (p : pred T) x :
  reflect (x \in A /\ p x) (x \in [set x in A | p x]).
Proof. rewrite !inE; exact: andP. Qed.

Section RootPartition.
Variables (T : finType) (e : rel T) (A : {set T}).
Hypothesis sym_e : connect_sym e.
Hypothesis closed_A : closed e A.

Lemma closed_root x : (root e x \in A) = (x \in A).
Proof.
symmetry; exact: closed_connect closed_A _ _ (connect_root _ _). 
Qed.

Let block x := [set y in connect e x].
Definition root_partition := [set block x | x in A & x \in roots e].

Lemma root_partitionE : 
  root_partition = equivalence_partition (connect e) A.
Proof.
apply/setP => B; apply/imsetP/imsetP => -[x Hx ->].
  move: Hx => /set_inP[x_A root_x]; exists x => //; apply/setP => y.
  by rewrite !inE andb_idl // => xy; rewrite -(closed_connect closed_A xy).
exists (root e x); first by rewrite !inE closed_root Hx roots_root.
apply/setP => y; rewrite !inE andb_idl => [|xy]. 
  apply: same_connect => //; exact: connect_root.
by rewrite -(closed_connect closed_A xy).
Qed. 

Lemma connect_equivalence : equivalence_rel (connect e).
Proof. 
by rewrite equivalence_relP; split; by [apply: connect0|apply: same_connect].
Qed.

Lemma root_partitionP : partition root_partition A.
Proof. 
rewrite root_partitionE equivalence_partitionP //.
by apply:in3W; apply: connect_equivalence. 
Qed.

Let rpP := root_partitionP.

Lemma sum_roots : #|A| = \sum_(x in roots e | x \in A) #|connect e x|.
Proof.
under [RHS]eq_bigl => ? do rewrite andbC.
rewrite (card_partition rpP) (set_partition_big_cond _ rpP) /=.
apply: eq_bigr => B /imsetP [x]; rewrite inE => /andP[x_A root_x] ->.
rewrite (big_pred1 x) ?cardsE // => y; rewrite !inE.
apply/andP/eqP => [[xy root_y]|->//]. 
by rewrite -(eqP root_y) -(rootP sym_e xy) (eqP root_x).
Qed.

Lemma n_comp_partition : n_comp e A = #|equivalence_partition (connect e) A|.
Proof. 
rewrite -root_partitionE.
rewrite card_in_imset; first by apply: eq_card => z; rewrite !inE andbC.
move => x y /set_inP [x_A root_x] /set_inP [y_A root_y] /setP /(_ y).
rewrite !inE connect0 -{2}[x](eqP root_x) -{2}[y](eqP root_y) => xy.
exact/rootP.
Qed.

End RootPartition.

Lemma closedT (T : finType) (e : rel T) : closed e [set: T].
Proof. by move=> *; rewrite !inE. Qed.

Lemma sum_rootsT (T : finType) (e : rel T) : 
  connect_sym e -> #|T| = \sum_(x in roots e) #|connect e x|.
Proof.
move=> sym_e; rewrite -cardsT (sum_roots sym_e); last exact: closedT.
by under eq_bigl => ? do rewrite !inE andbT.
Qed.

Lemma sum_roots_order (T : finType) (f : T -> T) (inj_f : injective f) :
  #|T| = \sum_(x in froots f) order f x.
Proof. exact/sum_rootsT/fconnect_sym. Qed.



Lemma sub_in_connect (T : finType) (e e' : rel T) (x : T) : 
  (forall y, connect e x y -> e y =1 e' y) -> forall y, connect e x y -> connect e' x y.
Proof.
move => H y /connectP [p]. elim/last_ind : p y => [y _ -> //|p z IHp y].
rewrite rcons_path last_rcons => /andP[pth_p ez -> {y}].
rewrite H in ez; last by apply/connectP; exists p.
apply: connect_trans (connect1 ez). exact: IHp.
Qed.
