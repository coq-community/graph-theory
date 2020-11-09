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

(*Axiom admitted_case : False.
Ltac admit := case admitted_case.*)

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

(** The [contra] lemmas below have been proposed for inclusion in Coq/mathcomp 
    (https://github.com/math-comp/math-comp/pull/499) *)

Lemma contra_not (P Q : Prop) : (Q -> P) -> (~ P -> ~ Q). Proof. by auto. Qed.
Lemma contraPnot (P Q : Prop) : (Q -> ~ P) -> (P -> ~ Q). Proof. by auto. Qed.

Lemma contraTnot b (P : Prop) : (P -> ~~ b) -> (b -> ~ P).
Proof. by case: b => //= H _ /H. Qed.

Lemma contraNnot (b : bool) (P : Prop) : (P -> b) -> (~~ b -> ~ P).
Proof. rewrite -{1}[b]negbK; exact: contraTnot. Qed.

Lemma contraPT (P : Prop) (b : bool) : (~~ b -> ~ P) -> P -> b.
Proof. by case: b => //= /(_ isT) nP /nP. Qed.

Lemma contra_notT (b : bool) (P : Prop) : (~~ b -> P) -> ~ P -> b.
Proof. by case: b => //= /(_ isT) HP /(_ HP). Qed.

Lemma contra_notN (b : bool) (P : Prop) : (b -> P) -> ~ P -> ~~ b.
Proof. rewrite -{1}[b]negbK; exact: contra_notT. Qed.

Lemma contraPN (b : bool) (P : Prop) : (b -> ~ P) -> (P -> ~~ b).
Proof. by case: b => //=; move/(_ isT) => HP /HP. Qed.

Lemma contraPneq (T:eqType) (a b : T) (P : Prop) : (a = b -> ~ P) -> (P -> a != b).
Proof. by move => ?; by apply: contraPN => /eqP. Qed.

Lemma contraPeq (T:eqType) (a b : T) (P : Prop) : (a != b -> ~ P) -> (P -> a = b).
Proof. move => Hab HP. by apply: contraTeq isT => /Hab /(_ HP). Qed.


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

Lemma leq_subn n m o : n <= m -> n - o <= m.
Proof. move => A. rewrite -[m]subn0. exact: leq_sub. Qed.

Lemma set1_inj (T : finType) : injective (@set1 T).
Proof. move => x y /setP /(_ y). by rewrite !inE eqxx => /eqP. Qed.

Lemma id_bij T : bijective (@id T).
Proof. exact: (Bijective (g := id)). Qed.

Lemma set2C (T : finType) (x y : T) : [set x;y] = [set y;x].
Proof. apply/setP => z. apply/set2P/set2P; tauto. Qed.

Lemma card_ltnT (T : finType) (p : pred T) x : ~~ p x -> #|p| < #|T|.
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
  have/inj_card_onto : injective f' by move => x1 x2 []; exact: f_inj.
  case/(_ _ (Sub y yP))/Wrap => [|/codomP[x]]; first by rewrite card_sig E.
  by move/(congr1 val) => /= ->; exact: codom_f.
Qed.

(** TODO: check whether the collection of lemmas on sets/predicates
and their cardinalities can be simplified *)

Lemma cards3 (T : finType) (a b c : T) : #|[set a;b;c]| <= 3.
Proof. 
  rewrite !cardsU !cards1 !addn1. 
  apply: leq_subn. rewrite ltnS. exact: leq_subn.
Qed.

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

Lemma take_uniq (T : eqType) (s : seq T) n : uniq s -> uniq (take n s).
Proof. exact/subseq_uniq/take_subseq. Qed.

Lemma card_geqP {T : finType} {A : pred T} {n} : 
  reflect (exists s, [/\ uniq s, size s = n & {subset s <= A}]) (n <= #|A|).
Proof.
apply: (iffP idP) => [n_le_A|[s] [uniq_s size_s /subsetP subA]]; last first.
  by rewrite -size_s -(card_uniqP uniq_s); exact: subset_leq_card. 
exists (take n (enum A)); rewrite take_uniq ?enum_uniq // size_take.
split => //; last by move => x /mem_take; rewrite mem_enum.
case: (ltnP n (size (enum A))) => // size_A.
by apply/eqP; rewrite eqn_leq size_A -cardE n_le_A.
Qed.

Lemma card_gt1P {T : finType}  {A : pred T} : 
  reflect (exists x y, [/\ x \in A, y \in A & x != y]) (1 < #|A|).
Proof. 
apply: (iffP card_geqP) => [[s] []|[x] [y] [xA yA xDy]].
- case: s => [|a [|b [|]]] //=; rewrite inE andbT => aDb _ subD.
  by exists a; exists b; rewrite aDb !subD ?inE ?eqxx.
- exists [:: x;y]; rewrite /= !inE xDy ; split => // z. 
  by rewrite !inE; case/pred2P => ->.
Qed.

Lemma card_gt2P {T : finType}  {A : pred T} : 
  reflect (exists x y z, [/\ x \in A, y \in A & z \in A] /\ [/\ x!=y, y!=z & z!=x]) 
          (2 < #|A|).
Proof.
apply: (iffP card_geqP) => [[s] []|[x] [y] [z] [[xD yD zD] [xDy xDz yDz]]].
- case: s => [|x [|y [|z [|]]]] //=; rewrite !inE !andbT negb_or -andbA. 
  case/and3P => xDy xDz yDz _ subA.
  by exists x;exists y;exists z; rewrite xDy yDz eq_sym xDz !subA ?inE ?eqxx.
- exists [:: x;y;z]; rewrite /= !inE negb_or xDy xDz eq_sym yDz; split => // u.
  by rewrite !inE => /or3P [] /eqP->.
Qed.

Lemma card_le1_eqP {T : finType} {A : pred T} : 
  reflect {in A&, forall x, all_equal_to x} (#|A| <= 1).
Proof.
apply: (iffP card_le1P) => [Ale1 x y xA yA /=|all_eq x xA y]. 
  by apply/eqP; rewrite -[_ == _]/(y \in pred1 x) -Ale1.
by rewrite inE; case: (altP (y =P x)) => [->//|]; exact/contra_neqF/all_eq.
Qed.

Lemma fintype_le1P (T : finType) : reflect (forall x : T, all_equal_to x) (#|T| <= 1).
Proof. apply: (iffP card_le1_eqP); [exact: in2T|exact: in2W]. Qed.

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

Definition smallest (T : finType) P (U : {set T}) := P U /\ forall V : {set T}, P V -> #|U| <= #|V|.

Lemma below_smallest (T : finType) P (U V : {set T}) : 
  smallest P U -> #|V| < #|U| -> ~ P V.
Proof. move => [_ small_U]; rewrite ltnNge; exact/contraNnot/small_U. Qed.

Definition largest (T : finType) P (U : {set T}) := P U /\ forall V : {set T}, P V -> #|V| <= #|U|.

Lemma above_largest (T : finType) P (U V : {set T}) : 
  largest P U -> #|V| > #|U| -> ~ P V.
Proof. move => [_ large_U]. rewrite ltnNge; exact/contraNnot/large_U. Qed.

(** compat:mathcomp-1.10 / in mathcomp-1.11, this will be subsumed by leqP *)
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

(* This section is part of >=mathcomp-8.12 *)
Section Disjoint.
Variable (T : finType).
Implicit Types (A B C D: {pred T}) (P Q : pred T) (x y : T) (s : seq T).

Lemma disjointFr A B x : [disjoint A & B] -> x \in A -> x \in B = false.
Proof. by move/pred0P/(_ x) => /=; case: (x \in A). Qed.

Lemma disjointFl A B x : [disjoint A & B] -> x \in B -> x \in A = false.
Proof. rewrite disjoint_sym; exact: disjointFr. Qed.

Lemma disjointWl A B C :
   A \subset B -> [disjoint B & C] -> [disjoint A & C].
Proof. by rewrite 2!disjoint_subset; apply: subset_trans. Qed.

Lemma disjointWr A B C : A \subset B -> [disjoint C & B] -> [disjoint C & A].
Proof. rewrite ![[disjoint C & _]]disjoint_sym. exact:disjointWl. Qed.

Lemma disjointW A B C D :
  A \subset B -> C \subset D -> [disjoint B & D] -> [disjoint A & C].
Proof.
by move=> subAB subCD BD; apply/(disjointWl subAB)/(disjointWr subCD).
Qed.

Lemma disjoints1 A x : [disjoint [set x] & A] = (x \notin A).
Proof. by rewrite (@eq_disjoint1 _ x) // => y; rewrite !inE. Qed.

End Disjoint.

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

Lemma rpath_sub (T : eqType) (e : rel T) (a : pred T) x p : 
  path (restrict a e) x p -> {subset p <= a}.
Proof.
  elim: p x => //= b p IH x. rewrite -!andbA => /and4P[H1 H2 H3 H4].
  apply/cons_subset. by split; eauto.
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

(** Extra Morphism declatations *)

Require Import Setoid Morphisms.

Instance ex2_iff_morphism (A : Type) :  
  Proper (pointwise_relation A iff ==> pointwise_relation A iff ==> iff) (@ex2 A).
Proof. by firstorder. Qed.


(*********************************************************************************)
(** * Preliminaries (used in Domination Theory) *)
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

Lemma sorted_leq_nth s (srt_s : sorted leq s) : 
  forall i j, i < j -> i < size s -> j < size s -> nth 0 s i <= nth 0 s j.
Proof. 
move => i j /ltnW i_j i_s j_s. apply: sorted_le_nth => //. exact: leq_trans.
Qed.
Arguments sorted_leq_nth : clear implicits. 

End Preliminaries_dom.

Arguments in11_in2 [T1 T2 P] A1 A2.
Arguments maxset_properP {T p D}.
Arguments minset_properP {T p D}.
