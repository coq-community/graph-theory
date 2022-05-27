From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** *** partitions and related properties *)

(** The majority of the lemmas in this file is part of mathcomp PR 731 *)

Section BigSetOps.

Variables T I : finType.
Implicit Types (U : {pred T}) (P : pred I) (A B : {set I}) (F :  I -> {set T}).

Lemma bigcup0P P F : 
  reflect (forall i, P i -> F i = set0) (\bigcup_(i | P i) F i == set0).
Proof.
rewrite -subset0; apply: (iffP bigcupsP) => sub0 i /sub0; last by move->.
by rewrite subset0 => /eqP. 
Qed.

Lemma bigcup_disjointP U P F  :
  reflect (forall i : I, P i -> [disjoint U & F i]) 
          [disjoint U & \bigcup_(i | P i) F i].
Proof.
apply: (iffP idP) => [disUF i Pp|]; last exact: bigcup_disjoint.
apply: disjointWr disUF; exact: bigcup_sup.
Qed.

End BigSetOps.


Lemma imset_cover (aT rT : finType) (P : {set {set aT}}) (f : aT -> rT) :
  [set f x | x in cover P] = \bigcup_(i in P) [set f x | x in i].
Proof.
apply/setP=> y; apply/imsetP/bigcupP => [|[A AP /imsetP[x xA ->]]].
  by move=> [x /bigcupP[A AP xA] ->]; exists A => //; rewrite imset_f.
by exists x => //; apply/bigcupP; exists A.
Qed.

Section partition.
Variable (T : finType) (P : {set {set T}}) (D : {set T}).
Implicit Types (A B S : {set T}).

Lemma partition0 : partition P D -> set0 \in P = false.
Proof. case/and3P => _ _. by apply: contraNF. Qed.

Lemma partition_neq0 B : partition P D -> B \in P -> B != set0.
Proof. by move=> partP; apply: contraTneq => ->; rewrite partition0. Qed.

Lemma partition_trivIset: partition P D -> trivIset P.
Proof. by case/and3P. Qed.

Lemma partitionS B : partition P D -> B \in P -> B \subset D.
Proof. 
by move=> partP BP; rewrite -(cover_partition partP); apply: bigcup_max BP _.
Qed.

Lemma cover1 A : cover [set A] = A.
Proof. by rewrite /cover big_set1. Qed.

Lemma trivIset1 A : trivIset [set A].
Proof. by rewrite /trivIset cover1 big_set1. Qed.

Lemma trivIsetD Q : trivIset P -> trivIset (P :\: Q).
Proof. 
move/trivIsetP => tP; apply/trivIsetP => A B /setDP[TA _] /setDP[TB _]; exact: tP.
Qed.

Lemma trivIsetU Q : 
  trivIset Q -> trivIset P -> [disjoint cover Q & cover P] -> trivIset (Q :|: P).
Proof.
move => /trivIsetP tQ /trivIsetP tP dQP; apply/trivIsetP => A B.
move => /setUP[?|?] /setUP[?|?]; first [exact:tQ|exact:tP|move => _].
  by apply: disjointW dQP; rewrite bigcup_sup.
by rewrite disjoint_sym; apply: disjointW dQP; rewrite bigcup_sup.
Qed.

Lemma coverD1 S : trivIset P -> S \in P -> cover (P :\ S) = cover P :\: S.
Proof.
move/trivIsetP => tP SP; apply/setP => x; rewrite inE.
apply/bigcupP/idP => [[A /setD1P [ADS AP] xA]|/andP[xNS /bigcupP[A AP xA]]].
  by rewrite (disjointFr (tP _ _ _ _ ADS)) //=; apply/bigcupP; exists A.
by exists A; rewrite // !inE AP andbT; apply: contraNneq xNS => <-.
Qed.

Lemma partitionD1 S : 
  partition P D -> S \in P -> partition (P :\ S) (D :\: S).
Proof.
case/and3P => /eqP covP trivP set0P SP.
by rewrite /partition inE (negbTE set0P) trivIsetD ?coverD1 -?covP ?eqxx ?andbF.
Qed.

Lemma partitionU1 S : 
  partition P D -> S != set0 -> [disjoint S & D] -> partition (S |: P) (S :|: D).
Proof.
case/and3P => /eqP covP trivP set0P SD0 disSD.
rewrite /partition !inE (negbTE set0P) orbF [_ == S]eq_sym SD0 andbT.
rewrite /cover bigcup_setU big_set1 -covP eqxx /=.
by move: disSD; rewrite -covP=> /bigcup_disjointP/trivIsetU1 => -[].
Qed.

Lemma partition_set0 : partition P set0 = (P == set0).
Proof.
apply/and3P/eqP => [[/bigcup0P covP _ ]|->]; last first.
  by rewrite /partition inE /trivIset/cover !big_set0 cards0 !eqxx.
by apply: contraNeq => /set0Pn[B BP]; rewrite -(covP B BP).
Qed.

Section Image.
Variables (T' : finType) (f : T -> T') (inj_f : injective f).
Let fP := [set f @: (S : {set T}) | S in P].

Lemma imset_inj : injective (fun A : {set T} => f @: A).
Proof. 
move => A B => /setP E; apply/setP => x. 
by rewrite -(mem_imset (mem A) x inj_f) E mem_imset.
Qed.

Lemma imset_disjoint (A B : {pred T}) :
  [disjoint f @: A & f @: B] = [disjoint A & B].
Proof.
apply/pred0Pn/pred0Pn => /= [[? /andP[/imsetP[x xA ->]] xB]|].
  by exists x; rewrite xA -(mem_imset (mem B) x inj_f).
by move => [x /andP[xA xB]]; exists (f x); rewrite !mem_imset ?xA.
Qed.

Lemma imset_trivIset : trivIset P = trivIset fP.
Proof.
apply/trivIsetP/trivIsetP.
- move=> trivP ? ? /imsetP[A AP ->] /imsetP[B BP ->].
  by rewrite (inj_eq imset_inj) imset_disjoint; apply: trivP.
- move=> trivP A B AP BP; rewrite -imset_disjoint -(inj_eq imset_inj).
  by apply: trivP; rewrite imset_f.
Qed.

Lemma imset0mem : (set0 \in fP) = (set0 \in P).
Proof. 
apply/imsetP/idP => [[A AP /esym/eqP]|P0]; last by exists set0; rewrite ?imset0.
by rewrite imset_eq0 => /eqP<-.
Qed.

Lemma imset_partition : partition P D = partition fP (f @: D).
Proof.
suff cov: (cover fP == f @:D) = (cover P == D).
  by rewrite /partition -imset_trivIset imset0mem cov.
by rewrite /fP cover_imset -imset_cover (inj_eq imset_inj).
Qed.
End Image.

Lemma partition_pigeonhole A :
  partition P D -> #|P| <= #|A| -> A \subset D -> {in P, forall B, #|A :&: B| <= 1} ->
  {in P, forall B, A :&: B != set0}.
Proof.
move=> partP card_A_P /subsetP subAD sub1; apply/forall_inP.
apply: contraTT card_A_P => /forall_inPn [B BP]; rewrite negbK => eq0.
rewrite -!ltnNge -(setD1K BP) cardsU1 !inE eqxx /= add1n ltnS.
have F (x : T) (xA : x \in A) : { C | (C \in P) & (x \in C) }.
  by apply/sig2W/bigcupP; rewrite -/(cover P) (cover_partition partP) subAD.
pose f (x : T) : {set T} :=
  if @idP (x \in A) is ReflectT xA then s2val (F _ xA) else set0.
have inj_f : {in A &, injective f}. 
{ move => x y; rewrite /f; 
  case : {1}_ / idP => // xA _; case : {1}_ / idP => // yA _ E.
  case: (F x xA) E (s2valP' (F y yA)) => /= C CP xC <- yC.
  by have/card_le1_eqP/(_ y x) := sub1 _ CP; apply; apply/setIP. }
rewrite -(card_in_imset inj_f); apply: subset_leq_card.
apply/subsetP => ? /imsetP[x xA ->]; rewrite /f; move: xA.
case : {1}_ / idP => // xA _; case: (F x xA) => /= C CP xC; rewrite !inE CP andbT.
by apply: contraTneq eq0 => <-; apply/set0Pn; exists x; apply/setIP.
Qed.

End partition.

Lemma indexed_partition (I T : finType) (J : {pred I}) (B : I -> {set T}) :
  let P := [set B i | i in J] in
  {in J &, forall i j : I, j != i -> [disjoint B i & B j]} -> 
  (forall i : I, J i -> B i != set0) -> partition P (cover P) /\ {in J&, injective B}.
Proof.
move=> P disjB inhB.
have s0NP : set0 \notin P.
  by apply/negP => /imsetP[x xI /eqP]; apply/negP; rewrite eq_sym inhB.
by rewrite /partition eqxx s0NP andbT /=; apply: trivIimset.
Qed.

(* TOTHINK: an alternative definition would be [[set B :&: A | B in P]:\ set0]. 
   Then one has to prove the partition properties, but the lemmas below 
   are simpler to prove. *)

(* This is not part of PR 731 *)

Section partition.
Variable (T : finType) (P : {set {set T}}) (D : {set T}).
Implicit Types (A B S : {set T}).


Definition sub_partition A : {set {set T}} := 
  preim_partition (pblock P) A.

Lemma sub_partitionP A : partition (sub_partition A) A.
Proof. exact: preim_partitionP. Qed.

Lemma sub_partition_sub A : 
  partition P D -> A \subset D -> sub_partition A \subset [set B :&: A | B in P].
Proof.
move=> partP /subsetP subAD; apply/subsetP => B; case/imsetP => [x xA ->].
have ? : x \in cover P by rewrite (cover_partition partP) subAD.
apply/imsetP; exists (pblock P x); first by rewrite pblock_mem.
by apply/setP => y; rewrite !inE eq_pblock 1?andbC //; case/and3P: partP.
Qed.

Lemma card_sub_partition A : 
  partition P D -> A \subset D -> #|sub_partition A| <= #|P|.
Proof. 
move=> partP subAD; apply: leq_trans (leq_imset_card (fun B => B :&: A) _).
apply: subset_leq_card. exact: sub_partition_sub. 
Qed.

End partition.
