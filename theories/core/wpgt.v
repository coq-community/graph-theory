From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import preliminaries bij digraph sgraph.
From GraphTheory Require Import dom partition coloring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Perfection *)

Definition perfect_mem (G : sgraph) (U : mem_pred G) := 
  [forall (A : {set G} | A \subset U), ω(A) == χ(A)].

Notation perfect U := (perfect_mem (mem U)).

(** relativize as well *)
Definition mimimally_imperfect (G : sgraph) := 
  (ω(G) != χ(G)) && [forall (A : {set G} | A \proper [set: G]), ω(A) == χ(A)].

Section PerfectBasics.
Variables (G : sgraph).
Implicit Types (A B H : {set G}) (P : {set {set G}}).

Lemma sub_perfect A B : A \subset B -> perfect B -> perfect A.
Proof. 
move=> subAB /forall_inP perfB; apply/forall_inP => C subCA. 
apply: perfB. exact: subset_trans _ subAB.
Qed.

Lemma perfect0 : perfect (set0 : {set G}).
Proof. by apply/forall_inP => A; rewrite subset0 => /eqP->; rewrite omega0 chi0. Qed.

Lemma perfectT (F : sgraph) : perfect([set: F]) = perfect(F). 
Proof. by apply: eq_forallb => A; rewrite subsetT subset_predT. Qed.

Lemma perfect_imset (F : sgraph) (i : F ⇀ G) (A : {set F}) : perfect A = perfect(i @: A).
Proof.
apply/idP/idP.
- move/forall_inP => perfIA; apply/forall_inP => B subBA.
  have subBi : B \subset codom i by apply: subset_trans subBA (imset_codom _ _).
  rewrite -[B](can_preimset i) //  -omega_isubgraph -chi_isubgraph; apply perfIA.
  rewrite -(@inj_imsetS _ _ i) // ?can_preimset //. exact: isubgraph_inj.
- move/forall_inP => perfA; apply/forall_inP => B ?.
  by rewrite (omega_isubgraph i) (chi_isubgraph i); apply/perfA/imsetS.
Qed.

Lemma perfect_induced H : perfect (induced H) = perfect H.
Proof. 
pose i := induced_isubgraph H.
by rewrite -perfectT (perfect_imset i) /= imset_valT setE. 
Qed.

Section Iso.
Variables (F : sgraph) (i : F ≃ G).

Let i_mono : {mono i : x y / x -- y}.
Proof. by move => x y; rewrite edge_diso. Qed.

Let i_inj : injective i.
Proof. by apply: (can_inj (g := i^-1)) => x; rewrite bijK. Qed.

Let i' : F ⇀ G := ISubgraph i_inj i_mono.

Lemma diso_perfect  (A : {set F}) : 
  perfect A = perfect (i @: A).
Proof. by rewrite (perfect_imset i'). Qed.

Lemma diso_perfectT : perfect F = perfect G.
Proof. by rewrite -!perfectT diso_perfect imset_bijT. Qed.

End Iso.

(** Here we prove the "strong elimination" and the "weak introduction"
lemmas for perfect graphs. Both are used in the proof of the Lovasz
replication lemma, and the strong introduction is used again in the
proof of the WPGT. *)

Lemma perfectEstrong (U H : {set G}) (v : G) :
  perfect U -> H \subset U -> v \in H -> 
  exists S, [/\ stable S, S \subset H, v \in S & [forall K in maxcliques H, S :&: K != set0]].
Proof.
move=> perfG subHU vH. have/eqP := forall_inP perfG _ subHU. 
case: chiP => P /andP[partP stabP] optP E. pose S := pblock P v. 
have vP : v \in cover P by rewrite (cover_partition partP) vH.
have SP : S \in P by rewrite pblock_mem // vP.
have SH : S \subset H by rewrite -(cover_partition partP); apply: bigcup_sup SP.
exists S; rewrite SH mem_pblock vP (forall_inP stabP) //; split => //.
apply: contra_eqT (E) => /forall_inPn/= [K maxK]; rewrite negbK setI_eq0 => disjK.
have colP' : coloring (P :\ S) (H :\: S) by apply: coloringD1 => //; apply/andP;split.
rewrite eqn_leq negb_and -!ltnNge; apply/orP;right.
have ωH : ω(H) <= ω(H :\: S). 
{ rewrite -(card_maxclique maxK) clique_bound //. 
  move: maxK; rewrite !inE -andbA => /and3P[K1 -> _]. 
  by rewrite subsetD K1 disjoint_sym disjK. }
apply: leq_ltn_trans ωH _. apply: leq_ltn_trans (omega_leq_chi _) _.
by apply: leq_ltn_trans (color_bound colP') _; rewrite [#|P|](cardsD1 S) SP.
Qed.

Lemma perfectIweak (U : {set G}) : 
  (forall H : {set G}, H \subset U -> H != set0 -> 
   exists S : {set G}, [/\ stable S, S \subset H & [forall K in maxcliques H, S :&: K != set0]]) 
  -> perfect U.
Proof.
move=> ex_stable; apply/forall_inP => /= H.
elim/card_ind : H => H IH subHU.
have [->|HD0] := eqVneq H set0; first by rewrite omega0 chi0.
have [S [stabS subSH /forall_inP cutS]] := ex_stable H subHU HD0.
rewrite eqn_leq omega_leq_chi /=. 
case: {-}_ /(omegaP H) => /= K maxK.
have cardHS : #|H :\: S| < #|H|. 
{ rewrite cardsDS // ltn_subrL; move/set0Pn : (cutS K maxK) => [x /setIP[xS _]].
  by apply/andP; split; apply/card_gt0P; exists x => //; apply: (subsetP subSH). }
apply: leq_trans (chiD1 _ stabS) _.
rewrite -(eqP (IH _ _ _)) //; first exact: omega_cut. 
by rewrite subDset subsetU // subHU orbT.
Qed.

End PerfectBasics.

(** needs generalized version of diso_perfect *)
Lemma diso_perfect_induced (G : sgraph) (U V : {set G}) :
  induced U ≃ induced V -> perfect U -> perfect V.
Proof.
move => i; rewrite -perfect_induced -perfectT (diso_perfect i).
have -> : i @: [set: induced U] = [set: induced V].
{ by apply/setP => x; rewrite !inE -[x](bijK' i) imset_f. }
by rewrite perfectT perfect_induced.
Qed.

(** ** Lovasz Replication Lemma *)

(** *** Single-vertex replication  *)

Definition replicate (G : sgraph) (v : G) := add_node G N[v].

Lemma diso_replicate (G : sgraph) (v : G) : G ≃ @induced (replicate v) [set~ None].
Proof. exact: diso_add_nodeK. Qed.

Arguments val : simpl never.
Arguments Sub : simpl never.

(* [v != v'] would suffice *)
Lemma replication_aux (G : sgraph) (v v' : G) : 
  v -- v' -> N[v] = N[v'] -> perfect [set~ v'] -> perfect G.
Proof.
move => vv' Nvv' perfNv'; rewrite -perfectT; apply: perfectIweak => H _ /set0Pn [z zH].
have [vv'_H|] := boolP ([set v;v'] \subset H); last first.
- have perfNv : perfect [set~ v]. 
  { apply: diso_perfect_induced perfNv'. exact: eq_cln_iso. }
  rewrite subUset !sub1set negb_and => vNH. 
  wlog vNH : v v' vv' {Nvv'} {perfNv'} perfNv {vNH} / v \notin H. 
    by case/orP: vNH => [vNH /(_ v v') |v'NH /(_ v' v)]; apply; rewrite // sgP.
  have [|S [S1 S2 _ S3]] := @perfectEstrong _ [set~ v] H z perfNv _ zH.
    by rewrite subsetC sub1set inE.
  by exists S. 
- have Hvv' : H :\ v' \subset [set~ v'] by rewrite subDset setUCr subsetT.
  have vHv' : v \in H :\ v' by rewrite !inE (sg_edgeNeq vv') (subsetP vv'_H) // !inE eqxx.
  have perfHv : perfect (H :\ v') by apply: sub_perfect perfNv'. 
  have := @perfectEstrong _ [set~ v'] (H :\ v')  v perfNv' Hvv' vHv'.
  move => [S] [stabS subSH vS cutS]; exists S; split => //. 
    exact: subset_trans subSH (subsetDl _ _).
  apply/forall_inP => K maxK. 
  have [v'K|v'NK] := boolP (v' \in K).
  - (* a maximal clique contains every vertex total to it *)
    suff vK : v \in K by apply/set0Pn; exists v; rewrite inE vS vK.
    apply: wlog_neg => v'NK.
    apply: maxclique_opn (maxK) _ ; first by case/setD1P : vHv'.
    apply/subsetP => x xK; case: (eqVneq x v) => [xv|xDv]; first by rewrite -xv xK in v'NK.
    rewrite opn_cln Nvv' !inE xDv -implyNb sgP; apply/implyP => xDv'.
    by rewrite (maxclique_clique maxK).
  - suff: K \in maxcliques (H :\ v') by move/(forall_inP cutS).
    by apply: maxclique_disjoint => //; rewrite disjoint_sym disjoints1.
Qed.

Lemma replication (G : sgraph) (v : G) : perfect G -> perfect (replicate v).
Proof.
move => perfG; apply: (@replication_aux (replicate v) (Some v) None).
- by rewrite /edge_rel/= v_in_clneigh. (* fixme: name! *)
- by apply/setP => -[x|] ; rewrite !inE /edge_rel//= ?v_in_clneigh ?Some_eqE ?in_cln 1?eq_sym.
- by rewrite -perfect_induced -(diso_perfectT (diso_replicate v)).
Qed.

(** *** Multiple simultaneous replicatsions - the Lovasz Graph *)

Section LovaszGraph.
Variables (G : sgraph) (m : G -> nat).

Definition LovaszRel (u v : Σ x : G, 'I_(m x)) := 
  if tag u == tag v then u != v else tag u -- tag v.

Lemma LovaszRel_sym : symmetric LovaszRel.
Proof.
by move=> u v; rewrite /LovaszRel [tag u == _]eq_sym [u == v]eq_sym sgP.
Qed.

Lemma LovaszRel_irrefl : irreflexive LovaszRel.
Proof. by move => [x i]; rewrite /LovaszRel/= !eqxx. Qed.

Definition Lovasz := SGraph LovaszRel_sym LovaszRel_irrefl.

Lemma Lovasz_tag_clique (K : {set Lovasz}) : 
  clique K -> clique (tag @: K).
Proof.
move => clK ? ? /imsetP[[x n] xnK ->] /imsetP[[y o] yoK ->] /= xDy.
have := clK _ _ xnK yoK; rewrite -tag_eqE/tag_eq/= (negbTE xDy) => /(_ isT).
by rewrite /edge_rel/=/LovaszRel/= (negbTE xDy).
Qed.

Lemma Lovasz_tag_stable (S : {set Lovasz}) : 
  stable S -> stable (tag @: S).
Proof.
move/stableP => stabS. 
apply/stableP => ? ? /imsetP[[/= u x] S1 ->] /imsetP[[/= v y] S2 ->].
have [<-|uDv] := eqVneq u v; first by rewrite sgP.
by have := stabS _ _ S1 S2; rewrite {1}/edge_rel/=/LovaszRel/= (negbTE uDv).
Qed.

Lemma Lovasz_tag_inj (S : {set Lovasz}) : 
  stable S -> {in S &, injective tag}.
Proof. 
move=> /stableP stabS [/= u x] [/= v y] uS vS uv; subst v; apply:eq_sigT => /=.
apply: contraNeq (stabS _ _ uS vS) => xDy.
by rewrite /edge_rel/=/LovaszRel/= eqxx -tag_eqE/tag_eq/= tagged_asE eqxx /=.
Qed.

Lemma Lovasz_stable_card (S : {set Lovasz}) :
  stable S -> #|tag @: S| = #|S|.
Proof. move=> stabS. rewrite card_in_imset //. exact: Lovasz_tag_inj. Qed.

Lemma alpha_Lovasz : α([set: Lovasz]) <= α([set: G]).
Proof.
case: alphaP => S /maxstabset_stable => stabS.
rewrite -(Lovasz_stable_card stabS); apply: stabset_bound.
by rewrite inE subsetT Lovasz_tag_stable.
Qed.

End LovaszGraph.

From mathcomp Require Import ssrint.
Local Notation "⟨ x , m ⟩" := (existT _ x m).

Definition ord_eq n := (inj_eq (@ord_inj n)).

Lemma isubgraph_Lovasz (G : sgraph) (m' m : G -> nat) : 
  (forall x, m' x <= m x) -> Lovasz m' ⇀ Lovasz m.
Proof.
move => leqM.
pose f (u : Lovasz m') : Lovasz m := 
  let: ⟨ x , i ⟩ := u in ⟨ x , widen_ord (leqM x) i ⟩.
have inj_f : injective f.
{ move => [x i] [y j] /eqP E; apply/eqP; move: E.
  rewrite /f -!tag_eqE/tag_eq/=; case: (eqVneq x y) => //= xEy.
  by move: j; subst y => j; rewrite !tagged_asE -ord_eq /=. }
have homo_f : {mono f : x y / x -- y}.
{ move => [x i] [y]; rewrite /f/edge_rel/=/LovaszRel/=. 
  have [-> j|//] := eqVneq y x. 
  by rewrite -!tag_eqE/tag_eq/= !tagged_asE -ord_eq /=. }
exact: ISubgraph inj_f homo_f.
Qed.

Lemma eq_iso_Lovasz (G : sgraph) (m m' : G -> nat) : 
  m =1 m' -> Lovasz m ≃ Lovasz m'.
Proof.
move => eq_m_m'; apply: isubgraph_iso.
  by apply: isubgraph_Lovasz => x; rewrite eq_m_m'.
by rewrite !card_tagged !sumnE !big_map; apply: leq_sum => i; rewrite eq_m_m'.
Qed.

Lemma iso_Lovasz1 (G : sgraph) : G ≃ Lovasz (fun _ : G => 1).
Proof. 
set L := Lovasz _.
pose f (x : G) : L := ⟨ x , ord0 ⟩. rewrite /= in f.
pose g (x : L) : G := tag x.
have can_f : cancel f g by []. 
have can_g : cancel g f. 
{ move => [x n];apply/eqP; rewrite /f/g/= tagged_eq.
  exact/eqP/esym/fintype.ord1. }
apply: (@Diso' G L) can_f can_g _ => x y. 
rewrite /f{1}/edge_rel/=/LovaszRel/=.
by have [->|//] := eqVneq y x; rewrite tagged_eq eqxx sgP.
Qed.

Lemma iso_Lovasz_repl (G : sgraph) (m : G -> nat) (z : G) (i : 'I_(m z)) : 
  @replicate (Lovasz m) ⟨ z, i ⟩ ≃ Lovasz (m[upd z := (m z).+1]).
Proof.
set F := replicate _; set m' := update _ _ _; set F' := Lovasz _. 
have mzS: (m z).+1 = m' z by rewrite /m' updateE.
have mxP : m z < m' z by rewrite /m' updateE.
have xNzP x : x != z -> m x = m' x by move=> ?; rewrite /m' updateE.
have xzP x (j : 'I_(m x)) : x == z -> j < m' z. 
{ by move => xz; rewrite /m' updateE -(eqP xz) ltnW // ltnS ltn_ord. }
pose f (x' : F) : F' := 
  if x' isn't Some ⟨ x , j ⟩ then ⟨ z , Ordinal mxP ⟩ else 
    match @boolP (x == z) with 
    | AltTrue xEz => ⟨ z , Ordinal (xzP x j xEz) ⟩
    | AltFalse xDz => ⟨ x , cast_ord (xNzP _ xDz) j ⟩
    end. 
pose g (x' : F') : F := let: ⟨ x , j ⟩ := x' in 
  match @boolP (x == z) with 
  | AltTrue xEz => if insub (j : nat) : option 'I_(m z) is Some j' 
                  then Some ⟨z, j'⟩ else None
  | AltFalse xDz => Some ⟨ x , cast_ord (esym (xNzP _ xDz)) j ⟩
  end.
have can_g : cancel g f.
{ move=> [x j]; rewrite /g/f/=; case : {-}_ / boolP => [/eqP xEz|xDz]; apply/eqP.
  - subst x. case: insubP => [j' Hj' vj'|].
    + by rewrite altT tagged_eq -ord_eq -vj'.
    + rewrite -leqNgt tagged_eq -ord_eq /= eqn_leq => -> /=. 
      by rewrite -ltnS mzS ltn_ord.
  - by rewrite altF tagged_eq -ord_eq /=. }
have can_f : cancel f g.
{ move=> [[x j]|]; last by rewrite /= altT // insubF ?ltnn.
  rewrite /g/f/=; case : {-}_ / boolP => [xEz|xDz]; apply/eqP.
  - rewrite altT //= insubT -?(eqP xEz) ?ltn_ord // => lt_j_mx.
    by rewrite Some_eqE tagged_eq -ord_eq.
  - by rewrite altF Some_eqE tagged_eq -ord_eq. }
apply : Diso' can_f can_g _.
move => [[x j]|] [[y o]|]; rewrite /f; last by rewrite !sgP.
- case: {-}_ / boolP => [xEz|xDz]; case: {-}_ / boolP => [yEz|yDz].
  + move: j o. have [? ?] : x = z /\ y = z by split; apply/eqP. subst x y => j o.
    by rewrite /edge_rel/= [RHS]/edge_rel/= /LovaszRel/= eqxx !tagged_eq -!ord_eq.
  + move: j. have ? : x = z by apply/eqP. subst x => j.
    by rewrite /edge_rel/= [RHS]/edge_rel/= /LovaszRel/= eq_sym (negbTE yDz).
  + move: o. have ? : y = z by apply/eqP. subst y => o.
    by rewrite /edge_rel/= [RHS]/edge_rel/= /LovaszRel/= (negbTE xDz).
  + rewrite /edge_rel/= [RHS]/edge_rel/= /LovaszRel/=.
    have [xEy|//] := eqVneq x y. move: o; subst y => o. 
    by rewrite !tagged_eq -!ord_eq.
- case: {-}_ / boolP => [xEz|xDz]. 
  + rewrite /edge_rel/=/LovaszRel/= eqxx tagged_eq -ord_eq /=.
    move: j; have ? : x = z by apply/eqP. subst x => j. 
    rewrite !inE /edge_rel/=/LovaszRel/= eqxx !tagged_eq.
    by rewrite -[j == i]eq_sym orbN eqn_leq negb_and -!ltnNge ltn_ord orbT.
  + rewrite /edge_rel/=/LovaszRel/= (negbTE xDz) !inE tagged_eqF //=.
    by rewrite /edge_rel/=/LovaszRel/= eq_sym (negbTE xDz) sgP.
- case: {-}_ / boolP => [yEz|yDz]. (* same as above *)
  + rewrite /edge_rel/=/LovaszRel/= eqxx tagged_eq -ord_eq /=.
    move: o; have ? : y = z by apply/eqP. subst y => o. 
    rewrite !inE /edge_rel/=/LovaszRel/= eqxx !tagged_eq.
    by rewrite -[o == i]eq_sym orbN eqn_leq negb_and -!ltnNge ltn_ord.
  + rewrite /edge_rel/=/LovaszRel/= eq_sym (negbTE yDz) !inE tagged_eqF //=.
    by rewrite /edge_rel/=/LovaszRel/= eq_sym (negbTE yDz).
Qed.

Lemma iso_Lovasz_const1 (G : sgraph) (m : G -> nat) :
  (forall x : G, m x = 1) -> G ≃ Lovasz m.
Proof.
move => ?; have M1 : m =1 fun=> 1 by [].
apply: diso_comp (iso_Lovasz1 G) _. exact/diso_sym/eq_iso_Lovasz.
Qed.

Lemma isubgraph_perfect (F G : sgraph) : F ⇀ G -> perfect G -> perfect F.
Proof. 
by move=> i; rewrite -!perfectT (perfect_imset i); apply: sub_perfect. 
Qed.

Lemma ltn_sum [I : eqType] (r : seq I) [P : pred I] [E1 E2 : I -> nat] (x : I) :
  (forall i : I, P i -> i !=x -> E1 i <= E2 i) -> x \in r -> P x -> E1 x < E2 x ->
  \sum_(i <- r | P i) E1 i < \sum_(i <- r | P i) E2 i.
Proof.
move=> leE12 x_r Px lt_x; rewrite !(big_rem x x_r) Px /= -addSn leq_add //.
apply: leq_sum => i Pi; have [->|] := eqVneq i x;[exact: ltnW| exact: leE12].
Qed.
Arguments ltn_sum [I r P E1 E2].

(* for m x > 1, this is replication, for m x = 0, this is deletion, for all x *)
Lemma Lovasz_perfect (G : sgraph) (m : G -> nat) : perfect G -> perfect (Lovasz m).
Proof.
have [n leMn] := ubnP (\sum_(x : G) `|m x - 1|%N).
elim: n G m leMn => // n IHn G m leMn perfG; rewrite ltnS in leMn.
have [/eqP|] := posnP (\sum_x `|m x - 1|).
- rewrite sum_nat_eq0 => /forallP/= sum0.
  have M1 x : m x = 1 by move: (sum0 x); rewrite distn_eq0 => /eqP.
  suff i : G ≃ Lovasz m by rewrite -(diso_perfectT i).
  exact: iso_Lovasz_const1.
- rewrite lt0n sum_nat_eq0 negb_forall/= => /existsP[x]; rewrite distn_eq0 => M1.
  have [lt_1_mx|lt_mx_2] := leqP 2 (m x).
  + pose m' := m[upd x := (m x).-1].
    have mxP : 0 < m' x by rewrite /m' updateE -ltnS ?(ltn_predK lt_1_mx).
    have/IHn/(_ perfG) perfG' : \sum_x `|m' x - 1| < n.
    { apply: leq_trans leMn. 
      apply: (ltn_sum x) => // [y _ yDx|]; first by rewrite /m' updateE.
      rewrite !distnEl //; last by rewrite ltnW.
      by rewrite -subSn // /m' updateE ?(ltn_predK lt_1_mx). }
    suff i : @replicate (Lovasz m') ⟨ x , Ordinal mxP ⟩ ≃ Lovasz m.
    { by rewrite -(diso_perfectT i); apply: replication. }
    apply: diso_comp (iso_Lovasz_repl _) (eq_iso_Lovasz _).
    move => y; have [->|yDx] := eqVneq y x; rewrite /m' !updateE //.
    by rewrite (ltn_predK lt_1_mx).
  + have {M1 lt_mx_2} mx0 : m x = 0 by move: (m x) M1 lt_mx_2 => [|[|[|]]].
    pose m' := m[upd x := 1]. 
    have/IHn/(_ perfG) perfG' : \sum_x `|m' x - 1| < n.
    { apply: leq_trans leMn. 
      apply: (ltn_sum x) => // [y _ yDx|]; first by rewrite /m' updateE.
      by rewrite /m' updateE mx0 distnn distnS. }
    suff i : Lovasz m ⇀ Lovasz m' by apply: isubgraph_perfect i perfG'.
    apply: isubgraph_Lovasz => y.
    by have [->|yDx] := eqVneq y x; rewrite /m' !updateE // mx0.
Qed.

(** * Weak Perfect Graph Theorem *)

(** ** First Proof - via replication *)

Lemma perfect_eq (G : sgraph) (A : {set G}) : perfect A -> ω(A) = χ(A).
Proof. by move/forall_inP => /(_ A (subxx A)) => /eqP. Qed.

Lemma weak_perfect_aux (G : sgraph) (x0 : G) : 
  perfect G -> exists2 K, cliqueb K & [forall S in maxstabsets [set: G], K :&: S != set0].
Proof.
move => perfG.
pose M := maxstabsets [set: G].
pose k := #|M|.
pose S (i : 'I_k) : {set G} := enum_val i.
pose m (x : G) := #|[set i : 'I_k | x \in S i]|.
pose G' := Lovasz m.
pose before (x : G) (i : 'I_k) := [set j : 'I_k | j < i & x \in S j]. 
pose B (i : 'I_k) := 
  [set xn : G' | tag xn \in S i & #|before (tag xn) i| == tagged xn :> nat].
pose P := [set B i | i : 'I_k].
have BiP (i : 'I_k) : B i \in P by apply/imsetP; exists i.
have beforeI (i : 'I_k) x : [set j in [set i0 | x \in S i0] | j < i] = before x i.
{ by apply/setP => j; rewrite !inE andbC. }
have ltn_before (i : 'I_k) x : x \in S i -> #|before x i| < m x. 
{ move=> x_Si; rewrite /before /m. apply: proper_card; apply/properP; split.
    by apply/subsetP => j; rewrite !inE => /andP[_ ->].
  by exists i; rewrite !inE ?ltnn. }
have coverP : cover P = [set: G'].
{ apply/eqP; rewrite eqEsubset subsetT; apply/subsetP => -[x n] _. 
  have/nth_ord [i] := ltn_ord n; rewrite !inE beforeI => x_Si b_xi. 
  by apply/bigcupP; exists (B i) => //; rewrite !inE /= x_Si b_xi eqxx. }
have tagB (i : 'I_k) : tag @: B i = S i.
{ apply/setP => x; apply/imsetP/idP => /= [[[z n] xn_Bi ->]|x_Si].
    by move: xn_Bi; rewrite inE => /andP[-> _].
  by exists ⟨ x , Ordinal (ltn_before _ _ x_Si) ⟩; rewrite // !inE /= x_Si eqxx. }
have disjB (i j : 'I_k) : j != i -> [disjoint B i & B j].
{ move =>jDi; apply/pred0Pn => -[[/= x n]].
  rewrite !inE /= -!andbA => /and4P[/= x_Si /eqP <- x_Sj]; apply/negP.
  wlog lt_i_j : i j {jDi} x_Si x_Sj / i < j => [W|].
  { case: (ltnP i j); [exact: W|rewrite leq_eqVlt eq_sym].
    by rewrite (inj_eq (@ord_inj _)) eq_sym (negbTE jDi) eq_sym /=; apply: W. }
  rewrite eq_sym eqn_leq negb_and -!ltnNge [X in _ || X]proper_card ?orbT //.
  apply/properP; split. 
  - by apply/subsetP => o; rewrite !inE => /andP[H ->]; rewrite (ltn_trans H lt_i_j).
  - by exists i; rewrite !inE ?lt_i_j ?ltnn. }
have inhB (i : 'I_k) : B i != set0. 
{ rewrite -(imset_eq0 tag) tagB -cards_eq0 (@card_maxstabset _ _ [set: G]).
    by rewrite alpha_eq0; apply/set0Pn; exists x0.
  exact: enum_valP. }
have [partP injP] : partition P [set: G'] /\ injective B.
{ have [/= ? inj] := (indexed_partition (J := predT) (in2W disjB) (in1W inhB)).
  by rewrite -coverP; split => //; apply: in2T inj. }
have cardP : #|P| = k by rewrite /P card_imset ?card_ord.
have stabB (i : 'I_k) : stable (B i). 
{ apply/stableP => -[/= x n] [/= y n']; rewrite !inE /=.
  have [xEy|xDy] := eqVneq x y.
  - by subst y => /andP[_ /eqP->] /andP[_ /eqP/ord_inj<-]; rewrite sgP.
  - move=> /andP[xSi _] /andP[ySi _]; rewrite /edge_rel/=/LovaszRel/= (negbTE xDy).
    by move: (enum_valP i); rewrite -/(S i) => /maxstabset_stable/stableP; apply. }
have maxB (i : 'I_k) : B i \in maxstabsets [set: G'].
{ rewrite !inE subsetT /= stabB /=; apply: leq_trans (alpha_Lovasz _) _.
  rewrite -Lovasz_stable_card // tagB. 
  by move: (enum_valP i); rewrite -/(S i) inE => /andP[_ ->]. }
have : ω([set: G']) = k.
{ have perfG' : perfect G' by apply: Lovasz_perfect.
  rewrite perfect_eq ?perfectT // -cardP; apply: maxstabset_coloring => //.
  move => ? /imsetP[i _ ->]; exact: maxB. }
have [K' maxK' cardK'] := omegaP.
have cutK' (i : 'I_k) : K' :&: B i != set0.
{ apply: partition_pigeonhole partP _ _ _ _ _ => // {i}.
    by rewrite cardK' cardP.
  move=> ? /imsetP[i _ ->]; apply: cliqueIstable.
  exact: maxclique_clique maxK'. exact: maxstabset_stable. }
exists (tag @: K').
- by apply/cliqueP/Lovasz_tag_clique; exact: maxclique_clique maxK'. 
- apply/forall_inP => A A_M; pose i : 'I_k := enum_rank_in A_M A.
  have defA : A = S i by rewrite /S enum_rankK_in.
  have [z /setIP[z_Bi z_K']] := set0Pn _ (cutK' i).
  by apply/set0Pn; exists (tag z); rewrite defA -tagB inE !imset_f.
Qed.

Theorem weak_perfect (G : sgraph) : perfect G -> perfect (compl G).
Proof.
rewrite -!perfectT => perfG ; apply: perfectIweak => H _ H0.
suff [K [clK subKH maxK]] : exists (K : {set G}), 
    [/\ cliqueb K, K \subset H & [forall S in @maxstabsets G H, K :&: S != set0]].
{ by exists K; rewrite stable_compl clK subKH maxcliques_compl. }
change {set G} in H; have {H0} [x xH]  := set0Pn _ H0.
have perfH : perfect (induced H).
  by rewrite perfect_induced; apply: sub_perfect perfG.
have [K clK /forall_inP cutK] := @weak_perfect_aux (induced H) (Sub x xH) perfH.
pose i := induced_isubgraph H.
exists (val @: K). rewrite -cliqueb_induced clK sub_induced; split => //.
apply/forall_inP => S /maxstabset_to_induced /cutK.
case/set0Pn => z; rewrite !inE => /andP[zK zS]; apply/set0Pn; exists (i z).
by rewrite inE zS imset_f.
Qed.

(** ** Second Proof - using matrix rank argument *)

Set Warnings "-ambiguous-paths".
From mathcomp Require Import all_algebra.
Set Warnings "ambiguous-paths".
Import GRing.Theory Num.Theory.

Section Rank.
Local Open Scope ring_scope.
(** This Lemma was kindly provided by Cyril Cohen *)

Lemma rank_argument (n k : nat) (A B : 'M[int]_(n,k)) : (k > 1)%N ->
   A^T *m B = \matrix_(i < k,j < k) (i != j : int) -> (k <= n)%N.
Proof.
move=> k_gt1 AtB; pose toQ := intr : int -> rat.
pose A' := map_mx toQ A; pose B' := map_mx toQ B.
suff: A'^T *m B' \in unitmx.
   by move=> /mxrank_unit rkAtB; have := mulmx_max_rank A'^T B'; rewrite 
rkAtB.
have {A A' B B' toQ n AtB}-> : A'^T *m B' = const_mx 1 - 1%:M.
   have := congr1 (map_mx toQ) AtB; rewrite map_mxM/= -map_trmx => ->.
   by apply/matrixP => i j; rewrite !mxE/=; case: eqP.
rewrite -(@unitmxZ _ _ (- 1)) ?rpredN// scaleN1r opprB.
suff: ~~ root (char_poly (const_mx 1 : 'M_k)) (1 : rat).
   rewrite /root /char_poly -[_.[_]]/(horner_eval _ _) -det_map_mx/=.
   rewrite /char_poly_mx map_mxD map_mxN/= !map_const_mx map_scalar_mx/=.
   by rewrite /horner_eval/= hornerX hornerC.
rewrite -eigenvalue_root_char; apply/eigenvalueP => -[v]; rewrite 
scale1r => v1.
have{v1} vE i : v ord0 i = \sum_j v ord0 j.
   by have /rowP/(_ i) := v1; rewrite !mxE; under eq_bigr do rewrite mxE 
mulr1.
have{vE} vMk i : v ord0 i *+ k.-1 = 0.
   rewrite -subn1 mulrnBr 1?ltnW//  mulr1n -[k as X in _ *+ X]card_ord.
   by rewrite -sumr_const/= vE -sumrB big1 => // j; rewrite vE subrr.
apply/negP; rewrite negbK; apply/eqP/rowP => i; rewrite mxE.
by have /eqP := vMk i; rewrite mulrn_eq0 -subn1 subn_eq0 ltn_geF// => /eqP.
Qed.
End Rank.

(** ** Minimally Imperfect Graphs *)

Definition min_imperfect_mem (G : sgraph) (A : mem_pred G) :=
  (omega_mem A < chi_mem A) && [forall (B : {set G} | B \proper A), perfect B].

Notation min_imperfect A := (min_imperfect_mem (mem A)).

Section MinImperfect.
Variable (G : sgraph).
Implicit Types (H A B S K : {set G}).

Lemma min_imperfect0 : min_imperfect (set0 : {set G}) = false.
Proof. by rewrite /min_imperfect_mem omega0 chi0. Qed.

Lemma min_imperfect_neq0 H : min_imperfect H -> H != set0.
Proof. by apply: contraTneq => ->; rewrite min_imperfect0. Qed.

Lemma proper_min_imperfect A H : 
  A \proper H -> min_imperfect H -> perfect A.
Proof. by move => propAH /andP[_ /forall_inP] /(_ _ propAH). Qed.

Lemma perfectPn H : 
  reflect (exists2 A : {set G}, A \subset H & min_imperfect A) (~~ perfect H).
Proof.
apply: (iffP forall_inPn) => -[A]; last first.
  move=> subAH /andP[lt_ω_α /forall_inP perfS]. exists A => //.
  by rewrite eqn_leq negb_and -!ltnNge lt_ω_α orbT.
rewrite unfold_in => subAH neq_ω_α.
exists [arg min_(B < A | (B \subset A) && (ω(B) != χ(B))) #|B|].
  case: arg_minnP; first by rewrite subxx.
  move=> B /andP[subBA _ _]; exact: subset_trans subAH.
case: arg_minnP; first by rewrite subxx.
move=> B /andP[subBA imB] minB; rewrite eqn_leq omega_leq_chi /= -ltnNge in imB.
rewrite /min_imperfect_mem imB; apply/forall_inP => C subCB. 
apply/forall_inP => D subDC. 
have propDB : D \proper B by apply: sub_proper_trans subCB.
move: (proper_card propDB). apply: contraTT; rewrite -ltnNge ltnS. 
by move: (minB D); rewrite (subset_trans _ subBA) // proper_sub.
Qed.

Lemma min_imperfect_maxclique H S : min_imperfect H -> 
   S \in stabsets H -> exists2 K, K \in maxcliques H & [disjoint K & S].
Proof.
case/andP => impH /forall_inP perfH stabS. 
have [->|[x xS]] := set_0Vmem S.
  by case: omegaP (leqnn ω(H)) => K maxK _; exists K => //; rewrite disjoint_sym disjoints0.
apply/exists_inP; apply: contraTT impH; rewrite negb_exists_in -ltnNge.
move/forall_inP => /= maxDn. 
have [subSH ?] := stabsetsP _ _ stabS.
apply: leq_ltn_trans (@chiD1 _ _ S _) _ => //.
have/perfH/perfect_eq <- : H :\: S \proper H.
  apply/properP; split; [exact: subsetDl|exists x => //].
  exact: (subsetP subSH). by rewrite !inE xS.
by apply: omega_cut => K maxK; rewrite setIC setI_eq0 maxDn.
Qed.

(* Bondy & Murty 14.14 *)
Lemma min_imperfectD S H : min_imperfect H -> S \in stabsets H -> ω(H :\: S) = ω(H).
Proof.
move=> min_imH stabS; apply/eqP; rewrite eqn_leq sub_omega ?subsetDl //=.
have [K maxK disjK] := min_imperfect_maxclique min_imH stabS.
rewrite -(card_maxclique maxK); apply: clique_bound.
exact/maxcliquesW/maxclique_disjoint.
Qed.


Lemma count_enum_cards (T : finType) (A : {set T}) (P : {pred T}) : 
  count P (enum A) = #|[set x in A | P x]|.
Proof.
rewrite -size_filter cardsE cardE.
apply/perm_size/uniq_perm; rewrite ?filter_uniq -?enumT ?enum_uniq //.
by move=> x; rewrite !(mem_enum,mem_filter,unfold_in) andbC.
Qed.

Lemma count_nth (T : Type) (x0 : T) (p : {pred T}) (s : seq T) :
  count p s = size [seq i <- iota 0 (size s) | p (nth x0 s i)].
Proof.
elim: s => //= a s ->; rewrite -[1]addn0 iotaDl filter_map fun_if /=.
by rewrite size_map; case: (p a).
Qed.

Lemma tuple_index_count (T : eqType) (n : nat) (s : n.-tuple T) (p : {pred T}) :
  #|[set j : 'I_n | p (tnth s j)]| = count p s.
Proof.
wlog x0 : n s p / T.
{ case: n s p => [|n] s p W; last exact/W/(thead s).
  by rewrite tuple0; apply: eq_card0 => -[j]. }
rewrite (count_nth x0) cardsE cardE -(size_map (@nat_of_ord n)).
apply/perm_size/uniq_perm. 
- by rewrite map_inj_uniq ?enum_uniq //; apply: ord_inj.
- by rewrite filter_uniq // iota_uniq.  
move => k. rewrite mem_filter mem_iota add0n leq0n /=.
have def_n : n = size s by case: s => /= s => /eqP->.
apply/mapP/andP => [[[j Hj] p_j] -> /=|[p_k lt_k_n]]. 
  by rewrite mem_enum /= unfold_in /tnth /= (set_nth_default x0) -?def_n // in p_j *.
rewrite -def_n in lt_k_n. exists (Ordinal lt_k_n) => //.
by rewrite mem_enum unfold_in /tnth /= (set_nth_default x0) // -def_n.
Qed.

Lemma trivIset_mem (T : finType) (P : {set {set T}}) x : 
  trivIset P -> #|[set B in P | x \in B]| = (x \in cover P).
Proof.
move=> trivP; have [x_covP /=|xNcovP] := boolP (x \in cover P); last first.
  apply: eq_card0 => B; rewrite !inE. apply: contraNF xNcovP => /andP[BP xB].
  by apply/bigcupP; exists B.
apply: (@eq_card1 _ (pblock P x)) => B; rewrite !inE.
apply/andP/eqP => [[BP xB]|->]; last by rewrite mem_pblock pblock_mem.
by apply/setP => y; rewrite (def_pblock _ _ xB).
Qed.

Lemma min_imperfect_stabsets_cliques H (a := α(H)) (w := ω(H)) (k := (a*w).+1) : 
  min_imperfect H -> 
  exists S K : 'I_k -> {set G}, 
    [/\ (forall i, S i \in stabsets H),
       (forall i, K i \in maxcliques H),
       (forall x, x \in H -> \sum_i (x \in S i) = a),
       (forall i, [disjoint K i & S i]) &
       (forall i j : 'I_k , i != j -> #|K i :&: S j| = 1)]. (* Bondy & Murty says "i < j" *)
Proof.
move => minH.
move: (leqnn a); rewrite {2}/a; case: alphaP => [S0 maxstabS _].
have colSv (v : { v | v \in S0}) : { P | coloring P (H :\ tag v) & #|P| == w }.
{ case: v => v v_S0; apply: sig2W => /=.
  have vH: v \in H by apply: (subsetP (maxstabsetS maxstabS)).
  have : χ(H :\ v) = w. rewrite -perfect_eq ?min_imperfectD //.
    by rewrite inE stable1 sub1set andbT. 
  apply: proper_min_imperfect minH; exact:properD1. 
  by case: chiP => P colP _ /eqP ?; exists P.  }
pose col v := if insub v is Some v' then s2val (colSv v') else set0.
pose s := S0 :: flatten [seq enum (col v) | v <- enum S0].
have size_s : size s == k.
{ rewrite /s/k /= eqSS size_flatten /shape sumnE !big_map big_enum /=.
  under eq_bigr => x x_S0 do 
    rewrite /col insubT -cardE /= (eqP (s2valP' (colSv (Sub x x_S0)))).
  by rewrite sum_nat_const (card_maxstabset maxstabS). }
pose S (i : 'I_k) := tnth (Tuple size_s) i; exists S.
(* pose S (i : 'I_k) := nth S0 s i; exists S.  *)
have stabS i : S i \in stabsets H. 
{ have := mem_tnth i (Tuple size_s); rewrite /S/=; set Si := tnth _ _. 
  rewrite !inE => /predU1P [->|].
    by move/maxstabsetW : maxstabS; rewrite inE => /andP[-> ->].
  move=> /flattenP => -[/= ?] /mapP [v v_S0 ->]; rewrite !mem_enum in v_S0 *.
  rewrite /col insubT; case: (colSv _) => /= P /andP[partP stabP]  _ SiP.
  rewrite (forall_inP stabP) // andbT. 
  exact: subset_trans (partitionS partP SiP) (subsetDl _ _). }
have cutS x : x \in H -> \sum_(i < k) (x \in S i) = a.
{ move => xH. 
  rewrite sum_cond1 /= sum1dep_card /S (tuple_index_count _ (fun S' => x \in S')).
  rewrite /s /= count_flatten !sumnE !big_map big_enum /= /a.
  have count_S v : v \in S0 -> count (fun S' => x \in S') (enum (col v)) = (v != x).
  { move=> v_S0. rewrite /col insubT; case: (colSv _) => /= P /andP[partP _] _.
    rewrite count_enum_cards trivIset_mem; last exact/partition_trivIset/partP.
    by rewrite (cover_partition partP) !inE xH 1?eq_sym andbT. }
  under eq_bigr => v vS0 do rewrite count_S //.
  rewrite -[RHS](card_maxstabset maxstabS) -sum1_card sum_cond1.
  have [x_S0|xNS0] := boolP (x \in S0).
  - by rewrite [RHS](bigD1 x) //=.
  - rewrite add0n big_mkcondr; apply: eq_bigr => v. 
    case: (eqVneq x v) => [<-|//]. by rewrite (negbTE xNS0). }
have cl (i : 'I_k) : { C | C \in maxcliques H & [disjoint C & S i] }.
  exact/sig2W/min_imperfect_maxclique. 
pose K (i : 'I_k) := s2val (cl i).
have maxK (i : 'I_k) : K i \in maxcliques H by exact: (s2valP (cl i)).
have disjK (i : 'I_k) : [disjoint K i & S i] by exact: (s2valP' (cl i)).
exists K; split => //. 
have le_KiSj i j : #|K i :&: S j| <= 1. 
{ apply: cliqueIstable; first exact:maxclique_clique. 
  by case/stabsetsP : (stabS j). }
have KiSi0 i : #|K i :&: S i| = 0 by apply/eqP; rewrite cards_eq0 setI_eq0.
have sum_j i : \sum_(j | i != j) #|K i :&: S j| >= a * w.
{ have <- : #|K i| = w by apply/card_maxclique/(s2valP (cl i)).
  rewrite -sum1_card sum_nat_mulnr.
  under eq_bigr => x x_Ki; first rewrite muln1 -(cutS x); first over. 
  move: x x_Ki; apply/subsetP. by move: (maxK i); rewrite !inE -andbA => /and3P[]. (* fixme *)
  rewrite exchange_big/=. under eq_bigr => j do rewrite sum_cardI.
  by rewrite [X in _ <= X]big_rmcond // => j /negPn/eqP<-. }
move => i j iDj; apply: contraTeq (sum_j i).
rewrite eqn_leq negb_and le_KiSj -leqNgt leqn0 /= -ltnNge => /eqP KiSj0.
rewrite (bigD1 j) //= KiSj0 add0n.
apply: (@leq_ltn_trans (\sum_(i0 < k | (i != i0) && (i0 != j)) 1)).
  exact: leq_sum => o _. 
rewrite sum1_card /= -ltnS -/k -[X in _ < X]card_ord.
set p := fun _ => _; rewrite -(cardC p) -addn1 addSn -addnS leq_add2l.
by apply/card_gt1P; exists i,j; rewrite !inE iDj !unfold_in !eqxx /= andbF.
Qed.

Lemma mulb (b1 b2 : bool) : ((b1 : int) * (b2 : int) = (b1 && b2 : int))%R.
Proof. by move: b1 b2 => [|] [|]. Qed.

Theorem Hajnal A : 
  reflect (forall B, B \subset A -> #|B| <= α(B) * ω(B)) (perfect A).
Proof.
apply introP => [perfA B subBA|].
{ rewrite perfect_eq ?(sub_perfect subBA) // mulnC. 
  have [P /coloring_stabsetP [partP stabP] _] := chiP.
  rewrite -{1}(cover_partition partP) /cover.
  have/eqP <- : trivIset P by case/and3P : partP. 
  rewrite -sum_nat_const; apply: leq_sum => C /stabP; exact: stabset_bound. }
case/perfectPn => H subHA minH => /(_ H subHA); apply/negP; rewrite -ltnNge.
have {A subHA} := min_imperfect_stabsets_cliques minH.
set a := α(H); set w := ω(H); set k := (a * w).+1; set n := #|H|.
move => [S] [K] [stabS maxK _ disjKS capKS].
pose x (i : 'I_n) : G := enum_val i.
pose MS := (\matrix_(i < n, j < k) (x i \in S j : int))%R.
pose MK := (\matrix_(i < n, j < k) (x i \in K j : int))%R.
suff: (MS^T *m MK = \matrix_(i < k,j < k) (i != j : int))%R.
{ apply: rank_argument. 
  by rewrite /k ltnS muln_gt0 !lt0n alpha_eq0 omega_eq0 min_imperfect_neq0. }
apply/matrixP => i j; rewrite !mxE.
under eq_bigr => z do rewrite !mxE mulb -in_setI /=.
have [<- {j}|iDj] /= := eqVneq i j.
- under eq_bigr => z do rewrite setIC (disjoint_setI0 (disjKS i)) inE /=.
  by rewrite GRing.sumr_const GRing.mul0rn.
- rewrite eq_sym in iDj. 
  move/capKS/mem_card1 : (iDj) => [v vP].
  have [o x_o] : exists o, x o = v.
  { have vH : v \in H. 
      have/cliques_subset/subsetP := maxcliquesW (maxK j).
      by apply; move/(_ v): vP; rewrite !inE eqxx => /andP[-> _].
    by exists (enum_rank_in vH v); rewrite /x enum_rankK_in. }
  subst v; rewrite (bigD1 o) //= setIC vP inE eqxx /=.
  have x_inj : injective x by apply: enum_val_inj.  
  under eq_bigr => z Hz do
    rewrite vP inE (inj_eq x_inj) (negbTE Hz) (_ : Posz 0 = 0 *+ 0)%R //.
  by rewrite GRing.sumrMnr mul0rn. 
Qed.
  
End MinImperfect.

