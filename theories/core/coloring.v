From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import preliminaries bij digraph.
From GraphTheory Require Import sgraph dom partition.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Clique Number, Stable Set Number and Chromatic Number *)

(** In this file, we define the graph parameters α,ω, and χ. As much
of the reasoning about these parameters is concerned with the values
for the parameters on induced subgraphs, we define the parameters as
functions of type [mem_pred G \to nat] and introduce a notation that
insertes the required [mem] cast. For [G : sgraph] and [A : {set G}],
we can therefore write both both χ(G) and χ(A). This (drastically)
reduces the amount of (induced) subgraphs that need to be constructed,
significantly simplifying the proofs. *)

(** ** Clique number *)

Section Cliques.
Variables (G : sgraph).
Implicit Types (H K : {set G}).

Definition cliques H := [set K : {set G} | (K \subset H) && cliqueb K].

Lemma cliques_gt0 A : 0 < #|cliques A|. 
Proof.
apply/card_gt0P; exists set0; rewrite inE sub0set; apply/cliqueP.
by apply: small_clique; rewrite cards0.
Qed.

Lemma cliquesW (A B K : {set G}) : A \subset B -> K \in cliques A -> K \in cliques B.
Proof. 
by move=> subAB; rewrite !inE => /andP[subKA ->]; rewrite (subset_trans subKA). 
Qed.

Lemma cliques_subset (A K : {set G}) : K \in cliques A -> K \subset A.
Proof. by rewrite !inE => /andP[-> _]. Qed.

Lemma cliqueU1 x K : K \subset N(x) -> clique K -> clique (x |: K).
Proof. 
move => /subsetP subKNx clK u v /setU1P[-> {u}|uK] /setU1P[-> {v}|vK].
- by rewrite eqxx.
- by move/subKNx : vK; rewrite inE.
- by move/subKNx : uK; rewrite inE sgP.
- exact: clK.
Qed.

Lemma sub_clique K K' : K' \subset K -> clique K -> clique K'.
Proof. by move=> /subsetP subK clK x y /subK xK /subK yK; exact: clK. Qed.

Lemma cliqueD K H : clique K -> clique (K :\: H).
Proof. by move => clK x y /setDP[xK _] /setDP[yK _]; exact: clK. Qed.

Lemma cliquesD K H S : K \in cliques (H :\: S) -> K \in cliques H.
Proof. by rewrite !inE subsetD -andbA => /and3P[-> _ ->]. Qed.

Definition omega_mem (A : mem_pred G) := 
  \max_(B in cliques [set x in A]) #|B|.

End Cliques.

Notation "ω( A )" := (omega_mem (mem A)) (format "ω( A )").

Definition maxcliques (G : sgraph) (H : {set G}) := 
  [set K in cliques H | ω(H) <= #|K|].

Section OmegaBasics.
Variables (G : sgraph).
Implicit Types (A B K H : {set G}).

Lemma maxclique_clique K H : K \in maxcliques H -> clique K.
Proof. by rewrite !inE -andbA => /and3P[_ /cliqueP ? _]. Qed.

Lemma maxcliquesW S H : S \in maxcliques H -> S \in cliques H.
Proof. by rewrite !inE -andbA => /and3P[-> -> _]. Qed.

Variant omega_spec A : nat -> Prop :=
  OmegaSpec K of K \in maxcliques A : omega_spec A #|K|.

Lemma omegaP A : omega_spec A ω(A).
Proof. 
rewrite /omega_mem setE. 
have [/= K clK maxK] := eq_bigmax_cond (fun A => #|A|) (cliques_gt0 A).
by rewrite maxK; apply: OmegaSpec; rewrite inE clK -maxK -{2}[A]setE leqnn.
Qed.

Lemma clique_bound K A : K \in cliques A -> #|K| <= ω(A).
Proof. by move => clK; apply: bigmax_sup (leqnn _); rewrite setE. Qed.

Lemma card_maxclique K H : K \in maxcliques H -> #|K| = ω(H).
Proof. 
rewrite inE => /andP[clK ltK]; apply/eqP; rewrite eqn_leq ltK andbT.
exact: clique_bound.
Qed.

Lemma sub_omega A B : A \subset B -> ω(A) <= ω(B).
Proof.
move=> subAB; have [K] := omegaP A; rewrite inE => /andP[clA _]. 
exact/clique_bound/(cliquesW subAB).
Qed.

Lemma maxclique_disjoint K H A : 
  K \in maxcliques H -> [disjoint K & A] -> K \in maxcliques (H :\: A).
Proof.
rewrite !inE -!andbA subsetD => /and3P[-> -> maxK] -> /=. 
apply: leq_trans (sub_omega _) maxK. exact: subsetDl.
Qed.

Lemma maxclique_opn H K v : 
  v \in H -> K \in maxcliques H -> K \subset N(v) -> v \in K.
Proof.
rewrite !inE -andbA => vH /and3P[subKH /cliqueP clK maxK] subNvK.
have/cliqueP clvK : clique (v |: K) by apply: cliqueU1.
apply: contraTT maxK => vNK ; rewrite -ltnNge.
rewrite -add1n -[1 + _]/(true + #|K|) -vNK -cardsU1; apply: clique_bound.
by rewrite !inE clvK subUset sub1set vH subKH.
Qed.

Lemma omega0 : ω(@set0 G) = 0.
Proof.  
by case: omegaP => K; rewrite !inE subset0 -andbA => /andP[/eqP-> _]; rewrite cards0.
Qed.

Lemma omega_eq0 A : (ω(A) == 0) = (A == set0).
Proof.
apply/idP/idP => [|/eqP->]; last by rewrite omega0.
apply: contraTT => /set0Pn[x xH]; rewrite -lt0n -(cards1 x).
apply: clique_bound. rewrite inE sub1set xH. exact/cliqueP/clique1.
Qed.

(** TODO: if [stable S], the difference is exactly 1 *)
Lemma omega_cut H S : 
  {in maxcliques H, forall K, S :&: K != set0} -> ω(H :\: S) < ω(H).
Proof.
move/forall_inP; rewrite ltnNge; apply: contraTN; rewrite negb_forall_in.
have [/= K maxK geH] := omegaP (H :\: S).
move: maxK; rewrite inE => /andP[clK cardK].
apply/exists_inP; exists K; first by rewrite inE geH (cliquesD clK).
by move: clK; rewrite !inE subsetD negbK setI_eq0 disjoint_sym -andbA => /and3P[_ -> _].
Qed.

End OmegaBasics.

(** ** Stable Set Number *)

Section StableSets.
Variable (G : sgraph).
Implicit Types (H A S : {set G}).

Definition stabsets H := [set S : {set G} | S \subset H & stable S].

(* mostly useful in the right to left region to reestablish [stabsets] *)
Lemma in_stabsets B H : B \in stabsets H = (B \subset H) && @stable G B.
Proof. by rewrite !inE. Qed.

Lemma stabsetsP H S : reflect (S \subset H /\ stable S) (S \in stabsets H).
Proof. by rewrite in_stabsets; exact: andP. Qed.

Lemma stabsets_gt0 A : 0 < #|stabsets A|. 
Proof.
apply/card_gt0P; exists set0; rewrite inE sub0set; apply/stableP.
by move => u v; rewrite inE.
Qed.

Definition alpha_mem (A : mem_pred G) := 
  \max_(S in stabsets [set x in A]) #|S|.

Lemma stable_compl A : stable (A : {set compl G}) = cliqueb A.
Proof. 
apply/stableP/cliqueP => [stabA|clA] x y xA yA; first move=> xDy.
  by move: (stabA _ _ xA yA); rewrite {1}/edge_rel/= xDy negbK.
have [<-|xDy] := eqVneq x y; by [rewrite sgP|rewrite /edge_rel/= xDy clA].
Qed.

(** alternative proof, using duality, likely not worth it *)
Lemma clique_compl A : cliqueb (A : {set compl G}) = stable A.
Proof. 
apply/cliqueP/stableP => [clA|stabA] x y xA yA; last move=> xDy.
  have [<-|xDy] := eqVneq x y; first by rewrite sgP.
  by move:(clA _ _ xA yA xDy); rewrite {1}/edge_rel/= xDy.
by move: (stabA _ _ xA yA); rewrite {2}/edge_rel/= xDy.
Qed.

End StableSets.

Notation "α( A )" := (alpha_mem (mem A)) (format "α( A )").

Definition maxstabsets (G : sgraph) (H : {set G}) := 
  [set S in stabsets H | α(H) <= #|S|].

Section AlphaBasics.
Variables (G : sgraph).
Implicit Types (A B K S H : {set G}).

Variant alpha_spec A : nat -> Prop :=
  AlphaSpec S of S \in maxstabsets A : alpha_spec A #|S|.

Lemma maxstabset_stable S H : S \in maxstabsets H -> stable S.
Proof. by rewrite !inE -andbA => /and3P[_ -> _]. Qed.

Lemma maxstabsetW S H : S \in maxstabsets H -> S \in stabsets H.
Proof. by rewrite !inE -andbA => /and3P[-> -> _]. Qed.

Lemma maxstabsetS S H : S \in maxstabsets H -> S \subset H.
Proof. by rewrite !inE -andbA => /and3P[-> _ _]. Qed.

Lemma alphaP A : alpha_spec A α(A).
Proof. 
rewrite /alpha_mem setE. 
have [/= S stabS maxS] := eq_bigmax_cond (fun A => #|A|) (stabsets_gt0 A).
by rewrite maxS; apply: AlphaSpec; rewrite inE stabS -maxS -{2}[A]setE leqnn.
Qed.

Lemma stabset_bound S A : S \in stabsets A -> #|S| <= α(A).
Proof. by move => stabS; apply: bigmax_sup (leqnn _); rewrite setE. Qed.

Lemma card_maxstabset K H : K \in maxstabsets H -> #|K| = α(H).
Proof. 
rewrite inE => /andP[stabS ltS]; apply/eqP; rewrite eqn_leq ltS andbT.
exact: stabset_bound.
Qed.

Lemma alpha0 : α(set0 : {set G}) = 0.
Proof. 
by case: alphaP => S; rewrite !inE subset0 -!andbA => /and3P[/eqP ->]; rewrite cards0.
Qed.

Lemma alpha_eq0 H : (α(H) == 0) = (H == set0).
Proof.
apply/idP/idP => [|/eqP->]; last by rewrite alpha0.
apply: contraTT => /set0Pn[x xH]; rewrite -lt0n -(cards1 x).
by apply: stabset_bound; rewrite !inE stable1 sub1set xH.
Qed.

End AlphaBasics.

(** ** chromatic number *)

Definition coloring (G : sgraph) (P : {set {set G}}) (D : {set G}) :=
  partition P D && [forall S in P, stable S].

Definition trivial_coloring (G : sgraph) (A : {set G}) := 
  [set [set x] | x in A].

Lemma trivial_coloringP (G : sgraph) (A : {set G}) :
  coloring (trivial_coloring A) A.
Proof.
apply/andP; split; last by apply/forall_inP=> ? /imsetP[x xA ->]; exact: stable1.
suff -> : trivial_coloring A = preim_partition id A by apply: preim_partitionP.
have E x : x \in A -> [set x] = [set y in A | x == y].
  by move=> xA; apply/setP => y; rewrite !inE eq_sym andb_idl // => /eqP<-.
by apply/setP => P; apply/imsetP/imsetP => -[x xA ->]; exists x => //; rewrite E.
Qed.
Arguments trivial_coloringP {G A}.

Definition chi_mem (G : sgraph) (A : mem_pred G) := 
  #|[arg min_(P < trivial_coloring [set x in A] | coloring P [set x in A]) #|P|]|.

Notation "χ( A )" := (chi_mem (mem A)) (format "χ( A )").


Section Basics.
Variable (G : sgraph).
Implicit Types (P : {set {set G}}) (A B C D H : {set G}).

(** the [sub_partition] is actually a sub_coloring *)
Lemma sub_coloring P D A :
  coloring P D -> A \subset D -> coloring (sub_partition P A) A.
Proof.
case/andP => partP /forall_inP/= stabP subAD; apply/andP;split.
  exact: sub_partitionP.
have/subsetP sub := sub_partition_sub partP subAD.
apply/forall_inP => S {}/sub /imsetP [B BP ->]. 
by apply: sub_stable (stabP _ BP); apply: subsetIl.
Qed.

Lemma empty_coloring : coloring set0 (@set0 G).
Proof. 
by rewrite /coloring partition_set0 eqxx; apply/forall_inP => S; rewrite inE. 
Qed.

Lemma coloringD1 P S H : coloring P H -> S \in P -> coloring (P :\ S) (H :\: S).
Proof. 
move=> /andP[partP stabP] SP; apply/andP; split; first exact: partitionD1.
by apply/forall_inP => A /setD1P[_ /(forall_inP stabP)].
Qed.

Lemma coloringU1 P S H : 
  stable S -> S != set0 -> coloring P H -> [disjoint S & H] -> coloring (S |: P) (S :|: H).
Proof.
move=> stS SD0 /andP[partP stabP] disHS; apply/andP; split; first exact: partitionU1.
by apply/forall_inP => A /setU1P[-> //|/(forall_inP stabP)].
Qed.

Variant chi_spec A : nat -> Prop :=
  ChiSpec P of coloring P A & (forall P', coloring P' A -> #|P| <= #|P'|) 
  : chi_spec A #|P|.

(** We can always replace [χ(A)] with [#|P|] for some optimal coloring [P]. *)
Lemma chiP A : chi_spec A χ(A).
Proof.
rewrite /chi_mem; case: arg_minnP; first exact: trivial_coloringP.
by move=> P; rewrite setE => ? ?; apply: ChiSpec.
Qed.

Lemma color_bound P A : coloring P A -> χ(A) <= #|P|.
Proof. by move => col_P; case: chiP => P' _ /(_ _ col_P). Qed.

Lemma coloring_stabsetP P D : 
  reflect (partition P D /\ {in P, forall B, B \in stabsets D}) (coloring P D).
Proof.
apply: (iffP andP) => -[partP stabP]; split => //; [|apply/forall_inP] => B BP.
  by rewrite inE (partitionS partP) ?(forall_inP stabP).
by move/stabP : BP; rewrite !inE => /andP[_ ->].
Qed.

Lemma chi0 : χ(@set0 G) = 0.
Proof. 
apply/eqP; rewrite -leqn0; apply: leq_trans (color_bound empty_coloring) _.
by rewrite cards0.
Qed.

Lemma leq_chi A : χ(A) <= #|A|.
Proof. 
case: chiP => C col_C /(_ _ (@trivial_coloringP _ A)).
rewrite /trivial_coloring card_imset //. exact: set1_inj.
Qed.

Lemma sub_chi A B : A \subset B -> χ(A) <= χ(B).
Proof.
move=> subAB; case: (chiP B) => P col_P opt_P.
have col_S := sub_coloring col_P subAB.
apply: leq_trans (color_bound col_S) (card_sub_partition _ subAB).
by case/andP : col_P.
Qed.

Lemma cliqueIstable A C : clique C -> stable A -> #|C :&: A| <= 1.
Proof.
move => clique_C; apply: contraTT; rewrite -ltnNge.
case/card_gt1P => x [y] [/setIP[xA xC] /setIP[yA yC] xDy].
apply/stablePn; exists x, y; split => //. exact: clique_C.
Qed.

Lemma chi_clique C : clique C -> χ(C) = #|C|.
Proof.
move=> clique_C; apply/eqP; rewrite eqn_leq leq_chi /=.
have [P /andP[partP /forall_inP /= stabP] opt_P] := chiP.
suff S A : A \in P -> #|A| = 1. 
{ rewrite (card_partition partP); under eq_bigr => A ? do rewrite S //.
  by rewrite sum_nat_const muln1. }
move=> AP; apply/eqP; rewrite eqn_leq card_gt0 (partition_neq0 partP) //. 
rewrite andbT -(@setIidPl _ A C _) ?(partitionS partP) // setIC.
exact : cliqueIstable (stabP _ _).
Qed.

Lemma omega_leq_chi A : ω(A) <= χ(A).
Proof.
case: omegaP => C; rewrite !inE -andbA => /and3P[subCA /cliqueP clique_C _].
by apply: leq_trans (sub_chi subCA); rewrite chi_clique.
Qed.

Lemma chiD1 H S : stable S -> χ(H) <= χ(H :\: S).+1.
Proof.
move=> stabS; wlog subSH : S stabS / S \subset H.
  move => /(_ (S :&: H)); rewrite setDIr setDv setU0 subsetIr; apply => //.
  by apply: sub_stable stabS; rewrite subsetIl.
have [->|SD0] := eqVneq S set0; first by rewrite setD0.
case: (chiP (H :\: S)) => P colP _; have := coloringU1 stabS SD0 colP. 
rewrite disjoint_sym disjoints_subset subsetDr [S :|: _]setUC setDK // => /(_ isT) => colP'.
by apply: leq_trans (color_bound colP') _; rewrite cardsU1; case (_ \in _).
Qed.

Let setG : [set x in mem [set: G]] = [set x in mem G]. 
Proof. by apply/setP => x; rewrite !inE. Qed.

Lemma alphaT : α([set: G]) = α(G). 
Proof. by rewrite /alpha_mem setG. Qed.

Lemma omegaT : ω([set: G]) = ω(G). 
Proof. by rewrite /omega_mem setG. Qed.

Lemma chiT : χ([set: G]) = χ(G).
Proof. by rewrite /chi_mem setG. Qed.

End Basics.


Notation sval := (@sval _ _).

Section ISubgraph.
Variables (F G : sgraph) (i : F ⇀ G).
Let i_inj := isubgraph_inj i.

Lemma cliqueb_isubgraph (K : {set F}) : cliqueb K = cliqueb (i @: K).
Proof.
rewrite /cliqueb (@forall2_imset _ _ i i).
apply: eq_forall_in => x xK; apply: eq_forall_in => y yK.
by rewrite (inj_eq (isubgraph_inj i)) isubgraph_mono.
Qed.

Lemma stable_isubgraph (S  : {set F}) : stable S = stable (i @: S).
Proof.
rewrite !stableEedge (@forall2_imset _ _ i i).
apply: eq_forall_in => x xS; apply: eq_forall_in => y yS.
by rewrite isubgraph_mono.
Qed.

Lemma coloring_isubgraph (P : {set {set F}}) (D : {set F}) : 
  coloring P D = @coloring G [set i @: (S : {set F}) | S in P] (i @: D).
Proof.
rewrite /coloring -imset_partition; last exact: isubgraph_inj.
by rewrite forall_imset; under [in RHS]eq_forallb => S do rewrite -stable_isubgraph.
Qed.

Lemma preim_coloring (P : {set {set G}}) (D : {set F}) : 
  coloring P (i @: D) -> coloring [set i @^-1: (B : {set G}) | B in P] D.
Proof.
move => colP; rewrite coloring_isubgraph -imset_comp /comp /=.
have coB B : B \in P -> B \subset codom i. 
{ case/andP: colP => partP _; move/(partitionS partP) => sub.
  apply: subset_trans sub _. exact: imset_codom. }
under [X in coloring X _]eq_in_imset => B BP. 
  rewrite (can_preimset i) ?coB //; over. 
by rewrite imset_id.
Qed.

Lemma chi_isubgraph (A : {set F}) : χ(A) = χ(i @: A).
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- case: (chiP (i @: A)) => P /preim_coloring colP minP.
  exact: leq_trans (color_bound colP) (leq_imset_card _ _).
- case: (chiP A) => P colP minP.
  rewrite coloring_isubgraph in colP; apply: leq_trans (color_bound colP) _.
  by rewrite card_imset //; apply/imset_inj/isubgraph_inj.
Qed.

Lemma isubgraph_cliques (B K : {set F}) : 
  (K \in cliques B) = (i @: K \in cliques (i @: B)).
Proof. by rewrite !inE inj_imsetS // -cliqueb_isubgraph. Qed.

Lemma clique_to_isubgraph (K A : {set G}) : 
  K \in cliques A -> i @^-1: K \in cliques (i @^-1: A).
Proof.
rewrite !inE => /andP[subKA /cliqueP clK]. 
rewrite preimsetS //= cliqueb_isubgraph; apply/cliqueP.
by apply: sub_clique clK; rewrite sub_imset_pre preimsetS.
Qed.

Lemma can_inj_imset (A : {set F}) : i @^-1: (i @: A) = A.
Proof. by apply/setP => x; rewrite !inE (mem_imset). Qed.

Lemma omega_isubgraph (B : {set F}) : ω(B) = ω(i @: B).
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- have [K] := omegaP B. 
  rewrite inE isubgraph_cliques => /andP[ckK _]; rewrite -(card_imset _ i_inj).
  exact: clique_bound.
- have [K] := omegaP; rewrite inE => /andP[clK].
  move/clique_to_isubgraph : (clK). rewrite can_inj_imset => clK' _. 
  apply: leq_trans (clique_bound clK'). rewrite inj_card_preimset //.
  exact: subset_trans (cliques_subset clK) (imset_codom _ _).
Qed.

End ISubgraph.

(** We have proper duality reasoning at this point *)
Lemma maxcliques_compl (G : sgraph) (H : {set G}) : 
  maxcliques (H : {set compl G}) = maxstabsets H.
Proof.
apply/setP => A. rewrite !inE clique_compl; apply: andb_id2l => /andP[subAH stabA].
rewrite /omega_mem /alpha_mem setE /=.
by under eq_bigl => B do rewrite inE clique_compl -(@in_stabsets G).
Qed.

Lemma omega_compl (G : sgraph) (A : {set G}) : ω(A : {set compl G}) = α(A).
Proof.
case: omegaP => K. rewrite maxcliques_compl. exact: (@card_maxstabset G). 
Qed.

Lemma alpha_isubgraph (F G : sgraph) (i : F ⇀ G) (A : {set F}) : α(A) = α(i @: A).
Proof. 
by rewrite -omega_compl (omega_isubgraph (isubgraph_compl i)) omega_compl. 
Qed.

Lemma maxstabsets_compl (G : sgraph) (H : {set G}) : 
  maxstabsets (H : {set compl G}) = maxcliques H.
Abort. 

Lemma alpha_compl (G : sgraph) (A : {set G}) : α(A : {set compl G}) = ω(A).
Abort.

Section Induced.
Variables (G : sgraph) (H : {set G}).
Let i := induced_isubgraph H.

Lemma alpha_induced : α(induced H) = α(H).
Proof. by rewrite -alphaT (alpha_isubgraph i) imset_valT setE. Qed.

Lemma omega_induced : ω(induced H) = ω(H).
Proof. by rewrite -omegaT (omega_isubgraph i) imset_valT setE. Qed.

Lemma chi_induced : χ(induced H) = χ(H).
Proof. by rewrite -chiT (chi_isubgraph i) imset_valT setE. Qed.

Lemma cliqueb_induced (K : {set induced H}) : cliqueb K = cliqueb (val @: K).
Proof. exact: (cliqueb_isubgraph i). Qed.

Lemma stable_induced (K : {set induced H}) : stable K = stable (val @: K).
Proof. exact: (stable_isubgraph i). Qed.

End Induced.

Lemma maxstabset_to_induced (G : sgraph) (H : {set G}) (S : {set G}) : 
  S \in maxstabsets H -> val @^-1: S \in maxstabsets [set: induced H].
Proof.
pose i := induced_isubgraph H.
rewrite !inE subsetT (stable_isubgraph i) -andbA /= => /and3P[S1 S2 S3].
have subSi : S \subset codom i. 
{ apply: subset_trans S1 _; apply/subsetP => x xH. by apply/codomP; exists (Sub x xH). }
rewrite (@can_preimset _ _ i) ?S2 //= (@inj_card_preimset _ _ i) //=.
rewrite alphaT alpha_induced //. exact: val_inj.
Qed.

(** A coloring consisting of maximal stable sets is optimal *)
Lemma maxstabset_coloring (G : sgraph) (P : {set {set G}}) (D : {set G}) :
  partition P D -> {in P, forall S, S \in maxstabsets D} -> χ(D) = #|P|.
Proof.
move=> partP maxP; have [D0|[x xD]] := set_0Vmem D. 
  by subst D; apply/esym/eqP; rewrite chi0 cards_eq0 -partition_set0.
have colP : coloring P D. 
  by apply/coloring_stabsetP; split => // B /maxP/maxstabsetW.
apply/eqP; rewrite eqn_leq (color_bound colP) /=.
have [P' /coloring_stabsetP[partP' stabP'] _] := chiP. 
have [trivP trivP'] : trivIset P /\ trivIset P'.
  by case/and3P : partP; case/and3P : partP'.
apply: contraTT (leqnn #|D|); rewrite -!ltnNge => lt_P'_P.
rewrite -{1}(cover_partition partP') -(cover_partition partP).
rewrite -(eqP trivP) -(eqP trivP').
under [X in _ < X]eq_bigr => B BP do rewrite (card_maxstabset (maxP _ BP)).
apply: (@leq_ltn_trans (#|P'| * α(D))).
  by rewrite -sum_nat_const; apply: leq_sum => B /stabP'; apply: stabset_bound.
rewrite sum_nat_const ltn_mul2r lt0n alpha_eq0 lt_P'_P andbT.
by apply/set0Pn; exists x.
Qed.


Section Iso.
Variables (F G : sgraph) (i : diso F G).
Implicit Types (A : {set F}).

Let i_mono : {mono i : x y / x -- y}.
Proof. by move => x y; rewrite edge_diso. Qed.

Let i_inj : injective i.
Proof. by apply: (can_inj (g := i^-1)) => x; rewrite bijK. Qed.

Definition i' : F ⇀ G := ISubgraph i_inj i_mono.

(* TODO *)

Lemma diso_stable A : stable A = stable (i @: A).
Abort.

Lemma diso_clique A : cliqueb A = cliqueb (i @: A).
Abort.

Lemma diso_omega A : ω(A) = ω(i @: A).
Abort.

Lemma diso_chi A : χ(A) = χ(i @: A).
Abort.

End Iso.
