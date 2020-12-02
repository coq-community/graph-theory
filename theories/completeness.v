Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries bij.
Require Import setoid_bigop structures mgraph pttdom mgraph2 rewriting reduction open_confluence transfer.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

(** * Completeness *)

Section s.
Variable A: Type. 
Notation term := (pttdom.term A).  
Notation nterm := (pttdom.nterm A).
Notation test := (test (term_is_a_Pttdom A)). 
Notation tgraph2 := (graph2 test term).
Notation graph := (graph unit (flat A)).
Notation graph2 := (graph2 unit (flat A)).
Notation step := (@step (term_is_a_Pttdom A)).
Notation steps := (@steps (term_is_a_Pttdom A)).

(* local confluence of the additive, packaged system (Proposition 8.1) *)
Proposition local_confluence G G' H H':
    step G G' -> step H H' -> G ≃2p H -> 
    exists F, steps G' F /\ steps H' F.
Proof.
  (* by transferring local confluence of open steps *)
  move => GG HH [GH].
  apply ostep_of in GG as [U [[sGU] [UG']]]. 
  apply ostep_of in HH as [V [[sHV] [VH']]].
  apply oiso_of in GH.
  destruct (ostep_iso sGU GH) as [W [sHW UW]].
  destruct (fun HF => local_confluence HF sHV sHW) as [T [sVT sWT]]. by apply GH.
  have gT: is_graph T. by eapply osteps_graph, sWT; apply UW.
  have gU: is_graph U. by apply UW. 
  have gV: is_graph V. by apply VH'. 
  have gW: is_graph W. by apply UW. 
  apply (steps_of gV gT) in sVT. 
  apply (steps_of gW gT) in sWT. 
  exists (pack T); split.
  - transitivity (pack W)=>//. apply iso_step. 
    etransitivity. apply openK. apply iso_of_oiso.
    eapply oiso2_trans. apply oiso2_sym. eassumption. assumption.
  - transitivity (pack V)=>//. apply iso_step. 
    etransitivity. apply openK. apply iso_of_oiso.
    by apply oiso2_sym.
Qed.

Definition measure (G: tgraph2) := #|vertex G| + #|edge G|.

Lemma step_decreases G H: step G H -> measure H < measure G.
Proof.
  rewrite /measure.
  case; intros=>/=; by rewrite ?card_option ?card_sum ?card_unit ?card_void ?addSnnS ?addnS ?addn0.
Qed.

Lemma iso_stagnates (G H : tgraph2) : G ≃2p H -> measure H = measure G.
Proof. case. move=>[l _]. by rewrite /measure (card_bij (iso_v l)) (card_bij (iso_e l)). Qed.

(* confluence, via appropriate variant of Newman's lemma  *)
Proposition confluence F: forall G H, steps F G -> steps F H -> exists F', steps G F' /\ steps H F'.
Proof.
  induction F as [F_ IH] using (well_founded_induction_type (Wf_nat.well_founded_ltof _ measure)).
  move=> G H S.
  move: G H S IH => _ H [F G FG|F__ F0 G' G FF0 FG GG] IH FH.
  - exists H; split=>//. by rewrite -(inhabits FG: _ ≃2p _). 
  - move: H FH IH FF0=> _ [F H FH|F F1 H' H FF1 FH HH] IH FF0. 
      exists G; split=>//. rewrite -(inhabits FH: _ ≃2p _).  eauto using cons_step.
    destruct (local_confluence FG FH) as [M[GM HM]]. by rewrite -(inhabits FF0: _ ≃2p _).
    destruct (fun D => IH G' D _ _ GG GM) as [L[GL ML]].
     rewrite /Wf_nat.ltof -(iso_stagnates (inhabits FF0)). apply /ltP. by apply step_decreases.
    have HL: steps H' L by transitivity M. 
    destruct (fun D => IH H' D _ _ HL HH) as [R[LR HR]].
     rewrite /Wf_nat.ltof -(iso_stagnates (inhabits FF1)). apply /ltP. by apply step_decreases.
     exists R. split=>//. by transitivity L.
Qed.

(* graphs of normal forms are in normal form (i.e., can't reduce) *)
Lemma normal_steps s: forall H : tgraph2 , steps (tgraph_of_nterm s) H -> tgraph_of_nterm s ≃2p H.
Proof.
  suff E: forall G H, steps G H -> G ≃2p tgraph_of_nterm s -> G ≃2p H.
    by intros; apply E=>//; reflexivity. 
  destruct 1 as [G H I|G' G H H' I S _]=>//L.
  - exfalso. setoid_rewrite (inhabits I: _ ≃2p _) in L.
    clear -S L. destruct L as [[L Li Lo]]. generalize (card_bij (iso_e L)).
    destruct s; destruct S; simpl in *; (try by rewrite !card_option ?card_sum ?card_unit ?card_void); rewrite /unl in Li, Lo; move=>_.
    * generalize (card_bij (iso_v L)). rewrite card_sum !card_unit addnC.
      have H: 0 < #|G|. apply /card_gt0P. by exists input.
      revert H. case #|G|; discriminate.
    * revert Li Lo. 
      suff E: input=output :>G by congruence.
      apply/(card_le1_eqP (A := predT)) => //.
      apply iso_v, card_bij in L. rewrite !card_sum !card_unit addnC in L.
        by injection L=>->.
    * have E: forall y, L (inr tt) <> L (inl y) by intros y H; generalize (bij_injective (f:=L) H). 
      case_eq (L (inr tt)); case.
       generalize (E input). simpl in *. congruence. 
       generalize (E output). simpl in *. congruence.
    * generalize (endpoint_iso L false None). generalize (endpoint_iso L true None).
      have H: L.e None = None by case (L.e None)=>//; repeat case.
      rewrite H. case L.d; simpl; congruence.
Qed.

(* isomorphisms on graphs of normal forms give back equations *)
Lemma normal_iso (s t: nterm):
  tgraph_of_nterm s ≃2p tgraph_of_nterm t ->
  term_of_nterm s ≡ term_of_nterm t.
Proof.
  case s=>[a|a u b];
  case t=>[c|c v d]=>/=; move=> [[h hi ho]].
  - symmetry. by apply (vlabel_iso h tt).
  - exfalso.
    generalize (bijK' h (inl tt)). generalize (bijK' h (inr tt)).
    case (h^-1 (inr tt)). case (h^-1 (inl tt)). congruence. 
  - exfalso.
    generalize (bijK h (inl tt)). generalize (bijK h (inr tt)).
    case (h (inr tt)). case (h (inl tt)). congruence.
  - generalize (vlabel_iso h (inl tt)).
    generalize (vlabel_iso h (inr tt)).
    simpl in *. 
    rewrite hi ho /=. 
    generalize (elabel_iso h None).
    generalize (endpoint_iso h (h.d None) None).
    have H: h.e None = None by case (h.e None)=>//; repeat case. rewrite H. 
    case (iso_d h None)=>/=. by rewrite hi.
    intros. symmetry. apply dot_eqv=>//. apply dot_eqv=>//. 
Qed.

(* transferring isomorphisms on letter-labeled graphs to term-labeled graphs *)
Lemma tgraph_graph (u: term): 
  tgraph_of_term u ≃2 
  relabel2 (fun _ => 1%CM) (fun x : flat A => pttdom.tm_var x) (graph_of_term u).
Proof.
  have ? : 1%CM ≡ (1 ⊗ 1)%CM by move => M; rewrite monU.
  induction u=>/=.
  - etransitivity. apply (dot_iso2 IHu1 IHu2). symmetry. apply relabel2_dot => //. 
  - etransitivity. apply (par_iso2 IHu1 IHu2). symmetry. apply relabel2_par=>//. 
  - etransitivity. apply (cnv_iso2 IHu). symmetry. apply relabel2_cnv=>//. 
  - etransitivity. apply (dom_iso2 IHu). symmetry. apply relabel2_dom=>//.
  - symmetry. apply relabel2_one=>//. 
  - symmetry. apply relabel2_var=>//.
Qed.

(* Lemma 5.3 *)
Lemma tgraph_graph_iso (u v: term):
  graph_of_term u ≃2p graph_of_term v -> tgraph_of_term u ≃2p tgraph_of_term v.
Proof.
  intros [h]. exists.
  etransitivity. apply tgraph_graph.  
  etransitivity. 2: symmetry; apply tgraph_graph.
  apply relabel2_iso=>//.
  case=>//=??/=->//.  
Qed.

(** ** Main Result *)
                  
(* main completeness theorem *)
Theorem completeness (u v: term): graph_of_term u ≃2p graph_of_term v -> u ≡ v.
Proof.
  move=>/tgraph_graph_iso h.
  pose proof (reduce u) as H.
  have H' : steps (tgraph_of_term u) (tgraph_of_nterm (nt v))
    by rewrite h; apply reduce. 
  case (confluence H H')=>F [/normal_steps HF /normal_steps HF'].
  rewrite-> (nt_correct u), (nt_correct v).
  apply normal_iso. by rewrite HF'. 
Qed.

(* actually an iff since graphs from a 2pdom algebra *)
Theorem soundness_and_completeness (u v: term): graph_of_term u ≃2p graph_of_term v <-> u ≡ v.
Proof.
  split => [|uv]; first exact: completeness.
  change (graph_of_term u ≡ graph_of_term v). 
  exact: uv. (* graph_of_term is an evaluation w.r.t. a 2pdom algebra *)
Qed.

End s.

