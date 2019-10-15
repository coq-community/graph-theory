Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries bij reduction open.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

Section s.
Variable A: Type.
Notation term := (term A).  
Notation nf_term := (nf_term A).  
Notation test := (test (tm_pttdom A)). 
Notation graph := (graph (pttdom_labels (tm_pttdom A))).
Notation graph2 := (graph2 (pttdom_labels (tm_pttdom A))).
Notation step := (@step (tm_pttdom A)).
Notation steps := (@steps (tm_pttdom A)).

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
  exists (close T); split.
  - eapply cons_iso_steps. 2:apply openK. apply steps_of.
    eapply osteps_iso. apply sWT.
    eapply oiso2_trans. apply oiso2_sym. apply UW. apply UG'.
  - eapply cons_iso_steps. 2:apply openK. apply steps_of.
    eapply osteps_iso. apply sVT. apply VH'.
Qed.

Definition measure (G: graph2) := #|vertex G| + #|edge G|.

Lemma step_decreases G H: step G H -> measure H < measure G.
Proof.
  rewrite /measure.
  case; intros=>/=; by rewrite ?card_option ?card_sum ?card_unit ?card_void ?addSnnS ?addnS ?addn0.
Qed.

Lemma iso_stagnates G H: G ≃2p H -> measure H = measure G.
Proof. case. move=>[l _]. by rewrite /measure (card_bij (iso_v l)) (card_bij (iso_e l)). Qed.

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
Lemma nf_steps s: forall H, steps (graph_of_nf_term s) H -> graph_of_nf_term s ≃2p H.
Proof.
  suff E: forall G H, steps G H -> G ≃2p graph_of_nf_term s -> G ≃2p H.
    by intros; apply E=>//; reflexivity. 
  destruct 1 as [G H I|G' G H H' I S _]=>//L.
  - exfalso. setoid_rewrite (inhabits I: _ ≃2p _) in L.
    clear -S L. destruct L as [[L Li Lo]]. generalize (card_bij (iso_e L)).
    destruct s; destruct S; simpl in *; (try by rewrite !card_option ?card_sum ?card_unit ?card_void); move=>_.
    * generalize (card_bij (iso_v L)). rewrite card_sum !card_unit addnC.
      have H: 0 < #|G|. apply /card_gt0P. by exists input.
      revert H. case #|G|; discriminate.
    * revert Li Lo. 
      suff E: input=output :>G by congruence.
      apply (card_le1 (D:=predT))=>//. 
      apply iso_v, card_bij in L. rewrite !card_sum !card_unit addnC in L.
        by injection L=>->.
    * have E: forall y, L (inr tt) <> L (inl y) by intros y H; generalize (bij_injective (f:=L) H). 
      case_eq (L (inr tt)); case.
       generalize (E input). simpl. congruence. 
       generalize (E output). simpl. congruence.
    * generalize (endpoint_iso L false None). generalize (endpoint_iso L true None).
      have H: L.e None = None by case (L.e None)=>//; repeat case.
      rewrite H. case L.d; simpl; congruence.
Qed.

(* isomorphisms on graphs of normal forms give back equations *)
Lemma iso_nf (s t: nf_term):
  graph_of_nf_term s ≃2p graph_of_nf_term t ->
  term_of_nf s ≡ term_of_nf t.
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

(* main completeness theorem *)
Theorem completeness (u v: term): graph_of_term u ≃2p graph_of_term v -> u ≡ v.
Proof.
  move=>h.
  pose proof (reduce u) as H.
  have H' : steps (graph_of_term u) (graph_of_nf_term (nf v))
    by rewrite h; apply reduce. 
  case (confluence H H')=>F [/nf_steps HF /nf_steps HF'].
  rewrite-> (nf_correct u), (nf_correct v).
  apply iso_nf. by rewrite HF'. 
Qed.

(* TODO: go one step further and get soundness and completeness w.r.t. letter-labelled graphs
   (using g2_pttdom on the flat bisetoid) *)

End s.
Print Assumptions completeness.
