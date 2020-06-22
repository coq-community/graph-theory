From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries digraph sgraph set_tac.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Preliminaries *)

Lemma ltn_subn n m o : n < m -> n - o < m.
Proof. apply: leq_ltn_trans. exact: leq_subr. Qed.

Lemma ord3P (P : 'I_3 -> Type) : P ord0 -> P ord1 -> P ord2 -> forall i : 'I_3, P i.
Proof. 
  have H (i j : 'I_3) : i == j -> P i -> P j by move/eqP->.
  move => P0 P1 P2 [[|[|[|//]]] Hi]. 
  exact: H P0. exact: H P1. exact: H P2. 
Qed.

(* Notation "A ∩ B" := (A :&: B) (at level 30). *)

(** We first show that for intersection closed properties, the helly
property of families of size three extends to the families of
arbitrary (finite) cardinalities. *)

(** TOTHINK: This should extend also to [T:choiceType] using the finmap library *)
Lemma helly3_lifting (T : finType) (P : {set T} -> Prop) :
  (forall A B, P A -> P B -> P (A :&: B)) ->
  (forall f : 'I_3 -> {set T}, 
    (forall i, P (f i)) -> (forall i j, f i :&: f j != set0) -> exists x, forall i, x \in f i) ->
  forall F : {set {set T}}, 
    0 < #|F| -> (forall A, A \in F -> P A) -> {in F &, forall A B, A :&: B != set0} -> exists x, forall A, A \in F -> x \in A.
Proof.
  move => closed_P helly3_P. 
  elim/card_ind => /= F IH inh_F F_sub_P F_pw_in.
  case: (ltnP 1 #|F|) => card_F.
  - case/card_gt1P : card_F => /= X [Y] [XF YF XY].
    move def_F' : ((F :\: [set X;Y]) :|: [set X :&: Y]) => F'.
    have F'_in_U : (forall A, A \in F' -> P A). 
    { rewrite -def_F'. move => A /setUP [/setDP []|/set1P->]; by auto. }
    have F'_pw_in : {in F' &, forall A B : {set T}, A :&: B != set0}.
    { move => A B. rewrite -def_F' !in_setU !in_set1 => HA HB. 
      wlog [HA HB]: A B {HA HB} / A = X :&: Y /\ B \in F.
      { move => W. 
        case/orP : HA => [/setDP [HA _]|/eqP HA]; case/orP : HB => [/setDP [HB _]|/eqP HB].
        - exact: F_pw_in.
        - rewrite setIC. by apply: W.  
        - exact: W.
        - rewrite HA HB setIid. exact: F_pw_in. }
      rewrite HA.
      pose f := tnth [tuple X; Y; B].
      case: (helly3_P f _ _).
      - apply: ord3P; by rewrite /f /tnth /=; apply: F_sub_P.
      - do 2 apply: ord3P; by rewrite /f /tnth /=; apply: F_pw_in.
      - move => x Hx. apply/set0Pn; exists x. rewrite !inE. 
        move: (Hx ord0) (Hx ord1) (Hx ord2). by rewrite /f /tnth /= => -> -> ->. } 
    have card_F' : #|F'| < #|F|.
    { (* set reasoning with cardinalities *)
      rewrite -def_F' cardsU cards1. apply: ltn_subn.
      rewrite -setDDl [#|F|](cardsD1 X) [#|F :\ X|](cardsD1 Y).
      rewrite !inE XF YF eq_sym XY /= add1n addnC. exact: leqnn. }
    have inh_F' : 0 < #|F'|.
    { apply/card_gt0P. exists (X :&: Y). by rewrite -def_F' !inE eqxx. }
    case: (IH F' _ _ _ _) => // x Hx. 
    exists x => A A_in_F. case: (boolP ((A == X) || (A == Y))) => H.
    + case : (setIP (Hx (X :&: Y) _)).
      * by rewrite -def_F' !inE eqxx.
      * by case/orP: H => /eqP ->.
    + apply: Hx. by rewrite -def_F' !inE H A_in_F. 
  - have/card1P [A HA] : #|F| == 1 by rewrite eqn_leq card_F.
    move: (F_pw_in A A). rewrite !HA inE eqxx. case/(_ _ _)/Wrap => //.
    case/set0Pn => x. rewrite setIid => Hx. exists x => B. 
    by rewrite HA inE => /eqP->.
Qed.

Section Tree.
Variable (G : sgraph).
Hypothesis tree_G : is_forest [set: G].

(** If the whole graph is a forest, every connected set of vertices is a subtree *)

(** Subtrees are closed under intersection *)
Lemma tree_connectI (T1 T2 : {set G}) : 
  connected T1 -> connected T2 -> connected (T1 :&: T2).
Proof.
  move => C1 C2 x y /setIP [X1 X2] /setIP [Y1 Y2]. 
  case: (path_in_connected C1 X1 Y1) => p Ip /subsetP Sp.
  case: (path_in_connected C2 X2 Y2) => q Iq /subsetP Sq.
  have {Iq Ip} ? : p = q by apply: tree_G.
  subst q. apply connectRI with p => z zp. by rewrite !inE Sp ?Sq.
Qed.

(** NOTE: The [irred p] assumption could be removed, but it doesn't hurt *)
Lemma subtree_cut (T1 T2 : {set G}) (x1 x2 : G) (p : Path x1 x2) :
  connected T1 -> connected T2 -> T1 :&: T2 != set0 -> x1 \in T1 -> x2 \in T2 ->
  irred p -> exists y, [/\ y \in p, y \in T1 & y \in T2].
Proof.
  move => tree_T1 tree_T2 cap_T12 X11 X22 Ip.
  case/set0Pn : cap_T12 => z /setIP [Z1 Z2]. 
  move: p Ip. move def_A : (T1 :&: T2) => A.
  have zA : z \in A by rewrite -def_A inE Z1.
  gen have H,Hp1 : T1 T2 x1 x2 tree_T1 tree_T2 X11 X22 Z1 Z2 def_A zA / 
    exists z1 (p1 : Path x1 z1), [/\ z1 \in A, irred p1, p1 \subset T1 & forall k, k \in A -> k \in p1 -> k = z1].
  { case: (@path_in_connected _ T1 x1 z) => // p1 Ip1 subT1.
    case: (split_at_first zA (path_end p1)) => z1 [p11] [p12] [E H1 H2]. subst.
    exists z1. exists p11. split => //. 
    + by case/irred_catE : Ip1. 
    + apply: subset_trans subT1. exact: subset_pcatL. }
  move: Hp1 => [z1] [p1] [zA1 Ip1 /subsetP sub_p1 H1].
  case: (H T2 T1 x2 x1) => // {H}; first by rewrite setIC. 
  move => z2 [p2] [zA2 Ip2 /subsetP sub_p2 H2].
  case: (path_in_connected _ zA1 zA2) => [|q Iq /subsetP qA].
  { rewrite -def_A. exact: tree_connectI. }
  set r := pcat (pcat p1 q) (prev p2).
  suff I: irred r. 
  { move => p Ip. 
    have -> : p = r by apply: forestT_unique. 
    exists z1. rewrite !inE /= -def_A in zA1 *. by case/setIP : zA1 => -> -> . }
  rewrite /r.
  apply: irred_catI. 
  - move => k. rewrite !inE. case/orP => U V.
    + rewrite [k]H2 //. by rewrite -def_A inE sub_p1 ?sub_p2. 
    + by rewrite [k]H2 // qA. 
  - apply: irred_catI => // k ? /qA ?. exact: H1.
  - by rewrite irred_rev.
Qed.

Lemma tree_I3 (T : 'I_3 -> {set G}) : 
  (forall i, connected (T i)) -> (forall i j, T i :&: T j != set0) -> exists z, forall i, z \in T i.
Proof.
  move => tree_T T_pw_in.
  case/set0Pn : (T_pw_in ord0 ord1) => x /setIP [X0 X1].
  case/set0Pn : (T_pw_in ord0 ord2) => y /setIP [Y0 Y1].
  case: (path_in_connected _ X0 Y0) => [|p irr_p /subsetP sub_T0]; first exact: tree_T. 
  case: (@subtree_cut (T ord1) (T ord2) x y p) => // z [/sub_T0 ? ? ?].
  exists z. exact: ord3P.
Qed.

Theorem tree_helly (F : {set {set G}}) : 
  (forall T : {set G}, T \in F -> connected T) -> F != set0 -> 
  {in F &, forall A B, A :&: B != set0} -> \bigcap_(A in F) A != set0.
Proof.
  rewrite -card_gt0. move => F_subtree F_inh F_pq_in.
  case: (@helly3_lifting G (@connected G) _ _ F _ _ _) => //.
  - exact: tree_connectI.
  - exact: tree_I3.
  - move => x Hx. apply/set0Pn. exists x. apply/bigcapP. exact: Hx.
Qed.

End Tree.



