Require Import RelationClasses Morphisms Setoid Omega.

From mathcomp Require Import all_ssreflect.

Require Import edone finite_quotient preliminaries.
Require Import multigraph subalgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs". 

(** * Isomorphim Properties for Term Graph Constructors *)

Local Open Scope quotient_scope.
Local Notation "\pi x" := (\pi_(_) x) (at level 4).

(** Iterated Term Constructors *)

(* NOTE: We need to use foldr1 here since there is no neutral element
for parallel composition in the term syntax for connected graphs *)
Definition big_tmI : seq term -> term := foldr1 tm1 tmI id.


(** ** Parallel Composition *)

Definition iso2_congruence (op : graph2 -> graph2 -> graph2) :=
  forall (G1 G2 G1' G2' : graph2), G1 ≈ G1' -> G2 ≈ G2' -> op G1 G2 ≈ op G1' G2'.

Lemma par2_congr : iso2_congruence par2.
Proof.
  move => G1 G2 G1' G2' [f f1 f2] [g g1 g2].
  have [h [I1 I2 I3 I4]] := iso2_union f1 f2 g1 g2.
  apply: (merge_congr (h := h)) => //; try by rewrite I3 f1.
  move=> x y /=. rewrite !par2_equiv_of. apply: lift_equiv; first by case: I2.
  move=> {x y} [x|x] [y|y]; rewrite /par2_eq/= !(I3, I4) //.
  by rewrite !iso2_inv_in // !iso2_inv_out.
Qed.

Instance par2_morphisem : 
  Proper (iso2 ==> iso2 ==> iso2) par2.
Proof. move => ? ? ? ? ? ?. exact: par2_congr. Qed.

Definition big_par2 (s : seq graph2) : graph2 := 
  \big[par2/top2]_(G <- s) G.

Lemma big_par2_cons G Gs : 
  big_par2 (G::Gs) = par2 G (big_par2 Gs).
Proof. by rewrite /big_par2 big_cons. Qed.

(** NOTE: For the moment this is only needed to provide an identity
element to par2. If this turns out hard to prove, use foldr1 instead *)

Lemma par2_LR (G1 G2 : graph2) x y :
  inl x = inr y %[mod_eq @par2_eqv G1 G2] ->
  x = g_in /\ y = g_in \/ x = g_out /\ y = g_out.
Proof.
  case/eqmodP; rewrite /=/par2_eqv /eq_op/= -!/eq_op. case: ifP => i_o.
  - rewrite !inE !eqEsubset. case/orP=> /andP[H _]; move: H.
    all: rewrite subUset !sub1set !inE /eq_op/= orbF =>/andP[/eqP-> /eqP->].
    + by left.
    + by right.
  - move/negbT: i_o. rewrite negb_and !negbK. case/orP=> /eqP<-.
    all: rewrite subUset !sub1set !inE /eq_op/= !orbF orbb.
    + case/andP=> /eqP-> /orP[]/eqP->; by [left | right].
    + case/andP=> /orP[]/eqP-> /eqP->; by [left | right].
Qed.

Lemma par2_injL (G1 G2 : graph2) x y : 
  g_in != g_out :> G2 -> 
  inl x = inl y %[mod_eq @par2_eqv G1 G2] ->
  x = y.
Proof.
  move=> iNo2 /eqmodP/=. rewrite /par2_eqv/= iNo2 andbT sum_eqE.
  case/orP=> [/eqP//|]. case: ifP => [iNo1 | /negbFE/eqP<-].
  - rewrite !inE !eqEsubset ![[set inl x; inl y] \subset _]subUset !sub1set !inE.
    rewrite /eq_op/= !orbF. by case/orP=> /andP[]/andP[/eqP-> /eqP->].
  - by rewrite subUset !sub1set !inE /eq_op/= !orbF !orbb => /andP[/eqP-> /eqP->].
Qed.

(** TODO: simplify once we have symmetry? *)
Lemma par2_injR (G1 G2 : graph2) x y : 
  g_in != g_out :> G1 -> 
  inr x = inr y %[mod_eq @par2_eqv G1 G2] ->
  x = y.
Proof.
  move=> iNo2 /eqmodP/=. rewrite /par2_eqv/= iNo2 /= sum_eqE.
  case/orP=> [/eqP//|]. case: ifP => [iNo1 | /negbFE/eqP<-].
  - rewrite !inE !eqEsubset ![[set inr x; inr y] \subset _]subUset !sub1set !inE.
    rewrite /eq_op/=. by case/orP=> /andP[]/andP[/eqP-> /eqP->].
  - by rewrite subUset !sub1set !inE /eq_op/= !orbb => /andP[/eqP-> /eqP->].
Qed.

Lemma par2_idR G : par2 G top2 ≈ G.
Proof 
  with try solve [by move/par2_injL => <- //
                 |by case/par2_LR => [] [? ?];subst ].
  pose f (x : par2 G top2) : G := 
    match repr x with
    | inl x => x 
    | inr false => g_in
    | inr true => g_out
    end.
  pose g (x : G) : par2 G top2 := \pi (inl x).
  have c1 : cancel f g.
  { move => x. rewrite /f /g. 
    case e1 : (repr x) => [a|[|]]; first by rewrite -e1 reprK.
    - rewrite -[x]reprK e1. apply/eqmodP => /=. by rewrite par2_eqv_io.
    - rewrite -[x]reprK e1. apply/eqmodP => /=. by rewrite par2_eqv_io. }
  have c2 : cancel g f.
  { move => x. rewrite /f /g. 
    case: piP => [[y|[]]] Hy. 
    - symmetry. exact: par2_injL Hy.
    - case: (par2_LR Hy) => [] [? ?];by subst.
    - case: (par2_LR Hy) => [] [? ?];by subst. }
  pose h (e: edge (par2 G top2)) : edge G :=
    match e with inl e => e | inr e => match e with end end.
  exists (f,h); repeat split => //=. (* simpl takes long ... *)
  - case => // e. rewrite /f. case: piP => [[y|[|]]]...
  - case => // e. rewrite /f. case: piP => [[y|[|]]]...
  - by case. 
  - rewrite /f. case: piP => [[y|[|]]]...
  - rewrite /f. case: piP => [[y|[|]]]...
  - exact: Bijective c1 c2.
  - by apply: (Bijective (g := inl)) => [[e|]|].
 Qed.

Lemma par2_idL G : par2 top2 G ≈ G.
Admitted.

Lemma big_par2_1 G : big_par2 [:: G] ≈ G.
Proof. rewrite /big_par2 big_cons big_nil. exact: par2_idR. Qed.

Lemma big_par2_map (r : seq term) : 
  ~~ nilp r -> big_par2 (map graph_of_term r) ≈ graph_of_term (big_tmI r).
Proof.
  elim: r => //= u s. case e : (nilp s).
  - move => _ _. by rewrite (nilP e) /= /big_par2_cons big_par2_1. 
  - move/(_ isT) => IH _. by rewrite big_par2_cons /= IH.
Qed.

(* TOTHINK: Do we really need to prove this ? *)
Lemma par2_assoc G1 G2 G3 : 
  par2 (par2 G1 G2) G3 ≈ par2 G1 (par2 G2 G3).
Admitted.

Lemma big_par2_cat r1 r2 : 
  big_par2 (r1 ++ r2) ≈ par2 (big_par2 r1) (big_par2 r2).
Proof. 
  rewrite /big_par2 big_cat_nested. 
  elim: r1 => [|G r1 IH].
  - by rewrite !big_nil par2_idL.
  - by rewrite !big_cons IH par2_assoc.
Qed.

Lemma big_par2_congr (T:finType) (s : seq T) (g1 g2 : T -> graph2) :
  (forall x, x \in s -> g1 x ≈ g2 x) -> 
  big_par2 [seq g1 x | x <- s] ≈ big_par2 [seq g2 x | x <- s].
Proof. 
  elim: s => //= a s IH. admit.
Admitted.



Lemma big_par2_congrs (T:finType) (s : {set T}) (g1 g2 : T -> graph2) :
  (forall x, x \in s -> g1 x ≈ g2 x) -> 
  big_par2 [seq g1 x | x in s] ≈ big_par2 [seq g2 x | x in s].
Proof. 
  move => A. apply: big_par2_congr => x. by rewrite mem_enum => /A.
Qed.


(** ** Sequential Composition *)

Lemma seq2_congr : iso2_congruence seq2.
  move => G1 G2 G1' G2' [f f1 f2] [g g1 g2].
  have [h [I1 I2 I3 I4]] := iso2_union f1 f2 g1 g2.
  apply: (merge_congr (h := h)) => //; try by rewrite ?(I3,I4) ?f1 ?g1.
  move=> x y /=. rewrite !seq2_equiv_of. apply: lift_equiv; first by case: I2.
  move=> {x y} [x|x] [y|y]; rewrite /seq2_eq /= !(I3,I4) //.
  by rewrite !sum_eqE !iso2_inv_in // !iso2_inv_out.
Qed.

Instance seq2_morphism : Proper (iso2 ==> iso2 ==> iso2) seq2.
Proof. move => ? ? ? ? ? ?. exact: seq2_congr. Qed.

Lemma seq2_injL (G1 G2 : graph2) (x y : G1) :
  inl x = inl y %[mod_eq @seq2_eqv G1 G2] -> x = y.
Proof.
  move=> /eqmodP. rewrite /=/seq2_eqv/= sum_eqE. case/orP=> [/eqP//|].
  by rewrite eq_sym eqEcard subUset -andbA andbCA !sub1set !inE.
Qed.

Lemma seq2_injR (G1 G2 : graph2) (x y : G2) :
  inr x = inr y %[mod_eq @seq2_eqv G1 G2] -> x = y.
Proof.
  move=> /eqmodP. rewrite /=/seq2_eqv/= sum_eqE. case/orP=> [/eqP//|].
  by rewrite eq_sym eqEcard subUset !sub1set !inE.
Qed.

Lemma seq2_LR (G1 G2 : graph2) (x : G1) (y : G2) :
  inl x = inr y %[mod_eq @seq2_eqv G1 G2] -> x = g_out /\ y = g_in.
Proof.
  move=> /eqmodP. rewrite /=/seq2_eqv/=.
  rewrite eq_sym eqEcard subUset !sub1set !inE orbC /= !sum_eqE.
  by case/andP=> /andP[/eqP<- /eqP<-].
Qed.

Lemma seq2_idR G : seq2 G one2 ≈ G.
Admitted.

Lemma seq2_idL G : seq2 one2 G ≈ G.
Admitted.

Lemma seq2_assoc G1 G2 G3 : 
  seq2 (seq2 G1 G2) G3 ≈ seq2 G1 (seq2 G2 G3).
Proof.
  pose x0 := (g_in : seq2 G1 (seq2 G2 G3)).
  pose f (x : seq2 (seq2 G1 G2) G3) :  seq2 G1 (seq2 G2 G3) := 
    match repr x with
    | inl y => match repr y with
              | inl z => \pi (inl z) 
              | inr z => \pi (inr (\pi (inl z)))
              end
    | inr y => \pi (inr (\pi (inr y)))
    end.
  pose g (x :  seq2 G1 (seq2 G2 G3)) : seq2 (seq2 G1 G2) G3 := 
    match repr x with
    | inr y => match repr y with
              | inl z => \pi (inl (\pi (inr z)))
              | inr z => \pi (inr z)
              end
    | inl y => \pi (inl (\pi (inl y)))
    end.
  (* rewrite /= in f,g. runs forever *)
  (* have Cfg : cancel f g. *)
  (* { move => x. rewrite /f /g.  *)
  (*   case e1: (repr x) => [a|a]. *)
  (*   case e2: (repr a) => [b|b]. *)
  (*   case: piP => y Hy. rewrite /= in Hy. (* why does this take to long? *) *)
  (*   case e3: y => [c|c]. *)
Admitted.

Definition big_seq2 (s : seq graph2) := \big[seq2/one2]_(G <- s) G.

Lemma big_seq2_cons G Gs : big_seq2 (G :: Gs) = seq2 G (big_seq2 Gs).
Proof. by rewrite /big_seq2 big_cons. Qed.
  
Lemma big_seq2_congr (T:finType) (s : seq T) (g1 g2 : T -> graph2) :
  (forall x, x \in s -> g1 x ≈ g2 x) -> 
  big_seq2 [seq g1 x | x <- s] ≈ big_seq2 [seq g2 x | x <- s].
Proof. 
  elim: s => //= a s IH.
Admitted.


Lemma big_seq2_congrs (T:finType) (s : {set T}) (g1 g2 : T -> graph2) :
  (forall x, x \in s -> g1 x ≈ g2 x) -> 
  big_seq2 [seq g1 x | x in s] ≈ big_seq2 [seq g2 x | x in s].
Proof. 
  move => A. apply: big_seq2_congr => x. by rewrite mem_enum => /A.
Qed.

Lemma big_seq2_map (I : Type) (r : seq I) F : 
  big_seq2 [seq graph_of_term (F u) | u <- r] ≈ 
  graph_of_term (\big[tmS/tm1]_(u <- r) F u).
Proof.
  elim: r => /= [|a r IH].
  - by rewrite /big_seq2 !big_nil.
  - by rewrite big_cons big_seq2_cons /= IH.
Qed.

(* TOTHINK: This Lemma matches the Proof below, but does it really
order the element of r in the same way *)
Lemma big_seq2_maps (I : finType) (r : {set I}) F : 
  big_seq2 [seq graph_of_term (F u) | u in r] ≈ 
  graph_of_term (\big[tmS/tm1]_(u in r) F u).
Proof. by rewrite big_seq2_map -filter_index_enum big_filter. Qed.

Instance dom2_morphism : Proper (iso2 ==> iso2) dom2.
Admitted.

Local Notation IO := ([set g_in; g_out]).

Lemma iso_split_par2 (G : graph2) (C D : {set G}) 
  (Ci : g_in \in C) (Co : g_out \in C) (Di : g_in \in D) (Do : g_out \in D) :
  C :&: D \subset IO -> C :|: D = setT -> 
  edge_set C :&: edge_set D = set0 -> edge_set C :|: edge_set D = setT ->
  G ≈ (par2 (point (induced C) (Sub g_in Ci) (Sub g_out Co)) 
            (point (induced D) (Sub g_in Di) (Sub g_out Do))).
Proof.
  move => subIO fullCD disjE fullE.
  set G' := par2 _ _.
  have decV (v : G) : ((v \in C) + (v \in D))%type.
  { admit. }
  have decE (e : edge G) : ((e \in edge_set C) + (e \in edge_set D))%type.
  { admit. }
  pose f (x : G) : G' := 
    match decV x with 
    | inl p => \pi_(_) (inl (Sub x p)) 
    | inr p => \pi_(_) (inr (Sub x p))
    end.
  (* do NOT use simpl *)
  pose h (e : edge G) : edge G' := 
    match decE e with 
    | inl p => inl (Sub e p)
    | inr p => inr (Sub e p)
    end.
  exists (f,h).
Admitted.


Lemma graph_of_big_tmI (T : eqType) (r : seq T) F : 
  graph_of_term (\big[tmI/tmT]_(x <- r) F x) ≈
  \big[par2/top2]_(x <- r) graph_of_term (F x).
Proof. elim: r => [|i r IH]; by rewrite ?big_nil ?big_cons /= ?IH. Qed.

Lemma graph_of_big_tmIs (T : finType) (r : {set T}) F : 
  graph_of_term (\big[tmI/tmT]_(x in r) F x) ≈
  \big[par2/top2]_(x in r) graph_of_term (F x).
Proof. by rewrite -!big_enum_in graph_of_big_tmI. Qed.

Lemma big_iso_congr op (con : iso2_congruence op) 
  (T : eqType) (s : seq T) idx F G : 
  (forall x, x \in s -> F x ≈ G x) ->
  \big[op/idx]_(x <- s) F x ≈ \big[op/idx]_(x <- s) G x.
Proof. 
  move => A. 
  elim: s A => [_|i s IH /all_cons [A B]]; first by rewrite !big_nil. 
  rewrite !big_cons. apply: con => //. exact: IH.
Qed.

Definition big_par2_congr' := big_iso_congr par2_congr.

Lemma iso_top (G : graph2) :
  g_in != g_out :> G -> 
  (forall x : G, x \in IO) -> 
  (forall e : edge G, False) -> G ≈ top2.
Proof.
  move => Dio A B. 
  pose f (x : G) : top2 := 
    if x == g_in then g_in else g_out.
  pose f' (x : top2) : G := 
    if x == g_in then g_in else g_out.
  pose g (e : edge G) : edge top2 := 
    match (B e) with end.
  pose g' (e : edge top2) : edge G := 
    match e with end.
  exists (f,g); repeat split => //=. 
  - by rewrite /f eqxx.
  - by rewrite /f eq_sym (negbTE Dio).
  - apply: (Bijective (g := f')) => x; rewrite /f /f'. 
    + case: (boolP (x == g_in)) => [/eqP <-|/=]; first by rewrite eqxx.
      move: (A x). case/setUP => /set1P => -> //. by rewrite eqxx.
    + case: (boolP (x == g_in)) => [/eqP <-|/=]; first by rewrite eqxx.
      case: x => // _. by rewrite eq_sym (negbTE Dio).
  - by apply: (Bijective (g := g')).
Qed.

Lemma iso_one (G : graph2) :
  g_in == g_out :> G -> 
  (forall x : G, x \in IO) -> 
  (forall e : edge G, False) -> G ≈ one2.
Proof.
  move => Dio A B. 
  pose f (x : G) : one2 := g_in.
  pose f' (x : one2) : G := g_in.
  pose g (e : edge G) : edge one2 := 
    match (B e) with end.
  pose g' (e : edge one2) : edge G := 
    match e with end.
  exists (f,g); repeat split => //=. 
  - apply: (Bijective (g := f')) => x; rewrite /f /f'.  
    move: (A x). rewrite !inE -(eqP Dio) => /orP. by case => /eqP->.
    by case: x.
  - by apply: (Bijective (g := g')).
Qed.