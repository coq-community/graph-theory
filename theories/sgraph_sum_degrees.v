From mathcomp Require Import all_ssreflect.
Require Import preliminaries digraph sgraph connectivity dom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(** Preliminaries *)

Lemma edges_opn0 (G : sgraph) (x : G) : E(G) = set0 -> #|N(x)| = 0.
Proof.
move => E0; apply: eq_card0 => y; rewrite !inE; apply: contra_eqF E0 => xy.
by apply/set0Pn; exists [set x;y]; rewrite in_edges.
Qed.

Lemma edges_eqn_sub (G : sgraph) (e1 e2 : {set G}) : 
  e1 \in E(G) -> e2 \in E(G) -> e1 != e2 -> ~~ (e1 \subset e2).
Proof.
move => /edgesP [x1 [y1 [-> xy1]]] /edgesP [x2 [y2 [-> xy2]]].
apply/contraNN; rewrite subUset !sub1set !inE => EQS.
case/andP : EQS xy1 xy2 => /pred2P[->|->] /pred2P [->|->].
all: by rewrite ?sg_irrefl // setUC.
Qed.

Notation "N( G ; x )" := (@open_neigh G x)
   (at level 0, G at level 99, x at level 99, format "N( G ; x )") : implicit_scope.


(** ** Edge Deletion for Simple Graphs *)

Section del_edges.
Variables (G : sgraph) (A : {set G}).

Definition del_edges_rel := [rel x y : G | x -- y && ~~ ([set x;y] \subset A)]. 

Definition del_edges_sym : symmetric del_edges_rel. 
Proof. by move=>x y /=; rewrite sgP setUC. Qed.

Definition del_edges_irrefl : irreflexive del_edges_rel.
Proof. by move=> x /=; rewrite sgP. Qed.

Definition del_edges := SGraph del_edges_sym del_edges_irrefl.
End del_edges.

Section del_edges_facts.
Variables (G : sgraph).
Implicit Types (x y z : G) (A e : {set G}).

Local Open Scope implicit_scope.

Lemma mem_del_edges e A : e \in E(del_edges A) = (e \in E(G)) && ~~ (e \subset A).
Proof.
apply/edgesP/andP => [[x] [y] [-> /andP[xy xyA]]|[]]; first by rewrite in_edges.
by move/edgesP => [x] [y] [-> xy xyNA]; exists x,y; split => //; apply/andP.  
Qed.

(** Neighborhood version of the above *)
Lemma del_edges_opn A x z : 
  z \in N(del_edges A;x) = (z \in N(G;x)) && ~~ ([set x; z] \subset A).
Proof. by rewrite !inE -in_edges mem_del_edges in_edges. Qed.

Lemma del_edges_sub A : E(del_edges A) \subset E(G).
Proof. by apply/subsetP => e; rewrite mem_del_edges => /andP[]. Qed.

Lemma del_edges_proper e A : 
  e \in E(G) -> e \subset A -> E(del_edges A) \proper E(G).
Proof.
move=> edge_e e_sub_A. rewrite properE del_edges_sub /=.
by apply/subsetPn; exists e => //; rewrite mem_del_edges edge_e e_sub_A.
Qed.

(** Two useful lemmas for the case of deleting a single edge *)
Lemma del_edgesN e : e \notin E(del_edges e).
Proof. by rewrite mem_del_edges subxx andbF. Qed.

Lemma del_edges1 e : e \in E(G) -> E(G) = e |: E(del_edges e).
Proof.
move => edge_e; apply/setP => e'; rewrite in_setU mem_del_edges in_set1.
case: (eqVneq e e') => [<-//|eDe'/=].
case: (boolP (e' \in E(G))) => //= edge_e'; symmetry. 
rewrite eq_sym in eDe'; exact: edges_eqn_sub eDe'.
Qed.

End del_edges_facts.

Local Open Scope implicit_scope.

Theorem edges_sum_degrees (G : sgraph) : 2 * #|E(G)| = \sum_(x in G) #|N(x)|.
Proof.
elim/(size_ind (fun G => #|E(G)|)) : G => G IH.
case: (set_0Vmem E(G)) => [E0|[e edge_e]].
- rewrite E0 cards0 muln0. 
  under eq_bigr => x do rewrite edges_opn0 //.
  by rewrite sum_nat_const muln0.
- have [x [y] [def_e xy]] := edgesP _ edge_e; set G' := del_edges e.
  have/IH E' : #|E(G')| < #|E(G)|.
  { by apply: proper_card; exact: del_edges_proper edge_e _. }
  rewrite (del_edges1 edge_e) cardsU1 del_edgesN mulnDr /= muln1 {}E' /=.
  rewrite [in LHS](bigID (mem e)) [in RHS](bigID (mem e)) /= addnA.
  congr (_ + _); last first.
  { apply eq_bigr => z zNe; apply eq_card => w. 
    by rewrite del_edges_opn subUset sub1set (negbTE zNe) /= andbT. }
  rewrite def_e !big_setU1 ?inE ?sg_edgeNeq //= !big_set1.
  suff Ne w : w \in e -> #|N(G';w)|.+1 = #|N(G;w)|.
  { rewrite -!Ne ?def_e ?in_set2 ?eqxx ?orbT //.
    by rewrite [RHS]addSn [in RHS]addnS add2n. }
  rewrite {}/G' {}def_e => {edge_e} w_in_xy.
  wlog w_is_x : x y xy {w_in_xy} / w = x.
  { move => W. case/set2P : w_in_xy; first exact: W.
    by rewrite setUC; apply: W; rewrite sgP. }
  subst w; suff -> : N(G;x) = y |: N(del_edges [set x;y];x). 
  { by rewrite cardsU1 del_edges_opn subxx andbF add1n. }
  apply/setP => z; rewrite 2!inE del_edges_opn !inE. 
  rewrite subUset subsetUl sub1set !inE /=. 
  case: (eqVneq z y) => [-> //|zDy /=]. 
  case: (eqVneq z x) => [->|]; by rewrite ?sg_irrefl //= ?orbT ?andbT.
Qed.
