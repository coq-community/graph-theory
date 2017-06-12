From mathcomp Require Import all_ssreflect.
Require Import finite_quotient preliminaries.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 


(** * Simple Graphs *)

Record sgraph := SGraph { svertex :> finType ; 
                         sedge: rel svertex; 
                         sg_sym: symmetric sedge;
                         sg_irrefl: irreflexive sedge}.

Record sgraph2 := SGraph2 { sgraph_of :> sgraph; 
                            s_in : sgraph_of; 
                            s_out : sgraph_of}.

Arguments s_in [s].
Arguments s_out [s].
Notation "x -- y" := (sedge x y) (at level 30).
Definition sgP := (sg_sym,sg_irrefl).
Prenex Implicits sedge.

(** ** Homomorphisms *)

Definition hom_s2 (G1 G2 : sgraph2) (h : G1 -> G2) :=
  [/\ {homo h : x y / x -- y}, h s_in = s_in & h s_out = s_out].

(** ** Forests *)

(** We define forests to be simple graphs where there exists at most one
duplicate free path between any two nodes *)

Definition upath (T : eqType) e (x y : T) p := 
  [/\ uniq (x::p), path e x p & last x p = y].

Definition tree_axiom (T:eqType) (e : rel T) :=
  forall (x y : T), unique (upath e x y).
  
Record tree := Tree { sgraph_of_tree :> sgraph ; 
                      treeP : tree_axiom (@sedge sgraph_of_tree)}.


Lemma rev_upath (G : sgraph) (x y : G) p : 
  upath sedge x y p -> upath sedge y x (rev (belast x p)).
Proof.
  case => A B C. split.
  - rewrite -C. by rewrite -cat1s -rev_uniq rev_cat revK cats1 -lastI.
  - rewrite -C rev_path (eq_path (e' := sedge)) //. move => a b /=. exact: sg_sym.
  - case: p C {A B} => //= a p _. by rewrite rev_cons last_rcons.
Qed.

Lemma upath_sym (G : sgraph) (x y : G) : 
  unique (upath sedge x y) -> unique (upath sedge y x).
Proof. 
  move => U p q Hp Hq. case: (Hp) => _ _ A. case: (Hq) => _ _ B.
  apply: rev_belast (U _ _ (rev_upath Hp) (rev_upath Hq)). by subst.
Qed.

Require Setoid Morphisms.
Import Morphisms.
Instance and3_mor : Proper (@iff ==> @iff ==> @iff ==> @iff) and3.
Proof. firstorder. Qed.

Lemma upath_cons (T : eqType) (e : rel T) x y a p : 
  upath e x y (a::p) <-> [/\ e x a, x != a, x \notin p & upath e a y p].
Proof.
  rewrite /upath /= !inE negb_or. rewrite -!(rwP and3P). rewrite -2!(rwP andP). 
  split. firstorder.  firstorder; by case/andP : H2. (* FIXME: why does -!(rwP andP) fail ?? *)
Qed.

Lemma upath_refl (T : eqType) (e : rel T) x : upath e x x [::].
Proof. done. Qed.

Lemma upath_nil (T : eqType) (e : rel T) x p : upath e x x p -> p = [::].
Proof. case: p => //= a p [/= A B C]. by rewrite -C mem_last in A. Qed.

Lemma upath_split (T : finType) (e : rel T) (x y z : T) p q : 
  upath e x y (rcons p z ++ q) -> 
  [/\ upath e x z (rcons p z), upath e z y q & [disjoint x::rcons p z & q]].
Proof.
  rewrite {1}/upath last_cat cat_path last_rcons => [[A /andP [B C] D]]. 
  move: A. rewrite -cat_cons cat_uniq => /and3P [E F G]. split. 
  - split => //. by rewrite last_rcons.
  - split => //=. rewrite G andbT. apply: contraNN F => H. 
    apply/hasP. exists z => //=. by rewrite !inE mem_rcons mem_head orbT.
  - by rewrite disjoint_sym disjoint_has.
Qed.

Lemma lift_upath (aT rT : finType) (e : rel aT) (e' : rel rT) (f : aT -> rT) a b p' : 
  (forall x y : aT, e' (f x) (f y) -> e x y) -> injective f -> 
  upath e' (f a) (f b) p' -> {subset p' <= codom f} -> exists p, upath e a b p /\ map f p = p'.
Proof.
  move => lift_e inj_f [p1 p2 p3] Sp'. case (lift_path lift_e p2 Sp') => p [P0 P1]; subst. 
  exists p. split => //. move: p3. rewrite last_map => /inj_f => p3. split => //.
  by rewrite -(map_inj_uniq inj_f).
Qed.


(** ** Disjoint Union *)

Section JoinSG.
  Variables (G1 G2 : sgraph).
  
  Definition join_rel (a b : G1 + G2) := 
    match a,b with
    | inl x, inl y => x -- y
    | inr x, inr y => x -- y
    | _,_ => false
    end.

  Lemma join_rel_sym : symmetric join_rel.
  Proof. move => [x|x] [y|y] //=; by rewrite sg_sym. Qed.

  Lemma join_rel_irrefl : irreflexive join_rel.
  Proof. move => [x|x] //=; by rewrite sg_irrefl. Qed.

  Definition sjoin := SGraph join_rel_sym join_rel_irrefl. 

  Lemma join_disc (x : G1) (y : G2) : connect join_rel (inl x) (inr y) = false.
  Proof. 
    apply/negP. case/connectP => p. elim: p x => // [[a|a]] //= p IH x.
    case/andP => _. exact: IH. 
  Qed.

End JoinSG.

Prenex Implicits join_rel.


(** Covering is not really required, but makes the renaming theorem easier to state *)
Record sdecomp (T:tree) (G : sgraph) (bag : T -> {set G}) := SDecomp
  { sbag_cover x : exists t, x \in bag t; 
    sbag_edge x y : x -- y -> exists t, (x \in bag t) && (y \in bag t);
    sbag_conn x t1 t2  : x \in bag t1 -> x \in bag t2 ->
      connect (restrict [pred t | x \in bag t] sedge) t1 t2}.

Arguments sdecomp T G bag : clear implicits.