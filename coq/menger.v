From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries path set_tac.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Preliminaries *)

Lemma irred_ind (G : relType) (P : forall x x0 : G, Path x x0 -> Type) (y : G) (x : G) (p : Path x y) : 
  P y y (idp y) ->
  (forall (x z : G) (p : Path z y) (xz : x -- z),
      irred p -> x \notin p -> P z y p -> P x y (pcat (edgep xz) p)) ->
  irred p -> P x y p.
Proof. move => A B C. exact: irred_ind. Qed.

Definition uncurry (aT rT : Type) (P : aT -> Type) (f : forall (x : aT), P x -> rT) (a : { aT & P aT }) := 
  @f (tag a) (tagged a).

Record mGraph := MGraph { vertex : finType;
                          edge: finType;
                          source : edge -> vertex;
                          target : edge -> vertex }.

Definition mgraph_rel (G : mGraph) : rel (vertex G) := 
  fun x y => [exists e, (source e == x) && (target e == y)].

Definition mgraph_relType (G : mGraph) := DiGraph (@mgraph_rel G).
Coercion mgraph_relType : mGraph >-> diGraph.

Section Connector.
Variables (G : diGraph).
Implicit Types (x y : G) (A B S : {set G}).

Definition pathS := { x : G * G & Path x.1 x.2 }.
Definition PathS x y (p : Path x y) : pathS := existT (fun x : G * G => Path x.1 x.2) (x,y) p.

Definition in_pathS (p : pathS) := [pred x | x \in tagged p].
Canonical pathS_predType := Eval hnf in mkPredType (@in_pathS).

Arguments in_pathS _ /.

(* We can override fst because MathComp uses .1 *)
Definition fst (p : pathS) := (tag p).1.
Definition lst (p : pathS) := (tag p).2.

Arguments fst _ /.
Arguments lst _ /.

Definition irredS : (pathS -> Prop) := uncurry (fun (x : G * G) (p : Path x.1 x.2) => irred p).
Definition nodesS : (pathS -> seq G) := uncurry (fun (x : G * G) (p : Path x.1 x.2) => nodes p).

Arguments uncurry aT rT P _ _ /.
Arguments irredS _ /.
Arguments nodesS _ /.

(* Arguments PathS x y _ /. *)

Record connector (A B : {set G}) n (p : 'I_n -> pathS) : Prop := 
  { conn_irred    : forall i, irredS (p i);
    conn_begin    : forall i, [set x in p i] :&: A = [set fst (p i)];
    conn_end      : forall i, [set x in p i] :&: B = [set lst (p i)];
    conn_disjoint :  forall i j, i != j -> [set x in p i] :&: [set x in p j] = set0 }.

Definition separator (A B S : {set G}) :=
  forall (a b : G) (p : Path a b), a \in A -> b \in B -> exists2 s, s \in S & s \in p.

Lemma separatorI A B S : 
  (forall (a b : G) (p : Path a b), irred p -> a \in A -> b \in B -> exists2 s, s \in S & s \in p)
  -> separator A B S.
Proof. 
  move => H a b p aA bB. case: (uncycle p) => p' sub_p Ip. case: (H _ _ p') => //.
  move => s sS /sub_p sp. by exists s.
Qed.

Definition separatorb (A B S : {set G}) := 
  [forall a in A, forall b in B, forall p : IPath a b, exists s in S, s \in p].

Lemma separatorP (A B S : {set G}) : reflect (separator A B S) (separatorb A B S).
Proof.
  rewrite /separatorb. apply: (iffP forall_inP) => [H|H a aA].
  - apply: separatorI => a b p Ip aA bB. 
    move/(_ _ aA) : H => /forall_inP /(_ _ bB) /forallP /(_ (Sub p Ip)) /exists_inP [s sS in_p]. by exists s.
  - apply/forall_inP => b bB. apply/forallP => [[p ?]]. apply/exists_inP. 
    case: (H a b p) => // s S1 S2. by exists s.
Qed.

Definition separates x y (S : {set G}) := 
  [/\ x \notin S, y \notin S & forall p : Path x y, exists2 z, z \in p & z \in S].

(* Definition independent x y n (p : 'I_n -> Path x y) :=  *)
(*  (forall i, irred (p i)) /\ (forall i j, i != j -> [set x in p i] :&: [set x in p j] = set0). *)

Lemma separator_cap A B S : 
  separator A B S -> A :&: B \subset S.
Proof.
  move => sepS. apply/subsetP => x /setIP [xA xB]. 
  case: (sepS _ _ (idp x)) => // s in_S. by rewrite mem_idp => /eqP <-.
Qed.  

Lemma separator_min A B S : 
  separator A B S -> #|A :&: B| <= #|S|.
Proof. move/separator_cap. exact: subset_leq_card. Qed.

Lemma connector_replace A B n (p : 'I_n -> pathS) x y i : 
  x \notin \bigcup_i [set z in p i] -> fst (p i) = y -> x -- y ->
  connector A B p -> exists q : 'I_n -> pathS, connector (x |: (A :\ y)) B q.
Admitted.

Lemma connector_cat (P A B : {set G}) n (p q : 'I_n -> pathS) : 
  #|P| = n -> separator A B P ->
  connector A P p -> connector P B q -> 
  exists (r : 'I_n -> pathS), connector A B r.
Admitted. (* Induction on n, using the fact that p and q cover P *)

Lemma trivial_connector A B : exists p : 'I_#|A :&: B| -> pathS, connector A B p.
Proof.
  exists (fun i => PathS (idp (enum_val i))). split.
  - move => i /=. exact: irred_idp.
  - move => i /=. case/setIP : (enum_valP i) => iA iB. apply/setP => z.
    rewrite !inE /= mem_idp. case e: (_ == _) => //. by rewrite (eqP e).
  - move => i /=. case/setIP : (enum_valP i) => iA iB. apply/setP => z.
    rewrite !inE /= mem_idp. case e: (_ == _) => //. by rewrite (eqP e).
  - move => i j. apply: contraNeq => /set0Pn [x /setIP[]]. 
    by rewrite !inE /= !mem_idp => /eqP-> /eqP /enum_val_inj->. 
Qed.

Lemma sub_connector A B n m (p : 'I_m -> pathS) : 
  n <= m -> connector A B p -> exists q : 'I_n -> pathS, connector A B q.
Proof.
  move => n_leq_m conn_p. pose W := widen_ord n_leq_m. exists (fun i => p (W i)).
  case: conn_p => C1 C2 C3 C4. split => // i j. exact:(C4 (W i) (W j)).
Qed.

End Connector.

Lemma nat_size_ind (X : Type) (P : X -> Type) (x : X) (f : X -> nat) :
       (forall x : X, (forall y : X, f y < f x -> P y) -> P x) -> P x.
Admitted.

Lemma subrel_pathp (T : finType) (e1 e2 : rel T) (x y : T) (p : seq T) :
  subrel e1 e2 -> @pathp (DiGraph e1) x y p -> @pathp (DiGraph e2) x y p.
Proof. 
  move => sub12. elim: p x => //= z p IHp x. rewrite !pathp_cons => /andP [A B].
  apply/andP;split; [exact: sub12 | exact: IHp].
Qed.

Arguments nat_size_ind [X] [P] [x] f.
Arguments separator : clear implicits.
Arguments separatorb : clear implicits.

Definition num_edges (G : diGraph) := #|[pred x : G * G | x.1 -- x.2]|.

Lemma subrelP (T : finType) (e1 e2 : rel T) : 
  reflect (subrel e1 e2) ([pred x | e1 x.1 x.2] \subset [pred x | e2 x.1 x.2]).
Proof. apply: (iffP subsetP) => [S x y /(S (x,y)) //|S [x y]]. exact: S. Qed.


Section DelEdge.

Notation PATH G x y := (@Path G x y). 
Notation IPATH G x y := (@IPath G x y). 

Variable (G : diGraph) (a b : G).

Definition del_rel a b := [rel x y : G | x -- y && ((x != a) || (y != b))].

Definition del_edge := DiGraph (del_rel a b).

Definition subrel_del_edge : subrel (del_rel a b) (@edge_rel G).
Proof. by move => x y /andP []. Qed.

Hypothesis ab : a -- b.

Lemma card_del_edge : num_edges del_edge < num_edges G.
Proof.
  apply: proper_card. apply/properP; split.
  - apply/subrelP. exact: subrel_del_edge. 
  - exists (a,b); by rewrite !inE //= !eqxx.
Qed.

(* Lemma del_edge_unlift (x y : G) (p : Path x y) :  *)
(*   (a \notin p) || (b \notin p) -> exists p' : @Path del_edge x y, nodes p = nodes p'. *)
(* Admitted.  *)

(* Lemma del_edge_unlift_loop (x y : G) (p : Path x y) :  *)
(*   a = b -> exists p' : @Path del_edge x y, nodes p = nodes p'. *)
(* Admitted. *)

(** This is the fundamental case analysis for irredundant paths in [G] in
terms of paths in [del_edge a b] *)

(** TOTHINK: The proof below is a slighty messy induction on
[p]. Informally, one would simply check wether [nodes p] contains and
[a] followed by a [b] *)
Lemma del_edge_path_case (x y : G) (p : Path x y) (Ip : irred p) :
    (exists (p1 : @IPath del_edge x a) (p2 : @IPath del_edge b y), 
        [/\ nodes p = nodes p1 ++ nodes p2, a \notin p2 & b \notin p1])
  \/ (exists p1 : @IPath del_edge x y, nodes p = nodes p1).
Proof.
  pattern x, y, p. set P := (fun _ _ _ => _). apply irred_ind => //; unfold P in *.
  - move => {P p Ip}. 
    have Ip : irred (@idp del_edge y) by apply: irred_idp. by right;exists (Sub _ Ip).
  - move => {x p Ip P} x z p xz Ip xp [[p1] [p2] [A B C]|[p1] E].
    + left. 
      have xyD : (x:del_edge) -- z. 
      { rewrite /edge_rel/= xz (_ : x != a) //. apply: contraNneq xp => -> .
        by rewrite mem_path A mem_cat -(@mem_path del_edge) path_end. }
      have Iq : irred (pcat (edgep xyD) p1). 
      { rewrite irred_edgeL (valP p1) andbT. 
        rewrite mem_path A mem_cat -(@mem_path del_edge) negb_or in xp.
        by case/andP : xp. }
      exists (Sub _ Iq). exists p2. split => //. 
      * by rewrite /= !nodes_pcat A [nodes p1](nodesE) /= -catA. 
      * change (b \notin pcat (edgep xyD) p1). 
        rewrite (@mem_pcat del_edge) (negbTE C) orbF mem_edgep negb_or.
        rewrite irred_edgeL in Iq. apply/andP; split.
        -- apply: contraNneq xp => <-. 
           by rewrite mem_path A mem_cat -!(@mem_path del_edge) path_begin.
        -- apply: contraTneq Ip => ?. subst z. 
           rewrite irredE A cat_uniq [has _ _](_ : _ = true) //. 
           apply/hasP. by exists b => /=; rewrite -!(@mem_path del_edge) path_begin.
    + case: (boolP ((x : del_edge) -- z)) => [xzD|xzND].
      * right. 
        have Iq : irred (pcat (edgep xzD) p1). 
        { by rewrite irred_edgeL (valP p1) mem_path -E -(@mem_path G) xp. }
        exists (Sub _ Iq). by rewrite !nodes_pcat E. 
      * left. rewrite /edge_rel/= xz /= negb_or !negbK in xzND. 
        case/andP : xzND => /eqP ? /eqP ?. subst x. subst z. 
        have Iq : irred (@idp del_edge a) by apply: irred_idp.
        exists (Sub _ Iq). exists p1. split => //=. 
        -- by rewrite nodes_pcat E [nodes p1]nodesE /= -cat1s catA !nodesE. 
        -- by rewrite (@mem_path del_edge) -E -(@mem_path G).
        -- rewrite (@mem_path del_edge) nodesE /= inE. 
           apply: contraNneq xp => <-. 
           by rewrite mem_path E -(@mem_path del_edge) path_begin.
Qed.

End DelEdge.

Arguments uncurry aT rT P _ _ /.
Arguments irredS _ _ /.
Arguments nodesS _ _ /.


Lemma del_edge_lift_proof (G : diGraph) (a b x y : G) p : 
  @pathp (del_edge a b) x y p -> @pathp G x y p.
Proof. case: G a b x y p => T e a b x y p. apply: subrel_pathp. exact: subrel_del_edge. Qed.

Definition del_edge_liftS (G : diGraph) (a b : G) (p : pathS (del_edge a b)) :=
  let: existT (x,y) p' := p in PathS (Build_Path (del_edge_lift_proof (valP p'))).

Lemma connector_nodes (T : finType) (e1 e2 : rel T) (A B : {set T}) : 
  forall s (p : 'I_s -> pathS (DiGraph e1)) (q : 'I_s -> pathS (DiGraph e2)), 
  (forall i, nodes (tagged (p i)) = nodes (tagged (q i)) :> seq T) -> 
  @connector (DiGraph e1) A B s p -> @connector (DiGraph e2) A B s q.
Proof.
  set G1 := DiGraph e1. set G2 := DiGraph e2.
  move => s p q Epq [C1 C2 C3 C4]. 
  have Spq : forall i, [set x in p i] = [set x in q i]. 
  { move => i. apply/setP => z. by rewrite !inE !mem_path Epq. }
  split.
  - move => i /=. rewrite irredE -Epq -(@irredE G1). exact: C1.
  - move => i /=. rewrite -Spq C2. f_equal. 
    move: (Epq i). case: (p i) => [[x y] pi]. case: (q i) => [[x' y'] qi].
    rewrite /fst /=. rewrite !nodesE. by case.
  - move => i /=. rewrite -Spq C3. f_equal. 
    move: (Epq i). case: (p i) => [[x y] pi]. case: (q i) => [[x' y'] qi].
    rewrite /lst /= in pi qi *. rewrite !nodesE => [[E1 E2]]. 
    by rewrite -(path_last pi) -(path_last qi) /= E2 E1.
  - move => i j /C4. by rewrite -!Spq.
Qed.
 
Lemma del_edge_connector (G : diGraph) (a b : G) (A B : {set G}) s (p : 'I_s -> pathS (del_edge a b)) : 
  @connector (del_edge a b) A B s p -> connector A B (fun i : 'I_s => del_edge_liftS (p i)).
Proof.
  destruct G. apply: connector_nodes => i. 
  case: (p i) => [[x y] pi] /=. by rewrite !nodesE. 
Qed.

Theorem Menger (G : diGraph) (A B : {set G}) s : 
  (forall S, separator G A B S -> s <= #|S|) -> exists (p : 'I_s -> pathS G), connector A B p.
Proof.
  move: s A B. pattern G. apply: (nat_size_ind num_edges) => {G}.
  move => G IH s A B min_s. 
  case: (boolP [exists x : G, exists y : G, x -- y]) => [E|E0]; last first.
  - suff Hs : s <= #|A :&: B|. 
    { case: (trivial_connector A B) => p. exact: sub_connector. }
    apply: min_s => a b p aA bB. 
    (* If a != b then p must have an edge, contradition *) admit.
  - case/existsP : E => x /existsP [y xy].
    pose G' := del_edge x y.
    have HG' : num_edges G' < num_edges G by exact: card_del_edge. 
    move/(_ _ HG' s) in IH.
    case: (boolP [exists S : {set G'}, separatorb G' A B S && (#|S| < s)]); last first.
    { move/exists_inPn => Hs. case: (IH A B) => [S sepS|p conn_p].
      - rewrite leqNgt Hs //. exact/separatorP. 
      - exists (fun i : 'I_s => del_edge_liftS (p i)). exact: del_edge_connector. }
    case/exists_inP => S /separatorP sepS ltn_s. 
    pose P := x |: S.
    have ? : x \in P by rewrite /P; set_tac.
    pose Q := y |: S.
    have sep_G_P : separator G A B P. 
    { apply: separatorI => a b p Ip aA bB. case: (del_edge_path_case x y Ip).
      - move => [p1] [p2] [H1 H2 H3]. exists x. by rewrite /P ; set_tac.
        rewrite mem_path H1 mem_cat. by rewrite -(@mem_path G') path_end.
      - move => [p1 Ep]. case/sepS : (p1) => // z Z1 Z2. exists z => //. by rewrite/P; set_tac.
        by rewrite mem_path Ep -(@mem_path G'). }
    have sep_G_Q : separator G A B Q.
    { (* same as above *) admit. }
    have lift_AP T : separator G' A P T -> separator G A B T.
    { move => sepT. apply/separatorI => a b p Ip aA bB. 
      case/sep_G_P : (p) => // z zP zp. case: (del_edge_path_case x y Ip).
      - move => [p1] [p2] [E Nx Ny]. case/sepT : (p1) => // t. admit.
      - case. case => p' Ip' /= E. 
        have zp' : z \in p'. admit. 
        case: (split_at_first (D := G') zP zp') => u [p1] [p2] [E' uP ?].
        case/sepT : (p1) => // t tT tp1. exists t => //. 
        by rewrite mem_path E -(@mem_path G') E' mem_pcat tp1. }
    have lift_QB T : separator G' Q B T -> separator G A B T.
    { (* same as above *) admit. }
    have size_AP T : separator G' A P T -> s <= #|T|. move/lift_AP. exact: min_s.
    have size_QB T : separator G' Q B T -> s <= #|T|. move/lift_QB. exact: min_s.
    case: (IH _ _ size_AP) => X /del_edge_connector conn_X.
    case: (IH _ _ size_QB) => Y /del_edge_connector conn_Y.
    case: (altP (x =P y)) => [?|xDy].
    - subst y. 
      apply: connector_cat conn_X conn_Y => //. admit.
    - admit.
Admitted.

Require Import sgraph.

Theorem Menger_sgraph (G : sgraph) (A B : {set G}) s : 
  (forall S, separator G A B S -> s <= #|S|) -> exists (p : 'I_s -> pathS G), connector A B p.
Proof. exact: Menger. Qed. 

Corollary theta (G : sgraph) (x y : G) s :
  ~~ x -- y ->
  (forall S, separates x y S -> s <= #|S|) -> 
  exists (p : 'I_s -> Path x y), forall i j : 'I_s, i != j -> independent (p i) (p j).
Proof.
Admitted.