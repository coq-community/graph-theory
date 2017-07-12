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

Definition hom_s (G1 G2 : sgraph) (h : G1 -> G2) := 
  forall x y, x -- y -> (h x = h y) \/ (h x -- h y).

Definition hom_s2 (G1 G2 : sgraph2) (h : G1 -> G2) :=
  [/\ hom_s h , h s_in = s_in & h s_out = s_out].

(** ** Forests *)

(** We define forests to be simple graphs where there exists at most one
duplicate free path between any two nodes *)

Definition upath (T : eqType) e (x y : T) p := 
  [/\ uniq (x::p), path e x p & last x p = y].

Definition tree_axiom (T:eqType) (e : rel T) :=
  forall (x y : T), unique (upath e x y).
  
Record tree := Tree { sgraph_of_tree :> sgraph ; 
                      treeP : tree_axiom (@sedge sgraph_of_tree)}.

Lemma rev_spath (G : sgraph) (x y : G) p : 
  path sedge x p -> last x p = y -> path sedge y (rev (belast x p)).
Proof. 
  move => B <-. rewrite rev_path (eq_path (e' := sedge)) //.
  move => a b /=. exact: sg_sym.
Qed.

Lemma last_rev_belast (G : finType) (x y : G) p : 
  last x p = y -> last y (rev (belast x p)) = x.
Proof. case: p => //= a p _. by rewrite rev_cons last_rcons. Qed.

Lemma rev_upath (G : sgraph) (x y : G) p : 
  upath sedge x y p -> upath sedge y x (rev (belast x p)).
Proof.
  case => A B C. split; [|exact: rev_spath|exact: last_rev_belast].
  rewrite -C. by rewrite -cat1s -rev_uniq rev_cat revK cats1 -lastI.
Qed.

Lemma upath_sym (G : sgraph) (x y : G) : 
  unique (upath sedge x y) -> unique (upath sedge y x).
Proof. 
  move => U p q Hp Hq. case: (Hp) => _ _ A. case: (Hq) => _ _ B.
  apply: rev_belast (U _ _ (rev_upath Hp) (rev_upath Hq)). by subst.
Qed.

Lemma upath_cons (T : eqType) (e : rel T) x y a p : 
  upath e x y (a::p) <-> [/\ e x a, x != a, x \notin p & upath e a y p].
Proof.
  rewrite /upath /= !inE negb_or -!andbA; split.
  + by move => [/and4P [? -> -> ?] /andP[? ?]] ?. 
  + by move => [-> -> ->] [-> -> ->].
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


Lemma upathP (T:finType) (e : rel T) x y : 
  reflect (exists p, upath e x y p) (connect e x y).
Proof.
  apply: (iffP connectP) => [[p p1 p2]|[p [p1 p2 p3]]]; last by exists p.
  exists (shorten x p). by case/shortenP : p1 p2. 
Qed.

Lemma upath_mono (T:eqType) (e e' : rel T) x y p : 
  subrel e e' -> upath e x y p -> upath e' x y p.
Proof. move => ? [? pth_p ?]. split => //. exact: sub_path pth_p. Qed.

Lemma upath_restrict (T:eqType) (e : rel T) (a : pred T) x y p :
  upath (restrict a e) x y p -> upath e x y p.
Proof. apply: upath_mono. exact: subrel_restrict. Qed.

Lemma restrict_tree (T : tree) (A : pred T) : 
  connect_sym (restrict A sedge).
Proof. apply: connect_symI => x y /=. by rewrite sgP [(x \in A) && _]andbC. Qed.


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

(** ** Tree Decompositions *)


(** Covering is not really required, but makes the renaming theorem easier to state *)
Record sdecomp (T:tree) (G : sgraph) (bag : T -> {set G}) := SDecomp
  { sbag_cover x : exists t, x \in bag t; 
    sbag_edge x y : x -- y -> exists t, (x \in bag t) && (y \in bag t);
    sbag_conn x t1 t2  : x \in bag t1 -> x \in bag t2 ->
      connect (restrict [pred t | x \in bag t] sedge) t1 t2}.

Arguments sdecomp T G bag : clear implicits.

(** Non-standard: we do not substract 1 *)
Definition width (T G : finType) (D : T -> {set G}) := \max_(t:T) #|D t|.


Definition subtree (T : tree) (A : {set T}) :=
  {in A&A, forall (x y : T) p, upath sedge x y p -> {subset p <= A}}.

Lemma subtree_connect (T : tree) (c : T) (a : pred T) : 
  subtree [set c' | connect (restrict a sedge) c c'].
Proof.
  move => u u' H1 H2 p H3.
  have/upathP [q pth_q] : connect (restrict a sedge) u u'.
  { apply: (connect_trans (y := c)).
    - by rewrite restrict_tree inE in H1 *.
    - by rewrite inE in H2. }
  have -> : p = q. { move/upath_restrict : pth_q. exact: treeP H3. }
  move => c' in_q. case: (path.splitP in_q) pth_q => p1 p2. 
  case/upath_split => H _ _. rewrite inE. 
  apply: (connect_trans (y := u)); first by rewrite inE in H1.
  apply/upathP. by exists (rcons p1 c'). 
Qed.

Lemma subtree_link (T : tree) (C : {set T}) t0 c0 c p : 
  subtree C -> t0 \notin C -> c0 \in C -> t0 -- c0 -> c \in C -> upath sedge t0 c p -> c0 \in p.
Proof.
  move => sub_C H1 H2 H3 H4 H5. 
  have [q Hq] : exists p, upath sedge c0 c p. 
  { apply/upathP. apply: (connect_trans (y := t0)). 
    + apply: connect1. by rewrite sgP.
    + apply/upathP. by exists p. }
  have X : upath sedge t0 c (c0::q). 
  { apply/upath_cons. split => //. 
    + apply/negP=>/eqP ?; subst. by contrab.
    + apply/negP =>/(sub_C c0 c H2 H4 _ Hq) H. by contrab. }
  rewrite (treeP H5 X). exact: mem_head.
Qed.

Lemma disjointE (T : finType) (A B : {set T}) x : 
  [disjoint A & B] -> x \in A -> x \in B -> False.
Proof. by rewrite disjoint_subset => /subsetP H /H /negP. Qed.

Definition clique (G : sgraph) (S : {set G}) :=
  {in S&S, forall x y, x != y -> x -- y}.                                  

Section DecompTheory.
  Variables (G : sgraph) (T : tree) (B : T -> {set G}).
  Implicit Types (t u v : T) (x y z : G).

  Hypothesis decD : sdecomp T G B.

  (* This lemma is not acutally used below *)
  Lemma sbag_mid t u v p : upath sedge u v p -> t \in p -> B u :&: B v \subset B t.
  Proof.
    move => upth_p in_p. apply/subsetP => z /setIP [z_in_u z_in_v].
    case/upathP : (sbag_conn decD z_in_u z_in_v) => q upth_q.
    have ? : q = p. { apply: treeP upth_p. exact: upath_restrict upth_q. }
    subst q. case: upth_q => _ /path_restrict A _. exact: A.
  Qed.
    
  Arguments sbag_conn [T G B] dec x t1 t2 : rename.

  Lemma decomp_clique (S : {set G}) : 
    0 < #|S| -> clique S -> exists t : T, S \subset B t.
  Proof. 
    move: S. 
    apply: (nat_size_ind (f := fun S : {set G} => #|S|)) => S IH inh_S clique_S.
    case: (leqP #|S| 2) => card_S. 
    - case: (card12 inh_S card_S) => [[x]|[x] [y] [Hxy]] ?; subst S.
      + case: (sbag_cover decD x) => t A. exists t. by rewrite sub1set.
      + have xy: x -- y. by apply: clique_S => //; rewrite !inE !eqxx ?orbT.
        case: (sbag_edge decD xy) => t A. exists t. by rewrite subUset !sub1set.
    - have [v [v0] [[Hv Hv0 X]]] := card_gt2 (ltnW card_S).
      pose S0 := S :\ v.
      pose T0 := [set t | S0 \subset B t]. 
      (* Wlog. no bag from [T0] contains [v] *)
      case: (boolP [forall t in T0, v \notin B t]); last first. (* TODO: wlog? *)
      { rewrite negb_forall_in. case/exists_inP => t. rewrite inE negbK => H1 H2.
        exists t. by rewrite -(setD1K Hv) subUset sub1set H2 H1. }
      move/forall_inP => HT0.
      have HT0' t : v \in B t -> ~~ (S0 \subset B t).
      { apply: contraTN => C. apply: HT0. by rewrite inE. }
      have pairs x y : x \in S -> y \in S -> exists t, x \in B t /\ y \in B t.
      { move => xS yS.  case: (IH [set x;y]). 
        - rewrite cardsU1 cards1 addn1. case (_ \notin _) => //=. exact: ltnW.
        - by rewrite cards2. 
        - apply: sub_in11W clique_S. apply/subsetP. by rewrite subUset !sub1set xS. 
        - move => t. rewrite subUset !sub1set => /andP [? ?]. by exists t. }
      (* obtain some node [c] whose bag contains [[set v,v0]] and
      consider its subtree outside of T0 *)
      have [c [Hc1 Hc2]] : exists t, v \in B t /\ v0 \in B t by apply: pairs. 
      pose C := [set t | connect (restrict [predC T0] sedge) c t].
      have inC: c \in C by rewrite inE connect0. 
      have C_subtree : subtree C by apply: subtree_connect.
      have disC: [disjoint C & T0]. 
      { rewrite disjoints_subset. apply/subsetP => c0. rewrite 2!inE.
        case/connectP => p /path_restrict H ->. case: p H => /=. 
        - move => _. apply/negPn. move/HT0. by rewrite Hc1. 
        - move => a p. apply. exact: mem_last. }
      (* Let [t0 -- c0] be the link connecting [T0] to [C] *)
      have [t0 [c0 [Ht0 Hc0 tc0]]] : exists t0 c0, [/\ t0 \in T0, c0 \in C & t0 -- c0].
      { case: (IH S0 _ _) => [|||t Ht].
        - by rewrite [#|S|](cardsD1 v) Hv.
        - apply/card_gt0P. exists v0. by rewrite !inE eq_sym X.
        - apply: sub_in11W clique_S. apply/subsetP. by rewrite subD1set.
        - have A : v0 \in B t. { apply (subsetP Ht). by rewrite !inE eq_sym X. }
          have H : connect sedge c t. 
          { apply: connect_mono (sbag_conn decD v0 c t Hc2 A). exact: subrel_restrict. }
          (* bespoke - is there a reasonable lemma? *)
          case/connectP : H => p. generalize c inC. 
          elim: p => /= [|a p IHp] c0 inC0.
          + move => _ /= ?. subst c0. 
            case: (disjointE disC inC0 _). by rewrite !inE.
          + case/andP => H1 H2 H3. case: (boolP (a \in T0)) => Ha.
            * exists a. exists c0. by rewrite sgP.
            * apply: IHp H3 => //. rewrite inE. 
              apply: (connect_trans (y := c0)).
              by rewrite inE in inC0.
              apply: connect1 => /=. rewrite !in_simpl /= Ha H1 !andbT. 
              apply/negP. exact: disjointE disC inC0. }
      have t0P p c' : c' \in C -> upath sedge t0 c' p -> c0 \in p.
      { apply: subtree_link tc0 => //.  apply/negP => H. exact: (disjointE disC H Ht0). }
      suff A : c0 \in T0 by case: (disjointE disC Hc0 A).
      rewrite inE. apply/subsetP => u u_in_S0.
      have Hu: u \in B t0. { rewrite inE in Ht0. exact: (subsetP Ht0). }
      have [cu [Hcu1 Hcu2]] : exists t,  u \in B t /\ v \in B t. 
      { apply: (pairs u v) => //. move: u_in_S0. rewrite inE. by case: (_ \notin _). }
      move:(sbag_conn decD u t0 cu Hu Hcu1). case/upathP => q upth_q. 
      suff Hq : c0 \in q. { case: upth_q => [_ A _]. exact: (path_restrict A). } 
      apply: t0P (upath_restrict upth_q).
      rewrite inE. move: (sbag_conn decD v c cu Hc1 Hcu2).
      apply: connect_mono => t t' /=. 
      rewrite !inE -andbA => /and3P [*]. by rewrite !HT0'.
  Qed.
      
End DecompTheory.

Definition K4_rel := [rel x y : 'I_4 | x != y].

Fact K4_sym : symmetric K4_rel. 
Proof. move => x y /=. by rewrite eq_sym. Qed.

Fact K4_irrefl : irreflexive K4_rel. 
Proof. move => x /=. by rewrite eqxx. Qed.

Definition K4 := SGraph K4_sym K4_irrefl.

Lemma K4_bag (T : tree) (D : T -> {set K4}) : 
  sdecomp T K4 D -> exists t, 4 <= #|D t|.
Proof.
  move => decD.
  case: (@decomp_clique _ _ _ decD setT _ _) => //.
  - by rewrite cardsT card_ord.
  - move => t A. exists t. rewrite -[4](card_ord 4) -cardsT. 
    exact: subset_leq_card.
Qed.

Lemma K4_width (T : tree) (D : T -> {set K4}) : 
  sdecomp T K4 D -> 4 <= width D.
Proof. case/K4_bag => t Ht. apply: leq_trans Ht _. exact: leq_bigmax. Qed.

(** ** Minors *)

Definition connected (G : sgraph) (S : {set G}) :=
  {in S & S, forall x y : G, connect (restrict (mem S) sedge) x y}.  

Notation "f @^-1 x" := (preimset f (mem (pred1 x))) (at level 24) : set_scope.  

(** H is a minor of G -- The order allows us to write [minor G] for the
colletion of [G]s minors *)

CoInductive minor (G H : sgraph) : Prop :=
  MinorI (phi : G -> option H) of 
    (forall y : H, exists x, phi x = Some y) 
  & (forall y : H, connected (phi @^-1 Some y)) 
  & (forall x y : H, x -- y -> 
     exists x0 y0, [/\ x0 \in phi @^-1 Some x, y0 \in phi @^-1 Some y & x0 -- y0]).

Lemma minor_trans : Transitive minor.
Proof.
  move => G H I [f f1 f2 f3] [g g1 g2 g3].
  exists (fun x => obind g (f x)).
  - move => y. case: (g1 y) => y'. case: (f1 y') => x E1 ?.
    exists x. by rewrite E1.
  - move => z x y. rewrite !inE. 
    case Ef : (f x) => [fx|] //= gfx. case Eg : (f y) => [fy|] //= gfy.
    move: (g2 z fx fy). rewrite !inE. case/(_ _ _)/Wrap => // /connectP => [[p]]. 
    elim: p x fx Ef gfx => /= [|a p IH] x fx Ef gfx.
    + move => _ ?. subst fy. 
      move: (f2 fx x y). rewrite !inE Ef Eg. case/(_ _ _)/Wrap => //. 
      apply: connect_mono => a b /=. rewrite !inE -andbA. 
      case/and3P => /eqP-> /eqP-> -> /=. by rewrite (eqP gfx) !eqxx.
    + rewrite !inE -!andbA => /and4P [H1 H2 H3 H4] H5. 
      case: (f1 a) => x' Hx'. apply: (connect_trans (y := x')); last exact: IH H5.
      move/f3 : (H3) => [x0] [y0] [X1 X2 X3]. 
      apply: (connect_trans (y := x0)); last apply: (connect_trans (y := y0)).
      * move: (f2 fx x x0). rewrite !inE ?Ef ?eqxx in X1 *. case/(_ _ _)/Wrap => //.
        apply: connect_mono => u v /=. rewrite !inE -andbA. 
        case/and3P => /eqP-> /eqP-> -> /=. by rewrite H1.
      * apply: connect1. rewrite /= !inE ?X3 ?andbT in X1 X2 *. 
        by rewrite (eqP X1) (eqP X2) /= (eqP gfx) eqxx.
      * move: (f2 a y0 x' X2). case/(_ _)/Wrap. by rewrite !inE Hx'.
        apply: connect_mono => u v /=. rewrite !inE -andbA. 
        case/and3P => /eqP-> /eqP-> -> /=. by rewrite H2.
  - move => x y /g3 [x'] [y'] [Hx' Hy'] /f3 [x0] [y0] [Hx0 Hy0 ?].
    exists x0. exists y0. rewrite !inE in Hx' Hy' Hx0 Hy0 *. 
    split => //; reflect_eq; by rewrite (Hx0,Hy0) /= (Hx',Hy'). 
Qed.

CoInductive strict_minor (G H : sgraph) : Prop :=
  SMinorI (phi : G -> H) of 
    (forall y : H, exists x, phi x = y) 
  & (forall y : H, connected (phi @^-1 y)) 
  & (forall x y : H, x -- y -> 
     exists x0 y0, [/\ x0 \in phi @^-1 x, y0 \in phi @^-1 y & x0 -- y0]).

Lemma strict_is_minor (G H : sgraph) : strict_minor G H -> minor G H.
Proof.
  case => phi A B C. exists (Some \o phi) => //= y.
  case: (A y) => x <-. by exists x.
Qed.

Definition subgraph (S G : sgraph) := 
  exists2 h : S -> G, injective h & hom_s h.

Lemma sub_minor (S G : sgraph) : subgraph S G -> minor G S.
Proof.
  move => [h inj_h hom_h].
  pose phi x := if @idP (x \in codom h) is ReflectT p then Some (iinv p) else None.
  exists phi.
  - move => y. exists (h y). rewrite /phi. 
    case: {-}_ / idP => [p|]; by rewrite ?iinv_f ?codom_f.
  - move => y x0 y0. rewrite !inE {1 2}/phi. 
    case: {-}_ / idP => // p /eqP[E1]. 
    case: {-}_ / idP => // q /eqP[E2]. 
    suff -> : (x0 = y0) by exact: connect0. 
    by rewrite -(f_iinv p) -(f_iinv q) E1 E2. 
  - move => x y A. move/hom_h : (A). 
    case => [/inj_h ?|B]; first by subst; rewrite sgP in A.
    exists (h x). exists (h y). rewrite !inE /phi B. 
    by do 2 case: {-}_ / idP => [?|]; rewrite ?codom_f ?iinv_f ?eqxx //.
Qed.


Section InducedSubgraph.
  Variables (G : sgraph) (S : {set G}).

  Definition induced_type := sig [eta mem S].

  Definition induced_rel := [rel x y : induced_type | val x -- val y].

  Lemma induced_sym : symmetric induced_rel.  
  Proof. move => x y /=. by rewrite sgP. Qed.
         
  Lemma induced_irrefl : irreflexive induced_rel.  
  Proof. move => x /=. by rewrite sgP. Qed.

  Definition induced := SGraph induced_sym induced_irrefl.

  Lemma induced_sub : subgraph induced G.
  Proof. exists val => //. exact: val_inj. by right. Qed.

  Lemma induced_minor : minor G induced.
  Proof. exact: sub_minor induced_sub. Qed.

End InducedSubgraph.

Definition rename (T G G' : finType) (B: T -> {set G}) (h : G -> G') := [fun x => h @: B x].

Definition edge_surjective (G1 G2 : sgraph) (h : G1 -> G2) :=
  forall x y : G2 , x -- y -> exists x0 y0, [/\ h x0 = x, h y0 = y & x0 -- y0].

(* The following should hold but does not fit the use case for minors *)
Lemma rename_sdecomp (T : tree) (G H : sgraph) D (dec_D : sdecomp T G D) (h :G -> H) : 
  hom_s h -> surjective h -> edge_surjective h -> 
  (forall x y, h x = h y -> exists t, (x \in D t) && (y \in D t)) -> 
  @sdecomp T _ (rename D h).
Abort. 

(* This should hold, but there are several choices for S, the induced
subgraph of the range of [phi] seems to be the canonical one. *)
Lemma minor_split (G H : sgraph) : 
  minor G H -> exists2 S, subgraph S G & strict_minor S H.
Proof.
  move => [phi p1 p2 p3].
  set S := [set x | phi x]. 
  exists (induced S); first exact: induced_sub.
  wlog x0 : / H.
  { admit. (* the empty graph is a minor of ever graph *) }
  pose f (x : induced S) := odflt x0 (phi (val x)).
  exists f. 
Abort. 


Lemma width_minor (G H : sgraph) (T : tree) (B : T -> {set G}) : 
  sdecomp T G B -> minor G H -> exists B', sdecomp T H B' /\ width B' <= width B.
Proof.
  move => decT [phi p1 p2 p3].
  pose B' t := [set x : H | [exists (x0 | x0 \in B t), phi x0 == Some x]].
  exists B'. split.
  - split. 
    + move => y. case: (p1 y) => x /eqP Hx.
      case: (sbag_cover decT x) => t Ht.
      exists t. apply/pimsetP. by exists x.
    + move => x y xy. move/p3: xy => [x0] [y0]. rewrite !inE => [[H1 H2 H3]].
      case: (sbag_edge decT H3) => t /andP [T1 T2]. exists t. 
      apply/andP; split; apply/pimsetP; by [exists x0|exists y0].
    + have conn_pre1 t1 t2 x x0 :
        phi x0 == Some x -> x0 \in B t1 -> x0 \in B t2 ->
        connect (restrict [pred t | x \in B' t] sedge) t1 t2.
      { move => H1 H2 H3. case: (sbag_conn decT H2 H3).
        apply: connect_mono => u v /=. rewrite !in_simpl -!andbA => /and3P [? ? ?]. 
        apply/and3P; split => //; apply/pimsetP; eexists; eauto. }
      move => x t1 t2 /pimsetP [x0 X1 X2] /pimsetP [y0 Y1 Y2].
      move: (p2 x x0 y0). rewrite !inE. case/(_ _ _)/Wrap => // /connectP [p]. 
      elim: p t1 x0 X1 X2 => /= [|z0 p IH] t1 x0 X1 X2. 
      * move => _ E. subst x0. exact: conn_pre1 X1 Y1.
      * rewrite -!andbA => /and3P [H1 H2 /andP [H3 H4] H5].
        case: (sbag_edge decT H3) => t /andP [T1 T2].
        apply: (connect_trans (y := t)). 
        -- move => {p IH H4 H5 y0 Y1 Y2 X2}. rewrite !inE in H1 H2.
           exact: conn_pre1 X1 T1.
        -- apply: IH H4 H5 => //. by rewrite inE in H2.
  - apply: max_mono => t. exact: pimset_card.
Qed.


Definition K4_free (G : sgraph) := ~ minor G K4.

Lemma TW2_K4_free (G : sgraph) (T : tree) (B : T -> {set G}) : 
  sdecomp T G B -> width B <= 3 -> K4_free G.
Proof.
  move => decT wT M. case: (width_minor decT M) => B' [B1 B2].
  suff: 4 <= 3 by []. 
  apply: leq_trans wT. apply: leq_trans B2. exact: K4_width.
Qed.

(** decidability of cycle agnostic path properties *)
Definition short_prop (T:eqType) e (P : T -> seq T -> bool) := 
  forall x p, path e x p -> P x (shorten x p) -> P x p.

Lemma short_prop_dec (T : finType) e (P : T -> seq T -> bool) x : 
  short_prop e P -> decidable (forall p, path e x p -> P x p).
Proof.
  move => spP. 
  pose Pb := [forall n : 'I_#|T|, forall p : n.-tuple T, path e x p ==> P x p].
  apply: (decP (b := Pb)). apply: (iffP forallP) => H.
  - move => p pth_p. apply: spP => //. 
    case/shortenP : pth_p => p' pth_p' uniq_p' _. 
    have bound_p' : size p' < #|T|. 
    { move/card_uniqP : uniq_p' => /= <-. exact: max_card. }
    move/forall_inP: (H (Ordinal bound_p')) => /(_ (in_tuple p')). 
    by apply.
  - move => n. apply/forall_inP => p. exact: H.
Qed.

Lemma dec_eq (P : Prop) (decP : decidable P) : decP <-> P.
Proof. by case: decP. Qed.


Section CheckPoints.
  Variables (G : sgraph).
  Implicit Types x y z : G.
  Definition checkpoint x y z := forall p, path sedge x p -> last x p = y -> z \in x :: p.

  Let cpb y z x p := (last x p == y) ==> (z \in x :: p).
  Lemma cp_short_prop y z : short_prop sedge (cpb y z).
  Proof. 
    move => x p. rewrite /cpb !inE. 
    case/shortenP => p' _ _ sub. do 2 case: (_ == _) => //=. exact: sub.
  Qed.

  Definition checkpointb x y z := short_prop_dec x (@cp_short_prop y z).

  Lemma checkpointP x y z : 
    reflect (checkpoint x y z) (checkpointb x y z).
  Proof.
    apply: (iffP idP) => /=.
    - move => /dec_eq H p p1 p2. move/implyP: (H p p1). apply. exact/eqP.
    - move => H. apply/dec_eq => p p1. apply/implyP => /eqP. exact: H.
  Qed.

  (* This is locked to keep inE from expanding it *)
  Definition cp x y := locked [set z | checkpointb x y z].

  Lemma cpP x y z : reflect (checkpoint x y z) (z \in cp x y).
  Proof. rewrite /cp -lock !inE. exact: checkpointP. Qed.

  Hypothesis G_conn : forall x y:G, connect sedge x y.

  Lemma cpPn x y z : 
    reflect [/\ z != x, z != y & exists p, [/\ path sedge x p, last x p = y & z \notin p]]
            (z \notin cp x y).
  Admitted. (* Properly refactor the decidability result to obtain this *)

  Lemma cp_sym x y : cp x y = cp y x.
  Proof.
    wlog suff S : x y / cp x y \subset cp y x. 
    { apply/eqP. by rewrite eqEsubset !S. }
    apply/subsetP => z /cpP H. apply/cpP => p p1 p2. 
    move/H: (rev_spath p1 p2). rewrite (last_rev_belast p2) -p2. 
    move/(_ erefl). rewrite inE mem_rev. 
    case/predU1P => [->|]; by [rewrite mem_last| apply: mem_belast].
  Qed.

  Lemma mem_cpl x y : x \in cp x y.
  Proof. apply/cpP => p. by rewrite mem_head. Qed.

  Lemma subcp x y : [set x;y] \subset cp x y.
  Proof. by rewrite subUset !sub1set {2}cp_sym !mem_cpl. Qed.

  Lemma cpxx x : cp x x = [set x].
  Proof. 
    apply/setP => z; rewrite !inE. 
    apply/idP/idP; last by move/eqP ->; rewrite mem_cpl.
    move/cpP/(_ [::] erefl erefl). by rewrite inE.
  Qed.

  Lemma cp_triangle z {x y} : cp x y \subset cp x z :|: cp z y.
  Proof.
    apply/subsetP => u /cpP cp_u. rewrite -[_ \in _]negbK inE negb_or.
    apply/negP => /andP[]. 
    case/cpPn => A B [p] [p1 p2 p3]. case/cpPn => C D [q] [q1 q2 q3]. 
    move: (cp_u (p ++ q)). 
    rewrite cat_path p1 p2 q1 last_cat p2 q2. case/(_ _ _)/Wrap => //.
    by rewrite !inE mem_cat (negbTE A) (negbTE p3) (negbTE q3).
  Qed.

  Definition CP (U : {set G}) := \bigcup_(xy in setX U U) cp xy.1 xy.2.

  (* Lemma 13 *)
  Lemma CP_closed U x y : 
    x \in CP U -> y \in CP U -> cp x y \subset CP U.
  Proof.
    
  Abort.

  Definition link_rel := [rel x y | (x != y) && (cp x y \subset [set x; y])].

  Lemma link_sym : symmetric link_rel.
  Proof. move => x y. by rewrite /= eq_sym cp_sym set2C. Qed.

  Lemma link_irrefl : irreflexive link_rel.
  Proof. move => x /=. by rewrite eqxx. Qed.

  Definition link_graph := SGraph link_sym link_irrefl.

  Lemma link_avoid (x y z : G) : 
    z \notin [set x; y] -> link_rel x y -> 
    exists p, [/\ path sedge x p, last x p = y & z \notin p].
  Admitted.
  
  Lemma link_seq_cp (y x : G) p :
    path link_rel x p -> last x p = y -> cp x y \subset [set z in [:: x, y & p]].
  Proof.
    elim: p x => [|z p IH] x /=.
    - move => _ ->. rewrite cpxx. admit.
    - rewrite -andbA => /and3P [A B C D]. 
      move: (IH _ C D) => IHz. apply: subset_trans (cp_triangle z) _.
      (* TODO: set theory reasoning *)
  Admitted.  

  (* Lemma 10 *)
  Lemma link_cycle (p : seq link_graph) : ucycle sedge p -> clique [set x in p].
  Proof. 
    move => cycle_p x y. rewrite !inE /= => xp yp xy. rewrite xy /=.
    case/andP : cycle_p => C1 C2. 
    case: (rot_to_arc C2 xp yp xy) => i p1 p2 _ _ I. 
    have {C1} C1 : cycle sedge (x :: p1 ++ y :: p2) by rewrite -I rot_cycle. 
    have {C2} C2 : uniq (x :: p1 ++ y :: p2) by rewrite -I rot_uniq.
    rewrite /cycle -cat_rcons rcons_cat cat_path last_rcons in C1. 
    case/andP: C1 => P1 /(rev_spath (y := x)).
    rewrite last_rcons belast_rcons rev_cons => /(_ erefl) P2 {i I}.
    apply/subsetP => z cp_z.
    move/(@link_seq_cp y) : P1. rewrite last_rcons => /(_ erefl) A.
    move/(@link_seq_cp y) : P2. rewrite last_rcons => /(_ erefl) B.
    (* TODO: p1 and p2 are disjoint, so the intersection is just {x,y} *)    
  Admitted.

  Definition upathb (T : eqType) (e : rel T) (x y : T) (p : seq T) :=
    [&& uniq (x :: p), path e x p & last x p == y].

  (* FIXME: This should probably be upathP *)
  Lemma upath_reflect (T : eqType) (e : rel T) (x y : T) (p : seq T) :
    reflect (upath e x y p) (upathb e x y p).
  Admitted. 

  (** This is redundant, but a boolean property. See [checkpoint_seq]
  in extraction.v *)
  Variables (i o : G).
  Hypothesis conn_io : connect sedge i o.

  Lemma the_upath_proof : exists p, upathb sedge i o p.
  Proof. 
    case/upathP : conn_io => p /upath_reflect Hp. by exists p.
  Qed.
                                                                
  Definition the_upath := xchoose (the_upath_proof).

  Lemma the_upathP x y : upath sedge i o (the_upath).
  Proof. apply/upath_reflect. exact: xchooseP. Qed.

  Definition cpo x y := let p := the_upath in 
                        index x (i::p) <= index y (i::p).

  Lemma cpo_trans : transitive cpo.
  Proof. move => ? ? ?. exact: leq_trans. Qed.

  Lemma cpo_total : total cpo.
  Proof. move => ? ?. exact: leq_total. Qed.

  Lemma cpo_antisym : {in cp i o&,antisymmetric cpo}.
  Proof. 
    move => x y Cx Cy. rewrite /cpo -eqn_leq. 
    have Hx: x \in i :: the_upath. 
    { move/cpP : Cx => /(_ (the_upath)). 
      apply; by case: (the_upathP). }
    have Hy: y \in i :: the_upath.
    { move/cpP : Cy => /(_ (the_upath)). 
      apply; by case: (the_upathP). }
    by rewrite -{2}[x](nth_index i Hx) -{2}[y](nth_index i Hy) => /eqP->.
  Qed.

  (** All paths visist all checkpoints in the same order as the canonical upath *)
  (* TOTHINK: Is this really the formulation that is needed in the proofs? *)
  Lemma cpo_order x y p : 
    x \in cp i o -> y \in cp i o -> path sedge i p -> last i p = o -> 
    cpo x y = (index x (i::p) <= index y (i::p)).
  Admitted.
    
End CheckPoints.