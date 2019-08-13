Require Import Setoid CMorphisms Morphisms.
From mathcomp Require Import all_ssreflect.

Require Import edone set_tac finite_quotient preliminaries bij equiv.
Require Import multigraph_new liso.

Require Import mathcomp.finmap.finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

Open Scope fset_scope.

(** ** Preliminaries *)

Notation "'Σ' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p%type)) ..))
  (at level 200, x binder, y binder, right associativity).

Lemma valK' (T : Type) (P : pred T) (sT : subType P) (x : sT) (p : P (val x)) : 
  Sub (val x) p = x.
Proof. apply: val_inj. by rewrite SubK. Qed.

Definition fresh (E : {fset nat}) : nat := (\max_(e <- E) e).+1.

Lemma freshP (E : {fset nat}) : fresh E \notin E. 
Proof. Admitted.

Lemma fsval_eqF (T:choiceType) (E : {fset T}) (e : E) x : x \notin E -> val e == x = false.
Admitted.

Lemma fresh_eqF (E : {fset nat}) (x : E) : val x == fresh E = false.
Admitted.

Lemma fsetDDD (T : choiceType) (A B C : {fset T}) : A `\` B `\` (C `\` B) = A `\` (B `|` C).
Proof. apply/fsetP => z. rewrite !inE. by case (z \in B). Qed.

Lemma in_imfsetT (aT : finType) (rT : choiceType) (f : aT -> rT) (x : aT) : 
  f x \in [fset f x | x in aT].
Proof. by rewrite in_imfset. Qed.

Lemma imfset_inv (aT : finType) (rT : choiceType) (f : aT -> rT) (y : [fset f x | x in aT]) : 
  Σ x : aT, f x = val y.
Proof. 
  suff E : exists x, f x == val y by exists (xchoose E); rewrite (eqP (xchooseP E)).
  case/imfsetP : (valP y) => /= x _ ->. by exists x.
Qed.

Lemma imfset1E (key : unit) (aT rT : choiceType) (f : aT -> rT) (x : aT) (A : finmempred aT) :
  A =1 pred1 x -> imfset key f A = [fset f x].
Admitted.
Arguments imfset1E [key aT rT f] x [A].

Lemma imfset_set1 (aT : finType) (rT : choiceType) (f : aT -> rT) (x : aT) : 
  [fset f z | z in [set x]] = [fset f x].
rewrite (imfset1E x) => //= z. by rewrite !inE. Qed.

Lemma fsetDEl (T : choiceType) (A B : {fset T}) (x : A `\` B) : val x \in A.
Proof. by case/fsetDP : (valP x). Qed.


Arguments fset1Ur [K x a B].
Arguments fset1U1 [K x B].
Arguments fset1U1 [K x B].

(** TOTHINK: how to have simpl keep the [h/h^-1] notation unless the functions actually reduce? *)

Section Bij.
Variable (G : finType) (T : choiceType) (g : G -> T).
Hypothesis g_inj : injective g.
Let vset := [fset g x | x in G].
Definition imfset_bij_fwd (x : G) : vset := Sub (g x) (in_imfsetT g x).
Definition imfset_bij_bwd (x : vset) : G := tag (imfset_inv x).

Lemma can_vset : cancel imfset_bij_fwd imfset_bij_bwd.
Proof. 
  move => x. rewrite /imfset_bij_fwd /imfset_bij_bwd /=. set S := Sub _ _. 
  apply: g_inj. by rewrite (tagged (imfset_inv S)).
Qed.

Lemma can_vset' : cancel imfset_bij_bwd imfset_bij_fwd.
Proof.
  move => [x Hx]. rewrite /imfset_bij_fwd /imfset_bij_bwd. apply: val_inj => /=.
  by rewrite (tagged (imfset_inv [` Hx])).
Qed.

Definition imfset_bij := Bij can_vset can_vset'.

Lemma imfset_bij_bwdE x p : imfset_bij_bwd (Sub (g x) p) = x.
Proof. 
  rewrite /imfset_bij_bwd. set t := imfset_inv _. 
  by move/g_inj : (tagged t).
Qed.

End Bij.

(* TODO: generalize to any [e \notin E] *)
Lemma fresh_bij (T : finType) (E : {fset nat}) (f : bij T E) e (He : e \notin E) : 
  bij (option T) (e |` E).
Proof.
  pose g (x : option T) :  e |` E := 
    if x is Some z then Sub (val (f z)) (fset1Ur (valP (f z))) else Sub e fset1U1.
  pose g_inv  (x : e |` E) : option T := 
    match fsetULVR (valP x) with inl _ => None | inr p => Some (f^-1 (Sub (val x) p)) end.
  have can_g : cancel g g_inv.
  { move => [x|]; rewrite /g/g_inv/=; case: (fsetULVR _) => [|p] //=. 
    - by rewrite inE fsval_eqF.
    - by rewrite valK' bijK.
    -  exfalso. by rewrite p in He. }
  have can_g_inv : cancel g_inv g.
  { move => [x Hx]; rewrite /g/g_inv/=. case: (fsetULVR _) => [|p] //=. 
    - rewrite !inE => A. apply: val_inj => /=. by rewrite (eqP A).
    - apply: val_inj => //=. by rewrite bijK'. }
  apply: (Bij can_g can_g_inv).
Defined.

Lemma fresh_bijE (T : finType) (E : {fset nat}) (f : bij T E) x (Hx : x \notin E) : 
  (forall x, fresh_bij f Hx (Some x) = Sub (val (f x)) (fset1Ur (valP (f x))))*
  (fresh_bij f Hx None = Sub x fset1U1).
Proof. done. Qed.


Definition bij_setD (aT : finType) (C : choiceType) (rT : {fset C}) (A : {set aT}) (f : bij aT rT) : 
  bij { x | x \in ~: A} (rT `\` [fset val (f x) | x in A]).
Proof.
  set aT' := ({ x | _ }). set rT' := _ `\` _.
  have g_proof (x : aT') : val (f (val x)) \in rT'.
  { rewrite !inE (valP (f (val x))) andbT. apply: contraTN (valP x).
    case/imfsetP => /= x0 inA /val_inj /(@bij_injective _ _ f) ->. by rewrite inE negbK. }
  pose g (x : aT') : rT' := Sub (val (f (val x))) (g_proof x).
  have g_inv_proof (x : rT') :  f^-1 (Sub (fsval x) (fsetDEl x)) \in ~: A.
  { rewrite inE. case/fsetDP: (valP x) => ?. apply: contraNN => X. apply/imfsetP.
    exists (f^-1 (Sub (fsval x) (fsetDEl x))) => //. by rewrite bijK'. }
  pose g_inv (x : rT') : aT' := Sub (f^-1 (Sub (val x) (fsetDEl x))) (g_inv_proof x). 
  have can1 : cancel g g_inv.
  { move => [x Hx]. rewrite /g/g_inv. apply: val_inj => /=. apply: (@bij_injective _ _ f).
    rewrite bijK'. exact: val_inj. }
  have can2 : cancel g_inv g.
  { move => [x Hx]. rewrite /g/g_inv. apply: val_inj => /=. by rewrite bijK'. }
  apply: Bij can1 can2.
Defined.




Section update.
Variables (aT : eqType) (rT : Type) (f : aT -> rT).
Definition update x a := fun z => if z == x then a else f z.

Lemma update_neq x z a : x != z -> update z a x = f x.
Proof. rewrite /update. by case: ifP. Qed.

Lemma update_eq z a : update z a z = a.
Proof. by rewrite /update eqxx. Qed.

End update.
Definition updateE := (update_eq,update_neq).
Notation "f [upd x := y ]" := (update f x y) (at level 2, left associativity, format "f [upd  x  :=  y ]").

Lemma update_same (aT : eqType) (rT : Type) (f : aT -> rT) x a b : 
  f[upd x := a][upd x := b] =1 f[upd x := b].
Admitted.

Lemma eqv_update (aT : eqType) (rT : Type) (f g : aT -> rT) (E : relation rT) z u v : 
  (forall x, E (f x) (g x)) -> E u v -> forall x, E (f[upd z := u] x) (g[upd z := v] x).
Admitted.

Lemma in_eqv_update (aT : choiceType) (rT : Type) (f g : aT -> rT) (E : relation rT) 
  (z : aT) (u v : rT) (A : {fset aT}) : 
  {in A, forall x : aT, E (f x) (g x)} -> E u v -> 
  {in z |` A, forall x : aT, E (f[upd z := u] x) (g[upd z := v] x)}.
Admitted.

Require Import confluence pttdom.


Notation "G ≅ H" := (liso G H) (at level 45).

Definition split_edge (G : lgraph) (e : edge G) : 
  del_edge G e ∔ [source e, elabel e, target e] ≅ G.
Admitted.

Lemma split_edgeE (G : lgraph) (e : edge G) (x : G) : 
  (split_edge e x = x) * ((split_edge e).e None = e).
Admitted.

Lemma split_vertex (G : lgraph) (z : G) (Hz : z \notin IO) :  
  edges_at G z = set0 -> G \ [z,Hz] ∔ vlabel z ≅ G. 
Admitted.



(** * Open Graphs *)

(** For the sake of clarity, we define two aliases of [nat], the type
[VT] of graph vertices and the type [ET] of graph edges. For each type
we have an injection into the type from any finite type via the rank
of the element in the enumeration (i.e., [enum_rank]) *)

Definition VT := nat.
Definition ET := nat.


Canonical ET_eqType := [eqType of ET].
Canonical ET_choiceType := [choiceType of ET].
Canonical ET_countType := [countType of ET].

Section inject.
Variable (T : finType).

Definition inj_v (x : T) : VT := enum_rank x.
Definition inj_e (x : T) : ET := enum_rank x.
Definition v0 : VT := 0.

Lemma inj_v_inj : injective inj_v. 
Proof. move => x y. by move/ord_inj/enum_rank_inj. Qed.

Lemma inj_e_inj : injective inj_e. 
Proof. move => x y. by move/ord_inj/enum_rank_inj. Qed.
End inject.

Hint Resolve inj_v_inj inj_e_inj.

Record pre_graph := { vset : {fset VT};
                      eset : {fset ET};
                      src : ET -> VT;
                      tgt : ET -> VT;
                      lv : VT -> test;
                      le : ET -> term;
                      p_in : VT;
                      p_out : VT }.

Class is_graph (G : pre_graph) := 
  { srcP (e:ET) : e \in eset G -> src G e \in vset G;
    tgtP (e:ET) : e \in eset G -> tgt G e \in vset G;
    p_inP : p_in G \in vset G;
    p_outP : p_out G \in vset G}.

Bind Scope open_scope with pre_graph.
Delimit Scope open_scope with O.

(** ** Opening and closing of type-based graphs *)

Section Open.
Variable (G : lgraph).

(** G may be edgeless, so there is no way to avoid the option type here *)
Definition proj_e (e : ET) : option (edge G) := 
  omap enum_val (insub e : option 'I_#|edge G|).

Lemma inj_eK (e : edge G) : proj_e (inj_e e) = Some e.
Proof. 
  rewrite /proj_e /inj_e /=. 
  have P : enum_rank e < #|edge G| by [].
  case: insubP => [k _ /ord_inj -> /=|]; by rewrite ?P ?enum_rankK.
Qed.

(** For two-pointed graphs, we can use the input as default vertex when inverting the injection into [VT] *)
Definition proj_v (v : VT) : G :=
  odflt input (omap enum_val (insub v : option 'I_#|G|)).

Lemma inj_vK (v : G) : proj_v (inj_v v) = v.
Proof.
  rewrite /proj_v /inj_v /=. 
  have P : enum_rank v < #|G| by [].
  case: insubP => [k _ /ord_inj -> /=|]; by rewrite ?P ?enum_rankK.
Qed.

Definition open : pre_graph := 
  {| vset := [fset inj_v x | x in G];
     eset := [fset inj_e x | x in edge G];
     src (e:ET) := if proj_e e is Some e' then inj_v (source e') else v0;
     tgt (e:ET) := if proj_e e is Some e' then inj_v (target e') else v0;
     lv v := vlabel (proj_v v);
     le e := if proj_e e is Some e' then elabel e' else one;
     p_in := inj_v (input : G);
     p_out := inj_v (output : G) |}.

Global Instance open_is_graph : is_graph open.
Proof.
  split.
  - move => e'. case/imfsetP => /= e _ ->. by rewrite inj_eK in_imfset.
  - move => e'. case/imfsetP => /= e _ ->. by rewrite inj_eK in_imfset.
  - by rewrite /= in_imfset.
  - by rewrite /= in_imfset.
Qed.

End Open.

Section Close.
Variable (G : pre_graph).
Context {graph_G : is_graph G}.

Lemma source_proof (e : eset G) : src G (val e) \in vset G.
Proof. exact: (srcP (valP e)). Qed.

Lemma target_proof (e : eset G) : tgt G (val e) \in vset G.
Proof. exact: (tgtP (valP e)). Qed.

Definition close' : graph test_setoid term_setoid := Eval simpl in 
  {| vertex := [finType of vset G];
     edge := [finType of eset G];
     source e := Sub (src G (val e)) (source_proof e);
     target e := Sub (tgt G (val e)) (target_proof e);
     vlabel v := lv G (val v);
     elabel e := le G (val e) |}.

Definition close := Eval hnf in
  @LGraph close' (Sub (p_in G) p_inP) (Sub (p_out G) p_outP).

End Close.
Arguments close G [_].

(** tracing vertices through the closing operation *)
Definition close_v (G : pre_graph) (graph_G : is_graph G) (x : VT) : close G :=
  match @idP (x \in vset G) with
  | ReflectT p => Sub x p
  | ReflectF _ => input
  end.

Lemma close_vK (G : pre_graph) (graph_G : is_graph G) (x : VT) : 
  x \in vset G -> fsval (close_v graph_G x) = x.
Proof. move => xG. rewrite /close_v. by case: {-}_ /idP. Qed.

Arguments close_v [G graph_G] _. 
Arguments close_v : simpl never.


Lemma openK (G : lgraph) : G ≅ close (open G). 
liso (imfset_bij (@inj_v_inj G)) 
     (imfset_bij (@inj_e_inj (edge G)))
     (fun => false) => /=.
- move => v. by rewrite inj_vK.
- move => e. by rewrite inj_eK.
- move => e. apply: val_inj => /=. by rewrite inj_eK.
- move => e. apply: val_inj => /=. by rewrite inj_eK.
- exact: val_inj.
- exact: val_inj.
Defined.

Lemma openKE (G : lgraph) (x : G) :
  openK G x = close_v (inj_v x) :> close (open G).
Proof. 
  rewrite /close_v /=. case: {-}_ /idP => [p|np]; first exact: val_inj.
  by rewrite in_imfsetT in np.
Qed.


(** We define isomorphisms via closing *)

Definition oliso (G H : pre_graph) :=
  Σ (graph_G : is_graph G) (graph_H : is_graph H), close G ≅ close H.

Notation "G ⩭ H" := (oliso G H) (at level 45).

Lemma closeK (G : pre_graph) (graph_G : is_graph G) : 
  G ⩭ open (close G).
Proof. rewrite /oliso. do 2 eexists. exact: openK. Defined.

Lemma close_irrelevance (G : pre_graph) (graph_G graph_G' : is_graph G) : 
  @close G graph_G ≅ @close G graph_G'.
Proof.
  liso bij_id bij_id (fun _ => false) => //= [e|e||]; exact: val_inj.
Qed.
  
Lemma liso_of_oliso (G H : pre_graph) (graph_G : is_graph G) (graph_H : is_graph H) : 
  G ⩭ H -> close G ≅ close H.
Proof. 
  case => graph_G' [graph_H'] I. rewrite -> (close_irrelevance graph_H graph_H'). 
  apply: liso_comp I. exact: close_irrelevance.
Qed.

Instance oliso_Equivalence : CRelationClasses.Equivalence oliso.
Admitted.

Lemma oliso_trans : CRelationClasses.Transitive oliso.
Proof. apply: CRelationClasses.Equivalence_Transitive. Qed.

Definition vfun_body (G H : pre_graph) 
  (graph_G : is_graph G) (graph_H : is_graph H) (h : bij (close G) (close H)) (x : VT) : VT := 
  locked (match @idP (x \in vset G) with
          | ReflectT p => val (h (Sub x p))
          | ReflectF _ => x
          end).

Definition vfun_of (G H : pre_graph) (h : G ⩭ H) := 
  let: existT GG (existT GH h) := h in vfun_body h.

Arguments vfun_of [G H] h x.

Coercion vfun_of : oliso >-> Funclass.

(** In open graphs, we have an equivalence of graphs that have the
same underlying structure with different, but equivalent, labels *)

Record weqG (G H : pre_graph) : Prop := WeqG {
  sameV : vset G = vset H;
  sameE : eset G = eset H;
  same_src : {in eset G, src G =1 src H};
  same_tgt : {in eset G, tgt G =1 tgt H};
  eqv_lv x : x \in vset G -> lv G x ≡ lv H x;
  eqv_le e : e \in eset G -> le G e ≡ le H e;
  same_in : p_in G = p_in H;
  same_out : p_out G = p_out H
}.
                                       
Instance weqG_Equivalence : Equivalence weqG. Admitted.

Notation "G ≡G H" := (weqG G H) (at level 79).


Section BijCast.
Variables (T : choiceType) (A A' : {fset T}) (eqA : A = A').
Definition bij_cast : bij A A'.
Proof. case eqA. exact bij_id. Defined.

Lemma cast_proof x : x \in A -> x \in A'. case eqA. exact id. Qed.

Lemma bij_castE x (Hx : x \in A) : bij_cast [` Hx] = [` cast_proof Hx].
Proof. 
  rewrite /bij_cast. move: (cast_proof _). case eqA => Hx'. exact: val_inj.
Qed.
End BijCast.

Definition weqG_oliso (G H : pre_graph) : 
  is_graph G -> is_graph H -> G ≡G H -> G ⩭ H.
Proof.
  move => isG isH [EV EE Es Et Elv Ele]. do 2 eexists. 
  liso (bij_cast EV) (bij_cast EE) (fun _ => false).
  - move => [v p]. by rewrite bij_castE /= Elv.
  - move => [e p]. by rewrite bij_castE /= Ele.
  - move => [e p]. rewrite !bij_castE /=. apply: val_inj => /=. by rewrite Es.
  - move => [e p]. rewrite !bij_castE /=. apply: val_inj => /=. by rewrite Et.
  - rewrite bij_castE. exact: val_inj.
  - rewrite bij_castE. exact: val_inj.
Qed.

(** Experimental: A class of boxed properties to allow inference of "non-class" assumptions *)
Class box (P : Prop) : Prop := Box { boxed : P }.
Hint Extern 0 (box _) => apply Box; assumption : typeclass_instances.

(** ** Helper functions *)

Section PreGraphTheory.
Variables (G : pre_graph).

Definition incident x e := (src G e == x) || (tgt G e == x).

Definition edges_at x := [fset e in eset G | incident x e].

Lemma edges_atF e x (edge_e : e \in eset G) :  
  e \notin edges_at x -> (src G e == x = false)*(tgt G e == x = false).
Proof. rewrite !inE /= edge_e /= negb_or. by do 2 case: (_ == x). Qed.

Definition pIO  := [fset p_in G; p_out G].

Lemma pIO_Ni x : x \notin pIO -> p_in G != x.
Admitted.

Lemma pIO_No x : x \notin pIO -> p_out G != x.
Admitted.

(** Making [e \in eset G] part of the definition of oarc allows us to mostly avoid
explicitly mentioning this assumption in the step relation. Moreover,
it avoids spurious lemmas such as [oarc G e x u y -> oarc (G \ z) e x u y] *)
Definition oarc e x u y := 
  e \in eset G /\ 
  ([/\ src G e = x, tgt G e = y & le G e ≡ u] \/
   [/\ tgt G e = x, src G e = y & le G e ≡ u°]).

End PreGraphTheory.

(** ** Operatons on open graphs *)

Definition del_vertex (G : pre_graph) (x : VT) := 
  {| vset := vset G `\ x;
     eset := eset G `\` edges_at G x;
     src := src G;
     tgt := tgt G;
     lv := lv G;
     le := le G;
     p_in := p_in G;
     p_out := p_out G |}.

Notation "G \ x" := (del_vertex G x) (at level 29,left associativity) : open_scope.

Global Instance del_vertex_graph (G : pre_graph) `{graph_G : is_graph G} (x : VT) `{Hx : box (x \notin pIO G)} : 
  is_graph (del_vertex G x).
Proof.
  rewrite /del_vertex; split => //=. 
  - move => e /fsetDP [A B]. by rewrite !inE (srcP A) edges_atF. 
  - move => e /fsetDP [A B]. by rewrite !inE (tgtP A) edges_atF.
  - case: Hx => Hx. by rewrite !inE p_inP andbT pIO_Ni.
  - case: Hx => Hx. by rewrite !inE p_outP andbT pIO_No.
Qed.

Definition add_vertex (G : pre_graph) (x : VT) a := 
  {| vset := x |` vset G ;
     eset := eset G;
     src := src G;
     tgt := tgt G;
     lv := (lv G)[upd x := a];
     le := le G;
     p_in := p_in G;
     p_out := p_out G |}.

Notation "G  ∔  [ x , a ]" := (add_vertex G x a) (at level 20) : open_scope.

Global Instance add_vertex_graph (G : pre_graph) `{graph_G : is_graph G} (x : VT) a : 
  is_graph (add_vertex G x a).
Admitted.

Definition del_edges (G : pre_graph) (E : {fset ET}) := 
  {| vset := vset G;
     eset := eset G `\` E;
     src := src G;
     tgt := tgt G;
     lv := lv G;
     le := le G;
     p_in := p_in G;
     p_out := p_out G |}.

Global Instance del_edges_graph (G : pre_graph) `{graph_G : is_graph G} (E : {fset ET}) :
  is_graph (del_edges G E).
Proof. 
  split; try by apply graph_G. 
  all: move => e /fsetDP [He _]; by apply graph_G.
Qed.

Definition add_edge' (G : pre_graph) (e:ET) x u y :=
  {| vset := vset G;
     eset := e |` eset G;
     src := update (src G) e x;
     tgt := update (tgt G) e y;
     lv := lv G;
     le := update (le G) e u;
     p_in := p_in G;
     p_out := p_out G |}.

Definition add_edge (G : pre_graph) x u y := add_edge' G (fresh (eset G)) x u y.

Notation "G ∔ [ x , u , y ]" := (add_edge G x u y) (at level 20,left associativity) : open_scope.
Notation "G ∔ [ e , x , u , y ]" := (add_edge' G e x u y) (at level 20,left associativity) : open_scope.

(* TOTHINK: This is not an instance because [x \in vset G] is not
inferrable. One could box it though and make it inferrable through
some external hints *)
(** Note that we do not require [e] to be fresh, adding an alreay
existing edge merely overwrites that edge *)
Lemma add_edge_graph' (G : pre_graph) (graph_G : is_graph G) e x y u :
  x \in vset G -> y \in vset G -> is_graph (G ∔ [e,x, u, y]).
Admitted.

Lemma add_edge_graph (G : pre_graph) (graph_G : is_graph G) x y u :
  x \in vset G -> y \in vset G -> is_graph (add_edge G x u y).
Admitted.

Definition add_test (G : pre_graph) (x:VT) (a:test) := 
  {| vset := vset G;
     eset := eset G;
     src := src G;
     tgt := tgt G;
     lv := update (lv G) x [lv G x·a];
     le := le G;
     p_in := p_in G;
     p_out := p_out G |}.

(* TODO: all notations for graph operations should be left associative
and at the same level, because this is the only way in which they can
be parsed *)

Instance add_test_graph (G : pre_graph) `{graph_G : is_graph G} x a :
  is_graph (add_test G x a). 
Proof. split => //=; apply graph_G. Qed.

Notation "G [adt x <- a ]" := (add_test G x a) 
   (at level 2, left associativity, format "G [adt  x  <-  a ]") : open_scope.

(** ** Properties of the operations *)

Lemma edges_at_del (G : pre_graph) (z x : VT) : 
  edges_at (G \ z) x = edges_at G x `\` edges_at G z.
Admitted.

(** TODO: generalize to add_edge' *)
Lemma add_edgeV (G : pre_graph) (x y : VT) (u : term) : 
  is_graph (add_edge G x u y) -> ((x \in vset G) * (y \in vset G))%type.
Proof.
  intros graph_G. split.
  - rewrite [x](_ : _ = src (add_edge G x u y) (fresh (eset G))).
    + apply: srcP. by rewrite /add_edge !inE eqxx.
    + by rewrite /= update_eq.
  - rewrite [y](_ : _ = tgt (add_edge G x u y) (fresh (eset G))).
    + apply: tgtP. by rewrite /add_edge !inE eqxx.
    + by rewrite /= update_eq.
Qed. 

(** ** Commutation Lemmas *)

Lemma del_vertexC (G : pre_graph) (x y : VT) : (G \ x \ y)%O = (G \ y \ x)%O. 
Proof. 
  rewrite /del_vertex/=; f_equal. 
  - by rewrite fsetDDl fsetUC -fsetDDl.
  - by rewrite !edges_at_del fsetDDD fsetUC -fsetDDD.
Qed.

Lemma add_testC (G : pre_graph) x y a b :
  G[adt x <- a][adt y <- b] ≡G G[adt y <- b][adt x <- a].
Proof.
  split => //= z. 
  case: (altP (x =P y)) => xy; subst. 
  - rewrite !update_same. case: (altP (z =P y)) => zy; subst; rewrite !updateE //=. 
    by rewrite -dotA dotC dotA.
  - case: (altP (z =P x)) => zx; case: (altP (z =P y)) => zy; subst.
    by rewrite eqxx in xy. all: by rewrite !updateE.
Qed.



Lemma del_vertex_add_test (G : pre_graph) z x a : 
  (G \ z)[adt x <- a] ≡G G[adt x <- a] \ z.
Proof. done. Qed.

(** This does not hold for [add_edge] since [add_edge] takes the
lowest available edge, which may change after deleting [z]. *)
Lemma del_vertex_add_edge (G : pre_graph) z x y u e : z != x -> z != y ->
  e \notin eset G ->                                                      
  add_edge' (G \ z) e x u y ≡G (add_edge' G e x u y) \ z.
Proof.
  move => Hx Hy He. split => //=. 
Admitted.

Lemma add_edge_test (G : pre_graph) e x y z u a : 
  (G ∔ [e,x,u,y])[adt z <- a] ≡G G[adt z <- a] ∔ [e,x,u,y].
Proof. done. Qed.

(** ** Morphism Lemmas *)

Instance add_edge_morphism : Proper (weqG ==> eq ==> weq ==> eq ==> weqG) add_edge.
Proof. 
  move => G H [EV EE Es Et Elv Ele Ei Eo] ? x ? u v uv ? y ?. subst. 
  split => //=; rewrite -?EE -?EV //; exact: in_eqv_update.
Qed.

Instance add_edge_morphism' : Proper (weqG ==> eq ==> eq ==> weq ==> eq ==> weqG) add_edge'.
Proof. 
  move => G H [EV EE Es Et Elv Ele Ei Eo] ? x ? u v uv ? y ?. subst. 
  (* split => //=; rewrite -?EE -?EV //; exact: in_eqv_update. *)
Admitted.


Instance del_vertex_morphism : Proper (weqG ==> eq ==> weqG) del_vertex.
Proof. 
  move => G H [EV EE Es Et Elv Ele Ei Eo] ? x ?. subst. 
  split => //=; rewrite -?EE -?EV //. 
  rewrite /edges_at/incident. rewrite !EE. congr fsetD. 
  apply/fsetP => z. 
Admitted.

Instance add_test_morphism : Proper (weqG ==> eq ==> test_weq ==> weqG) add_test.
Admitted.

Lemma name_add_edge (G : pre_graph) x y u (e : ET) :
  e \notin eset G -> G ∔ [x,u,y] ⩭ add_edge' G e x u y.
Admitted.
Arguments name_add_edge [G x y u] e _.

  
Lemma oliso_wegG_test (G : pre_graph) (isG : is_graph G) z z' x a x' u y' : 
  z != x' -> z != y' ->
   ((G \ z) [adt x <- a] \ z') ∔ [x', u, y']
⩭ ((G \ z') ∔ [x', u, y'] \ z)[adt x <- a].
Proof. 
  move => Hz1 Hz2. 
  pose e : ET := fresh (vset (G \ z)).
  apply: oliso_trans. apply: (name_add_edge e).
  { admit. }
  apply weqG_oliso. 
  - admit.
  - admit.
  - (* the edge on the left may be different (lower) than the edge on the right. 
       Thus, we require a proper isomorphism step *)
    rewrite !del_vertex_add_test del_vertexC add_edge_test.
    rewrite del_vertex_add_test. 
Admitted.


(** ** Commutation with open/close *)

Arguments freshP [E].

Lemma close_add_edge (G : pre_graph) (x y : VT) u (isG : is_graph G) (isG' : is_graph (G ∔ [x, u, y])) : 
  close (G ∔ [x, u, y]) ≅ close G ∔ [close_v x, u, close_v y].
Proof.
  apply: liso_sym. 
  liso (bij_id) (fresh_bij bij_id freshP) (fun => false) => //. 
  4-5: exact: val_inj.
  - move => [e|]; by rewrite fresh_bijE /= updateE /= ?fresh_eqF.
  - move => [e|] /=; apply: val_inj; rewrite /= updateE ?fresh_eqF //. 
    by rewrite close_vK // add_edgeV.
  - move => [e|] /=; apply: val_inj; rewrite /= updateE ?fresh_eqF //. 
    by rewrite close_vK // add_edgeV.
Defined.

Definition close_add_vertex (G : pre_graph) (graph_G : is_graph G) x a : x \notin vset G -> 
  close (add_vertex G x a) ≅ liso.add_vertex (close G) a.
Proof.
  move => xG. apply: liso_sym. 
  liso (fresh_bij bij_id xG) bij_id (fun => false) => //. 2-5: move => *; exact: val_inj.
  move => [v|] => //=; by rewrite /= updateE // fsval_eqF.
Defined.

(* Lemma vfunE (G H : lgraph) (h : bij (close (open G)) (close (open H))) (x : G) : *)
(*   vfun_body h (inj_v x) = inj_v (h (openK _ x)). *)
(* Admitted. *)

Lemma vfun_bodyE (G : lgraph) (H : pre_graph) (graph_H : is_graph H)
     (h : bij (close (open G)) (close H)) (x : G) : 
  vfun_body h (inj_v x) = val (h (Sub (inj_v x) (in_imfsetT _ _))).
Proof. 
  unlock vfun_body. case: {-}_/idP => [p|]; last by rewrite in_imfsetT.
  by rewrite [in_imfsetT _ _](bool_irrelevance _ p).
Qed.

Definition close_add_test (G : pre_graph) (isG : is_graph G) x (Hx : x \in vset G) a :
  (close G)[tst close_v x <- a] ≅ close (G[adt x <- a]).
Admitted.

Section Transfer.
Variable (G : lgraph).

Lemma edges_at_open (x : G) (E : {set edge G}) :  
  confluence.edges_at G x = E ->
  edges_at (open G) (inj_v x) = [fset inj_e e | e in E].
Admitted.


Lemma fresh_imfsetF (T : finType) (f : T -> ET) (e : T) :
   f e == fresh [fset f x | x in T] = false.
Admitted. 

Lemma inj_v_open (x : G) : inj_v x \in vset (open G).
Proof. by rewrite in_imfset. Qed.
Hint Resolve inj_v_open.

Definition open_add_vertex a : 
  open (liso.add_vertex G a) ⩭ add_vertex (open G) (fresh (vset (open G))) a.
Proof. 
  rewrite /oliso; do 2 eexists.
  apply: liso_comp (liso_sym _) _. apply: openK.
  apply: liso_comp (liso_sym _). 2: apply: close_add_vertex freshP. 
  apply: add_vertex_liso => //. exact: openK.
Defined.

Set Nested Proofs Allowed.

Lemma open_add_vertexE : 
  ((forall a, open_add_vertex a (@inj_v (G ∔ a)%L None) = fresh (vset (open G)))
  *(forall a x, open_add_vertex a (@inj_v (G ∔ a)%L (Some x)) = @inj_v G x))%type. 
Proof. 
  split => *.
  all: rewrite /= vfun_bodyE /=.
  all: by rewrite imfset_bij_bwdE. 
Qed.

Lemma open_add_edge (x y : G) u : 
  open (G ∔ [x, u, y]) ⩭ open G ∔ [inj_v x, u, inj_v y].
Proof. 
  have X : is_graph (add_edge (open G) (inj_v x) u (inj_v y)). 
  { exact: add_edge_graph. }
  rewrite /oliso. do 2 eexists.
  apply: liso_comp (liso_sym _) _. apply: openK.
  (* (* Variant using close_add_edge *) *)
  (* apply: liso_comp (liso_sym (close_add_edge _ _)).   *)
  (* TODO: use close_add_edge *)
  liso (imfset_bij (@inj_v_inj G)) 
       (fresh_bij (imfset_bij (@inj_e_inj (edge G))) freshP)
       (fun => false).
  - move => v /=. by rewrite inj_vK.
  - case => [e|] //=. 
    + rewrite /update ifF ?inj_eK //. exact: fresh_imfsetF.
    + by rewrite /update ifT.
  - move => [e|]; apply: val_inj => /=;by rewrite /update /= ?fresh_imfsetF ?inj_eK // ifT.
  - move => [e|]; apply: val_inj => /=;by rewrite /update /= ?fresh_imfsetF ?inj_eK // ifT.
  - exact: val_inj.
  - exact: val_inj.
Defined.


Lemma oarc_open (x y : G) (e : edge G) u : 
  arc G e x u y -> oarc (open G) (inj_e e) (inj_v x) u (inj_v y).
Admitted.

Definition open_add_test (x : G) a : 
  open (G[tst x <- a]) ⩭ (open G)[adt inj_v x <- a].
Admitted.

End Transfer. 
   
 
(* TODO: use generic construction above *)
Definition bij_delv (T : finType) (z : T) :  
  bij { x:T | x \in [set~ z]} ([fset inj_v x | x in T] `\ inj_v z).
Proof.
  set A := ({ x | _ }). set B := _ `\ _.
  have f_proof (x : A) : inj_v (val x) \in [fset inj_v x | x in T] `\ inj_v z by admit.
  pose f (x : A) : B := Sub (inj_v (val x)) (f_proof x).
  have f_inv_proof1 (x : B) : val x \in [seq inj_v z | z in [set~ z] ]. admit.
  have f_inv_proof2 (x : B) : iinv (f_inv_proof1 x) \in [set~ z]. admit.
  pose f_inv (x : B) := Sub (iinv (f_inv_proof1 x)) (f_inv_proof2 x) : A. simpl in *.
  apply: (@Bij _ _ f f_inv).
  - move => [x Hx]. rewrite /f_inv/f. apply: val_inj => /=. 
    move: (f_inv_proof1 _) => /= H. rewrite in_iinv_f //. apply: in2W. exact: inj_v_inj.
  - move => [x Hx]. rewrite /f_inv/f. apply: val_inj => /=. 
Admitted.

Lemma open_del_vertex (G : lgraph) (z : G) (Hz : z \notin IO) (Hz' : inj_v z \notin pIO (open G)) :
  open (G \ [z, Hz]) ⩭ open G \ inj_v z.
Proof.
  do 2 eexists. rewrite <- openK.
  have B : bij (edge (confluence.del_vertex G z Hz)) (edge (close (open G \ inj_v z))) by admit.
  liso (@bij_delv G z) B (fun _ => false).
Admitted.

Definition add_edge_cong (G H : pre_graph) (h : G ⩭ H) x u y : G ∔ [x,u,y] ⩭ H ∔ [h x,u,h y].
Admitted.

(** * Open Step relation  *)

Section ostep.
Implicit Types (x y z : VT) (e : ET).

(** We turn the first argument into a parameter, this keeps
case/destruct from introducing a new name for G *)
Variant ostep (G : pre_graph) : pre_graph -> Type := 
| ostep_v1 x z e u : 
    edges_at G z = [fset e] -> z \notin pIO G -> oarc G e x u z -> x != z ->
    ostep G (add_test G  x [dom(u·lv G z)] \ z)
| ostep_v2 x y z e1 e2 u v : 
    edges_at G z = [fset e1;e2] -> e1 != e2 -> z \notin pIO G -> x != z -> y != z ->
    oarc G e1 x u z -> oarc G e2 z v y -> 
    ostep G ((G \ z) ∔ [maxn e1 e2, x,u·lv G z·v,y])
| ostep_e0 x e u :
    oarc G e x u x -> 
    ostep G ((del_edges G [fset e])[adt x <- [1∥le G e]])
| ostep_e2 x y e1 e2 u v : e1 != e2 ->
    oarc G e1 x u y -> oarc G e2 x v y ->
    ostep G ((del_edges G [fset e1;e2]) ∔ [maxn e1 e2,x,u∥v,y]).

Inductive osteps: pre_graph -> pre_graph -> Type@{S} :=
  | oliso_step:    CRelationClasses.subrelation oliso osteps
  | ostep_step:    CRelationClasses.subrelation ostep osteps
  | osteps_trans : CRelationClasses.Transitive osteps.

Lemma oliso_stepL G G' H : G ⩭ G' -> osteps G' H -> osteps G H.
Admitted.

Lemma ostep_stepL G G' H : ostep G G' -> osteps G' H -> osteps G H.
Admitted.

Lemma oliso_stepR G H H' : oliso H H' -> osteps G H' -> osteps G H.
Admitted.

Lemma edges_at_add_vertex (G : pre_graph) x a : x \notin vset G -> 
  edges_at (add_vertex G x a) x = fset0.
Admitted.

Lemma edges_at_add_edge (G : pre_graph) x y e u : e \notin eset G -> 
  edges_at (add_edge' G e x u y) y = e |` edges_at G y.
Proof.
  move => _.
  rewrite /edges_at/=. 
Admitted.

Lemma edges_at_add_edge' G e x y z u : 
  x != z -> y != z -> edges_at (G ∔ [e,x,u,y]) z = edges_at G z.
Admitted.


Lemma pIO_add_vertex (G : pre_graph) x a : pIO (add_vertex G x a) = pIO G. done. Qed.
Lemma pIO_add_edge (G : pre_graph) e x u y : pIO (add_edge' G e x u y) = pIO G. done. Qed.
Definition pIO_add := (pIO_add_edge,pIO_add_vertex).

Lemma pIO_fresh (G : pre_graph) (isG : is_graph G) x : 
  x \notin vset G -> x \notin pIO G.
Proof. apply: contraNN. rewrite !inE. case/orP => /eqP ->; [exact: p_inP|exact: p_outP]. Qed.

Lemma oarc_add_edge (G : pre_graph) e e' x y x' y' u u' : 
  oarc G e' x' u' y' -> oarc (G ∔ [e,x,u,y]) e' x' u' y'. 
Admitted.

Lemma oarc_del_edges (G : pre_graph) e x u y E : 
  e \notin E -> oarc G e x u y -> oarc (del_edges G E) e x u y.
Admitted.

Lemma oarc_added_edge (G : pre_graph) e x y u : oarc (G ∔ [e,x,u,y]) e x u y. 
Proof. 
  split. 
  - by rewrite !inE eqxx.
  - by left; split; rewrite /= update_eq. 
Qed.


Lemma oarc_edge_atL (G : pre_graph) e x y u : 
  oarc G e x u y -> e \in edges_at G x.
Proof. by case => E [[A B C]|[A B C]]; rewrite !inE E /incident ?A ?B eqxx. Qed.

Instance oarc_morphism : Proper (weqG ==> eq ==> eq ==> weq ==> eq ==> iff) oarc.
Admitted.

Lemma oarc_cnv (G : pre_graph) e x y u : oarc G e x u y <-> oarc G e y u° x. 
Proof. 
  wlog suff W : x u y / oarc G e x u y -> oarc G e y u° x. 
  { split; first exact: W. move/W. by rewrite cnvI. }
  case => E [[A B C]|[A B C]]; split => //; [right|left]. 
  all: rewrite ?A ?B; split => //. by rewrite cnvI.
Qed.

Lemma oarc_edge_atR (G : pre_graph) e x y u : 
  oarc G e x u y -> e \in edges_at G y.
Proof. rewrite oarc_cnv. exact: oarc_edge_atL. Qed.

Lemma oarc_del_vertex (G : pre_graph) z e x y u : 
  e \notin edges_at G z -> oarc G e x u y -> oarc (G \ z) e x u y.
Proof. move => Iz [edge_e H]. apply: conj H. by rewrite inE Iz. Qed.
  
Lemma add_edge_del_vertex (G : pre_graph) e x u y : G ∔ [e,x,u,y] \ y ≡G G \ y.
Admitted.
Definition add_edgeKr := add_edge_del_vertex.
Lemma add_edgeKl (G : pre_graph) e x u y : G ∔ [e,x,u,y] \ x ≡G G \ x.
Admitted.


Lemma add_testK (G : pre_graph) x a : G[adt x <- a] \ x ≡G G \ x.
Admitted.

Lemma add_vertexK (G : pre_graph) x a : add_vertex G x a \ x ≡G G.
Admitted.

Lemma edges_at_test (G : pre_graph) x a z : edges_at G[adt x <- a] z = edges_at G z. done. Qed.

Lemma edges_at_del_edges (G : pre_graph) z E : 
  edges_at (del_edges G E) z = edges_at G z `\` E. 
Proof. 
  rewrite /del_edges {1}/edges_at/incident /=. 
Admitted.

Lemma lv_add_edge (G : pre_graph) e x u y z : lv (G ∔ [e,x,u,y]) z = lv G z. done. Qed.

Definition step_order G H (s: ostep G H): nat :=
  match s with
  | ostep_v1 _ _ _ _ _ _ _ _ => 1
  | ostep_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 2
  | ostep_e0 _ _ _ _ => 3
  | ostep_e2 _ _ _ _ _ _ _ _ _ => 4
  end.

Definition oconnected (G : pre_graph) (isG : is_graph G) : Prop. 
Admitted.
Arguments oconnected G [isG].

Lemma no_lens (G : pre_graph) (isG : is_graph G) x y : x != y ->
  edges_at G x = edges_at G y -> x \notin pIO G -> y \notin pIO G -> ~ oconnected G.
Admitted.

Lemma no_flower (G : pre_graph) (isG : is_graph G) x : 
  (forall e, e \in edges_at G x -> src G e = tgt G e) -> x \notin pIO G -> ~ oconnected G.
Admitted.
  
Lemma contraPN (b : bool) (P : Prop) : (b -> ~ P) -> (P -> ~~ b).
Proof. case: b => //=. by move/(_ isT) => H /H. Qed.

Lemma contraPneq (T:eqType) (a b : T) (P : Prop) : (a = b -> ~ P) -> (P -> a != b).
Proof. move => A. by apply: contraPN => /eqP. Qed.

Lemma contraPeq (T:eqType) (a b : T) (P : Prop) : (a != b -> ~ P) -> (P -> a = b).
Proof. move => H HP. by apply: contraTeq isT => /H /(_ HP). Qed.

Lemma eqfset1 (T : choiceType) (x y : T) : ([fset x] == [fset y]) = (x == y).
Admitted.

Lemma oarc_uniqeR (G : pre_graph) e e' x y u : 
  edges_at G y = [fset e] -> oarc G e' x u y -> e' = e.
Admitted.

Lemma oarc_uniqeL (G : pre_graph) e e' x y u : 
  edges_at G x = [fset e] -> oarc G e' x u y -> e' = e.
Admitted.

Lemma oarc_injL (G : pre_graph) e x x' y u u' : 
  oarc G e x u y -> oarc G e x' u' y -> x = x'.
Admitted.

Lemma oarc_weq (G : pre_graph) e x y u u' : 
  x != y -> oarc G e x u y -> oarc G e x u' y -> u ≡ u'.
Admitted.

Lemma oarc_loop G e e' x y x' u u' : oarc G e x u y -> oarc G e' x' u' x' -> x = y.
Admitted.

Lemma same_oarc G e x y x' y' u u' : oarc G e x u y -> oarc G e x' u' y' ->
  [/\ x = x', y = y' & u ≡ u'] + [/\ x = y', y = x' & u ≡ u'°].
Admitted.   
    

Lemma osteps_refl (G : pre_graph) (isG : is_graph G) : osteps G G.
Proof. apply: oliso_step. do 2 eexists. exact: liso_id. Qed.

Ltac e2split := do 2 eexists; split; [split|].

Lemma add_edge_flip (G : pre_graph) (isG : is_graph G) e x y u v: 
  u° ≡ v ->
  x \in vset G -> y \in vset G -> G ∔ [e,x,u,y] ⩭ G ∔ [e,y,v,x].
Admitted.

Lemma del_edges_add_test (G : pre_graph) E x a : 
  (del_edges G E)[adt x <- a] ≡G del_edges G[adt x <- a] E. 
Proof. done. Qed.

Lemma del_edgesK (G : pre_graph) E z :
  E `<=` edges_at G z -> (del_edges G E) \ z ≡G G \ z.
Proof. 
  move => subE. split => //=. 
  by rewrite edges_at_del_edges fsetDDD (fsetUidPr _ _ subE).
Qed.

Notation "G - E" := (del_edges G E) : open_scope.

Lemma del_vertex_edges G E z : G \ z - E ≡G (G - E)\z.
Proof. 
  split => //. 
  by rewrite /del_vertex/= edges_at_del_edges fsetDDD fsetDDl fsetUC.
Qed.

Lemma degree_one_two G x y e e1 e2 : e1 != e2 -> 
  edges_at G x = [fset e] -> edges_at G y = [fset e1;e2] -> x != y.
Admitted.

Lemma vset_del_vertex G x z : x \in vset G -> x != z -> x \in vset (G \ z).
Proof. by rewrite /= !inE => -> ->. Qed.

Lemma vset_del_edges G E x : x \in vset G -> x \in vset (G - E).
Proof. done. Qed.

Hint Resolve vset_del_vertex vset_del_edges : vset.

Lemma oarc_vsetL G (isG : is_graph G) e x y u : 
  oarc G e x u y -> x \in vset G.
Admitted.

Lemma oarc_vsetR G (isG : is_graph G) e x y u : 
  oarc G e x u y -> y \in vset G.
Admitted.

Hint Resolve oarc_vsetL oarc_vsetR : vset.

Lemma fset2_inv (T : choiceType) (x y x' y' : T) : x != y ->
  [fset x;y] = [fset x';y'] -> (x = x' /\ y = y') + (x = y' /\ y = x').
Proof.
  move => /negbTE D /fsetP H. move: (H x). rewrite !inE eqxx /= => /esym. 
  case/orb_sum => /eqP ?;[left|right]; subst; move: (H y).
  - rewrite !inE eqxx orbT eq_sym D. by move/esym/eqP.
  - rewrite !inE eqxx orbT [y == y']eq_sym D orbF. by move/esym/eqP.
Qed.

Lemma fset_cardI1 (T : choiceType) (A B : {fset T}) (x y : T) : 
  #|`A `&` B| = 1%N -> x \in A -> x \in B -> y \in A -> y \in B -> x = y.
Admitted.

Lemma close_same_step (Gl Gr : pre_graph) (isGl : is_graph Gl) (isGr : is_graph Gr) : 
  Gl ≡G Gr -> Σ Gl' Gr' : pre_graph, osteps Gl Gl' * osteps Gr Gr' * (Gl' ≡G Gr').
Proof. move => E. do 2 eexists; split;[split|]; by try exact: osteps_refl. Qed.

Lemma fset2_cases (T : choiceType) (x y x' y' : T) : x != y -> x' != y' ->
  let A := [fset x;y] in 
  let B := [fset x';y'] in 
  (A = B) + [disjoint A & B] + (Σ z : T, A `&` B = [fset z]).
Proof.
  move => D D' A B.
Admitted.

Inductive maxn_cases n m : nat -> Type := 
| MaxnR of n <= m : maxn_cases n m m
| MaxnL of m < n : maxn_cases n m n.

Lemma maxnP n m : maxn_cases n m (maxn n m).
Proof. 
  case: (leqP n m) => H.
  - rewrite (maxn_idPr H). by constructor.
  - rewrite (maxn_idPl _); [by constructor|exact: ltnW].
Qed.

Lemma maxn_eq n m : (maxn n m == n) || (maxn n m == m).
Proof. case: maxnP; by rewrite !eqxx. Qed.

Lemma mem_maxn n m (A : {fset nat}) : n \notin A -> m \notin A -> maxn n m \notin A.
Proof. by case: maxnP. Qed.

Lemma maxn_fset2 n m : maxn n m \in [fset n; m].
Proof. case: maxnP; by rewrite !in_fset2 eqxx. Qed.
  
Lemma maxn_fsetD n m (A : {fset nat}) : maxn n m \notin A `\` [fset n; m]. 
Proof. by rewrite inE negb_and negbK maxn_fset2. Qed.

Lemma fset2_maxn_neq n m x : x \notin [fset n; m] -> x != maxn n m.
Proof. apply: contraNneq => ->. exact: maxn_fset2. Qed.

Lemma edges_atC G e x y u : edges_at (G ∔ [e,x,u,y]) =1 edges_at (G ∔ [e,y,u°,x]).
Admitted.

Lemma add_edge_del_edges (G : pre_graph) e E x y u : 
  e \notin E -> G ∔ [e,x,u,y] - E ≡G (G - E) ∔ [e,x,u,y]. 
Proof. move => He. split => //=. by rewrite fsetUDl mem_fsetD1. Qed.

Lemma add_edge_del_edgesK (G : pre_graph) e E x y u : 
  e \in E -> G ∔ [e,x,u,y] - E ≡G (G - E). 
Admitted.

Lemma del_edges_vertexK (G : pre_graph) E z : 
  E `<=` edges_at G z -> (G - E) \ z ≡G G \ z.
Admitted.

Lemma del_edges_vertex (G : pre_graph) E z : 
  (G - E) \ z ≡G G \ z - E.
Proof. split => //=. by rewrite edges_at_del_edges fsetDDD fsetDDl fsetUC. Qed.

Lemma add_test_edge (G : pre_graph) e x y z a u : 
  (G[adt z <- a] ∔ [e,x,u,y])%O = ((G ∔ [e,x,u,y])[adt z <- a])%O.
Proof. done. Qed.

Lemma del_edges_edges (G : pre_graph) E E' : 
  G - E - E' ≡G G - (E `|` E').
Proof. split => //=. by rewrite fsetDDl. Qed.

Lemma add_edge_edge G e e' x y x' y' u u' : e != e' ->
  G ∔ [e,x,u,y] ∔ [e',x',u',y'] ≡G G ∔ [e',x',u',y'] ∔ [e,x,u,y].
Admitted.

(*TOTHINK: this looks messier than needed *)
Lemma edges_replace (G : pre_graph) (z z' : VT) (e1 e2 e2' : ET) (x : VT) (u : term) :
    edges_at G z = [fset e1; e2] -> edges_at G z' = [fset e2; e2'] ->
    e1 != e2 -> e2 != e2' -> e1 != e2' -> 
    edges_at ((G \ z) ∔ [maxn e1 e2, x, u, z']) z' = [fset maxn e1 e2; e2'].
Proof.
  move => Iz Iz' /negbTE E1 /negbTE E2 /negbTE E3. 
  rewrite edges_at_add_edge /= ?Iz ?maxn_fsetD //.
  suff -> : edges_at (G \ z) z' = [fset e2'] by [].
  rewrite edges_at_del Iz Iz'. apply/fsetP => e. rewrite !inE negb_or -andbA.
  apply/and3P/idP => [[A B /orP [/eqP C|/eqP C]]|/eqP->] ; subst. 
  - by rewrite eqxx in B. 
  - by rewrite eq_sym E3 in A.
  - by rewrite eqxx orbT eq_sym E3 eq_sym E2.
Qed.

Lemma pardot u v a : (u ∥ v)·a ≡ u ∥ v·a. Admitted.

Lemma critical_pair1 u v (a :test) : dom ((u∥v°)·a) ≡ 1 ∥ u·a·v.
Proof. by rewrite -dotA A10 cnvdot cnvtst pardot. Qed.

Lemma critical_pair2 u v : (1∥u)·(1∥v) ≡ 1∥(u∥v).
Proof. Admitted.

Lemma edges_at_oarc G e x y z u : 
  e \in edges_at G z -> oarc G e x u y -> x = z \/ y = z.
Admitted.


Lemma add_test_merge G x a b : 
  G[adt x <- a][adt x <- b] ≡G G[adt x <- [a·b]].
Proof. 
  constructor => //= y yG. 
  case: (altP (y =P x)) => [->|?]; rewrite !updateE //=.
  by rewrite dotA.
Qed.

Lemma par_tst_cnv (a : test) u : a ∥ u° ≡ a ∥ u.
Proof. by rewrite -[a∥u]/(term_of [a∥u]) -(@cnvtst [a∥u]) /= cnvpar cnvtst. Qed.

Lemma oarcxx_le G e x u : oarc G e x u x -> 1∥le G e ≡ 1∥u.
Proof. by case => _ [[_ _ A]|[_ _ A]]; rewrite A ?par_tst_cnv. Qed.


Proposition local_confluence (G : pre_graph) (isG : is_graph G) Gl Gr : 
  oconnected G ->
  ostep G Gl -> ostep G Gr -> Σ Gl' Gr', osteps Gl Gl' * osteps Gr Gr' * (Gl' ≡G Gr'). 
Proof with eauto with typeclass_instances.
  move => conn_G S1 S2.
  wlog : Gl Gr S1 S2 / step_order S1 <= step_order S2.
  { move => W. case/orb_sum: (leq_total (step_order S1) (step_order S2)) => SS.
    - exact: W SS.
    - case: (W _ _ _ _ SS) => H' [G'] [[stpG stpH] E]. 
      do 2 eexists; split; first split. 1-2:eassumption. by symmetry. }
  (* naming convention: primes on the second/right rule *)
  destruct S1 as [x  z  e  u  Iz  zIO  arc_e  xDz |
                  x y z e1 e2 u v Iz e1De2 zIO xDz yDz arc_e1 arc_e2|
                  x e u arc_e |
                  x y e1 e2 u v e1De2 arc_e1 arc_e2];
  destruct S2 as [x' z' e' u' Iz' zIO' arc_e' xDz'|
                  x' y' z' e1' e2' u' v' Iz' e1De2' zIO' xDz' yDz' arc_e1' arc_e2'|
                  x' e' u' arc_e' |
                  x' y' e1' e2' u' v' e1De2' arc_e1' arc_e2'];
  rewrite //=; move => CASE_TAG.
  - (* V1 / V1 *) 
    case: (altP (z =P z')) => [E|D]. 
    + (* same instance *)
      subst z'. 
      have ? : e' = e by apply: oarc_uniqeR arc_e'. subst e'.
      have ? : x = x' by apply: oarc_injL arc_e arc_e'. subst x'.
      apply: close_same_step. 
      suff -> : test_weq [dom (u·lv G z)] [dom (u'·lv G z)] by [].
      by rewrite /test_weq/= (oarc_weq _ arc_e arc_e').
    + (* distinct instances *)
      have E : e != e'. 
      { apply: contraPneq conn_G => ?. subst e. apply: no_lens zIO zIO' => //. congruence. }
      gen have H,Hz : z z' x x' e e' u u' Iz Iz' arc_e' arc_e E {xDz xDz' zIO zIO' D} / z != x'. 
      { apply: contraTneq E => ?. subst x'. 
        rewrite negbK eq_sym -in_fset1 -Iz. apply: oarc_edge_atL arc_e'. }
      have {H} Hz' : z' != x by apply: H arc_e arc_e' _ ; rewrite // eq_sym.
      do 2 eexists. split. split. 
      * eapply ostep_step, ostep_v1. 3: eapply oarc_del_vertex. 4: apply arc_e'.
        all: try done. 
        by rewrite edges_at_del /= !edges_at_test Iz' Iz mem_fsetD1 // inE.
        by rewrite edges_at_test Iz inE eq_sym.
      * eapply ostep_step, ostep_v1. 3: eapply oarc_del_vertex. 4: apply arc_e.
        all: try done. 
        by rewrite edges_at_del /= !edges_at_test Iz' Iz mem_fsetD1 // inE eq_sym.
        by rewrite edges_at_test Iz' inE.
      * by rewrite !del_vertex_add_test del_vertexC add_testC /= !updateE. 
  - (* V1 / V2 *)
    have zDz' : z != z' by apply: degree_one_two Iz Iz'.
    case: (boolP (z \in [fset x';y'])) => [z_xy'|xD'].
    + (* double pendant *)
      wlog: x' y' xDz' yDz' u' v' e1' e2' arc_e1' arc_e2' Iz' e1De2' {z_xy'} / z = y' => [W|?].
      { move: z_xy'. rewrite !inE. case/orb_sum => /eqP E ; last exact: W. 
        rewrite -> oarc_cnv in arc_e1',arc_e2'. 
        move/(_ y' x' yDz' xDz' _ _ _ _ arc_e2' arc_e1') in W. rewrite fsetUC eq_sym in W.
        case: W => // Gl [Gr] [[S1 S2] WG]. exists Gl. exists Gr. do 2 (split => //). 
        apply: oliso_stepL S2. rewrite maxnC. apply: add_edge_flip; eauto with vset.
        by rewrite !cnvdot cnvtst dotA. }
      subst y'. 
      have ? : e2' = e by apply: oarc_uniqeR arc_e2'. subst e2'. 
      have ? : x = z' by apply: oarc_injL arc_e arc_e2'. subst x. 
      have Dz : x' != z. 
      { apply: contra_neq e1De2' => ?. subst. exact: oarc_uniqeL arc_e1'. }
      e2split.
      * eapply ostep_step, ostep_v1. 
        3: { apply: oarc_del_vertex arc_e1'. by  rewrite Iz inE. }
        all: try done.
        rewrite edges_at_del !edges_at_test Iz Iz'. admit. 
      * eapply ostep_step, ostep_v1. 
        3: exact: oarc_added_edge. 
        all: try done.
        rewrite edges_at_add_edge ?edges_at_del. admit. admit.
      * rewrite /= updateE. set a := lv G z. set b := lv G z'. 
        rewrite -del_vertex_add_test del_vertexC add_testK. 
        rewrite -del_vertex_add_test add_edgeKr.
        apply: add_test_morphism => //. rewrite /test_weq/=. 
        by rewrite dotA -A13 !dotA (oarc_weq _ arc_e2' arc_e).
    + (* independent case *)
      e2split. 
      * eapply ostep_step, ostep_v2. 
        6: { apply: oarc_del_vertex. 2: apply: arc_e1'. rewrite edges_at_test Iz. admit. }
        6: { apply: oarc_del_vertex. 2: apply: arc_e2'. rewrite edges_at_test Iz. admit. }
        all: try done. 
        rewrite edges_at_del !edges_at_test. admit.
      * eapply ostep_step, ostep_v1. 
        3: { apply: oarc_add_edge. apply: oarc_del_vertex arc_e. admit. }
        all: try done. 
        admit.
      * set e12 := maxn _ _. set a := lv G z. set b := lv G z'. set a' := lv _ z. set b' := lv _ z'. 
        have <- : a = a' by []. have <- : b = b'. rewrite /b /b' /= updateE //. admit. 
        rewrite del_vertexC -del_vertex_add_test add_edge_test. rewrite -del_vertex_add_edge. done.
        admit. admit. by rewrite /= inE negb_and negbK Iz' !inE maxn_eq.
  - (* V1 / E0 - no nontrivial interaction *)
    have De : e != e'. 
    { apply: contra_neq xDz => ?; subst e'. exact: oarc_loop arc_e arc_e'. }
    have Dx' : x' != z. 
    { apply: contra_neq De => ?; subst x'. symmetry. exact: oarc_uniqeL arc_e'. }
    e2split.
    * eapply ostep_step, ostep_e0. apply: oarc_del_vertex arc_e'. 
      by rewrite Iz !inE eq_sym.
    * eapply ostep_step, ostep_v1. 3: { apply: oarc_del_edges arc_e. by rewrite inE. }
      all: try done. 
      by rewrite edges_at_test edges_at_del_edges Iz mem_fsetD1 // inE eq_sym.
    * rewrite /= updateE 1?eq_sym //. 
      rewrite del_vertex_edges -del_edges_add_test. 
      by rewrite del_vertex_add_test add_testC. 
  - (* V1 / E2 - no nontrivial interaction *) admit.
  - (* V2 / V2 *) 
    move: (fset2_cases e1De2 e1De2') => [[E|D]|[e He]].
    + (* same instance up to direction *)
      have ? : z = z' ; [|subst z'].
      { apply: contraPeq conn_G => H. by apply: no_lens zIO zIO'; congruence. }
      wlog [? ?] : x' y' e1' e2' u' v' e1De2' Iz' arc_e1' arc_e2' xDz' yDz' {E} / e1 = e1' /\ e2 = e2'.
      { move => W.
        case: (fset2_inv e1De2 E) => [[? ?]|[? ?]]; first exact: W.
        move/(_ y' x' e2' e1' v'° u'°) in W. rewrite fsetUC eq_sym in W. 
        case: W => //. 1-2: by rewrite <- oarc_cnv. 
        move => Gl [Gr] [[S1 S2] E']. e2split;[exact: S1| |exact: E']. 
        (* TODO: this is exactly the same as in the first wlog argument -> lemma *)
        apply: oliso_stepL S2. rewrite maxnC. apply: add_edge_flip; eauto with vset.
        by rewrite !cnvdot cnvtst dotA. }
      eapply close_same_step. 1-2: apply add_edge_graph'; eauto with vset typeclass_instances.
      admit.
     + (* independent instances *) admit.
     + (* overlap in one edge *) 
       wlog ? : e1 e2 x y u v  arc_e1 arc_e2 Iz e1De2 zIO xDz yDz He / e = e2 ; [move => W|subst e]. 
       { have: e \in [fset e1;e2]. { move/fsetP : He => /(_ e). rewrite in_fset1 eqxx. by case/fsetIP. }
         rewrite inE. case/orb_sum => /fset1P => E; last exact: W.
         rewrite -> oarc_cnv in arc_e1,arc_e2. 
         move/(_ _ _ _ _ _ _ arc_e2 arc_e1) in W. rewrite fsetUC eq_sym in W.
         case: W => // Gl [Gr] [[S1 S2] WG]. exists Gl. exists Gr. do 2 (split => //). 
         apply: oliso_stepL S1. rewrite maxnC. apply: add_edge_flip; eauto with vset.
         by rewrite !cnvdot cnvtst dotA. }
       wlog ? : e1' e2' x' y' u' v'  arc_e1' arc_e2' Iz' e1De2' xDz' yDz' He / e2 = e1' ; [move => W|subst e1'].
       { have: e2 \in [fset e1';e2']. { move/fsetP : He => /(_ e2). rewrite in_fset1 eqxx. by case/fsetIP. }
         rewrite inE. case/orb_sum => /fset1P => E; first exact: W.
         rewrite -> oarc_cnv in arc_e1',arc_e2'. 
         move/(_ _ _ _ _ _ _ arc_e2' arc_e1') in W. rewrite fsetUC eq_sym in W.
         case: W => // Gl [Gr] [[S1 S2] WG]. exists Gl. exists Gr. do 2 (split => //). 
         apply: oliso_stepL S2. rewrite maxnC. apply: add_edge_flip; eauto with vset.
         by rewrite !cnvdot cnvtst dotA. }
       have {He} E1 : e1 != e2'.
       { apply: contraNneq e1De2 => E. by rewrite -in_fset1 -He !inE E !eqxx. }
       have {arc_e2} [? ? C] : [/\ z = x' , y = z' & v ≡ u' ];[| subst x' y].
       { case: (same_oarc arc_e2 arc_e1') => [//|[A B C]]; subst.
         move: (oarc_edge_atR arc_e1). by rewrite Iz' !inE (negbTE e1De2) (negbTE E1). }
       (* x -[e1,u] -> z -[e2,v]-> z' -[e2',v'] y' *)
       e2split. 
       * eapply ostep_step,ostep_v2. 
         6: apply: oarc_added_edge. 
         6: apply: oarc_add_edge. 6: apply: oarc_del_vertex arc_e2'. 
         all: try done. 
         -- exact: edges_replace.
         -- by case/orP : (maxn_eq e1 e2) => /eqP ->.
         -- apply: contraTneq (oarc_edge_atL arc_e1) => ->. by rewrite Iz' !inE negb_or e1De2.
         -- by rewrite Iz !inE negb_or eq_sym E1 eq_sym.
       * eapply ostep_step,ostep_v2. 
         7: apply: oarc_added_edge.
         6: apply: oarc_add_edge. 6: apply: oarc_del_vertex arc_e1.
         all: try done. 
         -- rewrite edges_atC fsetUC maxnC. apply: edges_replace; by rewrite // 1?fsetUC 1?eq_sym.
         -- by case/orP : (maxn_eq e2 e2') => /eqP ->.
         -- apply: contraTneq (oarc_edge_atR arc_e2') => ->.
            by rewrite Iz !inE negb_or eq_sym E1 eq_sym.
         -- by rewrite Iz' !inE negb_or e1De2.
       * rewrite !add_edgeKr !add_edgeKl /= del_vertexC. 
         by rewrite maxnA !dotA C.
  - (* V2 / E0 *) 
    have xDz' : z != x'. admit.
    (* { apply: contraTneq isT => ?. subst x'. admit. } *)
    have He : e' \notin edges_at G z. admit.
    have He' : e' != maxn e1 e2. admit.
    e2split. 
    * eapply ostep_step,ostep_e0. apply: oarc_add_edge. exact: oarc_del_vertex arc_e'.
    * eapply ostep_step,ostep_v2. 
      6: { apply: oarc_del_edges arc_e1. 
           rewrite inE. apply: contraNneq He => <-. by rewrite Iz !inE eqxx. }
      6: { apply: oarc_del_edges arc_e2. 
           rewrite inE. apply: contraNneq He => <-. by rewrite Iz !inE eqxx. }
      all: try done. 
      by rewrite edges_at_test edges_at_del_edges -Iz mem_fsetD1.
    * rewrite /= !updateE //. rewrite add_edge_del_edges ?inE 1?eq_sym //. 
      by rewrite -del_vertex_add_test del_edges_vertex add_test_edge.
  - (* V2 / E2 *) 
    case: (boolP (z \in [fset x'; y'])) => Hz.
    + (* complete overlap *) 
      wlog ? : x' y' e1' e2' u' v' e1De2' arc_e1' arc_e2' {Hz} / z = y'.
      { move => W. move: Hz. rewrite in_fset2. case/orb_sum => /eqP ?; last exact: W.
        subst x'. rewrite -> oarc_cnv in arc_e2', arc_e1'. 
        case: (W _ _ _ _ _ _ _ arc_e2' arc_e1'); rewrite 1?eq_sym //.
        move => Gl' [Gr'] [[Sl Sr] E]. e2split; [exact: Sl| |exact: E].
        apply: oliso_stepL Sr. rewrite fsetUC maxnC. apply: add_edge_flip; eauto with vset.
        by rewrite cnvpar parC. }
      subst y'. 
      wlog ? : e1 e2 u v x y e1De2 arc_e1 arc_e2 xDz yDz Iz / e1' = e1.
      { move => W. move:(oarc_edge_atR arc_e1'). 
        rewrite Iz in_fset2. case/orb_sum => /eqP ? ; first exact: W.
        subst e1'. rewrite -> oarc_cnv in arc_e2, arc_e1. 
        case: (W _ _ _ _ _ _ _ arc_e2 arc_e1); rewrite // 1?eq_sym 1?fsetUC //.
        move => Gl [Gr] [[Sl Sr] E]. e2split; [ | exact: Sr|exact: E].
        apply: oliso_stepL Sl. rewrite maxnC. apply: add_edge_flip; eauto with vset.
        by rewrite !cnvdot cnvtst dotA. }
      subst e1'. 
      have /eqP ? : e2' == e2; [|subst e2'].
      { move:(oarc_edge_atR arc_e2'). by rewrite Iz in_fset2 eq_sym (negbTE e1De2'). }
      have ? := oarc_injL arc_e1 arc_e1'. subst x'.
      rewrite -> oarc_cnv in arc_e2. have ? := (oarc_injL arc_e2 arc_e2'); subst y.
      have Eu : u ≡ u' by apply: oarc_weq arc_e1 arc_e1'.
      have Ev : v° ≡ v' by apply: oarc_weq arc_e2 arc_e2'.
      move => {arc_e1 arc_e1' arc_e2 arc_e2' yDz e1De2'}.
      e2split.
      * eapply ostep_step,ostep_e0. apply: oarc_added_edge.
      * eapply ostep_step,ostep_v1. 3: apply: oarc_added_edge. 
        all: try done. 
        by rewrite edges_at_add_edge ?edges_at_del_edges -Iz ?fsetDv ?fsetU0 //= Iz maxn_fsetD.
      * rewrite /= !updateE.
        rewrite -del_vertex_add_test add_edgeKr add_edge_del_edgesK ?inE ?eqxx //.
        rewrite del_vertex_edges. 
        rewrite !del_edges_vertexK ?fsubUset ?fsub1set ?Iz ?in_fset2 ?eqxx ?maxn_eq //.
        apply: add_test_morphism => //=. by rewrite /test_weq/= -Eu -Ev critical_pair1.
    + (* independent case *)
      rewrite in_fset2 negb_or ![z == _]eq_sym in Hz. case/andP : Hz => xDz' yDz'.
      gen have H,H1 : e1' u' {e1De2'} arc_e1' / e1' \notin edges_at G z.
      { apply/negP => H. 
        case: (edges_at_oarc H arc_e1') => ?; subst; by rewrite ?eqxx in xDz' yDz'. }
      move: (H _ _ arc_e2') => H2 {H}.
      have He1 : e1 \notin [fset e1'; e2']. 
      { apply/negP. by case/fset2P => ?; subst; rewrite Iz !in_fset2 !eqxx in H1 H2. }
      have He2 : e2 \notin [fset e1'; e2']. 
      { apply/negP. by case/fset2P => ?; subst; rewrite Iz !in_fset2 !eqxx ?orbT in H1 H2. }
      set e := maxn e1 e2. set e' := maxn e1' e2'.
      have ? : e' != e. 
      { rewrite /e /e' eq_sym. case: (maxnP e1 e2) => _; exact: fset2_maxn_neq. }
      e2split. 
      * eapply ostep_step,ostep_e2. 
        3:{ apply: oarc_add_edge. exact: oarc_del_vertex arc_e2'. }
        2:{ apply: oarc_add_edge. exact: oarc_del_vertex arc_e1'. } 
        done.
      * eapply ostep_step,ostep_v2. 
        7: { apply: oarc_add_edge. exact: oarc_del_edges arc_e2. }
        6: { apply: oarc_add_edge. exact: oarc_del_edges arc_e1. }
        all: try done.
        rewrite edges_at_add_edge' // edges_at_del_edges. 
        by rewrite -fsetDDl !mem_fsetD1.
      * rewrite /=. 
        rewrite -del_vertex_add_edge ?[z == _]eq_sym //= ?maxn_fsetD //.
        rewrite del_edges_vertex add_edge_edge //.
        rewrite add_edge_del_edges //. exact: mem_maxn.
  - (* E0 / E0 *)
    case: (altP (e =P e')) => [?|xDx']; first subst e'.
    + (* same loop *)
      have ? : x' = x by case: (same_oarc arc_e arc_e') => [[? ? ?]|[? ? ?]]; subst.
      subst. exact: close_same_step. 
    + (* two independent loops *)
      e2split.
      * eapply ostep_step,ostep_e0. apply: oarc_del_edges arc_e'. by rewrite inE eq_sym.
      * eapply ostep_step,ostep_e0. apply: oarc_del_edges arc_e. by rewrite inE.
      * rewrite /=. by rewrite -!del_edges_add_test add_testC !del_edges_edges fsetUC.
  - (* E0 / E2 *) 
    case: (boolP (e \in [fset e1'; e2'])) => He.
    + (* parallel loops *)
      wlog ? : e1' e2' u' v' x' y' arc_e1' arc_e2' e1De2' {He} / e = e1'.
      { move => W. move: He. rewrite in_fset2. case/orb_sum => /eqP E; first exact: W.
        case: (W _ _ _ _ _ _ arc_e2' arc_e1' _ E); rewrite 1?eq_sym //.
        move => Gl [Gr] [[Sl Sr] Elr]. e2split; [exact: Sl | | exact: Elr].
        rewrite fsetUC maxnC. apply: oliso_stepL Sr. eapply weqG_oliso.
        - admit.
        - admit.
        - by rewrite parC. }
      subst e1'. move: (oarc_loop arc_e1' arc_e) => ?. subst y'.
      have [?] : x' = x by case: (same_oarc arc_e arc_e1') => [] [? ? ?]; congruence.
      subst x'. 
      e2split. 
      * eapply ostep_step,ostep_e0. apply: oarc_del_edges arc_e2'.
        by rewrite inE eq_sym.
      * eapply ostep_step,ostep_e0. apply: oarc_added_edge. 
      * rewrite /= !updateE. 
        rewrite -del_edges_add_test del_edges_edges add_edge_del_edgesK ?inE ?eqxx //.
        rewrite del_edges_edges [[fset _ ; _ ; _]]fsetUC [maxn _ _ |` _]mem_fset1U ?maxn_fset2 //.
        rewrite add_test_merge. apply: add_test_morphism => //.
        rewrite /test_weq/= (oarcxx_le arc_e1') (oarcxx_le arc_e2').
        by rewrite critical_pair2.
    + (* independent case *)
      set e' := maxn _ _. 
      have eDe' : e != e' by rewrite fset2_maxn_neq .
      e2split. 
      * eapply ostep_step,ostep_e2; [exact: e1De2'| |].
        -- apply: oarc_del_edges arc_e1'. apply: contraNN He. by rewrite !inE eq_sym => ->.
        -- apply: oarc_del_edges arc_e2'. apply: contraNN He. by rewrite !inE eq_sym => ->.
      * eapply ostep_step,ostep_e0. apply: oarc_add_edge. exact: oarc_del_edges arc_e.
      * rewrite /= -/e' updateE //. 
        rewrite -del_edges_add_test add_edge_del_edges ?del_edges_edges ?inE 1?eq_sym //.
        by rewrite fsetUC -add_test_edge.
  - (* E2 / E2 *)
    case: (fset2_cases e1De2 e1De2') => [[E|D]|[e He]].
    + (* fully overlapping instances *)
      wlog [? ?] : e1' e2' u' v' e1De2' arc_e1' arc_e2' {E} / e1 = e1' /\ e2 = e2'.
      { move => W. case: (fset2_inv e1De2 E) => [|[? ?]]; first exact: W.
        subst e2' e1'. rewrite [[fset e2;e1]]fsetUC [maxn e2 e1]maxnC. 
        case: (W _ _ _ _ _ arc_e2' arc_e1') => // Gl [Gr] [[Sl Sr] EG].
        e2split; [exact: Sl| |exact: EG]. apply: oliso_stepL Sr. 
        apply weqG_oliso. 1-2: apply: add_edge_graph'; eauto with vset.
        by rewrite parC. }
      subst e1' e2'. 
      wlog [? ? Hu] : x' y' u' v' {arc_e1'} arc_e2' / [/\ x = x', y = y' & u ≡ u'].
      { move => W. 
        case: (same_oarc arc_e1 arc_e1') => [|[? ? Hu]]; first exact: W.
        subst x' y'. rewrite -> oarc_cnv in arc_e2'. case: (W _ _ u'° _ arc_e2') => //.
        move => Gl [Gr] [[Sl Sr] EG]. 
        e2split; [exact: Sl| |exact: EG]. apply: oliso_stepL Sr. 
        apply: add_edge_flip; eauto with vset. by rewrite cnvpar. }
      subst x' y'. 
      (* There are actually two cases here *)
      have [Hv|[? Hv]]: ((v ≡ v') + (x = y /\ v ≡ v'°))%type.
      { case: (same_oarc arc_e2 arc_e2'); firstorder. }
      * apply close_same_step. 1-2: apply: add_edge_graph'; eauto with vset.
        by rewrite Hu Hv.
      * subst y. e2split. 
        -- eapply ostep_step,ostep_e0. apply: oarc_added_edge.
        -- eapply ostep_step,ostep_e0. apply: oarc_added_edge.
        -- rewrite /= !updateE !add_edge_del_edgesK ?in_fset1 ?eqxx //.
           apply: add_test_morphism => //. rewrite /test_weq/=.
           rewrite Hu Hv. rewrite [u'∥_]parC parA -[1]/(term_of [1]) par_tst_cnv.
           by rewrite -parA [v'∥_]parC.
    + (* independent instances *)
      move: (fdisjointP D) => D1. rewrite fdisjoint_sym in D. move: (fdisjointP D) => {D} D2.
      e2split. 
      * apply ostep_step,ostep_e2. 
        -- exact: e1De2'.
        -- apply: oarc_add_edge. apply: oarc_del_edges arc_e1'. by rewrite D2 // !inE eqxx.
        -- apply: oarc_add_edge. apply: oarc_del_edges arc_e2'. by rewrite D2 // !inE eqxx.
      * apply ostep_step,ostep_e2. 
        -- exact: e1De2.
        -- apply: oarc_add_edge. apply: oarc_del_edges arc_e1. by rewrite D1 // !inE eqxx.
        -- apply: oarc_add_edge. apply: oarc_del_edges arc_e2. by rewrite D1 // !inE eqxx.
      * rewrite !add_edge_del_edges ?D1 ?D2 ?maxn_fset2 //.
        rewrite !del_edges_edges fsetUC add_edge_edge //. 
        case: maxnP => _; by rewrite fset2_maxn_neq // ?D1 ?D2 // !inE eqxx.
    + (* associativity case *)
      wlog ? : e1 e2 x y u v  arc_e1 arc_e2 e1De2 He / e = e2 ; [move => W|subst e]. 
      { have: e \in [fset e1;e2]. { move/fsetP : He => /(_ e). rewrite in_fset1 eqxx. by case/fsetIP. }
        rewrite inE. case/orb_sum => /fset1P => E; last exact: W.
        rewrite -> oarc_cnv in arc_e1,arc_e2. 
        move/(_ _ _ _ _ _ _ arc_e2 arc_e1) in W. rewrite fsetUC eq_sym in W.
        case: W => // Gl [Gr] [[S1 S2] WG]. exists Gl. exists Gr. do 2 (split => //). 
        apply: oliso_stepL S1. rewrite maxnC. apply: add_edge_flip; eauto with vset.
        by rewrite !cnvpar parC. }
      wlog ? : e1' e2' x' y' u' v'  arc_e1' arc_e2' e1De2' He / e2 = e1' ; [move => W|subst e1'].
      { have: e2 \in [fset e1';e2']. { move/fsetP : He => /(_ e2). rewrite in_fset1 eqxx. by case/fsetIP. }
        rewrite inE. case/orb_sum => /fset1P => E; first exact: W.
        rewrite -> oarc_cnv in arc_e1',arc_e2'. 
        move/(_ _ _ _ _ _ _ arc_e2' arc_e1') in W. rewrite eq_sym [[fset e2';_]]fsetUC in W.
        case: W => // Gl [Gr] [[S1 S2] WG]. exists Gl. exists Gr. do 2 (split => //). 
        apply: oliso_stepL S2. rewrite maxnC fsetUC. apply: add_edge_flip; eauto with vset.
        by rewrite !cnvpar parC. }
      have {He} E1 : e1 != e2'.
      { apply: contraNneq e1De2 => E. by rewrite -in_fset1 -He !inE E !eqxx. }
      (* until here, the reasoning is essentially the same as in the V2/V2 assoc. case *)
      wlog [? ? Hu] : x' y' u' v' {arc_e1'} arc_e2' / [/\ x' = x, y' = y & u' ≡ v].
      { move => W. case: (same_oarc arc_e1' arc_e2) => [|[? ? E]]; first exact: W.
        rewrite -> oarc_cnv in arc_e2'. subst x' y'.  
        case: (W _ _ u'° _ arc_e2'). split => //. by rewrite E cnvI.
        move => Gl [Gr] [[Sl Sr] EG]. e2split; [exact: Sl| |exact: EG].
        apply: oliso_stepL Sr. rewrite maxnC fsetUC. apply: add_edge_flip; eauto with vset.
        by rewrite !cnvpar parC. }
      subst.
      e2split.
      * eapply ostep_step,ostep_e2. 
        2: exact: oarc_added_edge.
        2: { apply: oarc_add_edge. apply: oarc_del_edges arc_e2'. 
             by rewrite !inE negb_or ![e2' == _]eq_sym E1 e1De2'. }
        by case: maxnP.
      * eapply ostep_step,ostep_e2.
        3: exact: oarc_added_edge.
        2: { apply: oarc_add_edge. apply: oarc_del_edges arc_e1. 
             by rewrite !inE negb_or e1De2. }
        by case: maxnP.
      * rewrite maxnA. set f := maxn (maxn _ _) _. 
        rewrite !add_edge_del_edgesK ?inE ?eqxx // !del_edges_edges. 
        apply: add_edge_morphism' => //; last by rewrite Hu parA.
        pose A := [fset e1;e2;e2'].
        rewrite [_ `|` _](_ : _ = A) 1?[[fset e2; e2'] `|` _](_ : _ = A) //.
        rewrite [_ `|` [fset maxn _ _]]fsetUC. 
        all: rewrite fsetUC -!fsetUA. 
        all: rewrite [maxn _ _ |` _]mem_fset1U. 
        all: try by case: maxnP; rewrite !inE eqxx.
        by rewrite fsetUA.
        by rewrite fsetUC.
Admitted.

  


(** connecting the open step relation with the additive one on typed graphs *)

Lemma osteps_of (G H : lgraph) : step G H -> osteps (open G) (open H).
Proof with eauto with typeclass_instances.
  case => {G H}.
  - admit. (* do we really want the v0 rule? *)
  - move => G x u a.
    (* test *)
    apply: oliso_stepL (open_add_edge _ _ _) _.
    apply: oliso_stepL. apply: add_edge_cong. apply open_add_vertex. 
    rewrite !open_add_vertexE. 
    apply: oliso_stepR. apply open_add_test.
    rewrite /add_edge. set z := fresh (vset _). set e := fresh (eset _). 
    apply: ostep_stepL. apply: (@ostep_v1 _ (inj_v x) z e u).
    + by rewrite edges_at_add_edge ?edges_at_add_vertex ?freshP // fsetU0.
    + rewrite !pIO_add. by rewrite pIO_fresh // freshP.
    + exact: oarc_add_edge.
    + admit.
    + set b := [dom _]. apply: oliso_step. apply weqG_oliso...
      { admit. }
      rewrite -del_vertex_add_test add_edge_del_vertex add_vertexK. 
      by rewrite /b/= updateE.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma del_vertexK (G : pre_graph) (isG : is_graph G) z : 
  add_vertex (G \ z) z (lv G z) ≡G del_edges G (edges_at G z).
Admitted.

Lemma fsvalK (T : choiceType) (A : {fset T}) (x : A) (p : fsval x \in A) : Sub (fsval x) p = x.
Proof. exact: val_inj. Qed.

      
Lemma steps_of (G H : pre_graph) (isG : is_graph G) (isH : is_graph H) : 
  ostep G H -> steps (close G) (close H).
Proof with eauto with typeclass_instances.
  move => S. case: S isG isH => {G H}.
  - move => G x z e u He Hz arc_e xDz isG isH.
    set a := lv G z in isH *.
    have x_del_z : x \in vset (G \ z). admit.
    have z_del_z : z \notin vset (G \ z). admit.
    have h : close G ≅ close (G \ z) ∔ a ∔ [Some (close_v x), u, None].
    { symmetry.
      apply: liso_comp. apply: liso_add_edge. apply: (liso_sym (close_add_vertex _ _ z_del_z)).
      rewrite /=. 
      set Sx := Sub _ _. set Sz := Sub z _. set G' := add_vertex _ _ _.
      have -> : Sx = (@close_v G' _ x). { admit. }
      have -> : Sz = (@close_v G' _ z). { admit. } 
      apply: liso_comp (liso_sym _) _. eapply close_add_edge. 
      apply: liso_of_oliso. apply weqG_oliso...
      - admit.
      - admit. }
    apply: cons_step h _ _. constructor. 
    apply liso_step. rewrite -> close_add_test => //. 
    apply: liso_of_oliso. apply: weqG_oliso. by rewrite del_vertex_add_test.
  - admit.  
  - admit.
  - admit.
Admitted.


(* Lemma ostep_of (G H : lgraph) : *)
(*   step G H -> Σ H' : pre_graph, ostep (open G) H' * (H' ⩭ open H). *)
(* Proof. *)
(*   case => {G H}. *)
(*   - move => G x z e Hz xDz u arc_e at_z. eexists; split. *)
(*     + apply: ostep_v1. 3: apply: oarc_open arc_e.   *)
(*       admit. admit. admit. *)
(*     +  *)
(* Admitted. *)

(* TOTHINK: It appears that the "additive" variant of the step
relation (i.e., the one that never deletes anything) is more
convienient in the rest of the proofs. How reasonable is it to go
directtly to the open removal variant, or do we want the removal
variant on type-based graphs as intermediate representation? *)