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
  openK G x = close_v (inj_v x).
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

Definition oarc e x u y := 
  [/\ src G e = x, tgt G e = y & le G e ≡ u] \/
  [/\ tgt G e = x, src G e = y & le G e ≡ u°].

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


Notation "G \ x" := (del_vertex G x) (at level 29,left associativity).

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
Admitted.


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

(* TOTHINK: This is not an instance because [x \in vset G] is not
inferrable. One could box it though and make it inferrable through
some external hints *)
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

Instance add_test_graph (G : pre_graph) `{graph_G : is_graph G} x a :
  is_graph (add_test G x a). 
Proof. split => //=; apply graph_G. Qed.

Notation "G [adt x <- a ]" := (add_test G x a) (at level 2, left associativity, format "G [adt  x  <-  a ]").

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

Lemma del_vertexC (G : pre_graph) (x y : VT) : G \ x \ y = G \ y \ x.
Proof.
  rewrite /del_vertex/=; f_equal. 
  - by rewrite fsetDDl fsetUC -fsetDDl.
  - by rewrite !edges_at_del fsetDDD fsetUC -fsetDDD.
Qed.

Lemma add_testC (G H : pre_graph) x y a b :
  G[adt x <- a][adt y <- b] ≡G G[adt y <- b][adt x <- a].
Proof.
  split => //= z. 
  case: (altP (x =P y)) => xy; subst. 
  - rewrite !update_same. case: (altP (z =P y)) => zy; subst; rewrite !updateE //=. 
    by rewrite -dotA dotC dotA.
  - case: (altP (z =P x)) => zx; case: (altP (z =P y)) => zy; subst.
    by rewrite eqxx in xy. all: by rewrite !updateE.
Qed.

(* TODO: all notations for graph operations should be left associative
and at the same level, because this is the only way in which they can
be parsed *)
Notation "G ∔ [ x , u , y ]" := (add_edge G x u y) (at level 20,left associativity) : open_scope.
Open Scope open_scope.

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

Lemma add_edge_test (G : pre_graph) x y z u a : 
  (G ∔ [x,u,y])[adt z <- a] ≡G G[adt z <- a] ∔ [x,u,y].
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

Lemma close_add_edge (G : pre_graph) (x y : VT) u 
  (graph_G : is_graph G) (graph_G' : is_graph (add_edge G x u y)) : 
  close (add_edge G x u y) 
≅ liso.add_edge (close G) (close_v x) (close_v y) u.
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
  ((forall a, open_add_vertex a (@inj_v (G ∔ a) None) = fresh (vset (open G)))
  *(forall a x, open_add_vertex a (@inj_v (G ∔ a) (Some x)) = @inj_v G x))%type. 
Proof. 
  split => *.
  all: rewrite /= vfun_bodyE /=.
  all: by rewrite imfset_bij_bwdE. 
Qed.

Lemma open_add_edge (x y : G) u : 
  open (liso.add_edge G x y u) ⩭ add_edge (open G) (inj_v x) u (inj_v y).
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

(** * Step relation (TODO) *)

Inductive ostep : pre_graph -> pre_graph -> Type := 
| ostep_v1 (G : pre_graph) x z e u : 
    edges_at G z = [fset e] -> z \notin pIO G -> oarc G e x u z -> x != z ->
    ostep G (add_test G  x [dom(u·lv G z)] \ z)
| ostep_v2 (G : pre_graph) x y z e1 e2 u v : 
    edges_at G z = [fset e1;e2] -> z \notin pIO G -> x != z -> y != z ->
    oarc G e1 x u z -> oarc G e2 z v y -> 
    ostep G ((G \ z) ∔ [x,u·lv G z·v,y])
| ostep_e0 G x e : 
    src G e = x -> tgt G e = x ->
    ostep G ((del_edges G [fset e])[adt x <- [1∥le G e]])
| ostep_e2 G x y e1 e2 u v : 
    oarc G e1 x u y -> oarc G e2 x v y ->
    ostep G ((del_edges G [fset e1;e2]) ∔ [x,u∥v,y]).

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


Notation "G ∔ [ e , x , u , y ]" := (add_edge' G e x u y) (at level 20,left associativity) : open_scope.

Lemma edges_at_add_vertex (G : pre_graph) x a : x \notin vset G -> 
  edges_at (add_vertex G x a) x = fset0.
Admitted.

Lemma edges_at_add_edge (G : pre_graph) x y e u : e \notin eset G -> 
  edges_at (add_edge' G e x u y) y = e |` edges_at G y.
Admitted.

Lemma pIO_add_vertex (G : pre_graph) x a : pIO (add_vertex G x a) = pIO G. done. Qed.
Lemma pIO_add_edge (G : pre_graph) e x u y : pIO (add_edge' G e x u y) = pIO G. done. Qed.
Definition pIO_add := (pIO_add_edge,pIO_add_vertex).

Lemma pIO_fresh (G : pre_graph) (isG : is_graph G) x : 
  x \notin vset G -> x \notin pIO G.
Proof. apply: contraNN. rewrite !inE. case/orP => /eqP ->; [exact: p_inP|exact: p_outP]. Qed.

Lemma oarc_add_edge (G : pre_graph) e x y u : oarc (G ∔ [e,x,u,y]) e x u y. 
Proof. by left; split; rewrite /= update_eq. Qed.

Lemma add_edge_del_vertex (G : pre_graph) e x u y : G ∔ [e,x,u,y] \ y ≡G G \ y.
Admitted.

Lemma add_vertexK (G : pre_graph) x a : add_vertex G x a \ x ≡G G.
Admitted.

Lemma lv_add_edge (G : pre_graph) e x u y z : lv (G ∔ [e,x,u,y]) z = lv G z. done. Qed.

Lemma osteps_of (G H : lgraph) : step G H -> osteps (open G) (open H).
Proof with eauto with typeclass_instances.
  case => {G H}.
  - admit. (* do we really want the v0 rule? *)
  - move => G x u a.
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
    have h : close G ≅ liso.add_edge (liso.add_vertex (close (G \ z )) a) (Some (close_v x)) None u.
    { symmetry.
      apply: liso_comp. apply: liso.liso_add_edge. apply: (liso_sym (close_add_vertex _ _ z_del_z)).
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