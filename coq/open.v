Require Import Relation_Definitions Morphisms RelationClasses.
From mathcomp Require Import all_ssreflect.

Require Import edone set_tac finite_quotient preliminaries bij equiv.
Require Import pttdom mgraph mgraph2 rewriting.

Require Import finmap_plus.
Open Scope fset_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

(** ** Preliminaries *)

Axiom admitted_case : False.
Ltac admit := case admitted_case.

Lemma existsb_eq (P Q : pred bool) : (forall b, P b = Q b) -> [exists b, P b] = [exists b, Q b].
Proof. move => E. apply/existsP/existsP; case => b Hb; exists b; congruence. Qed.

Lemma existsb_case (P : pred bool) : [exists b, P b] = P true || P false.
Proof. apply/existsP/idP => [[[|] -> //]|/orP[H|H]]; eexists; exact H. Qed.


Lemma testC X (a b : test X) : a·b ≡ b·a. 
Admitted.

Lemma infer_testE X x x' y y' p p' : 
  (@infer_test X x y p) ≡ (@infer_test X x' y' p') <-> x ≡ x'.
Proof. rewrite /infer_test. by subst. Qed.

(** Christian: The follwing should hold (and typecheck) for all 2pdom algebras *)

Lemma eqv_negb (X: pttdom) (u v : X) b : u ≡[~~b] v <-> u ≡[b] v°.
Admitted.

(** *** Graphs *)

(** Incident Edges *)
Module mplus.
Section L.
Variable (L: labels).
  

Section Defs.
Variables (G : graph L).
Implicit Types (x y : G).

Definition incident x e := x \in [set source e; target e].
Definition edges_at x := [set e | incident x e].

Definition edges_in (V : {set G}) := (\bigcup_(x in V) edges_at x)%SET.

Lemma edges_in1 (x : G) : edges_in [set x] = edges_at x. 
Proof. by rewrite /edges_in big_set1. Qed.
End Defs.

Arguments edges_at [G] x, G x.

Section Theory.
Variables (G : graph L).
Implicit Types (x y : G).

Lemma edges_at_add_edgeT x u y z: z \in [set x;y] -> 
  edges_at (G ∔ [x,u,y])%G z = None |: Some @: edges_at z.
Admitted.

Lemma edges_at_add_edgeN x u y z: z \notin [set x;y] -> 
  edges_at (G ∔ [x,u,y])%G z = Some @: edges_at z.
Admitted.

End Theory.
End L.

Arguments edges_at [L G] x, [L] G x.
End mplus.
Import mplus.

(** Arcs *)

Section G.
Variable L: pttdom.
Notation test := (test L).
Notation Lv := test.
Notation Le := L.
Notation graph := (graph (pttdom_labels L)).
Notation graph2 := (graph2 (pttdom_labels L)).

Definition arc (G : graph) (e : edge G) x u y :=
  exists b, [/\ endpoint b e = x, endpoint (~~b) e = y & elabel e ≡[b] u].

Global Instance arc_morphism G : Proper (eq ==> eq ==> eqv ==> eq ==> iff) (@arc G).
Proof. 
  move => e e' E x x' X u u' U y y' Y. subst e' x' y'. 
  wlog suff S : u u' U /  arc e x u y -> arc e x u' y.
  { split; apply: S => //. by symmetry. }
  case => b [A B C]. exists b. split => //. by rewrite <- U.
Qed.

Variables (G : graph).
Implicit Types (x y : G) (u : Le).

Lemma arcC (e : edge G) x y u : 
  arc e x u y <-> arc e y u° x.
Proof. 
  wlog suff S : x y u /  arc e x u y -> arc e y u° x.
  { split; first exact: S. move/S. by rewrite cnvI. }
  case => b [A B C]. exists (~~b). split => //.
  - by rewrite ?negbK.
  - by rewrite eqv_negb cnvI.
Qed.

Lemma add_edge_arc x y u : @arc (G ∔ [x,u,y])%G None x u y.
Proof. by exists false. Qed.

Lemma add_edge_arc' x y x' y' u u' e : 
  @arc G e x u y -> @arc (G ∔ [x', u', y'])%G (Some e) x u y.
Proof. case => b [*]. by exists b. Qed.

End G.

Arguments eqv : simpl never.


(** Picking fresh vertices/edges *)

Definition fresh (E : {fset nat}) : nat := (\max_(e : E) val e).+1.

Lemma freshP (E : {fset nat}) : fresh E \notin E. 
Proof. 
  have S e' : e' \in E -> e' < fresh E. 
  { rewrite /fresh ltnS => inE. by rewrite -[e']/(val [`inE]) leq_bigmax. }
  apply/negP => /S. by rewrite ltnn.
Qed.   

Lemma fresh_eqF (E : {fset nat}) (x : E) : val x == fresh E = false.
Proof. by rewrite fsval_eqF // freshP. Qed.

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

Section OpenGraphs.
Variable (Lv Le : Type).

(* TODO: turn src and tgt into a function from [bool] *)
Record pre_graph := { vset : {fset VT};
                      eset : {fset ET};
                      endpt : bool -> ET -> VT;
                      lv : VT -> Lv;
                      le : ET -> Le;
                      p_in : VT;
                      p_out : VT }.

Class is_graph (G : pre_graph) := 
  { endptP (e:ET) b : e \in eset G -> endpt G b e \in vset G;
    p_inP : p_in G \in vset G;
    p_outP : p_out G \in vset G}.

End OpenGraphs.

Bind Scope open_scope with pre_graph.
Delimit Scope open_scope with O.

(** ** Opening and closing of type-based graphs *)

Class inh_type (A : Type) := { default : A }.

Section Open.
Variable L: labels.
Notation Le := (structures.le L).                
Notation Lv := (structures.lv L).
Notation graph := (graph L).
Notation graph2 := (graph2 L).
Variables (le0 : Le) (G : graph2).
Context `{inh_type Le}.

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

(** In order to totalize the edge labeling, we need a default edge label. This
is necessary since an edgeless [G] may use an empty type for labeling
edges... *)

Definition open : pre_graph Lv Le := 
  {| vset := [fset inj_v x | x in G];
     eset := [fset inj_e x | x in edge G];
     endpt b (e:ET) := if proj_e e is Some e' then inj_v (endpoint b e') else v0;
     lv v := vlabel (proj_v v);
     le e := if proj_e e is Some e' then elabel e' else default;
     p_in := inj_v (input : G);
     p_out := inj_v (output : G) |}.

Global Instance open_is_graph : is_graph open.
Proof.
  split.
  - move => e' b. case/imfsetP => /= e _ ->. by rewrite inj_eK in_imfset.
  - by rewrite /= in_imfset.
  - by rewrite /= in_imfset.
Qed.

End Open.

Section Close.
Variable L: labels.
Notation Le := (structures.le L).                
Notation Lv := (structures.lv L).
Notation graph := (graph L).
Notation graph2 := (graph2 L).
Variable (G : pre_graph Lv Le).
Context {graph_G : is_graph G}.

Lemma endpt_proof b (e : eset G) : endpt G b (val e) \in vset G.
Proof. exact: (endptP b (valP e)). Qed.

(* Lemma target_proof (e : eset G) : tgt G (val e) \in vset G. *)
(* Proof. exact: (tgtP (valP e)). Qed. *)

Definition close' : graph := Eval simpl in 
  {| vertex := [finType of vset G];
     edge := [finType of eset G];
     endpoint b e := Sub (endpt G b (val e)) (endpt_proof b e);
     vlabel v := lv G (val v);
     elabel e := le G (val e) |}.

Arguments Graph2 [_] graph_of _ _.

Definition close := Eval hnf in
  point close' (Sub (p_in G) (@p_inP _ _ _ _)) (Sub (p_out G) (@p_outP _ _ _ _)).

End Close.
Arguments close [_] G [_] , [_] G graph_G.

Section OpenCloseFacts.
Variable tm : pttdom.           (* TODO: rename *)
Notation test := (test tm).

Global Instance tm_inh_type : inh_type tm. 
exact: Build_inh_type (1%ptt).
Defined.

Notation pre_graph := (pre_graph test (car (setoid_of_ops (ops tm)))).
Notation graph := (graph (pttdom_labels tm)).
Notation graph2 := (graph2 (pttdom_labels tm)).

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

Lemma iso2_intro (G H : graph2) (hv : bij G H) (he : bij (edge G) (edge H)) (hd : edge G -> bool) :
  is_hom hv he hd -> hv input = input -> hv output = output -> G ≃2 H.
Proof. move => hom_h. by exists (Iso hom_h). Defined.

Tactic Notation "iso2" uconstr(hv) uconstr(he) uconstr(hd) := 
  match goal with |- ?G ≃2 ?H => apply (@iso2_intro G H hv he hd) end.


Lemma openK (G : graph2) : G ≃2 close (open G).
Proof.
iso2 (imfset_bij (@inj_v_inj G)) 
     (imfset_bij (@inj_e_inj (edge G)))
     (fun => false) => /=.
2-3: exact: val_inj.
split. 
- move => e b. apply: val_inj => /=;by rewrite !inj_eK.
- move => v /=. by rewrite inj_vK. 
- move => e /=. by rewrite inj_eK.
Defined.

(* Lemma iso2_introE (F G : graph2) hv he hd Hh Hi Ho (x : F) :  *)
(*   (@iso2_intro F G hv he hd Hh Hi Ho x) = hv x. *)
(* Proof. done. Qed. *)

Lemma openKE (G : graph2) (x : G) :
  openK G x = close_v (inj_v x) :> close (open G).
Proof. 
  rewrite /close_v /=. case: {-}_ /idP => [p|np].
  - by apply: val_inj => /=. 
  - by rewrite in_imfsetT in np.
Qed.

(** We define isomorphisms via closing *)


Definition oiso2 (G H : pre_graph) :=
  Σ (graph_G : is_graph G) (graph_H : is_graph H), close G ≃2 close H.

Notation "G ⩭2 H" := (oiso2 G H) (at level 45).

Lemma closeK (G : pre_graph) (graph_G : is_graph G) : 
  G ⩭2 open (close G).
Proof. rewrite /oiso2. do 2 eexists. exact: openK. Defined.

Lemma close_irrelevance (G : pre_graph) (graph_G graph_G' : is_graph G) : 
  close G graph_G ≃2 close G graph_G'.
Proof.
  iso2 bij_id bij_id xpred0; try exact: val_inj.
  split => // e [|]; exact: val_inj.
Qed.
  
Lemma liso_of_oliso (G H : pre_graph) (graph_G : is_graph G) (graph_H : is_graph H) : 
  G ⩭2 H -> close G ≃2 close H.
Proof. 
  case => graph_G' [graph_H'] I.
  transitivity (close G graph_G'); first exact: close_irrelevance.
  apply: iso2_comp I _. exact: close_irrelevance.
Qed.


Lemma oiso2_trans : CRelationClasses.Transitive oiso2.
Proof. 
  move => F G H [isF [isG FG]] [isG' [isH GH]]. do 2 eexists. 
  apply: iso2_comp GH. 
  (* by rewrite -> (close_irrelevance isG' isG). - fails now *)
  apply: iso2_comp FG _. exact: close_irrelevance.
Qed.

Lemma oiso2_sym : CRelationClasses.Symmetric oiso2.
Proof. move => F G [isF [isG]] /iso2_sym => ?. by do 2 eexists. Qed.

Instance oiso2_Equivalence : CRelationClasses.PER oiso2.
Proof. exact: (CRelationClasses.Build_PER _ oiso2_sym oiso2_trans). Qed.


Definition vfun_body (G H : pre_graph) (graph_G : is_graph G) (graph_H : is_graph H) 
  (h : bij (close G) (close H)) (x : VT) : VT := 
  locked (match @idP (x \in vset G) with
          | ReflectT p => val (h (Sub x p))
          | ReflectF _ => x
          end).

Definition vfun_of (G H : pre_graph) (h : G ⩭2 H) := 
  let: existT GG (existT GH h) := h in vfun_body h.

Arguments vfun_of [G H] h x.

Coercion vfun_of : oiso2 >-> Funclass.

(** In open graphs, we have an equivalence of graphs that have the
same underlying structure with different, but equivalent, labels *)

Record weqG (G H : pre_graph) : Prop := WeqG {
  sameV : vset G = vset H;
  sameE : eset G = eset H;
  same_endpt b : {in eset G, endpt G b =1 endpt H b };
  eqv_lv x : x \in vset G -> lv G x ≡ lv H x;
  eqv_le e : e \in eset G -> le G e ≡ le H e;
  same_in : p_in G = p_in H;
  same_out : p_out G = p_out H
}.

Notation "G ≡G H" := (weqG G H) (at level 79).
                                       
Instance weqG_Equivalence : Equivalence weqG.
Proof.
  split => //.
  - move => G H W. split => //; repeat intro; symmetry; apply W.  
    all: by rewrite ?(sameE W,sameV W).
  - move => F G H W1 W2. 
    have S1 := (sameV W1,sameE W1,same_endpt W1,
                eqv_lv W1,eqv_le W1,same_in W1,same_out W1).
    split => //; repeat intro.
    all: try rewrite S1; try apply W2. all: rewrite -?S1 //.
Qed.

Definition weqG_oliso (G H : pre_graph) : 
  is_graph G -> is_graph H -> G ≡G H -> G ⩭2 H.
Proof.
  move => isG isH [EV EE Eep Elv Ele]. do 2 eexists. 
  iso2 (bij_cast EV) (bij_cast EE) (fun _ => false).
  - split.
    + move => [e p] b /=. 
      apply: val_inj => /=. by rewrite !bij_castE /= ?Eep. 
    + move => [v p]. by rewrite bij_castE /= Elv.
    + move => [e p]. by rewrite bij_castE /= Ele.
  - rewrite bij_castE. exact: val_inj.
  - rewrite bij_castE. exact: val_inj.
Qed.

(** Experimental: A class of boxed properties to allow inference of "non-class" assumptions *)
Class box (P : Type) : Type := Box { boxed : P }.
Hint Extern 0 (box _) => apply Box; assumption : typeclass_instances.

(** ** Helper functions *)

Section PreGraphTheory.
Variables (G : pre_graph).

(** Note that the [incident] predicate does not check whether the edge
is present in the graph. The right way to check whether [e] is an edge
attached to [x] is [e \in edges_at x] *)

Definition incident x e := [exists b, endpt G b e == x].
Definition edges_at x := [fset e in eset G | incident x e].

Lemma edges_atE e x : e \in edges_at x = (e \in eset G) && (incident x e).
Proof. rewrite /edges_at. by rewrite !inE. Qed.

Lemma edges_atF b e x (edge_e : e \in eset G) :  
  e \notin edges_at x -> (endpt G b e == x = false).
Proof. rewrite !inE /= edge_e /=. apply: contraNF => ?. by existsb b. Qed.

Definition pIO  := [fset p_in G; p_out G].

Lemma pIO_Ni x : x \notin pIO -> p_in G != x.
Proof. apply: contraNneq => <-. by rewrite in_fset2 eqxx. Qed.

Lemma pIO_No x : x \notin pIO -> p_out G != x.
Proof. apply: contraNneq => <-. by rewrite in_fset2 eqxx. Qed.

(** Making [e \in eset G] part of the definition of oarc allows us to mostly avoid
explicitly mentioning this assumption in the step relation. Moreover,
it avoids spurious lemmas such as [oarc G e x u y -> oarc (G \ z) e x u y] *)
Definition oarc e x u y := 
  e \in eset G /\ 
  exists b, [/\ endpt G b e = x, endpt G (~~b) e = y & le G e ≡[b] u].

End PreGraphTheory.

(** ** Operatons on open graphs *)

Definition del_vertex (G : pre_graph) (x : VT) := 
  {| vset := vset G `\ x;
     eset := eset G `\` edges_at G x;
     endpt := endpt G;
     lv := lv G;
     le := le G;
     p_in := p_in G;
     p_out := p_out G |}.

Notation "G \ x" := (del_vertex G x) (at level 29,left associativity) : open_scope.

Global Instance del_vertex_graph (G : pre_graph) 
  {graph_G : is_graph G} (x : VT) {Hx : box (x \notin pIO G)} : 
  is_graph (del_vertex G x).
Proof.
  rewrite /del_vertex; split => //=. 
  - move => e b /fsetDP [A B]. by rewrite !inE (endptP b A) edges_atF. 
  - case: Hx => Hx. by rewrite !inE p_inP andbT pIO_Ni.
  - case: Hx => Hx. by rewrite !inE p_outP andbT pIO_No.
Qed.

Definition add_vertex (G : pre_graph) (x : VT) a := 
  {| vset := x |` vset G ;
     eset := eset G;
     endpt := endpt G;
     lv := (lv G)[upd x := a];
     le := le G;
     p_in := p_in G;
     p_out := p_out G |}.

Notation "G  ∔  [ x , a ]" := (add_vertex G x a) (at level 20) : open_scope.

Global Instance add_vertex_graph (G : pre_graph) {graph_G : is_graph G} (x : VT) a : 
  is_graph (add_vertex G x a).
Proof. 
  split => //=; first by move => e b inG; rewrite inE !endptP.
  all: by rewrite inE (p_inP,p_outP).
Qed.

Definition del_edges (G : pre_graph) (E : {fset ET}) := 
  {| vset := vset G;
     eset := eset G `\` E;
     endpt := endpt G;
     lv := lv G;
     le := le G;
     p_in := p_in G;
     p_out := p_out G |}.

Notation "G - E" := (del_edges G E) : open_scope.

Global Instance del_edges_graph (G : pre_graph) {graph_G : is_graph G} (E : {fset ET}) :
  is_graph (del_edges G E).
Proof. 
  split; try by apply graph_G. 
  move => e b /fsetDP [He _]; by apply graph_G.
Qed.

Definition add_edge' (G : pre_graph) (e:ET) x u y :=
  {| vset := vset G;
     eset := e |` eset G;
     endpt b := update (endpt G b) e (if b then y else x);
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
Proof.
  move => xG yG. split => //=; try apply graph_G. 
  move => e' b; case/fset1UE => [->|[? ?]]; rewrite updateE ?(endptP) //.
  by case: b.
Qed.

Lemma add_edge_graph (G : pre_graph) (graph_G : is_graph G) x y u :
  x \in vset G -> y \in vset G -> is_graph (add_edge G x u y).
Proof. exact: add_edge_graph'. Qed.

Definition add_test (G : pre_graph) (x:VT) (a:test) := 
  {| vset := vset G;
     eset := eset G;
     endpt  := endpt G;
     lv := update (lv G) x [lv G x·a];
     le := le G;
     p_in := p_in G;
     p_out := p_out G |}.

(* TODO: all notations for graph operations should be left associative
and at the same level, because this is the only way in which they can
be parsed *)

Instance add_test_graph (G : pre_graph) {graph_G : is_graph G} x a :
  is_graph (add_test G x a). 
Proof. split => //=; apply graph_G. Qed.

Notation "G [adt x <- a ]" := (add_test G x a) 
   (at level 2, left associativity, format "G [adt  x  <-  a ]") : open_scope.

(** ** Properties of the operations *)


Lemma incident_delv G z : incident (G \ z) =2 incident G. done. Qed.
Lemma incident_dele (G : pre_graph) E : incident (G - E) =2 incident G. done. Qed.

Lemma edges_at_del (G : pre_graph) (z x : VT) : 
  edges_at (G \ z) x = edges_at G x `\` edges_at G z.
Proof.
  apply/fsetP => k. by rewrite !(edges_atE,inE) !incident_delv !andbA.
Qed.

Lemma edges_at_add_edge (G : pre_graph) x y e u : 
  edges_at (add_edge' G e x u y) y = e |` edges_at G y.
Proof.
  apply/fsetP => e0. rewrite inE !edges_atE /= !inE. 
  case: (altP (e0 =P e)) => //= [->|e0De].
  - rewrite /incident/=. existsb true. by rewrite !update_eq. 
  - rewrite /incident/=. admit.
Qed.

Lemma edges_at_add_edge' G e x y z u : 
  e \notin eset G ->
  x != z -> y != z -> edges_at (G ∔ [e,x,u,y]) z = edges_at G z.
Proof.
  move => eGN xDz yDz. apply/fsetP => e0; rewrite !edges_atE /= !inE.
  case: (altP (e0 =P e)) => //= [->|e0De].
  (* - by rewrite (negbTE eGN) /incident /= !updateE (negbTE xDz) (negbTE yDz). *)
  (* - by rewrite /incident/= !update_neq. *)
  - admit.
  - admit.
Qed.

(* TODO: how to get parentheses around complex G to display? *)
Notation "'src' G e" := (endpt G false e) (at level 11).
Notation "'tgt' G e" := (endpt G true e) (at level 11).

Lemma endpt_add_edge (G : pre_graph) e b x y u : 
  endpt (G ∔ [e,x,u,y]) b e = if b then y else x.
Proof. by rewrite /= updateE. Qed.

Lemma add_edgeV (G : pre_graph) e (x y : VT) (u : tm) : 
  is_graph (add_edge' G e x u y) -> ((x \in vset G) * (y \in vset G))%type.
Proof.
  intros graph_G. case: graph_G => /(_ e) H _ _. split.
  - move: (H false). rewrite endpt_add_edge. apply. by rewrite !inE eqxx.
  - move: (H true). rewrite endpt_add_edge. apply. by rewrite !inE eqxx.
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
    by rewrite infer_testE -dotA testC dotA.
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
  move => Hx Hy He. split => //=. rewrite edges_at_add_edge' ?[_ == z]eq_sym //.
  rewrite fsetDUl [[fset _] `\` _](fsetDidPl _ _ _) //. 
  apply/fdisjointP => ? /fset1P ->. by rewrite edges_atE (negbTE He).
Qed.

Lemma add_edge_test (G : pre_graph) e x y z u a : 
  (G ∔ [e,x,u,y])[adt z <- a] ≡G G[adt z <- a] ∔ [e,x,u,y].
Proof. done. Qed.

(** ** Morphism Lemmas *)

Instance add_edge_morphism' : Proper (weqG ==> eq ==> eq ==> eqv ==> eq ==> weqG) add_edge'.
Proof. 
  move => G H [EV EE Eep Elv Ele Ei Eo] ? e ? ? x ? u v uv ? y ?. subst. 
  split => //= [|b|e'].
  - by rewrite EE.
  - apply: in_eqv_update => // ?. exact: Eep.
  - exact: in_eqv_update.
Qed.

Instance add_edge_morphism : Proper (weqG ==> eq ==> eqv ==> eq ==> weqG) add_edge.
Proof. 
  move => G H GH e e' E. apply: add_edge_morphism' => //. by rewrite (sameE GH).
Qed.
  
Lemma weqG_edges_at G H : G ≡G H -> edges_at G =1 edges_at H.
Proof. 
  move => GH. move => x. apply/fsetP => e. 
  rewrite !edges_atE -(sameE GH). case E : (_ \in _) => //=. 
  apply: existsb_eq => b. by rewrite (same_endpt GH).
Qed.

Instance del_vertex_morphism : Proper (weqG ==> eq ==> weqG) del_vertex.
Proof with  apply/fsubsetP; exact: fsubsetDl.
  move => G H [EV EE Eep Elv Ele Ei Eo] ? x ?. subst. 
  have EGH : edges_at G =1 edges_at H by exact: weqG_edges_at.
  split => //=; rewrite -?EE -?EV -?EGH //. 
  - move => b. apply: sub_in1 (Eep b) => //...
  - apply: sub_in1 Elv => //...
  - apply: sub_in1 Ele => //...
Qed.

(* TOTHINK is "eqv" the right equivalence to use for tests *)
Instance add_test_morphism : Proper (weqG ==> eq ==> eqv ==> weqG) add_test.
Proof.
  move => G H [EV EE Eep Elv Ele Ei Eo] ? x ? u v uv. subst.
  split => //= y Hy. case: (altP (y =P x)) => [?|?].
  - subst y. rewrite !updateE. 
    Fail rewrite Elv.
    rewrite infer_testE. Fail rewrite Elv. Fail rewrite uv.
    apply: tst_dot_eqv uv. exact: Elv.
  - by rewrite !updateE // Elv.
Qed.

(*
Lemma name_add_edge (G : pre_graph) x y u (e : ET) :
  e \notin eset G -> G ∔ [x,u,y] ⩭ add_edge' G e x u y.
Admitted.
Arguments name_add_edge [G x y u] e _.
*)

(** ** Commutation with open/close *)

Arguments freshP [E].

Lemma close_add_edge' G e x y u (isG : is_graph G)(isG' : is_graph (G ∔ [e,x, u, y])) :
  e \notin eset G -> 
  close (G ∔ [e,x, u, y]) ≃2 close G ∔ [close_v x, u, close_v y].
Proof. 
  move => eG.
  apply: iso2_sym. 
  iso2 (bij_id) (fresh_bij bij_id eG) (fun => false) => //. 
  2-3: exact: val_inj. 
  split => //.
  - move => [e'|] b; apply: val_inj => //.
    + by rewrite fresh_bijE /= updateE ?fsval_eqF.  
    + rewrite fresh_bijE /= updateE. 
      by case: b; rewrite close_vK // ?fsval_eqF add_edgeV.
  - by move => [e'|] /=; rewrite updateE // fsval_eqF.
Defined.

Lemma close_add_edge (G : pre_graph) (x y : VT) u (isG : is_graph G) (isG' : is_graph (G ∔ [x, u, y])) : 
  close (G ∔ [x, u, y]) ≃2 close G ∔ [close_v x, u, close_v y].
Proof. exact: close_add_edge' freshP. Defined.

Definition close_add_vertex (G : pre_graph) (graph_G : is_graph G) x a : x \notin vset G -> 
  close (G ∔ [x, a]) ≃2 (close G) ∔ a.
Proof.
  move => xG. apply: iso2_sym. 
  iso2 (fresh_bij bij_id xG) bij_id (fun => false) => //. 2-3: move => *; exact: val_inj.
  split => //.
  + move => e b. exact: val_inj.
  + by move => [v|] /=; rewrite updateE // fsval_eqF.
Defined.

(* Lemma vfunE (G H : lgraph) (h : bij (close (open G)) (close (open H))) (x : G) : *)
(*   vfun_body h (inj_v x) = inj_v (h (openK _ x)). *)
(* Admitted. *)

Lemma vfun_bodyE (G H : pre_graph) (isG : is_graph G) (isH : is_graph H) x
  (h : bij (close G isG) (close H isH)) (p : x \in vset G) : vfun_body h x = val (h (Sub x p)).
Proof.
  unlock vfun_body. 
  case: {-}_ / idP => [p'|]; by [rewrite (bool_irrelevance p p')| move/(_ p)].
Qed.

Lemma inj_v_open (G : graph2) (x : G) : inj_v x \in vset (open G).
Proof. by rewrite in_imfset. Qed.
Hint Resolve inj_v_open.

Lemma vfun_bodyEinj (G : graph2) (H : pre_graph) (graph_H : is_graph H)
     (h : bij (close (open G)) (close H)) (x : G) :
  vfun_body h (inj_v x) = val (h (Sub (inj_v x) (inj_v_open x))).
Proof. by rewrite vfun_bodyE. (* why is the side conition resolved automatically? *) Qed.

Lemma close_fsval (G : pre_graph) (isG : is_graph G) (v : vset G) : close_v (fsval v) = v.
Proof. apply: val_inj => //=. by rewrite close_vK ?fsvalP. Qed.


Definition close_add_test (G : pre_graph) (isG : is_graph G) x (Hx : x \in vset G) a :
  (close G)[tst close_v x <- a] ≃2 close (G[adt x <- a]).
Proof.
  iso2 bij_id bij_id xpred0; try exact: val_inj.
  split => //.
  - move => e b. exact: val_inj.
  - move => v. rewrite /= /update. (* simpl should not expose tst_dot *)
    case: (altP (v =P close_v x)) => [->|D]. 
    + rewrite close_vK // eqxx /=. admit. (* never want to see this ! *)
    + suff -> : (fsval v == x = false) by []. 
      apply: contra_neqF D => /eqP<-. by rewrite close_fsval.
Defined.

Section Transfer.
Variable (G : graph2).

Lemma edges_at_open (x : G) (E : {set edge G}) :  
  mplus.edges_at G x = E ->
  edges_at (open G) (inj_v x) = [fset inj_e e | e in E].
Admitted.


Lemma fresh_imfsetF (T : finType) (f : T -> ET) (e : T) :
   f e == fresh [fset f x | x in T] = false.
Admitted. 

(* TOTHINK: could replace [fresh _] with an arbitrary fresh edge *)
Definition open_add_vertex a : 
  open (G ∔ a) ⩭2 (open G) ∔ [fresh (vset (open G)), a].
Proof. 
  rewrite /oiso2; do 2 eexists.
  apply: iso2_comp (iso2_sym _) _. apply: openK.
  apply: iso2_comp (iso2_sym _). 2: apply: close_add_vertex freshP. 
  apply: add_vertex2_cong => //. exact: openK.
Defined.

Lemma open_add_vertexE : 
  ((forall a, open_add_vertex a (@inj_v (G ∔ a)%G2 None) = fresh (vset (open G)))
  *(forall a x, open_add_vertex a (@inj_v (G ∔ a)%G2 (Some x)) = @inj_v G x))%type. 
Proof. 
  split => *. 
  all: rewrite /= vfun_bodyEinj /=.
  (* all: by rewrite imfset_bij_bwdE. - fixme add_vertex2_cong *) 
Admitted.

Lemma open_add_edge (x y : G) u : 
  open (G ∔ [x, u, y]) ⩭2 open G ∔ [inj_v x, u, inj_v y].
Proof. 
  have X : is_graph (add_edge (open G) (inj_v x) u (inj_v y)). 
  { exact: add_edge_graph. }
  rewrite /iso2. do 2 eexists.
  apply: iso2_comp (iso2_sym _) _. apply: openK.
  (* (* Variant using close_add_edge *) *)
  (* apply: iso2_comp (iso2_sym (close_add_edge _ _)).   *)
  (* TODO: use close_add_edge *)
  iso2 (imfset_bij (@inj_v_inj G)) 
       (fresh_bij (imfset_bij (@inj_e_inj (edge G))) freshP)
       (fun => false). 2-3: exact: val_inj.
  admit.
  (* - move => v /=. by rewrite inj_vK. *)
  (* - case => [e|] //=.  *)
  (*   + rewrite /update ifF ?inj_eK //. exact: fresh_imfsetF. *)
  (*   + by rewrite /update ifT. *)
  (* - move => [e|]; apply: val_inj => /=;by rewrite /update /= ?fresh_imfsetF ?inj_eK // ifT. *)
  (* - move => [e|]; apply: val_inj => /=;by rewrite /update /= ?fresh_imfsetF ?inj_eK // ifT. *)
Defined.


Lemma oarc_open (x y : G) (e : edge G) u : 
  arc e x u y -> oarc (open G) (inj_e e) (inj_v x) u (inj_v y).
Proof.
Admitted.

Definition open_add_test (x : G) a : 
  open (G[tst x <- a]) ⩭2 (open G)[adt inj_v x <- a].
Proof.
  do 2 eexists. 
  apply: iso2_comp (iso2_sym (openK _)) _.
  (* ??? *)
Admitted.

End Transfer. 
   
Lemma oliso_is_graphL (G H : pre_graph) (h : G ⩭2 H) : is_graph G.
Proof. by case: h. Qed.

Lemma oliso_is_graphR (G H : pre_graph) (h : G ⩭2 H) : is_graph H.
Proof. by case: h => [? []]. Qed.


(* TOTHINK: the converse does NOT hold since [h] is the identity on
vertices outside of [G]. This could be made to hold by taking [fresh (vset H)] 
as value outside of [G] *)
Lemma vfun_of_vset (G H : pre_graph) (h : G ⩭2 H) x : x \in vset G -> h x \in vset H.
Proof. case: h  => isG [isH h] /= xG. rewrite vfun_bodyE. exact: valP. Qed.

Section FsetU1Fun.
Variables (T : choiceType) (A B : {fset T}) (f : A -> B) (x y : T).

Definition fsetU1_fun  (a : (x |` A)) : (y |`B) :=
  match fset1UE (fsvalP a) with
  | inl _ => Sub y fset1U1
  | inr (_,p) => Sub (val (f [` p])) (fset1Ur (valP (f [` p])))
  end.

(* Use below *)
Lemma fsetU1_funE1 (p : x \in x |` A) : fsetU1_fun [`p] = Sub y fset1U1.
Admitted.

Lemma fsetU1_funE2 z (p : z \in x |` A) (p' : z \in A) :                                        
    fsetU1_fun [`p] = Sub (val (f [` p'])) (fset1Ur (valP (f [` p']))).
Admitted.


End FsetU1Fun.
Arguments fsetU1_fun [T A B] f x y a.

Lemma fsetU1_fun_can (T : choiceType) (A B : {fset T}) (x y : T) (f : A -> B) (g : B -> A) : 
  x \notin A -> y \notin B -> cancel f g -> cancel (fsetU1_fun f x y) (fsetU1_fun g y x).
Proof.
  move => Hx Hy can_f a. 
  rewrite {2}/fsetU1_fun. case: fset1UE => [/=|[D Ha]].
  - rewrite /fsetU1_fun. case: fset1UE => //=. 
    + move => _ E. apply: val_inj => /=. by rewrite E.
    + rewrite eqxx. by case.
  - rewrite /fsetU1_fun /=. case: fset1UE.
    + move => E. by rewrite -E (fsvalP _) in Hy. 
    + case => A1 A2. apply: val_inj => //=. 
      rewrite (_ : [`A2] = (f.[Ha])%fmap) ?can_f //. exact: val_inj.
Qed.

Section Fresh2Bij.
Variables (T : choiceType) (A B : {fset T}) (x y : T) (f : bij A B) (Hx : x \notin A) (Hy : y \notin B).

Definition fresh2_bij : bij (x |` A) (y |`B).
Proof.
  pose fwd := fsetU1_fun f x y.
  pose bwd := fsetU1_fun f^-1 y x.
  exists fwd bwd. 
  - abstract (apply: fsetU1_fun_can => //; exact: bijK).
  - abstract (apply: fsetU1_fun_can => //; exact: bijK').
Defined.

End Fresh2Bij.

Definition add_edge_cong (G H : pre_graph) (h : G ⩭2 H) x u y : 
  x \in vset G -> y \in vset G -> G ∔ [x,u,y] ⩭2 H ∔ [h x,u,h y].
Proof.
  move => xG yG. case: (h) => [isG [isH h']] /=.
  unshelve (do 2 eexists).
  - exact: add_edge_graph.
  - unshelve apply: add_edge_graph. all:by rewrite vfun_bodyE; exact: valP.
  - iso2 h' (fresh2_bij h'.e freshP freshP) (fun => false) => //.
    
    (* + move => v. by rewrite (vlabel_liso h'). *)
    (* + case => /= e He. case/fset1UE : (He) => [E|[E1 E2]]. *)
    (*   * subst e. by rewrite fsetU1_funE1 /= !updateE.  *)
    (*   * admit. *)

    (* apply: liso_comp. apply: close_add_edge. *)
    (* apply: liso_comp. 2: apply: liso_sym. 2: apply: close_add_edge. *)
    (* have C z : z \in vset G -> close_v (vfun_body h' z) = h' (@close_v G isG z). *)
    (* { move => zG. unlock vfun_body.  *)
    (* rewrite !C.  *)
    (* apply: liso_add_edge_congr. *)
Admitted.

(** * Open Step relation  *)

Section ostep.
Implicit Types (x y z : VT) (e : ET).

(** We turn the first argument into a parameter, this keeps
case/destruct from introducing a new name for G *)
Variant ostep (G : pre_graph) : pre_graph -> Type := 
| ostep_v0 z : 
    edges_at G z = fset0 -> z \notin pIO G -> ostep G (G \ z)
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

Inductive osteps: pre_graph -> pre_graph -> Prop :=
  | oliso_step:    CRelationClasses.subrelation oiso2 osteps
  | ostep_step:    CRelationClasses.subrelation ostep osteps
  | osteps_trans : CRelationClasses.Transitive osteps.

Lemma oliso_stepL G G' H : G ⩭2 G' -> osteps G' H -> osteps G H.
Admitted.

Lemma ostep_stepL G G' H : ostep G G' -> osteps G' H -> osteps G H.
Admitted.

Lemma oliso_stepR G H H' : oiso2 H H' -> osteps G H' -> osteps G H.
Admitted.

Lemma edges_at_add_vertex (G : pre_graph) x a : x \notin vset G -> 
  edges_at (add_vertex G x a) x = fset0.
Admitted.



Lemma pIO_add_vertex (G : pre_graph) x a : pIO (add_vertex G x a) = pIO G. done. Qed.
Lemma pIO_add_edge (G : pre_graph) e x u y : pIO (add_edge' G e x u y) = pIO G. done. Qed.
Lemma pIO_add_test (G : pre_graph) x a : pIO (G[adt x <- a]) = pIO G. done. Qed.
Definition pIO_add := (pIO_add_edge,pIO_add_vertex,pIO_add_test).

Lemma pIO_fresh (G : pre_graph) (isG : is_graph G) x : 
  x \notin vset G -> x \notin pIO G.
Proof. apply: contraNN. rewrite !inE. case/orP => /eqP ->; [exact: p_inP|exact: p_outP]. Qed.

Lemma oarc_add_edge (G : pre_graph) e e' x y x' y' u u' : 
  e' != e ->
  oarc G e' x' u' y' -> oarc (G ∔ [e,x,u,y]) e' x' u' y'. 
Proof.
  move => eDe'. 
  rewrite /oarc /= !updateE // in_fset1U (negbTE eDe') /=. 
  case => A [b] B. split => //. exists b. by rewrite !updateE.
Qed.

Lemma oarc_del_edges (G : pre_graph) e x u y E : 
  e \notin E -> oarc G e x u y -> oarc (del_edges G E) e x u y.
Proof. move => He. by rewrite /oarc /= inE He. Qed.

Lemma oarc_added_edge (G : pre_graph) e x y u : oarc (G ∔ [e,x,u,y]) e x u y. 
Proof. 
  split. 
  - by rewrite !inE eqxx.
  - by exists false; split; rewrite /= update_eq. 
Qed.


Lemma oarc_edge_atL (G : pre_graph) e x y u : 
  oarc G e x u y -> e \in edges_at G x.
Proof. case => E [b] [A B C]. rewrite !inE E /= /incident. existsb b. exact/eqP. Qed.

Instance oarc_morphism : Proper (weqG ==> eq ==> eq ==> eqv ==> eq ==> iff) oarc.
Proof.
  move => G H GH ? e ? ? x ? u v uv ? y ?. subst. 
  wlog suff: G H GH u v uv / oarc G e x u y -> oarc H e x v y.
  { move => W. split; apply: W => //; by symmetry. }
  case: GH => [EV EE Eep Elv Ele _ _] [He [b] [A B C]].
  split; first by rewrite -EE. 
  exists b. rewrite -!Eep //. split => //. by rewrite -Ele // -uv.
Qed.

Lemma oarc_cnv (G : pre_graph) e x y u : oarc G e x u y <-> oarc G e y u° x. 
Proof. 
  wlog suff W : x u y / oarc G e x u y -> oarc G e y u° x. 
  { split; first exact: W. move/W. by rewrite cnvI. }
  case => E [b] [A B C]. split => //. exists (~~b). rewrite negbK.
  split => //. by rewrite eqv_negb cnvI.
Qed.

Lemma oarc_edge_atR (G : pre_graph) e x y u : 
  oarc G e x u y -> e \in edges_at G y.
Proof. rewrite oarc_cnv. exact: oarc_edge_atL. Qed.

Lemma oarc_del_vertex (G : pre_graph) z e x y u : 
  e \notin edges_at G z -> oarc G e x u y -> oarc (G \ z) e x u y.
Proof. move => Iz [edge_e H]. apply: conj H. by rewrite inE Iz. Qed.



(* Note that the assumption [e \notin eset G] is necessary since [G ∔ [e,x,u,y]] 
may otherwise turn an already existing edge not adjacent to [y] into one 
that is adjacent to [y]. This edge would not be removed in [G\y]. *)
Lemma add_edge_del_vertex (G : pre_graph) e x u y : 
  e \notin eset G -> G ∔ [e,x,u,y] \ y ≡G G \ y.
Proof.
  move => He. split => //=; rewrite edges_at_add_edge. 2: move => b.
  all: rewrite fsetUDU ?fdisjoint1X // => f /fsetDP [Hf _]; 
       rewrite update_neq //; by apply: contraNneq He => <-.
Qed.
Definition add_edgeKr := add_edge_del_vertex.

Lemma add_edgeKl (G : pre_graph) e x u y : 
  e \notin eset G -> G ∔ [e,x,u,y] \ x ≡G G \ x.
Admitted. (* similar to above, symmetry argument *)

Lemma add_testK (G : pre_graph) x a : G[adt x <- a] \ x ≡G G \ x.
Proof. split => //= y /fsetD1P [? _]. by rewrite updateE. Qed.

Lemma add_vertexK (G : pre_graph) x a : 
  x \notin vset G -> G ∔ [x, a] \ x ≡G G.
Proof. 
  move => Hx. split => //=.
  - by rewrite fsetU1K.
  - by rewrite edges_at_add_vertex // fsetD0.
  - rewrite fsetU1K // => y Hy. rewrite update_neq //. 
    by apply: contraNneq Hx => <-.
Qed.

Lemma edges_at_test (G : pre_graph) x a z : edges_at G[adt x <- a] z = edges_at G z. done. Qed.



Lemma edges_at_del_edges (G : pre_graph) z E : 
  edges_at (del_edges G E) z = edges_at G z `\` E. 
Proof.
  apply/fsetP => e. by rewrite !(inE,edges_atE) -andbA incident_dele.
Qed.

Lemma lv_add_edge (G : pre_graph) e x u y z : lv (G ∔ [e,x,u,y]) z = lv G z. done. Qed.

Definition step_order G H (s: ostep G H): nat :=
  match s with
  | ostep_v0 _ _ _ => 0
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
  (forall e, e \in edges_at G x -> endpt G false e = endpt G true e) -> x \notin pIO G -> ~ oconnected G.
Admitted.
  

Lemma oarc_uniqeR (G : pre_graph) e e' x y u : 
  edges_at G y = [fset e] -> oarc G e' x u y -> e' = e.
Proof. move => Iy /oarc_edge_atR. rewrite Iy. by move/fset1P. Qed.

Lemma oarc_uniqeL (G : pre_graph) e e' x y u : 
  edges_at G x = [fset e] -> oarc G e' x u y -> e' = e.
Proof. rewrite oarc_cnv. exact: oarc_uniqeR. Qed.

Lemma oarc_injL (G : pre_graph) e x x' y u u' : 
  oarc G e x u y -> oarc G e x' u' y -> x = x'.
Proof. 
  case => E [b] [? ? ?] [_ [b'] [? ? ?]]. subst. 
  by destruct b; destruct b'.
Qed.

Lemma oarc_injR (G : pre_graph) e x y y' u u' : 
  oarc G e x u y -> oarc G e x u' y' -> y = y'.
Proof. 
  case => E [b] [? ? ?] [_ [b'] [? ? ?]]. subst. 
  by destruct b; destruct b'.
Qed.

Lemma oarc_weq (G : pre_graph) e x y u u' : 
  x != y -> oarc G e x u y -> oarc G e x u' y -> u ≡ u'.
Proof. 
  move => xDy [[E] [b] [A B C]] [[_] [b'] [A' B' C']].

  (* move => xDy [E A1] [_ A2].  *)
  (* case: A1 => [[S1 T1 E1]|[S1 T1 E1]]; case: A2 => [[S2 T2 E2]|[S2 T2 E2]]; subst. *)
  (* - by rewrite -?E1 -?E2 //.  *)
  (* - by rewrite S2 eqxx in xDy. *)
  (* - by rewrite S2 eqxx in xDy. *)
  (* - by rewrite -[u]cnvI -E1 E2 cnvI. *)
Admitted.

Lemma oarc_loop G e x y x' u u' : oarc G e x u y -> oarc G e x' u' x' -> x = y.
Admitted.
(* Proof. move => [E [[? ? ?]|[? ? ?]]] [_ [[? ? ?]|[? ? ?]]]; by subst. Qed. *)

Lemma same_oarc G e x y x' y' u u' : oarc G e x u y -> oarc G e x' u' y' ->
  [/\ x = x', y = y' & u ≡ u'] + [/\ x = y', y = x' & u ≡ u'°].

Admitted.   
    

Lemma osteps_refl (G : pre_graph) (isG : is_graph G) : osteps G G.
Proof. apply: oliso_step. do 2 eexists. exact: iso2_id. Qed.

Ltac e2split := do 2 eexists; split; [split|].

Lemma iso2_edge_flip (G : graph2) (x y : G) u : G ∔ [x,u,y] ≃2 G ∔ [y,u°,x].
Proof.
  pose dir (e : edge (G ∔ [x,u,y])%G2) := ~~ e.
  iso2 bij_id bij_id dir => //.
  admit.
Defined.

(* We prove this directly rather than going though [liso_edge_flip],
because this way we can avoid the assumption [e \notin eset G] *)
Lemma add_edge_flip (G : pre_graph) (isG : is_graph G) e x y u v: 
  u° ≡ v ->
  x \in vset G -> y \in vset G -> G ∔ [e,x,u,y] ⩭2 G ∔ [e,y,v,x].
Proof.
  move => E xG yG. 
  have isG1 : is_graph (G ∔ [e,x,u,y]) by apply: add_edge_graph'.
  have isG2 : is_graph (G ∔ [e,y,v,x]) by apply: add_edge_graph'.
  do 2 eexists.
  pose dir (e0 : edge (close (G ∔ [e,x,u,y]) isG1)) := val e0 == e.
  iso2 bij_id bij_id dir => //=. 2-3: exact: val_inj.
  admit.
  (* - case => e' /= He'. case: (fset1UE He') => [?|].  *)
  (*   + subst e'. by rewrite /dir/= eqxx /= !updateE /= -E cnvI. *)
  (*   + case => A ?. by rewrite /dir/= (negbTE A) //= !updateE. *)
  (* - case => e' /= He'. apply: val_inj => /=. case: (fset1UE He') => [?|]. *)
  (*   + subst e'. by rewrite /dir/= eqxx /= !updateE. *)
  (*   + case => A ?. by rewrite /dir/= (negbTE A) /= !updateE. *)
  (* - case => e' /= He'. apply: val_inj => /=. case: (fset1UE He') => [?|]. *)
  (*   + subst e'. by rewrite /dir/= eqxx /= !updateE. *)
  (*   + case => A ?. by rewrite /dir/= (negbTE A) /= !updateE. *)
Defined.

Lemma del_edges_add_test (G : pre_graph) E x a : 
  (del_edges G E)[adt x <- a] ≡G del_edges G[adt x <- a] E. 
Proof. done. Qed.

Lemma del_edgesK (G : pre_graph) E z :
  E `<=` edges_at G z -> (del_edges G E) \ z ≡G G \ z.
Proof. 
  move => subE. split => //=. 
  by rewrite edges_at_del_edges fsetDDD (fsetUidPr _ _ subE).
Qed.

Lemma del_vertex_edges G E z : G \ z - E ≡G (G - E)\z.
Proof. 
  split => //. 
  by rewrite /del_vertex/= edges_at_del_edges fsetDDD fsetDDl fsetUC.
Qed.

Lemma degree_one_two G x y e e1 e2 : e1 != e2 -> 
  edges_at G x = [fset e] -> edges_at G y = [fset e1;e2] -> x != y.
Proof.
  move => A Ix Iy. apply: contra_neq A => ?;subst y. 
  wlog suff S : e1 e2 Iy / e1 = e.
  { rewrite (S _ _ Iy). symmetry. apply: S. by rewrite Iy fsetUC. }
  apply/eqP. by rewrite -in_fset1 -Ix Iy in_fset2 eqxx.
Qed.

Lemma vset_del_vertex G x z : x \in vset G -> x != z -> x \in vset (G \ z).
Proof. by rewrite /= !inE => -> ->. Qed.

Lemma vset_del_edges G E x : x \in vset G -> x \in vset (G - E).
Proof. done. Qed.

Hint Resolve vset_del_vertex vset_del_edges : vset.

Lemma oarc_vsetL G (isG : is_graph G) e x y u : 
  oarc G e x u y -> x \in vset G.
Proof. case => E [b] [<- _ _]. exact: endptP. Qed.

Lemma oarc_vsetR G (isG : is_graph G) e x y u : 
  oarc G e x u y -> y \in vset G.
Proof. case => E [b] [_ <- _]. exact: endptP. Qed.

Hint Resolve oarc_vsetL oarc_vsetR : vset.

Lemma fset2_inv (T : choiceType) (x y x' y' : T) : x != y ->
  [fset x;y] = [fset x';y'] -> (x = x' /\ y = y') + (x = y' /\ y = x').
Proof.
  move => /negbTE D /fsetP H. move: (H x). rewrite !inE eqxx /= => /esym. 
  case/orb_sum => /eqP ?;[left|right]; subst; move: (H y).
  - rewrite !inE eqxx orbT eq_sym D. by move/esym/eqP.
  - rewrite !inE eqxx orbT [y == y']eq_sym D orbF. by move/esym/eqP.
Qed.

Lemma close_same_step (Gl Gr : pre_graph) (isGl : is_graph Gl) (isGr : is_graph Gr) : 
  Gl ≡G Gr -> Σ Gl' Gr' : pre_graph, osteps Gl Gl' * osteps Gr Gr' * (Gl' ≡G Gr').
Proof. move => E. do 2 eexists; split;[split|]; by try exact: osteps_refl. Qed.


Lemma incident_flip_edge G e x u y : 
  incident (G ∔ [e, x, u, y]) =2 incident (G ∔ [e, y, u°, x]).
Proof. 
  move => z f. rewrite /incident/= !existsb_case.
  case: (altP (f =P e)) => [->|?]; by rewrite !updateE // orbC.
Qed.

Lemma edges_atC G e x y u : edges_at (G ∔ [e,x,u,y]) =1 edges_at (G ∔ [e,y,u°,x]).
Proof. move => z. apply/fsetP => f. by rewrite !edges_atE /= incident_flip_edge. Qed.

Lemma add_edge_del_edges (G : pre_graph) e E x y u : 
  e \notin E -> G ∔ [e,x,u,y] - E ≡G (G - E) ∔ [e,x,u,y]. 
Proof. move => He. split => //=. by rewrite fsetUDl mem_fsetD1. Qed.

Lemma fset1D (T : choiceType) (x:T) (A : {fset T}) : 
  [fset x] `\` A = if x \in A then fset0 else [fset x].
Proof. 
  case: (boolP (x \in A)) => xA. 
  - apply/eqP. by rewrite fsetD_eq0 fsub1set.
  - apply/fsetDidPl. by rewrite fdisjoint1X.
Qed.

Lemma add_edge_del_edgesK (G : pre_graph) e E x y u : 
  e \in E -> G ∔ [e,x,u,y] - E ≡G (G - E). 
Proof.
  move => eE. 
  have X : (e |` eset G) `\` E = eset G `\` E.
  { by rewrite fsetDUl fset1D eE fset0U. }
  split => //=; rewrite X. 1: move => b.
  all: move => f Hf; rewrite updateE //.
  all: apply: contraTneq Hf => ->; by rewrite inE eE.
Qed.

Lemma del_edges_vertexK (G : pre_graph) E z : 
  E `<=` edges_at G z -> (G - E) \ z ≡G G \ z.
Proof. 
  move => EIz. split => //=. 
  by rewrite fsetDDl edges_at_del_edges fsetUDl fsetDv fsetD0 (fsetUidPr _ _ EIz).
Qed.

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
Proof.
  move => eDe'. split => //=; first by rewrite fsetUA [[fset _;_]]fsetUC -fsetUA.
  1: move => b.
  all: move => f; case/fset1UE => [->|[?]]; last case/fset1UE => [->|[? ?]].
  all: by rewrite !updateE // eq_sym.
Qed.

(*TOTHINK: this looks messier than needed *)
Lemma edges_replace (G : pre_graph) (z z' : VT) (e1 e2 e2' : ET) (x : VT) (u : tm) :
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


(** TODO fix the 2pdom theory *)

Lemma cnvtst (a : test) : a° ≡ a. Admitted.

Lemma critical_pair1 u v (a :test) : dom ((u∥v°)·a) ≡ 1 ∥ u·a·v.
(* Proof. by rewrite -dotA A10 cnvdot cnvtst -lifttstR. Qed. *)
Admitted.

Lemma critical_pair2 (u v : tm) : (1∥u)·(1∥v) ≡ 1∥(u∥v).
(* Proof. by rewrite dotpartst' parA [_∥1]parC !parA par11. Qed. *)
Admitted.

Lemma edges_at_oarc G e x y z u : 
  e \in edges_at G z -> oarc G e x u y -> x = z \/ y = z.
Admitted.

Lemma add_test_merge G x a b : 
  G[adt x <- a][adt x <- b] ≡G G[adt x <- [a·b]].
Proof. 
  constructor => //= y yG. 
  case: (altP (y =P x)) => [->|?]; rewrite !updateE //=.
  by rewrite infer_testE dotA.
Qed.

Lemma par_tst_cnv (a : test) u : a ∥ u° ≡ a ∥ u.
(* Proof. by rewrite -[a∥u]/(term_of [a∥u]) -(@cnvtst [a∥u]) /= cnvpar cnvtst. Qed. *)
Admitted.

Lemma oarcxx_le G e x u : oarc G e x u x -> 1∥le G e ≡ 1∥u.
(* Proof. by case => _ [[_ _ A]|[_ _ A]]; rewrite A ?par_tst_cnv. Qed. *)
Admitted.



Lemma local_confluence_aux (G : pre_graph) (isG : is_graph G) Gl Gr : 
  ostep G Gl -> ostep G Gr -> Σ Gl' Gr', osteps Gl Gl' * osteps Gr Gr' * (Gl' ≡G Gr'). 
Proof with eauto with typeclass_instances.
  have conn_G : oconnected G by admit. (* fixme: this should be removed *)
  move => S1 S2.
  wlog : Gl Gr S1 S2 / step_order S1 <= step_order S2.
  { move => W. case/orb_sum: (leq_total (step_order S1) (step_order S2)) => SS.
    - exact: W SS.
    - case: (W _ _ _ _ SS) => H' [G'] [[stpG stpH] E]. 
      do 2 eexists; split; first split. 1-2:eassumption. by symmetry. }
  (* naming convention: primes on the second/right rule *)
  destruct S1 as [z Iz zIO|
                  x  z  e  u  Iz  zIO  arc_e  xDz |
                  x y z e1 e2 u v Iz e1De2 zIO xDz yDz arc_e1 arc_e2|
                  x e u arc_e |
                  x y e1 e2 u v e1De2 arc_e1 arc_e2];
  destruct S2 as [z' Iz' zIO'|
                  x' z' e' u' Iz' zIO' arc_e' xDz'|
                  x' y' z' e1' e2' u' v' Iz' e1De2' zIO' xDz' yDz' arc_e1' arc_e2'|
                  x' e' u' arc_e' |
                  x' y' e1' e2' u' v' e1De2' arc_e1' arc_e2'];
  rewrite //=; move => CASE_TAG.
  - (* V0 / V0 *)
    case: (altP (z =P z')) => [?|D].
    + subst z'. do 2 exists ((G \ z)%O). split => //. split => //; exact: osteps_refl.
    + exists (G \ z \ z')%O. exists (G \ z' \ z)%O. rewrite {2}del_vertexC. split => //.
      split; apply ostep_step,ostep_v0 => //; by rewrite edges_at_del Iz Iz' fsetD0.
  - (* V0 / V1 *) 
    (* have Hz : z \notin [fset z'; x']. - not actually needed *) 
    e2split.
    + eapply ostep_step,ostep_v1. 3: eapply oarc_del_vertex,arc_e'. all: try done.
      * by rewrite edges_at_del Iz Iz' fsetD0.
      * by rewrite Iz inE.
    + eapply ostep_step,(ostep_v0 (z := z)). 2:done.
      by rewrite edges_at_del edges_at_test Iz fset0D.
    + by rewrite del_vertexC del_vertex_add_test.
  - (* V0 / V2 *) 
    have ? : z != z'. { apply: contra_eq_neq Iz' => <-. by rewrite Iz eq_sym fset1U0. }
    have [? ?] : x' != z /\ y' != z. 
    { split. 
      - apply: contra_eq_neq Iz => <-. apply/fset0Pn; exists e1'. exact: oarc_edge_atL arc_e1'.
      - apply: contra_eq_neq Iz => <-. apply/fset0Pn; exists e2'. exact: oarc_edge_atR arc_e2'. }
    e2split.
    + eapply ostep_step,ostep_v2. 
      6-7: apply: oarc_del_vertex. 7: apply arc_e1'. 8: apply: arc_e2'.
      all: try done.
      all: by rewrite ?edges_at_del ?Iz ?Iz' ?fsetD0 ?inE.
    + eapply ostep_step,(ostep_v0 (z := z)). 2:done.
      rewrite @edges_at_add_edge' //=. 
      * by rewrite edges_at_del Iz fset0D.
      * by rewrite Iz' maxn_fsetD.
    + by rewrite -del_vertex_add_edge 1?eq_sym 1?del_vertexC //= Iz' maxn_fsetD.
  - (* V0 / E1 *) admit.
  - (* V0 / E2 *) admit.
  - (* V1 / V1 *) 
    case: (altP (z =P z')) => [E|D]. 
    + (* same instance *)
      subst z'. 
      have ? : e' = e by apply: oarc_uniqeR arc_e'. subst e'.
      have ? : x = x' by apply: oarc_injL arc_e arc_e'. subst x'.
      apply: close_same_step. 
      suff -> : [dom (u·lv G z)] ≡ [dom (u'·lv G z)] by [].
      by rewrite infer_testE (oarc_weq _ arc_e arc_e').
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
        rewrite edges_at_del !edges_at_test Iz Iz'. 
        (* fset? *) by rewrite fsetDUl fsetDv fsetU0 mem_fsetD1 // inE eq_sym.
      * eapply ostep_step, ostep_v1. 
        3: exact: oarc_added_edge. 
        all: try done.
        rewrite edges_at_add_edge ?edges_at_del Iz Iz'. 
        rewrite [_ `\` _](_ : _ = fset0) ?fsetU0 //.
        apply/eqP. by rewrite fsetD_eq0 fsub1set in_fset2 eqxx.
      * rewrite /= updateE. set a := lv G z. set b := lv G z'. 
        rewrite -del_vertex_add_test del_vertexC add_testK. 
        rewrite -del_vertex_add_test add_edgeKr /= ?Iz' ?maxn_fsetD //.
        apply: add_test_morphism => //. rewrite infer_testE.
        by rewrite dotA -A13 !dotA (oarc_weq _ arc_e2' arc_e).
    + (* independent case *)
      move: xD'. rewrite in_fset2 negb_or => /andP [zDx zDy].
      have E1 : e1' != e. 
      { rewrite -in_fset1 -Iz. apply/negP => H. move:(edges_at_oarc H arc_e1'). 
        case => ?;subst; by rewrite eqxx in zDx zDz'.  }
      have E2 : e2' != e. 
      { rewrite -in_fset1 -Iz. apply/negP => H. move:(edges_at_oarc H arc_e2'). 
        case => ?;subst; by rewrite eqxx in zDy zDz'. }
      have Z : z' != x. 
      { apply: contraTneq (oarc_edge_atL arc_e) => <-. 
        by rewrite Iz' in_fset2 negb_or ![e == _]eq_sym E1. }
      have ? : e \notin [fset e1';e2'] by rewrite in_fset2 negb_or ![e == _]eq_sym E1.
      e2split. 
      * eapply ostep_step, ostep_v2. 
        6: { apply: oarc_del_vertex. 2: apply: arc_e1'. by rewrite edges_at_test Iz inE. }
        6: { apply: oarc_del_vertex. 2: apply: arc_e2'. by rewrite edges_at_test Iz inE. }
        all: try done. 
        by rewrite edges_at_del !edges_at_test Iz Iz' mem_fsetD1.
      * eapply ostep_step, ostep_v1. 
        3: { apply: oarc_add_edge. 2:apply: oarc_del_vertex arc_e. 
             apply: fset2_maxn_neq => //. by rewrite Iz'. }
        all: try done. 
        rewrite edges_at_add_edge' ?[_ == z]eq_sym //= ?edges_at_del ?Iz Iz' ?maxn_fsetD //.
        by rewrite -fsetDDl !mem_fsetD1 ?inE.
      * set e12 := maxn _ _. set a := lv G z. set b := lv G z'. set a' := lv _ z. set b' := lv _ z'. 
        have <- : a = a' by []. have <- : b = b'. rewrite /b /b' /= updateE //. 
        rewrite del_vertexC -del_vertex_add_test add_edge_test. rewrite -del_vertex_add_edge //. 
        by rewrite /= inE negb_and negbK Iz' !inE maxn_eq.
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
  - (* V1 / E2 - no nontrivial interaction *)
    gen have D,zDx : e1' e2' x' y' u' v' arc_e1' arc_e2' e1De2' / x' != z. 
    { apply: contra_neq e1De2' => ?. subst x'. 
      wlog suff : e1' e2' u' v' arc_e1' arc_e2' / e1' = e. 
      { move => S. by rewrite (S _ _ _ _ arc_e1' arc_e2') (S _ _ _ _ arc_e2' arc_e1'). }
      apply/eqP. rewrite -in_fset1 -Iz. apply: oarc_edge_atL arc_e1'. }
    have {D} zDy : y' != z. 
    { rewrite -> oarc_cnv in arc_e1',arc_e2'. apply: D arc_e2' arc_e1' _. by rewrite eq_sym. }
    have E1 : e1' != e. 
    { rewrite -in_fset1 -Iz. apply/negP => H. move:(edges_at_oarc H arc_e1'). 
      case => ?;subst; by rewrite eqxx in zDx zDy. }
    have E2 : e2' != e. 
    { rewrite -in_fset1 -Iz. apply/negP => H. move:(edges_at_oarc H arc_e2'). 
      case => ?;subst; by rewrite eqxx in zDx zDy. }
    have ? : e \notin [fset e1';e2'] by rewrite in_fset2 negb_or ![e == _]eq_sym E1.
    e2split.
    * eapply ostep_step, ostep_e2. 
      -- exact: e1De2'.
      -- apply: oarc_del_vertex arc_e1'. by rewrite Iz inE.
      -- apply: oarc_del_vertex arc_e2'. by rewrite Iz inE.
    * eapply ostep_step, ostep_v1.
      3: { apply: oarc_add_edge. 2: apply: oarc_del_edges arc_e => //.
           exact: fset2_maxn_neq. }
      all: try done.
      rewrite edges_at_add_edge' //= ?maxn_fsetD //. 
      by rewrite edges_at_del_edges -fsetDDl !mem_fsetD1 // Iz in_fset1.
    * rewrite /= add_edge_test del_edges_add_test -del_vertex_add_edge -?del_vertex_edges // 1?eq_sym //.
      by rewrite maxn_fsetD.
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
      subst e1' e2'. 
      move: (oarc_injL arc_e1 arc_e1') (oarc_injR arc_e2 arc_e2') => ? ?. subst x' y'.
      by rewrite (oarc_weq _ arc_e1' arc_e1) ?(oarc_weq _ arc_e2' arc_e2) // eq_sym.
     + (* independent instances *)
       move: (fdisjointP D) => D1. rewrite fdisjoint_sym in D. move: (fdisjointP D) => D2.
       have ?: x != z'. 
       { apply: contraTneq (oarc_edge_atL arc_e1) => ->. by rewrite Iz' D1 // in_fset2 eqxx. }
       have ?: y != z'. 
       { apply: contraTneq (oarc_edge_atR arc_e2) => ->. by rewrite Iz' D1 // in_fset2 eqxx. }
       have ?: x' != z. 
       { apply: contraTneq (oarc_edge_atL arc_e1') => ->. by rewrite Iz D2 // in_fset2 eqxx. }
       have ?: y' != z. 
       { apply: contraTneq (oarc_edge_atR arc_e2') => ->. by rewrite Iz D2 // in_fset2 eqxx. }
       (* have zDz' : z != z'. by admit. *)       
       e2split.
       * eapply ostep_step,ostep_v2. 
         7: { apply: oarc_add_edge. 2:apply: oarc_del_vertex arc_e2'. 
              apply: fset2_maxn_neq. by rewrite D2 // in_fset2 eqxx.
              by rewrite Iz D2 // !inE eqxx. }
         6: { apply: oarc_add_edge. 2:apply: oarc_del_vertex arc_e1'. 
              apply: fset2_maxn_neq. by rewrite D2 // in_fset2 eqxx.
              by rewrite Iz D2 // !inE eqxx. }
         all: try done.
         rewrite edges_at_add_edge' //= ?Iz ?maxn_fsetD // edges_at_del Iz Iz'. 
         by apply/fsetDidPl.
       * eapply ostep_step,ostep_v2. 
         7: { apply: oarc_add_edge. 2: apply: oarc_del_vertex arc_e2. 
              apply: fset2_maxn_neq. by rewrite D1 // in_fset2 eqxx.
              by rewrite Iz' D1 // in_fset2 eqxx. }
         6: { apply: oarc_add_edge. 2: apply: oarc_del_vertex arc_e1. 
              apply: fset2_maxn_neq. by rewrite D1 // in_fset2 eqxx.
              by rewrite Iz' D1 // !inE eqxx. }
         all: try done.
         (* FIXME : swap disequality assumptions on edges_at_add_edge' *)
         rewrite edges_at_add_edge' //= ?Iz' ?maxn_fsetD // edges_at_del Iz Iz'. 
         apply/fsetDidPl. by rewrite fdisjoint_sym.
       * rewrite /=. rewrite -!del_vertex_add_edge /= ?Iz ?Iz' 1?eq_sym ?maxn_fsetD //.
         rewrite del_vertexC add_edge_edge //. 
         by case: maxnP => _; rewrite fset2_maxn_neq // D1 // !inE eqxx.
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
         6: apply: oarc_add_edge. 7: apply: oarc_del_vertex arc_e2'. 
         all: try done. 
         -- exact: edges_replace.
         -- by case/orP : (maxn_eq e1 e2) => /eqP ->.
         -- apply: contraTneq (oarc_edge_atL arc_e1) => ->. by rewrite Iz' !inE negb_or e1De2.
         -- apply: fset2_maxn_neq. by rewrite in_fset2 ![e2' == _]eq_sym negb_or E1.
         -- by rewrite Iz !inE negb_or eq_sym E1 eq_sym.
       * eapply ostep_step,ostep_v2. 
         7: apply: oarc_added_edge.
         6: apply: oarc_add_edge. 7: apply: oarc_del_vertex arc_e1.
         all: try done. 
         -- rewrite edges_atC fsetUC maxnC. apply: edges_replace; by rewrite // 1?fsetUC 1?eq_sym.
         -- by case/orP : (maxn_eq e2 e2') => /eqP ->.
         -- apply: contraTneq (oarc_edge_atR arc_e2') => ->.
            by rewrite Iz !inE negb_or eq_sym E1 eq_sym.
         -- apply: fset2_maxn_neq. by rewrite in_fset2 negb_or e1De2.
         -- by rewrite Iz' !inE negb_or e1De2.
       * rewrite !add_edgeKr ?add_edgeKl /= ?Iz ?Iz' ?maxn_fsetD //.
         by rewrite del_vertexC maxnA !dotA C.
  - (* V2 / E0 *) 
    have He : e' \notin edges_at G z. 
    { rewrite Iz in_fset2 negb_or. apply/andP; split.
      - apply: contra_neq xDz => ?; subst e'. exact: oarc_loop arc_e1 arc_e'.
      - apply: contra_neq yDz => ?; subst e'. symmetry. exact: oarc_loop arc_e2 arc_e'. }
    have xDz' : z != x' by apply: contraTneq (oarc_edge_atL arc_e') => <-. 
    have He' : e' != maxn e1 e2. apply: fset2_maxn_neq. by rewrite -Iz. 
    e2split. 
    * eapply ostep_step,ostep_e0. apply: oarc_add_edge He' _. exact: oarc_del_vertex arc_e'.      
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
        rewrite -del_vertex_add_test add_edgeKr /= ?maxn_fsetD //.
        rewrite add_edge_del_edgesK ?inE ?eqxx // del_vertex_edges. 
        rewrite !del_edges_vertexK ?fsubUset ?fsub1set ?Iz ?in_fset2 ?eqxx ?maxn_eq //.
        apply: add_test_morphism => //=. by rewrite infer_testE -Eu -Ev critical_pair1.
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
        3:{ apply: oarc_add_edge. 2:exact: oarc_del_vertex arc_e2'. 
            apply: fset2_maxn_neq. by rewrite -Iz. }
        2:{ apply: oarc_add_edge. 2:exact: oarc_del_vertex arc_e1'. 
            apply: fset2_maxn_neq. by rewrite -Iz. } 
        done.
      * eapply ostep_step,ostep_v2. 
        7: { apply: oarc_add_edge. 2:exact: oarc_del_edges arc_e2. 
             exact: fset2_maxn_neq. }
        6: { apply: oarc_add_edge. 2: exact: oarc_del_edges arc_e1. 
             exact: fset2_maxn_neq. }
        all: try done.
        rewrite edges_at_add_edge' //= ?maxn_fsetD // edges_at_del_edges. 
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
        - apply: add_edge_graph'; by eauto with vset.
        - apply: add_edge_graph'; by eauto with vset.
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
        rewrite infer_testE /= (oarcxx_le arc_e1') (oarcxx_le arc_e2').
        by rewrite critical_pair2.
    + (* independent case *)
      set e' := maxn _ _. 
      have eDe' : e != e' by rewrite fset2_maxn_neq .
      e2split. 
      * eapply ostep_step,ostep_e2; [exact: e1De2'| |].
        -- apply: oarc_del_edges arc_e1'. apply: contraNN He. by rewrite !inE eq_sym => ->.
        -- apply: oarc_del_edges arc_e2'. apply: contraNN He. by rewrite !inE eq_sym => ->.
      * eapply ostep_step,ostep_e0. apply: oarc_add_edge eDe' _. exact: oarc_del_edges arc_e.
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
           apply: add_test_morphism => //. rewrite infer_testE. admit.
           (* rewrite Hu Hv. rewrite [u'∥_]parC parA -[1]/(term_of [1]) par_tst_cnv. *)
           (* by rewrite -parA [v'∥_]parC. *)
    + (* independent instances *)
      move: (fdisjointP D) => D1. rewrite fdisjoint_sym in D. move: (fdisjointP D) => {D} D2.
      e2split. 
      * apply ostep_step,ostep_e2. 
        -- exact: e1De2'.
        -- apply: oarc_add_edge. 
           ++ apply: fset2_maxn_neq. by rewrite D2 // in_fset2 eqxx.
           ++ apply: oarc_del_edges arc_e1'. by rewrite D2 // !inE eqxx.
        -- apply: oarc_add_edge. 
           ++ apply: fset2_maxn_neq. by rewrite D2 // in_fset2 eqxx.
           ++ apply: oarc_del_edges arc_e2'. by rewrite D2 // !inE eqxx.
      * apply ostep_step,ostep_e2. 
        -- exact: e1De2.
        -- apply: oarc_add_edge. 
           ++ apply: fset2_maxn_neq. by rewrite D1 // in_fset2 eqxx.
           ++ apply: oarc_del_edges arc_e1. by rewrite D1 // !inE eqxx.
        -- apply: oarc_add_edge. 
           ++ apply: fset2_maxn_neq. by rewrite D1 // !inE eqxx.
           ++ apply: oarc_del_edges arc_e2. by rewrite D1 // !inE eqxx.
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
        by rewrite !cnvpar. }
      subst.
      have He2' : e2' \notin [fset e1; e2] by rewrite !inE negb_or ![e2' == _]eq_sym E1 e1De2'.
      have He1 : e1 \notin [fset e2; e2'] by rewrite !inE negb_or e1De2. 
      e2split.
      * eapply ostep_step,ostep_e2. 
        2: exact: oarc_added_edge.
        2: { apply: oarc_add_edge. 2:exact: oarc_del_edges arc_e2'.
             exact: fset2_maxn_neq. }
        by case: maxnP.
      * eapply ostep_step,ostep_e2.
        3: exact: oarc_added_edge.
        2: { apply: oarc_add_edge. 2: exact: oarc_del_edges arc_e1. 
             exact: fset2_maxn_neq. }
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
Qed.

Lemma ostep_graph (F G : pre_graph) (isG : is_graph F) : ostep F G -> is_graph G.
Admitted.

Lemma osteps_graph (F G : pre_graph) (isG : is_graph F) : osteps F G -> is_graph G.
Admitted.

Proposition local_confluence (F G1 G2 : pre_graph) (isF : is_graph F) : 
  ostep F G1 -> ostep F G2 -> Σ H, osteps G1 H * osteps G2 H.
Proof.
  move => S1 S2.
  move: (local_confluence_aux isF S1 S2) => [H1] [H2] [[S1' S2'] I].
  exists H2. split => //. apply: osteps_trans (S1') _. apply: oliso_step. 
  suff [isH1 isH2] : is_graph H1 /\ is_graph H2 by apply: weqG_oliso I.
  split. 
  - unshelve eapply (osteps_graph _ S1'). apply: ostep_graph S1.
  - unshelve eapply (osteps_graph _ S2'). apply: ostep_graph S2.
Qed.

Lemma oiso2_del_vertex (F G : pre_graph) (z : VT) (i : F ⩭2 G) : 
  z \notin pIO F -> F \ z ⩭2 G \ i z.
Proof.   
Admitted.

Lemma osteps_iso (F G H : pre_graph) : 
  ostep F G -> F ⩭2 H -> Σ U, ostep H U * (G ⩭2 U).
Proof.
  case => {G}.
  - move => z Iz zIO i. exists (H \ i z)%O. split.
    + apply ostep_v0. admit. admit.
    + exact: oiso2_del_vertex. 
  - admit.
  - admit.
  - admit.
Admitted.


Lemma inj_v_fresh (G : graph2) (x : G) (z : VT) : z \notin vset (open G) -> inj_v x != z.
Proof. apply: contraNneq => <-. exact: inj_v_open. Qed.

Lemma vset_add_vertex (G : pre_graph) x a z : 
  z \in vset (G ∔ [x,a]) = (z == x) || (z \in vset G).
Proof. by rewrite /= !inE. Qed.

(** connecting the open step relation with the additive one on typed graphs *)

Lemma osteps_of (G H : graph2) : step G H -> osteps (open G) (open H).
Proof with eauto with typeclass_instances.
  case => {G H}.
  - (* V0 *) 
    move => G a. apply: oliso_stepL (open_add_vertex _ _ ) _.
    apply: ostep_stepL. apply: (ostep_v0 (z := fresh (vset (open G)))).
    + by rewrite edges_at_add_vertex // freshP.
    + by rewrite pIO_add_vertex pIO_fresh // freshP.
    + apply: oliso_step. apply weqG_oliso... 
      * eapply del_vertex_graph... constructor. 
        by rewrite pIO_add_vertex pIO_fresh // freshP.
      * apply: add_vertexK. exact: freshP.
  - (* V1 *) move => G x u a.
    (* test *)
    apply: oliso_stepL (open_add_edge _ _ _) _.
    apply: oliso_stepL. apply: add_edge_cong. apply open_add_vertex. 
      1-2: exact: inj_v_open.
    rewrite !open_add_vertexE. 
    apply: oliso_stepR. apply open_add_test. 
    rewrite /add_edge. set z := fresh (vset _). set e := fresh (eset _). 
    apply: ostep_stepL. apply: (@ostep_v1 _ (inj_v x) z e u).
    + by rewrite edges_at_add_edge ?edges_at_add_vertex ?freshP // fsetU0.
    + rewrite !pIO_add. by rewrite pIO_fresh // freshP.
    + exact: oarc_added_edge.
    + by rewrite inj_v_fresh // freshP. 
    + set b := [dom _]. apply: oliso_step. apply weqG_oliso...
      { apply del_vertex_graph; first apply add_test_graph.
        - by apply: add_edge_graph; rewrite vset_add_vertex ?eqxx ?inj_v_open.
        - rewrite ?pIO_add. constructor. by rewrite pIO_fresh // freshP. }
      rewrite -del_vertex_add_test add_edge_del_vertex.
      * by rewrite add_vertexK ?freshP // /b/= updateE.
      * admit.
  - (* V2 *) admit.
  - (* E0 *) move => G x u.
    apply: oliso_stepL (open_add_edge _ _ _) _.
    apply: oliso_stepR (open_add_test _ _) _.
    rewrite /add_edge. set e := fresh _.
    apply: ostep_stepL. apply: (@ostep_e0 _ (inj_v x) e u). 
    + exact: oarc_added_edge.
    + apply: oliso_step. apply weqG_oliso... admit. admit.
  - admit.
Admitted.

Lemma del_vertexK (G : pre_graph) (isG : is_graph G) z : 
  add_vertex (G \ z) z (lv G z) ≡G del_edges G (edges_at G z).
Admitted.


Lemma close_add_edge_eq G e x y u (isG : is_graph G) (x' y' : close G) (isG' : is_graph (G ∔ [e,x, u, y])) :
  e \notin eset G -> x' = close_v x :> close G -> y' = close_v y :> close G -> 
  close (G ∔ [e,x, u, y]) ≃2 close G ∔ [x', u,y'].
Admitted.


      
Lemma steps_of (G H : pre_graph) (isG : is_graph G) (isH : is_graph H) : 
  ostep G H -> steps (close G) (close H).
(*
Proof with eauto with typeclass_instances.
  move => S. case: S isG isH => {H}.
  - move => x z e u He Hz arc_e xDz isG isH.
    set a := lv G z in isH *.
    have xV : x \in vset G by eauto with vset.
    have x_del_z : x \in vset (G \ z) by eauto with vset.
    have z_del_z : z \notin vset (G \ z) by rewrite !inE eqxx.
    have h : close G ≃2 close (G \ z) ∔ a ∔ [Some (close_v x), u, None].
    { symmetry.
      apply: iso2_comp. apply: (iso2_add_edge _). apply liso_sym, close_add_vertex,z_del_z.
      rewrite /=. 
      set Sx := Sub _ _. set Sz := Sub z _. set G' := add_vertex _ _ _.
      have -> : Sx = (@close_v G' _ x). { apply: val_inj. rewrite /= !close_vK /G' //. admit. }
      have -> : Sz = (@close_v G' _ z). { admit. } 
      apply: liso_comp (liso_sym _) _. eapply close_add_edge. 
      apply: liso_of_oliso. apply weqG_oliso...
      - apply: add_edge_graph. by rewrite !inE xDz (oarc_vsetL _ arc_e). by rewrite !inE eqxx.
      - admit. }
    apply: cons_step h _ _. constructor. 
    apply liso_step. rewrite -> close_add_test => //. 
    apply: liso_of_oliso. apply: weqG_oliso. by rewrite del_vertex_add_test.
  - move => x y z e1 e2 u v Iz e1De2 Hz xDz yDz arc_e1 arc_e2 isG isH.
    set a := lv G z in isH *.
    have xV : x \in vset G by eauto with vset.
    have yV : y \in vset G by eauto with vset.
    have x_del_z : x \in vset (G \ z) by eauto with vset.
    have y_del_z : y \in vset (G \ z) by eauto with vset.
    have z_del_z : z \notin vset (G \ z) by rewrite !inE eqxx.
    have h : close G ≃2 
             close (G \ z) ∔ a ∔ [Some (close_v x),u,None] ∔ [None,v,Some (close_v y)].
    { symmetry. 
      apply: liso_comp. 
        apply: liso_add_edge. 
        apply: liso_add_edge. 
        apply: liso_sym. apply: close_add_vertex z_del_z. 
      rewrite /=. 
      set Sx := Sub _ _. set Sz := Sub _ _. set Sy := Sub _ _. set G' := add_vertex _ _ _.
      (* have -> : Sx = (@close_v G' _ x). admit. *)
      (* have -> : Sy = (@close_v G' _ y). admit. *)
      (* have -> : Sz = (@close_v G' _ z). admit. *)
      have isG' : is_graph (G' ∔ [e1,x, u, z]). admit.
      apply: liso_comp. 
        apply: liso_add_edge.
        apply: liso_sym. apply (@close_add_edge_eq _ e1 x z).
        admit.
        admit.
        admit.
      apply: liso_comp.
        apply: liso_sym. eapply (@close_add_edge_eq _ e2 z y).
        admit.
        admit.
        admit.
      admit.
    }
    apply: cons_step h _ _. constructor. 
    apply liso_step. apply: liso_sym _.
    apply: (@close_add_edge' (G \ z)). by rewrite /= Iz maxn_fsetD. 
  - admit.
  - admit.
*)
Admitted.

Definition measure (G : pre_graph) := (#|` vset G| + #|` eset G|)%N.

Lemma step_decreases (F G : pre_graph) : ostep F G -> measure G < measure F.
Admitted.

Lemma iso2_stagnates (F G : pre_graph) : F ⩭2 G -> measure G = measure F.
Admitted.


Inductive osteps1L : pre_graph -> pre_graph -> Prop := 
| Osteps1L_iso F G : F ⩭2 G -> osteps1L F G
| Osteps1L_ostep F G H : ostep F G -> osteps1L G H -> osteps1L F H.

Lemma osteps1L_refl G : osteps1L G G. Admitted.

Lemma osteps1L_trans : Transitive osteps1L.
Proof. 
  (* requires well-founded induction to push isomorphims down *)
Admitted.
      
Lemma osteps1LP F G : osteps F G -> osteps1L F G.
Proof. 
  elim => {F G}. 
  - move => F G. exact: Osteps1L_iso.
  - move => F G S. apply: Osteps1L_ostep S _. exact: osteps1L_refl.
  - move => F G H ? S1 ?. exact: osteps1L_trans.
Qed.

Proposition open_confluence (F G H : pre_graph) (isF : is_graph F) : 
  osteps F G -> osteps F H -> exists F', is_graph F' /\ (osteps G F') /\ (osteps H F').
Proof.
  induction F as [F_ IH] using (well_founded_induction_type (Wf_nat.well_founded_ltof _ measure)).
Admitted.

Lemma osteps_of_steps (G H : graph2) : steps G H -> osteps (open G) (open H).
Admitted.

Lemma steps_of_osteps (G H : pre_graph) (isG : is_graph G) (isH : is_graph H) :
  osteps G H -> steps (close G) (close H).
Admitted.


Theorem confluence (F G H : graph2) : 
  steps F G -> steps F H -> exists F', steps G F' /\ steps H F'.
Proof.
  move => /osteps_of_steps S1 /osteps_of_steps S2.
  case: (open_confluence _ S1 S2) => F' [isF' [/steps_of_osteps S1' /steps_of_osteps S2']]. 
  exists (close F'). split. 
  + transitivity (close (open G)) => //. apply: iso_step. exact: openK.
  + transitivity (close (open H)) => //. apply: iso_step. exact: openK.
Qed.

End ostep.
End OpenCloseFacts.
