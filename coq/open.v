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
(* TODO move elsewhere *)

Lemma iso2_intro (L : labels) (G H : graph2 L) (hv : bij G H) (he : bij (edge G) (edge H)) (hd : edge G -> bool) :
  is_hom hv he hd -> hv input = input -> hv output = output -> G ≃2 H.
Proof. move => hom_h. by exists (Iso hom_h). Defined.

Tactic Notation "iso2" uconstr(hv) uconstr(he) uconstr(hd) := 
  match goal with |- ?G ≃2 ?H => refine (@iso2_intro _ G H hv he hd _ _ _) end.



Lemma testC X (a b : test X) : a·b ≡ b·a. 
Proof. exact: tst_dotC. Qed.

Lemma eqvxx (X : setoid) (x : X) : x ≡ x. reflexivity. Qed.
Arguments eqvxx [X x].
Arguments eqv : simpl never.

Lemma infer_testE X x x' y y' p p' : 
  (@infer_test X x y p) ≡ (@infer_test X x' y' p') <-> x ≡ x'.
Proof. rewrite /infer_test. by subst. Qed.

Lemma eqvb_trans (X : pttdom) (u v w : X) (b1 b2 : bool) : 
  u ≡[b1] v -> v ≡[b2] w -> u ≡[b1 (+) b2] w.
Proof. 
  case: b1; case: b2 => //=; eauto using eqv10, eqv01, eqv11. 
  by transitivity v.
Qed.

Lemma eqvb_transR (X : pttdom) b b' (u v v' : X) : 
  u ≡[b (+) b'] v' ->  v' ≡[b'] v ->  u ≡[b] v.
Proof. move => A B. move:(eqvb_trans A B). by rewrite -addbA addbxx addbF. Qed.

Lemma eqvb_transL (X : pttdom) b b' (u u' v : X) : 
  u' ≡[b (+) b'] v ->  u ≡[b'] u' ->  u ≡[b] v.
Proof. move => A B. move:(eqvb_trans B A). by rewrite addbC -addbA addbxx addbF. Qed.

(** whats a reasonable name for [u ≡[b] v] and the associated lemmas? *)
Lemma eqvb_neq (X: pttdom) (u v : X) b : u ≡[~~b] v <-> u ≡[b] v°.
Proof. 
  split; apply: eqvb_transL.
  - rewrite addbN addbxx. change (v ≡ v°°). by rewrite cnvI.
  - by rewrite addNb addbxx. 
Qed.


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

(* TODO: lock this, so that one can no longer confuse vertices and edges*)
Definition VT := nat.
Definition ET := nat.

Canonical VT_eqType := [eqType of VT].
Canonical VT_choiceType := [choiceType of VT].
Canonical VT_countType := [countType of VT].
Canonical ET_eqType := [eqType of ET].
Canonical ET_choiceType := [choiceType of ET].
Canonical ET_countType := [countType of ET].

(** Injecting arbitrary fintypes (e.g., vertex and edge type) into the generic
vertex and edge type *)
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

(** Unlike the typed graphs in mgraph.v and mgraph2.v, the definition of open
graphs is split into a Record for the computational content and a Class for the
well-formedness predicate [is_graph]. This allows us to separate the definition
of operations on open graphs and the fact that they preserve well-formedness *)

Section OpenGraphs.
Variable (Lv Le : Type).

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

(** ** Open 2p-graphs labeled with elements of a 2pdom algebra *)

Section PttdomGraphTheory.
Variable tm : pttdom.           (* TODO: rename *)
Notation test := (test tm).

Global Instance tm_inh_type : inh_type tm. 
exact: Build_inh_type (1%ptt).
Defined.

Notation pre_graph := (pre_graph test (car (setoid_of_ops (ops tm)))).
Notation graph := (graph (pttdom_labels tm)).
Notation graph2 := (graph2 (pttdom_labels tm)).


(** We define isomorphisms via closing *)

Record oiso2 (G H : pre_graph) := 
  OIso2 { oiso2_graphL : is_graph G;
          oiso2_graphR : is_graph H;
          oiso2_iso : close G ≃2 close H}.
Global Existing Instance oiso2_graphL.
Global Existing Instance oiso2_graphR.

Notation "G ⩭2 H" := (oiso2 G H) (at level 45).

(** tracing vertices through the closing operation *)
Definition close_v (G : pre_graph) (graph_G : is_graph G) (x : VT) : close G :=
  match @idP (x \in vset G) with
  | ReflectT p => Sub x p
  | ReflectF _ => input
  end.

Lemma close_vE (G : pre_graph) (isG : is_graph G) z (Vz : z \in vset G) : 
  @close_v G isG z = Sub z Vz.
Proof.
  rewrite /close_v. case: {-}_ / idP => [p|]; [exact: val_inj|by rewrite Vz].
Qed.

Lemma close_vK (G : pre_graph) (graph_G : is_graph G) (x : VT) : 
  x \in vset G -> fsval (close_v graph_G x) = x.
Proof. move => Vx. by rewrite close_vE. Qed.

Arguments close_v [G graph_G] _. 
Arguments close_v : simpl never.


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

Lemma oiso_of (G H: graph2): G ≃2 H -> open G ⩭2 open H.
Proof.
  intro.
  apply (@OIso2 _ _ (open_is_graph G) (open_is_graph H)).
  etransitivity. symmetry. apply openK.
  etransitivity. eassumption. apply openK.
Qed.

Lemma openKE (G : graph2) (x : G) :
  openK G x = close_v (inj_v x) :> close (open G).
Proof. 
  rewrite /close_v /=. case: {-}_ /idP => [p|np].
  - by apply: val_inj => /=. 
  - by rewrite in_imfsetT in np.
Qed.

Lemma closeK (G : pre_graph) (graph_G : is_graph G) : 
  G ⩭2 open (close G).
Proof. econstructor. exact: openK. Defined.

Lemma close_irrelevance (G : pre_graph) (graph_G graph_G' : is_graph G) : 
  close G graph_G ≃2 close G graph_G'.
Proof.
  iso2 bij_id bij_id xpred0; try exact: val_inj.
  split => // e [|]; exact: val_inj.
Defined.
  
Lemma liso_of_oliso (G H : pre_graph) (graph_G : is_graph G) (graph_H : is_graph H) : 
  G ⩭2 H -> close G ≃2 close H.
Proof. 
  case => graph_G' graph_H' I.
  transitivity (close G graph_G'); first exact: close_irrelevance.
  apply: iso2_comp I _. exact: close_irrelevance.
Qed.

(** [oiso2] is a per on pre_graphs, but it is only reflexive on well-formed graphs *)

Lemma oiso2_trans : CRelationClasses.Transitive oiso2.
Proof. 
  move => F G H [isF isG FG] [isG' isH GH]. econstructor.
  apply: iso2_comp GH. 
  apply: iso2_comp FG _. exact: close_irrelevance.
Defined.

Lemma oiso2_sym : CRelationClasses.Symmetric oiso2.
Proof. move => F G [isF isG /iso2_sym ?]. by econstructor. Qed.

Instance oiso2_Equivalence : CRelationClasses.PER oiso2.
Proof. exact: (CRelationClasses.Build_PER _ oiso2_sym oiso2_trans). Qed.

(** In order to reason about [F ⩭2 G] without dependent types, we need to vast
the bijections underlying the isomorphism of [close F ≃2 close G] to functions
on [VT -> VT] and [ET -> ET] respectively. These functions are bijective only on
vertices and edge of the respective graphs. *)

Definition vfun_body (G H : pre_graph) (graph_G : is_graph G) (graph_H : is_graph H) 
  (h : bij (close G) (close H)) (x : VT) : VT := 
  locked (match @idP (x \in vset G) with
          | ReflectT p => val (h (Sub x p))
          | ReflectF _ => x
          end).

Definition vfun_of (G H : pre_graph) (h : G ⩭2 H) := vfun_body (oiso2_iso h).
Arguments vfun_of [G H] h x.
Coercion vfun_of : oiso2 >-> Funclass.

Definition efun_body (G H : pre_graph) (graph_G : is_graph G) (graph_H : is_graph H) 
  (he : bij (edge (close G)) (edge (close H))) (e : ET) : ET := 
  locked (match @idP (e \in eset G) with
          | ReflectT p => val (he (Sub e p))
          | ReflectF _ => e
          end).

Definition efun_of (G H : pre_graph) (h : G ⩭2 H) := efun_body (oiso2_iso h).e.

Definition edir_body (G : pre_graph) (graph_G : is_graph G)  
  (hd : edge (close G) -> bool) (e : ET) : bool := 
  locked (match @idP (e \in eset G) with
          | ReflectT p => hd (Sub e p)
          | ReflectF _ => false
          end).

Definition edir_of (G H : pre_graph) (h : G ⩭2 H) := edir_body (oiso2_iso h).d.

Arguments vfun_of [G H] h / _.
Arguments efun_of [G H] h e /.
Arguments edir_of [G H] h e /.

Lemma vfun_bodyE (G H : pre_graph) (isG : is_graph G) (isH : is_graph H) x
  (h : bij (close G isG) (close H isH)) (p : x \in vset G) : vfun_body h x = val (h (Sub x p)).
Proof.
  unlock vfun_body. 
  case: {-}_ / idP => [p'|]; by [rewrite (bool_irrelevance p p')| move/(_ p)].
Qed.

Lemma efun_bodyE (G H : pre_graph) (isG : is_graph G) (isH : is_graph H) 
  (he : bij (edge (close G)) (edge (close H))) e (He : e \in eset G) : 
  efun_body he e = val (he (Sub e He)).
Proof. 
  unlock efun_body. case: {-}_ / idP => [p|]; last by rewrite He. 
  by rewrite (bool_irrelevance He p).
Qed.

Lemma edir_bodyE (G : pre_graph) (isG : is_graph G) 
  (hd : (edge (close G)) -> bool) e (He : e \in eset G) : 
  edir_body hd e = hd (Sub e He).
Proof. 
  unlock edir_body. case: {-}_ / idP => [p|]; last by rewrite He. 
  by rewrite (bool_irrelevance He p).
Qed.

Lemma im_efun_of (F G : pre_graph) (i : F ⩭2 G) : {in eset F, forall e, efun_of i e \in eset G}.
Proof. move => e eF. rewrite /= efun_bodyE. exact: valP. Qed.

Lemma efun_of_inj (F G : pre_graph) (i : F ⩭2 G) : {in eset F&, injective (efun_of i)}.
Proof. 
  move => e1 e2 eF1 eF2. rewrite /= !efun_bodyE. 
  move/val_inj. by move/(bij_injective (f := (oiso2_iso i).e)) => [].
Qed.

Lemma efun_of_bij (F G : pre_graph) (i : F ⩭2 G) : 
  exists g, [/\ {in eset F, cancel (efun_of i) g},
          {in eset G, cancel g (efun_of i)} &
          {in eset G, forall x, g x \in eset F}].
Proof.
  case: i => isF isG i /=.
  pose g := efun_body (iso2_sym i).e.
  exists g. split => //; rewrite /efun_of/=. 
  - move => e Fe. rewrite /g !efun_bodyE /=. exact: valP.
    move => p. by rewrite fsvalK bijK.
  - move => e Ge. rewrite /g !efun_bodyE /=. exact: valP.
    move => p. by rewrite fsvalK bijK'.
  - move => e Ge. rewrite /g !efun_bodyE /=. exact: valP.
Qed.

Lemma oiso2_lv (F G : pre_graph) (i : F ⩭2 G) x : 
  x \in vset F -> lv G (i x) ≡ lv F x.
Proof. 
  case: i => isF isG i Ee /=. rewrite vfun_bodyE /=. 
  exact: (vlabel_hom (is_hom := (iso_hom i))). (* this needs a bit of help ? *)
Qed.

Lemma oiso2_le (F G : pre_graph) (i : F ⩭2 G) e : e \in eset F ->
  le G (efun_of i e) ≡[edir_of i e] le F e.
Proof.
  case: i => isF isG i Ee /=. rewrite efun_bodyE edir_bodyE. 
  exact: elabel_hom. (* this doesn't ? *)
Qed.


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
  move => isG isH [EV EE Eep Elv Ele]. econstructor.
  iso2 (bij_cast EV) (bij_cast EE) (fun _ => false).
  - split.
    + move => [e p] b /=. 
      apply: val_inj => /=. by rewrite !bij_castE /= ?Eep. 
    + move => [v p]. by rewrite bij_castE /= Elv.
    + move => [e p]. by rewrite bij_castE /= Ele.
  - rewrite bij_castE. exact: val_inj.
  - rewrite bij_castE. exact: val_inj.
Defined.

Lemma weqG_iso2E (G H : pre_graph) (isG : is_graph G) (isH : is_graph H) (E : G ≡G H) x :
  x \in vset G ->
  @weqG_oliso G H isG isH E x = x.
Proof. 
  move => Vx. rewrite /= vfun_bodyE /=. destruct E.
  rewrite /=. by rewrite bij_castE.
Qed.

(** Experimental: A class of boxed properties to allow inference of "non-class" assumptions *)
Class box (P : Type) : Type := Box { boxed : P }.
Hint Extern 0 (box _) => apply Box; assumption : typeclass_instances.

(** ** Helper functions *)

Section PreGraphOps.
Variables (G : pre_graph).

(** Making [e \in eset G] part of the definition of oarc allows us to mostly avoid
explicitly mentioning this assumption in the step relation. Moreover,
it avoids spurious lemmas such as [oarc G e x u y -> oarc (G \ z) e x u y] *)
Definition oarc e x u y := 
  e \in eset G /\ 
  exists b, [/\ endpt G b e = x, endpt G (~~b) e = y & le G e ≡[b] u].

Definition is_edge e x u y :=
  e \in eset G /\ [/\ endpt G false e = x, endpt G true e = y & le G e ≡ u].

Definition incident x e := [exists b, endpt G b e == x].
Definition edges_at x := [fset e in eset G | incident x e].

End PreGraphOps.

Instance oarc_morphism : Proper (weqG ==> eq ==> eq ==> eqv ==> eq ==> iff) oarc.
Proof.
  move => G H GH ? e ? ? x ? u v uv ? y ?. subst. 
  wlog suff: G H GH u v uv / oarc G e x u y -> oarc H e x v y.
  { move => W. split; apply: W => //; by symmetry. }
  case: GH => [EV EE Eep Elv Ele _ _] [He [b] [A B C]].
  split; first by rewrite -EE. 
  exists b. rewrite -!Eep //. split => //. by rewrite -Ele // -uv.
Qed.

Section PreGraphTheory.
Variables (G : pre_graph).

(** Note that the [incident] predicate does not check whether the edge
is present in the graph. The right way to check whether [e] is an edge
attached to [x] is [e \in edges_at x] *)


Lemma edges_atE e x : e \in edges_at G x = (e \in eset G) && (incident G x e).
Proof. rewrite /edges_at. by rewrite !inE. Qed.

Lemma edges_atF b e x (edge_e : e \in eset G) :  
  e \notin edges_at G x -> (endpt G b e == x = false).
Proof. rewrite !inE /= edge_e /=. apply: contraNF => ?. by existsb b. Qed.

Definition pIO  := [fset p_in G; p_out G].

Lemma pIO_Ni x : x \notin pIO -> p_in G != x.
Proof. apply: contraNneq => <-. by rewrite in_fset2 eqxx. Qed.

Lemma pIO_No x : x \notin pIO -> p_out G != x.
Proof. apply: contraNneq => <-. by rewrite in_fset2 eqxx. Qed.

Lemma is_edge_vsetL {isG : is_graph G} e x y u : is_edge G e x u y -> x \in vset G.
Proof. case => E [<- _ _]. exact: endptP. Qed.

Lemma is_edge_vsetR {isG : is_graph G} e x y u : is_edge G e x u y -> y \in vset G.
Proof. case => E [_ <- _]. exact: endptP. Qed.

Lemma oarc_cnv e x y u : oarc G e x u y <-> oarc G e y u° x. 
Proof. 
  wlog suff W : x u y / oarc G e x u y -> oarc G e y u° x. 
  { split; first exact: W. move/W. by rewrite cnvI. }
  case => E [b] [A B C]. split => //. exists (~~b). rewrite negbK.
  split => //. by rewrite eqvb_neq cnvI.
Qed.

Lemma oarc_edge_atL e x y u : 
  oarc G e x u y -> e \in edges_at G x.
Proof. case => E [b] [A B C]. rewrite !inE E /= /incident. existsb b. exact/eqP. Qed.

Lemma oarc_edge_atR e x y u : 
  oarc G e x u y -> e \in edges_at G y.
Proof. rewrite oarc_cnv. exact: oarc_edge_atL. Qed.

Lemma oarc_cases e x u y : 
  oarc G e x u y -> is_edge G e x u y \/ is_edge G e y u° x.
Proof. by case => E [[|]] [A B C]; [right|left]. Qed.

Lemma oarc_vsetL (isG : is_graph G) e x y u : 
  oarc G e x u y -> x \in vset G.
Proof. case => E [b] [<- _ _]. exact: endptP. Qed.

Lemma oarc_vsetR (isG : is_graph G) e x y u : 
  oarc G e x u y -> y \in vset G.
Proof. case => E [b] [_ <- _]. exact: endptP. Qed.

End PreGraphTheory.
Hint Resolve is_edge_vsetL is_edge_vsetR : vset.
Hint Resolve oarc_vsetL oarc_vsetR : vset.


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

Lemma incident_addv (G : pre_graph) x a : incident (G ∔ [x,a]) =2 incident G.
Proof. done. Qed.

Lemma incident_vset (G : pre_graph) (isG : is_graph G) x e : 
  e \in eset G -> incident G x e -> x \in vset G.
Proof. move => He /existsP[b][/eqP<-]. exact: endptP. Qed.

Lemma edges_at_del (G : pre_graph) (z x : VT) : 
  edges_at (G \ z) x = edges_at G x `\` edges_at G z.
Proof.
  apply/fsetP => k. by rewrite !(edges_atE,inE) !incident_delv !andbA.
Qed.

Lemma edges_at_add_edge (G : pre_graph) x y e u : 
  edges_at (G ∔ [e, x, u, y]) y = e |` edges_at G y.
Proof.
  apply/fsetP => e0. rewrite inE !edges_atE /= !inE. 
  case: (altP (e0 =P e)) => //= [->|e0De].
  - rewrite /incident/=. existsb true. by rewrite !update_eq. 
  - rewrite /incident/=. by rewrite !existsb_case !updateE.
Qed.

Lemma edges_at_add_edgeL (G : pre_graph) x y e u : 
  edges_at (G ∔ [e, x, u, y]) x = e |` edges_at G x.
Proof.
  apply/fsetP => e0. rewrite inE !edges_atE /= !inE. 
  case: (altP (e0 =P e)) => //= [->|e0De].
  - rewrite /incident/=. existsb false. by rewrite !update_eq. 
  - rewrite /incident/=. by rewrite !existsb_case !updateE.
Qed.

Lemma edges_at_add_edge' G e x y z u : 
  e \notin eset G ->
  x != z -> y != z -> edges_at (G ∔ [e,x,u,y]) z = edges_at G z.
Proof.
  move => eGN xDz yDz. apply/fsetP => e0; rewrite !edges_atE /= !inE.
  case: (altP (e0 =P e)) => //= [->|e0De].
  - by rewrite (negbTE eGN) /incident /= existsb_case !updateE (negbTE xDz) (negbTE yDz).
  - by rewrite /incident/= !existsb_case !update_neq.
Qed.

(** this acually relies on [eset G] containing edges incident to [x] *) 
Lemma edges_at_added_vertex (G : pre_graph) (isG : is_graph G) x a : x \notin vset G -> 
  edges_at (G ∔ [x, a]) x = fset0.
Proof. 
  move => Hx. apply/fsetP => e. rewrite inE edges_atE. 
  case Ee : (_ \in _) => //=. rewrite incident_addv. 
  apply: contraNF Hx. exact: incident_vset.
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

(** ** Killing Lemmas *)

Lemma del_vertexK (G : pre_graph) (isG : is_graph G) z : 
  z \in vset G -> 
  (G \ z) ∔ [z,lv G z] ≡G G - edges_at G z.
Proof. split => //= [|x _]; by rewrite ?fsetD1K ?update_fx. Qed.


Lemma del_edgeK (G : pre_graph) (isG : is_graph G) e x y u : 
  is_edge G e x u y -> (G - [fset e]) ∔ [e,x,u,y] ≡G G.
Proof.
  case => E [A B C]. split => //=.
  - by rewrite fsetD1K.
  - move => b. rewrite fsetD1K // => e'. case: (altP (e' =P e)) => [->|?] ?; rewrite updateE //.
    by case: b; rewrite ?A ?B.
  - move => e'. rewrite fsetD1K // => He'. by case: (altP (e' =P e)) => [->|?]; rewrite updateE // C.
Qed. 


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

(* similar to above, symmetry argument? *)
Lemma add_edgeKl (G : pre_graph) e x u y : 
  e \notin eset G -> G ∔ [e,x,u,y] \ x ≡G G \ x.
Proof.
  move => He. split => //=; rewrite edges_at_add_edgeL. 2: move => b.
  all: rewrite fsetUDU ?fdisjoint1X // => f /fsetDP [Hf _]; 
       rewrite update_neq //; by apply: contraNneq He => <-.
Qed.

Lemma add_testK (G : pre_graph) x a : G[adt x <- a] \ x ≡G G \ x.
Proof. split => //= y /fsetD1P [? _]. by rewrite updateE. Qed.

(* TOTHINK: is the [is_graph] assumption really required, or only for [edges_at_added_vertex] *)
Lemma add_vertexK (G : pre_graph) (isG : is_graph G) x a : 
  x \notin vset G -> G ∔ [x, a] \ x ≡G G.
Proof. 
  move => Hx. split => //=.
  - by rewrite fsetU1K.
  - by rewrite edges_at_added_vertex // fsetD0.
  - rewrite fsetU1K // => y Hy. rewrite update_neq //. 
    by apply: contraNneq Hx => <-.
Qed.


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
  iso2 (fresh_bij' bij_id xG) sumxU (fun => false) => //. 2-3: move => *; exact: val_inj.
  split => //.
  + move => [e|[]] b. exact: val_inj.
  + by move => [v|] /=; rewrite updateE // fsval_eqF.
  + by move => [e|[]]. 
Defined.




Lemma inj_v_open (G : graph2) (x : G) : inj_v x \in vset (open G).
Proof. by rewrite in_imfset. Qed.
Hint Resolve inj_v_open.

Lemma inj_v_fresh (G : graph2) (x : G) (z : VT) : z \notin vset (open G) -> inj_v x != z.
Proof. apply: contraNneq => <-. exact: inj_v_open. Qed.

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
    + rewrite close_vK // eqxx /=. by rewrite tst_dotC.
    + suff -> : (fsval v == x = false) by []. 
      apply: contra_neqF D => /eqP<-. by rewrite close_fsval.
Defined.

Section Transfer.
Variable (G : graph2).

(* (* not used? *) *)
(* Lemma edges_at_open (x : G) (E : {set edge G}) :   *)
(*   mgraph.edges_at G x = E -> *)
(*   edges_at (open G) (inj_v x) = [fset inj_e e | e in E]. *)
(* Admitted. *)


(* Lemma fresh_imfsetF (T : finType) (f : T -> ET) (e : T) : *)
(*    f e == fresh [fset f x | x in T] = false. *)
(* Admitted.  *)

(* TOTHINK: could replace [fresh _] with an arbitrary fresh  *)
Definition open_add_vertex a : 
  open (G ∔ a) ⩭2 (open G) ∔ [fresh (vset (open G)), a].
Proof. 
  econstructor.
  apply: iso2_comp (iso2_sym _) _. apply: openK.
  apply: iso2_comp (iso2_sym _). 2: apply: close_add_vertex freshP. 
  apply: add_vertex2_iso => //. exact: openK.
Defined.

Lemma open_add_vertexE : 
  ((forall a, open_add_vertex a (@inj_v (G ∔ a)%G2 (inr tt)) = fresh (vset (open G)))
  *(forall a x, open_add_vertex a (@inj_v (G ∔ a)%G2 (inl x)) = @inj_v G x))%type. 
Proof. 
  split => [a|a x]. 
  - rewrite /vfun_of/= vfun_bodyE. exact: inj_v_open.
    move => H /=. rewrite imfset_bij_bwdE //=. exact: inj_v_inj.
  - rewrite /vfun_of/= vfun_bodyE. exact: inj_v_open.
    move => H /=. rewrite imfset_bij_bwdE //=. exact: inj_v_inj.
Qed.

(* This follows the same pattern as open_add_vertex. Lemma? *)
Lemma open_add_edge (x y : G) u : 
  open (G ∔ [x, u, y]) ⩭2 open G ∔ [inj_v x, u, inj_v y].
Proof. 
  have X : is_graph (add_edge (open G) (inj_v x) u (inj_v y)). 
  { exact: add_edge_graph. }
  econstructor.
  apply: iso2_comp (iso2_sym _) _. apply: openK.
  apply: iso2_comp _ (iso2_sym _). 2: apply close_add_edge.
  apply: (add_edge2_iso'' (h := (openK _))) => //; exact: openKE.
Defined.


Definition open_add_test (x : G) a : 
  open (G[tst x <- a]) ⩭2 (open G)[adt inj_v x <- a].
Proof.
  econstructor.
  apply: iso2_comp (iso2_sym (openK _)) _.
  apply: iso2_comp (close_add_test _ _ _); last exact: inj_v_open.
  apply: iso2_comp. 
    apply: (add_test_cong _ _ eqvxx). apply: openK. 
  by rewrite openKE.
Defined.

End Transfer. 
   
(* TOTHINK: the converse does NOT hold since [h] is the identity on
vertices outside of [G]. This could be made to hold by taking [fresh (vset H)] 
as value outside of [G] *)
Lemma vfun_of_vset (G H : pre_graph) (h : G ⩭2 H) x : x \in vset G -> h x \in vset H.
Proof. case: h => /= isG isH h /= xG. rewrite /vfun_of vfun_bodyE. exact: valP. Qed.

(** * Open Step relation  *)

Section ostep.
Implicit Types (x y z : VT) (e : ET).

(** We turn the first argument into a parameter, this keeps
case/destruct from introducing a new name for G *)
Variant ostep (G : pre_graph) : pre_graph -> Type := 
| ostep_v0 z : z \in vset G ->
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
  | oiso_step:    CRelationClasses.subrelation oiso2 osteps
  | ostep_step:    CRelationClasses.subrelation ostep osteps
  | osteps_trans : CRelationClasses.Transitive osteps.

Lemma oiso_stepL G G' H : G ⩭2 G' -> osteps G' H -> osteps G H.
Proof. move => h A. apply: osteps_trans _ A. exact: oiso_step. Qed.

Lemma ostep_stepL G G' H : ostep G G' -> osteps G' H -> osteps G H.
Proof. move => A. apply: osteps_trans. exact: ostep_step. Qed.


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




Lemma oarc_del_vertex (G : pre_graph) z e x y u : 
  e \notin edges_at G z -> oarc G e x u y -> oarc (G \ z) e x u y.
Proof. move => Iz [edge_e H]. apply: conj H. by rewrite inE Iz. Qed.





Lemma edges_at_test (G : pre_graph) x a z : edges_at G[adt x <- a] z = edges_at G z. done. Qed.



Lemma edges_at_del_edges (G : pre_graph) z E : 
  edges_at (del_edges G E) z = edges_at G z `\` E. 
Proof.
  apply/fsetP => e. by rewrite !(inE,edges_atE) -andbA incident_dele.
Qed.

Lemma lv_add_edge (G : pre_graph) e x u y z : lv (G ∔ [e,x,u,y]) z = lv G z. done. Qed.

Definition step_order G H (s: ostep G H): nat :=
  match s with
  | ostep_v0 _ _ _ _ => 0
  | ostep_v1 _ _ _ _ _ _ _ _ => 1
  | ostep_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 2
  | ostep_e0 _ _ _ _ => 3
  | ostep_e2 _ _ _ _ _ _ _ _ _ => 4
  end.

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

Lemma eqb_negR (b1 b2 : bool) : (b1 == ~~ b2) = (b1 != b2).
Proof. by case: b1; case: b2. Qed.

Lemma eqv_addb b (X : pttdom) (u v : X) : u ≡[b (+) b] v -> u ≡ v.
Proof. by rewrite addbxx. Qed.
Arguments eqv_addb b [X] u v _.

Lemma eqv_addbN b (X : pttdom) (u v : X) : u ≡[b (+) ~~ b] v -> u ≡ v°.
Proof. by rewrite addbN addbxx. Qed.
Arguments eqv_addbN b [X] u v _.

Lemma oarc_weq (G : pre_graph) e x y u u' : 
  x != y -> oarc G e x u y -> oarc G e x u' y -> u ≡ u'.
Proof. 
  move => xDy [[E] [b] [A B C]] [[_] [b'] [A' B' C']].
  have ? : b' = b. 
  { apply: contra_neq_eq xDy. rewrite -eqb_negR => /eqbP ?; subst.
    by symmetry. }
  subst b'. change (u ≡[false] u'). rewrite -(addbxx b). 
  apply: eqvb_trans. symmetry. exact: C. done.
Qed.

Lemma oarc_loop G e x y x' u u' : oarc G e x u y -> oarc G e x' u' x' -> x = y.
Proof. case => Ee [[|]] [? ? ?]; case => _ [[|]] [? ? ?]; by subst. Qed.

Lemma same_oarc G e x y x' y' u u' : oarc G e x u y -> oarc G e x' u' y' ->
  [/\ x = x', y = y' & u ≡ u'] \/ [/\ x = y', y = x' & u ≡ u'°].
Proof.
  case => Ee [b] [A B C]. case => _ [b'] [A' B' C']. 
  case: (altP (b =P b')) => [Eb|]. 
  - subst. left. split => //. apply: (eqv_addb b'). apply: eqvb_trans C'. by symmetry.
  - rewrite -eqb_negR => /eqP ?; subst. right; split => //. by rewrite negbK.
    apply: (eqv_addbN b'). rewrite addbC. apply: eqvb_trans C'. by symmetry.
Qed.

Lemma osteps_refl (G : pre_graph) (isG : is_graph G) : osteps G G.
Proof. apply: oiso_step. econstructor. exact: iso2_id. Qed.

Ltac e2split := do 2 eexists; split; [split|].

(* Lemma iso2_edge_flip (G : graph2) (x y : G) u : G ∔ [x,u,y] ≃2 G ∔ [y,u°,x]. *)
(* Proof. apply add_edge2_rev. by apply Eqv'_sym. Defined. *)

(* We prove this directly rather than going though [add_edge2_rev],
because this way we can avoid the assumption [e \notin eset G] *)
Lemma add_edge_flip (G : pre_graph) (isG : is_graph G) e x y u v: 
  u° ≡ v ->
  x \in vset G -> y \in vset G -> G ∔ [e,x,u,y] ⩭2 G ∔ [e,y,v,x].
Proof.
  move => E xG yG. 
  have isG1 : is_graph (G ∔ [e,x,u,y]) by apply: add_edge_graph'.
  have isG2 : is_graph (G ∔ [e,y,v,x]) by apply: add_edge_graph'.
  econstructor.
  pose dir (e0 : edge (close (G ∔ [e,x,u,y]) isG1)) := val e0 == e.
  iso2 bij_id bij_id dir => //=. 2-3: exact: val_inj.
  split => //.
  - case => e' He' b /=. apply: val_inj => /=. case: (fset1UE He') => [?|].
    + subst e'. by rewrite /dir/=!eqxx addTb !updateE if_neg. 
    + case => A ?. by rewrite /dir/= (negbTE A) !updateE.
  - case => e' He'. rewrite /dir/=. case: (fset1UE He') => [?|].
    + subst e'. rewrite eqxx !updateE. by symmetry in E.
    + case => A ?. by rewrite /dir/= (negbTE A) !updateE.
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


Lemma close_same_step (Gl Gr : pre_graph) (isGl : is_graph Gl) (isGr : is_graph Gr) : 
  Gl ≡G Gr -> exists Gl' Gr' : pre_graph, (osteps Gl Gl' /\ osteps Gr Gr') /\ (Gl' ≡G Gr').
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

(* should have proved this earlier ... *)
Lemma edges_atP G e z : reflect (e \in eset G /\ exists b, endpt G b e = z) (e \in edges_at G z).
Proof.
  rewrite edges_atE /incident. apply: (iffP andP); intuition. 
  - case/existsP : H1 => b /eqP<-. by exists b.
  -case: H1 => b <-. apply/existsP. by exists b.
Qed.
                                     
Lemma edges_at_oarc G e x y z u : 
  e \in edges_at G z -> oarc G e x u y -> x = z \/ y = z.
Proof.
  move => Iz [Ee [b] [<- <- _]]. case/edges_atP : Iz => _ [[|]]; case: b; tauto. 
Qed.

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

Lemma fset01 (T : choiceType) (x : T) : [fset x] != fset0.
Proof. by rewrite -[[fset x]]fsetU0 fset1U0. Qed.

Lemma local_confluence_aux (G : pre_graph) (isG : is_graph G) Gl Gr : 
  ostep G Gl -> ostep G Gr -> exists Gl' Gr', (osteps Gl Gl' /\ osteps Gr Gr') /\ (Gl' ≡G Gr'). 
Proof with eauto with typeclass_instances.
  move => S1 S2.
  wlog : Gl Gr S1 S2 / step_order S1 <= step_order S2.
  { move => W. case/orb_sum: (leq_total (step_order S1) (step_order S2)) => SS.
    - exact: W SS.
    - case: (W _ _ _ _ SS) => H' [G'] [[stpG stpH] E]. 
      do 2 eexists; split; first split. 1-2:eassumption. by symmetry. }
  (* naming convention: primes on the second/right rule *)
  destruct S1 as [z Vz Iz zIO|
                  x  z  e  u  Iz  zIO  arc_e  xDz |
                  x y z e1 e2 u v Iz e1De2 zIO xDz yDz arc_e1 arc_e2|
                  x e u arc_e |
                  x y e1 e2 u v e1De2 arc_e1 arc_e2];
  destruct S2 as [z' Vz' Iz' zIO'|
                  x' z' e' u' Iz' zIO' arc_e' xDz'|
                  x' y' z' e1' e2' u' v' Iz' e1De2' zIO' xDz' yDz' arc_e1' arc_e2'|
                  x' e' u' arc_e' |
                  x' y' e1' e2' u' v' e1De2' arc_e1' arc_e2'];
  rewrite //=; move => CASE_TAG.
  - (* V0 / V0 *)
    case: (altP (z =P z')) => [?|D].
    + subst z'. do 2 exists ((G \ z)%O). split => //. split => //; exact: osteps_refl.
    + exists (G \ z \ z')%O. exists (G \ z' \ z)%O. rewrite {2}del_vertexC. split => //.
      split; apply ostep_step,ostep_v0 => //=. 
      2,4: by rewrite edges_at_del Iz Iz' fsetD0.
      all: by rewrite !inE ?D 1?eq_sym ?D.
  - (* V0 / V1 *) 
    have D : z != z'. { apply: contra_eq_neq Iz => ->. by rewrite Iz' fset01. }
    e2split.
    + eapply ostep_step,ostep_v1. 3: eapply oarc_del_vertex,arc_e'. all: try done.
      * by rewrite edges_at_del Iz Iz' fsetD0.
      * by rewrite Iz inE.
    + eapply ostep_step,(ostep_v0 (z := z)). 3:done.
      * by rewrite !inE D /=.
      * by rewrite edges_at_del edges_at_test Iz fset0D.
    + by rewrite del_vertexC del_vertex_add_test.
  - (* V0 / V2 *) 
    have D : z != z'. { apply: contra_eq_neq Iz' => <-. by rewrite Iz eq_sym fset1U0. }
    have [? ?] : x' != z /\ y' != z. 
    { split. 
      - apply: contra_eq_neq Iz => <-. apply/fset0Pn; exists e1'. exact: oarc_edge_atL arc_e1'.
      - apply: contra_eq_neq Iz => <-. apply/fset0Pn; exists e2'. exact: oarc_edge_atR arc_e2'. }
    e2split.
    + eapply ostep_step,ostep_v2. 
      6-7: apply: oarc_del_vertex. 7: apply arc_e1'. 8: apply: arc_e2'.
      all: try done.
      all: by rewrite ?edges_at_del ?Iz ?Iz' ?fsetD0 ?inE.
    + eapply ostep_step,(ostep_v0 (z := z)). 3:done.
        by rewrite !inE D.
      rewrite @edges_at_add_edge' //=. 
      * by rewrite edges_at_del Iz fset0D.
      * by rewrite Iz' maxn_fsetD.
    + by rewrite -del_vertex_add_edge 1?eq_sym 1?del_vertexC //= Iz' maxn_fsetD.
  - (* V0 / E0 *) 
    have zDx : z != x'. 
    { apply: contra_eq_neq Iz => ->. apply/fset0Pn. exists e'. exact: oarc_edge_atL arc_e'. }
    e2split.
    + eapply ostep_step,ostep_e0. apply: oarc_del_vertex arc_e'. by rewrite Iz inE.
    + eapply ostep_step,(@ostep_v0 _ z) => //.
      by rewrite edges_at_test edges_at_del_edges Iz fset0D.
    + by rewrite /= -del_vertex_add_test -del_vertex_edges.
  - (* V0 / E2 *) 
    have[zDx zDy] : z != x' /\ z != y'. 
    { split;apply: contra_eq_neq Iz => ->;apply/fset0Pn;exists e1'. 
      exact: oarc_edge_atL arc_e1'. exact: oarc_edge_atR arc_e1'. }
    e2split.
    + eapply ostep_step,ostep_e2. exact: e1De2'.
      all: apply oarc_del_vertex; eauto. all: by rewrite Iz inE.
    + eapply ostep_step,(@ostep_v0 _ z) => //.
      rewrite edges_at_add_edge' 1?eq_sym ?maxn_fsetD //. 
      by rewrite edges_at_del_edges Iz fset0D.
    + by rewrite del_vertex_edges del_vertex_add_edge ?maxn_fsetD.
  - (* V1 / V1 *) 
    case: (altP (z =P z')) => [E|D]; last case: (altP (e =P e')) => [E|E].
    + (* same instance *)
      subst z'. 
      have ? : e' = e by apply: oarc_uniqeR arc_e'. subst e'.
      have ? : x = x' by apply: oarc_injL arc_e arc_e'. subst x'.
      apply: close_same_step. 
      suff -> : [dom (u·lv G z)] ≡ [dom (u'·lv G z)] by [].
      by rewrite infer_testE (oarc_weq _ arc_e arc_e').
    + (* isolated [z --e-- z'] pseudo-case *) subst e'.
      case: (same_oarc arc_e arc_e') => [[? ? U]|[? ? U]]; subst z' x'; first by rewrite eqxx in D.
      e2split.
      * eapply ostep_step, (@ostep_v0 _ x) => //.
        rewrite !inE eq_sym D. exact: oarc_vsetL arc_e.
        by rewrite edges_at_del !edges_at_test Iz Iz' fsetDv.
      * eapply ostep_step, (@ostep_v0 _ z) => //. 
        rewrite !inE D. exact: oarc_vsetR arc_e.
        by rewrite edges_at_del !edges_at_test Iz Iz' fsetDv.
      * by rewrite del_vertexC [in X in _ ≡G X]del_vertexC !add_testK del_vertexC.
     + (* two independen pendants *)
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
        apply: oiso_stepL S2. rewrite maxnC. apply: add_edge_flip; eauto with vset.
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
    (* the {e1,e2} = {e1',e2'} case is actually two cases that share the same wlog reasoing *)
    + wlog [? ?] : x' y' e1' e2' u' v' e1De2' Iz' arc_e1' arc_e2' xDz' yDz' {E} / e1 = e1' /\ e2 = e2'.
        { move => W.
          case: (fset2_inv e1De2 E) => [[? ?]|[? ?]]; first exact: W.
          move/(_ y' x' e2' e1' v'° u'°) in W. rewrite fsetUC eq_sym in W. 
          case: W => //. 1-2: by rewrite <- oarc_cnv. 
          move => Gl [Gr] [[S1 S2] E']. e2split;[exact: S1| |exact: E']. 
          (* TODO: this is exactly the same as in the first wlog argument -> lemma *)
          apply: oiso_stepL S2. rewrite maxnC. apply: add_edge_flip; eauto with vset.
          by rewrite !cnvdot cnvtst dotA. }
        subst e1' e2'.
        case: (altP (z =P z')) => [?|D].
        { (* same instance up to direction *)
          subst z'.
          eapply close_same_step. 1-2: apply add_edge_graph'; eauto with vset typeclass_instances.
          move: (oarc_injL arc_e1 arc_e1') (oarc_injR arc_e2 arc_e2') => ? ?. subst x' y'.
          by rewrite (oarc_weq _ arc_e1' arc_e1) ?(oarc_weq _ arc_e2' arc_e2) // eq_sym. }
        { (* z =e1/e2= z' -- pseudo case *)
          (* there is only z and and z' ... *)
          case: (same_oarc arc_e1 arc_e1') => [[? ? U]|[? ? U]]; first by subst;rewrite eqxx in D.
          subst x x'.
          case: (same_oarc arc_e2 arc_e2') => [[? ? U']|[? ? U']]; first by subst;rewrite eqxx in D.
          subst y y'.
          e2split.
          * apply: ostep_stepL. apply: ostep_e0. apply: oarc_added_edge.
            apply: ostep_step. apply: (@ostep_v0 _ z'). all: try done.
              rewrite /= in_fsetD inE eq_sym D. exact: oarc_vsetL arc_e1.
            rewrite /= edges_at_test edges_at_del_edges edges_at_add_edge. 
            rewrite edges_at_del. (* OK *) admit.
          * apply: ostep_stepL. apply: ostep_e0. apply: oarc_added_edge.
            apply: ostep_step. apply: (@ostep_v0 _ z). all: try done.
              rewrite /= in_fsetD inE D. exact: oarc_vsetR arc_e1.
            rewrite /= edges_at_test edges_at_del_edges edges_at_add_edge. 
            rewrite edges_at_del. (* OK *) admit.
          * rewrite !add_testK !add_edge_del_edgesK. 2-3: by rewrite in_fset1.
            by rewrite -!del_vertex_edges del_vertexC. }
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
         apply: oiso_stepL S1. rewrite maxnC. apply: add_edge_flip; eauto with vset.
         by rewrite !cnvdot cnvtst dotA. }
       wlog ? : e1' e2' x' y' u' v'  arc_e1' arc_e2' Iz' e1De2' xDz' yDz' He / e2 = e1' ; [move => W|subst e1'].
       { have: e2 \in [fset e1';e2']. { move/fsetP : He => /(_ e2). rewrite in_fset1 eqxx. by case/fsetIP. }
         rewrite inE. case/orb_sum => /fset1P => E; first exact: W.
         rewrite -> oarc_cnv in arc_e1',arc_e2'. 
         move/(_ _ _ _ _ _ _ arc_e2' arc_e1') in W. rewrite fsetUC eq_sym in W.
         case: W => // Gl [Gr] [[S1 S2] WG]. exists Gl. exists Gr. do 2 (split => //). 
         apply: oiso_stepL S2. rewrite maxnC. apply: add_edge_flip; eauto with vset.
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
        apply: oiso_stepL Sr. rewrite fsetUC maxnC. apply: add_edge_flip; eauto with vset.
        by rewrite cnvpar parC. }
      subst y'. 
      wlog ? : e1 e2 u v x y e1De2 arc_e1 arc_e2 xDz yDz Iz / e1' = e1.
      { move => W. move:(oarc_edge_atR arc_e1'). 
        rewrite Iz in_fset2. case/orb_sum => /eqP ? ; first exact: W.
        subst e1'. rewrite -> oarc_cnv in arc_e2, arc_e1. 
        case: (W _ _ _ _ _ _ _ arc_e2 arc_e1); rewrite // 1?eq_sym 1?fsetUC //.
        move => Gl [Gr] [[Sl Sr] E]. e2split; [ | exact: Sr|exact: E].
        apply: oiso_stepL Sl. rewrite maxnC. apply: add_edge_flip; eauto with vset.
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
        rewrite fsetUC maxnC. apply: oiso_stepL Sr. eapply weqG_oliso.
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
        e2split; [exact: Sl| |exact: EG]. apply: oiso_stepL Sr. 
        apply weqG_oliso. 1-2: apply: add_edge_graph'; eauto with vset.
        by rewrite parC. }
      subst e1' e2'. 
      wlog [? ? Hu] : x' y' u' v' {arc_e1'} arc_e2' / [/\ x = x', y = y' & u ≡ u'].
      { move => W. 
        case: (same_oarc arc_e1 arc_e1') => [|[? ? Hu]]; first exact: W.
        subst x' y'. rewrite -> oarc_cnv in arc_e2'. case: (W _ _ u'° _ arc_e2') => //.
        move => Gl [Gr] [[Sl Sr] EG]. 
        e2split; [exact: Sl| |exact: EG]. apply: oiso_stepL Sr. 
        apply: add_edge_flip; eauto with vset. by rewrite cnvpar. }
      subst x' y'. 
      (* There are actually two cases here *)
      have [Hv|[? Hv]]: ((v ≡ v') \/ (x = y /\ v ≡ v'°)).
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
        apply: oiso_stepL S1. rewrite maxnC. apply: add_edge_flip; eauto with vset.
        by rewrite !cnvpar parC. }
      wlog ? : e1' e2' x' y' u' v'  arc_e1' arc_e2' e1De2' He / e2 = e1' ; [move => W|subst e1'].
      { have: e2 \in [fset e1';e2']. { move/fsetP : He => /(_ e2). rewrite in_fset1 eqxx. by case/fsetIP. }
        rewrite inE. case/orb_sum => /fset1P => E; first exact: W.
        rewrite -> oarc_cnv in arc_e1',arc_e2'. 
        move/(_ _ _ _ _ _ _ arc_e2' arc_e1') in W. rewrite eq_sym [[fset e2';_]]fsetUC in W.
        case: W => // Gl [Gr] [[S1 S2] WG]. exists Gl. exists Gr. do 2 (split => //). 
        apply: oiso_stepL S2. rewrite maxnC fsetUC. apply: add_edge_flip; eauto with vset.
        by rewrite !cnvpar parC. }
      have {He} E1 : e1 != e2'.
      { apply: contraNneq e1De2 => E. by rewrite -in_fset1 -He !inE E !eqxx. }
      (* until here, the reasoning is essentially the same as in the V2/V2 assoc. case *)
      wlog [? ? Hu] : x' y' u' v' {arc_e1'} arc_e2' / [/\ x' = x, y' = y & u' ≡ v].
      { move => W. case: (same_oarc arc_e1' arc_e2) => [|[? ? E]]; first exact: W.
        rewrite -> oarc_cnv in arc_e2'. subst x' y'.  
        case: (W _ _ u'° _ arc_e2'). split => //. by rewrite E cnvI.
        move => Gl [Gr] [[Sl Sr] EG]. e2split; [exact: Sl| |exact: EG].
        apply: oiso_stepL Sr. rewrite maxnC fsetUC. apply: add_edge_flip; eauto with vset.
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

Hint Resolve oarc_vsetL oarc_vsetR : vset.

Lemma ostep_graph (F G : pre_graph) (isG : is_graph F) : ostep F G -> is_graph G.
Proof with eauto with typeclass_instances.
  case => {G}...
  - move => x y z e1 e2 u v Iz D IOz xDz yDz arc_e1 arc_e2.
    apply: add_edge_graph'; rewrite /= in_fsetD1 ?xDz ?yDz /=.
    exact: oarc_vsetL arc_e1. exact: oarc_vsetR arc_e2.
  - move => x y e1 e2 u v e1De2 arc_e1 arc_e2. 
    apply: add_edge_graph'. exact: oarc_vsetL arc_e1. exact: oarc_vsetR arc_e2.
Qed.

Lemma osteps_graph (F G : pre_graph) (isG : is_graph F) : osteps F G -> is_graph G.
Proof.
  move => S. elim: S isG => {F G}. 
  - move => F G FG _. apply: oiso2_graphR FG.
  - move => F G FG isF. apply: ostep_graph FG.
  - move => F G H. tauto.
Qed.

Proposition local_confluence (F G1 G2 : pre_graph) (isF : is_graph F) : 
  ostep F G1 -> ostep F G2 -> exists H, osteps G1 H /\ osteps G2 H.
Proof.
  move => S1 S2.
  move: (local_confluence_aux isF S1 S2) => [H1] [H2] [[S1' S2'] I].
  exists H2. split => //. apply: osteps_trans (S1') _. apply: oiso_step. 
  suff [isH1 isH2] : is_graph H1 /\ is_graph H2 by apply: weqG_oliso I.
  split. 
  - unshelve eapply (osteps_graph _ S1'). apply: ostep_graph S1.
  - unshelve eapply (osteps_graph _ S2'). apply: ostep_graph S2.
Qed.


(* note: the converse does not hold, due to the totalization of i *)
Lemma iso2_vset (F G : pre_graph) (i : F ⩭2 G) x : 
  x \in vset F -> i x \in vset G.
Proof. case: i => i isF isG Vx /=. by rewrite vfun_bodyE /= fsvalP. Qed.

Lemma oiso2_input (F G : pre_graph) (i : F ⩭2 G) : i (p_in F) = p_in G.
Proof. 
  case: i => isF isG i /=. rewrite vfun_bodyE => [|p]. exact: p_inP.
  rewrite [Sub _ _](_ : _ = @input _ (close F)) ?iso2_input //. exact: val_inj. 
Qed.

Lemma oiso2_output (F G : pre_graph) (i : F ⩭2 G) : i (p_out F) = p_out G.
Proof. 
  case: i => isF isG i /=. rewrite vfun_bodyE => [|p]. exact: p_outP.
  rewrite [Sub _ _](_ : _ = @output _ (close F)) ?iso2_output //. exact: val_inj. 
Qed.

Lemma vfun_of_inj (F G : pre_graph) (i : F ⩭2 G) : {in vset F &, injective i}.
Proof.
  case: i => isF isG i. move => x y Vx Vy /=. rewrite !vfun_bodyE. 
  move/val_inj => H. move: (bij_injective H). by case. 
Qed.

Lemma oiso2_pIO (F G : pre_graph) (i : F ⩭2 G) z : z \in vset F -> 
  (z \in pIO F) = (i z \in pIO G).
Proof with  eauto with typeclass_instances.
  move => Vz. apply/idP/idP.
  - rewrite !inE. case/orP => /eqP ->; by rewrite ?oiso2_input ?oiso2_output eqxx.
  - rewrite !inE. case/orP => /eqP. 
    + rewrite -(oiso2_input i). move/vfun_of_inj => -> //; first by rewrite eqxx.
      eapply p_inP...
    + rewrite -(oiso2_output i). move/vfun_of_inj => -> //; first by rewrite eqxx.
      eapply p_outP...
Qed.

Lemma oiso2_pIO_vfun (F G : pre_graph) (isF : is_graph F) (isG : is_graph G) 
  (i : close F ≃2 close G) z (Vz : z \in vset F) : 
  z \in pIO F = (val (i (Sub z Vz)) \in pIO G).
Proof. by rewrite (oiso2_pIO (OIso2 i)) //= vfun_bodyE. Qed. 


Lemma close_v_IO (F : pre_graph) (isF : is_graph F) z (Hz : z \notin pIO F) : 
  z \in vset F -> @close_v F isF z \notin IO.
Proof. move => Vz. apply: contraNN Hz. by rewrite close_vE !inE. Qed.

(* Lemma close_del_vertex (F : pre_graph) (isF : is_graph F) z (isF' : is_graph (F \ z)) (Hz : z \notin pIO F) :  *)
(*   close (F \ z) ≃2 @del_vertex2 tm (close F) (close_v z) (close_v_IO isF Hz). *)
(* Proof. *)
(*   (* rewrite /close/close'/del_vertex2/mgraph.del_vertex/subgraph_for/sub_vertex/=. rewrite/sub_edge/=. *) *)
(*   (* symmetry. *) *)
(* Admitted. *)


Lemma Sub_endpt (G : pre_graph) (isG : is_graph G) (e : ET) (He : e \in eset G) b (p : endpt G b e \in vset G) :
  Sub (endpt G b e) p = @endpoint _ (close G) b (Sub e He).
Proof. exact: val_inj. Qed.

Lemma oiso2_endpoint (F G : pre_graph) (i : F ⩭2 G) (e : ET) b :
  e \in eset F -> endpt G b (efun_of i e) = i (endpt F (edir_of i e (+) b) e).
Proof.
  case: i => isF isG i Ee /=. 
  rewrite edir_bodyE efun_bodyE vfun_bodyE ?endptP // => p.
  by rewrite Sub_endpt -endpoint_hom /=.
Qed.

Lemma oiso2_incident (F G : pre_graph) (i : F ⩭2 G) (x : VT) (e : ET) :
  x \in vset F -> e \in eset F ->
  incident F x e = incident G (i x) (efun_of i e).
Proof.
  move => Vx Ee. rewrite /incident. apply/existsP/existsP. 
  - move => [b] e_x. exists (edir_of i e (+) b). rewrite oiso2_endpoint //.
    by rewrite addbA addbxx [addb _ _]/= (eqP e_x).
  - move => [b] e_ix. exists (edir_of i e (+) b).
    rewrite oiso2_endpoint // in e_ix. move/eqP : e_ix. move/vfun_of_inj => -> //.
    rewrite -> endptP => //. exact: oiso2_graphL i.
Qed.



Lemma oiso2_edges_at  (F G : pre_graph) (i : F ⩭2 G) z : z \in vset F ->
  edges_at G (i z) = [fset (efun_of i) x | x in edges_at F z].
Proof.
  case: (efun_of_bij i) => ie_inv [I1 I2 I3] ?.
  rewrite /edges_at imfset_sep. apply/fsetP => e'. rewrite in_fsep.
  apply/andP/imfsetP => [[Ee' Ie']|[/= e2 He2 ->]]. 
  - exists (ie_inv e'); rewrite ?I2 // inE I3 //. 
    by rewrite -[e']I2 // -oiso2_incident // I3 in Ie'.
  - rewrite !inE in He2. case/andP : He2 => A B. split; first exact: im_efun_of. 
    by rewrite -oiso2_incident.
Qed.

Lemma oiso2_oarc (F G : pre_graph) (i : F ⩭2 G) e x y u : 
  oarc F e x u y -> oarc G (efun_of i e) (i x) u (i y).
Proof.
  case => Ee [b] [A B C]. split; first exact: im_efun_of.
  exists (edir_of i e (+) b). 
  rewrite !oiso2_endpoint // -addbN !addbA !addbxx !addFb A B. split => //.
  exact: eqvb_trans (oiso2_le _ _ ) _.
Qed.

Lemma oiso2_add_test (F G : pre_graph) (i : F ⩭2 G) x a b :
  x \in vset F ->
  a ≡ b -> F[adt x <- a] ⩭2 G[adt i x <- b].
Proof.
  case: i => isF isG i Vx ab. (* rewrite {}E /=. *)
  econstructor. 
  apply: iso2_comp (iso2_sym _) _. by apply: close_add_test.
  apply: iso2_comp. 2: apply: close_add_test. 2: exact: (iso2_vset (OIso2 i)).
  apply add_vlabel2_iso'' with i. 2:exact: ab.
  abstract (by rewrite /= vfun_bodyE /= close_fsval close_vE).
Defined.

Lemma oiso2_add_testE (F G : pre_graph) (i : F ⩭2 G) x a b Vx ab z : 
  z \in vset F ->
  @oiso2_add_test F G i x a b Vx ab z = i z.
Proof.
  move => Vz. rewrite /= !vfun_bodyE //=. rewrite /oiso2_add_test/=.
  case: i => isF isG i /=. by rewrite vfun_bodyE. 
Qed.

Arguments del_vertex2 [L] G z _.


 
(* TOTHINK: this is the only place where close_del_vertex is used far. It might
be easiert to treat del_vertex without going to the mgraph2 pendant *)
Lemma oiso2_del_vertex (F G : pre_graph) (z : VT) (j : F ⩭2 G) : 
  z \in vset F ->
  z \notin pIO F -> F \ z ⩭2 G \ j z.
Proof.
  (* move => Vz IOz. *)
  move: j => [isF isG i] Vz IOz /=.
  (* have [isF isG] : is_graph F /\ is_graph G; eauto with typeclass_instances. *)
  unshelve econstructor. 
  { apply del_vertex_graph => //; constructor. rewrite (oiso2_pIO (OIso2 i)) // in IOz. }
  have E1 : [fset vfun_body i z] = [fset val (i x) | x : vset F & val x \in [fset z]]. (* : / in?? *)
  { apply/fsetP => k. rewrite inE vfun_bodyE. apply/eqP/imfsetP => /= [->|[x] /= ].
    - exists (Sub z Vz) => //. by rewrite !inE.
    - rewrite !inE => /eqP X ->. move: Vz. rewrite -X => Vz. by rewrite fsvalK. }
  have E2 : edges_at G (vfun_body i z) = [fset val (i.e x) | x : eset F & val x \in edges_at F z].
  { rewrite (@oiso2_edges_at _ _ (OIso2 i)) //=. apply/fsetP => k. apply/imfsetP/imfsetP.
    - case => /= x Ix ->. 
      have Hx : x \in eset F. move: Ix. rewrite edges_atE. by case: (_ \in _).
      exists (Sub x Hx) => //. by rewrite efun_bodyE. 
    - case => /= x. rewrite inE => Hx ->. exists (fsval x) => //. by rewrite efun_bodyE fsvalK. }
  - have P e (p : e \in eset (F \ z)) : val (i.e (Sub e (fsetDl p))) \in eset G `\` edges_at G (vfun_body i z).
    { rewrite inE [_ \in eset G]valP andbT E2. apply: contraTN (p).
      case/imfsetP => /= e0. rewrite inE => A. move/val_inj. move/(@bij_injective _ _ i.e) => ?; subst.
      by rewrite inE A. }
    have Q v (p : v \in vset (F \ z)) : val (i (Sub v (fsetDl p))) \in vset G `\ vfun_body i z.
    { rewrite inE [_ \in vset G]valP andbT E1. apply: contraTN (p).
      case/imfsetP => /= v0. rewrite inE => A. move/val_inj. move/(@bij_injective _ _ i) => ?; subst.
      by rewrite inE A. }
    iso2 (fsetD_bij (f := i) E1) (fsetD_bij (f := i.e) E2) (fun k => i.d (Sub (val k) (fsetDl (valP k)))). 
    + split. 
      * case => e p b. rewrite fsetD_bijE. apply: P.
        move => q. 
        rewrite /=. apply/val_inj => /=. move: (fsetDl _) => He. move: (fsetDl _) => He'. move: (fsetDl _) => Hv.
        rewrite [fsval _](_ : _ = (efun_of (OIso2 i) e)) ?(@oiso2_endpoint _ _ (OIso2 i)) //=.
        rewrite vfun_bodyE; first exact: endptP. rewrite edir_bodyE => Hv'. by rewrite (bool_irrelevance Hv Hv').
        by rewrite efun_bodyE (bool_irrelevance He He').
      * case => v p. case/fsetD1P : (p) => p1 p2. rewrite fsetD_bijE. apply: Q.
        move => q. rewrite ![vlabel _]/=. rewrite -(oiso2_lv (OIso2 i)) //= vfun_bodyE. 
        by rewrite (bool_irrelevance (fsetDl p) p2).
      * case => e p. case/fsetDP : (p) => p1 p2. rewrite fsetD_bijE. apply: P.
        move => q. rewrite ![elabel _]/=. rewrite [i.d _]/=. 
        move: (oiso2_le (OIso2 i) p1) => H. apply: eqvb_transR H => //=. 
        rewrite edir_bodyE efun_bodyE. rewrite (bool_irrelevance (fsetDl p) p1). 
        rewrite (bool_irrelevance (fsetDl (valP [` p])) p1) addbxx. done.
    + rewrite fsetD_bijE. apply: Q.
      move => q. apply/val_inj => /=. rewrite -(oiso2_input (OIso2 i)) /= vfun_bodyE. apply: p_inP. 
      move => r. set X := fsetDl _. by rewrite (bool_irrelevance X r).
    + rewrite fsetD_bijE. apply: Q.
      move => q. apply/val_inj => /=. rewrite -(oiso2_output (OIso2 i)) /= vfun_bodyE. apply: p_outP. 
      move => r. set X := fsetDl _. by rewrite (bool_irrelevance X r).
Defined.

(*   move: j => [isF isG i] Vz IOz /=.  *)
(*   have IOiz : vfun_body i z \notin pIO G by abstract (by rewrite vfun_bodyE -oiso2_pIO_vfun). *)
(*   have isG' : is_graph (G \ vfun_body i z) by apply: del_vertex_graph. *)
(*   econstructor. *)
(*   apply: iso2_comp. apply: close_del_vertex. assumption. *)
(*   apply: iso2_comp (iso2_sym _). 2: apply: close_del_vertex. 2:assumption. *)
(*   apply del_vertex2_iso' with i. *)
(*   abstract (by rewrite /vfun_of vfun_bodyE /= close_fsval close_vE). *)
(* Defined. *)

Lemma oiso2_del_vertexE (F G : pre_graph) (z : VT) (j : F ⩭2 G) A B x : 
  x \in vset (F \ z) -> @oiso2_del_vertex F G z j A B x = j x.
Proof.
  case: j => isF isG j Vx. rewrite /= !vfun_bodyE fsetD_bijE.
  - rewrite !inE [_ \in vset G]valP andbT. rewrite vfun_bodyE val_eqE bij_eqLR bijK.
    by case/fsetD1P : (Vx).
  - move => p. by rewrite /= (vfun_bodyE _ (fsetDl Vx)). 
Qed.

(** Variant of the above with a linear pattern in the conclusion *)
Lemma oiso2_del_vertex_ (F G : pre_graph) (z z' : VT) (j : F ⩭2 G) : 
  z \in vset F -> z \notin pIO F -> z' = j z ->
  F \ z ⩭2 G \ z'.
Proof. move => ? ? ->. exact: oiso2_del_vertex. Qed.

Lemma oiso2_add_edge (F G : pre_graph) (i : F ⩭2 G) e1 e2 x y u v : 
  e1 \notin eset F -> e2 \notin eset G -> x \in vset F -> y \in vset F -> u ≡ v ->
  F ∔ [e1,x,u,y] ⩭2 G ∔ [e2,i x,v,i y].
Proof.
  case: i => isF isG i fresh_e1 fresh_e2 Vx Vy uv /=.
  have isF' : is_graph (F ∔ [e1, x, u, y]) by abstract exact: add_edge_graph'.
  have isG' : is_graph (G ∔ [e2, vfun_body i x, v, vfun_body i y]).
    by abstract (apply: add_edge_graph'; exact: (iso2_vset (OIso2 i))).
  econstructor.
  apply: iso2_comp. apply: close_add_edge'. assumption. 
  apply: iso2_comp (iso2_sym _). 2: apply: close_add_edge';assumption. 
  apply add_edge2_iso'' with i; try assumption.
  all: abstract (by rewrite /vfun_of vfun_bodyE /= close_fsval close_vE).
Defined.

Arguments del_edges2 [L] G E.

Definition fsetD_sig_bij (T : choiceType) (A B : {fset T}) : 
  bij (A `\` B) { x : A | x \in ~: [set y | val y \in B]}.
Admitted.

Lemma close_del_edges (G : pre_graph) (isG : is_graph G) (E : {fset ET})  : 
  close (G - E) ≃2 del_edges2 (close G) [set e | val e \in E].
Proof.
  iso2 bij_id (fsetD_sig_bij _ _) xpred0. 2-3: exact: val_inj.
  split => //=.
  - admit.
  - admit.
Qed.

Lemma oiso2_del_edges (F G : pre_graph) (i : F ⩭2 G) E E':
  E' = [fset efun_of i e | e in E] -> (F - E) ⩭2 (G - E').
Proof.
  case: i => isF isG i /= EE'.
  econstructor.
  apply: iso2_comp. apply: close_del_edges. 
  apply: iso2_comp (iso2_sym _). 2: apply: close_del_edges.
  apply iso2_del_edges2 with i.
  admit.
Defined.

Lemma oiso2_del_edgesE (F G : pre_graph) (i : F ⩭2 G) E E' EE' :
  @oiso2_del_edges F G i E E' EE' =1 i.
Proof. rewrite /=. 
Admitted.

Lemma ostep_iso (F G H : pre_graph) : 
  ostep F G -> F ⩭2 H -> Σ U, ostep H U * (G ⩭2 U).
Proof with eauto with vset.
  case => {G}.
  - move => z Vz Iz zIO i. exists (H \ i z)%O. split.
    + apply ostep_v0. 
      * exact: iso2_vset.
      * by rewrite oiso2_edges_at // Iz imfset0.
      * by rewrite -oiso2_pIO.
    + exact: oiso2_del_vertex. 
  - move => x z e u Iz IOz arc_e xDz i.
    have [isF isH] : is_graph F /\ is_graph H by eauto with typeclass_instances.
    have Vz : z \in vset F by apply: oarc_vsetR arc_e.
    exists (H[adt i x <- [dom (u·lv H (i z))]] \ i z)%O. split.
    + apply: (ostep_v1 (e := efun_of i e)). 
      * by rewrite oiso2_edges_at // Iz imfset1. 
      * by rewrite -oiso2_pIO.
      * exact: oiso2_oarc arc_e.
      * apply: contra_neq xDz. apply: vfun_of_inj...
    + unshelve apply: oiso2_del_vertex_. apply: oiso2_add_test...
      * (* rewrite infer_testE. rewrite (oiso2_lv i Vz). -- why does this fail? *)
        abstract admit.
      * done.
      * done.
      * by rewrite oiso2_add_testE. 
  - move => x y z e1 e2 u v Iz e1De2 IOz xDz yDz arc_e1 arc_e2 i.
    have [isF isH] : is_graph F /\ is_graph H by eauto with typeclass_instances.
    have Vz : z \in vset F...
    set e : ET := maxn (efun_of i e1) (efun_of i e2).
    exists ((H \ i z) ∔ [e, i x, u·lv H (i z)·v,i y])%O. split.
    + apply: (ostep_v2).
      * by rewrite oiso2_edges_at // Iz imfset1U imfset1.
      * apply: contra_neq e1De2. apply: efun_of_inj... 
          by case: arc_e1. by case: arc_e2.
      * by rewrite -oiso2_pIO.
      * apply: contra_neq xDz. apply: vfun_of_inj...
      * apply: contra_neq yDz. apply: vfun_of_inj...
      * exact: oiso2_oarc arc_e1.
      * exact: oiso2_oarc arc_e2.
    + have @j : (F \ z)  ⩭2 (H \ i z). exact: oiso2_del_vertex.
      have jE : {in vset (F \ z), j =1 i}. exact: oiso2_del_vertexE.
      rewrite -![i x]jE -?[i y]jE //=. apply (oiso2_add_edge j).
      * by rewrite /= Iz maxn_fsetD.
      * rewrite in_fsetD negb_and negbK oiso2_edges_at //. 
        by rewrite Iz imfset1U imfset1 maxn_fset2.
      * rewrite in_fsetD1 xDz /=...
      * rewrite in_fsetD1 yDz /=...
      * move: (oiso2_lv i Vz) => X. Fail rewrite X. admit. (* why? *)
      * rewrite in_fsetD1 yDz /=...
      * rewrite in_fsetD1 xDz /=...
  - move => x e u arc_e i.
    have [isF isH] : is_graph F /\ is_graph H by eauto with typeclass_instances.
    exists ((H - [fset efun_of i e])[adt i x <- [1 ∥ le H (efun_of i e)]])%O. split.
    + apply: (ostep_e0 (e := efun_of i e)). exact: oiso2_oarc arc_e.
    + have @j : (F - [fset e]) ⩭2 (H - [fset efun_of i e]). 
      { apply: (oiso2_del_edges (i := i)). abstract (by rewrite imfset1). }
      have jE : j =1 i. { exact: oiso2_del_edgesE. }
      rewrite -!jE. apply: oiso2_add_test. 
      * rewrite /=. exact: oarc_vsetL arc_e.
      *  admit. (* OK *)
  - move => x y e1 e2 u v e1De2 arc_e1 arc_e2 i.
    have [isF isH] : is_graph F /\ is_graph H by eauto with typeclass_instances.
    set e : ET := maxn (efun_of i e1) (efun_of i e2).
    exists ((H - [fset efun_of i e1; efun_of i e2]) ∔ [e,i x, u∥v,i y])%O. split.
    + apply: (ostep_e2). 
      * apply: contra_neq e1De2. apply: efun_of_inj... 
        by case: arc_e1. by case: arc_e2.
      * exact: oiso2_oarc arc_e1.
      * exact: oiso2_oarc arc_e2.
    + have @j : (F - [fset e1; e2]) ⩭2 (H - [fset efun_of i e1; efun_of i e2]). 
      { apply: (oiso2_del_edges (i := i)). abstract (by rewrite imfset1U imfset1). }
      have jE : j =1 i. { exact: oiso2_del_edgesE. }
      rewrite -!jE. apply: oiso2_add_edge. 
      * by rewrite maxn_fsetD.
      * by rewrite in_fsetD negb_and negbK maxn_fset2.
      * rewrite /=...
      * rewrite /=...
      * done.
Qed.

Lemma osteps_iso (F G H: pre_graph): osteps F H -> F ⩭2 G -> osteps G H.
Proof.
  intros FH FG. eapply osteps_trans. 
  apply oiso_step. symmetry. apply FG.
  assumption. 
Qed.

Lemma vset_add_vertex (G : pre_graph) x a z : 
  z \in vset (G ∔ [x,a]) = (z == x) || (z \in vset G).
Proof. by rewrite /= !inE. Qed.

(** connecting the open step relation with the additive one on typed graphs *)

(** Transfer of a single closed step to the open step relation. We
first prove a slightly weaker statement with isomorphisms on both
sides of the open step. We then use preservation open steps under
isomorphisms to obtain the desired form of the lemma *)

Lemma eqvG_close G H (isG : is_graph G) (isH : is_graph H) : 
  G ≡G H -> close G ≃2 close H.
Admitted.

Lemma oiso2_add_edge' (F G : pre_graph) (i : F ⩭2 G) 
 (e1 e2 : ET) (x y x' y' : VT) (u v : tm) :
 e1 \notin eset F -> e2 \notin eset G ->
 x \in vset F -> y \in vset F -> x' \in vset G -> y' \in vset G -> 
 i x = x' -> i y = y' -> u ≡ v -> 
 F ∔ [e1, x, u, y] ⩭2 G ∔ [e2, x', v, y'].
Proof with eauto with typeclass_instances.
  case: i => isF isG i.
  move => E1 E2 Vx Vy Vx' Vy' Ix Iy uv. 
  have isF' : is_graph ( F ∔ [e1, x, u, y] ). apply add_edge_graph'...
  have isG' : is_graph (  G ∔ [e2, x', v, y']). apply add_edge_graph'...
  econstructor. 
  apply: iso2_comp. apply: close_add_edge'. assumption.
  apply: iso2_comp (iso2_sym _). 2: apply: close_add_edge'; try assumption.
  apply: (add_edge2_iso'' (h := i)). 
  abstract (by rewrite -Ix //= vfun_bodyE close_fsval close_vE).
  abstract (by rewrite -Iy //= vfun_bodyE close_fsval close_vE).
  exact: uv.
Defined.
  

Lemma oiso2_add_edgeE' F G i e1 e2 x y x' y' u v E1 E2 Vx Vy Vx' Vy' Ix Iy uv k : 
  k \in vset F ->
  @oiso2_add_edge' F G i e1 e2 x y x' y' u v E1 E2 Vx Vy Vx' Vy' Ix Iy uv k = i k.
Proof.
  move => Vk. destruct i => /=. by rewrite !vfun_bodyE /=.
Qed.

Lemma oiso2_transE F G H i j k : k \in vset F -> @oiso2_trans F G H i j k = j (i k).
Proof. 
  case: i j => isF isG i [isF' isH j] Vk.
  rewrite /= !vfun_bodyE; first exact: valP. 
  move => p /=. by rewrite fsvalK.
Qed.

Hint Resolve inj_v_open : vset.
Hint Resolve freshP : vset.

Lemma inj_vNfresh (G : graph2) (x : G) : inj_v x != fresh (vset (open G)).
Proof. apply: inj_v_fresh. exact: freshP. Qed.

Lemma oiso2_id G (isG : is_graph G) : G ⩭2 G. 
Proof. econstructor. exact: iso2_id. Defined.

Lemma oiso2_idE G (isG : is_graph G) x : 
  x \in vset G -> oiso2_id isG x = x.
Proof. move => Vx. by rewrite /= vfun_bodyE. Qed.

Lemma open_add_edgeE (G : graph2) (x y z : G) u :
  @open_add_edge G x y u (inj_v z) = (inj_v z). 
Proof.
  rewrite /= vfun_bodyE ?inj_v_open //= => p. 
  by rewrite imfset_bij_bwdE.
Qed.

Definition oiso2E := (oiso2_transE, 
                      open_add_edgeE, 
                      oiso2_add_edgeE', 
                      oiso2_idE, 
                      open_add_vertexE).

Lemma ostep_of' (F G : graph2) : 
  step F G -> inhabited (Σ F' G', (open F ⩭2 F') * ostep F' G' * (G' ⩭2 open G)).
Proof with eauto with typeclass_instances vset.
  case => {F G}.
  - (* V0 *)
    move => G a. constructor. 
    have ? : fresh (vset (open G)) \notin pIO (open G ∔ [fresh (vset (open G)), a]).
    { rewrite pIO_add. apply: pIO_fresh. exact: freshP. }
    e2split.
    + apply: open_add_vertex.
    + apply: (ostep_v0 (z := fresh (vset (open G)))) => //.
      * by rewrite /= !inE eqxx.
      * by rewrite edges_at_added_vertex // freshP.
    + apply weqG_oliso => //... by rewrite add_vertexK // freshP.
  - (* V1 *) 
    move => G x u a. constructor. e2split.
    + apply: oiso2_trans. apply: open_add_edge. 
      apply: oiso2_add_edge. apply open_add_vertex. 
      2: instantiate (1 := fresh (eset (open G))). 5: instantiate (1 := u). 
      all: idtac... reflexivity.
    + rewrite !open_add_vertexE. 
      set z := fresh _. set e := fresh _.
      apply: (@ostep_v1 _ (inj_v x) z e u). 
      * rewrite edges_at_add_edge edges_at_added_vertex ?fsetU0 //.
        exact: freshP.
      * rewrite !pIO_add. apply: pIO_fresh. exact: freshP.
      * exact: oarc_added_edge.
      * exact: inj_vNfresh.
    + set z := fresh _. set e := fresh _. rewrite /= updateE.
      etransitivity. 2: symmetry. 2: apply: open_add_test.
      eapply weqG_oliso...
      * apply del_vertex_graph => //=. 
        -- apply add_test_graph. by apply: add_edge_graph'; rewrite !inE ?eqxx ?inj_v_open.
        -- rewrite !pIO_add. constructor. apply: pIO_fresh. exact: freshP.
      * rewrite -del_vertex_add_test add_edgeKr ?add_vertexK ?freshP //.
  - (* V2 *) 
    move => G x y u a v. constructor. 
    (* mathcomp pose does not resolve inh_type *)
    pose (z := fresh (vset (open G))).
    pose (e1 := fresh (eset (open G))).
    pose (e2 := fresh (e1 |` eset (open G))).
    have ? : e1 != e2. 
    { apply: contraTneq (@freshP  (e1 |` eset (open G))). 
      rewrite -/e2 => <-. by rewrite !inE eqxx. }
    exists (open G ∔ [z,a] ∔ [e1, inj_v x, u, z] ∔ [e2,z,v,inj_v y])%O. 
    eexists; split; first split.
    + apply: oiso2_trans. apply: open_add_edge. 
      unshelve apply: oiso2_add_edge'.
      apply: oiso2_trans. apply: open_add_edge. 
      unshelve apply: oiso2_add_edge'.
      apply: oiso2_trans. apply: open_add_vertex. 
      exact: oiso2_id.
      (* side conditons *)
      all: try abstract by rewrite ?freshP ?inE ?inj_v_open.
      1: abstract (by rewrite /= !inE eqxx).
      3: abstract (by rewrite /= !inE eqxx).
      1-2: abstract by rewrite !oiso2E // ?inE ?inj_v_open ?eqxx.
      all: by rewrite !oiso2E // ?inE ?inj_v_open ?eqxx.
    + apply (@ostep_v2 _ (inj_v x) (inj_v y) z e1 e2 u v).
      all: rewrite ?pIO_add ?pIO_fresh ?inj_v_fresh ?freshP //.
      * by rewrite edges_at_add_edgeL edges_at_add_edge edges_at_added_vertex ?freshP ?fsetU0 1?fsetUC.
      * apply: oarc_add_edge => //. exact: oarc_added_edge.
      * exact: oarc_added_edge.
    + rewrite /= updateE. 
      apply: oiso2_trans _ (oiso2_sym _). 2: apply: open_add_edge.
      unshelve apply: oiso2_add_edge'. 
      { apply weqG_oliso ...      
all: abstract admit. }
      1: admit.
      all: rewrite ?weqG_iso2E ?freshP //=.
      all: by rewrite ?inE ?inj_v_open ?inj_vNfresh.
  - (* E0 *) move => G x u. 
    pose (e := fresh (eset (open G))).
    constructor. e2split.
    + apply: open_add_edge.
    + apply: (@ostep_e0 _ (inj_v x) e u). exact: oarc_added_edge.
    + rewrite /= update_eq.
      apply: oiso2_trans _ (oiso2_sym _). 2:apply: open_add_test.
      eapply weqG_oliso... admit. admit.
  - (* E2 *) 
    move => G x y u v. constructor. 
    pose (e1 := fresh (eset (open G))).
    pose (e2 := fresh (e1 |` eset (open G))).
    have: e1 != e2 by admit.
    exists (open G ∔  [e1, inj_v x, u, inj_v y] ∔ [e2, inj_v x, v, inj_v y])%O.
    eexists; split; first split.
    + apply: oiso2_trans. apply: open_add_edge. 
      unshelve apply: oiso2_add_edge'.
      apply: open_add_edge. 
      all: by rewrite ?freshP ?inj_v_open ?open_add_edgeE.
    + apply: (@ostep_e2 _ (inj_v x) (inj_v y) e1 e2 u v) => //.
      * apply: oarc_add_edge => //. exact: oarc_added_edge.
      * exact: oarc_added_edge.
    + apply: oiso2_trans _ (oiso2_sym _). 2: apply: open_add_edge.
      unshelve apply: oiso2_add_edge'. 
      { apply weqG_oliso... all: abstract admit. }
      1: by rewrite maxn_fsetD.
      all: by rewrite ?weqG_iso2E ?freshP //= ?inj_v_open.
Qed.

Lemma ostep_of (F G : graph2) : 
  step F G -> exists G', [/\ inhabited (ostep (open F) G') & inhabited (G' ⩭2 open G)].
Proof.
  move/ostep_of' => [[F'] [G']  [[A B] C]].
  case: (ostep_iso B (oiso2_sym A)) => H [H1 H2]. 
  exists H. split => //. constructor. etransitivity. 2: apply: C. by symmetry.
Qed.

(* Lemma close_add_edge_eq G e x y u (isG : is_graph G) (x' y' : close G) (isG' : is_graph (G ∔ [e,x, u, y])) : *)
(*   e \notin eset G -> x' = close_v x :> close G -> y' = close_v y :> close G ->  *)
(*   close (G ∔ [e,x, u, y]) ≃2 close G ∔ [x', u,y']. *)
(* Admitted. *)

(** We need one expansion lemma for every rule *)


Lemma expand_isolated (G : pre_graph) (z : VT) (isG : is_graph G) (isH : is_graph (G \ z)) :
    z \in vset G -> edges_at G z = fset0 -> close G ≃2 close (G \ z) ∔ lv G z.
Proof.
Admitted.

Lemma expand_pendant (G : pre_graph) (x z : VT) (e : ET) (isG : is_graph G) (Hz : z \notin pIO G) u :
    edges_at G z = [fset e] -> is_edge G e x u z -> x != z -> 
    close G ≃2 close (G \ z) ∔ lv G z ∔ [inl (close_v x), u, inr tt].
Proof.
  move => Iz arc_e xDz. 
  symmetry.  
  apply: iso2_comp. apply: add_edge2_iso. apply: iso2_sym. apply: close_add_vertex. instantiate (1 := z).
  abstract (by rewrite !inE eqxx). rewrite /=. 
  set G' := ((_ \ _) ∔ [_,_])%O. set Sx := Sub _ _. set Sz := Sub _ _. 
  have -> : Sx = (@close_v G' _ x).
  { apply: val_inj => /=. rewrite !close_vE //. admit. admit. }
  have -> : Sz = (@close_v G' _ z). 
  { apply: val_inj => /=. rewrite !close_vE //. admit. }
  apply: iso2_comp (iso2_sym _) _. eapply (close_add_edge' (e := e)). Unshelve.
  - by rewrite /G' /= in_fsetD Iz !inE eqxx.
  - rewrite /G' {}/Sz {}/Sx.  (* TODO: fix edge direction *)
    apply eqvG_close. rewrite del_vertexK ?Iz ?del_edgeK //. admit. 
  - apply: add_edge_graph'. admit. admit.
Qed.

Arguments close_v [G _] x,G [_] x. 

Lemma expand_chain (G : pre_graph) (isG : is_graph G) (x y z : VT) (e1 e2 : ET) (Hz : z \notin pIO G) u v :
  edges_at G z = [fset e1; e2] -> e1 != e2 -> x != z -> y != z -> is_edge G e1 x u z -> is_edge G e2 z v y ->
  x \in vset G -> y \in vset G -> 
  close G ≃2p close (G \ z) ∔ lv G z ∔ [inl (close_v x), u, inr tt] ∔ [inr tt, v, inl (close_v y)].
Proof.
  move => Iz e1De2 xDz yDz arc_e1 arc_e2 Vx Vy. symmetry. constructor.
  (* first extrusion *)
  apply: iso2_comp. apply: add_edge2_iso. apply: add_edge2_iso. 
  apply: iso2_sym. apply: (@close_add_vertex (G \ z) _ z _). 
  abstract (by rewrite !inE eqxx). rewrite /=. 
  set G' := add_vertex _ _ _. set Sx := Sub _ _. set Sz := Sub _ _. set Sy := Sub _ _. 
  have -> : Sx = (@close_v G' _ x). apply: val_inj => /=. rewrite !close_vE //. admit. admit.
  have -> : Sy = (@close_v G' _ y). admit.
  have -> : Sz = (@close_v G' _ z). admit.
  rewrite {}/G'. clear Sx Sy Sz. 
  (* second extrusion *)
  have isG' : is_graph ((G \ z) ∔ [z, lv G z] ∔ [e1, x, u, z]). admit.
  apply: iso2_comp. apply: add_edge2_iso. 
  apply: iso2_sym. eapply (close_add_edge' (e := e1)). 
  { abstract admit. }
  rewrite /=.
  have C k : close_v ((G \ z) ∔ [z, lv G z]) k = close_v ((G \ z) ∔ [z, lv G z] ∔ [e1, x, u, z]) k.
  { apply: val_inj => /=. rewrite !close_vE //. admit. admit. }
  (* third extrusion *)
  rewrite !{}C.
  apply: iso2_comp. apply: iso2_sym. eapply (close_add_edge' (e := e2)). 
  { abstract admit. }
  have ? : z \in vset G by exact: is_edge_vsetR arc_e1.
  apply eqvG_close.
  rewrite del_vertexK // Iz fsetUC -del_edges_edges !del_edgeK //. 
  admit. 
  Unshelve.
  admit.
Qed.

Lemma expand_loop (G : pre_graph) (isG : is_graph G) (x : VT) (e : ET) u :
    is_edge G e x u x -> close G ≃2 close (G - [fset e]) ∔ [close_v x, le G e, close_v x].
Proof.
Admitted.

Lemma expand_parallel (G : pre_graph) (isG : is_graph G) (x y : VT) (e1 e2 : ET) u v :
  e1 != e2 -> is_edge G e1 x u y -> is_edge G e2 x v y ->
  close G ≃2 close (G - [fset e1; e2]) ∔ [close_v x, u, close_v y] ∔ [close_v x, v, close_v y].
Proof.
Admitted.


(** Move this up ?*)

Definition flip_edge (G : pre_graph) (e : ET) :=
  {| vset := vset G;
     eset := eset G;
     endpt b := (endpt G b)[upd e := endpt G (~~ b) e];
     lv := lv G;
     le := (le G)[upd e := (le G e)°];
     p_in := p_in G;
     p_out := p_out G |}. 

Global Instance flip_edge_graph (G : pre_graph) (isG : is_graph G) e : 
  is_graph (flip_edge G e).
Proof. 
  split => //=; rewrite ?p_inP ?p_outP //.
  move => e0 b. case: (altP (e0 =P e)) => [->|?] E0; by rewrite updateE // endptP. 
Qed.

Lemma flip_edge_iso (G : pre_graph) (isG : is_graph G) e : close G ≃2 close (flip_edge G e).
Proof.
  iso2 bij_id bij_id (fun e' : edge (close G) => val e' == e). 2-3: by apply: val_inj.
  split => //=.
  - move => e' b. apply/val_inj => /=.
    case: (altP (fsval e' =P e)) => /= [->|?]; by rewrite updateE.
  - move => e'. case: (altP (fsval e' =P e)) => /= [->|?]; by rewrite updateE.
Defined.
Arguments flip_edge_iso [G isG] e.

Lemma flipped_edge (G : pre_graph) e x y u : 
  is_edge G e x u° y -> is_edge (flip_edge G e) e y u x.
Proof.
  rewrite /is_edge /flip_edge /= !updateE. firstorder. by rewrite H2 cnvI.
Qed.

Lemma is_edge_flip_edge (G : pre_graph) e1 e2 x y u : 
  e2 != e1 -> is_edge G e2 x u y -> is_edge (flip_edge G e1) e2 x u y.
Proof. move => D. by rewrite /is_edge /flip_edge /= !updateE. Qed.

Lemma oarc_flip_edge (G : pre_graph) e1 e2 x y u : 
  oarc G e2 x u y -> oarc (flip_edge G e1) e2 x u y.
Proof.
  case: (altP (e2 =P e1)) => [->|D]. 
  - case => E [b] [A B C]. split => //. exists (~~ b). rewrite /= !negbK !updateE. 
    split => //. symmetry. rewrite eqvb_neq. symmetry. by rewrite cnvI.
  - case => E [b] [A B C]. split => //. exists b. by rewrite /= !updateE.
Qed.

Lemma incident_flip (G : pre_graph) e x : incident (flip_edge G e) x =1 incident G x.
Proof. 
  move => e0. rewrite /incident. case: (altP (e0 =P e)) => [->|D]. 
  - apply/existsP/existsP => [] [b] /eqP<-; exists (~~ b) => /=; by rewrite updateE ?negbK.
  - apply/existsP/existsP => [] [b] /eqP<-; exists b => /=; by rewrite updateE ?negbK.
Qed.

Lemma edges_at_flip_edge (G : pre_graph) (e : ET) (x : VT) : 
  edges_at (flip_edge G e) x = edges_at G x.
Proof. rewrite /edges_at. apply: eq_imfset => //= e0. by rewrite !inE incident_flip. Qed.

Lemma flip_edge_add_test (G : pre_graph) (e : ET) (x : VT) a : 
  ((flip_edge G e)[adt x <- a])%O = (flip_edge (G[adt x <- a]) e)%O.
Proof. done. Qed.

Lemma flip_edge_kill (G : pre_graph) (e : ET) (x : VT)  : 
  e \in edges_at G x -> (flip_edge G e) \ x ≡G G \ x.
Proof. 
  move => He. split; rewrite //= edges_at_flip_edge //.
  - move => b e' /fsetDP [A B]. rewrite updateE //. by apply: contraNneq B => ->.
  - move => e' /fsetDP [A B]. rewrite updateE //. by apply: contraNneq B => ->.
Qed.
  
Lemma flip_edge_kill' (G : pre_graph) (e : ET) (E : {fset ET})  : 
  e \in E -> (flip_edge G e) - E ≡G G - E.
Proof. 
  move => He. split; rewrite //= ?edges_at_flip_edge //.
  - move => b e' /fsetDP [A B]. rewrite updateE //. by apply: contraNneq B => ->.
  - move => e' /fsetDP [A B]. rewrite updateE //. by apply: contraNneq B => ->.
Qed.
  
Lemma steps_of_ostep (G H : pre_graph) (isG : is_graph G) (isH : is_graph H) : 
  ostep G H -> steps (close G) (close H).
Proof with eauto with typeclass_instances.
  move => S. case: S isG isH => {H}.
  - move => z Vz Iz IOz isG isH. 
    have h : close G ≃2 close (G \ z) ∔ lv G z by exact: expand_isolated.
    apply: cons_step h _ (steps_refl _). by constructor.
  - move => x z e u He Hz arc_e xDz isG isH.
    (* resolve oarc *)
    wlog edge_e : G He Hz {arc_e} isG isH / is_edge G e x u z.
    { move => W. case: (oarc_cases arc_e) => {arc_e} edge_e; first exact: W.
      etransitivity. apply: iso_step. apply: (flip_edge_iso e).
      etransitivity. apply: W => //.
      - by rewrite ?edges_at_flip_edge.
      - exact: flipped_edge. 
      - apply: iso_step. apply: eqvG_close. rewrite flip_edge_add_test flip_edge_kill //=.
        by rewrite edges_at_test He !inE. }
    set a := lv G z in isH *.
    have xV : x \in vset G by eauto with vset.
    have x_del_z : x \in vset (G \ z) by eauto with vset.
    have z_del_z : z \notin vset (G \ z) by rewrite !inE eqxx.
    have h : close G ≃2 close (G \ z) ∔ a ∔ [inl (close_v x), u, inr tt]. 
      { exact: expand_pendant He edge_e _. }
      apply: cons_step h _ _. constructor. 
      apply iso_step. apply: iso2_comp. apply: close_add_test => //.
      apply: eqvG_close. by rewrite del_vertex_add_test.
  - move => x y z e1 e2 u v Iz e1De2 Hz xDz yDz arc_e1 arc_e2 isG isH.
    wlog edge_e1 : G Iz Hz {arc_e1} arc_e2 isG isH / is_edge G e1 x u z.
    { move => W. case: (oarc_cases arc_e1) => {arc_e1} edge_e1; first exact: W.
      etransitivity. apply: iso_step. apply: (flip_edge_iso e1).
      etransitivity. unshelve eapply (W (flip_edge G e1)) => //.
      - abstract by apply: add_edge_graph'; rewrite !inE ?xDz ?yDz ; 
          [apply: (is_edge_vsetR edge_e1)|apply: oarc_vsetR arc_e2].
      - by rewrite ?edges_at_flip_edge.
      - exact: oarc_flip_edge.
      - exact: flipped_edge. 
      - apply: iso_step. apply: eqvG_close. rewrite flip_edge_kill //=.
        by rewrite Iz !inE eqxx. }
    wlog edge_e2 : G Iz Hz {arc_e2} edge_e1 isG isH / is_edge G e2 z v y.
    { move => W. case: (oarc_cases arc_e2) => {arc_e2} edge_e2; first exact: W.
      etransitivity. apply: iso_step. apply: (flip_edge_iso e2).
      etransitivity. unshelve eapply (W (flip_edge G e2)) => //.
      - abstract by apply: add_edge_graph'; rewrite !inE ?xDz ?yDz;
          [apply: (is_edge_vsetL edge_e1)|apply: is_edge_vsetL edge_e2].
      - by rewrite ?edges_at_flip_edge.
      - exact: is_edge_flip_edge.
      - exact: flipped_edge. 
      - apply: iso_step. apply: eqvG_close. rewrite flip_edge_kill //=.
        by rewrite Iz !inE eqxx. }
    set a := lv G z in isH *.
    have xV : x \in vset G by eauto with vset.
    have yV : y \in vset G by eauto with vset.
    have x_del_z : x \in vset (G \ z) by eauto with vset.
    have y_del_z : y \in vset (G \ z) by eauto with vset.
    have z_del_z : z \notin vset (G \ z) by rewrite !inE eqxx.
    have [h] : close G ≃2p 
             close (G \ z) ∔ a ∔ [inl (close_v x),u,inr tt] ∔ [inr tt,v,inl (close_v y)].
    { apply: expand_chain. exact: Iz. all: try done. }
    apply: cons_step h _ _. constructor. 
    apply: iso_step. apply: iso2_comp (iso2_sym _) _. apply: (@close_add_edge' (G \ z)).
    by rewrite /= Iz maxn_fsetD. reflexivity.
  - move => x e u arc_e isG isH.
    have edge_e : is_edge G e x u x. { admit. (* TODO: the rule should use is_edge *) }
    have h : close G ≃2 close (G - [fset e]) ∔ [close_v x,le G e,close_v x].
    { exact: expand_loop edge_e. }
    apply: cons_step h _ _. constructor. 
    apply: iso_step. apply: iso2_comp. apply: close_add_test. 
    + by eauto with vset.
    + exact: close_irrelevance.
  - move => x y e1 e2 u v e1De2 arc_e1 arc_e2 isF isH.
    wlog edge_e1 : G {arc_e1} arc_e2 isF isH / is_edge G e1 x u y.
    { move => W. case: (oarc_cases arc_e1) => {arc_e1} edge_e1; first exact: W.
      etransitivity. apply: iso_step. apply: (flip_edge_iso e1).
      etransitivity. unshelve eapply (W (flip_edge G e1)) => //.
      - abstract by apply: add_edge_graph' => /=;  eauto with vset. 
      - exact: oarc_flip_edge.
      - exact: flipped_edge. 
      - apply: iso_step. apply: eqvG_close. rewrite flip_edge_kill' //=.
        by rewrite !inE eqxx. }
    wlog edge_e2 : G {arc_e2} edge_e1 isF isH / is_edge G e2 x v y.
    { move => W. case: (oarc_cases arc_e2) => {arc_e2} edge_e2; first exact: W.
      etransitivity. apply: iso_step. apply: (flip_edge_iso e2).
      etransitivity. unshelve eapply (W (flip_edge G e2)) => //.
      - abstract by apply: add_edge_graph' => /=;  eauto with vset. 
      - exact: is_edge_flip_edge.
      - exact: flipped_edge. 
      - apply: iso_step. apply: eqvG_close. rewrite flip_edge_kill' //=.
        by rewrite !inE eqxx. }
    have h : close G ≃2 close (G - [fset e1; e2]) ∔ [close_v x,u,close_v y] ∔ [close_v x,v,close_v y].
    { exact: expand_parallel. }
    apply: cons_step h _ _. constructor. 
    apply: iso_step. apply: iso2_comp (iso2_sym _) _. apply: (@close_add_edge' (G - [fset e1;e2])).
    + by rewrite maxn_fsetD.
    + reflexivity.
Qed.

Lemma steps_of (G H : pre_graph) (isG : is_graph G) (isH : is_graph H) : 
  osteps G H -> steps (close G) (close H).
Proof.
  move => S. elim: S isG isH => {G H} [G H h|G H GH |G F H S IH1 _ IH2] isG isH.
  - apply: iso_step.
    apply: iso2_comp (iso2_comp (oiso2_iso h) _); apply: close_irrelevance.
  - exact: steps_of_ostep.
  - have isF : is_graph F by apply: osteps_graph S. 
    by transitivity (close F). 
Qed.

End ostep.
End PttdomGraphTheory.

