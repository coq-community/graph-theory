Require Import Relation_Definitions Morphisms RelationClasses.
From mathcomp Require Import all_ssreflect.

Require Import edone finite_quotient preliminaries bij equiv.
Require Import setoid_bigop structures pttdom mgraph mgraph2 rewriting open_confluence.

Require Import finmap_plus.
Open Scope fset_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

(** * Transfer of Open Local Confluence *)

(** ** Opening and packing of type-based graphs *)
Ltac e2split := do 2 eexists; split; [split|].

Lemma iso2_intro (L : labels) (G H : graph2 L) (hv : bij G H) (he : bij (edge G) (edge H)) (hd : edge G -> bool) :
  is_ihom hv he hd -> hv input = input -> hv output = output -> G ≃2 H.
Proof. move => hom_h. by exists (Iso hom_h). Defined.

Tactic Notation "iso2" uconstr(hv) uconstr(he) uconstr(hd) := 
  match goal with |- ?G ≃2 ?H => refine (@iso2_intro _ G H hv he hd _ _ _) end.


(** In order turn packaged graphs into open graphs, we need to inject
arbitrary finite types into [VT] and [ET]. *)

Section inject.
Variable (T : finType).

Definition inj_v (x : T) : VT := enum_rank x.
Definition inj_e (x : T) : ET := enum_rank x.

Lemma inj_v_inj : injective inj_v. 
Proof. move => x y. by move/ord_inj/enum_rank_inj. Qed.

Lemma inj_e_inj : injective inj_e. 
Proof. move => x y. by move/ord_inj/enum_rank_inj. Qed.

End inject.
Hint Resolve inj_v_inj inj_e_inj : core.
Instance VT_inh_type : inh_type VT := Build_inh_type 0. 
Arguments inj_v {T}.
Arguments inj_e {T}.

Section Open.
Variable L: labels.
Notation Le := (structures.le L).                
Notation Lv := (structures.lv L).
Notation graph := (graph L).
Notation graph2 := (graph2 L).
Variables (G : graph2).
Context `{inh_type Le}.

(** We also need (partial) inverses to the functons [inj_v] and
[inj_e]. For edges, this is necessarily partial, because the edge type
may be empty. For vertices, we can use a total function, because we
are dealing with 2p-graphs. *)

Definition proj_e (e : ET) : option (edge G) := 
  omap enum_val (insub e : option 'I_#|edge G|).

Lemma inj_eK : pcancel inj_e proj_e.
Proof. 
  move => e. rewrite /proj_e /inj_e /=.
  have P : enum_rank e < #|edge G| by [].
  case: insubP => [k _ /ord_inj -> /=|]; by rewrite ?P ?enum_rankK.
Qed.

(** For two-pointed graphs, we can use the input as default vertex when inverting the injection into [VT] *)
Definition proj_v (v : VT) : G :=
  odflt input (omap enum_val (insub v : option 'I_#|G|)).

Lemma inj_vK : cancel inj_v proj_v.
Proof.
  move => v. rewrite /proj_v /inj_v /=. 
  have P : enum_rank v < #|G| by [].
  case: insubP => [k _ /ord_inj -> /=|]; by rewrite ?P ?enum_rankK.
Qed.

(** In order to totalize the edge labeling, we need a default edge label. This
is necessary since an edgeless [G] may use an empty type for labeling
edges... *)

Definition open : pre_graph Lv Le := 
  {| vset := [fset inj_v x | x in G];
     eset := [fset inj_e x | x in edge G];
     endpt b (e:ET) := if proj_e e is Some e' then inj_v (endpoint b e') else default;
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

Lemma inj_v_open (x : G) : inj_v x \in vset open.
Proof. by rewrite in_imfset. Qed.

Lemma inj_v_fresh (x : G) (z : VT) : z \notin vset open -> inj_v x != z.
Proof. apply: contraNneq => <-. exact: inj_v_open. Qed.

Lemma inj_vNfresh (x : G) : inj_v x != fresh (vset open).
Proof. apply: inj_v_fresh. exact: freshP. Qed.

End Open.
Hint Resolve inj_v_open : core.
Hint Resolve freshP : vset.


Section Pack.
Variable L: labels.
Notation Le := (structures.le L).
Notation Lv := (structures.lv L).
Notation graph := (graph L).
Notation graph2 := (graph2 L).
Variable (G : pre_graph Lv Le).
Context {graph_G : is_graph G}.

Lemma endpt_proof b (e : eset G) : endpt G b (val e) \in vset G.
Proof. exact: (endptP b (valP e)). Qed.

Definition pack' : graph :=  
  {| vertex := fset_sub_finType (vset G);
     edge := fset_sub_finType (eset G);
     endpoint b e := Sub (endpt G b (val e)) (endpt_proof b e);
     vlabel v := lv G (val v);
     elabel e := le G (val e) |}.

Definition pack := Eval hnf in
  point pack' (Sub (p_in G) (@p_inP _ _ _ _)) (Sub (p_out G) (@p_outP _ _ _ _)).

(** Since the vertex type od a packed graph is simply the vertex set
seen as type, we can trace vertcies through the packing operation. *)
Definition pack_v (x : VT) : pack :=
  match @idP (x \in vset G) with
  | ReflectT p => Sub x p
  | ReflectF _ => input
  end.

Lemma pack_vE z (Vz : z \in vset G) : 
  pack_v z = Sub z Vz.
Proof.
  rewrite /pack_v. case: {-}_ / idP => [p|]; [exact: val_inj|by rewrite Vz].
Qed.

Lemma pack_vK (x : VT) : x \in vset G -> fsval (pack_v x) = x.
Proof. move => Vx. by rewrite pack_vE. Qed.

Lemma pack_fsval (v : vset G) : pack_v (fsval v) = v.
Proof. apply: val_inj => //=. by rewrite pack_vK ?fsvalP. Qed.

End Pack.
Arguments pack [_] G {_} , [_] G graph_G.
Arguments pack_v [L G _] x,[L] G [_] x. 
Arguments pack_v : simpl never.


(** ** Isomorphism and Commutation Properties *)

(* TODO: separate the things that are specific to pttdom from those that work for any label structure *)
Section PttdomGraphTheory.
Variable tm : pttdom. 
Notation test := (test tm).

Notation pre_graph := (pre_graph test (car (setoid_of_ops (pttdom.ops tm)))).
Notation graph := (graph (pttdom_labels tm)).
Notation graph2 := (graph2 (pttdom_labels tm)).

(** We define isomorphisms of open graphs via packing *)
Set Primitive Projections.
Record oiso2 (G H : pre_graph) := 
  OIso2 { oiso2_graphL : is_graph G;
          oiso2_graphR : is_graph H;
          oiso2_iso : pack G ≃2 pack H}.
Unset Primitive Projections.
Global Existing Instance oiso2_graphL.
Global Existing Instance oiso2_graphR.

Notation "G ⩭2 H" := (oiso2 G H) (at level 45).

Lemma pack_irrelevance (G : pre_graph) (graph_G graph_G' : is_graph G) : 
  pack G graph_G ≃2 pack G graph_G'.
Proof.
  iso2 bij_id bij_id xpred0; try exact: val_inj.
  split => // e [|]; exact: val_inj.
Defined.

Lemma iso_of_oiso (G H : pre_graph) (graph_G : is_graph G) (graph_H : is_graph H) : 
  G ⩭2 H -> pack G ≃2 pack H.
Proof. 
  case => graph_G' graph_H' I.
  transitivity (pack G graph_G'); first exact: pack_irrelevance.
  apply: iso2_comp I _. exact: pack_irrelevance.
Qed.

(** [oiso2] is a PER on pre_graphs, but it is only reflexive on well-formed graphs *)

Lemma oiso2_trans : CRelationClasses.Transitive oiso2.
Proof. 
  move => F G H [isF isG FG] [isG' isH GH]. econstructor.
  apply: iso2_comp GH. 
  apply: iso2_comp FG _. exact: pack_irrelevance.
Defined.

Lemma oiso2_sym : CRelationClasses.Symmetric oiso2.
Proof. move => F G [isF isG /iso2_sym ?]. by econstructor. Qed.

Global Instance oiso2_Equivalence : CRelationClasses.PER oiso2.
Proof. exact: (CRelationClasses.Build_PER _ oiso2_sym oiso2_trans). Qed.

(** [open] and [pack] cancel each other up to isomorphism *)

Lemma openK (G : graph2) : G ≃2 pack (open G).
Proof.
  iso2 (imfset_bij (@inj_v_inj G)) (imfset_bij (@inj_e_inj (edge G))) (fun => false) => /=.
  2-3: exact: val_inj.
  split. 
  - move => e b. apply: val_inj => /=;by rewrite !inj_eK.
  - move => v /=. by rewrite inj_vK. 
  - move => e /=. by rewrite inj_eK.
Defined.

Lemma openKE (G : graph2) (x : G) :
  openK G x = pack_v (inj_v x) :> pack (open G).
Proof. 
  rewrite /pack_v /=. case: {-}_ /idP => [p|np].
  - by apply: val_inj => /=. 
  - by rewrite in_imfsetT in np.
Qed.

Lemma packK (G : pre_graph) (graph_G : is_graph G) : 
  G ⩭2 open (pack G).
Proof. econstructor. exact: openK. Defined.

Lemma oiso_of (G H: graph2): G ≃2 H -> open G ⩭2 open H.
Proof.
  intro.
  apply (@OIso2 _ _ (open_is_graph G) (open_is_graph H)).
  etransitivity. symmetry. apply openK.
  etransitivity. eassumption. apply openK.
Qed.
  

(** In order to reason about [F ⩭2 G] without dependent types, we need
to cast the bijections underlying the isomorphism of [pack F ≃2 pack
G] to functions on [VT -> VT] and [ET -> ET] respectively. These
functions are bijective only on vertices and edges of the respective
graphs. *)

Definition vfun_body (G H : pre_graph) (graph_G : is_graph G) (graph_H : is_graph H) 
  (h : bij (pack G) (pack H)) (x : VT) : VT := 
  locked (match @idP (x \in vset G) with
          | ReflectT p => val (h (Sub x p))
          | ReflectF _ => x
          end).

Definition vfun_of (G H : pre_graph) (h : G ⩭2 H) := vfun_body (oiso2_iso h).
Coercion vfun_of : oiso2 >-> Funclass.

Definition efun_body (G H : pre_graph) (graph_G : is_graph G) (graph_H : is_graph H) 
  (he : bij (edge (pack G)) (edge (pack H))) (e : ET) : ET := 
  locked (match @idP (e \in eset G) with
          | ReflectT p => val (he (Sub e p))
          | ReflectF _ => e
          end).

Definition efun_of (G H : pre_graph) (h : G ⩭2 H) := efun_body (oiso2_iso h).e.

Definition edir_body (G : pre_graph) (graph_G : is_graph G)  
  (hd : edge (pack G) -> bool) (e : ET) : bool := 
  locked (match @idP (e \in eset G) with
          | ReflectT p => hd (Sub e p)
          | ReflectF _ => false
          end).

Definition edir_of (G H : pre_graph) (h : G ⩭2 H) := edir_body (oiso2_iso h).d.

Arguments vfun_of [G H] h / _.
Arguments efun_of [G H] h e /.
Arguments edir_of [G H] h e /.

Lemma vfun_bodyE (G H : pre_graph) (isG : is_graph G) (isH : is_graph H) x
  (h : bij (pack G isG) (pack H isH)) (p : x \in vset G) : vfun_body h x = val (h (Sub x p)).
Proof.
  unlock vfun_body. 
  case: {-}_ / idP => [p'|]; by [rewrite (bool_irrelevance p p')| move/(_ p)].
Qed.

Lemma vfun_bodyEinj (G : graph2) (H : pre_graph) (graph_H : is_graph H)
     (h : bij (pack (open G)) (pack H)) (x : G) :
  vfun_body h (inj_v x) = val (h (Sub (inj_v x) (inj_v_open x))).
Proof. by rewrite vfun_bodyE. Qed.

Lemma efun_bodyE (G H : pre_graph) (isG : is_graph G) (isH : is_graph H) 
  (he : bij (edge (pack G)) (edge (pack H))) e (He : e \in eset G) : 
  efun_body he e = val (he (Sub e He)).
Proof. 
  unlock efun_body. case: {-}_ / idP => [p|]; last by rewrite He. 
  by rewrite (bool_irrelevance He p).
Qed.

Lemma edir_bodyE (G : pre_graph) (isG : is_graph G) 
  (hd : (edge (pack G)) -> bool) e (He : e \in eset G) : 
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

(* TOTHINK: the converse does NOT hold since [h] is the identity on
vertices outside of [G]. This could be made to hold by taking [fresh (vset H)] 
as value outside of [G] *)
Lemma oiso2_vset (G H : pre_graph) (h : G ⩭2 H) x : x \in vset G -> h x \in vset H.
Proof. case: h => /= isG isH h /= xG. rewrite /vfun_of vfun_bodyE. exact: valP. Qed.


Lemma oiso2_input (F G : pre_graph) (i : F ⩭2 G) : i (p_in F) = p_in G.
Proof. 
  case: i => isF isG i /=. rewrite vfun_bodyE => [|p]. exact: p_inP.
  rewrite [Sub _ _](_ : _ = @input _ (pack F)) ?iso2_input //. exact: val_inj. 
Qed.

Lemma oiso2_output (F G : pre_graph) (i : F ⩭2 G) : i (p_out F) = p_out G.
Proof. 
  case: i => isF isG i /=. rewrite vfun_bodyE => [|p]. exact: p_outP.
  rewrite [Sub _ _](_ : _ = @output _ (pack F)) ?iso2_output //. exact: val_inj. 
Qed.

Lemma oiso2_id G (isG : is_graph G) : G ⩭2 G. 
Proof. econstructor. exact: iso2_id. Defined.

Lemma oiso2_idE G (isG : is_graph G) x : 
  x \in vset G -> oiso2_id isG x = x.
Proof. move => Vx. by rewrite /= vfun_bodyE. Qed.

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
  (i : pack F ≃2 pack G) z (Vz : z \in vset F) : 
  z \in pIO F = (val (i (Sub z Vz)) \in pIO G).
Proof. by rewrite (oiso2_pIO (OIso2 i)) //= vfun_bodyE. Qed. 

Lemma pack_v_IO (F : pre_graph) (isF : is_graph F) z (Hz : z \notin pIO F) : 
  z \in vset F -> @pack_v _ F isF z \notin IO.
Proof. move => Vz. apply: contraNN Hz. by rewrite pack_vE !inE. Qed.

Lemma Sub_endpt (G : pre_graph) (isG : is_graph G) (e : ET) (He : e \in eset G) b (p : endpt G b e \in vset G) :
  Sub (endpt G b e) p = @endpoint _ (pack G) b (Sub e He).
Proof. exact: val_inj. Qed.

Lemma oiso2_endpoint (F G : pre_graph) (i : F ⩭2 G) (e : ET) b :
  e \in eset F -> endpt G b (efun_of i e) = i (endpt F (edir_of i e (+) b) e).
Proof.
  case: i => isF isG i Ee /=. 
  rewrite edir_bodyE efun_bodyE vfun_bodyE ?endptP // => p.
  by rewrite Sub_endpt -endpoint_hom /=.
Qed.

(** While injectivity of [vfun_of i] and [efun_of i] is sufficient to
prove that they are preserved under isomorphisms, we actually need to
show that [efun_of i] is a bijection between [eset F] and [eset G] in
order to transfer the [edges_at] function *)

(* TOTHINK: encapsulate this notion? *)
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
  case: i => isF isG i Ee /=. rewrite vfun_bodyE /=. exact: (vlabel_iso i).
Qed.

Lemma oiso2_le (F G : pre_graph) (i : F ⩭2 G) e : e \in eset F ->
  le G (efun_of i e) ≡[edir_of i e] le F e.
Proof.
  case: i => isF isG i Ee /=. rewrite efun_bodyE edir_bodyE. 
  exact: elabel_hom. (* this doesn't ? *)
Qed.

(** perservation of incidence and the [oarc] predicate *)

Lemma oiso2_incident (F G : pre_graph) (i : F ⩭2 G) (x : VT) (e : ET) :
  x \in vset F -> e \in eset F ->
  incident F x e = incident G (i x) (efun_of i e).
Proof.
  move => Vx Ee. rewrite /incident. apply/existsP/existsP. 
  - move => [b] e_x. exists (edir_of i e (+) b). rewrite oiso2_endpoint //.
    by rewrite addbA addbb [addb _ _]/= (eqP e_x).
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
  rewrite !oiso2_endpoint // -addbN !addbA !addbb !addFb A B. split => //.
  exact: eqvb_trans (oiso2_le _ _ ) _.
Qed.


(** Graph equivalence gives rise to graph isomorphism for well-formed
graphs. Note that one of the [is_graph _] assumptions follows from the
other. So use the more specific [L/R] lemmas below. *)

Definition eqvG_iso2 (G H : pre_graph) : 
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

Definition eqvG_iso2L (G H : pre_graph) (isG : is_graph G) (E : G ≡G H) := 
  @eqvG_iso2 G H isG (eqvG_graph isG E) E.

Definition eqvG_iso2R (G H : pre_graph) (isH : is_graph H) (E : G ≡G H) := 
  @eqvG_iso2 G H (eqvG_graph isH (eqvG_sym E)) isH E.

Lemma eqvG_iso2E (G H : pre_graph) (isG : is_graph G) (isH : is_graph H) (E : G ≡G H) x :
  x \in vset G ->
  @eqvG_iso2 G H isG isH E x = x.
Proof. 
  move => Vx. rewrite /= vfun_bodyE /=. destruct E.
  rewrite /=. by rewrite bij_castE.
Qed.

Lemma eqvG_pack (G H : pre_graph) (isG : is_graph G) (isH : is_graph H) : 
  G ≡G H -> pack G ≃2 pack H.
Proof. 
  move/eqvG_iso2 => h. 
  apply: iso2_comp _ (iso2_comp  (@oiso2_iso _ _ h) _); apply: pack_irrelevance.
Qed.

(** ** Commutation with open/pack *)

Arguments freshP {E}.

Lemma pack_add_edge' (G : pre_graph) e x y u 
  (isG : is_graph G)(isG' : is_graph (G ∔ [e,x, u, y])) :
  e \notin eset G -> pack (G ∔ [e,x, u, y]) ≃2 pack G ∔ [pack_v x, u, pack_v y].
Proof. 
  move => eG.
  apply: iso2_sym. 
  iso2 (bij_id) (fresh_bij bij_id eG) (fun => false) => //. 
  2-3: exact: val_inj. 
  split => //.
  - move => [e'|] b; apply: val_inj => //.
    + by rewrite fresh_bijE /= updateE ?fsval_eqF.  
    + rewrite fresh_bijE /= updateE. 
      by case: b; rewrite pack_vK // ?fsval_eqF add_edgeV.
  - by move => [e'|] /=; rewrite updateE // fsval_eqF.
Defined.

Lemma pack_add_edge (G : pre_graph) (x y : VT) u 
  (isG : is_graph G) (isG' : is_graph (G ∔ [x, u, y])) : 
  pack (G ∔ [x, u, y]) ≃2 pack G ∔ [pack_v x, u, pack_v y].
Proof. exact: pack_add_edge' freshP. Defined.

Definition pack_add_vertex (G : pre_graph) (graph_G : is_graph G) x a : x \notin vset G -> 
  pack (G ∔ [x, a]) ≃2 (pack G) ∔ a.
Proof.
  move => xG. apply: iso2_sym. 
  iso2 (fresh_bij' bij_id xG) sumxU (fun => false) => //. 2-3: move => *; exact: val_inj.
  split => //.
  + move => [e|[]] b. exact: val_inj.
  + by move => [v|] /=; rewrite updateE // fsval_eqF.
  + by move => [e|[]]. 
Defined.

Definition pack_add_test (G : pre_graph) (isG : is_graph G) x (Hx : x \in vset G) a :
  (pack G)[tst pack_v x <- a] ≃2 pack (G[adt x <- a]).
Proof.
  iso2 bij_id bij_id xpred0; try exact: val_inj.
  split => //.
  - move => e b. exact: val_inj. 
  - move => v. rewrite /= /update. (* simpl should not expose tst_dot *)
    case: (altP (v =P pack_v x)) => [->|D]. 
    + by rewrite pack_vK // eqxx.
    + suff -> : (fsval v == x = false) by []. 
      apply: contra_neqF D => /eqP<-. by rewrite pack_fsval.
Defined.

Section Open.
Variable (G : graph2).

Definition open_add_vertex a : 
  open (G ∔ a) ⩭2 (open G) ∔ [fresh (vset (open G)), a].
Proof. 
  econstructor.
  apply: iso2_comp (iso2_sym _) _. apply: openK.
  apply: iso2_comp (iso2_sym _). 2: apply: pack_add_vertex freshP. 
  apply: add_vertex2_iso => //. exact: openK.
Defined.

Lemma open_add_vertexE : 
  ((forall a, open_add_vertex a (@inj_v (G ∔ a)%G2 (inr tt)) = fresh (vset (open G)))
  *(forall a x, open_add_vertex a (@inj_v (G ∔ a)%G2 (inl x)) = @inj_v G x))%type. 
Proof. 
  split => [a|a x]. 
  - rewrite /vfun_of/= vfun_bodyE. exact: inj_v_open.
    move => H /=. by rewrite imfset_bij_bwdE.
  - rewrite /vfun_of/= vfun_bodyE. exact: inj_v_open.
    move => H /=. by rewrite imfset_bij_bwdE //=.
Qed.

(* This follows the same pattern as open_add_vertex. Lemma? *)
Lemma open_add_edge (x y : G) u : 
  open (G ∔ [x, u, y]) ⩭2 open G ∔ [inj_v x, u, inj_v y].
Proof. 
  have X : is_graph (add_edge (open G) (inj_v x) u (inj_v y)). 
  { exact: add_edge_graph. }
  econstructor.
  apply: iso2_comp (iso2_sym _) _. apply: openK.
  apply: iso2_comp _ (iso2_sym _). 2: apply pack_add_edge.
  apply: (add_edge2_iso'' (h := (openK _))) => //; exact: openKE.
Defined.

Lemma open_add_edgeE (x y z : G) u :
  @open_add_edge x y u (inj_v z) = (inj_v z). 
Proof.
  rewrite /= vfun_bodyE ?inj_v_open //= => p. 
  by rewrite imfset_bij_bwdE.
Qed.

Definition open_add_test (x : G) a : 
  open (G[tst x <- a]) ⩭2 (open G)[adt inj_v x <- a].
Proof.
  econstructor.
  apply: iso2_comp (iso2_sym (openK _)) _.
  apply: iso2_comp (pack_add_test _ _ _); last exact: inj_v_open.
  apply: iso2_comp. 
    apply: (add_test_cong _ _ eqvxx). apply: openK. 
  by rewrite openKE.
Defined.

End Open. 
   
(** ** Isomorphisms on open graphs *)

(* We prove this directly rather than going though [add_edge2_rev],
because this way we can avoid the assumption [e \notin eset G] *)
Lemma add_edge_flip (G : pre_graph) e x y u v (isG1 : is_graph (G ∔ [e,x,u,y])): 
  u° ≡ v ->
  x \in vset G -> y \in vset G -> G ∔ [e,x,u,y] ⩭2 G ∔ [e,y,v,x].
Proof.
  move => E xG yG. 
  have isG2 : is_graph (G ∔ [e,y,v,x]) by apply: add_edge_graph''.
  econstructor.
  pose dir (e0 : edge (pack (G ∔ [e,x,u,y]) isG1)) := val e0 == e.
  iso2 bij_id bij_id dir => //=. 2-3: exact: val_inj.
  split => //.
  - case => e' He' b /=. apply: val_inj => /=. case: (fset1UE He') => [?|].
    + subst e'. by rewrite /dir/=!eqxx addTb !updateE if_neg. 
    + case => A ?. by rewrite /dir/= (negbTE A) !updateE.
  - case => e' He'. rewrite /dir/=. case: (fset1UE He') => [?|].
    + subst e'. rewrite eqxx !updateE. by symmetry in E.
    + case => A ?. by rewrite /dir/= (negbTE A) !updateE.
Defined.

Lemma oiso2_add_test (F G : pre_graph) (i : F ⩭2 G) x a b :
  x \in vset F ->
  a ≡ b -> F[adt x <- a] ⩭2 G[adt i x <- b].
Proof.
  case: i => isF isG i Vx ab. (* rewrite {}E /=. *)
  econstructor. 
  apply: iso2_comp (iso2_sym _) _. by apply: pack_add_test.
  apply: iso2_comp. 2: apply: pack_add_test. 2: exact: (oiso2_vset (OIso2 i)).
  apply add_vlabel2_iso'' with i. 2:exact: ab.
  abstract (by rewrite /= vfun_bodyE /= pack_fsval pack_vE).
Defined.

Lemma oiso2_add_testE (F G : pre_graph) (i : F ⩭2 G) x a b Vx ab z : 
  z \in vset F ->
  @oiso2_add_test F G i x a b Vx ab z = i z.
Proof. by move => Vz; rewrite /= !vfun_bodyE. Qed.

Hint Extern 0 (box _) => apply Box; assumption : typeclass_instances.

(* TOTHINK: can this be simplified? Should we connect this to typed vertex removal? *) 
Lemma oiso2_remove_vertex (F G : pre_graph) (z : VT) (j : F ⩭2 G) : 
  z \in vset F ->
  z \notin pIO F -> F \ z ⩭2 G \ j z.
Proof.
  move: j => [isF isG i] Vz IOz /=.
  unshelve econstructor. 
  { apply remove_vertex_graph => //; constructor. rewrite (oiso2_pIO (OIso2 i)) // in IOz. }
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
        rewrite (bool_irrelevance (fsetDl (valP [` p])) p1) addbb. done.
    + rewrite fsetD_bijE. apply: Q.
      move => q. apply/val_inj => /=. rewrite -(oiso2_input (OIso2 i)) /= vfun_bodyE. apply: p_inP. 
      move => r. set X := fsetDl _. by rewrite (bool_irrelevance X r).
    + rewrite fsetD_bijE. apply: Q.
      move => q. apply/val_inj => /=. rewrite -(oiso2_output (OIso2 i)) /= vfun_bodyE. apply: p_outP. 
      move => r. set X := fsetDl _. by rewrite (bool_irrelevance X r).
Defined.

Lemma oiso2_remove_vertexE (F G : pre_graph) (z : VT) (j : F ⩭2 G) A B x : 
  x \in vset (F \ z) -> @oiso2_remove_vertex F G z j A B x = j x.
Proof.
  case: j => isF isG j Vx. rewrite /= !vfun_bodyE fsetD_bijE.
  - rewrite !inE [_ \in vset G]valP andbT. rewrite vfun_bodyE val_eqE bij_eqLR bijK.
    by case/fsetD1P : (Vx).
  - move => p. by rewrite /= (vfun_bodyE _ (fsetDl Vx)). 
Qed.

(** Variant of the above with a linear pattern in the conclusion *)
Lemma oiso2_remove_vertex_ (F G : pre_graph) (z z' : VT) (j : F ⩭2 G) : 
  z \in vset F -> z \notin pIO F -> z' = j z ->
  F \ z ⩭2 G \ z'.
Proof. move => ? ? ->. exact: oiso2_remove_vertex. Qed.

Lemma oiso2_add_edge (F G : pre_graph) (i : F ⩭2 G) e1 e2 x y u v : 
  e1 \notin eset F -> e2 \notin eset G -> x \in vset F -> y \in vset F -> u ≡ v ->
  F ∔ [e1,x,u,y] ⩭2 G ∔ [e2,i x,v,i y].
Proof.
  case: i => isF isG i fresh_e1 fresh_e2 Vx Vy uv /=.
  have isF' : is_graph (F ∔ [e1, x, u, y]) by abstract exact: add_edge_graph'.
  have isG' : is_graph (G ∔ [e2, vfun_body i x, v, vfun_body i y]).
    by abstract (apply: add_edge_graph'; exact: (oiso2_vset (OIso2 i))).
  econstructor.
  apply: iso2_comp. apply: pack_add_edge'. assumption. 
  apply: iso2_comp (iso2_sym _). 2: apply: pack_add_edge';assumption. 
  apply add_edge2_iso'' with i; try assumption.
  all: abstract (by rewrite /vfun_of vfun_bodyE /= pack_fsval pack_vE).
Defined.

Lemma oiso2_remove_edges (F G : pre_graph) (i : F ⩭2 G) E E':
  E `<=` eset F ->
  E' = [fset efun_of i e | e in E] -> (F - E) ⩭2 (G - E').
Proof.
  case: i => isF isG i /= S EE'. econstructor.
  have X :  E' = [fset val (i.e x) | x : eset F & val x \in E].
  { subst. apply/fsetP => k. apply/imfsetP/imfsetP.
    - case => /= x Ix ->.  
      have Hx : x \in eset F. move: Ix. apply: (fsubsetP S). 
      exists (Sub x Hx) => //. by rewrite efun_bodyE. 
    - case => /= x. rewrite inE => Hx ->. exists (fsval x) => //. by rewrite efun_bodyE fsvalK. }
  have P e (p : e \in eset (F - E)) : val (i.e (Sub e (fsetDl p))) \in eset G `\` E'.
  { rewrite inE [_ \in eset G]valP andbT X. apply: contraTN (p).
    case/imfsetP => /= e0. rewrite inE => A. move/val_inj. move/(@bij_injective _ _ i.e) => ?; subst.
    by rewrite inE A. }
  iso2 i (fsetD_bij (f := i.e) X) (fun k => i.d (Sub (val k) (fsetDl (valP k)))).
  - split. (* the edge part is essentially the same as for del-vertex *)
    + move => [e p] b. 
      rewrite fsetD_bijE. apply P.
      move => q. apply/val_inj => /=. move: (fsetDl _) => He. move: (fsetDl _) => He'. move: (endpt_proof _ _) => Hv.
      rewrite [fsval _](_ : _ = (efun_of (OIso2 i) e)) ?(@oiso2_endpoint _ _ (OIso2 i)) //=.
      rewrite vfun_bodyE; first exact: endptP. rewrite edir_bodyE => Hv'. by rewrite (bool_irrelevance Hv Hv').
      by rewrite efun_bodyE (bool_irrelevance He He').
    + move => v. rewrite /=. rewrite -(oiso2_lv (OIso2 i)) /=. 2:apply: valP.
      by rewrite vfun_bodyE fsvalK.
    + move => [e p]. rewrite fsetD_bijE => [|q]; first exact: P.
      case/fsetDP : (p) => p1 p2. rewrite ![elabel _]/=. rewrite [i.d _]/=. 
      move: (oiso2_le (OIso2 i) p1) => H. apply: eqvb_transR H => //=. 
      rewrite edir_bodyE efun_bodyE. rewrite (bool_irrelevance (fsetDl p) p1). 
      rewrite (bool_irrelevance (fsetDl (valP [` p])) p1) addbb. done.
  - apply: val_inj => /=. rewrite -(oiso2_input (OIso2 i)) /= vfun_bodyE ?p_inP // => q.
    set q' := @p_inP _ _ _ _. by rewrite (bool_irrelevance q' q).
  - apply: val_inj => /=. rewrite -(oiso2_output (OIso2 i)) /= vfun_bodyE ?p_outP // => q.
    set q' := @p_outP _ _ _ _. by rewrite (bool_irrelevance q' q).
Defined.

Lemma oiso2_remove_edgesE (F G : pre_graph) (i : F ⩭2 G) E E' S EE' z :
  z \in vset F ->
  @oiso2_remove_edges F G i E E' S EE' z = i z.
Proof. 
  case: i EE' => isF isG j EE' Vx. by rewrite /= !vfun_bodyE. 
Qed.

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
  apply: iso2_comp. apply: pack_add_edge'. assumption.
  apply: iso2_comp (iso2_sym _). 2: apply: pack_add_edge'; try assumption.
  apply: (add_edge2_iso'' (h := i)). 
  abstract (by rewrite -Ix //= vfun_bodyE pack_fsval pack_vE).
  abstract (by rewrite -Iy //= vfun_bodyE pack_fsval pack_vE).
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


(** ** Preservation of open steps under isomorphisms *)

Lemma ostep_iso (F G H : pre_graph) : 
  ostep F G -> F ⩭2 H -> Σ U, ostep H U * (G ⩭2 U).
Proof with eauto with vset.
  case => {G}.
  - move => z Vz Iz zIO i. exists (H \ i z)%O. split.
    + apply ostep_v0. 
      * exact: oiso2_vset.
      * by rewrite oiso2_edges_at // Iz imfset0.
      * by rewrite -oiso2_pIO.
    + exact: oiso2_remove_vertex. 
  - move => x z e u Iz IOz arc_e xDz i.
    have [isF isH] : is_graph F /\ is_graph H by eauto with typeclass_instances.
    have Vz : z \in vset F by apply: oarc_vsetR arc_e.
    exists (H[adt i x <- [dom (u·lv H (i z))]] \ i z)%O. split.
    + apply: (ostep_v1 (e := efun_of i e)). 
      * by rewrite oiso2_edges_at // Iz imfset1. 
      * by rewrite -oiso2_pIO.
      * exact: oiso2_oarc arc_e.
      * apply: contra_neq xDz. apply: vfun_of_inj...
    + unshelve apply: oiso2_remove_vertex_. apply: oiso2_add_test...
      * by rewrite infer_testE  (rwT (oiso2_lv i Vz)). 
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
    + have @j : (F \ z)  ⩭2 (H \ i z). exact: oiso2_remove_vertex.
      have jE : {in vset (F \ z), j =1 i}. exact: oiso2_remove_vertexE.
      rewrite -![i x]jE -?[i y]jE //=. apply (oiso2_add_edge j).
      * by rewrite /= Iz maxn_fsetD.
      * rewrite in_fsetD negb_and negbK oiso2_edges_at //. 
        by rewrite Iz imfset1U imfset1 maxn_fset2.
      * rewrite in_fsetD1 xDz /=...
      * rewrite in_fsetD1 yDz /=...
      * move: (oiso2_lv i Vz) => X.
        Fail rewrite -X. (* why? *)
        apply: dot_eqv => //. apply dot_eqv => //. symmetry in X. etransitivity. exact X. done.
      * rewrite in_fsetD1 yDz /=...
      * rewrite in_fsetD1 xDz /=...
  - move => x e u arc_e i.
    have [isF isH] : is_graph F /\ is_graph H by eauto with typeclass_instances.
    exists ((H - [fset efun_of i e])[adt i x <- [1 ∥ le H (efun_of i e)]])%O. split.
    + apply: (ostep_e0 (e := efun_of i e)). exact: oiso2_oarc arc_e.
    + have @j : (F - [fset e]) ⩭2 (H - [fset efun_of i e]). 
      { apply: (oiso2_remove_edges (i := i)). 
        + abstract (rewrite fsub1set; by case: arc_e).
        + abstract (by rewrite imfset1). }
      have jE z (Vz : z \in vset F) : j z = i z. { exact: oiso2_remove_edgesE. }
      rewrite -!jE. apply: oiso2_add_test. 
      * rewrite /=. exact: oarc_vsetL arc_e.
      * case: arc_e {j jE} => E _.
        move:(oiso2_le i E). move: (efun_of i e) => e'. move: (edir_of i e) => b X. 
        symmetry. exact: eqvb_par1 X. 
      * rewrite /=. exact: oarc_vsetL arc_e.
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
      { apply: (oiso2_remove_edges (i := i)). 
        abstract (rewrite fsubUset !fsub1set; case: arc_e1 => -> _; by case: arc_e2).
        abstract (by rewrite imfset1U imfset1). }
      have jE z (Vz : z \in vset F) : j z = i z. { exact: oiso2_remove_edgesE. }
      rewrite -!jE. apply: oiso2_add_edge. 
      * by rewrite maxn_fsetD.
      * by rewrite in_fsetD negb_and negbK maxn_fset2.
      * rewrite /=...
      * rewrite /=...
      * done.
      * apply: oarc_vsetR arc_e1.
      * apply: oarc_vsetL arc_e1.
Qed.

Lemma osteps_iso (F G H: pre_graph): osteps F H -> F ⩭2 G -> exists U, osteps G U /\ inhabited (H ⩭2 U).
Proof.
  intro S. revert G. induction S as [F G FG|F G FG|F G FG|F G H FG IH GH IH']; intros F' FF'.
  - exists F'. split. by []. exists. transitivity F=>//. symmetry. apply eqvG_iso2L=>//. apply FF'.
  - exists F'. split=>//. destruct FG. exists. etransitivity. 2: eassumption.
    symmetry. apply add_edge_flip=>//. apply FF'. 
  - destruct (ostep_iso FG FF') as [U [F'U GU]]. exists U. split. by apply ostep_step. by exists.
  - destruct (IH _ FF') as [G' [F'G' [GG']]]. 
    destruct (IH' _ GG') as [H' [G'H' [HH']]]. 
    exists H'. split=>//. by transitivity G'. 
Qed.

Lemma vset_add_vertex (G : pre_graph) x a z : 
  z \in vset (G ∔ [x,a]) = (z == x) || (z \in vset G).
Proof. by rewrite /= !inE. Qed.

(** connecting the open step relation with the additive one on typed graphs *)

(** Transfer of a single packd step to the open step relation. We
first prove a slightly weaker statement with isomorphisms on both
sides of the open step. We then use preservation open steps under
isomorphisms to obtain the desired form of the lemma *)





Lemma remove_edgesD (G : pre_graph) E  : [disjoint eset G & E] -> G - E ≡G G.
Proof. move => D. split => //=. exact: fsetDidPl. Qed.

(** ** Packaged steps to open steps *) 

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
    + apply eqvG_iso2R... by rewrite add_vertexK // freshP.
  - (* V1 *) 
    move => G x u a. constructor. e2split.
    + apply: oiso2_trans. apply: open_add_edge. 
      apply: oiso2_add_edge. apply open_add_vertex. 
      2: instantiate (1 := fresh (eset (open G))). 5: instantiate (1 := u). 
      all: idtac... 
    + rewrite !open_add_vertexE. 
      set z := fresh _. set e := fresh _.
      apply: (@ostep_v1 _ _ (inj_v x) z e u). 
      * rewrite edges_at_add_edge edges_at_added_vertex ?fsetU0 //.
        exact: freshP.
      * rewrite !pIO_add. apply: pIO_fresh. exact: freshP.
      * exact: oarc_added_edge.
      * exact: inj_vNfresh.
    + set z := fresh _. set e := fresh _. rewrite /= updateE.
      etransitivity. 2: symmetry. 2: apply: open_add_test.
      eapply eqvG_iso2...
      * apply remove_vertex_graph => //=. 
        -- apply add_test_graph. by apply: add_edge_graph'; rewrite !inE ?eqxx ?inj_v_open.
        -- rewrite !pIO_add. constructor. apply: pIO_fresh. exact: freshP.
      * rewrite -remove_vertex_add_test add_edgeKr ?add_vertexK ?freshP //.
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
    + apply (@ostep_v2 _ _ (inj_v x) (inj_v y) z e1 e2 u v).
      all: rewrite ?pIO_add ?pIO_fresh ?inj_v_fresh ?freshP //.
      * by rewrite edges_at_add_edgeL edges_at_add_edge edges_at_added_vertex ?freshP ?fsetU0 1?fsetUC.
      * apply: oarc_add_edge => //. exact: oarc_added_edge.
      * exact: oarc_added_edge.
    + rewrite /= updateE. 
      have E : open G ∔ [z, a] ∔ [e1, inj_v x, u, z] ∔ [e2, z, v, inj_v y] \ z ≡G open G.
      { by rewrite add_edgeKl ?add_edgeKr ?add_vertexK ?freshP. }
      apply: oiso2_trans _ (oiso2_sym _). 2: apply: open_add_edge.
      unshelve apply: oiso2_add_edge'. apply: eqvG_iso2R E.
      1: { rewrite (sameE E). case: maxnP => _; rewrite ?freshP //. apply: freshP'. apply: fsubsetUr. }
      all: rewrite ?eqvG_iso2E ?freshP //=.
      all: by rewrite ?inE ?inj_v_open ?inj_vNfresh.
  - (* E0 *) move => G x u. 
    pose (e := fresh (eset (open G))).
    constructor. e2split.
    + apply: open_add_edge.
    + apply: (@ostep_e0 _ _ (inj_v x) e u). exact: oarc_added_edge.
    + rewrite /= update_eq.
      apply: oiso2_trans _ (oiso2_sym _). 2:apply: open_add_test.
      eapply eqvG_iso2R...
      rewrite add_edge_remove_edgesK ?inE //.
      by rewrite remove_edgesD // fdisjointX1 freshP. 
  - (* E2 *) 
    move => G x y u v. constructor. 
    pose (e1 := fresh (eset (open G))).
    pose (e2 := fresh (e1 |` eset (open G))).
    have ? : e1 != e2. 
    { apply: contraTneq (@freshP  (e1 |` eset (open G))). 
      rewrite -/e2 => <-. by rewrite !inE eqxx. }
    exists (open G ∔  [e1, inj_v x, u, inj_v y] ∔ [e2, inj_v x, v, inj_v y])%O.
    eexists; split; first split.
    + apply: oiso2_trans. apply: open_add_edge. 
      unshelve apply: oiso2_add_edge'.
      apply: open_add_edge. 
      all: by rewrite ?freshP ?inj_v_open ?open_add_edgeE.
    + apply: (@ostep_e2 _ _ (inj_v x) (inj_v y) e1 e2 u v) => //.
      * apply: oarc_add_edge => //. exact: oarc_added_edge.
      * exact: oarc_added_edge.
    + apply: oiso2_trans _ (oiso2_sym _). 2: apply: open_add_edge.
      unshelve apply: oiso2_add_edge'. 
      { apply eqvG_iso2R... rewrite !add_edge_remove_edgesK ?inE ?eqxx //.
        rewrite remove_edgesD // fdisjointXU !fdisjointX1 freshP freshP' //. apply: fsubsetUr. }
      1: by rewrite maxn_fsetD.
      all: by rewrite ?eqvG_iso2E ?freshP //= ?inj_v_open.
Qed.

Lemma ostep_of (F G : graph2) : 
  step F G -> exists G', [/\ inhabited (ostep (open F) G') & inhabited (G' ⩭2 open G)].
Proof.
  move/ostep_of' => [[F'] [G']  [[A B] C]].
  case: (ostep_iso B (oiso2_sym A)) => H [H1 H2]. 
  exists H. split => //. constructor. etransitivity. 2: apply: C. by symmetry.
Qed.

(** ** Open steps to packaged steps *)

(** We need one expansion lemma for every rule *)

(* TODO: why is [simple apply] unable to use the non-instantiated lemmas? *)
Hint Resolve (@in_vsetDV tm) (@in_vsetDE tm) (@in_vsetAE tm) (@in_vsetAV tm) (@in_vsetAV' tm) : vset.

Lemma expand_isolated (G : pre_graph) (z : VT) (isG : is_graph G) (isH : is_graph (G \ z)) :
    z \in vset G -> edges_at G z = fset0 -> pack G ≃2 pack (G \ z) ∔ lv G z.
Proof.
 move => Vz Iz. symmetry.
 apply: iso2_comp (iso2_sym _) _. apply: pack_add_vertex. instantiate (1 := z).
 - by rewrite !inE eqxx.
 - apply: eqvG_pack. by rewrite remove_vertexK // Iz remove_edges0.
Qed.


Lemma expand_pendant (G : pre_graph) (x z : VT) (e : ET) (isG : is_graph G) (Hz : z \notin pIO G) u :
    edges_at G z = [fset e] -> is_edge G e x u z -> x != z -> 
    pack G ≃2 pack (G \ z) ∔ lv G z ∔ [inl (pack_v x), u, inr tt].
Proof with eauto with vset.
  move => Iz arc_e xDz. 
  symmetry.  
  apply: iso2_comp. apply: add_edge2_iso. apply: iso2_sym. apply: pack_add_vertex. instantiate (1 := z).
  abstract (by rewrite !inE eqxx). rewrite /=. 
  set G' := ((_ \ _) ∔ [_,_])%O. set Sx := Sub _ _. set Sz := Sub _ _. 
  have -> : Sx = (pack_v G' x).
  { apply: val_inj => /=. rewrite !pack_vE /G' //... }
  have -> : Sz = (pack_v G' z). 
  { apply: val_inj => /=. rewrite !pack_vE //... by rewrite !inE eqxx. }
  apply: iso2_comp (iso2_sym _) _. unshelve eapply (pack_add_edge' (e := e)). 
  - apply: add_edge_graph'; rewrite /G'...  
  - by rewrite /G' /= in_fsetD Iz !inE eqxx.
  - rewrite /G' {}/Sz {}/Sx.  (* TODO: fix edge direction *)
    apply eqvG_pack. rewrite remove_vertexK ?Iz ?remove_edgeK //...
Qed.


Lemma expand_chain (G : pre_graph) (isG : is_graph G) (x y z : VT) (e1 e2 : ET) (Hz : z \notin pIO G) u v :
  edges_at G z = [fset e1; e2] -> e1 != e2 -> x != z -> y != z -> is_edge G e1 x u z -> is_edge G e2 z v y ->
  x \in vset G -> y \in vset G -> 
  pack G ≃2p pack (G \ z) ∔ lv G z ∔ [inl (pack_v x), u, inr tt] ∔ [inr tt, v, inl (pack_v y)].
Proof with eauto with vset.
  move => Iz e1De2 xDz yDz arc_e1 arc_e2 Vx Vy. symmetry. constructor.
  (* first extrusion *)
  apply: iso2_comp. apply: add_edge2_iso. apply: add_edge2_iso. 
  apply: iso2_sym. apply: (@pack_add_vertex (G \ z) _ z _). 
  abstract (by rewrite !inE eqxx). rewrite /=. 
  set G' := add_vertex _ _ _. set Sx := Sub _ _. set Sz := Sub _ _. set Sy := Sub _ _. 
  have -> : Sx = (pack_v G' x). apply: val_inj => /=. rewrite !pack_vE //... rewrite /G'...
  have -> : Sy = (pack_v G' y). apply: val_inj => /=. rewrite !pack_vE //... rewrite /G'...
  have -> : Sz = (pack_v G' z). apply: val_inj => /=. rewrite !pack_vE //... rewrite /G'...
  rewrite {}/G'. clear Sx Sy Sz. 
  (* second extrusion *)
  have isG' : is_graph ((G \ z) ∔ [z, lv G z] ∔ [e1, x, u, z]). 
  { apply: add_edge_graph'... }
  apply: iso2_comp. apply: add_edge2_iso. 
  apply: iso2_sym. eapply (pack_add_edge' (e := e1))... 
  { abstract( by rewrite inE negb_and negbK Iz !inE eqxx). }
  rewrite /=.
  have C k (Vk : k \in vset G) : 
    pack_v ((G \ z) ∔ [z, lv G z]) k = pack_v ((G \ z) ∔ [z, lv G z] ∔ [e1, x, u, z]) k.
  { apply: val_inj => /=. rewrite !pack_vE //; rewrite !inE Vk; by case: (k == z). }
  (* third extrusion *)
  have ? : z \in vset G by exact: is_edge_vsetR arc_e1.
  have E:  (G \ z) ∔ [z, lv G z] ∔ [e1, x, u, z] ∔ [e2, z, v, y] ≡G G.
  {   rewrite remove_vertexK // Iz fsetUC -remove_edges_edges !remove_edgeK //. 
      apply: is_edge_remove_edges arc_e1. by rewrite !inE e1De2. }
  rewrite !{}C //...
  apply: iso2_comp. apply: iso2_sym. eapply (pack_add_edge' (e := e2)).
  { by rewrite 3!inE Iz eq_sym !inE eqxx. }
  apply: eqvG_pack E. Unshelve. symmetry in E. exact: eqvG_graph E.
Qed.

Lemma expand_loop (G : pre_graph) (isG : is_graph G) (x : VT) (e : ET) u :
    is_edge G e x u x -> pack G ≃2 pack (G - [fset e]) ∔ [pack_v x, le G e, pack_v x].
Proof.
  move => edge_e. symmetry. 
  have E : (G - [fset e]) ∔ [e,x,le G e,x] ≡G G. 
  { rewrite remove_edgeK //. by case: edge_e => E [A B C]. }
  apply: iso2_comp (iso2_sym _) _. 
  unshelve eapply (pack_add_edge' (G := G - [fset e]) (e := e)).
  { symmetry in E. apply: eqvG_graph E. }
  - by rewrite /= !inE eqxx.
  - exact: eqvG_pack E.
Qed.

Lemma expand_parallel (G : pre_graph) (isG : is_graph G) (x y : VT) (e1 e2 : ET) u v :
  e1 != e2 -> is_edge G e1 x u y -> is_edge G e2 x v y ->
  pack G ≃2 pack (G - [fset e1; e2]) ∔ [pack_v x, u, pack_v y] ∔ [pack_v x, v, pack_v y].
Proof with eauto with vset.
  move => e1De2 edge_e1 edge_e2. symmetry.
  pose G' := ((G - [fset e1; e2]) ∔ [e1, x, u, y])%O.
  have isG' : is_graph G'. { apply: add_edge_graph'... }
  apply: iso2_comp. apply: add_edge2_iso. apply: iso2_sym. 
  unshelve eapply (pack_add_edge' (e := e1)).
  { abstract (by rewrite !inE eqxx). }
  rewrite /=. 
  have E : (G - [fset e1; e2]) ∔ [e1, x, u, y] ∔ [e2,x, v,y] ≡G G. 
  { rewrite fsetUC -remove_edges_edges !remove_edgeK //. apply: is_edge_remove_edges edge_e1. by rewrite inE. }
  apply: iso2_comp (iso2_sym _) _. 
  rewrite -/G'. set Cx := pack_v x. set Cy := pack_v y.
  have -> : Cx = (pack_v G' x). { rewrite /Cx /G' !pack_vE... move => ? ?. exact: val_inj. }
  have -> : Cy = (pack_v G' y). { rewrite /Cy /G' !pack_vE... move => ? ?. exact: val_inj. }
  unshelve eapply (pack_add_edge' (G := G') (e := e2)).
  - rewrite /G'. symmetry in E. apply: eqvG_graph E.
  - by rewrite !inE eqxx eq_sym (negbTE e1De2).
  - exact: eqvG_pack E.
Qed.

Lemma flip_edge_iso (G : pre_graph) (isG : is_graph G) e : pack G ≃2 pack (flip_edge G e).
Proof.
  iso2 bij_id bij_id (fun e' : edge (pack G) => val e' == e). 2-3: by apply: val_inj.
  split => //=.
  - move => e' b. apply/val_inj => /=.
    case: (altP (fsval e' =P e)) => /= [->|?]; by rewrite updateE.
  - move => e'. case: (altP (fsval e' =P e)) => /= [->|?]; by rewrite updateE.
Defined.
Arguments flip_edge_iso [G isG] e.
 
Lemma steps_of_ostep (G H : pre_graph) (isG : is_graph G) (isH : is_graph H) : 
  ostep G H -> steps (pack G) (pack H).
Proof with eauto with typeclass_instances.
  move => S. case: S isG isH => {H}.
  - move => z Vz Iz IOz isG isH. 
    have h : pack G ≃2 pack (G \ z) ∔ lv G z by exact: expand_isolated.
    apply: cons_step h _ (steps_refl _). by constructor.
  - move => x z e u He Hz arc_e xDz isG isH.
    (* resolve oarc *)
    wlog edge_e : G He Hz {arc_e} isG isH / is_edge G e x u z.
    { move => W. case: (oarc_cases arc_e) => {arc_e} edge_e; first exact: W.
      etransitivity. apply: iso_step. apply: (flip_edge_iso e).
      etransitivity. apply: W => //.
      - by rewrite ?edges_at_flip_edge.
      - exact: flipped_edge. 
      - apply: iso_step. apply: eqvG_pack. rewrite flip_edge_add_test flip_edgeK //=.
        by rewrite edges_at_test He !inE. }
    set a := lv G z in isH *.
    have xV : x \in vset G by eauto with vset.
    have x_remove_z : x \in vset (G \ z) by eauto with vset.
    have z_remove_z : z \notin vset (G \ z) by rewrite !inE eqxx.
    have h : pack G ≃2 pack (G \ z) ∔ a ∔ [inl (pack_v x), u, inr tt]. 
      { exact: expand_pendant He edge_e _. }
      apply: cons_step h _ _. constructor. 
      apply iso_step. apply: iso2_comp. apply: pack_add_test => //.
      apply: eqvG_pack. by rewrite remove_vertex_add_test.
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
      - apply: iso_step. apply: eqvG_pack. rewrite flip_edgeK //=.
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
      - apply: iso_step. apply: eqvG_pack. rewrite flip_edgeK //=.
        by rewrite Iz !inE eqxx. }
    set a := lv G z in isH *.
    have xV : x \in vset G by eauto with vset.
    have yV : y \in vset G by eauto with vset.
    have x_remove_z : x \in vset (G \ z) by eauto with vset.
    have y_remove_z : y \in vset (G \ z) by eauto with vset.
    have z_remove_z : z \notin vset (G \ z) by rewrite !inE eqxx.
    have [h] : pack G ≃2p 
             pack (G \ z) ∔ a ∔ [inl (pack_v x),u,inr tt] ∔ [inr tt,v,inl (pack_v y)].
    { apply: expand_chain. exact: Iz. all: try done. }
    apply: cons_step h _ _. constructor. 
    apply: iso_step. apply: iso2_comp (iso2_sym _) _. apply: (@pack_add_edge' (G \ z)).
    by rewrite /= Iz maxn_fsetD. reflexivity.
  - move => x e u arc_e isG isH.
    wlog edge_e : G u {arc_e} isG isH / is_edge G e x u x.
    { move => W. case: (oarc_cases arc_e) => {arc_e} edge_e; first apply: W edge_e.
      etransitivity. apply: iso_step. apply: (flip_edge_iso e).
      etransitivity. apply: (W _ u).
      - exact: flipped_edge. 
      - apply: iso_step. apply: eqvG_pack. rewrite flip_edgeK' ?inE ?eqxx //= updateE.
        rewrite (_ : [1∥(le G e)°] ≡ [1∥(le G e)]) //. exact: par_tst_cnv. }
    have h : pack G ≃2 pack (G - [fset e]) ∔ [pack_v x,le G e,pack_v x].
    { exact: expand_loop edge_e. }
    apply: cons_step h _ _. constructor. 
    apply: iso_step. apply: iso2_comp. apply: pack_add_test. 
    + by eauto with vset.
    + exact: pack_irrelevance.
  - move => x y e1 e2 u v e1De2 arc_e1 arc_e2 isF isH.
    wlog edge_e1 : G {arc_e1} arc_e2 isF isH / is_edge G e1 x u y.
    { move => W. case: (oarc_cases arc_e1) => {arc_e1} edge_e1; first exact: W.
      etransitivity. apply: iso_step. apply: (flip_edge_iso e1).
      etransitivity. unshelve eapply (W (flip_edge G e1)) => //.
      - abstract by apply: add_edge_graph' => /=;  eauto with vset. 
      - exact: oarc_flip_edge.
      - exact: flipped_edge. 
      - apply: iso_step. apply: eqvG_pack. rewrite flip_edgeK' //=.
        by rewrite !inE eqxx. }
    wlog edge_e2 : G {arc_e2} edge_e1 isF isH / is_edge G e2 x v y.
    { move => W. case: (oarc_cases arc_e2) => {arc_e2} edge_e2; first exact: W.
      etransitivity. apply: iso_step. apply: (flip_edge_iso e2).
      etransitivity. unshelve eapply (W (flip_edge G e2)) => //.
      - abstract by apply: add_edge_graph' => /=;  eauto with vset. 
      - exact: is_edge_flip_edge.
      - exact: flipped_edge. 
      - apply: iso_step. apply: eqvG_pack. rewrite flip_edgeK' //=.
        by rewrite !inE eqxx. }
    have h : pack G ≃2 pack (G - [fset e1; e2]) ∔ [pack_v x,u,pack_v y] ∔ [pack_v x,v,pack_v y].
    { exact: expand_parallel. }
    apply: cons_step h _ _. constructor. 
    apply: iso_step. apply: iso2_comp (iso2_sym _) _. apply: (@pack_add_edge' (G - [fset e1;e2])).
    + by rewrite maxn_fsetD.
    + reflexivity.
Qed.

Lemma steps_of (G H : pre_graph) (isG : is_graph G) (isH : is_graph H) : 
  osteps G H -> steps (pack G) (pack H).
Proof.
  move => S. elim: S isG isH => {G H} [G H h|G H GH|G H GH|G F H S IH1 _ IH2] isG isH.
  - apply: iso_step.
    apply (eqvG_iso2L isG) in h.
    apply: iso2_comp (iso2_comp (oiso2_iso h) _); apply: pack_irrelevance.
  - destruct GH. apply iso_step. apply iso_of_oiso. apply add_edge_flip=>//.
  - exact: steps_of_ostep.
  - have isF : is_graph F by apply: osteps_graph S. 
    by transitivity (pack F). 
Qed.


End PttdomGraphTheory.

