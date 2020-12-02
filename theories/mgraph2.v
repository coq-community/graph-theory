Require Import Setoid Morphisms.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries bij equiv.
Require Import setoid_bigop structures pttdom mgraph ptt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

(** * Two-pointed labelled multigraphs *)

(** 2pdom-operations on such graphs and proof that they form a 2pdom-algebra *)
(** local operations on such graphs (for the rewrite system) *)

(* TODO:
 - input/output as a function from [bool]?
 - recheck status of [unr/unl]
 *)

(* 2p-graphs  *)
Set Primitive Projections.
Record graph2 Lv Le :=
  Graph2 {
      graph_of:> graph Lv Le;
      input: graph_of;
      output: graph_of }.
Arguments input {_ _ _}, [_ _] G : rename.
Arguments output {_ _ _}, [_ _] G : rename.
Notation point G := (@Graph2 _ _ G).

Section s1.
    
Variables (Lv : Type) (Le : Type).
Notation graph := (graph Lv Le).
Notation graph2 := (graph2 Lv Le).
Local Notation point G := (@Graph2 Lv Le G).
Implicit Types (a : Lv) (u v : Le).


(* basic operations *)
Definition add_vertex2 (G: graph2) a := point (add_vertex G a) (unl input) (unl output).
Definition add_edge2 (G: graph2) (x y: G) u := point (add_edge G x y u) input output.

Notation "G ∔ a" := 
  (@add_vertex2 G a%CM) (at level 20, left associativity).
Notation "G ∔ [ x , u , y ]" := 
  (@add_edge2 G x y u) (at level 20, left associativity).


(* basic graphs *)
Definition unit_graph2 a := point (unit_graph a) tt tt.
Definition two_graph2 a b := point (two_graph a b) (inl tt) (inr tt). 
Definition edge_graph2 a u b := two_graph2 a b ∔ [inl tt, u, inr tt]. 

End s1.

Declare Scope graph2_scope.
Bind Scope graph2_scope with graph2.
Delimit Scope graph2_scope with G2.

Arguments add_edge2 [_ _] _ _ _ _. 
Notation "G ∔ [ x , u , y ]" := 
  (add_edge2 G x y u) (at level 20, left associativity) : graph2_scope.
Arguments add_vertex2 [_ _] _ _. 
Notation "G ∔ a" := 
  (add_vertex2 G a%CM) (at level 20, left associativity) : graph2_scope.

Arguments two_graph2 [Lv Le] _ _, [Lv] Le _ _.
Arguments unit_graph2 [Lv Le] _, [Lv] Le _.
Arguments edge_graph2 [Lv Le] _ _ _.

Section s1.
Variables (Lv : comMonoid) (Le : elabelType).
Notation LvS := (ComMonoid.sort Lv).
Notation LeS := (Elabel.sort Le).
Notation graph := (graph Lv Le).
Notation graph2 := (graph2 Lv Le).
Local Notation point G := (@Graph2 LvS LeS G).
Implicit Types (a : Lv) (u v : Le).
Local Open Scope cm_scope.


Definition add_vlabel2 (G: graph2) (x: G) a := point (add_vlabel G x a) input output.
Definition merge2 (G: graph2) (r: equiv_rel G) := point (merge G r) (\pi input) (\pi output).
Arguments merge2 _ _: clear implicits.
Notation "G [tst  x <- a ]" := 
  (@add_vlabel2 G x a) (at level 20, left associativity).
Notation merge2_seq G l := (merge2 G (eqv_clot l)).


(** ** Isomorphisms of 2p-graphs *)

Universe S2.
Set Primitive Projections.
Record iso2 (F G: graph2): Type@{S2} :=
  Iso2 { iso2_iso:> F ≃ G;
         iso2_input: iso2_iso input = input;
         iso2_output: iso2_iso output = output }.
Infix "≃2" := iso2 (at level 79).

Definition iso2_id (G: graph2): G ≃2 G.
Proof. by exists iso_id. Defined.
Hint Resolve iso2_id : core.         (* so that [by] gets it... *)

Definition iso2_sym F G: F ≃2 G -> G ≃2 F.
Proof.
  intro h. exists (iso_sym h). 
    by rewrite /= -(bijK h input) iso2_input. 
    by rewrite /= -(bijK h output) iso2_output. 
Defined.

Definition iso2_comp F G H: F ≃2 G -> G ≃2 H -> F ≃2 H.
Proof.
  move => f g.
  exists (iso_comp f g); by rewrite /= ?iso2_input ?iso2_output.
Defined.

Global Instance iso2_Equivalence: CEquivalence iso2.
Proof. split. exact iso2_id. exact iso2_sym. exact iso2_comp. Qed.

(* Prop version *)
Definition iso2prop (F G: graph2) := inhabited (F ≃2 G). 
Infix "≃2p" := iso2prop (at level 79).
Global Instance iso2prop_Equivalence: Equivalence iso2prop.
Proof.
  split.
  - by constructor.
  - intros G H [f]. constructor. by symmetry.
  - intros F G H [h] [k]. constructor. etransitivity; eassumption.
Qed.
HB.instance Definition g2_setoid := 
  Setoid_of_Type.Build (mgraph2.graph2 LvS LeS) iso2prop_Equivalence.

Tactic Notation "Iso2" uconstr(f) :=
  match goal with |- ?F ≃2 ?G => refine (@Iso2 F G f _ _)=>// end.

(* NOTE: used sparsely *)
Lemma iso_iso2 (F G: graph) (h: F ≃ G) (i o: F):
  point F i o ≃2 point G (h i) (h o).
Proof. now exists h. Defined.

(* NOTE: to be removed: the Iso2 tactic does the job... *)
Lemma iso_iso2' (F G: graph) (h: F ≃ G) (i o: F) (i' o': G):
  h i = i' -> h o = o' -> point F i o ≃2 point G i' o'.
Proof. intros. Iso2 h. Defined.


(* simple tactics for rewriting with isomorphisms at toplevel, in the lhs or in the rhs
   (used in place of setoid_rewrite or rewrite->, which are pretty slow, or just don't work) *)
Tactic Notation "irewrite" uconstr(L) := (eapply iso2_comp;[apply L|]); last 1 first.
Tactic Notation "irewrite'" uconstr(L) := eapply iso2_comp;[|apply iso2_sym, L].


(** ** 2pdom operations on graphs *)

(* parallel composition *)
Definition g2_par (F G: graph2) :=
  point (merge_seq (F ⊎ G) [::(unl input,unr input); (unl output,unr output)])
        (\pi (unl input)) (\pi (unr output)).
  (* merge2_seq (point (F ⊎ G) (inl input) (inr output)) *)
  (*            [::(inl input,inr input); (inl output,inr output)]. *)

(* sequential composition *)
Definition g2_dot (F G: graph2) :=
  point (merge_seq (F ⊎ G) [::(unl output,unr input)])
        (\pi (unl input)) (\pi (unr output)).
  (* merge2_seq (point (F ⊎ G) (inl input) (inr output)) *)
  (*            [::(inl output,inr input)]. *)

Definition g2_cnv (F: graph2) := point F output input.

Definition g2_dom (F: graph2) := point F input input.

Definition g2_one: graph2 := unit_graph2 1.

Definition g2_top: graph2 := two_graph2 1 1.

Definition g2_var u : graph2 := edge_graph2 1 u 1.

(* Note: would be nicer to prove that this is a 2p algebra (with top)
   and deduce automatically that this is a 2pdom  *)

HB.instance Definition g2_ops := 
  Ops_of_Type.Build (mgraph2.graph2 LvS LeS) g2_dot g2_par g2_cnv g2_dom g2_one g2_top.

(** Laws about low level operations ([union]/[merge]/[add_vertex]/[add_vlabel]/[add_edge]) 
    (mostly recasting the ones proved in [mgraph]) *)

(** isomorphisms about [unit_graph2] *)

Local Arguments unit_graph_iso [Lv Le x y] _, [Lv] Le [x y] _. 
Local Arguments add_vlabel_two [Lv Le] a b x c, [Lv] Le a b x c.

Global Instance unit_graph2_iso: CProper (eqv ==> iso2) (@unit_graph2 Lv Le).
Proof. intros a b e. Iso2 (unit_graph_iso e). Defined.

(** isomorphisms about [two_graph2] *)

Global Instance two_graph2_iso: CProper (eqv ==> eqv ==> iso2) (@two_graph2 Lv Le).
Proof. intros a b ab c d cd. Iso2 (union_iso (unit_graph_iso ab) (unit_graph_iso cd)). Defined.

(** isomorphisms about [two_vertex2] *)

Global Instance add_vertex2_iso: CProper (iso2 ==> eqv ==> iso2) (@add_vertex2 Lv Le).
Proof.
  move => F G FG u v uv.
  Iso2 (union_iso FG (unit_graph_iso uv))=>/=; rewrite /unl/=; f_equal; apply FG.
Defined.

(** isomorphisms about [add_edge2] *)

Lemma add_edge2_iso'' F G (h: F ≃2 G) x x' (ex: h x = x') y y' (ey: h y = y') u v (e: u ≡ v):
  F ∔ [x, u, y] ≃2 G ∔ [x', v, y'].
Proof. Iso2 (add_edge_iso'' ex ey e); apply h. Defined.

Lemma add_edge2_iso' F G (h: F ≃2 G) x u v y (e: u ≡ v): F ∔ [x, u, y] ≃2 G ∔ [h x, v, h y].
Proof. by eapply add_edge2_iso''. Defined.

Lemma add_edge2_iso F G (h: F ≃2 G) x u y: F ∔ [x, u, y] ≃2 G ∔ [h x, u, h y].
Proof. by apply add_edge2_iso'. Defined.

Lemma add_edge2_C F x u y z v t: F ∔ [x, u, y] ∔ [z, v, t] ≃2 F ∔ [z, v, t] ∔ [x, u, y].
Proof. Iso2 (add_edge_C _ _ _). Defined.

Lemma add_edge2_rev F x u v y (e: u ≡' v): F ∔ [x, u, y] ≃2 F ∔ [y, v, x].
Proof. Iso2 (add_edge_rev _ _ e). Defined.

Lemma add_edge2_vlabel F x a y u z: F [tst x <- a] ∔ [y, u, z] ≃2 F ∔ [y, u, z] [tst x <- a].
Proof. Iso2 (add_edge_vlabel _ _ _). Defined.

(** isomorphisms about [edge_graph2] *)

Global Instance edge_graph2_iso: CProper (eqv ==> eqv ==> eqv ==> iso2) (@edge_graph2 Lv Le).
Proof. intros a b ab u v uv c d cd. refine (add_edge2_iso' (two_graph2_iso ab cd) _ _ uv). Defined.

(** isomorphisms about [add_vlabel2] *)

Lemma add_vlabel2_iso'' F G (h: F ≃2 G) x x' (ex: h x = x') a b (e: a ≡ b): F [tst x <- a] ≃2 G [tst x' <- b].
Proof. Iso2 (add_vlabel_iso'' ex e); apply h. Defined.

Lemma add_vlabel2_iso' F G (h: F ≃2 G) x a b (e: a ≡ b): F [tst x <- a] ≃2 G [tst h x <- b].
Proof. by eapply add_vlabel2_iso''. Defined.

Lemma add_vlabel2_iso F G (h: F ≃2 G) x a: F [tst x <- a] ≃2 G [tst h x <- a].
Proof. by apply add_vlabel2_iso'. Defined.

Lemma add_vlabel2_C F x a y b: F [tst x <- a] [tst y <- b] ≃2 F [tst y <- b] [tst x <- a].
Proof. Iso2 (add_vlabel_C _ _). Defined.

Lemma add_vlabel2_unit a x b: unit_graph2 a [tst x <- b] ≃2 unit_graph2 (a⊗b).
Proof. Iso2 (add_vlabel_unit _ _). Defined.

Lemma add_vlabel2_unit' x b: unit_graph2 b ≃2 unit_graph2 1 [tst x <- b].
Proof. apply iso2_sym. irewrite add_vlabel2_unit. apply unit_graph2_iso. by rewrite monC monU. Defined.

Lemma add_vlabel2_two a b (x: unit+unit) c:
  two_graph2 a b [tst x <- c] ≃2 two_graph2 (if x then a⊗c else a) (if x then b else b⊗c).
Proof. Iso2 (add_vlabel_two _ _ _ _); by case x; case. Defined.

Lemma add_vlabel2_edge a u b (x: unit+unit) c:
  edge_graph2 a u b [tst x <- c] ≃2 edge_graph2 (if x then a⊗c else a) u (if x then b else b⊗c).
Proof. Iso2 (add_vlabel_edge _ _ _ _ _); by case x; case. Defined.

Lemma add_vlabel2_mon0 G x: G [tst x <- 1] ≃2 G.
Proof. Iso2 (add_vlabel_mon0 x). Defined.

(** isomorphisms about [merge] *)

(** note: h should be informative so that map_pairs can be simplified. *)
Lemma merge2_iso2 F G (h: F ≃2 G) l:
  merge2_seq F l ≃2 merge2_seq G (map_pairs h l).
Proof. Iso2 (merge_iso h l); by rewrite h_mergeE ?iso2_input ?iso2_output. Qed.

Lemma merge_iso2 (F G : graph) (h: F ≃ G) l (i o: F):
  point (merge_seq F l) (\pi i) (\pi o) ≃2
  point (merge_seq G (map_pairs h l)) (\pi (h i)) (\pi (h o)).
Proof. Iso2 (merge_iso h l); by rewrite h_mergeE. Defined.

Lemma merge2_surj (G: graph2) (r: equiv_rel G) (H: graph2) 
    (fv : G -> H) (fv': H -> G) (fe : bij (edge G) (edge H)) fd :
  (forall x y, reflect (kernel fv x y) (r x y)) ->
  cancel fv' fv ->
  is_hom fv fe fd ->
  fv input = input -> fv output = output ->
  merge2 G r ≃2 H.
Proof.
  intros H1 H2 H3 I O.
  Iso2 (merge_surj H1 H2 H3); by rewrite merge_surjE.
Defined.

Lemma merge_same (F : graph) (h k: equiv_rel F) (i i' o o': F):
  (h =2 k) ->
  h i i' ->
  h o o' ->
  point (merge F h) (\pi i) (\pi o) ≃2 point (merge F k) (\pi i') (\pi o').
Proof.
  intros H Hi Ho.
  Iso2 (merge_same' H);
    rewrite merge_same'E =>//;
    apply /eqquotP; by rewrite <- H. 
Defined.

Lemma merge_same' (F : graph) (h k: equiv_rel F) (i o: F):
  (h =2 k) ->
  point (merge F h) (\pi i) (\pi o) ≃2 point (merge F k) (\pi i) (\pi o).
Proof. intros. by apply merge_same. Defined.

Lemma merge2_same (F : graph) (h k: equiv_rel F) (i i' o o': F):
  (h =2 k) -> h i i' -> h o o' -> merge2 (point F i o) h ≃2 merge2 (point F i' o') k.
Proof. apply merge_same. Qed.

Lemma merge2_same' (F : graph2) (h k: equiv_rel F):
  (h =2 k) -> merge2 F h ≃2 merge2 F k.
Proof. intro. by apply merge2_same. Qed.

Lemma merge_nothing (F: graph) (h: pairs F) (i o: F):
  List.Forall (fun p => p.1 = p.2) h ->
  point (merge_seq F h) (\pi i) (\pi o) ≃2 point F i o.
Proof. intros H. Iso2 (merge_nothing H); by rewrite merge_nothingE. Defined.

Lemma merge2_nothing (F: graph2) (h: pairs F):
  List.Forall (fun p => p.1 = p.2) h ->
  merge2_seq F h ≃2 F.
Proof. destruct F. apply merge_nothing. Defined.


Lemma merge_merge (G: graph) (h k: pairs G) (k': pairs (merge_seq G h)) (i o: G):
  k' = map_pairs (pi (eqv_clot h)) k ->
  point (merge_seq (merge_seq G h) k') (\pi (\pi i)) (\pi (\pi o))
≃2 point (merge_seq G (h++k)) (\pi i) (\pi o).
Proof. intro K. Iso2 (merge_merge_seq K); by rewrite /=merge_merge_seqE. Qed.

Lemma merge2_merge (G: graph2) (h k: pairs G) (k': pairs (merge_seq G h)):
  k' = map_pairs (pi (eqv_clot h)) k ->
  merge2_seq (merge2_seq G h) k' ≃2 merge2_seq G (h++k).
Proof. apply merge_merge. Qed.


Lemma merge_union_K_l (F K: graph) (i o: F+K) (h: pairs (F+K)) (k: K -> F)
      (kv: forall x: K, vlabel x = 1)
      (ke: edge K -> False)
      (kh: forall x: K, unr x = unl (k x) %[mod (eqv_clot h)]):
  point (merge_seq (F ⊎ K) h) (\pi i) (\pi o)
≃2 point (merge_seq F (union_K_pairs h k)) (\pi (sum_left k i)) (\pi (sum_left k o)).
Proof. Iso2 (merge_union_K kv kh ke)=>/=; by rewrite ?merge_union_KE. Defined.

Lemma merge2_add_edge (G: graph2) (r: equiv_rel G) x u y: merge2 (G ∔ [x, u, y]) r ≃2 merge2 G r ∔ [\pi x, u, \pi y].
Proof. Iso2 (merge_add_edge _ _ _ _); by rewrite merge_add_edgeE. Defined.

Lemma merge2_add_vlabel (G: graph2) (r: equiv_rel G) x a: merge2 (G [tst x <- a]) r ≃2 merge2 G r [tst \pi x <- a].
Proof. Iso2 (merge_add_vlabel _ _ _); by rewrite merge_add_vlabelE. Defined.

(** ** 2p-graphs form a 2p-algebra *)

(* TODO: for now the 2p laws are all proved in Type [iso2], 
   because some of them could be useful in Type in open.v and reduction.v
   (simple ones like commutativity to get symmetry reasonning, 
    but also CProper)
   we might want to downgrade some of them to Prop [iso2prop]
 *)

Local Close Scope cm_scope.

Lemma par2C (F G: graph2): F ∥ G ≃2 G ∥ F.
Proof.
  irewrite (merge_iso2 (union_C F G)) =>/=.
  apply merge_same. apply eqv_clot_eq; leqv. eqv. eqv. 
Qed.

Lemma par2top (F: graph2): F ∥ top ≃2 F. 
Proof.
  irewrite (merge_union_K_l (K:=g2_top) _ _ (k:=fun b => if b then input else output))=>/=; try by repeat case.
  apply merge2_nothing. 
  by repeat constructor. 
  repeat case; apply /eqquotP; eqv. 
Qed.

Lemma par2A (F G H: graph2): F ∥ (G ∥ H) ≃2 (F ∥ G) ∥ H.
Proof.
  irewrite (merge_iso2 (union_merge_r _ _)).
  rewrite /map_pairs/map 2!union_merge_rEl 2!union_merge_rEr /=.
  irewrite (merge_merge (G:=F ⊎ (G ⊎ H))
                        (k:=[::(unl input,unr (unl input)); (unl output,unr (unr output))]))=>//.
  irewrite' (merge_iso2 (union_merge_l _ _)).
  rewrite /map_pairs/map 2!union_merge_lEl 2!union_merge_lEr /=.
  irewrite' (merge_merge (G:=(F ⊎ G) ⊎ H)
                              (k:=[::(unl (unl input),unr input); (unl (unr output),unr output)]))=>//.
  irewrite (merge_iso2 (union_A _ _ _)).
  apply merge_same'. rewrite /unl/unr/=.
  set a := inl _. set (b := inl _). set (c := inl _). set (d := inl _). set (e := inr _). set (f := inr _).
  apply eqv_clot_eq=>/=.  
   constructor. apply eqv_clot_trans with c; eqv. 
   constructor. apply eqv_clot_trans with b; eqv.
   constructor. eqv.
   constructor. apply eqv_clot_trans with b; eqv.
   leqv.

   constructor. eqv. 
   constructor. apply eqv_clot_trans with f; eqv. 
   constructor. apply eqv_clot_trans with a; eqv. 
   leqv. 
Qed.

Lemma dot2unit_r (G: graph2) a: G · unit_graph2 a ≃2 G [tst output <- a].
Proof.
  (* compositional proof *)
  (* a bit messy because [merge_union_K] only allows us to kill mon0-labelled vertices
     (a more general version of [merge_union_K] is possible, but requires updating the 
     labels of several vertices at once *)
  irewrite (merge_iso2 (union_iso iso_id (add_vlabel2_unit' output _))). simpl.
  etransitivity. refine (merge_iso2 (union_add_vlabel_r _ _ _) _ _ _). simpl.
  etransitivity. refine (iso_iso2 (merge_add_vlabel _ _ _) _ _). simpl.
  etransitivity. refine (iso_iso2 (add_vlabel_iso (merge_union_K_l (K:=g2_one) (unl input) (unl output) (k:=fun _ => output) _ _ _) _ _) _ _)=>//. 
  case; apply /eqquotP; eqv. simpl. 
  rewrite !merge_union_KE/=. 
  etransitivity. refine (add_vlabel2_iso (merge2_nothing _) _ _).
  repeat (constructor=>//).
  destruct G=>/=. by rewrite merge_nothingE. 
Qed.

Lemma dot2unit_r' (G: graph2) a: G · unit_graph2 a ≃2 G [tst output <- a].
Proof.
  (* global proof, via surjective homomorphism *)
  unshelve Iso2
   (@merge_surj _ _
     (G ⊎ unit_graph2 a) _
     (G [tst output <- a])
     (fun x => match x with inl y => y | inr tt => output end)
     (fun x => unl x)
     sumxU xpred0 _ _ _).
  4,5: by rewrite merge_surjE.
  - apply kernel_eqv_clot.
    * by constructor.
    * case=>[x|[]]; case=>[y|[]]=>//->; eqv. 
  - by []. 
  - split. 
    + by move=> [e|[]] b.
    + move=>x/=. rewrite big_sumType big_pred1_eq. 
    case: (altP (x =P output)) => [?|xDo]; subst.
    * by rewrite (big_pred1 tt) => [|[]]; rewrite 1?monC /= ?eqxx.
    * rewrite big_pred0 ?monU // => [[]]. by rewrite eq_sym (negbTE xDo).
    + by case.  
Qed.

(* [dot2one] follows from [dot2unit_r] *)
Lemma dot2one (F: graph2): F · 1 ≃2 F.
Proof. irewrite dot2unit_r. apply add_vlabel2_mon0. Qed.

(* ... but also has a reasonable direct proof *)
Lemma dot2one' (F: graph2): F · 1 ≃2 F.
Proof.
  irewrite (merge_union_K_l (K:=g2_one) _ _ (k:=fun _ => output))=>//.
  apply merge2_nothing.
  repeat (constructor =>//).
  intros []; apply /eqquotP; eqv.
Qed.


(* half of associativity *)
Lemma dot2Aflat (F G H: graph2):
  F·(G·H) ≃2 
  point (merge_seq (F ⊎ (G ⊎ H)) 
                   [::(unr (unl output),unr (unr input));
                      (unl output,unr (unl input))]) 
        (\pi unl input) (\pi unr (unr output)).
Proof.
  irewrite (merge_iso2 (union_merge_r _ _)).
  rewrite /map_pairs/map 2!union_merge_rEl 2!union_merge_rEr /fst/snd.
  irewrite (merge_merge (G:=F ⊎ (G ⊎ H))
                              (k:=[::(unl output,unr (unl input))])) =>//.
Qed.

Lemma dot2A (F G H: graph2): F · (G · H) ≃2 (F · G) · H.
Proof.
  irewrite dot2Aflat. 
  irewrite' (merge_iso2 (union_merge_l _ _)).
  rewrite /map_pairs/map 2!union_merge_lEl 2!union_merge_lEr /fst/snd.
  irewrite' (merge_merge (G:=(F ⊎ G) ⊎ H)
                              (k:=[::(unl (unr output),unr input)])) =>//. 
  irewrite (merge_iso2 (union_A _ _ _)).
  apply merge_same'=>/=.
  apply eqv_clot_eq; leqv.
Qed.

Lemma cnv2I (F: graph2): F°° ≃2 F.
Proof. by case F. Qed.

Lemma cnv2par (F G: graph2): (F ∥ G)° ≃2 F° ∥ G°.
Proof.
  apply merge_same. apply eqv_clot_eq; leqv. eqv. eqv.
Qed.

Lemma cnv2dot (F G: graph2): (F · G)° ≃2 G° · F°.
Proof.
  irewrite (merge_iso2 (union_C F G)).
  apply merge_same'=>/=. apply eqv_clot_eq; leqv.
Qed.

Lemma par2dot F G: input F = output -> input G = output -> F ∥ G ≃2 F · G.
Proof.
  intros HF HG. apply merge2_same; rewrite !HF !HG //.
  apply eqv_clot_eq; leqv.
Qed.

Lemma par2oneone: 1 ∥ 1 ≃2 1.
Proof. etransitivity. apply par2dot=>//. apply dot2one. Qed.

Lemma dom2E (F: graph2): dom F ≃2 1 ∥ (F · top).
Proof.
  symmetry. 
  irewrite par2C.
  irewrite (merge_iso2 (union_merge_l _ _)).
  rewrite /map_pairs/map 2!union_merge_lEl 1!union_merge_lEr /=.
  irewrite (merge_merge (G:=(F ⊎ g2_top) ⊎ g2_one)
                              (k:=[::(inl (inl input),inr tt); (inl (inr (inr tt)),inr tt)])) =>//.
  irewrite (merge_iso2 (iso_sym (union_A _ _ _))).
  irewrite (merge_union_K_l (K:=g2_top ⊎ g2_one) _ _ 
                            (k:=fun x => match x with inl (inl tt) => output | _ => input end))=>/=.
  apply merge_nothing. 
  repeat (constructor =>//=).
  by intros [[]|].
  by intros [[]|].
  repeat case; apply /eqquotP; try eqv.
  apply eqv_clot_trans with (inr (inr tt)); eqv. 
Qed.

Lemma g2_A10 (F G: graph2): 1 ∥ F·G ≃2 dom (F ∥ G°).
Proof.
  irewrite (par2C 1).
  irewrite (merge_iso2 (union_merge_l _ _)).
  rewrite /map_pairs/map 2!union_merge_lEl 1!union_merge_lEr /fst/snd.
  irewrite (merge_merge (G:=(F ⊎ G) ⊎ g2_one)
                              (k:=[::(unl (unl input),inr tt); (unl (unr output),inr tt)])) =>//.
  irewrite (merge_union_K_l (F:=F ⊎ G) _ _ (k:=fun x => unl input))=>//=.
  2: by intros []; apply /eqquotP; simpl; eqv.
  apply merge_same; simpl.
  apply eqv_clot_eq; simpl; leqv.
  eqv.
  eqv.
Qed.

(* TOFIX: topL should be obtained from topR by duality *)
Lemma topL (F: graph2): 
  top·F ≃2 point (F ⊎ unit_graph 1%CM) (@unr _ _ F (unit_graph _) tt) (unl output).
Proof.
  irewrite (merge_iso2 (union_C _ _))=>/=.
  etransitivity. refine (merge_iso2 (union_A _ _ _) _ _ _)=>/=.
  irewrite (merge_union_K_l (F:=F ⊎ _) _ _ (k:=fun x => unl input))=>//=.
  apply merge_nothing. by constructor.
  intros []. apply /eqquotP. eqv.
Qed.

Lemma topR (F: graph2): 
  F·top ≃2 point (F ⊎ unit_graph 1%CM) (unl input) (@unr _ _ F (unit_graph _) tt).
Proof.
  irewrite (merge_iso2 (union_iso iso_id (union_C _ _))).
  irewrite (merge_iso2 (union_A _ _ _)).
  irewrite (merge_union_K_l (F:=F ⊎ _) _ _ (k:=fun x => unl output))=>//=.
  apply merge_nothing. by constructor.
  case. apply /eqquotP. eqv.
Qed.

Lemma g2_A11 (F: graph2): F·top ≃2 dom F·top.
Proof. irewrite topR. symmetry. by irewrite topR. Qed.

Lemma g2_A12' (F G: graph2): input F = output F -> F·G ≃2 F·top ∥ G.
Proof.
  intro H.
  irewrite' (merge_iso2 (union_merge_l _ _)).
  rewrite /map_pairs/map 2!union_merge_lEl 2!union_merge_lEr /=.
  irewrite' (merge_merge (G:=(F ⊎ g2_top) ⊎ G)
                              (k:=[::(inl (inl input),inr input);(inl (inr (inr tt)),inr output)])) =>//.
  irewrite' (merge_iso2 (union_C (_ ⊎ _) _)).
  irewrite' (merge_iso2 (union_A _ _ _))=>/=.
  irewrite' (merge_union_K_l (F:=G ⊎ F) (K:=g2_top) _ _ 
                             (k:=fun x => if x then unr input else unl output))=>//.
  2: by case. 2: by repeat case; apply /eqquotP; rewrite H; eqv.
  irewrite (merge_iso2 (union_C F G)) =>/=.
  apply merge_same'. rewrite H. apply eqv_clot_eq; leqv.
  repeat case=>//=; rewrite H; apply /eqquotP; eqv. 
Qed.

Lemma g2_A12 (F G: graph2): (F ∥ 1)·G ≃2 (F ∥ 1)·top ∥ G.
Proof.
  apply g2_A12'.
  apply /eqquotP. apply eqv_clot_trans with (inr tt); eqv.
Qed.

(** these two laws are skipped since we go through 2p algebra *)

(*
Lemma g2_A13 (F G: graph2): dom(F·G) ≃2 dom(F·dom G).
Proof. reflexivity. Qed.

Lemma g2_A14' (F G H: graph2): @input F = output -> F·(G∥H) ≃2 F·G ∥ H.
Proof.
  intro E. 
  irewrite (merge_iso2 (union_merge_r _ _)).
  rewrite /map_pairs/map 2!union_merge_rEl 2!union_merge_rEr /=.
  irewrite (merge_merge (G:=F ⊎ (G ⊎ H))
                        (k:=[::(unl output,unr (unl input))]))=>//.
  irewrite' (merge_iso2 (union_merge_l _ _)).
  rewrite /map_pairs/map 2!union_merge_lEl 2!union_merge_lEr /=.
  irewrite' (merge_merge (G:=(F ⊎ G) ⊎ H)
                              (k:=[::(unl (unl input),unr input); (unl (unr output),unr output)]))=>//.
  irewrite (merge_iso2 (union_A _ _ _)).
  apply merge_same'. rewrite /unl/unr/=E.
  set a := inl _. set (b := inl _). set (c := inl _). set (e := inr _). set (f := inr _).
  apply eqv_clot_eq=>/=.  
   constructor=>/=. apply eqv_clot_trans with c; eqv.
   leqv. 
   constructor. eqv. 
   constructor=>/=. apply eqv_clot_trans with a; eqv. 
   leqv. 
Qed.

Lemma g2_A14 (F G H: graph2): dom F·(G∥H) ≃2 dom F·G ∥ H.
Proof. by apply g2_A14'. Qed.
 *)

Global Instance dot_iso2: CProper (iso2 ==> iso2 ==> iso2) g2_dot.
Proof.
  intros F F' f G G' g. rewrite /g2_dot.
  irewrite (merge_iso2 (union_iso f g))=>/=.
  apply merge_same; by rewrite /= ?iso2_input ?iso2_output. 
Qed.  

Global Instance par_iso2: CProper (iso2 ==> iso2 ==> iso2) g2_par.
Proof.
  intros F F' f G G' g. rewrite /g2_par.
  irewrite (merge_iso2 (union_iso f g))=>/=.
  apply merge_same; by rewrite /= ?iso2_input ?iso2_output. 
Qed.

Global Instance cnv_iso2: CProper (iso2 ==> iso2) g2_cnv.
Proof. intros F F' f. eexists; apply f. Qed.

Global Instance dom_iso2: CProper (iso2 ==> iso2) g2_dom.
Proof. intros F F' f. eexists; apply f. Qed.

(** 2p-graphs form a 2pdom algebra (Proposition 5.2) *)
Definition g2_ptt: Ptt_of_Ops.axioms_ g2_setoid g2_ops.
  refine (Ptt_of_Ops.Build (mgraph2.graph2 LvS LeS) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
     abstract apply CProper2, dot_iso2. 
     abstract apply CProper2, par_iso2. 
     abstract apply CProper1, cnv_iso2. 
     abstract (exists; apply dom2E).
     abstract (exists; apply par2A).
     abstract (exists; apply par2C).
     abstract (exists; apply dot2A).
     abstract (exists; apply dot2one).
     abstract (exists; apply cnv2I).
     abstract (exists; apply cnv2par).
     abstract (exists; apply cnv2dot).
     abstract (exists; apply par2oneone).
     abstract (exists; apply g2_A10).
     abstract (exists; apply g2_A11).
     abstract (exists; apply g2_A12).
Defined.
HB.instance (mgraph2.graph2 LvS LeS) g2_ptt. 
HB.instance (mgraph2.graph2 LvS LeS) (pttdom_of_ptt graph2_is_a_Ptt).

(** ** additional laws required for the completeness proof *)

(* additional lemmas needed in reduction.v *)
Local Open Scope cm_scope.

Lemma dot2unit_l (G: graph2) a: unit_graph2 a · G ≃2 G [tst input <- a].
Proof.
  irewrite (iso2_sym (cnv2I _)). 
  irewrite' (iso2_sym (cnv2I _)).
  apply cnv_iso2.
  irewrite cnv2dot. 
  apply dot2unit_r.
Qed.

Lemma par2unitunit a b: unit_graph2 a ∥ unit_graph2 b ≃2 unit_graph2 (a⊗b).
Proof.
  etransitivity. apply par2dot=>//.
  etransitivity. apply dot2unit_r.
  apply add_vlabel2_unit.
Qed.

Lemma par2edgeunit a u b c: 
  edge_graph2 a u b ∥ unit_graph2 c ≃2 unit_graph2 (a⊗(b⊗c)) ∔ [tt, u, tt].
Proof.
  unshelve Iso2
   (@merge_surj _ _ (edge_graph2 a u b ⊎ unit_graph2 c) _ (unit_graph2 (a⊗(b⊗c)) ∔ [tt, u, tt])
     (fun _ => tt)
     (fun _ => inr tt)
     (bij_comp sumxU (option_bij sumxU)) xpred0 _ _ _).
  - apply kernel_eqv_clot.
    + by repeat constructor.
    + (repeat case)=>//=_; try eqv; apply eqv_clot_trans with (inr tt); eqv.
  - by case. 
  - split.
    + move=>d. by repeat case. 
    + repeat case=>//=. by rewrite eqxx /= !big_sumType !big_unitType monA.
    + by repeat case.
Qed.


(** lemmas for term extraction *)

(** Extensionality lemma for [subgraph_for], the general construction
underlying bag and interval subgraphs used in the extraction
function. *)
Lemma subgraph_for_iso (G : graph2) V1 V2 E1 E2 i1 i2 o1 o2
  (C1 : @consistent _ _ G V1 E1) (C2: consistent V2 E2) :
  V1 = V2 -> E1 = E2 -> val i1 = val i2 -> val o1 = val o2 ->
  point (subgraph_for C1) i1 o1 ≃2 point (subgraph_for C2) i2 o2.
Proof.
  move => eq_V eq_E eq_i eq_o. subst.
  move/val_inj : eq_i => ->. move/val_inj : eq_o => ->.
  unshelve Iso2 (@Iso _ _ (subgraph_for C1) (subgraph_for C2) bij_id bij_id xpred0 _).
  split=>//e b//=. by apply val_inj. 
Qed.

(** recognizing the full subgraph *)
Lemma iso2_subgraph_forT (G : graph2) (V : {set G}) (E : {set edge G}) (con : consistent V E) i o :
  (forall x, x \in V) -> (forall e, e \in E) -> val i = input -> val o = output ->
  point (subgraph_for con) i o ≃2 G. 
Proof.
  move => HV HE Hi Ho.
  have ? : V = [set: G] by apply/setP => z; rewrite inE HV.
  have ? : E = [set: edge G] by apply/setP => z; rewrite inE HE.
  subst.
  transitivity (point (subgraph_for (@consistentTT _ _ G)) i o).
  - exact: subgraph_for_iso.
  - irewrite (iso_iso2 (iso_subgraph_forT _)). rewrite /= Ho Hi. by case G. 
Qed.

End s1. 

Arguments input {_ _ _}.
Arguments output {_ _ _}.
Arguments g2_top {_ _}.
Arguments g2_one {_ _}.
Arguments add_vlabel2 [_ _] _ _ _. 
Arguments merge2 [_ _] _ _. 

Notation IO := [set input;output].

Notation "G [tst  x <- a ]" := 
  (add_vlabel2 G x a%CM) (at level 20, left associativity) : graph2_scope.
Notation merge2_seq G l := (merge2 G (eqv_clot l)).

Arguments iso2 {_ _}.
Arguments iso2prop {_ _}.
Arguments iso2_id {_ _ _}.

Infix "≃2" := iso2 (at level 79).
Infix "≃2p" := iso2prop (at level 79).
Hint Resolve iso2_id : core.   (* so that [by] gets it... *)

Tactic Notation "Iso2" uconstr(f) :=
  match goal with |- ?F ≃2 ?G => refine (@Iso2 _ _ F G f _ _)=>// end.

(* temporary *)
Notation add_test := add_vlabel2 (only parsing).
Notation add_test_cong := add_vlabel2_iso' (only parsing).


(** ** Relabeling Graphs *)
(* used to move from letter-labeled graphs to term-labeled graphs (Lemma 5.3) *)
(* (i.e., the [g2_pttdom] construction is functorial) *)
Section h.
  Variable (Lv1 Lv2 : comMonoid) (Le1 Le2 : elabelType).
  Variable fv: Lv1 -> Lv2.
  Variable fe: Le1 -> Le2.
  Definition relabel (G: graph Lv1 Le1): graph Lv2 Le2 :=
    Graph (@endpoint _ _ G) (fv \o (@vlabel _ _  G)) (fe \o (@elabel _ _ G)).
  Hypothesis Hfv: Proper (eqv ==> eqv) fv.
  Hypothesis Hfe: forall b, Proper (eqv_ b ==> eqv_ b) fe.
  Global Instance relabel_iso: CProper (iso ==> iso) relabel.
  Proof.
    intros G H h. Iso h h.e h.d. split.
    - apply h.
    - intro. apply Hfv, h.
    - intro. apply Hfe, h.
  Defined.
  Lemma relabel_union F G: relabel (F ⊎ G) ≃ relabel F ⊎ relabel G.
  Proof. Iso bij_id bij_id xpred0. by split=>//; case. Defined.
  Hypothesis Hfvmon2: forall a b, fv (a ⊗ b)%CM ≡ (fv a ⊗ fv b)%CM.
  Hypothesis Hfvmon0: fv 1%CM ≡ 1%CM.
  Lemma relabel_merge F r: relabel (merge F r) ≃ merge (relabel F) r.
  Proof.
    Iso bij_id bij_id xpred0.
    split=>//= v. 
    elim/big_rec2 : _ => [|i y1 y2 _ ->]; by [rewrite ?Hfvmon2|symmetry].
  Defined.
  Lemma relabel_add_edge F x y u: relabel (F ∔ [x, u, y]) ≃ relabel F ∔ [x, fe u, y].
  Proof.
    Iso bij_id bij_id xpred0. by split=>//; case.
  Defined.    
  Lemma relabel_unit a: relabel (unit_graph a) ≃ unit_graph (fv a).
  Proof. Iso bij_id bij_id xpred0. by split. Defined.
  Lemma relabel_two a b: relabel (two_graph a b) ≃ two_graph (fv a) (fv b).
  Proof. etransitivity. apply relabel_union. apply union_iso; apply relabel_unit. Defined.
  Lemma relabel_edge a u b: relabel (edge_graph a u b) ≃ edge_graph (fv a) (fe u) (fv b).
  Proof. etransitivity. apply relabel_add_edge. by apply (add_edge_iso'' (h:=relabel_two _ _)). Defined.

  Definition relabel2 (G: graph2 Lv1 Le1): graph2 Lv2 Le2 :=
    point (relabel G) input output.
  Global Instance relabel2_iso: CProper (iso2 ==> iso2) relabel2.
  Proof. intros G H h. Iso2 (relabel_iso h); apply h. Defined.
  Lemma relabel2_dot (F G: graph2 Lv1 Le1): relabel2 (F · G) ≃2 relabel2 F · relabel2 G.
  Proof.
    etransitivity. apply (iso_iso2 (relabel_merge _)).
    refine (merge_iso2 (relabel_union F G) _ _ _).
  Qed.
  Lemma relabel2_par (F G: graph2 Lv1 Le1): relabel2 (F ∥ G) ≃2 relabel2 F ∥ relabel2 G.
  Proof.
    etransitivity. apply (iso_iso2 (relabel_merge _)).
    refine (merge_iso2 (relabel_union F G) _ _ _).
  Qed.
  Lemma relabel2_cnv (F: graph2 Lv1 Le1): relabel2 (F°) ≃2 (relabel2 F)°.
  Proof. reflexivity. Qed.
  Lemma relabel2_dom (F: graph2 Lv1 Le1): relabel2 (dom F) ≃2 dom (relabel2 F).
  Proof. reflexivity. Qed.
  Lemma relabel2_one: relabel2 1 ≃2 1.
  Proof.
    transitivity (unit_graph2 Le2 (fv 1%CM)). Iso2 (relabel_unit _).
    apply unit_graph2_iso, Hfvmon0.
  Qed.
  Lemma relabel2_top: relabel2 g2_top ≃2 g2_top.
  Proof.
    transitivity (two_graph2 Le2 (fv 1%CM) (fv 1%CM)). Iso2 (relabel_two _ _).
    apply two_graph2_iso; apply Hfvmon0.
  Qed.
  Lemma relabel2_var a: relabel2 (g2_var _ a) ≃2 g2_var _ (fe a).
  Proof.
    transitivity (edge_graph2 (fv 1%CM) (fe a) (fv 1%CM)). Iso2 (relabel_edge _ _ _).
    apply edge_graph2_iso=>//.
  Qed.
End h.
