Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries bij equiv.
Require Export structures mgraph pttdom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

(* two pointed labelled multigraphs and their operations

TO DO
 - input/output as a function from [bool]?
 - recheck status of [unr/unl]

 *)

Section s.
    
Variable L: labels.
Notation Lv := (lv L).  
Notation Le := (le L).
Notation graph := (graph L). 

Record graph2 :=
  Graph2 {
      graph_of:> graph;
      input: graph_of;
      output: graph_of }.
Arguments input {_}.
Arguments output {_}.
Notation point G := (@Graph2 G).

(* basic operations *)
Definition add_vertex2 (G: graph2) a := point (add_vertex G a) (inl input) (inl output).
Definition add_edge2 (G: graph2) (x y: G) u := point (add_edge G x y u) input output.
Definition add_vlabel2 (G: graph2) (x: G) a := point (add_vlabel G x a) input output.
Definition merge2 (G: graph2) (r: equiv_rel G) := point (merge G r) (\pi input) (\pi output).
Arguments merge2 _ _: clear implicits.

Notation "G ∔ a" := 
  (add_vertex2 G a) (at level 20, left associativity).
Notation "G ∔ [ x , u , y ]" := 
  (@add_edge2 G x y u) (at level 20, left associativity).
Notation "G [tst  x <- a ]" := 
  (@add_vlabel2 G x a) (at level 20, left associativity).
Notation merge2_seq G l := (merge2 G (eqv_clot l)).

(* basic graphs *)
Definition unit_graph2 a := point (unit_graph a) tt tt.
Definition two_graph2 a b := point (two_graph a b) (inl tt) (inr tt). 
Definition edge_graph2 a u b := two_graph2 a b ∔ [inl tt, u, inr tt]. 


(* TODO: via sigma types again?

Notation "'Σ' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p%type)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition iso2 (F G: graph2): Type :=
   Σ f: iso F G, f input = input /\ f output = output. 

 *)
Record iso2 (F G: graph2): Type :=
  Iso2 { iso2_iso:> F ≃ G;
         iso2_input: iso2_iso input = input;
         iso2_output: iso2_iso output = output }.
Infix "≃2" := iso2 (at level 79).

Definition iso2_id (G: graph2): G ≃2 G.
Proof. by exists iso_id. Defined.
Hint Resolve iso2_id.         (* so that [by] gets it... *)

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
Canonical Structure g2_setoid: setoid := Setoid iso2prop_Equivalence. 
Section CProper.
Variables A B C: Type.
Notation i R := (fun x y => inhabited (R x y)). 
Variable R: A -> A -> Type.
Variable S: B -> B -> Type.
Variable T: C -> C -> Type.
Variable f: A -> B.
Hypothesis Hf: CProper (R ==> S) f.
Lemma CProper1: Proper (i R ==> i S) f.
Proof. intros x y [H]. exists. by apply Hf. Qed.
Variable g: A -> B -> C.
Hypothesis Hg: CProper (R ==> S ==> T) g.
Lemma CProper2: Proper (i R ==> i S ==> i T) g.
Proof. intros x y [E] u v [F]. exists. by apply Hg. Qed.
End CProper.

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
   (used in place of setoid_rewrite or rewrite->, which are pretty slow) *)
Tactic Notation "irewrite" uconstr(L) := (eapply iso2_comp;[apply L|]); last 1 first.
Tactic Notation "irewrite'" uconstr(L) := eapply iso2_comp;[|apply iso2_sym, L].


(* two pointed graphs operations *)

Definition g2_par (F G: graph2) :=
  point (merge_seq (F ⊎ G) [::(unl input,unr input); (unl output,unr output)])
        (\pi (unl input)) (\pi (unr output)).
  (* merge2_seq (point (F ⊎ G) (inl input) (inr output)) *)
  (*            [::(inl input,inr input); (inl output,inr output)]. *)

Definition g2_dot (F G: graph2) :=
  point (merge_seq (F ⊎ G) [::(unl output,unr input)])
        (\pi (unl input)) (\pi (unr output)).
  (* merge2_seq (point (F ⊎ G) (inl input) (inr output)) *)
  (*            [::(inl output,inr input)]. *)

Definition g2_cnv (F: graph2) := point F output input.

Definition g2_dom (F: graph2) := point F input input.

Definition g2_one: graph2 := unit_graph2 mon0.

Definition g2_top: graph2 := two_graph2 mon0 mon0.

Definition g2_var a: graph2 := edge_graph2 mon0 a mon0.

(* Note: maybe nicer to prove that this is a ptt algebra (with top)
  and deduce automatically that this is a pttdom (as we did in the previous version) *)
Canonical Structure g2_ops: pttdom.ops_ :=
  {| dot := g2_dot;
     par := g2_par;
     cnv := g2_cnv;
     dom := g2_dom;
     one := g2_one;
     (* top := g2_top *) |}.
Notation top := g2_top.         (* TEMPORARY *)

(* laws about low level operations (union/merge/add_vertex/add_vlabel/add_edge) *)

(* isomorphisms about [unit_graph2] *)

Lemma unit_graph2_iso: CProper (eqv ==> iso2) unit_graph2.
Proof. intros a b e. Iso2 (unit_graph_iso e). Defined.

(* isomorphisms about [two_graph2] *)

Lemma two_graph2_iso: CProper (eqv ==> eqv ==> iso2) two_graph2.
Proof. intros a b ab c d cd. Iso2 (union_iso (unit_graph_iso ab) (unit_graph_iso cd)). Defined.

(* isomorphisms about [two_vertex2] *)

Lemma add_vertex2_iso: CProper (iso2 ==> eqv ==> iso2) add_vertex2.
Proof.
  move => F G FG u v uv.
  Iso2 (union_iso FG (unit_graph_iso uv))=>/=; f_equal; apply FG.
Defined.

(* isomorphisms about [add_edge2] *)

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

(* isomorphisms about [edge_graph2] *)

Lemma edge_graph2_iso: CProper (eqv ==> eqv ==> eqv ==> iso2) edge_graph2.
Proof. intros a b ab u v uv c d cd. refine (add_edge2_iso' (two_graph2_iso ab cd) _ _ uv). Defined.

(* isomorphisms about [add_vlabel2] *)

Lemma add_vlabel2_iso'' F G (h: F ≃2 G) x x' (ex: h x = x') a b (e: a ≡ b): F [tst x <- a] ≃2 G [tst x' <- b].
Proof. Iso2 (add_vlabel_iso'' ex e); apply h. Defined.

Lemma add_vlabel2_iso' F G (h: F ≃2 G) x a b (e: a ≡ b): F [tst x <- a] ≃2 G [tst h x <- b].
Proof. by eapply add_vlabel2_iso''. Defined.

Lemma add_vlabel2_iso F G (h: F ≃2 G) x a: F [tst x <- a] ≃2 G [tst h x <- a].
Proof. by apply add_vlabel2_iso'. Defined.

Lemma add_vlabel2_C F x a y b: F [tst x <- a] [tst y <- b] ≃2 F [tst y <- b] [tst x <- a].
Proof. Iso2 (add_vlabel_C _ _). Defined.

Lemma add_vlabel2_unit a x b: unit_graph2 a [tst x <- b] ≃2 unit_graph2 (mon2 a b).
Proof. Iso2 (add_vlabel_unit _ _). Defined.

Lemma add_vlabel2_unit' x b: unit_graph2 b ≃2 unit_graph2 mon0 [tst x <- b].
Proof. apply iso2_sym. irewrite add_vlabel2_unit. apply unit_graph2_iso. by rewrite monC monU. Defined.

Lemma add_vlabel2_two a b (x: unit+unit) c:
  two_graph2 a b [tst x <- c] ≃2 two_graph2 (if x then mon2 a c else a) (if x then b else mon2 b c).
Proof. Iso2 (add_vlabel_two _ _ _ _); by case x; case. Defined.

Lemma add_vlabel2_edge a u b (x: unit+unit) c:
  edge_graph2 a u b [tst x <- c] ≃2 edge_graph2 (if x then mon2 a c else a) u (if x then b else mon2 b c).
Proof. Iso2 (add_vlabel_edge _ _ _ _ _); by case x; case. Defined.

Lemma add_vlabel2_mon0 G x: G [tst x <- mon0] ≃2 G.
Proof. Iso2 (add_vlabel_mon0 x). Defined.


(* isomorphisms about [merge] *)

Lemma merge2_iso2 F G (h: F ≃2 G) l:
  merge2_seq F l ≃2 merge2_seq G (map_pairs h l).
  (* note: h should be informative so that map_pairs can be simplified... *)
Proof. Iso2 (merge_iso h l); by rewrite h_mergeE ?iso2_input ?iso2_output. Qed.

Lemma merge_iso2 (F G : graph) (h: F ≃ G) l (i o: F):
  point (merge_seq F l) (\pi i) (\pi o) ≃2
  point (merge_seq G (map_pairs h l)) (\pi (h i)) (\pi (h o)).
Proof. Iso2 (merge_iso h l); by rewrite h_mergeE. Defined.

Lemma merge2_surj (G: graph2) (r: equiv_rel G) (H: graph2) (fv : G -> H) (fv': H -> G) (fe : bij (edge G) (edge H)):
  (forall x y, reflect (kernel fv x y) (r x y)) ->
  cancel fv' fv ->
  (forall b e, fv (endpoint b e) = endpoint b (fe e)) ->
  (forall e, elabel (fe e) ≡ elabel e) ->
  (forall y: H, vlabel y ≡ \big[mon2/mon0]_(x | fv x == y) vlabel x) ->
  fv input = input -> fv output = output ->
  merge2 G r ≃2 H.
Proof.
  intros H1 H2 H3 H4 H5 I O.
  Iso2 (merge_surj H1 H2 H3 H4 H5); by rewrite merge_surjE.
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
Qed.

Lemma merge_same' (F : graph) (h k: equiv_rel F) (i o: F):
  (h =2 k) ->
  point (merge F h) (\pi i) (\pi o) ≃2 point (merge F k) (\pi i) (\pi o).
Proof. intros. by apply merge_same. Qed.

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


(** merge_merge  *)
Lemma merge_merge (G: graph) (h k: pairs G) (k': pairs (merge_seq G h)) (i o: G):
  k' = map_pairs (pi (eqv_clot h)) k ->
  point (merge_seq (merge_seq G h) k') (\pi (\pi i)) (\pi (\pi o))
≃2 point (merge_seq G (h++k)) (\pi i) (\pi o).
Proof. intro K. Iso2 (merge_merge_seq K); by rewrite /=merge_merge_seqE. Qed.

Lemma merge2_merge (G: graph2) (h k: pairs G) (k': pairs (merge_seq G h)):
  k' = map_pairs (pi (eqv_clot h)) k ->
  merge2_seq (merge2_seq G h) k' ≃2 merge2_seq G (h++k).
Proof. apply merge_merge. Qed.


(**  merge_union_K  *)
Lemma merge_union_K_l (F K: graph) (i o: F+K) (h: pairs (F+K)) (k: K -> F)
      (kv: forall x: K, vlabel x = mon0)
      (ke: edge K -> False)
      (kh: forall x: K, unr x = unl (k x) %[mod (eqv_clot h)]):
  point (merge_seq (F ⊎ K) h) (\pi i) (\pi o)
≃2 point (merge_seq F (union_K_pairs h k)) (\pi (sum_left k i)) (\pi (sum_left k o)).
Proof. Iso2 (merge_union_K kv kh ke)=>/=; by rewrite ?merge_union_KE. Defined.

Lemma merge2_add_edge (G: graph2) (r: equiv_rel G) x u y: merge2 (G ∔ [x, u, y]) r ≃2 merge2 G r ∔ [\pi x, u, \pi y].
Proof. Iso2 (merge_add_edge _ _ _ _); by rewrite merge_add_edgeE. Defined.

Lemma merge2_add_vlabel (G: graph2) (r: equiv_rel G) x a: merge2 (G [tst x <- a]) r ≃2 merge2 G r [tst \pi x <- a].
Proof. Iso2 (merge_add_vlabel _ _ _); by rewrite merge_add_vlabelE. Defined.

Lemma merge2_two a b: merge2_seq (two_graph2 a b) [:: (inl tt,inr tt)] ≃2 unit_graph2 (mon2 a b).
Proof. Iso2 (merge_two a b); by rewrite merge_twoE. Defined.


(** ** 2p-graphs form a 2p-algebra *)

(* TODO: for now the 2p laws are all proved in Type [iso2], 
   because some of them could be useful in Type in open.v and reduction.v
   (simple ones like commutativity to get symmetry reasonning, 
    but also CProper)
   we might want to prove downgrade some of them to Prop [iso2prop]
 *)

Lemma par2C (F G: graph2): F ∥ G ≃2 G ∥ F.
Proof.
  rewrite /=/g2_par.
  irewrite (merge_iso2 (union_C F G)) =>/=.
  apply merge_same. apply eqv_clot_eq; leqv. eqv. eqv. 
Qed.

Lemma par2top (F: graph2): F ∥ top ≃2 F. 
Proof.
  rewrite /=/g2_par.
  irewrite (merge_union_K_l (K:=top) _ _ (k:=fun b => if b then input else output))=>/=; try by repeat case.
  apply merge2_nothing. 
  by repeat constructor. 
  repeat case; apply /eqquotP; eqv. 
Qed.

Lemma par2A (F G H: graph2): F ∥ (G ∥ H) ≃2 (F ∥ G) ∥ H.
Proof.
  irewrite (merge_iso2 (union_merge_r _ _)).
  rewrite /map_pairs/map 2!union_merge_rEl 2!union_merge_rEr /fst/snd.
  irewrite (merge_merge (G:=F ⊎ (G ⊎ H))
                        (k:=[::(unl input,unr (unl input)); (unl output,unr (unr output))]))=>//.
  irewrite' (merge_iso2 (union_merge_l _ _)).
  rewrite /map_pairs/map 2!union_merge_lEl 2!union_merge_lEr /fst/snd.
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
  rewrite /=/g2_dot.
  irewrite (merge_iso2 (union_iso iso_id (add_vlabel2_unit' output _)))=>/=.
  etransitivity. refine (merge_iso2 (union_add_vlabel_r _ _ _) _ _ _). simpl.
  etransitivity. refine (iso_iso2 (merge_add_vlabel _ _ _) _ _). simpl.
  etransitivity. refine (iso_iso2 (add_vlabel_iso (merge_union_K_l (K:=g2_one) (inl input) (inl output) (k:=fun _ => output) _ _ _) _ _) _ _)=>//. 
  case; apply /eqquotP; eqv.
  rewrite /=!merge_union_KE !merge_add_vlabelE !merge_union_KE/=. 
  etransitivity. refine (add_vlabel2_iso (merge2_nothing _) _ _).
  repeat (constructor =>//=).
  destruct G=>/=. by rewrite merge_nothingE. 
Qed.

Lemma dot2unit_r' (G: graph2) a: G · unit_graph2 a ≃2 G [tst output <- a].
Proof.
  (* global proof, via surjective homomorphism *)
  unshelve Iso2
   (@merge_surj _
     (G ⊎ unit_graph2 a) _
     (G [tst output <- a])
     (fun x => match x with inl y => y | inr tt => output end)
     (fun x => inl x)
     sumxU _ _ _ _ _).
  6,7: by rewrite merge_surjE.
  - apply kernel_eqv_clot.
    * by constructor.
    * case=>[x|[]]; case=>[y|[]]=>//->; eqv. 
  - by []. 
  - by move=>b [e|[]].
  - by case. 
  - move=>x/=. admit.           (* should be rather simple... *)
Admitted.

(* [dot2one] follows from [dot2unit_r] *)
Lemma dot2one (F: graph2): F · 1 ≃2 F.
Proof. etransitivity. apply dot2unit_r. apply add_vlabel2_mon0. Qed.

(* ... but also has a reasonable direct proof *)
Lemma dot2one' (F: graph2): F · 1 ≃2 F.
Proof.
  rewrite /=/g2_dot.
  irewrite (merge_union_K_l (K:=g2_one) _ _ (k:=fun _ => output))=>//.
  apply merge2_nothing.
  repeat (constructor =>//=).
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
  rewrite /=/g2_dot.
  irewrite (merge_iso2 (union_merge_r _ _)).
  rewrite /map_pairs/map 2!union_merge_rEl 2!union_merge_rEr /fst/snd.
  irewrite (merge_merge (G:=F ⊎ (G ⊎ H))
                              (k:=[::(unl output,unr (unl input))])) =>//.
Qed.

Lemma dot2A (F G H: graph2): F · (G · H) ≃2 (F · G) · H.
Proof.
  irewrite dot2Aflat. 
  rewrite /=/g2_dot.
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
  rewrite /=/g2_cnv/g2_par.
  apply merge_same. apply eqv_clot_eq; leqv. eqv. eqv.
Qed.

Lemma cnv2dot (F G: graph2): (F · G)° ≃2 G° · F°.
Proof.
  rewrite /=/g2_cnv/g2_dot. 
  irewrite (merge_iso2 (union_C F G)).
  apply merge_same'=>/=. apply eqv_clot_eq; leqv.
Qed.

Lemma par2dot F G: @input F = output -> @input G = output -> F ∥ G ≃2 F · G.
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
  rewrite /=/g2_dom/g2_par/g2_dot.
  irewrite (merge_iso2 (union_merge_l _ _)).
  rewrite /map_pairs/map 2!union_merge_lEl 1!union_merge_lEr /fst/snd.
  irewrite (merge_merge (G:=(F ⊎ top) ⊎ g2_one)
                              (k:=[::(inl (inl input),inr tt); (inl (inr (inr tt)),inr tt)])) =>//.
  irewrite (merge_iso2 (iso_sym (union_A _ _ _))).
  irewrite (merge_union_K_l (K:=top ⊎ g2_one) _ _ 
                            (k:=fun x => match x with inl (inl tt) => output | _ => input end))=>/=.
  apply merge_nothing. 
  repeat (constructor =>//=).
  by intros [[]|].
  by intros [[]|].
  repeat case; apply /eqquotP; try eqv.
  apply eqv_clot_trans with (inr (inr tt)); eqv. 
Qed.

Lemma A10 (F G: graph2): 1 ∥ F·G ≃2 dom (F ∥ G°).
Proof.
  irewrite (par2C 1).
  rewrite /=/g2_par/g2_dot/g2_dom/g2_cnv.
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

Lemma topR (F: graph2): F·top ≃2 point (F ⊎ unit_graph mon0) (unl input) (inr tt).
Proof.
  rewrite /=/g2_dot.
  irewrite (merge_iso2 (union_iso iso_id (union_C _ _))).
  irewrite (merge_iso2 (union_A _ _ _)).
  irewrite (merge_union_K_l (F:=F ⊎ _) _ _ (k:=fun x => unl output))=>//=.
  apply merge_nothing. by constructor.
  case. apply /eqquotP. eqv.
Qed.

Lemma A11 (F: graph2): F·top ≃2 dom F·top.
Proof. irewrite topR. symmetry. by irewrite topR. Qed.

Lemma A12' (F G: graph2): @input F = @output F -> F·G ≃2 F·top ∥ G.
Proof.
  intro H. rewrite /=/g2_par/g2_dot.
  irewrite' (merge_iso2 (union_merge_l _ _)).
  rewrite /map_pairs/map 2!union_merge_lEl 2!union_merge_lEr /fst/snd.
  irewrite' (merge_merge (G:=(F ⊎ top) ⊎ G)
                              (k:=[::(inl (inl input),inr input);(inl (inr (inr tt)),inr output)])) =>//.
  irewrite' (merge_iso2 (union_C (_ ⊎ _) _)).
  irewrite' (merge_iso2 (union_A _ _ _))=>/=.
  irewrite' (merge_union_K_l (F:=G ⊎ F) (K:=top) _ _ 
                             (k:=fun x => if x then unr input else unl output))=>//.
  2: by case. 2: by repeat case; apply /eqquotP; rewrite H; eqv.
  irewrite (merge_iso2 (union_C F G)) =>/=.
  apply merge_same'. rewrite H. apply eqv_clot_eq; leqv.
  repeat case=>//=; rewrite H; apply /eqquotP; eqv. 
Qed.

Lemma A12 (F G: graph2): (F ∥ 1)·G ≃2 (F ∥ 1)·top ∥ G.
Proof.
  apply A12'.
  apply /eqquotP. apply eqv_clot_trans with (inr tt); eqv.
Qed.

Lemma dot_iso2: CProper (iso2 ==> iso2 ==> iso2) g2_dot.
Proof.
  intros F F' f G G' g. rewrite /g2_dot.
  irewrite (merge_iso2 (union_iso f g))=>/=.
  apply merge_same; by rewrite /= ?iso2_input ?iso2_output. 
Qed.  

Lemma par_iso2: CProper (iso2 ==> iso2 ==> iso2) g2_par.
Proof.
  intros F F' f G G' g. rewrite /g2_par.
  irewrite (merge_iso2 (union_iso f g))=>/=.
  apply merge_same; by rewrite /= ?iso2_input ?iso2_output. 
Qed.

Lemma cnv_iso2: CProper (iso2 ==> iso2) g2_cnv.
Proof. intros F F' f. eexists; apply f. Qed.

Lemma dom_iso2: CProper (iso2 ==> iso2) g2_dom.
Proof. intros F F' f. eexists; apply f. Qed.

Program Definition g2_pttdom: pttdom := {| ops := g2_ops |}.
Next Obligation. apply CProper2, dot_iso2. Qed.
Next Obligation. apply CProper2, par_iso2. Qed.
Next Obligation. apply CProper1, cnv_iso2. Qed.
Next Obligation. apply CProper1, dom_iso2. Qed.
Next Obligation. exists. apply par2A. Qed.
Next Obligation. exists. apply par2C. Qed.
Next Obligation. exists. apply dot2A. Qed.
Next Obligation. exists. apply dot2one. Qed.
Next Obligation. exists. apply cnv2I. Qed.
Next Obligation. exists. apply cnv2par. Qed.
Next Obligation. exists. apply cnv2dot. Qed.
Next Obligation. exists. apply par2oneone. Qed.
Next Obligation. exists. apply A10. Qed.
Next Obligation. exists. Admitted. (* consequence of being a 2p algebra... *)
Next Obligation. exists. Admitted. (* consequence of being a 2p algebra... *)
Canonical g2_pttdom.

(* additional lemmas needed in reduction.v *)

Lemma dot2unit_l (G: graph2) a: unit_graph2 a · G ≃2 G [tst input <- a].
Proof.
  irewrite (iso2_sym (cnv2I _)). 
  irewrite' (iso2_sym (cnv2I _)).
  apply cnv_iso2.
  irewrite cnv2dot. 
  apply dot2unit_r.
Qed.

Lemma par2unitunit a b: unit_graph2 a ∥ unit_graph2 b ≃2 unit_graph2 (mon2 a b).
Proof.
  etransitivity. apply par2dot=>//.
  etransitivity. apply dot2unit_r.
  apply add_vlabel2_unit.
Qed.

Lemma par2edgeunit a u b c: edge_graph2 a u b ∥ unit_graph2 c ≃2 unit_graph2 (mon2 a (mon2 b c)) ∔ [tt, u, tt].
  unshelve Iso2
   (@merge_surj _ (edge_graph2 a u b ⊎ unit_graph2 c) _ (unit_graph2 (mon2 a (mon2 b c)) ∔ [tt, u, tt])
     (fun _ => tt)
     (fun _ => inr tt)
     (bij_comp sumxU (option_bij sumxU)) _ _ _ _ _).
  6,7: by rewrite merge_surjE.
  - apply kernel_eqv_clot.
    * by repeat constructor.
    * (repeat case)=>//=_; try eqv; apply eqv_clot_trans with (inr tt); eqv.
  - by case. 
  - move=>d. repeat case=>//=. by case d. 
  - by repeat case. 
  - repeat case=>//=. rewrite eq_refl/=.
    (* grr: again, how to let this compute? *)
    admit.
Admitted.

(* lemmas needed in open.v *)

Notation IO := [set input;output].

Parameter del_vertex2 : 
  forall (G : graph2) (z : G) (Hz : z \notin IO), graph2.

Arguments del_vertex2 : clear implicits.

Lemma del_vertex_cong (F G : graph2) (i : F ≃2 G) 
  (z : F) (z' : G) (Hz : z \notin IO) (Hiz : z' \notin IO) :
  z' = i z -> del_vertex2 F z Hz ≃2 del_vertex2 G z' Hiz.
Admitted.

Parameter del_edges2 : 
  forall (G : graph2) (E : {set edge G}), graph2.

Lemma iso2_del_edges2 (F G : graph2) (i : F ≃2 G) 
  (EF : {set edge F}) (EG : {set edge G}) : 
  EG = [set i.e e | e in EF] -> del_edges2 EF ≃2 del_edges2 EG.
Admitted.

(* requires definition to type check *)
(* Lemma iso2_del_edges2E (F G : graph2) (i : F ≃2 G) EF EG h :  *)
(*   @iso2_del_edges2 F G i EF EG h =1 i. *)

End s. 

Bind Scope graph2_scope with graph2.
Delimit Scope graph2_scope with G2.

Arguments input {_ _}.
Arguments output {_ _}.
Arguments add_edge2 [_] _ _ _ _. 
Arguments add_vertex2 [_] _ _. 
Arguments add_vlabel2 [_] _ _ _. 
Arguments merge2 [_] _ _. 

Notation IO := [set input;output].
Notation point G i o := (@Graph2 _ G i o).

Notation "G ∔ [ x , u , y ]" := 
  (add_edge2 G x y u) (at level 20, left associativity) : graph2_scope.
Notation "G ∔ a" := 
  (add_vertex2 G a) (at level 20, left associativity) : graph2_scope.
Notation "G [tst  x <- a ]" := 
  (add_vlabel2 G x a) (at level 20, left associativity) : graph2_scope.
Notation merge2_seq G l := (merge2 G (eqv_clot l)).

Arguments iso2 {_}.
Arguments iso2prop {_}.
Arguments iso2_id {_ _}.

Infix "≃2" := iso2 (at level 79).
Infix "≃2p" := iso2prop (at level 79).
Hint Resolve iso2_id.         (* so that [by] gets it... *)

Tactic Notation "Iso2" uconstr(f) :=
  match goal with |- ?F ≃2 ?G => refine (@Iso2 _ F G f _ _)=>// end.


(* temporary *)
Notation add_test := add_vlabel2 (only parsing).
Notation add_test_cong := add_vlabel2_iso' (only parsing).
