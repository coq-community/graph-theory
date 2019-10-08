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

(* basic graphs and operations *)
Definition unit_graph2 a := point (unit_graph a) tt tt.
Definition two_graph2 a b := point (two_graph a b) false true. 
Definition edge_graph2 a u b := point (edge_graph a u b) false true. 
Definition add_vertex2 (G: graph2) l := point (add_vertex G l) (Some input) (Some output).
Definition add_edge2 (G: graph2) (x y: G) u := point (add_edge G x y u) input output.

Notation "G ∔ [ x , u , y ]" := 
  (@add_edge2 G x y u) (at level 20, left associativity).
Notation "G ∔ a" := 
  (add_vertex2 G a) (at level 20, left associativity).

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
Proof. by exists (@iso_id _ _). Defined.
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

Lemma iso_iso2 (F G: graph) (h: F ≃ G) (i o: F):
  point F i o ≃2 point G (h i) (h o).
Proof. now exists h. Qed.

Lemma iso_iso2' (F G: graph) (h: F ≃ G) (i o: F) (i' o': G):
  i' = h i -> o' = h o -> point F i o ≃2 point G i' o'.
Proof. intros -> ->. by apply iso_iso2. Qed.

Lemma union_C2 (F G: graph) (i o: F+G):
  point (union F G) i o ≃2 point (union G F) (sumC i) (sumC o).
Proof. apply (iso_iso2 (union_C _ _)). Qed.

Lemma union_A2 (F G H: graph) (i o: F+(G+H)):
  point (union F (union G H)) i o ≃2 point (union (union F G) H) (sumA i) (sumA o).
Proof. apply (iso_iso2 (union_A _ _ _)). Qed.

Lemma union_A2' (F G H: graph) (i o: (F+G)+H):
  point (union (union F G) H) i o ≃2 point (union F (union G H)) (sumA' i) (sumA' o).
Proof. apply (iso_iso2 (iso_sym (union_A _ _ _))). Qed.


(* simple tactics for rewriting with isomorphisms at toplevel, in the lhs or in the rhs
   (used in place of setoid_rewrite or rewrite->, which are pretty slow) *)
Tactic Notation "irewrite" uconstr(L) := (eapply iso2_comp;[apply L|]); last 1 first.
Tactic Notation "irewrite'" uconstr(L) := eapply iso2_comp;[|apply iso2_sym, L].


(* two pointed graphs operations *)

Definition g2_par (F G: graph2) :=
  point (merge_seq (F ⊎ G) [::(unl input,unr input); (unl output,unr output)])
        (\pi (unl input)) (\pi (unr output)).

Definition g2_dot (F G: graph2) :=
  point (merge_seq (F ⊎ G) [::(unl output,unr input)])
        (\pi (unl input)) (\pi (unr output)).

Definition g2_cnv (F: graph2) :=
  point F output input.

Definition g2_dom (F: graph2) :=
  point F input input.

Definition g2_one: graph2 :=
  point (unit_graph mon0) tt tt.

Definition g2_top: graph2 :=
  point (two_graph mon0 mon0) false true.

Definition g2_var a: graph2 :=
  point (edge_graph mon0 a mon0) false true.

Definition add_test (G: graph2) (x: G) (a: Lv): graph2 :=
  point (upd_vlabel x (mon2 a)) input output.

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

(* laws about low level operations (union/merge) *)

Lemma merge_iso2 (F G : graph) (h: iso F G) l (i o: F):
  point (merge_seq F l) (\pi i) (\pi o) ≃2
  point (merge_seq G (map_pairs h l)) (\pi (h i)) (\pi (h o)).
Proof. apply (iso_iso2' (h:=merge_iso h l)); by rewrite h_mergeE. Qed.

Lemma merge_same (F : graph) (h k: equiv_rel F) (i i' o o': F):
  (h =2 k) ->
  h i i' ->
  h o o' ->
  point (merge F h) (\pi i) (\pi o) ≃2 point (merge F k) (\pi i') (\pi o').
Proof.
  intros H Hi Ho.
  apply (iso_iso2' (h:=merge_same' H));
    rewrite merge_same'E =>//;
    symmetry; apply /eqquotP; by rewrite <- H. 
Qed.

Lemma merge_seq_same (F : graph) (h k: pairs F) (i i' o o': F):
  (eqv_clot h =2 eqv_clot k) ->
  eqv_clot h i i' ->
  eqv_clot h o o' ->
  point (merge_seq F h) (\pi i) (\pi o) ≃2 point (merge_seq F k) (\pi i') (\pi o').
Proof. apply merge_same. Qed.

Lemma merge_seq_same' (F : graph) (h k: pairs F) (i o: F):
  (eqv_clot h =2 eqv_clot k) ->
  point (merge_seq F h) (\pi i) (\pi o) ≃2 point (merge_seq F k) (\pi i) (\pi o).
Proof.
  intros. by apply merge_seq_same. 
Qed.

Lemma merge_nothing (F: graph) (h: pairs F) (i o: F):
  List.Forall (fun p => p.1 = p.2) h ->
  point (merge_seq F h) (\pi i) (\pi o) ≃2 point F i o.
Proof.
  intros H. apply (iso_iso2' (h:=merge_nothing H)); by rewrite merge_nothingE.
Qed.


(** merge_merge  *)
Lemma merge_merge (G: graph) (h k: pairs G) (k': pairs (merge_seq G h)) (i o: G):
  k' = map_pairs (pi (eqv_clot h)) k ->
  point (merge_seq (merge_seq G h) k') (\pi (\pi i)) (\pi (\pi o))
≃2 point (merge_seq G (h++k)) (\pi i) (\pi o).
Proof.
  intro K. apply (iso_iso2' (h:=merge_merge_seq K)); by rewrite /=merge_merge_seqE. 
Qed.

(** union_merge_l  *)
Lemma union_merge_l_ll (F G: graph) (i o: F) (h: pairs F):
  point (merge_seq F h ⊎ G) (inl (\pi i)) (inl (\pi o))
≃2 point (merge_seq (F ⊎ G) (map_pairs unl h)) (\pi (unl i)) (\pi (unl o)).
Proof. apply (iso_iso2' (h:=union_merge_l _ _)); by rewrite /=union_merge_lEl. Qed.

Lemma union_merge_l_lr (F G: graph) (i: F) (o: G) (h: pairs F):
  point (merge_seq F h ⊎ G) (inl (\pi i)) (inr o)
≃2 point (merge_seq (F ⊎ G) (map_pairs unl h)) (\pi (unl i)) (\pi (unr o)).
Proof.
  apply (iso_iso2' (h:=union_merge_l _ _)).
    by rewrite /=union_merge_lEl.
    by rewrite /=union_merge_lEr.
Qed.

Lemma union_merge_l_rl (F G: graph) (i: G) (o: F) (h: pairs F):
  point (merge_seq F h ⊎ G) (unr i) (inl (\pi o))
≃2 point (merge_seq (F ⊎ G) (map_pairs unl h)) (\pi (unr i)) (\pi (unl o)).
Proof.
  apply (iso_iso2' (h:=union_merge_l _ _)).
    by rewrite /=union_merge_lEr.
    by rewrite /=union_merge_lEl.
Qed.

Lemma union_merge_l_rr (F G: graph) (i o: G) (h: pairs F):
  point (merge_seq F h ⊎  G) (unr i) (unr o)
≃2 point (merge_seq (F ⊎ G) (map_pairs unl h)) (\pi (unr i)) (\pi (unr o)).
Proof. apply (iso_iso2' (h:=union_merge_l _ _)); by rewrite /=union_merge_lEr. Qed.

(** union_merge_r  *)
Lemma union_merge_r_ll (F G: graph) (i o: F) (h: pairs G):
  point (F ⊎ merge_seq G h) (unl i) (unl o)
≃2 point (merge_seq (F ⊎ G) (map_pairs unr h)) (\pi (unl i)) (\pi (unl o)).
Proof. apply (iso_iso2' (h:=union_merge_r _ _)); by rewrite union_merge_rEl. Qed.

Lemma union_merge_r_lr (F G: graph) (i: F) (o: G) (h: pairs G):
  point (F ⊎ merge_seq G h) (unl i) (inr (\pi o))
≃2 point (merge_seq (F ⊎ G) (map_pairs unr h)) (\pi (unl i)) (\pi (unr o)).
Proof.
  apply (iso_iso2' (h:=union_merge_r _ _)).
    by rewrite union_merge_rEl.
    by rewrite union_merge_rEr.
Qed.

Lemma union_merge_r_rl (F G: graph) (i: G) (o: F) (h: pairs G):
  point (F ⊎ merge_seq G h) (inr (\pi i)) (unl o)
≃2 point (merge_seq (F ⊎ G) (map_pairs unr h)) (\pi (unr i)) (\pi (unl o)).
Proof.
  apply (iso_iso2' (h:=union_merge_r _ _)).
    by rewrite union_merge_rEr.
    by rewrite union_merge_rEl.
Qed.

Lemma union_merge_r_rr (F G: graph) (i o: G) (h: pairs G):
  point (F ⊎ merge_seq G h) (inr (\pi i)) (inr (\pi o))
≃2 point (merge_seq (F ⊎ G) (map_pairs unr h)) (\pi (unr i)) (\pi (unr o)).
Proof. apply (iso_iso2' (h:=union_merge_r _ _)); by rewrite union_merge_rEr. Qed.

(**  merge_union_K  *)
Lemma merge_union_K_ll (F K: graph) (i o: F) (h: pairs (F+K)) (k: K -> F)
      (kv: forall x: K, vlabel x = mon0)
      (ke: edge K -> False)
      (kh: forall x: K, unr x = unl (k x) %[mod (eqv_clot h)]):
  point (merge_seq (F ⊎ K) h) (\pi (unl i)) (\pi (unl o))
≃2 point (merge_seq F (union_K_pairs h k)) (\pi i) (\pi o).
Proof.
  apply (iso_iso2' (h:=merge_union_K kv kh ke)); by rewrite /=merge_union_KEl.
Qed.

Lemma merge_union_K_lr (F K: graph) (i: F) (o: K) (h: pairs (F+K)) (k: K -> F)
      (kv: forall x: K, vlabel x = mon0)
      (ke: edge K -> False)
      (kh: forall x: K, unr x = unl (k x) %[mod (eqv_clot h)]):
  point (merge_seq (F ⊎ K) h) (\pi (unl i)) (\pi (unr o))
≃2 point (merge_seq F (union_K_pairs h k)) (\pi i) (\pi (k o)).
Proof.
  apply (iso_iso2' (h:=merge_union_K kv kh ke)).
   by rewrite /=merge_union_KEl.
   by rewrite /=merge_union_KEr.
Qed.

Lemma merge_union_K_rl (F K: graph) (i: K) (o: F) (h: pairs (F+K)) (k: K -> F)
      (kv: forall x: K, vlabel x = mon0)
      (ke: edge K -> False)
      (kh: forall x: K, unr x = unl (k x) %[mod (eqv_clot h)]):
  point (merge_seq (F ⊎ K) h) (\pi (unr i)) (\pi (unl o))
≃2 point (merge_seq F (union_K_pairs h k)) (\pi (k i)) (\pi o).
Proof.
  apply (iso_iso2' (h:=merge_union_K kv kh ke)).
   by rewrite /=merge_union_KEr.
   by rewrite /=merge_union_KEl.
Qed.

Lemma merge_union_K_rr (F K: graph) (i o: K) (h: pairs (F+K)) (k: K -> F)
      (kv: forall x: K, vlabel x = mon0)
      (ke: edge K -> False)
      (kh: forall x: K, unr x = unl (k x) %[mod (eqv_clot h)]):
  point (merge_seq (F ⊎ K) h) (\pi (unr i)) (\pi (unr o))
≃2 point (merge_seq F (union_K_pairs h k)) (\pi (k i)) (\pi (k o)).
Proof.
  apply (iso_iso2' (h:=merge_union_K kv kh ke)); by rewrite /=merge_union_KEr.
Qed.

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
  apply merge_seq_same.
  apply eqv_clot_eq. leqv. leqv. 
  eqv. eqv. 
Qed.

Lemma par2top (F: graph2): F ∥ top ≃2 F. 
Proof.
  rewrite /=/g2_par.
  irewrite (merge_union_K_lr (K:=top) _ _ (k:=fun b => if b then output else input)).
  irewrite merge_nothing. by case F. 
  repeat (constructor =>//=).
  by case. 
  by [].
  intros [|]; apply /eqquotP; eqv. 
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
  apply merge_seq_same'. rewrite /unl/unr/=.
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

Lemma dot2one (F: graph2): F · 1 ≃2 F.
Proof.
  rewrite /=/g2_dot.
  irewrite (merge_union_K_lr _ _ (k:=fun _ => output))=>//.
  destruct F. apply merge_nothing.
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
  apply merge_seq_same'=>/=.
  apply eqv_clot_eq; leqv.
Qed.

Lemma cnv2I (F: graph2): F°° ≃2 F.
Proof. by case F. Qed.

Lemma cnv2par (F G: graph2): (F ∥ G)° ≃2 F° ∥ G°.
Proof.
  rewrite /=/g2_cnv/g2_par.
  apply merge_seq_same.
  apply eqv_clot_eq; leqv.
  eqv.
  eqv.
Qed.

Lemma cnv2dot (F G: graph2): (F · G)° ≃2 G° · F°.
Proof.
  rewrite /=/g2_cnv/g2_dot. 
  irewrite (merge_iso2 (union_C F G)).
  apply merge_seq_same'=>/=.
  apply eqv_clot_eq; leqv.
Qed.

Lemma par2oneone: 1 ∥ 1 ≃2 g2_one.
Proof.
  rewrite /=/g2_par.
  irewrite (merge_union_K_lr (F:=unit_graph mon0) (K:=unit_graph mon0) _ _ (k:=fun _ => tt))=>//=.
  apply merge_nothing.
  repeat (constructor =>//=).
  intros []; apply /eqquotP; eqv.
Qed.

Lemma dom2E (F: graph2): dom F ≃2 1 ∥ (F · top).
Proof.
  symmetry. 
  irewrite par2C.
  rewrite /=/g2_dom/g2_par/g2_dot.
  irewrite (merge_iso2 (union_merge_l _ _)).
  rewrite /map_pairs/map 2!union_merge_lEl 1!union_merge_lEr /fst/snd.
  irewrite (merge_merge (G:=(F ⊎ top) ⊎ g2_one)
                              (k:=[::(inl (inl input),inr tt); (inl (inr true),inr tt)])) =>//.
  irewrite (merge_iso2 (iso_sym (union_A _ _ _))).
  irewrite (merge_union_K_lr (K:=top ⊎ g2_one) _ _ 
                             (k:=fun x => match x with inl false => output | _ => input end))=>/=.
  apply merge_nothing. 
  repeat (constructor =>//=).
  by intros [[]|].
  by intros [[]|].
  intros [[|]|[]]; apply /eqquotP; try eqv.
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
  irewrite (merge_union_K_lr (F:=F ⊎ G) _ _ (k:=fun x => unl input))=>//=.
  2: by intros []; apply /eqquotP; simpl; eqv.
  apply merge_seq_same; simpl.
  apply eqv_clot_eq; simpl; leqv.
  eqv.
  eqv.
Qed.

Lemma topR (F: graph2): F·top ≃2 point (F ⊎ unit_graph mon0) (unl input) (inr tt).
Proof.
  rewrite /=/g2_dot.
  irewrite (merge_iso2 (union_iso (@iso_id _ _) (iso_two_graph mon0 mon0))).
  irewrite (merge_iso2 (union_iso (@iso_id _ _) (union_C _ _))).
  irewrite (merge_iso2 (union_A _ _ _)).
  irewrite (merge_union_K_ll (F:=F ⊎ _) _ _ (k:=fun x => unl output))=>//=.
  apply merge_nothing. by constructor.
  intros []. apply /eqquotP. eqv.
Qed.

Lemma A11 (F: graph2): F·top ≃2 dom F·top.
Proof. irewrite topR. symmetry. by irewrite topR. Qed.

Lemma A12' (F G: graph2): @input F = @output F -> F·G ≃2 F·top ∥ G.
Proof.
  intro H. rewrite /=/g2_par/g2_dot.
  irewrite' (merge_iso2 (union_merge_l _ _)).
  rewrite /map_pairs/map 2!union_merge_lEl 2!union_merge_lEr /fst/snd.
  irewrite' (merge_merge (G:=(F ⊎ top) ⊎ G)
                              (k:=[::(inl (inl input),inr input);(inl (inr true),inr output)])) =>//.
  irewrite' (merge_iso2 (union_C (_ ⊎ _) _)).
  irewrite' (merge_iso2 (union_A _ _ _))=>/=.
  irewrite' (merge_union_K_ll (F:=G ⊎ F) (K:=top) _ _ 
                            (k:=fun x => if x then unl output else unr input))=>//.
  2: by case. 2: by intros []; apply /eqquotP; rewrite H; eqv.
  irewrite (merge_iso2 (union_C F G)) =>/=.
  apply merge_seq_same'. rewrite H. apply eqv_clot_eq; leqv.
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
  apply merge_seq_same; by rewrite /= ?iso2_input ?iso2_output. 
Qed.  

Lemma par_iso2: CProper (iso2 ==> iso2 ==> iso2) g2_par.
Proof.
  intros F F' f G G' g. rewrite /g2_par.
  irewrite (merge_iso2 (union_iso f g))=>/=.
  apply merge_seq_same; by rewrite /= ?iso2_input ?iso2_output. 
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

End s. 

Bind Scope graph2_scope with graph2.
Delimit Scope graph2_scope with G2.

Arguments input {_ _}.
Arguments output {_ _}.
Notation point G := (@Graph2 _ G).

Notation "G ∔ [ x , u , y ]" := 
  (@add_edge2 _ G x y u) (at level 20, left associativity) : graph2_scope.
Notation "G ∔ a" := 
  (add_vertex2 G a) (at level 20, left associativity) : graph2_scope.
Notation "G [tst x <- a ]" := 
  (@add_test _ G x a) (at level 20, left associativity, format "G [tst  x  <-  a ]") : graph2_scope.

Arguments iso2 {_}.
Arguments iso2prop {_}.

Infix "≃2" := iso2 (at level 79).
Infix "≃2p" := iso2prop (at level 79).
Hint Resolve iso2_id.         (* so that [by] gets it... *)
