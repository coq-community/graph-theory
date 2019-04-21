From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries equiv ptt_algebra multigraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 

Record graph2 :=
  Graph2 { graph_of :> graph;
           g_in : graph_of;
           g_out : graph_of }.
Arguments g_in [_].
Arguments g_out [_].

Notation point G := (@Graph2 G).

Lemma point_io (G : graph2) : G = point G g_in g_out.
Proof. by case: G. Qed.

Definition iso2 (F G: graph2) : Prop := 
  (exists h: h_ty F G, iso_g h * (h.1 g_in = g_in) * (h.1 g_out = g_out))%type.

Notation "G ≈ H" := (iso2 G H) (at level 45).

Definition par2 (F G: graph2) :=
  point (merge_seq (union F G) [::(unl g_in,unr g_in); (unl g_out,unr g_out)])
        (\pis (unl g_in)) (\pis (unl g_out)).

Definition dot2 (F G: graph2) :=
  point (merge_seq (union F G) [::(unl g_out,unr g_in)])
        (\pis (unl g_in)) (\pis (unr g_out)).

Definition cnv2 (F: graph2) :=
  point F g_out g_in.

Definition dom2 (F: graph2) :=
  point F g_in g_in.

Definition one2 :=
  point unit_graph tt tt.

Definition top2 :=
  point two_graph false true.

Definition sym2 a :=
  point (edge_graph a) false true.

Canonical Structure graph2_ops: ptt_ops :=
  {| weq := iso2;
     dot := dot2;
     par := par2;
     cnv := cnv2;
     dom := dom2;
     one := one2;
     top := top2 |}.
Bind Scope ptt_ops with graph2.

Definition graph_of_term (u: term sym): graph2 := eval sym2 u. 

Instance iso2_Equivalence: Equivalence iso2.
Proof.
  constructor.
  - intro G. exists (id,id). split=>//; split=>//. apply iso_id.
  - intros F G [h [[[H [[g1 H1 G1] [g2 H2 G2]]] Hi] Ho]].
    exists (g1,g2). (repeat split)=> /= [e|e|e||||].
    by rewrite -{1}(G2 e) -H H1.
    by rewrite -{1}(G2 e) -H H1.
    by rewrite -H G2.
    by eexists. 
    by eexists. 
    by rewrite -(H1 g_in) Hi.
    by rewrite -(H1 g_out) Ho.
  - intros F G H [f [[Hf Fi] Fo]] [g [[Hg Gi] Go]].
    eexists. split. split. apply (iso_comp Hf Hg).
    simpl. congruence. 
    simpl. congruence. 
Qed.

(* TODO: added this hint so that by/done solve these cases, is there a nicer way to proceeed? *)
Lemma iso2_refl G: G ≈ G.
Proof. reflexivity. Qed.
Hint Resolve iso2_refl.

Opaque merge_seq union.

(** * from isomorphisms on graphs to isomorphisms on 2p-graphs *)

Lemma iso_iso2 (F G: graph) (i o: F) (h: h_ty F G):
  iso_g h -> point F i o ≈ point G (h.1 i) (h.1 o).
Proof. intro H. now exists h. Qed.

Lemma iso_iso2' (F G: graph) (i o: F) (i' o': G) (h: h_ty F G):
  iso_g h -> i' = h.1 i -> o' = h.1 o -> point F i o ≈ point G i' o'.
Proof. intros H -> ->. by apply iso_iso2. Qed.

Lemma union_C2 (F G: graph) (i o: F+G):
  point (union F G) i o ≈ point (union G F) (sumC i) (sumC o).
Proof. by eapply iso_iso2'; first apply iso_union_C. Qed.

Lemma union_A2 (F G H: graph) (i o: F+(G+H)):
  point (union F (union G H)) i o ≈ point (union (union F G) H) (sumA i) (sumA o).
Proof. by eapply iso_iso2'; first apply iso_union_A. Qed.

Lemma union_A2' (F G H: graph) (i o: (F+G)+H):
  point (union (union F G) H) i o ≈ point (union F (union G H)) (sumA' i) (sumA' o).
Proof. by eapply iso_iso2'; first apply iso_union_A'. Qed.

Lemma merge_iso2 (F G : graph) (h: h_ty F G): iso_g h ->
  forall l (i o: F),
  point (merge_seq F l) (\pis i) (\pis o) ≈
  point (merge_seq G (map_pairs h.1 l)) (\pis (h.1 i)) (\pis (h.1 o)).
Proof.
  intros. eapply iso_iso2'. apply merge_iso, H.
  by rewrite h_mergeE. 
  by rewrite h_mergeE. 
Qed.

Lemma merge_same (F : graph) (h k: pairs F) (i i' o o': F):
  (eqv_clot h =2 eqv_clot k) ->
  eqv_clot h i i' ->
  eqv_clot h o o' ->
  point (merge_seq F h) (\pis i) (\pis o) ≈ point (merge_seq F k) (\pis i') (\pis o').
Proof.
  intros H Hi Ho.
  eapply iso_iso2'. by apply merge_same_iso.
  rewrite h_merge_sameE =>//.
  symmetry. apply /eqquotP. by rewrite <- H. 
  rewrite h_merge_sameE =>//.
  symmetry. apply /eqquotP. by rewrite <- H. 
Qed.

Lemma merge_same' (F : graph) (h k: pairs F) (i o: F):
  (eqv_clot h =2 eqv_clot k) ->
  point (merge_seq F h) (\pis i) (\pis o) ≈ point (merge_seq F k) (\pis i) (\pis o).
Proof.
  intros. by apply merge_same. 
Qed.

Lemma merge_nothing (F: graph) (h: pairs F) (i o: F):
  List.Forall (fun p => p.1 = p.2) h ->
  point (merge_seq F h) (\pis i) (\pis o) ≈ point F i o.
Proof.
  intros H. 
  eapply iso_iso2'. by apply merge_nothing_iso.
  by rewrite h_merge_nothingE.
  by rewrite h_merge_nothingE.
Qed.


(** ** merge_merge  *)
Lemma merge_merge (G: graph) (h k: pairs G) (k': pairs (merge_seq G h)) (i o: G):
  k' = map_pairs (pi h) k ->
  point (merge_seq (merge_seq G h) k') (\pis (\pis i)) (\pis (\pis o))
≈ point (merge_seq G (h++k)) (\pis i) (\pis o).
Proof.
  intro K. eapply iso_iso2'; first apply iso_merge_merge_seq=>//; by rewrite /=h_merge_merge_seqE. 
Qed.

(** ** union_merge_l  *)
Lemma union_merge_l_ll (F G: graph) (i o: F) (h: pairs F):
  point (union (merge_seq F h) G) (unl (\pis i)) (unl (\pis o))
≈ point (merge_seq (union F G) (map_pairs unl h)) (\pis (unl i)) (\pis (unl o)).
Proof. eapply iso_iso2'; first apply iso_union_merge_l; by rewrite /=h_union_merge_lEl. Qed.

Lemma union_merge_l_lr (F G: graph) (i: F) (o: G) (h: pairs F):
  point (union (merge_seq F h) G) (unl (\pis i)) (unr o)
≈ point (merge_seq (union F G) (map_pairs unl h)) (\pis (unl i)) (\pis (unr o)).
Proof.
  eapply iso_iso2'; first apply iso_union_merge_l.
    by rewrite /=h_union_merge_lEl.
    by rewrite /=h_union_merge_lEr.
Qed.

Lemma union_merge_l_rl (F G: graph) (i: G) (o: F) (h: pairs F):
  point (union (merge_seq F h) G) (unr i) (unl (\pis o))
≈ point (merge_seq (union F G) (map_pairs unl h)) (\pis (unr i)) (\pis (unl o)).
Proof.
  eapply iso_iso2'; first apply iso_union_merge_l.
    by rewrite /=h_union_merge_lEr.
    by rewrite /=h_union_merge_lEl.
Qed.

Lemma union_merge_l_rr (F G: graph) (i o: G) (h: pairs F):
  point (union (merge_seq F h) G) (unr i) (unr o)
≈ point (merge_seq (union F G) (map_pairs unl h)) (\pis (unr i)) (\pis (unr o)).
Proof. eapply iso_iso2'; first apply iso_union_merge_l; by rewrite /=h_union_merge_lEr. Qed.

(** ** union_merge_r  *)
Lemma union_merge_r_ll (F G: graph) (i o: F) (h: pairs G):
  point (union F (merge_seq G h)) (unl i) (unl o)
≈ point (merge_seq (union F G) (map_pairs unr h)) (\pis (unl i)) (\pis (unl o)).
Proof. eapply iso_iso2'; first apply iso_union_merge_r; by rewrite /=h_union_merge_rEl. Qed.

Lemma union_merge_r_lr (F G: graph) (i: F) (o: G) (h: pairs G):
  point (union F (merge_seq G h)) (unl i) (unr (\pis o))
≈ point (merge_seq (union F G) (map_pairs unr h)) (\pis (unl i)) (\pis (unr o)).
Proof.
  eapply iso_iso2'; first apply iso_union_merge_r.
    by rewrite /=h_union_merge_rEl.
    by rewrite /=h_union_merge_rEr.
Qed.

Lemma union_merge_r_rl (F G: graph) (i: G) (o: F) (h: pairs G):
  point (union F (merge_seq G h)) (unr (\pis i)) (unl o)
≈ point (merge_seq (union F G) (map_pairs unr h)) (\pis (unr i)) (\pis (unl o)).
Proof.
  eapply iso_iso2'; first apply iso_union_merge_r.
    by rewrite /=h_union_merge_rEr.
    by rewrite /=h_union_merge_rEl.
Qed.

Lemma union_merge_r_rr (F G: graph) (i o: G) (h: pairs G):
  point (union F (merge_seq G h)) (unr (\pis i)) (unr (\pis o))
≈ point (merge_seq (union F G) (map_pairs unr h)) (\pis (unr i)) (\pis (unr o)).
Proof. eapply iso_iso2'; first apply iso_union_merge_r; by rewrite /=h_union_merge_rEr. Qed.

(** ** merge_union_K  *)
Lemma merge_union_K_ll (F K: graph) (i o: F) (h: pairs (F+K)) (k: K -> F)
      (ke: edge K -> False)
      (kh: forall x: K, unr x = unl (k x) %[mod_eq (eqv_clot h)]):
  point (merge_seq (union F K) h) (\pis (unl i)) (\pis (unl o))
≈ point (merge_seq F (union_K_pairs h k)) (\pis i) (\pis o).
Proof.
  eapply iso_iso2'; first (by apply (iso_merge_union_K kh ke)); by rewrite /=h_merge_union_KEl.
Qed.

Lemma merge_union_K_lr (F K: graph) (i: F) (o: K) (h: pairs (F+K)) (k: K -> F)
      (ke: edge K -> False)
      (kh: forall x: K, unr x = unl (k x) %[mod_eq (eqv_clot h)]):
  point (merge_seq (union F K) h) (\pis (unl i)) (\pis (unr o))
≈ point (merge_seq F (union_K_pairs h k)) (\pis i) (\pis (k o)).
Proof.
  eapply iso_iso2'; first (by apply (iso_merge_union_K kh ke)).
   by rewrite /=h_merge_union_KEl.
   by rewrite /=h_merge_union_KEr.
Qed.

Lemma merge_union_K_rl (F K: graph) (i: K) (o: F) (h: pairs (F+K)) (k: K -> F)
      (ke: edge K -> False)
      (kh: forall x: K, unr x = unl (k x) %[mod_eq (eqv_clot h)]):
  point (merge_seq (union F K) h) (\pis (unr i)) (\pis (unl o))
≈ point (merge_seq F (union_K_pairs h k)) (\pis (k i)) (\pis o).
Proof.
  eapply iso_iso2'; first (by apply (iso_merge_union_K kh ke)).
   by rewrite /=h_merge_union_KEr.
   by rewrite /=h_merge_union_KEl.
Qed.

Lemma merge_union_KD2_rr (F K: graph) (i o: K) (h: pairs (F+K)) (k: K -> F)
      (ke: edge K -> False)
      (kh: forall x: K, unr x = unl (k x) %[mod_eq (eqv_clot h)]):
  point (merge_seq (union F K) h) (\pis (unr i)) (\pis (unr o))
≈ point (merge_seq F (union_K_pairs h k)) (\pis (k i)) (\pis (k o)).
Proof.
  eapply iso_iso2'; first (by apply (iso_merge_union_K kh ke)); by rewrite /=h_merge_union_KEr.
Qed.




(** * 2p-graphs form a 2p-algebra *)

Lemma par2C (F G: graph2): F ∥ G ≡ G ∥ F.
Proof.
  rewrite /=/par2.
  rewrite (merge_iso2 (iso_union_C _ _)) /=.
  apply merge_same.
  apply eqv_clot_eq. leqv. leqv. 
  eqv. eqv. 
Qed.

Lemma par2top (F: graph2): F ∥ top ≡ F.
Proof.
  rewrite /=/par2 (merge_union_K_ll (K:=top2) _ _ (k:=fun b => if b then g_out else g_in)).
  apply merge_nothing.
  repeat (constructor =>//=).
  by [].
  intros [|]; apply /eqquotP; eqv. 
Qed.

Lemma par2A (F G H: graph2): F ∥ (G ∥ H) ≡ (F ∥ G) ∥ H.
Proof.
  rewrite /=/par2/=.
  rewrite (merge_iso2 (iso_union_merge_r _ _)) /=.
  rewrite (merge_iso2 (iso_union_merge_l _ _)) /=.
  rewrite 2!h_union_merge_rEl 2!h_union_merge_lEl.
  rewrite 2!h_union_merge_rEr 2!h_union_merge_lEr.
  rewrite (merge_merge (G:=union F (union G H))
                       (k:=[::(unl g_in,unr (unl g_in)); (unl g_out,unr (unl g_out))])) =>//.
  rewrite (merge_merge (G:=union (union F G) H)
                       (k:=[::(unl (unl g_in),unr g_in); (unl (unl g_out),unr g_out)])) =>//.
  rewrite (merge_iso2 (iso_union_A _ _ _)) /=.
  apply merge_same'.
  apply eqv_clot_eq.
   constructor. apply eqv_clot_trans with (unl (unl (g_in))); eqv. 
   constructor. apply eqv_clot_trans with (unl (unl (g_out))); eqv.
   leqv.

   constructor. eqv. 
   constructor. eqv. 
   constructor. apply eqv_clot_trans with (unl (unr g_in)); eqv. 
   constructor. apply eqv_clot_trans with (unl (unr g_out)); eqv. 
   leqv.
Qed.

Lemma dot2one (F: graph2): F · 1 ≡ F.
Proof.
  rewrite /=/dot2 (merge_union_K_lr _ _ (k:=fun _ => g_out)).
  destruct F. apply merge_nothing.
  repeat (constructor =>//=).
  by [].
  intros []; apply /eqquotP; eqv.
Qed.

Lemma dot2A (F G H: graph2): F · (G · H) ≡ (F · G) · H.
Proof.
  rewrite /=/dot2/=.
  rewrite (merge_iso2 (iso_union_merge_r _ _)) /=.
  rewrite (merge_iso2 (iso_union_merge_l _ _)) /=.
  rewrite 2!h_union_merge_rEl 2!h_union_merge_lEl.
  rewrite 2!h_union_merge_rEr 2!h_union_merge_lEr.
  rewrite (merge_merge (G:=union F (union G H))
                       (k:=[::(unl g_out,unr (unl g_in))])) =>//.
  rewrite (merge_merge (G:=union (union F G) H)
                       (k:=[::(unl (unr g_out),unr g_in)])) =>//. 
  rewrite (merge_iso2 (iso_union_A _ _ _)) /=.
  apply merge_same'.
  apply eqv_clot_eq; leqv.
Qed.

Lemma cnv2I (F: graph2): F°° ≡ F.
Proof. destruct F. reflexivity. Qed.

Lemma cnv2par (F G: graph2): (F ∥ G)° ≡ F° ∥ G°.
Proof.
  rewrite /=/cnv2/par2/=.
  apply merge_same'.
  apply eqv_clot_eq; leqv.
Qed.

Lemma cnv2dot (F G: graph2): (F · G)° ≡ G° · F°.
Proof.
  rewrite /=/cnv2/dot2/=. 
  rewrite (merge_iso2 (iso_union_C _ _)) /=.
  apply merge_same'.
  apply eqv_clot_eq; simpl; leqv.
Qed.

Lemma par2oneone: 1 ∥ 1 ≡ one2.
Proof.
  rewrite /=/par2/=.
  rewrite (merge_union_K_ll (F:=unit_graph) (K:=unit_graph) _ _ (k:=fun _ => tt)).
  simpl. apply merge_nothing.
  repeat (constructor =>//=).
  by [].
  intros []; apply /eqquotP; eqv.
Qed.

Lemma dom2E (F: graph2): dom F ≡ 1 ∥ (F · top).
Proof.
  rewrite par2C/=/dom2/par2/dot2/=.
  rewrite (merge_iso2 (iso_union_merge_l _ _)) /=.
  rewrite 2!h_union_merge_lEl 1!h_union_merge_lEr.
  rewrite (merge_merge (G:=union (union F two_graph) unit_graph)
                       (k:=[::(unl (unl g_in),unr (tt: unit_graph)); (unl (unr (true: two_graph)),unr (tt: unit_graph))])) =>//.
  rewrite (merge_iso2 (iso_union_A' _ _ _)) /=.
  rewrite (merge_union_K_lr (K:=union two_graph unit_graph) _ _ 
                             (k:=fun x => match x with inl false => g_out | _ => g_in end)).
  symmetry. apply merge_nothing. 
  repeat (constructor =>//=).
  by intros [|].
  intros [[|]|[]]; apply /eqquotP; try eqv.
  apply eqv_clot_trans with (unr (unr (tt: unit_graph))); eqv. 
Qed.

Lemma A10 (F G: graph2): 1 ∥ F·G ≡ dom (F ∥ G°).
Proof.
  rewrite par2C/=/par2/dot2/dom2/cnv2.
  rewrite (merge_iso2 (iso_union_merge_l _ _)) /=.
  rewrite 2!h_union_merge_lEl 1!h_union_merge_lEr.
  rewrite (merge_merge (G:=union (union F G) unit_graph)
                       (k:=[::(unl (unl g_in),unr (tt: unit_graph)); (unl (unr g_out),unr (tt: unit_graph))])) =>//.
  rewrite (merge_union_K_ll (F:=union F G) _ _ (k:=fun x => unl g_in)).
  2: by []. 2: intros []; apply /eqquotP; simpl; eqv.
  apply merge_same; simpl.
  apply eqv_clot_eq; simpl; leqv.
  eqv.
  eqv.
Qed.

Lemma A11' (F: graph2): F·top ≡ point (union F unit_graph) (unl g_in) (unr (tt: unit_graph)).
Proof.
  rewrite /=/dot2/=.
  rewrite (merge_iso2 (iso_union iso_id iso_two_graph))/=. 
  rewrite (merge_iso2 (iso_union_A _ _ _))/=. 
  rewrite (merge_union_K_ll (F:=union F _) _ _ (k:=fun x => unl g_out))//=.
  apply merge_nothing. by constructor. 
  intros []. apply /eqquotP. eqv. 
Qed.

Lemma A11 (F: graph2): F·top ≡ dom F·top.
Proof. now rewrite 2!A11'. Qed.

Lemma A12' (F G: graph2): @g_in F = @g_out F -> F·G ≡ F·top ∥ G.
Proof.
  intro H. rewrite /=/par2/dot2/=.
  rewrite (merge_iso2 (iso_union_merge_l _ _)) /=.
  rewrite 2!h_union_merge_lEl 2!h_union_merge_lEr.
  rewrite (merge_merge (G:=union (union F two_graph) G)
                       (k:=[::(unl (unl g_in),unr g_in);(unl (unr (true: two_graph)),unr g_out)])) =>//.
  rewrite (merge_iso2 (iso_union_C (union _ _) _)) /=.
  rewrite (merge_iso2 (iso_union_A _ _ _)) /=.
  rewrite (merge_union_K_lr (F:=union G F) (K:=two_graph) _ _ 
                            (k:=fun x => if x then unl g_out else unr g_in)).
  2: intros []. 2: intros []; apply /eqquotP; rewrite H; eqv.
  rewrite (merge_iso2 (iso_union_C _ _)) /=.
  apply merge_same'. rewrite H. apply eqv_clot_eq; leqv.
Qed.

Lemma A12 (F G: graph2): (F ∥ 1)·G ≡ (F ∥ 1)·top ∥ G.
Proof.
  apply A12'.
  apply /eqquotP. apply eqv_clot_trans with (unr (tt: unit_graph)); eqv.
Qed.

Lemma dot2_iso2: Proper (iso2 ==> iso2 ==> iso2) dot2.
Proof.
  intros F F' (f&[Hf fi]&fo) G G' (g&[Hg gi]&go). rewrite /dot2.
  rewrite (merge_iso2 (iso_union Hf Hg))/=.
  apply merge_same; simpl; rewrite ?fi ?fo ?gi ?go //. 
Qed.  

Lemma par2_iso2: Proper (iso2 ==> iso2 ==> iso2) par2.
Proof.
  intros F F' (f&[Hf fi]&fo) G G' (g&[Hg gi]&go). rewrite /par2.
  rewrite (merge_iso2 (iso_union Hf Hg))/=.
  apply merge_same; simpl; rewrite ?fi ?fo ?gi ?go //. 
Qed.

Lemma cnv2_iso2: Proper (iso2 ==> iso2) cnv2.
Proof. intros F F' (f&[[Hf fi] fo]&FF). now exists f. Qed.

Global Instance graph2_laws: ptt_laws graph2_ops.
Proof.
  constructor.
  apply iso2_Equivalence.
  apply dot2_iso2. 
  apply par2_iso2. 
  apply cnv2_iso2.
  apply dom2E. 
  apply par2A. 
  apply par2C. 
  apply dot2A. 
  apply dot2one.
  apply cnv2I.
  apply cnv2par.
  apply cnv2dot.
  apply par2oneone.
  apply A10.
  apply A11.
  apply A12.
Qed.



Lemma graph_of_big_par (T : eqType) (r : seq T) F : 
  graph_of_term (\big[@tm_par _/@tm_top _]_(x <- r) F x) ≈
  \big[par2/top2]_(x <- r) graph_of_term (F x).
Proof. by elim: r => [|i r IH]; rewrite ?big_nil ?big_cons /= ?IH. Qed.

Lemma graph_of_big_pars (T : finType) (r : {set T}) F : 
  graph_of_term (\big[@tm_par _/@tm_top _]_(x in r) F x) ≈
  \big[par2/top2]_(x in r) graph_of_term (F x).
Proof. by rewrite -!big_enum_in graph_of_big_par. Qed.

Lemma big_par_iso2 (T : eqType) (s : seq T) idx F G : 
  (forall x, x \in s -> F x ≈ G x) ->
  \big[par2/idx]_(x <- s) F x ≈ \big[par2/idx]_(x <- s) G x.
Proof.
  move => A. 
  elim: s A => [_|i s IH /all_cons [A B]].
  by rewrite !big_nil. 
  rewrite !big_cons. apply: par2_iso2; auto. 
Qed.


Section alt.
 Variables F G: graph2.
 Import ssrbool.

 Definition par2_eqv : rel (union F G) :=
   fun x y => (x == y) ||
     if (g_in != g_out :> F) && (g_in != g_out :> G)
     then [set x; y] \in [set [set inl g_in; inr g_in]; [set inl g_out; inr g_out]]
     else [set x; y] \subset [set inl g_in; inl g_out; inr g_in; inr g_out].

 Definition par2_eqv_refl : ssrbool.reflexive par2_eqv.
 Proof. by move=> ?; rewrite /par2_eqv eqxx. Qed.

 Lemma par2_eqv_sym : ssrbool.symmetric par2_eqv.
 Proof. move=> x y. by rewrite /par2_eqv [[set y; x]]setUC [y == x]eq_sym. Qed.

 Definition par2_eqv_trans : ssrbool.transitive par2_eqv.
 Proof.
   move=> y x z. rewrite /par2_eqv.
   case/altP: (x =P y) => [<-//|xNy/=]. case/altP: (y =P z) => [<-->//=|yNz/=]. 
   case/boolP: ((g_in != g_out :> F) && (g_in != g_out :> G)).
   - rewrite !inE -(implyNb (x == z)).
     case/andP=> /negbTE iNo1 /negbTE iNo2 Hxy Hyz. apply/implyP=> xNz.
     move: Hxy xNy. rewrite 2!eqEcard 2!subUset 4!sub1set !inE.
     case/orP => /andP[]/andP[] /orP[]/eqP ? /orP[]/eqP ? _; subst=> // _.
     all: move: Hyz xNz yNz; rewrite 2!eqEcard 2!subUset 4!sub1set !inE.
     all: rewrite ?eqxx ?sum_eqE ?[g_out == g_in]eq_sym ?iNo1 ?iNo2 ?orbT ?orbF /=.
     all: case/andP => /orP[]/eqP-> _; by rewrite !eqxx.
   - rewrite -implyNb => _ Hxy Hyz. apply/implyP=> xNz.
     rewrite subUset !sub1set. apply/andP; split.
     + apply: (subsetP Hxy). by rewrite !inE eqxx.
     + apply: (subsetP Hyz). by rewrite !inE eqxx.
 Qed.

 Canonical par2_eqv_equivalence :=
   EquivRel par2_eqv par2_eqv_refl par2_eqv_sym par2_eqv_trans.

 Lemma par2_eqv_io :
   (par2_eqv (inl g_in) (inr g_in)) * (par2_eqv (inl g_out) (inr g_out)).
 Proof.
   rewrite /par2_eqv/=. case: ifP => _.
   - by rewrite !inE !eqxx.
   - by rewrite !subUset !sub1set !inE !eqxx.
 Qed.

 Definition par2_eq (x y : union F G) :=
   match x,y with
   | inl x, inr y => (x == g_in) && (y == g_in) || (x == g_out) && (y == g_out)
   | _,_ => false
   end.

 Lemma set2_in_sym (T : finType) (x y a b : T) (e : rel T) :  
   x != y -> ssrbool.symmetric e -> e a b -> [set x;y] == [set a;b] -> e x y.
 Proof.
   move => xDy sym_e e_ab E. move: E xDy. rewrite eqEsubset !subUset !sub1set -andbA.
   case/and3P => /set2P[->|->] /set2P[->|->] _; by rewrite ?eqxx // sym_e.
 Qed.

 Hint Resolve equiv_of_sym.
 Ltac sub := apply: sub_equiv_of => /=; by rewrite !eqxx.

 Lemma par2_equiv_of : par2_eqv =2 equiv_of par2_eq.
 Proof using.
   move=> x y. apply/idP/idP.
   - rewrite /par2_eqv. case/altP: (x =P y) => [<- _|xNy]/=; first exact: equiv_of_refl.
     case: ifP => [_|/negbT].
     + rewrite !inE. case/orP; apply: set2_in_sym => //; sub.
     + rewrite negb_and 2!negbK. case/orP=> [/eqP Eio1|/eqP Eio2].
       * rewrite -Eio1 setUid => Exy.
         have Rio2 : equiv_of par2_eq (inr g_out) (inr g_in). 
         { apply: (@equiv_of_trans _ _ (inl g_in)); first rewrite equiv_of_sym Eio1; sub. }
         move: Exy xNy; rewrite subUset 2!sub1set !inE -2!orbA.
         case/andP=> /or3P[]/eqP-> /or3P[]/eqP->.
         all: rewrite ?eqxx // ?[equiv_of _ _ (inl _)]equiv_of_sym => _.
         all: try solve [apply: (@sub_equiv_of _ _ (inl _));
                         by rewrite /par2_eq -?Eio1 !eqxx].
         by rewrite equiv_of_sym.
       * rewrite -setUA -Eio2 setUid => Exy.
         have Rio2 : equiv_of par2_eq (inl g_out) (inl g_in).
         { apply: (@equiv_of_trans _ _ (inr g_out)); last rewrite equiv_of_sym -Eio2;
           by apply: sub_equiv_of; rewrite /par2_eq !eqxx. }
         move: Exy xNy; rewrite subUset 2!sub1set !inE -2!orbA.
         case/andP=> /or3P[]/eqP-> /or3P[]/eqP->.
         all: rewrite ?eqxx // ?[equiv_of _ (inr _) _]equiv_of_sym => _.
         all: try solve [apply: (@sub_equiv_of _ _ (inl _));
                         by rewrite /par2_eq -?Eio2 !eqxx].
         by rewrite equiv_of_sym.
   - apply: equiv_of_sub; auto using par2_eqv_refl,par2_eqv_sym,par2_eqv_trans.
     move => {x y} [x|x] [y|y] => //=. 
     by case/orP; case/andP => /eqP-> /eqP->; rewrite par2_eqv_io.
 Qed.

 Lemma par2_eqv_ii x y : 
   x = g_in :> F -> y = g_in :> G ->
   par2_eqv (inl x) (inr y).
 Proof.
   move => -> ->. rewrite par2_equiv_of. apply: sub_equiv_of.
     by rewrite /par2_eq !eqxx. 
 Qed.
 
 Lemma par2_eqv_oo x y : 
   x = g_out :> F -> y = g_out :> G ->
   par2_eqv (inl x) (inr y).
 Proof.
   move => -> ->. rewrite par2_equiv_of. apply: sub_equiv_of.
     by rewrite /par2_eq !eqxx. 
 Qed.

 Transparent union.
 Lemma par2_LR x y :
   inl x = inr y %[mod_eq par2_eqv] ->
   x = g_in /\ y = g_in \/ x = g_out /\ y = g_out.
 Proof.
   move/eqmodP. rewrite /=/par2_eqv /eq_op/= -!/eq_op. case: ifP => i_o.
   - rewrite !inE !eqEsubset. case/orP=> /andP[H _]; move: H.
     all: rewrite subUset !sub1set !inE /eq_op/= orbF =>/andP[/eqP-> /eqP->].
     + by left.
     + by right.
   - move/negbT: i_o. rewrite negb_and !negbK. case/orP=> /eqP<-.
     all: rewrite subUset !sub1set !inE /eq_op/= !orbF orbb.
     + case/andP=> /eqP-> /orP[]/eqP->; by [left | right].
     + case/andP=> /orP[]/eqP-> /eqP->; by [left | right].
 Qed.
 Opaque union.

 Lemma par2_injL x y : 
   g_in != g_out :> G -> 
   inl x = inl y %[mod_eq par2_eqv] ->
   x = y.
 Proof.
   move=> iNo2 /eqmodP/=. rewrite /par2_eqv/= iNo2 andbT sum_eqE.
   case/orP=> [/eqP//|]. case: ifP => [iNo1 | /negbFE/eqP<-].
   - rewrite !inE !eqEsubset ![[set inl x; inl y] \subset _]subUset !sub1set !inE.
     rewrite /eq_op/= !orbF. by case/orP=> /andP[]/andP[/eqP-> /eqP->].
   - by rewrite subUset !sub1set !inE /eq_op/= !orbF !orbb => /andP[/eqP-> /eqP->].
 Qed.
  
 Lemma par2_injR x y : 
   g_in != g_out :> F -> 
   inr x = inr y %[mod_eq par2_eqv] ->
   x = y.
 Proof.
   move=> iNo2 /eqmodP/=. rewrite /par2_eqv/= iNo2 /= sum_eqE.
   case/orP=> [/eqP//|]. case: ifP => [iNo1 | /negbFE/eqP<-].
   - rewrite !inE !eqEsubset ![[set inr x; inr y] \subset _]subUset !sub1set !inE.
     rewrite /eq_op/=. by case/orP=> /andP[]/andP[/eqP-> /eqP->].
   - by rewrite subUset !sub1set !inE /eq_op/= !orbb => /andP[/eqP-> /eqP->].
 Qed.
 
 Definition par2' := 
   {| graph_of := merge (union F G) par2_eqv ;
      g_in := \pi_{eq_quot par2_eqv} (inl g_in);
      g_out := \pi_{eq_quot par2_eqv} (inl g_out) |}.

 Lemma par2_eqE: par2_eq =2 rel_of_pairs [::(unl g_in,unr g_in);(unl g_out,unr g_out)].
 Admitted.

 Lemma par2_eqvE: par2_eqv =2 equiv_of (rel_of_pairs [::(unl g_in,unr g_in);(unl g_out,unr g_out)]).
 Admitted.
 
 Lemma par2_alt: par2 F G ≈ par2'.
 Admitted.


 Definition dot2_eqv : rel (union F G) :=
   fun x y => (x == y) || ([set x; y] == [set inl g_out; inr g_in]).

 Definition dot2_eqv_refl : ssrbool.reflexive dot2_eqv.
 Proof. by move=> ?; rewrite /dot2_eqv eqxx. Qed.

 Lemma dot2_eqv_sym : ssrbool.symmetric dot2_eqv.
 Proof. move=> x y. by rewrite /dot2_eqv [[set y; x]]setUC [y == x]eq_sym. Qed.

 Definition dot2_eqv_trans : ssrbool.transitive dot2_eqv.
 Proof using.
   move=> y x z. rewrite /dot2_eqv.
   case/altP: (x =P y) => [<-//|/= xNy Exy].
   case/altP: (y =P z) => [<-|/= yNz Eyz]; first by rewrite Exy.
   case/altP: (x =P z) => //= xNz.
   have := eq_refl #|[set inl (@g_out F); inr (@g_in G)]|.
   rewrite -{1}(setUid [set _; _]) -{1}(eqP Exy) -{1}(eqP Eyz).
   rewrite set2C -setUUr (cardsU1 y) !cards2 !inE.
   by rewrite (eq_sym y x) negb_or xNy yNz xNz.
 Qed.

 Canonical dot2_eqv_equivalence :=
   EquivRel dot2_eqv dot2_eqv_refl dot2_eqv_sym dot2_eqv_trans.

 Lemma dot2_eqv_io : dot2_eqv (inl g_out) (inr g_in).
 Proof. rewrite /dot2_eqv/=. Admitted.

 Definition dot2_eq : simpl_rel (union F G) :=
   [rel a b | (a == inl g_out) && (b == inr g_in)].

 Lemma dot2_equiv_of : dot2_eqv =2 equiv_of dot2_eq.
 Proof using.
   move=> x y. apply/idP/idP.
   - rewrite/dot2_eqv. case/altP: (x =P y) => [<- _|xNy]; first exact: equiv_of_refl.
     apply: set2_in_sym => //. sub.
   - apply: equiv_of_sub; auto using dot2_eqv_refl,dot2_eqv_sym,dot2_eqv_trans.
     move => {x y} [x|x] [y|y] //=; case/andP => /eqP -> /eqP ->; by rewrite dot2_eqv_io.
 Qed.

 Lemma dot2_injL (x y : F) :
   inl x = inl y %[mod_eq dot2_eqv] -> x = y.
 Proof.
   move=> /eqmodP. rewrite /=/dot2_eqv/= sum_eqE. case/orP=> [/eqP//|].
   by rewrite eq_sym eqEcard subUset -andbA andbCA !sub1set !inE.
 Qed.
 
 Lemma dot2_injR (x y : G) :
   inr x = inr y %[mod_eq dot2_eqv] -> x = y.
 Proof.
   move=> /eqmodP. rewrite /=/dot2_eqv/= sum_eqE. case/orP=> [/eqP//|].
   by rewrite eq_sym eqEcard subUset !sub1set !inE.
 Qed.

 Transparent union.
 Lemma dot2_LR (x : F) (y : G) :
   inl x = inr y %[mod_eq dot2_eqv] -> x = g_out /\ y = g_in.
 Proof.
   move=> /eqmodP. rewrite /=/dot2_eqv/=.
   rewrite eq_sym eqEcard subUset !sub1set !inE orbC /= !sum_eqE.
   by case/andP=> /andP[/eqP<- /eqP<-].
 Qed.
 Opaque union.
 
 Definition dot2' :=
   {| graph_of := merge (union F G) dot2_eqv ;
      g_in := \pi_{eq_quot dot2_eqv} (inl g_in);
      g_out := \pi_{eq_quot dot2_eqv} (inr g_out) |}.

 Lemma dot2_eqE: dot2_eq =2 rel_of_pairs [::(unl g_out,unr g_in)].
 Admitted.

 Lemma dot2_eqvE: dot2_eqv =2 equiv_of (rel_of_pairs [::(unl g_out,unr g_in)]).
 Admitted.
 
 Lemma dot2_alt: dot2 F G ≈ dot2'.
 Admitted.
End alt.

