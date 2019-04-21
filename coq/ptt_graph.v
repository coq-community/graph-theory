From mathcomp Require Import all_ssreflect.
Require Import finite_quotient preliminaries equiv ptt_algebra multigraph.

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

Local Instance iso2_Equivalence: Equivalence iso2.
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

