Require Import Setoid CMorphisms.
From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries equiv ptt_algebra multigraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
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


Class is_hom2 (F G: graph2) (hv: F -> G) (he: edge F -> edge G): Prop := Hom2
  { hom2_hom: is_hom hv he;
    hom_in: hv g_in = g_in;
    hom_out: hv g_out = g_out }.

Lemma hom2_id G: @is_hom2 G G id id.
Proof. by split. Qed.

Lemma hom2_comp F G H hv he kv ke:
  @is_hom2 F G hv he -> @is_hom2 G H kv ke -> is_hom2 (kv \o hv) (ke \o he).
Proof.
  intros E E'. split. apply hom_comp. apply E. apply E'.
  by rewrite /=2!hom_in. 
  by rewrite /=2!hom_out. 
Qed.

Lemma hom2_sym (F G: graph2) (hv: bij F G) (he: bij (edge F) (edge G)):
  is_hom2 hv he -> 
  is_hom2 hv^-1 he^-1.
Proof.
  intro H. split. apply hom_sym, H. 
  by rewrite -(bijK hv g_in) hom_in.
  by rewrite -(bijK hv g_out) hom_out.
Qed.

Record iso2 (F G: graph2): Type := Iso2
  { iso2_v: bij F G;
    iso2_e: bij (edge F) (edge G);
    iso2_hom2: is_hom2 iso2_v iso2_e }.
Existing Instance iso2_hom2.

Notation "G ≈ H" := (iso2 G H) (at level 45).

Definition iso2_iso F G (h: iso2 F G): iso F G := Iso (@hom2_hom _ _ _ _ (iso2_hom2 h)).
Coercion iso2_iso: iso2 >-> iso.

Lemma iso_in F G (h: F ≈ G): h g_in = g_in.
Proof. apply hom_in. Qed.

Lemma iso_out F G (h: F ≈ G): h g_out = g_out.
Proof. apply hom_out. Qed.

Lemma Iso2' (F G: graph2) (h: iso F G) (hi: h g_in = g_in) (ho: h g_out = g_out): F ≈ G.
  apply Iso2 with (iso_v h) (iso_e h). abstract (split=>//; apply h).
Defined.

Definition Iso2'' F G f g h k fg gf hk kh H I O :=  
  @Iso2 F G (@Bij _ _ f g fg gf) (@Bij _ _ h k hk kh) (@Hom2 _ _ f h (Hom' H) I O).


Definition iso2_id G: G ≈ G := Iso2' (h:=iso_id) erefl erefl. 

Definition iso2_sym F G: F ≈ G -> G ≈ F.
Proof.
  move => f. 
  apply Iso2 with (bij_sym f) (bij_sym (iso_e f)) =>/=.
  apply hom2_sym, f. 
Defined.

Definition iso2_comp F G H: F ≈ G -> G ≈ H -> F ≈ H.
Proof.
  move => f g. 
  apply Iso2 with (bij_comp f g) (bij_comp (iso_e f) (iso_e g)) =>/=.
  apply hom2_comp. apply f. apply g.
Defined.

Instance iso2_Equivalence: Equivalence iso2.
constructor. exact @iso2_id. exact @iso2_sym. exact @iso2_comp. Defined.

(* TODO: added this hint so that by/done solve these cases, is there a nicer way to proceeed? *)
Lemma iso2_refl G: G ≈ G.
Proof. reflexivity. Qed.
Hint Resolve iso2_refl.

Lemma iso_in' F G (h: F ≈ G): h^-1 g_in = g_in.
Proof. apply (iso_in (iso2_sym h)). Qed.

Lemma iso_out' F G (h: F ≈ G): h^-1 g_out = g_out.
Proof. apply (iso_out (iso2_sym h)). Qed.


(** * two pointed graph constructions *)

Definition par2 (F G: graph2) :=
  point (merge_seq (union F G) [::(unl g_in,unr g_in); (unl g_out,unr g_out)])
        (\pi (unl g_in)) (\pi (unl g_out)).

Definition dot2 (F G: graph2) :=
  point (merge_seq (union F G) [::(unl g_out,unr g_in)])
        (\pi (unl g_in)) (\pi (unr g_out)).

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

Opaque merge union.

(** * from isomorphisms on graphs to isomorphisms on 2p-graphs *)

Lemma iso_iso2 (F G: graph) (h: iso F G) (i o: F):
  point F i o ≈ point G (h i) (h o).
Proof. now apply Iso2' with h. Qed.

Lemma iso_iso2' (F G: graph) (h: iso F G) (i o: F) (i' o': G):
  i' = h i -> o' = h o -> point F i o ≈ point G i' o'.
Proof. intros -> ->. by apply iso_iso2. Qed.

Lemma union_C2 (F G: graph) (i o: F+G):
  point (union F G) i o ≈ point (union G F) (sumC i) (sumC o).
Proof. apply (iso_iso2 (union_C _ _)). Qed.

Lemma union_A2 (F G H: graph) (i o: F+(G+H)):
  point (union F (union G H)) i o ≈ point (union (union F G) H) (sumA i) (sumA o).
Proof. apply (iso_iso2 (union_A _ _ _)). Qed.

Lemma union_A2' (F G H: graph) (i o: (F+G)+H):
  point (union (union F G) H) i o ≈ point (union F (union G H)) (sumA' i) (sumA' o).
Proof. apply (iso_iso2 (iso_sym (union_A _ _ _))). Qed.

Lemma merge_iso2 (F G : graph) (h: iso F G) l (i o: F):
  point (merge_seq F l) (\pi i) (\pi o) ≈
  point (merge_seq G (map_pairs h l)) (\pi (h i)) (\pi (h o)).
Proof. apply (iso_iso2' (h:=merge_iso h l)); by rewrite h_mergeE. Qed.

Lemma merge_same (F : graph) (h k: equiv_rel F) (i i' o o': F):
  (h =2 k) ->
  h i i' ->
  h o o' ->
  point (merge F h) (\pi i) (\pi o) ≈ point (merge F k) (\pi i') (\pi o').
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
  point (merge_seq F h) (\pi i) (\pi o) ≈ point (merge_seq F k) (\pi i') (\pi o').
Proof. apply merge_same. Qed.

Lemma merge_seq_same' (F : graph) (h k: pairs F) (i o: F):
  (eqv_clot h =2 eqv_clot k) ->
  point (merge_seq F h) (\pi i) (\pi o) ≈ point (merge_seq F k) (\pi i) (\pi o).
Proof.
  intros. by apply merge_seq_same. 
Qed.

Lemma merge_nothing (F: graph) (h: pairs F) (i o: F):
  List.Forall (fun p => p.1 = p.2) h ->
  point (merge_seq F h) (\pi i) (\pi o) ≈ point F i o.
Proof.
  intros H. apply (iso_iso2' (h:=merge_nothing H)); by rewrite merge_nothingE.
Qed.


(** ** merge_merge  *)
Lemma merge_merge (G: graph) (h k: pairs G) (k': pairs (merge_seq G h)) (i o: G):
  k' = map_pairs (pi (eqv_clot h)) k ->
  point (merge_seq (merge_seq G h) k') (\pi (\pi i)) (\pi (\pi o))
≈ point (merge_seq G (h++k)) (\pi i) (\pi o).
Proof.
  intro K. apply (iso_iso2' (h:=merge_merge_seq K)); by rewrite /=merge_merge_seqE. 
Qed.

(** ** union_merge_l  *)
Lemma union_merge_l_ll (F G: graph) (i o: F) (h: pairs F):
  point (union (merge_seq F h) G) (inl (\pi i)) (inl (\pi o))
≈ point (merge_seq (union F G) (map_pairs unl h)) (\pi (unl i)) (\pi (unl o)).
Proof. apply (iso_iso2' (h:=union_merge_l _ _)); by rewrite /=union_merge_lEl. Qed.

Lemma union_merge_l_lr (F G: graph) (i: F) (o: G) (h: pairs F):
  point (union (merge_seq F h) G) (inl (\pi i)) (inr o)
≈ point (merge_seq (union F G) (map_pairs unl h)) (\pi (unl i)) (\pi (unr o)).
Proof.
  apply (iso_iso2' (h:=union_merge_l _ _)).
    by rewrite /=union_merge_lEl.
    by rewrite /=union_merge_lEr.
Qed.

Lemma union_merge_l_rl (F G: graph) (i: G) (o: F) (h: pairs F):
  point (union (merge_seq F h) G) (unr i) (inl (\pi o))
≈ point (merge_seq (union F G) (map_pairs unl h)) (\pi (unr i)) (\pi (unl o)).
Proof.
  apply (iso_iso2' (h:=union_merge_l _ _)).
    by rewrite /=union_merge_lEr.
    by rewrite /=union_merge_lEl.
Qed.

Lemma union_merge_l_rr (F G: graph) (i o: G) (h: pairs F):
  point (union (merge_seq F h) G) (unr i) (unr o)
≈ point (merge_seq (union F G) (map_pairs unl h)) (\pi (unr i)) (\pi (unr o)).
Proof. apply (iso_iso2' (h:=union_merge_l _ _)); by rewrite /=union_merge_lEr. Qed.

(** ** union_merge_r  *)
Lemma union_merge_r_ll (F G: graph) (i o: F) (h: pairs G):
  point (union F (merge_seq G h)) (unl i) (unl o)
≈ point (merge_seq (union F G) (map_pairs unr h)) (\pi (unl i)) (\pi (unl o)).
Proof. apply (iso_iso2' (h:=union_merge_r _ _)); by rewrite union_merge_rEl. Qed.

Lemma union_merge_r_lr (F G: graph) (i: F) (o: G) (h: pairs G):
  point (union F (merge_seq G h)) (unl i) (inr (\pi o))
≈ point (merge_seq (union F G) (map_pairs unr h)) (\pi (unl i)) (\pi (unr o)).
Proof.
  apply (iso_iso2' (h:=union_merge_r _ _)).
    by rewrite union_merge_rEl.
    by rewrite union_merge_rEr.
Qed.

Lemma union_merge_r_rl (F G: graph) (i: G) (o: F) (h: pairs G):
  point (union F (merge_seq G h)) (inr (\pi i)) (unl o)
≈ point (merge_seq (union F G) (map_pairs unr h)) (\pi (unr i)) (\pi (unl o)).
Proof.
  apply (iso_iso2' (h:=union_merge_r _ _)).
    by rewrite union_merge_rEr.
    by rewrite union_merge_rEl.
Qed.

Lemma union_merge_r_rr (F G: graph) (i o: G) (h: pairs G):
  point (union F (merge_seq G h)) (inr (\pi i)) (inr (\pi o))
≈ point (merge_seq (union F G) (map_pairs unr h)) (\pi (unr i)) (\pi (unr o)).
Proof. apply (iso_iso2' (h:=union_merge_r _ _)); by rewrite union_merge_rEr. Qed.

(** ** merge_union_K  *)
Lemma merge_union_K_ll (F K: graph) (i o: F) (h: pairs (F+K)) (k: K -> F)
      (ke: edge K -> False)
      (kh: forall x: K, unr x = unl (k x) %[mod (eqv_clot h)]):
  point (merge_seq (union F K) h) (\pi (unl i)) (\pi (unl o))
≈ point (merge_seq F (union_K_pairs h k)) (\pi i) (\pi o).
Proof.
  apply (iso_iso2' (h:=merge_union_K kh ke)); by rewrite /=merge_union_KEl.
Qed.

Lemma merge_union_K_lr (F K: graph) (i: F) (o: K) (h: pairs (F+K)) (k: K -> F)
      (ke: edge K -> False)
      (kh: forall x: K, unr x = unl (k x) %[mod (eqv_clot h)]):
  point (merge_seq (union F K) h) (\pi (unl i)) (\pi (unr o))
≈ point (merge_seq F (union_K_pairs h k)) (\pi i) (\pi (k o)).
Proof.
  apply (iso_iso2' (h:=merge_union_K kh ke)).
   by rewrite /=merge_union_KEl.
   by rewrite /=merge_union_KEr.
Qed.

Lemma merge_union_K_rl (F K: graph) (i: K) (o: F) (h: pairs (F+K)) (k: K -> F)
      (ke: edge K -> False)
      (kh: forall x: K, unr x = unl (k x) %[mod (eqv_clot h)]):
  point (merge_seq (union F K) h) (\pi (unr i)) (\pi (unl o))
≈ point (merge_seq F (union_K_pairs h k)) (\pi (k i)) (\pi o).
Proof.
  apply (iso_iso2' (h:=merge_union_K kh ke)).
   by rewrite /=merge_union_KEr.
   by rewrite /=merge_union_KEl.
Qed.

Lemma merge_union_K_rr (F K: graph) (i o: K) (h: pairs (F+K)) (k: K -> F)
      (ke: edge K -> False)
      (kh: forall x: K, unr x = unl (k x) %[mod (eqv_clot h)]):
  point (merge_seq (union F K) h) (\pi (unr i)) (\pi (unr o))
≈ point (merge_seq F (union_K_pairs h k)) (\pi (k i)) (\pi (k o)).
Proof.
  apply (iso_iso2' (h:=merge_union_K kh ke)); by rewrite /=merge_union_KEr.
Qed.




(** * 2p-graphs form a 2p-algebra *)

Lemma par2C (F G: graph2): F ∥ G ≡ G ∥ F.
Proof.
  rewrite /=/par2.
  setoid_rewrite (merge_iso2 (union_C F G)) =>/=.
  apply merge_seq_same.
  apply eqv_clot_eq. leqv. leqv. 
  eqv. eqv. 
Qed.

Lemma par2top (F: graph2): F ∥ top ≡ F.
Proof.
  rewrite /=/par2.
  setoid_rewrite (merge_union_K_ll (K:=top2) _ _ (k:=fun b => if b then g_out else g_in)).
  setoid_rewrite merge_nothing. by rewrite -point_io. 
  repeat (constructor =>//=).
  by [].
  intros [|]; apply /eqquotP; eqv. 
Qed.

Lemma par2A (F G H: graph2): F ∥ (G ∥ H) ≡ (F ∥ G) ∥ H.
Proof.
  rewrite /=/par2/=.
  setoid_rewrite (merge_iso2 (@union_merge_r F (union G H) _))=> /=.
  rewrite 2!union_merge_rEl 2!union_merge_rEr.
  setoid_rewrite (merge_merge (G:=union F (union G H))
                              (k:=[::(unl g_in,unr (unl g_in)); (unl g_out,unr (unl g_out))])) =>//.
  setoid_rewrite (merge_iso2 (@union_merge_l (union F G) H _))=> /=.
  rewrite 2!union_merge_lEl 2!union_merge_lEr.
  setoid_rewrite (merge_merge (G:=union (union F G) H)
                              (k:=[::(unl (unl g_in),unr g_in); (unl (unl g_out),unr g_out)])) =>//=.
  setoid_rewrite (merge_iso2 (union_A _ _ _))=> /=.
  apply merge_seq_same'.
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
  rewrite /=/dot2.
  setoid_rewrite (merge_union_K_lr _ _ (k:=fun _ => g_out)).
  destruct F. apply merge_nothing.
  repeat (constructor =>//=).
  by [].
  intros []; apply /eqquotP; eqv.
Qed.

Lemma dot2A (F G H: graph2): F · (G · H) ≡ (F · G) · H.
Proof.
  rewrite /=/dot2/=.
  setoid_rewrite (merge_iso2 (union_merge_r _ _)) =>/=.
  rewrite 2!union_merge_rEl 2!union_merge_rEr.
  setoid_rewrite (merge_merge (G:=union F (union G H))
                              (k:=[::(unl g_out,unr (unl g_in))])) =>//.
  setoid_rewrite (merge_iso2 (union_merge_l _ _)) =>/=.
  rewrite 2!union_merge_lEl 2!union_merge_lEr.
  setoid_rewrite (merge_merge (G:=union (union F G) H)
                              (k:=[::(unl (unr g_out),unr g_in)])) =>//. 
  setoid_rewrite (merge_iso2 (union_A _ _ _)) =>/=.
  apply merge_seq_same'.
  apply eqv_clot_eq; leqv.
Qed.

Lemma cnv2I (F: graph2): F°° ≡ F.
Proof. destruct F. reflexivity. Qed.

Lemma cnv2par (F G: graph2): (F ∥ G)° ≡ F° ∥ G°.
Proof.
  rewrite /=/cnv2/par2/=.
  apply merge_seq_same'.
  apply eqv_clot_eq; leqv.
Qed.

Lemma cnv2dot (F G: graph2): (F · G)° ≡ G° · F°.
Proof.
  rewrite /=/cnv2/dot2/=. 
  setoid_rewrite (merge_iso2 (union_C F G))=>/=.
  apply merge_seq_same'.
  apply eqv_clot_eq; simpl; leqv.
Qed.

Lemma par2oneone: 1 ∥ 1 ≡ one2.
Proof.
  rewrite /=/par2/=.
  setoid_rewrite (merge_union_K_ll (F:=unit_graph) (K:=unit_graph) _ _ (k:=fun _ => tt))=>/=.
  simpl. apply merge_nothing.
  repeat (constructor =>//=).
  by [].
  intros []; apply /eqquotP; eqv.
Qed.

Lemma dom2E (F: graph2): dom F ≡ 1 ∥ (F · top).
Proof.
  setoid_rewrite par2C.
  rewrite /=/dom2/par2/dot2/=.
  setoid_rewrite (merge_iso2 (union_merge_l _ _))=>/=.
  rewrite 2!union_merge_lEl 1!union_merge_lEr.
  setoid_rewrite (merge_merge (G:=union (union F two_graph) unit_graph)
                              (k:=[::(unl (unl g_in),unr (tt: unit_graph)); (unl (unr (true: two_graph)),unr (tt: unit_graph))])) =>//.
  setoid_rewrite (merge_iso2 (iso_sym (union_A _ _ _))) =>/=.
  setoid_rewrite (merge_union_K_lr (K:=union two_graph unit_graph) _ _ 
                             (k:=fun x => match x with inl false => g_out | _ => g_in end)).
  symmetry. apply merge_nothing. 
  repeat (constructor =>//=).
  by intros [|].
  intros [[|]|[]]; apply /eqquotP; try eqv.
  apply eqv_clot_trans with (unr (unr (tt: unit_graph))); eqv. 
Qed.

Lemma A10 (F G: graph2): 1 ∥ F·G ≡ dom (F ∥ G°).
Proof.
  setoid_rewrite (par2C 1).
  rewrite /=/par2/dot2/dom2/cnv2.
  setoid_rewrite (merge_iso2 (union_merge_l _ _)) =>/=.
  rewrite 2!union_merge_lEl 1!union_merge_lEr.
  setoid_rewrite (merge_merge (G:=union (union F G) unit_graph)
                              (k:=[::(unl (unl g_in),unr (tt: unit_graph)); (unl (unr g_out),unr (tt: unit_graph))])) =>//.
  setoid_rewrite (merge_union_K_ll (F:=union F G) _ _ (k:=fun x => unl g_in)).
  2: by []. 2: intros []; apply /eqquotP; simpl; eqv.
  apply merge_seq_same; simpl.
  apply eqv_clot_eq; simpl; leqv.
  eqv.
  eqv.
Qed.

Lemma A11' (F: graph2): F·top ≡ point (union F unit_graph) (unl g_in) (unr (tt: unit_graph)).
Proof.
  rewrite /=/dot2/=.
  setoid_rewrite (merge_iso2 (union_iso (@iso_id _) iso_two_graph))=>/=. 
  setoid_rewrite (merge_iso2 (union_A _ _ _))=>/=. 
  setoid_rewrite (merge_union_K_ll (F:=union F _) _ _ (k:=fun x => unl g_out))=>//=.
  apply merge_nothing. by constructor. 
  intros []. apply /eqquotP. eqv. 
Qed.

Lemma A11 (F: graph2): F·top ≡ dom F·top.
Proof. now setoid_rewrite A11'. Qed.

Lemma A12' (F G: graph2): @g_in F = @g_out F -> F·G ≡ F·top ∥ G.
Proof.
  intro H. rewrite /=/par2/dot2/=.
  setoid_rewrite (merge_iso2 (union_merge_l _ _)) =>/=.
  rewrite 2!union_merge_lEl 2!union_merge_lEr.
  setoid_rewrite (merge_merge (G:=union (union F two_graph) G)
                              (k:=[::(unl (unl g_in),unr g_in);(unl (unr (true: two_graph)),unr g_out)])) =>//.
  setoid_rewrite (merge_iso2 (union_C (union _ _) _)) =>/=.
  setoid_rewrite (merge_iso2 (union_A _ _ _)) =>/=.
  setoid_rewrite (merge_union_K_lr (F:=union G F) (K:=two_graph) _ _ 
                            (k:=fun x => if x then unl g_out else unr g_in)).
  2: intros []. 2: intros []; apply /eqquotP; rewrite H; eqv.
  setoid_rewrite (merge_iso2 (union_C F G)) =>/=.
  apply merge_seq_same'. rewrite H. apply eqv_clot_eq; leqv.
Qed.

Lemma A12 (F G: graph2): (F ∥ 1)·G ≡ (F ∥ 1)·top ∥ G.
Proof.
  apply A12'.
  apply /eqquotP. apply eqv_clot_trans with (unr (tt: unit_graph)); eqv.
Qed.

Lemma dot2_iso2: Proper (iso2 ==> iso2 ==> iso2) dot2.
Proof.
  intros F F' f G G' g. rewrite /dot2.
  setoid_rewrite (merge_iso2 (union_iso f g))=>/=.
  apply merge_seq_same; by rewrite /= ?hom_in ?hom_out. 
Qed.  

Lemma par2_iso2: Proper (iso2 ==> iso2 ==> iso2) par2.
Proof.
  intros F F' f G G' g. rewrite /par2.
  setoid_rewrite (merge_iso2 (union_iso f g))=>/=.
  apply merge_seq_same; by rewrite /= ?hom_in ?hom_out. 
Qed.

Lemma cnv2_iso2: Proper (iso2 ==> iso2) cnv2.
Proof. intros F F' f. eexists. constructor; apply f. Qed.

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
Proof. by elim: r => [|i r IH]; rewrite ?big_nil ?big_cons //=; setoid_rewrite IH. Qed.

Lemma graph_of_big_pars (T : finType) (r : {set T}) F : 
  graph_of_term (\big[@tm_par _/@tm_top _]_(x in r) F x) ≈
  \big[par2/top2]_(x in r) graph_of_term (F x).
Proof. by rewrite -!big_enum_in; setoid_rewrite graph_of_big_par. Qed.

Lemma big_par_iso2 (T : eqType) (s : seq T) idx F G : 
  (forall x, x \in s -> F x ≈ G x) ->
  \big[par2/idx]_(x <- s) F x ≈ \big[par2/idx]_(x <- s) G x.
Proof.
  move => A. 
  elim: s A => [_|i s IH (* /all_cons [A B] *) E]. 
  by rewrite !big_nil. 
  rewrite !big_cons. apply: par2_iso2; auto.
  apply E, mem_head. apply IH=>x Hx. apply E. by apply mem_tail. 
Qed.


Section alt.
 Variables F G: graph2.

 Definition par2_eqv : rel (union F G) :=
   fun x y => (x == y) ||
     if (g_in != g_out :> F) && (g_in != g_out :> G)
     then [set x; y] \in [set [set inl g_in; inr g_in]; [set inl g_out; inr g_out]]
     else [set x; y] \subset [set inl g_in; inl g_out; inr g_in; inr g_out].

 Definition par2_eqv_refl : reflexive par2_eqv.
 Proof. by move=> ?; rewrite /par2_eqv eqxx. Qed.

 Lemma par2_eqv_sym : symmetric par2_eqv.
 Proof. move=> x y. by rewrite /par2_eqv [[set y; x]]setUC [y == x]eq_sym. Qed.

 Definition par2_eqv_trans : transitive par2_eqv.
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
   x != y -> symmetric e -> e a b -> [set x;y] == [set a;b] -> e x y.
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
   inl x = inr y %[mod par2_eqv_equivalence] ->
   x = g_in /\ y = g_in \/ x = g_out /\ y = g_out.
 Proof.
   move/eqquotP. rewrite /=/par2_eqv /eq_op/= -!/eq_op. case: ifP => i_o.
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
   inl x = inl y %[mod par2_eqv_equivalence] ->
   x = y.
 Proof.
   move=> iNo2 /eqquotP/=. rewrite /par2_eqv/= iNo2 andbT sum_eqE.
   case/orP=> [/eqP//|]. case: ifP => [iNo1 | /negbFE/eqP<-].
   - rewrite !inE !eqEsubset ![[set inl x; inl y] \subset _]subUset !sub1set !inE.
     rewrite /eq_op/= !orbF. by case/orP=> /andP[]/andP[/eqP-> /eqP->].
   - by rewrite subUset !sub1set !inE /eq_op/= !orbF !orbb => /andP[/eqP-> /eqP->].
 Qed.
  
 Lemma par2_injR x y : 
   g_in != g_out :> F -> 
   inr x = inr y %[mod par2_eqv_equivalence] ->
   x = y.
 Proof.
   move=> iNo2 /eqquotP/=. rewrite /par2_eqv/= iNo2 /= sum_eqE.
   case/orP=> [/eqP//|]. case: ifP => [iNo1 | /negbFE/eqP<-].
   - rewrite !inE !eqEsubset ![[set inr x; inr y] \subset _]subUset !sub1set !inE.
     rewrite /eq_op/=. by case/orP=> /andP[]/andP[/eqP-> /eqP->].
   - by rewrite subUset !sub1set !inE /eq_op/= !orbb => /andP[/eqP-> /eqP->].
 Qed.
 
 Definition par2' := 
   {| graph_of := merge (union F G) par2_eqv_equivalence ;
      g_in := \pi (inl g_in);
      g_out := \pi (inl g_out) |}.

 Lemma par2_eqE: rel_of_pairs [::(unl g_in,unr g_in);(unl g_out,unr g_out)] =2 par2_eq.
 Proof. 
   move => [x|x] [y|y]; rewrite /rel_of_pairs /par2_eq/= !inE /unl /unr //.
  by rewrite !xpair_eqE.
 Qed.

 Hint Resolve id_bij.

 Lemma par2_eqvE: eqv_clot [::(unl g_in,unr g_in);(unl g_out,unr g_out)] =2 par2_eqv.
 Proof. 
   move => x y. rewrite eqv_clotE par2_equiv_of.
   apply: (lift_equiv (h := id)) => //. exact: par2_eqE.
 Qed.

 Lemma par2_alt: par2 F G ≈ par2'.
 Proof. apply: merge_same=>//. apply par2_eqvE. Qed.

 Definition dot2_eqv : rel (union F G) :=
   fun x y => (x == y) || ([set x; y] == [set inl g_out; inr g_in]).

 Definition dot2_eqv_refl : reflexive dot2_eqv.
 Proof. by move=> ?; rewrite /dot2_eqv eqxx. Qed.

 Lemma dot2_eqv_sym : symmetric dot2_eqv.
 Proof. move=> x y. by rewrite /dot2_eqv [[set y; x]]setUC [y == x]eq_sym. Qed.

 Definition dot2_eqv_trans : transitive dot2_eqv.
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
 Proof. by rewrite /dot2_eqv/= eqxx. Qed.

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
   inl x = inl y %[mod dot2_eqv_equivalence] -> x = y.
 Proof.
   move=> /eqquotP. rewrite /=/dot2_eqv/= sum_eqE. case/orP=> [/eqP//|].
   by rewrite eq_sym eqEcard subUset -andbA andbCA !sub1set !inE.
 Qed.
 
 Lemma dot2_injR (x y : G) :
   inr x = inr y %[mod dot2_eqv_equivalence] -> x = y.
 Proof.
   move=> /eqquotP. rewrite /=/dot2_eqv/= sum_eqE. case/orP=> [/eqP//|].
   by rewrite eq_sym eqEcard subUset !sub1set !inE.
 Qed.

 Transparent union.
 Lemma dot2_LR (x : F) (y : G) :
   inl x = inr y %[mod dot2_eqv_equivalence] -> x = g_out /\ y = g_in.
 Proof.
   move=> /eqquotP. rewrite /=/dot2_eqv/=.
   rewrite eq_sym eqEcard subUset !sub1set !inE orbC /= !sum_eqE.
   by case/andP=> /andP[/eqP<- /eqP<-].
 Qed.
 Opaque union.
 
 Definition dot2' :=
   {| graph_of := merge (union F G) dot2_eqv_equivalence ;
      g_in := \pi (inl g_in);
      g_out := \pi (inr g_out) |}.

 Lemma dot2_eqE: rel_of_pairs [::(unl g_out,unr g_in)] =2 dot2_eq.
 Proof. move => x y. by rewrite /rel_of_pairs /dot2_eq /= inE xpair_eqE. Qed.

 Lemma dot2_eqvE: eqv_clot [::(unl g_out,unr g_in)] =2 dot2_eqv.
 Proof.
   move => x y. rewrite eqv_clotE dot2_equiv_of.
   apply: (lift_equiv (h := id)) => //. exact: dot2_eqE.
 Qed.
 
 Lemma dot2_alt: dot2 F G ≈ dot2'.
 Proof. apply: merge_same=>//. apply dot2_eqvE. Qed.
End alt.
