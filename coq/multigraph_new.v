Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries finite_quotient bij equiv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

(** * Directed Multigraphs *)

(* FIXME: Properly abstract this *)
Lemma _symbols : { sym : eqType & sym }. exists [eqType of nat]; exact: 0. Qed.
Definition sym : eqType := projT1 _symbols.
Definition sym0 : sym := projT2 _symbols.

Structure setoid :=
  Setoid { car:> Type; eqv: car -> car -> Prop; Eqv: Equivalence eqv }.
Infix "≡" := eqv (at level 79).
Existing Instance Eqv.

Class comm_monoid (X: setoid) :=
  Comm_monoid { mon0: X;
                mon2: X -> X -> X;
                mon_eqv:> Proper (@eqv X ==> @eqv X ==> @eqv X) mon2;
                monA: forall x y z, mon2 x (mon2 y z) ≡ mon2 (mon2 x y) z;
                monC: forall x y, mon2 x y ≡ mon2 y x;
                monU: forall x, mon2 x mon0 ≡ x }.

Section s.

Variables (Lv Le: setoid).
Variable Lv_mon: comm_monoid Lv.

Record graph := Graph { vertex :> finType;
                        edge: finType;
                        source : edge -> vertex;
                        target : edge -> vertex;
                        vlabel : vertex -> Lv;
                        elabel : edge -> Le }.

Definition unit_graph a := @Graph [finType of unit] _ vfun vfun (fun _ => a) vfun.
Definition two_graph a b := @Graph [finType of bool] _ vfun vfun (fun v => if v then b else a) vfun.
Definition edge_graph a u b := Graph (fun _ : unit => false) (fun _ => true) (fun v => if v then b else a) (fun _ => u).                           

Definition add_vertex (G: graph) (l: Lv): graph :=
  @Graph [finType of option G] (edge G)
         (fun e => Some (source e))
         (fun e => Some (target e))
         (fun v => match v with Some v => vlabel v | None => l end)
         (@elabel G).

Definition add_edge (G: graph) (x y: G) (l: Le): graph :=
  @Graph (vertex G) [finType of option (edge G)]
         (fun e => match e with Some e => source e | None => x end)
         (fun e => match e with Some e => target e | None => y end)
         (@vlabel G)
         (fun e => match e with Some e => elabel e | None => l end).
Arguments add_edge: clear implicits. 

Definition upd_vlabel (G: graph) (x: G) (l: Lv -> Lv): graph :=
  @Graph (vertex G) (edge G)
         (@source G)
         (@target G)
         (fun v => if v==x then l (vlabel v) else vlabel v)
         (@elabel G).
Arguments upd_vlabel: clear implicits. 



(** *** Edge sets *)

Definition edges (G : graph) (x y : G) :=
  [set e | (source e == x) && (target e == y)].

Definition edge_set (G:graph) (S : {set G}) :=
  [set e | (source e \in S) && (target e \in S)].

Lemma edge_set1 (G : graph) (x : G) : edge_set [set x] = edges x x.
Proof. apply/setP=> e. by rewrite !inE. Qed.

Lemma edge_in_set (G : graph) e (A : {set G}) x y :
  x \in A -> y \in A -> e \in edges x y -> e \in edge_set A.
Proof. move => Hx Hy. rewrite !inE => /andP[/eqP->/eqP->]. by rewrite Hx. Qed.

(** ** Disjoint Union *)

Definition union (G1 G2 : graph) : graph :=
  {| vertex := [finType of G1 + G2];
     edge := [finType of edge G1 + edge G2];
     source := sumf (@source G1) (@source G2);
     target := sumf (@target G1) (@target G2);
     vlabel e := match e with inl e => vlabel e | inr e => vlabel e end;
     elabel e := match e with inl e => elabel e | inr e => elabel e end;
  |}.

Definition unl {G H: graph} (x: G): union G H := inl x.
Definition unr {G H: graph} (x: H): union G H := inr x.

(** ** Homomorphisms *)


Class is_hom (F G: graph) (hv: F -> G) (he: edge F -> edge G): Prop := Hom
  { source_hom: forall e, source (he e) = hv (source e);
    target_hom: forall e, target (he e) = hv (target e);
    vlabel_hom: forall v, vlabel (hv v) ≡ vlabel v;
    elabel_hom: forall e, elabel (he e) ≡ elabel e;
  }.

Lemma hom_id G: @is_hom G G id id.
Proof. by split. Qed.

Lemma hom_comp F G H hv he kv ke:
  @is_hom F G hv he -> @is_hom G H kv ke -> is_hom (kv \o hv) (ke \o he).
Proof.
  intros E E'. split; intro e=>/=.
  by rewrite 2!source_hom. 
  by rewrite 2!target_hom. 
  by rewrite 2!vlabel_hom. 
  by rewrite 2!elabel_hom. 
Qed.

Lemma hom_sym (F G: graph) (hv: bij F G) (he: bij (edge F) (edge G)):
  is_hom hv he -> 
  is_hom hv^-1 he^-1.
Proof.
  intro H. split=>e/=.
  by rewrite -{2}(bijK' he e) source_hom bijK. 
  by rewrite -{2}(bijK' he e) target_hom bijK. 
  by rewrite -{2}(bijK' hv e) vlabel_hom. 
  by rewrite -{2}(bijK' he e) elabel_hom. 
Qed.
  
(** ** Quotient Graphs *)

Definition merge (G : graph) (r : equiv_rel G) :=
  {| vertex := quot r;
     edge := (edge G);
     source e := \pi (source e);
     target e := \pi (target e);
     vlabel c := \big[mon2/mon0]_(w | \pi w == c) vlabel w;
     elabel e := elabel e |}.
Arguments merge: clear implicits.
Notation merge_seq G l := (merge G (eqv_clot l)).


(** ** Subgraphs and Induced Subgraphs *)

Definition subgraph (H G : graph) := 
  exists hv he, @is_hom H G hv he /\ injective hv /\ injective he.

Section Subgraphs.
  Variables (G : graph) (V : {set G}) (E : {set edge G}).
  Definition consistent := forall e, e \in E -> source e \in V /\ target e \in V.
  Hypothesis in_V : consistent.
  
  Definition sub_vertex := sig [eta mem V].
  Definition sub_edge := sig [eta mem E].

  Fact source_proof (e : sub_edge) : source (val e) \in V.
  Proof. by move: (svalP e) => /in_V []. Qed.

  Fact target_proof (e : sub_edge) : target (val e) \in V.
  Proof. by move: (svalP e) => /in_V []. Qed.

  Definition subgraph_for := 
    {| vertex := [finType of sub_vertex];
       edge := [finType of sub_edge];
       source e := Sub (source (val e)) (source_proof e);
       target e := Sub (target (val e)) (target_proof e);
       vlabel v := vlabel (val v);
       elabel e := elabel (val e);
    |}.

  Lemma subgraph_sub : subgraph subgraph_for G.
  Proof. exists val, val. split => //=. split; exact: val_inj. Qed.
End Subgraphs.

Definition induced_proof (G: graph) (S : {set G}) : consistent S (edge_set S).
Proof. move => e. by rewrite inE => /andP. Qed.

Definition induced (G: graph) (S : {set G}) := 
  subgraph_for (@induced_proof G S).

Lemma induced_sub (G: graph) (S : {set G}) : subgraph (induced S) G.
Proof. exact: subgraph_sub. Qed.


(** ** Isomorphim Properties *)

Record iso (F G: graph): Type := Iso
  { iso_v:> bij F G;
    iso_e: bij (edge F) (edge G);
    iso_hom: is_hom iso_v iso_e }.

Notation "h '.e'" := (iso_e h) (at level 2, left associativity). 
Existing Instance iso_hom.

Lemma source_iso F G (h: iso F G) e: source (h.e e) = h (source e).
Proof. apply source_hom. Qed.

Lemma target_iso F G (h: iso F G) e: target (h.e e) = h (target e).
Proof. apply target_hom. Qed.

Lemma vlabel_iso F G (h: iso F G) v: vlabel (h v) ≡ vlabel v.
Proof. apply vlabel_hom. Qed.

Lemma elabel_iso F G (h: iso F G) e: elabel (h.e e) ≡ elabel e.
Proof. apply elabel_hom. Qed.

Definition iso_id {G}: iso G G := @Iso _ _ bij_id bij_id (hom_id G). 

Definition iso_sym F G: iso F G -> iso G F.
Proof.
  move => f. 
  apply Iso with (bij_sym f) (bij_sym (iso_e f)) =>/=.
  apply hom_sym, f. 
Defined.

Definition iso_comp F G H: iso F G -> iso G H -> iso F H.
Proof.
  move => f g. 
  apply Iso with (bij_comp f g) (bij_comp (iso_e f) (iso_e g)) =>/=.
  apply hom_comp. apply f. apply g.
Defined.

Import CMorphisms.

Instance iso_Equivalence: Equivalence iso.
constructor. exact @iso_id. exact @iso_sym. exact @iso_comp. Defined.

Lemma source_iso' F G (h: iso F G) e: source (h.e^-1 e) = h^-1 (source e).
Proof. apply (source_iso (iso_sym h)). Qed.

Lemma target_iso' F G (h: iso F G) e: target (h.e^-1 e) = h^-1 (target e).
Proof. apply (target_iso (iso_sym h)). Qed.

Lemma vlabel_iso' F G (h: iso F G) v: vlabel (h^-1 v) ≡ vlabel v.
Proof. apply (vlabel_iso (iso_sym h)). Qed.

Lemma elabel_iso' F G (h: iso F G) e: elabel (h.e^-1 e) ≡ elabel e.
Proof. apply (elabel_iso (iso_sym h)). Qed.

Definition Iso' (F G: graph)
           (fv: F -> G) (fv': G -> F)
           (fe: edge F -> edge G) (fe': edge G -> edge F):
  cancel fv fv' -> cancel fv' fv ->
  cancel fe fe' -> cancel fe' fe ->
  is_hom fv fe -> iso F G.
Proof. move=> fv1 fv2 fe1 fe2 E. exists (Bij fv1 fv2) (Bij fe1 fe2). apply E. Defined.

Lemma iso_two_graph a b: iso (two_graph a b) (union (unit_graph b) (unit_graph a)).
Proof.
  apply Iso' with
      (fun x: bool => if x then inl tt else inr tt)
      (fun x => match x with inl _ => true | _ => false end)
      (vfun)
      (fun x => match x with inl x | inr x => x end).
  all: repeat first [case|split|reflexivity].
Defined.

Lemma iso_two_swap a: iso (two_graph a a) (two_graph a a).
  apply (@Iso' (two_graph a a) (two_graph a a)
               negb negb 
               (fun e => match e with end) (fun e => match e with end)). 
  all: abstract by (repeat split; case). 
Defined.

(** ** Specific isomorphisms about union and merge *)

Global Instance union_iso: Proper (iso ==> iso ==> iso) union.
Proof.
  intros F F' f G G' g.
  exists (sum_bij f g) (sum_bij f.e g.e).
  abstract by split; case=>e/=; rewrite ?source_iso ?target_iso ?vlabel_iso ?elabel_iso.
Defined.

Lemma union_C G H: iso (union G H) (union H G).
Proof. exists bij_sumC bij_sumC. abstract by split; case. Defined.

Lemma union_A F G H: iso (union F (union G H)) (union (union F G) H).
Proof. exists bij_sumA bij_sumA. abstract by split; case=>[|[|]]. Defined.

Section h_merge_nothing'.
 Variables (F: graph) (r: equiv_rel F).
 Hypothesis H: forall x y: F, r x y -> x=y.
 Lemma merge_nothing': iso (merge F r) F.
 Proof.
   exists (quot_id H: bij (merge F r) F) bij_id.
   split=>e; rewrite /=?quot_idE?H//.
 Admitted.
End h_merge_nothing'.


Section merge_merge.
  Variables (F: graph) (e: equiv_rel F) (e': equiv_rel (merge F e)).
  Lemma hom_merge_merge: is_hom (quot_quot e': merge _ e' -> merge F _) bij_id.
  Proof.
    split=> a//; try by rewrite /=-equiv_comp_pi.
  Admitted.
  Lemma merge_merge: iso (merge (merge F e) e') (merge F (equiv_comp e')).
  Proof. eexists. eapply hom_merge_merge. Defined.
End merge_merge.


Section merge.
  Variables (F G: graph) (h: iso F G) (l: pairs F).
  Definition h_merge: bij (merge_seq F l) (merge_seq G (map_pairs h l)).
    eapply bij_comp. apply (quot_bij h). apply quot_same. apply eqv_clot_iso.
  Defined. 
  Lemma h_mergeE (x: F): h_merge (\pi x) = \pi h x.
  Proof. by rewrite /=quot_bijE quot_sameE. Qed.
  Lemma merge_hom: is_hom h_merge h.e.
  Proof.
    split=>e. 
    - rewrite /= source_iso. symmetry. apply h_mergeE. 
    - rewrite /= target_iso. symmetry. apply h_mergeE.
    - simpl. rewrite quot_sameE. admit. 
    - by rewrite /= elabel_iso.
  Admitted.
  Definition merge_iso: iso (merge_seq F l) (merge_seq G (map_pairs h l)) := Iso merge_hom.
  Lemma merge_isoE (x: F): merge_iso (\pi x) = \pi h x.
  Proof. apply h_mergeE. Qed.
End merge.
Global Opaque h_merge merge_iso.

Section merge_same'.
 Variables (F: graph) (h k: equiv_rel F).
 Hypothesis H: h =2 k. 
 Lemma merge_same'_hom: is_hom (quot_same H: merge _ h -> merge _ k) bij_id.
 Proof.
   split=>e//; try (rewrite /=; apply/eqquotP; rewrite -H; apply: piK').
 Admitted.
 Definition merge_same': iso (merge F h) (merge F k) := Iso merge_same'_hom.
 Lemma merge_same'E (x: F): merge_same' (\pi x) = \pi x.
 Proof. apply quot_sameE. Qed.
End merge_same'.
Global Opaque merge_same'.

Section merge_same.
 Variables (F: graph) (h k: pairs F).
 Hypothesis H: eqv_clot h =2 eqv_clot k.
 Definition merge_same: iso (merge_seq F h) (merge_seq F k) := merge_same' H. 
 Definition merge_sameE (x: F): merge_same (\pi x) = \pi x := merge_same'E H x. 
End merge_same.
Global Opaque merge_same.


Section merge_nothing.
 Variables (F: graph) (h: pairs F).
 Hypothesis H: List.Forall (fun p => p.1 = p.2) h.
 Definition merge_nothing: iso (merge_seq F h) F.
 Proof. apply merge_nothing', eqv_clot_nothing', H. Defined.
 Lemma merge_nothingE (x: F): merge_nothing (\pi x) = x.
 Admitted.                      (* need Transparent merge_nothing *)
 (* Proof. apply quot_idE. Qed. *)
End merge_nothing.
Global Opaque merge_nothing.

Section merge_merge_seq.
  Variables (F: graph) (h k: pairs F) (k': pairs (merge_seq F h)).
  Hypothesis kk': k' = map_pairs (pi (eqv_clot h)) k.
  Definition h_merge_merge_seq: bij (merge_seq (merge_seq F h) k') (merge_seq F (h++k)).
  Proof.
    eapply bij_comp. apply quot_quot. apply quot_same.
    rewrite kk'. apply eqv_clot_cat.
  Defined.
  Lemma hom_merge_merge_seq: is_hom h_merge_merge_seq bij_id.
  Proof.
    split=>e//; try by rewrite /=quot_quotE quot_sameE.
  Admitted.
  Definition merge_merge_seq: iso (merge_seq (merge_seq F h) k') (merge_seq F (h++k)) :=
    Iso hom_merge_merge_seq.
  Lemma merge_merge_seqE (x: F): merge_merge_seq (\pi (\pi x)) = \pi x.
  Proof. by rewrite /=quot_quotE quot_sameE. Qed.
End merge_merge_seq.
Global Opaque merge_merge_seq.

Lemma eqv_clot_map_lr (F G : finType) (l : pairs F) x y : 
  eqv_clot (map_pairs inl l) (@inl F G x) (@inr F G y) = false.
Proof. rewrite (@eqv_clot_mapF _) ?inr_codom_inl //. exact: inl_inj. Qed.

Lemma union_equiv_l_eqv_clot (A B: finType) (l: pairs A):
  union_equiv_l B (eqv_clot l) =2 eqv_clot (map_pairs inl l).
Proof.
  rewrite /union_equiv_l/=/union_equiv_l_rel. move => [x|x] [y|y].
  + rewrite (@eqv_clot_map _ _  _ _ _ (@inl A B)) //. exact: inl_inj.
  + by rewrite eqv_clot_map_lr.
  + by rewrite equiv_sym eqv_clot_map_lr. 
  + by rewrite eqv_clot_map_eq ?sum_eqE // inr_codom_inl.
Qed.

Section union_merge_l.
  Variables (F G: graph) (l: pairs F).
  Definition h_union_merge_l: bij (union (merge_seq F l) G) (merge_seq (union F G) (map_pairs unl l)).
  Proof. eapply bij_comp. apply union_quot_l. apply quot_same. apply union_equiv_l_eqv_clot. Defined.
  Lemma hom_union_merge_l: is_hom h_union_merge_l bij_id.
  Proof.
    try (split; move=>[e|e]//=; rewrite ?union_quot_lEl ?union_quot_lEr quot_sameE //).
  Admitted.
  Definition union_merge_l: iso (union (merge_seq F l) G) (merge_seq (union F G) (map_pairs unl l)) :=
    Iso hom_union_merge_l.
  Lemma union_merge_lEl (x: F): union_merge_l (inl (\pi x)) = \pi unl x.
  Proof. by rewrite /=union_quot_lEl quot_sameE. Qed.
  Lemma union_merge_lEr (x: G): union_merge_l (unr x) = \pi unr x.
  Proof. by rewrite /=union_quot_lEr quot_sameE. Qed.
End union_merge_l.  
Global Opaque union_merge_l.

Lemma map_map_pairs {A B C} (f: A -> B) (g: B -> C) l: map_pairs g (map_pairs f l) = map_pairs (g \o f) l.
Proof. by rewrite /map_pairs -map_comp. Qed.

Section union_merge_r.
  Variables (F G: graph) (l: pairs G).
  Lemma union_merge_r: iso (union F (merge_seq G l)) (merge_seq (union F G) (map_pairs unr l)).
  Proof.
    eapply iso_comp. apply union_C.
    eapply iso_comp. apply union_merge_l.
    eapply iso_comp. apply (merge_iso (union_C _ _)).
    apply merge_same. abstract by rewrite map_map_pairs. 
  Defined.
  Lemma union_merge_rEr (x: G): union_merge_r (inr (\pi x)) = \pi (unr x).
  Proof.
    (* BUG: the second rewrite hangs if F and x are not given *)
    rewrite /=. rewrite (union_merge_lEl F _ x).
    rewrite (merge_isoE (union_C G F) _ (unl x)).
    by rewrite merge_sameE. 
  Qed.
  Lemma union_merge_rEl (x: F): union_merge_r (unl x) = \pi (unl x).
  Proof.
    rewrite /=. rewrite (union_merge_lEr _ x) .
    rewrite (merge_isoE (union_C G F) _ (unr x)).
    by rewrite merge_sameE. 
  Qed.
End union_merge_r.  
Global Opaque union_merge_r.

Section merge_union_K.
  Variables (F K: graph) (h: pairs (F+K)) (k: K -> F).
  Definition union_K_pairs := map_pairs (fun x => match x with inl x => x | inr x => k x end) h.

  Hypothesis kv: forall x: K, vlabel x = mon0.
  Hypothesis kh: forall x: K, unr x = unl (k x) %[mod (eqv_clot h)].

  Lemma equiv_clot_Kl: union_K_equiv (eqv_clot h) =2 eqv_clot union_K_pairs.
  Proof.
    move=> x y. rewrite /union_K_equiv map_equivE. 
    rewrite !eqv_clotE. set e1 := rel_of_pairs _. set e2 := rel_of_pairs _. 
    pose j := (fun x => match x with inl x => x | inr x => k x end).
    apply/idP/idP. 
    - suff S u v : equiv_of e1 u v -> equiv_of e2 (j u) (j v) by apply: S. 
      apply: equiv_ofE => {u v} [[u|u] [u'|u']] /= H. 
      all: rewrite /e2 /j; apply: sub_equiv_of; apply/mapP. 
      + by exists (unl u,unl u').
      + by exists (unl u,unr u').
      + by exists (unr u,unl u').
      + by exists (unr u,unr u').
    - apply: equiv_ofE => {x y} x x' xx'. 
      have kh' z : equiv_of e1 (unr z) (unl (k z)).
      { rewrite -eqv_clotE. apply/eqquotP. exact: kh. }
      case/mapP : xx' => [[[u|u] [v|v]] H] /= [-> ->] {x x'}.
      + exact: sub_equiv_of.
      + apply: equiv_trans => /=. 2: exact: (kh' v). exact: sub_equiv_of.
      + apply: equiv_trans => /=. rewrite equiv_sym /=. exact: kh'. exact: sub_equiv_of.
      + apply: equiv_trans. 2: exact: kh'. apply: equiv_trans. 
        rewrite equiv_sym. exact: kh'. exact: sub_equiv_of.
  Qed.
  
  Definition h_merge_union_K: bij (merge_seq (union F K) h) (merge_seq F union_K_pairs).
    eapply bij_comp. apply quot_union_K with k. apply kh.
    apply quot_same. apply equiv_clot_Kl. 
  Defined.

  Hypothesis ke: edge K -> False.

  Definition h_merge_union_Ke1 (e: edge (merge_seq (union F K) h)): edge (merge_seq F union_K_pairs) :=
    match e with inl e => e | inr e => match ke e with end end.

  Definition h_merge_union_Ke: bij (edge (merge_seq (union F K) h)) (edge (merge_seq F union_K_pairs)).
    exists h_merge_union_Ke1 inl=>x//. by case x.
  Defined.

  Lemma hom_merge_union_K: is_hom h_merge_union_K h_merge_union_Ke.
  Proof.
    split; try (move => [e//=|//]; by rewrite ?quot_union_KEl ?quot_union_KEr quot_sameE).
  Admitted.

  Definition merge_union_K: iso (merge_seq (union F K) h) (merge_seq F union_K_pairs) :=
    Iso hom_merge_union_K.
  Lemma merge_union_KEl (x: F): merge_union_K (\pi (unl x)) = \pi x.
  Proof. by rewrite /=quot_union_KEl quot_sameE. Qed.
  Lemma merge_union_KEr (x: K): merge_union_K (\pi (unr x)) = \pi k x.
  Proof. by rewrite /=quot_union_KEr quot_sameE. Qed.
End merge_union_K.
Global Opaque merge_union_K.

Lemma valK' (T : eqType) (P : pred T) (u : sig_subType P) (Px : val u \in P) : 
  Sub (val u) Px = u.
Proof. exact: val_inj. Qed.


Section QuotFun.
Variables (T1 T2 : finType) (e1 : equiv_rel T1) (e2 : equiv_rel T2) (h1 : T1 -> T2).
Definition quot_fun (x : quot e1) : quot e2 := \pi (h1 (repr x)).
End QuotFun.
Arguments quot_fun [T1 T2 e1 e2].

Lemma quot_fun_can (T1 T2 : finType) (e1 : equiv_rel T1) (e2 : equiv_rel T2) (h1 : T1 -> T2) (h2 : T2 -> T1) :
  {homo h2 : x y / x = y %[mod e2] >-> x = y %[mod e1]} ->
  (forall x, h2 (h1 x) = x %[mod e1]) ->
  @cancel (quot e2) (quot e1) (quot_fun h1) (quot_fun h2).
Proof.
  move => h2_hom h1_can x.
  rewrite /quot_fun -{2}[x]reprK -[\pi (repr x)]h1_can.
  apply: h2_hom. by rewrite reprK.
Qed.

Section BijT.
Variables (T : finType) (P : pred T).
Hypothesis inP : forall x, P x.
Definition subT_bij : bij {x : T | P x} T.
Proof. exists val (fun x => Sub x (inP x)). 
       abstract (case => x Px; exact: val_inj).
       abstract done.
Defined.
End BijT.

Definition setT_bij (T : finType) : bij {x : T | x \in setT} T := 
  Eval hnf in subT_bij (@in_setT T).
Arguments setT_bij [T].

Lemma consistentT (G : graph) (E : {set edge G}) : consistent [set: G] E. by []. Qed.

Lemma consistentTT (G : graph) : consistent [set: G] [set: edge G]. by []. Qed.
Arguments consistentTT : clear implicits.

Lemma setT_bij_hom (G : graph) : @is_hom (subgraph_for (@consistentTT G)) G setT_bij setT_bij. 
Proof. by []. Qed.

Definition iso_subgraph_forT (G : graph) : iso (subgraph_for (consistentTT G)) G := 
  Eval hnf in Iso (setT_bij_hom G).

Section QuotBij.
  Variables (T1 T2 : finType) (e1 : equiv_rel T1) (e2 : equiv_rel T2).
  Variables (h : T1 -> T2) (h_inv : T2 -> T1).

  (** All 4 assumptions are necessary *)
  Hypothesis h_homo : {homo h : x y / x = y %[mod e1] >-> x = y %[mod e2]}.
  Hypothesis h_inv_homo : {homo h_inv : x y / x = y %[mod e2] >-> x = y %[mod e1]}. 

  Hypothesis h_can : forall x, h_inv (h x) = x %[mod e1].
  Hypothesis h_inv_can : forall x, h (h_inv x) = x %[mod e2].

  Definition quot_bij : bij (quot e1) (quot e2).
  Proof. exists (quot_fun h) (quot_fun h_inv); abstract exact: quot_fun_can. Defined.

  Lemma quot_bijE (x: T1): quot_bij (\pi x) = \pi h x.
  Proof. simpl. apply: h_homo. by rewrite reprK. Qed.
  
  Lemma quot_bijE' (x: T2): quot_bij^-1 (\pi x) = \pi h_inv x.
  Proof. simpl. apply: h_inv_homo. by rewrite reprK. Qed.
End QuotBij.
Global Opaque quot_bij.

Arguments Sub : simpl never.

Section union_bij.
Variables (T : finType) (U V : {set T}).
Notation sig S := ({ x : T | x \in S}) (only parsing).

Lemma union_bij_proofL x : x \in U -> x \in U :|: V.
Proof. apply/subsetP. exact: subsetUl. Qed.

Lemma union_bij_proofR x : x \in V -> x \in U :|: V.
Proof. apply/subsetP. exact: subsetUr. Qed.

Definition union_bij_fwd (x : sig U + sig V) : sig (U :|: V) :=
  match x with 
  | inl x => Sub (val x) (union_bij_proofL (valP x))
  | inr x => Sub (val x) (union_bij_proofR (valP x))
  end.

Lemma setU_dec x : x \in U :|: V -> ((x \in U) + (x \notin U)*(x \in V))%type.
Proof. case E : (x \in U); last rewrite !inE E; by [left|right]. Qed.

Definition union_bij_bwd (x : sig (U :|: V)) : sig U + sig V :=
  match setU_dec (valP x) with 
  | inl p => inl (Sub (val x) p) 
  | inr p => inr (Sub (val x) p.2) 
  end.

Inductive union_bij_bwd_spec : sig (U :|: V) -> sig U + sig V ->  Type :=
| union_bij_bwdL x (inU : x \in U) (inUV : x \in U :|: V) : 
    union_bij_bwd_spec (Sub x inUV) (inl (Sub x inU))
| union_bij_bwdR x (inV : x \in V) (inUV : x \in U :|: V) : 
    x \notin U -> union_bij_bwd_spec (Sub x inUV) (inr (Sub x inV)).

Lemma union_bij_bwdP x : union_bij_bwd_spec x (union_bij_bwd x).
Proof.
  rewrite /union_bij_bwd. 
  case: (setU_dec _) => p.
  - rewrite {1}[x](_ : x = Sub (val x) (valP x)). exact: union_bij_bwdL. 
    by rewrite valK'.
  - rewrite {1}[x](_ : x = Sub (val x) (valP x)). apply: union_bij_bwdR. 
    by rewrite p.  by rewrite valK'.
Qed.

Definition union_bij_bwdEl x (p : x \in U :|: V) (inU : x \in U) : 
  union_bij_bwd (Sub x p) = inl (Sub x inU).
Proof.
  rewrite /union_bij_bwd. case: (setU_dec _) => p'. 
  - rewrite /=. congr inl. exact: val_inj.
  - exfalso. move: p'. rewrite /= inU. by case.
Qed.
Arguments union_bij_bwdEl [x p].

Definition union_bij_bwdEr x (p : x \in U :|: V) (inV : x \in V) : 
  x \notin U -> 
  union_bij_bwd (Sub x p) = inr (Sub x inV).
Proof.
  move => xNU. rewrite /union_bij_bwd. case: (setU_dec _) => p'. 
  - exfalso. move: p'. by rewrite /= (negbTE xNU). 
  - rewrite /=. congr inr. exact: val_inj.
Qed.
Arguments union_bij_bwdEr [x p].

Hint Extern 0 (is_true (sval _ \in _)) => exact: valP.
Hint Extern 0 (is_true (val _ \in _)) => exact: valP.

Section Dis.
  Hypothesis disUV : [disjoint U & V].

  Lemma union_bij_fwd_can : cancel union_bij_fwd union_bij_bwd.
  Proof. 
    move => [x|x] /=. 
    - by rewrite union_bij_bwdEl // valK'.
    - by rewrite union_bij_bwdEr ?valK' // (disjointFl disUV).
  Qed.
  
  Lemma union_bij_bwd_can : cancel union_bij_bwd union_bij_fwd.
  Proof. move => x. case: union_bij_bwdP => //= {x} x *; exact: val_inj. Qed.

  Definition union_bij := Bij union_bij_fwd_can union_bij_bwd_can.

  Lemma union_bijE :
    (forall x, union_bij (inl x) = Sub (val x) (union_bij_proofL (valP x)))*
    (forall x, union_bij (inr x) = Sub (val x) (union_bij_proofR (valP x))).
  Proof. done. Qed.

End Dis.

Section Quot.
  Variables (e : equiv_rel (sig U + sig V)).
  Definition merge_union_rel := map_equiv union_bij_bwd e.

  Hypothesis eqvI : forall x (inU : x \in U) (inV : x \in V), 
      inl (Sub x inU) = inr (Sub x inV) %[mod e].

  Lemma union_bij_fwd_can' x : union_bij_bwd (union_bij_fwd x) = x %[mod e].
  Proof.
    case: x => /= => x. 
    - by rewrite union_bij_bwdEl valK'.
    - case: (boolP (val x \in U)) => H. rewrite (union_bij_bwdEl H). 
      + case: x H => x p H. exact: eqvI.
      + by rewrite (union_bij_bwdEr _ H) // valK'.
  Qed.

  Lemma union_bij_bwd_can' x : union_bij_fwd (union_bij_bwd x) = x %[mod merge_union_rel].
  Proof. case: union_bij_bwdP => {x} *; congr pi; exact: val_inj. Qed.

  Lemma union_bij_fwd_hom : 
    {homo union_bij_fwd : x y / x = y %[mod e] >-> x = y %[mod merge_union_rel]}.
  Proof.
    move => x y H. apply/eqquotP. rewrite map_equivE. apply/eqquotP. 
    by rewrite !union_bij_fwd_can'.
  Qed.

  Lemma union_bij_bwd_hom : 
    {homo union_bij_bwd : x y / x = y %[mod merge_union_rel] >-> x = y %[mod e]}.
  Proof. move => x y /eqquotP. rewrite map_equivE. by move/eqquotP. Qed.

  Definition merge_union_bij : bij (quot e) (quot merge_union_rel) := 
    Eval hnf in quot_bij union_bij_fwd_hom union_bij_bwd_hom
                             union_bij_fwd_can' union_bij_bwd_can'.

  Lemma merge_unionEl x : 
    merge_union_bij (\pi (inl x)) = \pi (Sub (val x) (union_bij_proofL (valP x))).
  Proof. exact: quot_bijE. Qed.
  Lemma merge_unionEr x : 
    merge_union_bij (\pi (inr x)) = \pi (Sub (val x) (union_bij_proofR (valP x))).
  Proof. exact: quot_bijE. Qed.
  Definition merge_unionE := (merge_unionEl,merge_unionEr).
End Quot.

End union_bij.

Lemma bij_same A B (f : A -> B) (f_inv : B -> A) (i : bij A B) :
  f =1 i -> f_inv =1 i^-1 -> bij A B.
Proof.
  move => Hf Hf'.
  exists f f_inv; abstract (move => x; by rewrite Hf Hf' ?bijK ?bijK').
Defined.
Arguments bij_same [A B] f f_inv i _ _.

(** ** Merging Subgraphs *)

(** This construction allows transforming a quotient on [G[V1,E1] + G[V2,E2]] 
    into a quotient on [G[V1 :|: V2, E1 :|: E2]], provided the edge sets are
    disjoint and the quotient merges all duplicated verices (i.e., those
    occurring both in [V1] and in [V2]. Note that the underlying pair of 
    functions only becomes a bijection after quotienting. *)

Section MergeSubgraph.
  Variables (G : graph) (V1 V2 : {set G}) (E1 E2 : {set edge G}) 
            (con1 : consistent V1 E1) (con2 : consistent V2 E2)
            (h : pairs (union (subgraph_for con1) (subgraph_for con2))).

  Lemma consistentU : consistent (V1 :|: V2) (E1 :|: E2).
  Proof using con1 con2. 
    move => e. case/setUP => E. 
    - case: (con1 E) => H1 H2. by rewrite !inE H1 H2.
    - case: (con2 E) => H1 H2. by rewrite !inE H1 H2. 
  Qed.    

  Hypothesis eqvI : forall x (inU : x \in V1) (inV : x \in V2), 
      inl (Sub x inU) = inr (Sub x inV) %[mod eqv_clot h].

  Hypothesis disE : [disjoint E1 & E2].

  Local Notation G1 := (subgraph_for con1).
  Local Notation G2 := (subgraph_for con2).
  Local Notation G12 := (subgraph_for consistentU).

  Definition h' := map_pairs (@union_bij_fwd _ _ _) h.
  Lemma eqv_clot_union_rel : merge_union_rel (eqv_clot h) =2 eqv_clot h'.
  Proof.
    move => x y. rewrite /merge_union_rel /h' map_equivE. apply/idP/idP.
    - have aux z : union_bij_fwd (union_bij_bwd z) = z %[mod eqv_clot (map_pairs (@union_bij_fwd _ _ _) h)].
      { apply/eqquotP. case: union_bij_bwdP => *; apply: eq_equiv; by apply: val_inj. }
      move => H. apply/eqquotP. rewrite -[_ x]aux -[_ y]aux. apply/eqquotP.
      move: H. apply: eqv_clot_map'.
    - rewrite eqv_clotE. apply: equiv_ofE => /= {x y} x y. 
      rewrite /rel_of_pairs/=. case/mapP => /= [[u v]] in_h [-> ->].
      apply/eqquotP. rewrite 2!(union_bij_fwd_can' eqvI). apply/eqquotP.
      exact: eqv_clot_pair.
  Qed.

  Definition merge_subgraph_v : bij (merge_seq (union G1 G2) h) (merge_seq G12 h') :=
    Eval hnf in (bij_comp (merge_union_bij eqvI) (quot_same eqv_clot_union_rel)).

  Definition merge_subgraph_e : bij (edge G1 + edge G2) (edge G12) := 
    union_bij disE.

  Lemma merge_subgraph_hom : is_hom merge_subgraph_v merge_subgraph_e.
  Proof.
    rewrite /merge_subgraph_e /merge_subgraph_v. 
    split;[ | | admit| ]; case => x //=.
    all: rewrite merge_unionE quot_sameE. 
    all: congr pi; try exact: val_inj.
  Admitted.

  Definition merge_subgraph_iso : iso (merge_seq (union G1 G2) h) (merge_seq G12 h') := 
    Iso merge_subgraph_hom.

End MergeSubgraph.

End s.
Arguments merge [_ _] _ _ _.
Notation merge_seq M G l := (merge M G (eqv_clot l)).
Arguments unit_graph [_ _] _. 
Arguments two_graph [_ _] _ _. 
Arguments edge_graph [_ _] _ _ _. 
Arguments add_edge [_ _] _ _ _. 
Arguments upd_vlabel [_ _] _ _ _.

