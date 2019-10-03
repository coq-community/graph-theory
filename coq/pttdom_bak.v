Require Import Setoid CMorphisms.
From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries bij equiv multigraph_new liso.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

(* 
   strategies:

   A
    1. 2pdom + TaT=T    (with rule G+· --> G)
    2. 2pdom by conservativity
    3. 2p by normalisation and reduction to 2pdom (for nfs u v, G(u)≃G(v) -> G(u[t/T])≃G(v[t/T]))

    + reasonable syntactic normalisation
    + nice rewriting system
    + confluence without having to deal with connectedness
    -- reduction for 2p should remain complicated (zig-zags)


   B
    1. 2pdom (for CPP) then 2p
    2. 2pdom by conservativity
    3. 2pdom + TaT by simple analysis
    
    + target for CPP
    + 2pdom + TaT not necessary
    + confluence without having to deal with connectedness (even in the intermediate case with the kill rule)
    - need 'graphs with a term' for the rewriting system
    - syntactic normalisation is rather heavy

   C
    1. 2pdom
    2. 2p by global analysis
    3. 2pdom + TaT by simple analysis
    + simple syntactic normalisation
    + smaller rewriting system
    + 2pdom + TaT not necessary
    - analysis for 2p should be complicated (zig-zags)

   B seems the most reasonable option in the long term ; so for now we focus on B1 for 2pdom

  
   TOTHINK: algebra of lgraphs v.s. algebra of graphs ???
   . would be convenient to have some of the laws on lgraphs
   . current [completeness] theorem, at the end of the file, stated in terms of lgraphs
     -> need to get 
     iso (graph_of_term u) (graph_of_term v)  -> liso (lgraph_of_term u) (lgraph_of_term v)
     (certainly through homomorphism lgraph_of_graph)
 *)


(** TOMOVE  *)

Notation "'Σ' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p%type)) ..))
  (at level 200, x binder, y binder, right associativity).

Notation IO := [set input; output].


Definition S_option A: bij (unit+A) (option A).
Proof.
  exists (fun x => match x with inr a => Some a | inl _ => None end)
         (fun x => match x with Some a => inr a | None => inl tt end);
    case=>//; case=>//.
Defined.

Definition two_bool: bij (unit+unit) bool.
Proof. etransitivity. apply S_option. symmetry. apply bool_option_unit. Defined.

Definition two_option_option_void: bij (unit+unit) (option (option void)).
Proof.
  etransitivity. apply bij_sumC.
  etransitivity. apply S_option.
  apply option_bij. apply unit_option_void.
Defined.

Definition merge43: bij (quot (eqv_clot [::(inl true,inr false)])) (option bool).
Admitted.
Lemma merge43E:
  ((merge43 (\pi inl false) = Some false) *
   (merge43 (\pi inl true) = None) *
   (merge43 (\pi inr false) = None) *
   (merge43 (\pi inr true) = Some true))%type.
Admitted.
Lemma merge43E':
  ((merge43^-1 (Some false) = \pi inl false) *
   (merge43^-1 None = \pi inl true) *
   (merge43^-1 (Some true) = \pi inr true))%type.
Admitted.


(* TOMOVE *)
Lemma iso_vbij Lv Le (G: graph Lv Le) (V: finType) (h: bij (vertex G) V):
  iso G (@Graph _ _ V (edge G)
                (h \o (@source _ _ G))
                (h \o (@target _ _ G))
                ((@vlabel _ _ G) \o h^-1)
                (@elabel _ _ G)).
Proof. iso h bij_id. by split=>//= v; rewrite bijK. Defined.

Lemma iso_ebij Lv Le (G: graph Lv Le) (E: finType) (h: bij (edge G) E):
  iso G (@Graph _ _ (vertex G) E
                ((@source _ _ G) \o h^-1)
                ((@target _ _ G) \o h^-1)
                (@vlabel _ _ G)
                ((@elabel _ _ G) \o h^-1)).
Proof. iso bij_id h. by split=>//= v; rewrite bijK. Defined.

Lemma liso_vbij (G: lgraph) (V: finType) (h: bij (vertex G) V):
  liso G
       (point (@Graph _ _ V (edge G)
                      (h \o (@source _ _ G))
                      (h \o (@target _ _ G))
                      ((@vlabel _ _ G) \o h^-1)
                      (@elabel _ _ G))
              (h input) (h output)).
Proof. apply (iso_liso (iso_vbij h)). Qed.

Lemma liso_ebij (G: lgraph) (E: finType) (h: bij (edge G) E):
  liso G
       (point (@Graph _ _ (vertex G) E
                ((@source _ _ G) \o h^-1)
                ((@target _ _ G) \o h^-1)
                (@vlabel _ _ G)
                ((@elabel _ _ G) \o h^-1))
              input output).
Proof. apply (iso_liso (iso_ebij h)). Qed.

Universe S.
Inductive step: lgraph -> lgraph -> Type@{S} :=
  | step_v0: forall G alpha,
      step
        (add_vertex G alpha)
        G
  | step_v1: forall G x u alpha,
      step
        (add_edge (add_vertex G alpha) (Some x) None u)
        (add_test G x (tst_dom (u·alpha)))
  | step_v2: forall G x y u alpha v,
      step
        (add_edge (add_edge (add_vertex G alpha) (Some x) None u) None (Some y) v)
        (add_edge G x y (u·alpha·v))
  | step_e0: forall G x u,
      step
        (add_edge G x x u)
        (add_test G x [1∥u])
  | step_e2: forall G x y u v,
      step
        (add_edge (add_edge G x y u) x y v)
        (add_edge G x y (u∥v)).

(** It is crucial that we name the universe steps resides in. Without
the explicit name, the inferred universe is a max-universe, causing
setoid rewite underneath of steps to fail with the anomaly: "Unable to
handle arbitrary u+k <= v constraints." *)
Inductive steps: lgraph -> lgraph -> Type@{S} :=
  | liso_step: CRelationClasses.subrelation liso steps
  | cons_step: forall F G H H', liso F G -> step G H -> steps H H' -> steps F H'.
Existing Instance liso_step.

Instance PreOrder_steps: CRelationClasses.PreOrder steps.
Proof.
  split. intro. apply liso_step, liso_id.
  intros F G H S S'. induction S as [F G I|F G G' G'' I S _ IH].
  - destruct S' as [F' G' I'|F' G' G'' G''' I' S'].
    apply liso_step. etransitivity; eassumption.
    apply cons_step with G' G''=>//. etransitivity; eassumption.
  - apply cons_step with G G'=>//. by apply IH. 
Qed.

Instance one_step: CRelationClasses.subrelation step steps.
Proof. intros F G S. by apply cons_step with F G. Qed.

Definition step_order G H (s: step G H): nat :=
  match s with
  | step_v0 _ _ => 0
  | step_v1 _ _ _ _ => 1
  | step_v2 _ _ _ _ _ _ => 2
  | step_e0 _ _ _ => 3
  | step_e2 _ _ _ _ _ => 4
  end.

(* Lemmas for manual chaining *)
Lemma steps_lisoL G G' H : steps G' H -> liso G G' -> steps G H.
Proof. intros. etransitivity; eauto using liso_step. Qed.

Lemma steps_stepL G G' H : steps G' H -> step G G' -> steps G H.
Proof. intros. eapply cons_step. reflexivity. eassumption. assumption. Qed.

Lemma steps_comp F G H : steps F G -> steps G H -> steps F H.
Proof. etransitivity; eassumption. Qed.


Instance steps_proper : Proper (liso ==> liso ==> iffT) steps.
Proof.
  move => G G' g H H' h. split => S. 
  - apply: steps_lisoL (liso_sym g). apply: steps_comp S _. exact: liso_step.
  - apply: steps_lisoL g. apply: steps_comp S _. apply: liso_step. exact: liso_sym.
Qed. 

Tactic Notation "liso_step" uconstr(h) :=
  match goal with
  | |- steps ?G _ => etransitivity;
                     [apply liso_step;
                      first [apply h|apply (@liso_vbij G _ h)|apply (@liso_ebij G _ h)]|]
  | |- liso ?G _ => etransitivity;
                    [first [apply h|apply (@liso_vbij G _ h)|apply (@liso_ebij G _ h)]|]
  end.

Proposition local_confluence G G' H H':
    step G G' -> step H H' -> liso G H -> 
    {F & steps G' F * steps H' F}%type.
Admitted.                       (* through open confluence *)

Definition measure (G: lgraph) := #|vertex G| + #|edge G|.

Lemma step_decreases G H: step G H -> measure H < measure G.
Proof.
  rewrite /measure.
  case; intros=>/=; by rewrite !card_option ?addSnnS ?addnS.
Qed.

Lemma liso_stagnates G H: liso G H -> measure H = measure G.
Proof. move=>l. by rewrite /measure (card_bij (liso_v l)) (card_bij (liso_e l)). Qed.

Proposition confluence F: forall G H, steps F G -> steps F H -> {F' & steps G F' * steps H F'}%type.
Proof.
  induction F as [F_ IH] using (well_founded_induction_type (Wf_nat.well_founded_ltof _ measure)).
  move=> G H S.
  move: G H S IH => _ H [F G FG|F__ F0 G' G FF0 FG GG] IH FH.
  - exists H; split=>//. transitivity F=>//. by apply liso_step, liso_sym.
  - move: H FH IH FF0=> _ [F H FH|F F1 H' H FF1 FH HH] IH FF0. 
      exists G; split=>//. transitivity F. by apply liso_step, liso_sym. eauto using cons_step.
    destruct (local_confluence FG FH) as [M[GM HM]]. transitivity F=>//. by symmetry.
    destruct (fun D => IH G' D _ _ GG GM) as [L[GL ML]].
     rewrite /Wf_nat.ltof -(liso_stagnates FF0). apply /ltP. by apply step_decreases.
    have HL: steps H' L by transitivity M. 
    destruct (fun D => IH H' D _ _ HL HH) as [R[LR HR]].
     rewrite /Wf_nat.ltof -(liso_stagnates FF1). apply /ltP. by apply step_decreases.
     exists R. split=>//. by transitivity L.
Qed.


(** ** 2pdom-operations on graphs *)

Notation merge_seq G l := (@merge _ _ test_monoid G (eqv_clot l)).

(** Note: We choose [unl input] as input and [unr output] as output
for both binary operations. This allows us to state lemmas for both
without generalizing only over the sequence *)

Definition lpar (F G: lgraph) :=
  point (merge_seq (union F G) [::(unl input,unr input); (unl output,unr output)])
        (\pi (unl input)) (\pi (unr output)).

Definition ldot (F G: lgraph) :=
  point (merge_seq (union F G) [::(unl output,unr input)])
        (\pi (unl input)) (\pi (unr output)).

Definition lcnv (F: lgraph) :=
  point F output input.

Definition ldom (F: lgraph) :=
  point F input input.

Definition lone :=
  point (unit_graph [1]) tt tt.

Definition ltop :=
  point (two_graph [1] [1]) false true.

Definition lvar a :=
  point (edge_graph [1] (var a) [1]) false true.

Fixpoint lgraph_of_term (u: term): lgraph :=
  match u with
  | dot u v => ldot (lgraph_of_term u) (lgraph_of_term v)
  | par u v => lpar (lgraph_of_term u) (lgraph_of_term v)
  | cnv u => lcnv (lgraph_of_term u)
  | dom u => ldom (lgraph_of_term u)
  | one => lone
  | var a => lvar a
  end.

Definition lgraph_of_nf_term (t: nf_term): lgraph :=
  match t with
  | nf_test a => point (unit_graph a) tt tt
  | nf_conn a u b => point (edge_graph a u b) false true
  end.

(*
Definition lgraph_of_graph2 (G: graph2): lgraph :=
  LGraph (@multigraph.source G)
         (@multigraph.target G)
         (fun _ => [1])
         (fun e => var (multigraph.label e))
         input
         output.

Lemma lgraph_of_graph2_of_term (u: term): liso (lgraph_of_term u) (lgraph_of_graph2 (graph2_of_term u)).
Admitted. 

Lemma lgraph_of_graph2_iso (G H: graph2):
  G ≈ H -> liso (lgraph_of_graph2 G) (lgraph_of_graph2 H).
Proof.
  move=>h. exists (iso2_v h) h.e (fun _ => false)=>//; try intro; try apply h.
    by rewrite /=(label_iso h).
Qed.
*)

Lemma dot_liso: Proper (liso ==> liso ==> liso) ldot.
Proof.
  move => F F' FF G G' GG. rewrite /ldot.
  (* setoid_rewrite (iso_liso (merge_iso (union_iso FF GG))). *)
  (* cannot work: we would need a coercion from liso to iso, which is not true *)
Admitted.

Lemma par_liso: Proper (liso ==> liso ==> liso) lpar.
Admitted.

Lemma cnv_liso: Proper (liso ==> liso) lcnv.
Proof. intros F G l. liso (liso_v l) (liso_e l) (liso_dir l) ; apply l. Qed.

Lemma lcnvC G : liso (lcnv (lcnv G)) G.
Proof. case: G => G i o. rewrite /lcnv/=. apply: liso_id. Defined.

Lemma dom_liso: Proper (liso ==> liso) ldom.
Proof. intros F G l. liso (liso_v l) (liso_e l) (liso_dir l); apply l. Qed.

Lemma step_to_steps f:
  Proper (liso ==> liso) f -> Proper (step ==> steps) f -> Proper (steps ==> steps) f.
Proof.
  intros If Sf G G' S.
  induction S as [G G' I|G G' F H' I S Ss IH].
  - by apply liso_step, If.
  - etransitivity. apply liso_step, If, I.
    etransitivity. apply Sf, S. apply IH. 
Qed.

Instance cnv_steps: Proper (steps ==> steps) lcnv.
Proof.
  apply step_to_steps. by apply cnv_liso.
  move=>F G S. eapply one_step. destruct S.
  * apply (@step_v0 (point G output input) alpha).
  * apply (@step_v1 (point G output input) x u alpha).
  * apply (@step_v2 (point G output input) x y u alpha v).
  * apply (@step_e0 (point G output input) x u).
  * apply (@step_e2 (point G output input) x y u v).
Qed.

Instance dom_steps: Proper (steps ==> steps) ldom.
Proof.
  apply step_to_steps. by apply dom_liso.
  move=>F G S. eapply one_step. destruct S.
  * apply (@step_v0 (point G input input) alpha).
  * apply (@step_v1 (point G input input) x u alpha).
  * apply (@step_v2 (point G input input) x y u alpha v).
  * apply (@step_e0 (point G input input) x u).
  * apply (@step_e2 (point G input input) x y u v).
Qed.


Fixpoint mentions (A  : eqType) (l : pairs A) := flatten [seq [:: x.1;x.2] | x <- l].

Definition admissible_l (G H : lgraph) (e : pairs (union G H)) := 
  all (fun x => if x is inl z then z \in IO else true) (mentions e).

Definition replace_ioL (G G' H : lgraph) (e : pairs (union G H)) : pairs (union G' H) := 
  map_pairs (fun (x: union G H) => match x with 
                   | inl z => if z == output :> G then inl output else inl input
                   | inr z => inr z
                   end) e.
Arguments replace_ioL [G G' H].

Lemma replace_ioE (vT eT1 eT2 :finType) s1 t1 s2 t2 lv1 lv2 le1 le2 i1 i2 o1 o2 H e : admissible_l e -> 
   i1 = i2 -> o1 = o2 ->                                                                      
   @replace_ioL (@LGraph (@Graph test_setoid term_setoid vT eT1 s1 t1 lv1 le1) i1 o1) 
                (@LGraph (@Graph test_setoid term_setoid vT eT2 s2 t2 lv2 le2) i2 o2) H e = e.
Admitted.

(* Local Notation merge := (@merge test_setoid term_setoid test_monoid). *)

Local Open Scope lgraph_scope.

Lemma iso_merge_add_edgeL (G H : lgraph) x y u e : 
  iso (merge_seq (union (G ∔ [x,u,y]) H) e) 
      (multigraph_new.add_edge (merge_seq (union G H) e) (\pi unl x) (\pi unl y) u).
Admitted.

Definition merge_add_edgeL (G H : lgraph) x y u l i o : 
  liso (point (merge_seq (union (G ∔ [x,u,y]) H) l) i o)
       (point (merge_seq (union G H) l) i o ∔ [\pi unl x,u,\pi unl y]).
Admitted.

Lemma merge_add_edgeLE G H x y u l i o z : @merge_add_edgeL G H x y u l i o z = z.
Admitted.  

Definition merge_add_testL (G H : lgraph) x a (l : pairs (union (G[tst x <- a]) H)) i o : 
  liso (point (merge_seq (union (G[tst x <- a]) H) l) i o)
       ((point (merge_seq (union G H) l) i o)[tst \pi unl x <- a]).
Admitted.

(*
Fixpoint pmap_pairs A B (f : A -> option B) (l : pairs A) : pairs B := 
  match l with 
  | [::] => [::]
  | (x,y)::l' => if (f x,f y) is (Some x',Some y') 
                then (x',y') :: pmap_pairs f l' 
                else pmap_pairs f l'
  end.

Fixpoint strip_SomeL A B (l : pairs ((option A) + B)) : pairs (A + B) := 
  pmap_pairs (fun p => match p with 
                    | inl (Some x) => Some (inl x)
                    | inr x => Some (inr x) 
                    | inl None => None 
                    end) l.
*)

Definition merge_add_vertexL (G H : lgraph) a l : admissible_l l ->
  liso (point (merge_seq (union (G ∔ a) H) l) (\pi (unl input)) (\pi (unr output)))
       ((point (merge_seq (union G H) (replace_ioL l)) (\pi (unl input)) (\pi (unr output))) ∔ a).
Admitted.

Lemma merge_add_vertexLE (G H : lgraph) a (l : pairs(union (G ∔ a) H)) (A : admissible_l l) :
  ((forall x, merge_add_vertexL A (\pi inl (Some x)) = Some (\pi inl x))*
   (merge_add_vertexL A (\pi inl None) = None))%type.
Admitted.

Arguments merge_add_edgeL [G H x y u l i o].
Arguments liso_add_edge [G G'] l [x y u].

Lemma liso_add_edgeE G H l x y u z : @liso_add_edge G H l x y u z = l z. by []. Qed.

Lemma steps_merge (G' G H : lgraph) (l : pairs (union G H)) : 
  admissible_l l -> step G G' -> 
  steps (point (merge_seq (union G H) l) (\pi (unl input)) (\pi (unr output)))
        (point (merge_seq (union G' H) (replace_ioL l)) (\pi (unl input)) (\pi (unr output))).
Proof.
  Arguments replace_ioL : clear implicits.
  move => A B. destruct B. (* why does case fail? *)
  - admit.
  - apply: steps_lisoL merge_add_edgeL.
    apply: steps_lisoL. 2: apply: liso_add_edge. 2: apply (merge_add_vertexL A).
    rewrite !merge_add_vertexLE.
    apply: steps_stepL (step_v1 _ _ _ ) .
    apply: liso_step.  apply: liso_sym. exact: merge_add_testL.
  - apply: steps_lisoL merge_add_edgeL.
    apply: steps_lisoL (liso_add_edge (merge_add_edgeL)).
    rewrite !merge_add_edgeLE. 
    apply: steps_lisoL (liso_add_edge (liso_add_edge (merge_add_vertexL A))).
    rewrite [X in steps X _]/=. rewrite !merge_add_vertexLE.
    apply: steps_stepL (step_v2 _ _ _ _ _) . 
    exact: steps_lisoL (liso_sym merge_add_edgeL). 
  - apply: steps_lisoL merge_add_edgeL.
    apply: steps_stepL (step_e0 _ _).
    apply: steps_lisoL. 2: apply liso_sym. 2: apply: merge_add_testL.
    by rewrite replace_ioE.
  - apply: steps_lisoL merge_add_edgeL.
    apply: steps_lisoL (liso_add_edge (merge_add_edgeL)).
    rewrite !merge_add_edgeLE.
    apply: steps_stepL (step_e2 _ _ _ _).
    apply: steps_lisoL. 2: apply liso_sym. 2: simpl. 2:exact merge_add_edgeL.
    by rewrite replace_ioE.
Admitted.

Lemma step_IO G G' : step G G' -> (input == output :> G) = (input == output :> G').
Proof. by case. Qed.

Lemma dot_steps_l G G' H: steps G G' -> steps (ldot G H) (ldot G' H).
Proof.
  apply (step_to_steps (f:=fun G => ldot G H)) => {G G'}.
  - apply: (fun _ _ I => dot_liso I liso_id). 
  - move => G G' stp_G_G'. rewrite /ldot. etransitivity. apply: (@steps_merge G') => //=.
    + rewrite /admissible_l/=. by rewrite !inE eqxx.
    + by rewrite /replace_ioL/= eqxx. 
Qed.

Lemma ldotcnv G H: liso (ldot G H) (lcnv (ldot (lcnv H) (lcnv G))).
Admitted.

Lemma dot_steps_r G G' H: steps G G' -> steps (ldot H G) (ldot H G').
Proof.
  move => GG'. setoid_rewrite ldotcnv.
  by apply cnv_steps, dot_steps_l, cnv_steps.
Qed.

Instance dot_steps: Proper (steps ==> steps ==> steps) ldot.
Proof.
  repeat intro. by etransitivity; [apply dot_steps_l | apply dot_steps_r].
Qed.

Lemma lparC G H: liso (lpar G H) (lpar H G).
Admitted.

Lemma par_steps_l G G' H: steps G G' -> steps (lpar G H) (lpar G' H).
Proof.
  apply (step_to_steps (f:=fun G => lpar G H))  => {G G'}. 
  - move => G G' I. by apply par_liso.
  - move => G G' step_G_G'. 
    etransitivity. apply: (@steps_merge G') => //=.
    + by rewrite /admissible_l/= !inE !eqxx.
    + rewrite /replace_ioL/= !eqxx. case: ifP => [E|//].
      rewrite (step_IO step_G_G') in E.
      by rewrite -[in (inl output,inr input)](eqP E). 
Qed.

Lemma par_steps_r G G' H: steps G G' -> steps (lpar H G) (lpar H G').
Proof.
  intro.
  etransitivity. apply liso_step, lparC. 
  etransitivity. 2: apply liso_step, lparC.
  by apply par_steps_l. 
Qed.

Instance par_steps: Proper (steps ==> steps ==> steps) lpar.
Proof.
  repeat intro. by etransitivity; [apply par_steps_l | apply par_steps_r].
Qed.


Lemma ldotunit G a: liso (ldot G (point (unit_graph a) tt tt)) (add_test G output a).
Admitted.

Lemma lunitdot G a: liso (ldot (point (unit_graph a) tt tt) G) (add_test G input a).
Admitted.

Lemma lparunitunit a b:
  liso (lpar (point (unit_graph a) tt tt) (point (unit_graph b) tt tt))
       (point (unit_graph [a·b]) tt tt).
Admitted.

Lemma lparedgeunit a u b c:
  liso (lpar (point (edge_graph a u b) false true) (point (unit_graph c) tt tt))
       (point (unit_graph [c∥a·u·b]) tt tt).
Admitted.
       
Lemma add_test_point a c: liso (point (unit_graph a) tt tt [tst tt <- c]) (point (unit_graph [a·c]) tt tt).
Admitted.                       (* could be inlined for now *)

Lemma add_test_edge (x: bool) a u b c:
  liso (point (edge_graph a u b) false true [tst x <- c])
       (point (edge_graph (if x then a else [c·a]) u (if x then [b·c] else b)) false true).
Admitted.

Proposition reduce (u: term): steps (lgraph_of_term u) (lgraph_of_nf_term (nf u)).
Proof.
  induction u=>//=.
  - etransitivity. apply dot_steps; [apply IHu1|apply IHu2].
    case (nf u1)=>[a|a u b];
    case (nf u2)=>[c|c v d]=>/=.
    * apply liso_step.
      setoid_rewrite ldotunit. simpl.
      apply add_test_point. 
    * apply liso_step.
      setoid_rewrite lunitdot. simpl.
      apply add_test_edge. 
    * apply liso_step.
      setoid_rewrite ldotunit. simpl.
      apply add_test_edge. 
    * rewrite /ldot/=.
      etransitivity. apply liso_step.
      2: etransitivity.
      2: apply one_step, (step_v2 (G:=point (two_graph a d) false true) false true u [b·c] v).
      2: apply liso_step.
      2: liso_step (bij_sym unit_option_void)=>/=.
      2: liso bij_id bij_id (fun _ => false)=>//= _; by rewrite !dotA.
      liso_step merge43=>/=. 
      liso_step two_option_option_void=>/=.
      liso bij_id bij_id (fun _ => false)=>//=;
           (repeat case)=>//=;
           rewrite ?merge43E ?merge43E' //=.
      admit.
      admit.
      admit.
      
  - etransitivity. apply par_steps; [apply IHu1|apply IHu2].
    case (nf u1)=>[a|a u b];
    case (nf u2)=>[c|c v d]=>/=.
    * apply liso_step. apply lparunitunit.
    * apply liso_step. setoid_rewrite lparC. apply lparedgeunit.
    * apply liso_step. apply lparedgeunit.
    * rewrite /lpar/=.
      etransitivity. apply liso_step.
      2: etransitivity.
      2: apply one_step, (step_e2 (G:=point (two_graph [a·c] [b·d]) false true) false true u v).
      admit.
      apply liso_step.
      liso_step (bij_sym unit_option_void)=>/=. 
      liso bij_id bij_id (fun _ => false)=>//.
      
  - etransitivity. apply cnv_steps, IHu. 
    case (nf u)=>[a|a v b]=>//=.
    apply liso_step.
    rewrite /lcnv/=. liso bool_swap bij_id (fun _ => true)=>//=.
      by case.
      move=>_. apply cnvI.
      
  - etransitivity. apply dom_steps, IHu. 
    case (nf u)=>[a|a v b]=>//=.
    rewrite /ldom/=.
    etransitivity. apply liso_step.
    2: etransitivity. 2: apply one_step, (@step_v1 (point (unit_graph a) tt tt) tt v b).
    simpl.
    liso_step bool_option_unit=>/=. 
    liso_step unit_option_void=>/=.
    liso bij_id bij_id (fun _ => false)=>//=; case=>//.
    apply liso_step.
    liso bij_id bij_id (fun _ => false)=>//=; case=>//.
    apply dotC. 
Admitted.

Lemma nf_steps s: forall H, steps (lgraph_of_nf_term s) H -> liso (lgraph_of_nf_term s) H.
Proof.
  suff E: forall G H, steps G H -> liso G (lgraph_of_nf_term s) -> liso G H
    by intros; apply E. 
  destruct 1 as [G H I|G' G H H' I S _ _]=>//L.
  - exfalso. apply (liso_comp (liso_sym I)) in L. clear -S L. generalize (card_bij (liso_e L)).
    destruct s; destruct S; simpl in *; (try by rewrite !card_option ?card_unit ?card_void); move=>_.
    * generalize (card_bij (liso_v L)). rewrite card_unit card_option.
      have H: 0 < #|G|. apply /card_gt0P. by exists input.
      revert H. case #|G|; discriminate.
    * generalize (liso_input L). generalize (liso_output L). simpl.
      suff E: input=output :>G by congruence.
      apply (card_le1 (D:=predT))=>//. 
      apply liso_v, card_bij in L. rewrite card_option card_bool in L.
        by injection L=>->.
    * have E: forall y, L None <> L (Some y) by intros y H; generalize (bij_injective (f:=L) H). 
      case_eq (L None).
       generalize (liso_output L) (E output). simpl. congruence. 
       generalize (liso_input L) (E input). simpl. congruence. 
    * generalize (source_liso L None). generalize (target_liso L None).
      case liso_dir; simpl; congruence.
Qed.

Lemma liso_nf (s t: nf_term):
  liso (lgraph_of_nf_term s) (lgraph_of_nf_term t) ->
  term_of_nf s ≡ term_of_nf t.
Proof.
  case s=>[a|a u b];
  case t=>[c|c v d]=>/= h.
  - rewrite -(vlabel_liso h tt). by case (h tt). 
  - exfalso.
    generalize (bijK' h false). generalize (bijK' h true).
    case (h^-1 true). case (h^-1 false). congruence. 
  - exfalso.
    generalize (bijK h false). generalize (bijK h true).
    case (h true). case (h false). congruence.
  - rewrite -(vlabel_liso h false).
    rewrite -(vlabel_liso h true).
    rewrite liso_input liso_output /=. 
    generalize (elabel_liso h tt).
    generalize (source_liso h tt).
    case (liso_dir h tt)=>/=. by rewrite liso_input.
    by move=>_ ->. 
Qed.

Theorem completeness (u v: term): liso (lgraph_of_term u) (lgraph_of_term v) -> u ≡ v.
Proof.
  move=>h.
  pose proof (reduce u) as H.
  have H' : steps (lgraph_of_term u) (lgraph_of_nf_term (nf v))
    by liso_step h; apply reduce. 
  case (confluence H H')=>F [/nf_steps HF /nf_steps HF'].
  rewrite-> (nf_correct u), (nf_correct v).
  apply liso_nf. liso_step HF. by symmetry. 
Qed.
