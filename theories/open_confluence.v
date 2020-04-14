Require Import Relation_Definitions Morphisms RelationClasses.
From mathcomp Require Import all_ssreflect.

Require Import edone finite_quotient preliminaries bij equiv.
Require Import setoid_bigop structures pttdom rewriting.

Require Import finmap_plus.
Open Scope fset_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

(** Picking fresh vertices/edges *)

Definition fresh (E : {fset nat}) : nat := (\max_(e : E) val e).+1.

Lemma freshP (E : {fset nat}) : fresh E \notin E. 
Proof. 
  have S e' : e' \in E -> e' < fresh E. 
  { rewrite /fresh ltnS => inE. by rewrite -[e']/(val [`inE]) leq_bigmax. }
  apply/negP => /S. by rewrite ltnn.
Qed.

Lemma freshP' (E E' : {fset nat}) : E' `<=` E -> fresh E \notin E'.
Proof. apply: contraTN => H. apply/fsubsetPn. exists (fresh E) => //. exact: freshP. Qed.

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

(* Declare Scope open_scope. compat:coq-8.9*)
Bind Scope open_scope with pre_graph.
Delimit Scope open_scope with O.


(** ** Open 2p-graphs labeled with elements of a 2pdom algebra *)

Class inh_type (A : Type) := { default : A }.

Section PttdomGraphTheory.
Variable tm : pttdom.           (* TODO: rename *)
Notation test := (test tm).

Global Instance tm_inh_type : inh_type tm. 
exact: Build_inh_type (1%ptt).
Defined.

Notation pre_graph := (pre_graph test (car (setoid_of_ops (pttdom.ops tm)))).
(* Notation graph := (graph (pttdom_labels tm)). *)
(* Notation graph2 := (graph2 (pttdom_labels tm)). *)

(** ** Strong Equivalence *)


(** In open graphs, we have an equivalence of graphs that have the
same underlying structure with different, but equivalent, labels *)

Set Primitive Projections.
Record eqvG (G H : pre_graph) : Prop := WeqG {
  sameV : vset G = vset H;
  sameE : eset G = eset H;
  same_endpt b : {in eset G, endpt G b =1 endpt H b };
  eqv_lv x : x \in vset G -> lv G x ≡ lv H x;
  eqv_le e : e \in eset G -> le G e ≡ le H e;
  same_in : p_in G = p_in H;
  same_out : p_out G = p_out H
}.

Notation "G ≡G H" := (eqvG G H) (at level 79).
                                       
Global Instance eqvG_Equivalence : Equivalence eqvG.
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

Lemma eqvG_sym : Symmetric eqvG.
Proof. move => *. by symmetry. Qed.

Lemma eqvG_graph (G H : pre_graph) (isG : is_graph G) : G ≡G H -> is_graph H.
Proof.
  move => [EV EE Eep Elv Ele Ei Eo]. econstructor.
  - move => e b Ee. rewrite -EE in Ee. rewrite -EV -Eep //. exact: endptP. 
  - rewrite -EV -Ei. exact: p_inP.
  - rewrite -EV -Eo. exact: p_outP.
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

Global Instance oarc_morphism : Proper (eqvG ==> eq ==> eq ==> eqv ==> eq ==> iff) oarc.
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

(** lemmas about [edges_at] *)

Lemma edges_atE e x : e \in edges_at G x = (e \in eset G) && (incident G x e).
Proof. rewrite /edges_at. by rewrite !inE. Qed.

Lemma edges_atP e z : reflect (e \in eset G /\ exists b, endpt G b e = z) (e \in edges_at G z).
Proof.
  rewrite edges_atE /incident. apply: (iffP andP); intuition. 
  - case/existsP : H1 => b /eqP<-. by exists b.
  -case: H1 => b <-. apply/existsP. by exists b.
Qed.

Lemma edges_atF b e x (edge_e : e \in eset G) :  
  e \notin edges_at G x -> (endpt G b e == x = false).
Proof. rewrite !inE /= edge_e /=. apply: contraNF => ?. by existsb b. Qed.

Lemma degree_one_two x y e e1 e2 : e1 != e2 -> 
  edges_at G x = [fset e] -> edges_at G y = [fset e1;e2] -> x != y.
Proof.
  move => A Ix Iy. apply: contra_neq A => ?;subst y. 
  wlog suff S : e1 e2 Iy / e1 = e.
  { rewrite (S _ _ Iy). symmetry. apply: S. by rewrite Iy fsetUC. }
  apply/eqP. by rewrite -in_fset1 -Ix Iy in_fset2 eqxx.
Qed.

(** lemmas about pIO *)

Definition pIO  := [fset p_in G; p_out G].

Lemma pIO_Ni x : x \notin pIO -> p_in G != x.
Proof. apply: contraNneq => <-. by rewrite in_fset2 eqxx. Qed.

Lemma pIO_No x : x \notin pIO -> p_out G != x.
Proof. apply: contraNneq => <-. by rewrite in_fset2 eqxx. Qed.

Lemma pIO_fresh (isG : is_graph G) x : 
  x \notin vset G -> x \notin pIO.
Proof. apply: contraNN. rewrite !inE. case/orP => /eqP ->; [exact: p_inP|exact: p_outP]. Qed.

(** lemmas about [is_edge] *)

Lemma is_edge_vsetL {isG : is_graph G} e x y u : is_edge G e x u y -> x \in vset G.
Proof. case => E [<- _ _]. exact: endptP. Qed.

Lemma is_edge_vsetR {isG : is_graph G} e x y u : is_edge G e x u y -> y \in vset G.
Proof. case => E [_ <- _]. exact: endptP. Qed.

(** lemmas about [oarc] *)

Lemma edges_at_oarc e x y z u : 
  e \in edges_at G z -> oarc G e x u y -> x = z \/ y = z.
Proof.
  move => Iz [Ee [b] [<- <- _]]. case/edges_atP : Iz => _ [[|]]; case: b; tauto. 
Qed.

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

Lemma oarcxx_le e x u : oarc G e x u x -> 1∥le G e ≡ 1∥u.
Proof. case => E [[|] [A B /= C]]; by rewrite C ?par_tst_cnv. Qed.

Lemma oarc_uniqeR e e' x y u : 
  edges_at G y = [fset e] -> oarc G e' x u y -> e' = e.
Proof. move => Iy /oarc_edge_atR. rewrite Iy. by move/fset1P. Qed.

Lemma oarc_uniqeL e e' x y u : 
  edges_at G x = [fset e] -> oarc G e' x u y -> e' = e.
Proof. rewrite oarc_cnv. exact: oarc_uniqeR. Qed.

Lemma oarc_injL e x x' y u u' : 
  oarc G e x u y -> oarc G e x' u' y -> x = x'.
Proof. 
  case => E [b] [? ? ?] [_ [b'] [? ? ?]]. subst. 
  by destruct b; destruct b'.
Qed.

Lemma oarc_injR e x y y' u u' : 
  oarc G e x u y -> oarc G e x u' y' -> y = y'.
Proof. 
  case => E [b] [? ? ?] [_ [b'] [? ? ?]]. subst. 
  by destruct b; destruct b'.
Qed.

Lemma oarc_loop e x y x' u u' : oarc G e x u y -> oarc G e x' u' x' -> x = y.
Proof. case => Ee [[|]] [? ? ?]; case => _ [[|]] [? ? ?]; by subst. Qed.

Lemma same_oarc e x y x' y' u u' : oarc G e x u y -> oarc G e x' u' y' ->
  [/\ x = x', y = y' & u ≡ u'] \/ [/\ x = y', y = x' & u ≡ u'°].
Proof.
  case => Ee [b] [A B C]. case => _ [b'] [A' B' C']. 
  case: (altP (b =P b')) => [Eb|]. 
  - subst. left. split => //. apply: eqvbN. apply: eqvb_transR C'. by symmetry.
  - rewrite -eqb_negR => /eqP ?; subst. right; split => //. by rewrite negbK.
    apply: eqvbT. apply: eqvb_transR C'. by symmetry.
Qed.

Lemma oarc_eqv e x y u u' : 
  x != y -> oarc G e x u y -> oarc G e x u' y -> u ≡ u'.
Proof. 
  move => xDy arc_e arc_e'. case: (same_oarc arc_e arc_e') xDy => -[? ? ?] //; subst.  
  by rewrite eqxx.
Qed.

End PreGraphTheory.
Hint Resolve is_edge_vsetL is_edge_vsetR : vset.
Hint Resolve oarc_vsetL oarc_vsetR : vset.


(** ** Operatons on open graphs *)

Definition remove_vertex (G : pre_graph) (x : VT) := 
  {| vset := vset G `\ x;
     eset := eset G `\` edges_at G x;
     endpt := endpt G;
     lv := lv G;
     le := le G;
     p_in := p_in G;
     p_out := p_out G |}.

Notation "G \ x" := (remove_vertex G x) (at level 29,left associativity) : open_scope.

Global Instance remove_vertex_graph (G : pre_graph) 
  {graph_G : is_graph G} (x : VT) {Hx : box (x \notin pIO G)} : 
  is_graph (remove_vertex G x).
Proof.
  rewrite /remove_vertex; split => //=. 
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

Notation "G  ∔  [ x , a ]" := (add_vertex G x a) (at level 20, left associativity) : open_scope.

Global Instance add_vertex_graph (G : pre_graph) {graph_G : is_graph G} (x : VT) a : 
  is_graph (add_vertex G x a).
Proof. 
  split => //=; first by move => e b inG; rewrite inE !endptP.
  all: by rewrite inE (p_inP,p_outP).
Qed.

Definition remove_edges (G : pre_graph) (E : {fset ET}) := 
  {| vset := vset G;
     eset := eset G `\` E;
     endpt := endpt G;
     lv := lv G;
     le := le G;
     p_in := p_in G;
     p_out := p_out G |}.

Notation "G - E" := (remove_edges G E) : open_scope.

Lemma remove_edges0 (G : pre_graph) : G - fset0 ≡G G. 
Proof. split => //=. exact: fsetD0. Qed.

Global Instance remove_edges_graph (G : pre_graph) {graph_G : is_graph G} (E : {fset ET}) :
  is_graph (remove_edges G E).
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

Lemma add_edge_graph'' (G : pre_graph) e z t v (graph_G : is_graph (G ∔ [e,z,v,t])) x y u :
  x \in vset G -> y \in vset G -> is_graph (G ∔ [e,x,u,y]).
Proof.
  move => xG yG. split => //=; try apply graph_G. 
  move => e' b; case/fset1UE => [->|[? H]]; rewrite updateE ?(endptP) //.
  by case: b.
  generalize (endptP (is_graph:=graph_G) (e:=e') b). 
  rewrite /=updateE//. move=>D. apply D. by apply fset1Ur. 
Qed.

Lemma add_edge_graph (G : pre_graph) (graph_G : is_graph G) x y u :
  x \in vset G -> y \in vset G -> is_graph (add_edge G x u y).
Proof. exact: add_edge_graph'. Qed.

Definition add_test (G : pre_graph) (x:VT) (a:test) := 
  {| vset := vset G;
     eset := eset G;
     endpt  := endpt G;
     lv := update (lv G) x (a ⊗ lv G x)%lbl;
     le := le G;
     p_in := p_in G;
     p_out := p_out G |}.

(* TODO: all notations for graph operations should be left associative
and at the same level, because this is the only way in which they can
be parsed *)

Global Instance add_test_graph (G : pre_graph) {graph_G : is_graph G} x a :
  is_graph (add_test G x a). 
Proof. split => //=; apply graph_G. Qed.

Notation "G [adt x <- a ]" := (add_test G x a) 
   (at level 2, left associativity, format "G [adt  x  <-  a ]") : open_scope.


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


(** ** Properties of the operations *)

(** Preservation of vertices and edges *)

Lemma in_vsetDV (G : pre_graph) z x : x != z -> x \in vset G -> x \in vset (G \ z).
Proof. by rewrite !inE => -> -> . Qed.

Lemma in_vsetDE (G : pre_graph) x E: x \in vset G -> x \in vset (G - E).
Proof. apply. Qed.

Lemma in_vsetAV (G : pre_graph) z a x : x \in vset G -> x \in vset (G ∔ [z,a]).
Proof. by rewrite !inE => ->. Qed.

Lemma in_vsetAE (G : pre_graph) x y z u e : x \in vset G -> x \in vset (G ∔ [e,y,u,z]).
Proof. by apply. Qed.

Lemma in_vsetAV' (G : pre_graph) z a : z \in vset (G ∔ [z,a]).
Proof. by rewrite !inE eqxx. Qed.
Hint Resolve in_vsetDV in_vsetDE in_vsetAV in_vsetAE in_vsetAV' : vset.

(** Preservation of predicates *)

Lemma pIO_add_vertex (G : pre_graph) x a : pIO (add_vertex G x a) = pIO G. done. Qed.
Lemma pIO_add_edge (G : pre_graph) e x u y : pIO (add_edge' G e x u y) = pIO G. done. Qed.
Lemma pIO_add_test (G : pre_graph) x a : pIO (G[adt x <- a]) = pIO G. done. Qed.
Definition pIO_add := (pIO_add_edge,pIO_add_vertex,pIO_add_test).

Lemma incident_delv G z : incident (G \ z) =2 incident G. done. Qed.
Lemma incident_dele (G : pre_graph) E : incident (G - E) =2 incident G. done. Qed.

Lemma incident_addv (G : pre_graph) x a : incident (G ∔ [x,a]) =2 incident G. done. Qed.

Lemma incident_flip (G : pre_graph) e x : incident (flip_edge G e) x =1 incident G x.
Proof. 
  move => e0. rewrite /incident. case: (altP (e0 =P e)) => [->|D]. 
  - apply/existsP/existsP => [] [b] /eqP<-; exists (~~ b) => /=; by rewrite updateE ?negbK.
  - apply/existsP/existsP => [] [b] /eqP<-; exists b => /=; by rewrite updateE ?negbK.
Qed.

Lemma incident_flip_edge G e x u y : 
  incident (G ∔ [e, x, u, y]) =2 incident (G ∔ [e, y, u°, x]).
Proof. 
  move => z f. rewrite /incident/= !existsb_case.
  case: (altP (f =P e)) => [->|?]; by rewrite !updateE // orbC.
Qed.

Lemma incident_vset (G : pre_graph) (isG : is_graph G) x e : 
  e \in eset G -> incident G x e -> x \in vset G.
Proof. move => He /existsP[b]/eqP<-. exact: endptP. Qed.

Lemma is_edge_remove_edges (G : pre_graph) E e x u y : 
  e \notin E -> is_edge G e x u y -> is_edge (G - E) e x u y.
Proof. move => He. by rewrite /is_edge /= inE He. Qed.

Lemma flipped_edge (G : pre_graph) e x y u : 
  is_edge G e x u° y -> is_edge (flip_edge G e) e y u x.
Proof.
  rewrite /is_edge /flip_edge /= !updateE. firstorder. by rewrite H2 cnvI.
Qed.

Lemma is_edge_flip_edge (G : pre_graph) e1 e2 x y u : 
  e2 != e1 -> is_edge G e2 x u y -> is_edge (flip_edge G e1) e2 x u y.
Proof. move => D. by rewrite /is_edge /flip_edge /= !updateE. Qed.


Lemma lv_add_edge (G : pre_graph) e x u y z : lv (G ∔ [e,x,u,y]) z = lv G z. done. Qed.

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

Lemma edges_at_test (G : pre_graph) x a z : edges_at G[adt x <- a] z = edges_at G z. done. Qed.

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

Lemma edges_atC G e x y u : edges_at (G ∔ [e,x,u,y]) =1 edges_at (G ∔ [e,y,u°,x]).
Proof. move => z. apply/fsetP => f. by rewrite !edges_atE /= incident_flip_edge. Qed.

(** this acually relies on [eset G] containing edges incident to [x] *) 
Lemma edges_at_added_vertex (G : pre_graph) (isG : is_graph G) x a : x \notin vset G -> 
  edges_at (G ∔ [x, a]) x = fset0.
Proof. 
  move => Hx. apply/fsetP => e. rewrite inE edges_atE. 
  case Ee : (_ \in _) => //=. rewrite incident_addv. 
  apply: contraNF Hx. exact: incident_vset.
Qed.

Lemma edges_at_remove_edges (G : pre_graph) z E : 
  edges_at (remove_edges G E) z = edges_at G z `\` E. 
Proof.
  apply/fsetP => e. by rewrite !(inE,edges_atE) -andbA incident_dele.
Qed.

Lemma edges_at_flip_edge (G : pre_graph) (e : ET) (x : VT) : 
  edges_at (flip_edge G e) x = edges_at G x.
Proof. rewrite /edges_at. apply: eq_imfset => //= e0. by rewrite !inE incident_flip. Qed.


Lemma oarc_add_edge (G : pre_graph) e e' x y x' y' u u' : 
  e' != e ->
  oarc G e' x' u' y' -> oarc (G ∔ [e,x,u,y]) e' x' u' y'. 
Proof.
  move => eDe'. 
  rewrite /oarc /= !updateE // in_fset1U (negbTE eDe') /=. 
  case => A [b] B. split => //. exists b. by rewrite !updateE.
Qed.

Lemma oarc_added_edge (G : pre_graph) e x y u : oarc (G ∔ [e,x,u,y]) e x u y. 
Proof. 
  split. 
  - by rewrite !inE eqxx.
  - by exists false; split; rewrite /= update_eq. 
Qed.

Lemma oarc_remove_edges (G : pre_graph) e x u y E : 
  e \notin E -> oarc G e x u y -> oarc (remove_edges G E) e x u y.
Proof. move => He. by rewrite /oarc /= inE He. Qed.

Lemma oarc_remove_vertex (G : pre_graph) z e x y u : 
  e \notin edges_at G z -> oarc G e x u y -> oarc (G \ z) e x u y.
Proof. move => Iz [edge_e H]. apply: conj H. by rewrite inE Iz. Qed.

Lemma oarc_flip_edge (G : pre_graph) e1 e2 x y u : 
  oarc G e2 x u y -> oarc (flip_edge G e1) e2 x u y.
Proof.
  case: (altP (e2 =P e1)) => [->|D]. 
  - case => E [b] [A B C]. split => //. exists (~~ b). rewrite /= !negbK !updateE. 
    split => //. symmetry. rewrite eqvb_neq. symmetry. by rewrite cnvI.
  - case => E [b] [A B C]. split => //. exists b. by rewrite /= !updateE.
Qed.



(** ** Commutation Lemmas *)

Lemma remove_vertexC (G : pre_graph) (x y : VT) : (G \ x \ y)%O = (G \ y \ x)%O. 
Proof. 
  rewrite /remove_vertex/=; f_equal. 
  - by rewrite fsetDDl fsetUC -fsetDDl.
  - by rewrite !edges_at_del fsetDDD fsetUC -fsetDDD.
Qed.

Lemma add_testC (G : pre_graph) x y a b :
  G[adt x <- a][adt y <- b] ≡G G[adt y <- b][adt x <- a].
Proof.
  split => //= z. 
  case: (altP (x =P y)) => xy; subst. 
  - rewrite !update_same. case: (altP (z =P y)) => zy; subst; rewrite !updateE => //=.
    by rewrite monA [(b ⊗ a)%lbl]monC -monA.
  - case: (altP (z =P x)) => zx; case: (altP (z =P y)) => zy; subst.
    by rewrite eqxx in xy. all: by rewrite !updateE.
Qed.

Lemma remove_vertex_add_test (G : pre_graph) z x a : 
  (G \ z)[adt x <- a] ≡G G[adt x <- a] \ z.
Proof. done. Qed.

(** This does not hold for [add_edge] since [add_edge] takes the
lowest available edge, which may change after deleting [z]. *)
Lemma remove_vertex_add_edge (G : pre_graph) z x y u e : z != x -> z != y ->
  e \notin eset G ->                                                      
  add_edge' (G \ z) e x u y ≡G (add_edge' G e x u y) \ z.
Proof.
  move => Hx Hy He. split => //=. rewrite edges_at_add_edge' ?[_ == z]eq_sym //.
  rewrite fsetDUl [[fset _] `\` _](fsetDidPl _ _ _) //. 
  apply/fdisjointP => ? /fset1P ->. by rewrite edges_atE (negbTE He).
Qed.

Lemma remove_vertex_edges G E z : G \ z - E ≡G (G - E)\z.
Proof. 
  split => //. 
  by rewrite /remove_vertex/= edges_at_remove_edges fsetDDD fsetDDl fsetUC.
Qed.

Lemma add_edge_test (G : pre_graph) e x y z u a : 
  (G ∔ [e,x,u,y])[adt z <- a] ≡G G[adt z <- a] ∔ [e,x,u,y].
Proof. done. Qed.

Lemma remove_edges_add_test (G : pre_graph) E x a : 
  (remove_edges G E)[adt x <- a] ≡G remove_edges G[adt x <- a] E. 
Proof. done. Qed.

Lemma add_edge_remove_edges (G : pre_graph) e E x y u : 
  e \notin E -> G ∔ [e,x,u,y] - E ≡G (G - E) ∔ [e,x,u,y]. 
Proof. move => He. split => //=. by rewrite fsetUDl mem_fsetD1. Qed.

Lemma remove_edges_vertex (G : pre_graph) E z : 
  (G - E) \ z ≡G G \ z - E.
Proof. split => //=. by rewrite edges_at_remove_edges fsetDDD fsetDDl fsetUC. Qed.

Lemma add_test_edge (G : pre_graph) e x y z a u : 
  (G[adt z <- a] ∔ [e,x,u,y])%O = ((G ∔ [e,x,u,y])[adt z <- a])%O.
Proof. done. Qed.

Lemma remove_edges_edges (G : pre_graph) E E' : 
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

Lemma add_test_merge G x a b : 
  G[adt x <- a][adt x <- b] ≡G G[adt x <- [a·b]].
Proof. 
  constructor => //= y yG. 
  case: (altP (y =P x)) => [->|?]; rewrite !updateE //=. 
  by rewrite monA [(b ⊗ a)%lbl]monC -monA.
Qed.

Lemma flip_edge_add_test (G : pre_graph) (e : ET) (x : VT) a : 
  ((flip_edge G e)[adt x <- a])%O = (flip_edge (G[adt x <- a]) e)%O.
Proof. done. Qed.


(** ** Morphism Lemmas *)

Global Instance add_edge_morphism' : Proper (eqvG ==> eq ==> eq ==> eqv ==> eq ==> eqvG) add_edge'.
Proof. 
  move => G H [EV EE Eep Elv Ele Ei Eo] ? e ? ? x ? u v uv ? y ?. subst. 
  split => //= [|b|e'].
  - by rewrite EE.
  - apply: in_eqv_update => // ?. exact: Eep.
  - exact: in_eqv_update.
Qed.

Global Instance add_edge_morphism : Proper (eqvG ==> eq ==> eqv ==> eq ==> eqvG) add_edge.
Proof. 
  move => G H GH e e' E. apply: add_edge_morphism' => //. by rewrite (sameE GH).
Qed.
  
Lemma eqvG_edges_at G H : G ≡G H -> edges_at G =1 edges_at H.
Proof. 
  move => GH. move => x. apply/fsetP => e. 
  rewrite !edges_atE -(sameE GH). case E : (_ \in _) => //=. 
  apply: existsb_eq => b. by rewrite (same_endpt GH).
Qed.

Global Instance remove_vertex_morphism : Proper (eqvG ==> eq ==> eqvG) remove_vertex.
Proof with  apply/fsubsetP; exact: fsubsetDl.
  move => G H [EV EE Eep Elv Ele Ei Eo] ? x ?. subst. 
  have EGH : edges_at G =1 edges_at H by exact: eqvG_edges_at.
  split => //=; rewrite -?EE -?EV -?EGH //. 
  - move => b. apply: sub_in1 (Eep b) => //...
  - apply: sub_in1 Elv => //...
  - apply: sub_in1 Ele => //...
Qed.

(* TOTHINK is "eqv" the right equivalence to use for tests *)
Global Instance add_test_morphism : Proper (eqvG ==> eq ==> eqv ==> eqvG) add_test.
Proof.
  move => G H [EV EE Eep Elv Ele Ei Eo] ? x ? u v uv. subst.
  split => //= y Hy. case: (altP (y =P x)) => [?|?].
  - subst y. by rewrite !updateE Elv // uv.
  - by rewrite !updateE // Elv.
Qed.

(** ** Killing Lemmas *)

Lemma remove_vertexK (G : pre_graph) (isG : is_graph G) z : 
  z \in vset G -> 
  (G \ z) ∔ [z,lv G z] ≡G G - edges_at G z.
Proof. split => //= [|x _]; by rewrite ?fsetD1K ?update_fx. Qed.

Lemma remove_edgesK (G : pre_graph) E z :
  E `<=` edges_at G z -> (remove_edges G E) \ z ≡G G \ z.
Proof. 
  move => subE. split => //=. 
  by rewrite edges_at_remove_edges fsetDDD (fsetUidPr _ _ subE).
Qed.

Lemma remove_edgeK (G : pre_graph) (isG : is_graph G) e x y u : 
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
Lemma add_edge_remove_vertex (G : pre_graph) e x u y : 
  e \notin eset G -> G ∔ [e,x,u,y] \ y ≡G G \ y.
Proof.
  move => He. split => //=; rewrite edges_at_add_edge. 2: move => b.
  all: rewrite fsetUDU ?fdisjoint1X // => f /fsetDP [Hf _]; 
       rewrite update_neq //; by apply: contraNneq He => <-.
Qed.
Definition add_edgeKr := add_edge_remove_vertex.

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

Lemma add_edge_remove_edgesK (G : pre_graph) e E x y u : 
  e \in E -> G ∔ [e,x,u,y] - E ≡G (G - E). 
Proof.
  move => eE. 
  have X : (e |` eset G) `\` E = eset G `\` E.
  { by rewrite fsetDUl fset1D eE fset0U. }
  split => //=; rewrite X. 1: move => b.
  all: move => f Hf; rewrite updateE //.
  all: apply: contraTneq Hf => ->; by rewrite inE eE.
Qed.

Lemma remove_edges_vertexK (G : pre_graph) E z : 
  E `<=` edges_at G z -> (G - E) \ z ≡G G \ z.
Proof. 
  move => EIz. split => //=. 
  by rewrite fsetDDl edges_at_remove_edges fsetUDl fsetDv fsetD0 (fsetUidPr _ _ EIz).
Qed.

Lemma flip_edgeK (G : pre_graph) (e : ET) (x : VT)  : 
  e \in edges_at G x -> (flip_edge G e) \ x ≡G G \ x.
Proof. 
  move => He. split; rewrite //= edges_at_flip_edge //.
  - move => b e' /fsetDP [A B]. rewrite updateE //. by apply: contraNneq B => ->.
  - move => e' /fsetDP [A B]. rewrite updateE //. by apply: contraNneq B => ->.
Qed.
  
Lemma flip_edgeK' (G : pre_graph) (e : ET) (E : {fset ET})  : 
  e \in E -> (flip_edge G e) - E ≡G G - E.
Proof. 
  move => He. split; rewrite //= ?edges_at_flip_edge //.
  - move => b e' /fsetDP [A B]. rewrite updateE //. by apply: contraNneq B => ->.
  - move => e' /fsetDP [A B]. rewrite updateE //. by apply: contraNneq B => ->.
Qed.


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
    ostep G ((remove_edges G [fset e])[adt x <- [1∥le G e]])
| ostep_e2 x y e1 e2 u v : e1 != e2 ->
    oarc G e1 x u y -> oarc G e2 x v y ->
    ostep G ((remove_edges G [fset e1;e2]) ∔ [maxn e1 e2,x,u∥v,y]).

(* flipping an edge; this rule is not included in [ostep] as it would make the rewrite system non-terminating 
   we however use it in [osteps] in order to enable wlog reasonings in the local confluence proof
   this is fine in the end since fliping edges is allowed in isomorphisms

   it would be even nicer to let eqvG handle edge flips ; 
   it is however convenient to keep eqvG in Prop
   and adding edge flips in Prop prevents us from proving the implication eqvG => oiso2 (lemma [eqvG_oiso] below, with oiso2 in Type) 
   this implication is quite convenient in [ostep_of]
 *)
End ostep.

Variant fstep: relation pre_graph :=
| flip_step: forall (G : pre_graph) e x y u v, 
                      u° ≡ v ->
                      x \in vset G -> y \in vset G ->
                      fstep (G ∔ [e,x,u,y])%O (G ∔ [e,y,v,x])%O.
  
Inductive osteps: relation pre_graph :=
| eqvG_step: RelationClasses.subrelation eqvG osteps
| fstep_step: RelationClasses.subrelation fstep osteps
| ostep_step: CRelationClasses.subrelation ostep osteps
| osteps_trans: RelationClasses.Transitive osteps.
Global Instance osteps_preorder: PreOrder osteps.
Proof.
  split. intro. by apply eqvG_step.
  apply osteps_trans.
Qed.
Global Existing Instance eqvG_step.
Global Existing Instance fstep_step.
Global Existing Instance ostep_step.

Lemma osteps_refl (G : pre_graph) : osteps G G.
Proof. exact: eqvG_step. Qed.
Hint Resolve osteps_refl : core.

Lemma eqvG_stepL G G' H : G ≡G G' -> osteps G' H -> osteps G H.
Proof. move => h A. by rewrite h. Qed.

Lemma ostepL G G' H : ostep G G' -> osteps G' H -> osteps G H.
Proof. move => A. apply: osteps_trans. exact: ostep_step. Qed.


Definition step_order G H (s: ostep G H): nat :=
  match s with
  | ostep_v0 _ _ _ _ => 0
  | ostep_v1 _ _ _ _ _ _ _ _ => 1
  | ostep_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 2
  | ostep_e0 _ _ _ _ => 3
  | ostep_e2 _ _ _ _ _ _ _ _ _ => 4
  end.

(** ** Open Local Confluence *)

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

Lemma critical_pair1 u v (a :test) : dom ((u∥v°)·a) ≡ 1 ∥ u·a·v. 
Proof. by rewrite -dotA A10 cnvdot cnvtst partst. Qed. 

Lemma critical_pair2 (u v : tm) : (1∥u)·(1∥v) ≡ 1∥(u∥v).
Proof. 
  rewrite (par1tst u) (par1tst v) -pardot /=.
  by rewrite parA [_∥1]parC !parA par11. 
Qed. 

Lemma critical_pair3 u u' (a b : test) :  dom (u'·(dom (u·a)·b)) ≡ dom (u'·b·u·a).
by rewrite (dom_tst (u·a)) tst_dotC /= dotA -A13 !dotA.
Qed.

Ltac e2split := do 2 eexists; split; [split|].

Lemma close_same_step (Gl Gr : pre_graph) (isGl : is_graph Gl) (isGr : is_graph Gr) : 
  Gl ≡G Gr -> exists Gl' Gr' : pre_graph, (osteps Gl Gl' /\ osteps Gr Gr') /\ (Gl' ≡G Gr').
Proof. move => E. e2split; by try exact: osteps_refl. Qed.


(* Local confluence: Proposition 8.5 *)
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
    + subst z'. do 2 exists ((G \ z)%O). split => //. 
    + exists (G \ z \ z')%O. exists (G \ z' \ z)%O. rewrite {2}remove_vertexC. split => //.
      split; apply ostep_step,ostep_v0 => //=. 
      2,4: by rewrite edges_at_del Iz Iz' fsetD0.
      all: by rewrite !inE ?D 1?eq_sym ?D.
  - (* V0 / V1 *) 
    have D : z != z'. { apply: contra_eq_neq Iz => ->. by rewrite Iz' fset01. }
    e2split.
    + eapply ostep_step,ostep_v1. 3: eapply oarc_remove_vertex,arc_e'. all: try done.
      * by rewrite edges_at_del Iz Iz' fsetD0.
      * by rewrite Iz inE.
    + eapply ostep_step,(ostep_v0 (z := z)). 3:done.
      * by rewrite !inE D /=.
      * by rewrite edges_at_del edges_at_test Iz fset0D.
    + by rewrite remove_vertexC remove_vertex_add_test.
  - (* V0 / V2 *) 
    have D : z != z'. { apply: contra_eq_neq Iz' => <-. by rewrite Iz eq_sym fset1U0. }
    have [? ?] : x' != z /\ y' != z. 
    { split. 
      - apply: contra_eq_neq Iz => <-. apply/fset0Pn; exists e1'. exact: oarc_edge_atL arc_e1'.
      - apply: contra_eq_neq Iz => <-. apply/fset0Pn; exists e2'. exact: oarc_edge_atR arc_e2'. }
    e2split.
    + eapply ostep_step,ostep_v2. 
      6-7: apply: oarc_remove_vertex. 7: apply arc_e1'. 8: apply: arc_e2'.
      all: try done.
      all: by rewrite ?edges_at_del ?Iz ?Iz' ?fsetD0 ?inE.
    + eapply ostep_step,(ostep_v0 (z := z)). 3:done.
        by rewrite !inE D.
      rewrite @edges_at_add_edge' //=. 
      * by rewrite edges_at_del Iz fset0D.
      * by rewrite Iz' maxn_fsetD.
    + by rewrite -remove_vertex_add_edge 1?eq_sym 1?remove_vertexC //= Iz' maxn_fsetD.
  - (* V0 / E0 *) 
    have zDx : z != x'. 
    { apply: contra_eq_neq Iz => ->. apply/fset0Pn. exists e'. exact: oarc_edge_atL arc_e'. }
    e2split.
    + eapply ostep_step,ostep_e0. apply: oarc_remove_vertex arc_e'. by rewrite Iz inE.
    + eapply ostep_step,(@ostep_v0 _ z) => //.
      by rewrite edges_at_test edges_at_remove_edges Iz fset0D.
    + by rewrite /= -remove_vertex_add_test -remove_vertex_edges.
  - (* V0 / E2 *) 
    have[zDx zDy] : z != x' /\ z != y'. 
    { split;apply: contra_eq_neq Iz => ->;apply/fset0Pn;exists e1'. 
      exact: oarc_edge_atL arc_e1'. exact: oarc_edge_atR arc_e1'. }
    e2split.
    + eapply ostep_step,ostep_e2. exact: e1De2'.
      all: apply oarc_remove_vertex; eauto. all: by rewrite Iz inE.
    + eapply ostep_step,(@ostep_v0 _ z) => //.
      rewrite edges_at_add_edge' 1?eq_sym ?maxn_fsetD //. 
      by rewrite edges_at_remove_edges Iz fset0D.
    + by rewrite remove_vertex_edges remove_vertex_add_edge ?maxn_fsetD.
  - (* V1 / V1 *) 
    case: (altP (z =P z')) => [E|D]; last case: (altP (e =P e')) => [E|E].
    + (* same instance *)
      subst z'. 
      have ? : e' = e by apply: oarc_uniqeR arc_e'. subst e'.
      have ? : x = x' by apply: oarc_injL arc_e arc_e'. subst x'.
      apply: close_same_step. 
      suff -> : [dom (u·lv G z)] ≡ [dom (u'·lv G z)] by [].
      by rewrite infer_testE (oarc_eqv _ arc_e arc_e').
    + (* isolated [z --e-- z'] pseudo-case *) subst e'.
      case: (same_oarc arc_e arc_e') => [[? ? U]|[? ? U]]; subst z' x'; first by rewrite eqxx in D.
      e2split.
      * eapply ostep_step, (@ostep_v0 _ x) => //.
        rewrite !inE eq_sym D. exact: oarc_vsetL arc_e.
        by rewrite edges_at_del !edges_at_test Iz Iz' fsetDv.
      * eapply ostep_step, (@ostep_v0 _ z) => //. 
        rewrite !inE D. exact: oarc_vsetR arc_e.
        by rewrite edges_at_del !edges_at_test Iz Iz' fsetDv.
      * by rewrite remove_vertexC [in X in _ ≡G X]remove_vertexC !add_testK remove_vertexC.
     + (* two independen pendants *)
      gen have H,Hz : z z' x x' e e' u u' Iz Iz' arc_e' arc_e E {xDz xDz' zIO zIO' D} / z != x'. 
      { apply: contraTneq E => ?. subst x'. 
        rewrite negbK eq_sym -in_fset1 -Iz. apply: oarc_edge_atL arc_e'. }
      have {H} Hz' : z' != x by apply: H arc_e arc_e' _ ; rewrite // eq_sym.
      do 2 eexists. split. split. 
      * eapply ostep_step, ostep_v1. 3: eapply oarc_remove_vertex. 4: apply arc_e'.
        all: try done. 
        by rewrite edges_at_del /= !edges_at_test Iz' Iz mem_fsetD1 // inE.
        by rewrite edges_at_test Iz inE eq_sym.
      * eapply ostep_step, ostep_v1. 3: eapply oarc_remove_vertex. 4: apply arc_e.
        all: try done. 
        by rewrite edges_at_del /= !edges_at_test Iz' Iz mem_fsetD1 // inE eq_sym.
        by rewrite edges_at_test Iz' inE.
      * by rewrite !remove_vertex_add_test remove_vertexC add_testC /= !updateE. 
  - (* V1 / V2 *)
    have zDz' : z != z' by apply: degree_one_two Iz Iz'.
    case: (boolP (z \in [fset x';y'])) => [z_xy'|xD'].
    + (* double pendant *)
      wlog: x' y' xDz' yDz' u' v' e1' e2' arc_e1' arc_e2' Iz' e1De2' {z_xy'} / z = y' => [W|?].
      { move: z_xy'. rewrite !inE. case/orb_sum => /eqP E ; last exact: W. 
        rewrite -> oarc_cnv in arc_e1',arc_e2'. 
        move/(_ y' x' yDz' xDz' _ _ _ _ arc_e2' arc_e1') in W. rewrite fsetUC eq_sym in W.
        case: W => // Gl [Gr] [[S1 S2] WG]. exists Gl. exists Gr. do 2 (split => //).
        rewrite-> maxnC, flip_step ; eauto with vset. 
        by rewrite !cnvdot cnvtst dotA. }
      subst y'. 
      have ? : e2' = e by apply: oarc_uniqeR arc_e2'. subst e2'. 
      have ? : x = z' by apply: oarc_injL arc_e arc_e2'. subst x. 
      have Dz : x' != z. 
      { apply: contra_neq e1De2' => ?. subst. exact: oarc_uniqeL arc_e1'. }
      e2split.
      * eapply ostep_step, ostep_v1. 
        3: { apply: oarc_remove_vertex arc_e1'. by  rewrite Iz inE. }
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
        rewrite -remove_vertex_add_test remove_vertexC add_testK. 
        rewrite -remove_vertex_add_test add_edgeKr /= ?Iz' ?maxn_fsetD //.
        apply: add_test_morphism => //=.
        rewrite infer_testE (oarc_eqv _ arc_e2' arc_e) //. exact: critical_pair3.
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
        6: { apply: oarc_remove_vertex. 2: apply: arc_e1'. by rewrite edges_at_test Iz inE. }
        6: { apply: oarc_remove_vertex. 2: apply: arc_e2'. by rewrite edges_at_test Iz inE. }
        all: try done. 
        by rewrite edges_at_del !edges_at_test Iz Iz' mem_fsetD1.
      * eapply ostep_step, ostep_v1. 
        3: { apply: oarc_add_edge. 2:apply: oarc_remove_vertex arc_e. 
             apply: fset2_maxn_neq => //. by rewrite Iz'. }
        all: try done. 
        rewrite edges_at_add_edge' ?[_ == z]eq_sym //= ?edges_at_del ?Iz Iz' ?maxn_fsetD //.
        by rewrite -fsetDDl !mem_fsetD1 ?inE.
      * set e12 := maxn _ _. set a := lv G z. set b := lv G z'. set a' := lv _ z. set b' := lv _ z'. 
        have <- : a = a' by []. have <- : b = b'. rewrite /b /b' /= updateE //. 
        rewrite remove_vertexC -remove_vertex_add_test add_edge_test. rewrite -remove_vertex_add_edge //. 
        by rewrite /= inE negb_and negbK Iz' !inE maxn_eq.
  - (* V1 / E0 - no nontrivial interaction *)
    have De : e != e'. 
    { apply: contra_neq xDz => ?; subst e'. exact: oarc_loop arc_e arc_e'. }
    have Dx' : x' != z. 
    { apply: contra_neq De => ?; subst x'. symmetry. exact: oarc_uniqeL arc_e'. }
    e2split.
    * eapply ostep_step, ostep_e0. apply: oarc_remove_vertex arc_e'. 
      by rewrite Iz !inE eq_sym.
    * eapply ostep_step, ostep_v1. 3: { apply: oarc_remove_edges arc_e. by rewrite inE. }
      all: try done. 
      by rewrite edges_at_test edges_at_remove_edges Iz mem_fsetD1 // inE eq_sym.
    * rewrite /= updateE 1?eq_sym //. 
      rewrite remove_vertex_edges -remove_edges_add_test. 
      by rewrite remove_vertex_add_test add_testC. 
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
      -- apply: oarc_remove_vertex arc_e1'. by rewrite Iz inE.
      -- apply: oarc_remove_vertex arc_e2'. by rewrite Iz inE.
    * eapply ostep_step, ostep_v1.
      3: { apply: oarc_add_edge. 2: apply: oarc_remove_edges arc_e => //.
           exact: fset2_maxn_neq. }
      all: try done.
      rewrite edges_at_add_edge' //= ?maxn_fsetD //. 
      by rewrite edges_at_remove_edges -fsetDDl !mem_fsetD1 // Iz in_fset1.
    * rewrite /= add_edge_test remove_edges_add_test -remove_vertex_add_edge -?remove_vertex_edges // 1?eq_sym //.
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
          rewrite-> maxnC, flip_step; eauto with vset.
          by rewrite !cnvdot cnvtst dotA. }
        subst e1' e2'.
        case: (altP (z =P z')) => [?|D].
        { (* same instance up to direction *)
          subst z'.
          eapply close_same_step. 1-2: apply add_edge_graph'; eauto with vset typeclass_instances.
          move: (oarc_injL arc_e1 arc_e1') (oarc_injR arc_e2 arc_e2') => ? ?. subst x' y'.
          by rewrite (oarc_eqv _ arc_e1' arc_e1) ?(oarc_eqv _ arc_e2' arc_e2) // eq_sym. }
        { (* z =e1/e2= z' -- pseudo case *)
          (* there is only z and and z' ... *)
          case: (same_oarc arc_e1 arc_e1') => [[? ? U]|[? ? U]]; first by subst;rewrite eqxx in D.
          subst x x'.
          case: (same_oarc arc_e2 arc_e2') => [[? ? U']|[? ? U']]; first by subst;rewrite eqxx in D.
          subst y y'.
          have ?: (maxn e1 e2 |` [fset e1; e2] `\` [fset e1; e2]) `\ maxn e1 e2 = fset0.
          { apply/fsetP => e; rewrite !inE; case: maxnP => _.
            all: case (altP (e =P e1)) => [?|?]; subst; rewrite ?(negbTE e1De2) //=.
            all: by case: (altP (e =P e2)). }
          e2split.
          * apply: ostepL. apply: ostep_e0. apply: oarc_added_edge.
            apply: ostep_step. apply: (@ostep_v0 _ z'). all: try done.
              rewrite /= in_fsetD inE eq_sym D. exact: oarc_vsetL arc_e1.
            rewrite /= edges_at_test edges_at_remove_edges edges_at_add_edge. 
            by rewrite edges_at_del Iz Iz'. 
          * apply: ostepL. apply: ostep_e0. apply: oarc_added_edge.
            apply: ostep_step. apply: (@ostep_v0 _ z). all: try done.
              rewrite /= in_fsetD inE D. exact: oarc_vsetR arc_e1.
            rewrite /= edges_at_test edges_at_remove_edges edges_at_add_edge. 
            by rewrite edges_at_del Iz Iz'. 
          * rewrite !add_testK !add_edge_remove_edgesK. 2-3: by rewrite in_fset1.
            by rewrite -!remove_vertex_edges remove_vertexC. }
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
       (* have zDz' : z != z'. by .... *)       
       e2split.
       * eapply ostep_step,ostep_v2. 
         7: { apply: oarc_add_edge. 2:apply: oarc_remove_vertex arc_e2'. 
              apply: fset2_maxn_neq. by rewrite D2 // in_fset2 eqxx.
              by rewrite Iz D2 // !inE eqxx. }
         6: { apply: oarc_add_edge. 2:apply: oarc_remove_vertex arc_e1'. 
              apply: fset2_maxn_neq. by rewrite D2 // in_fset2 eqxx.
              by rewrite Iz D2 // !inE eqxx. }
         all: try done.
         rewrite edges_at_add_edge' //= ?Iz ?maxn_fsetD // edges_at_del Iz Iz'. 
         by apply/fsetDidPl.
       * eapply ostep_step,ostep_v2. 
         7: { apply: oarc_add_edge. 2: apply: oarc_remove_vertex arc_e2. 
              apply: fset2_maxn_neq. by rewrite D1 // in_fset2 eqxx.
              by rewrite Iz' D1 // in_fset2 eqxx. }
         6: { apply: oarc_add_edge. 2: apply: oarc_remove_vertex arc_e1. 
              apply: fset2_maxn_neq. by rewrite D1 // in_fset2 eqxx.
              by rewrite Iz' D1 // !inE eqxx. }
         all: try done.
         (* FIXME : swap disequality assumptions on edges_at_add_edge' *)
         rewrite edges_at_add_edge' //= ?Iz' ?maxn_fsetD // edges_at_del Iz Iz'. 
         apply/fsetDidPl. by rewrite fdisjoint_sym.
       * rewrite /=. rewrite -!remove_vertex_add_edge /= ?Iz ?Iz' 1?eq_sym ?maxn_fsetD //.
         rewrite remove_vertexC add_edge_edge //. 
         by case: maxnP => _; rewrite fset2_maxn_neq // D1 // !inE eqxx.
     + (* overlap in one edge *) 
       wlog ? : e1 e2 x y u v  arc_e1 arc_e2 Iz e1De2 zIO xDz yDz He / e = e2 ; [move => W|subst e]. 
       { have: e \in [fset e1;e2]. { move/fsetP : He => /(_ e). rewrite in_fset1 eqxx. by case/fsetIP. }
         rewrite inE. case/orb_sum => /fset1P => E; last exact: W.
         rewrite -> oarc_cnv in arc_e1,arc_e2. 
         move/(_ _ _ _ _ _ _ arc_e2 arc_e1) in W. rewrite fsetUC eq_sym in W.
         case: W => // Gl [Gr] [[S1 S2] WG]. exists Gl. exists Gr. do 2 (split => //). 
         rewrite-> maxnC, flip_step; eauto with vset.
         by rewrite !cnvdot cnvtst dotA. }
       wlog ? : e1' e2' x' y' u' v'  arc_e1' arc_e2' Iz' e1De2' xDz' yDz' He / e2 = e1' ; [move => W|subst e1'].
       { have: e2 \in [fset e1';e2']. { move/fsetP : He => /(_ e2). rewrite in_fset1 eqxx. by case/fsetIP. }
         rewrite inE. case/orb_sum => /fset1P => E; first exact: W.
         rewrite -> oarc_cnv in arc_e1',arc_e2'. 
         move/(_ _ _ _ _ _ _ arc_e2' arc_e1') in W. rewrite fsetUC eq_sym in W.
         case: W => // Gl [Gr] [[S1 S2] WG]. exists Gl. exists Gr. do 2 (split => //). 
         rewrite-> maxnC, flip_step; eauto with vset.
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
         6: apply: oarc_add_edge. 7: apply: oarc_remove_vertex arc_e2'. 
         all: try done. 
         -- exact: edges_replace.
         -- by case/orP : (maxn_eq e1 e2) => /eqP ->.
         -- apply: contraTneq (oarc_edge_atL arc_e1) => ->. by rewrite Iz' !inE negb_or e1De2.
         -- apply: fset2_maxn_neq. by rewrite in_fset2 ![e2' == _]eq_sym negb_or E1.
         -- by rewrite Iz !inE negb_or eq_sym E1 eq_sym.
       * eapply ostep_step,ostep_v2. 
         7: apply: oarc_added_edge.
         6: apply: oarc_add_edge. 7: apply: oarc_remove_vertex arc_e1.
         all: try done. 
         -- rewrite edges_atC fsetUC maxnC. apply: edges_replace; by rewrite // 1?fsetUC 1?eq_sym.
         -- by case/orP : (maxn_eq e2 e2') => /eqP ->.
         -- apply: contraTneq (oarc_edge_atR arc_e2') => ->.
            by rewrite Iz !inE negb_or eq_sym E1 eq_sym.
         -- apply: fset2_maxn_neq. by rewrite in_fset2 negb_or e1De2.
         -- by rewrite Iz' !inE negb_or e1De2.
       * rewrite !add_edgeKr ?add_edgeKl /= ?Iz ?Iz' ?maxn_fsetD //.
         by rewrite remove_vertexC maxnA !dotA C.
  - (* V2 / E0 *) 
    have He : e' \notin edges_at G z. 
    { rewrite Iz in_fset2 negb_or. apply/andP; split.
      - apply: contra_neq xDz => ?; subst e'. exact: oarc_loop arc_e1 arc_e'.
      - apply: contra_neq yDz => ?; subst e'. symmetry. exact: oarc_loop arc_e2 arc_e'. }
    have xDz' : z != x' by apply: contraTneq (oarc_edge_atL arc_e') => <-. 
    have He' : e' != maxn e1 e2. apply: fset2_maxn_neq. by rewrite -Iz. 
    e2split. 
    * eapply ostep_step,ostep_e0. apply: oarc_add_edge He' _. exact: oarc_remove_vertex arc_e'.      
    * eapply ostep_step,ostep_v2. 
      6: { apply: oarc_remove_edges arc_e1. 
           rewrite inE. apply: contraNneq He => <-. by rewrite Iz !inE eqxx. }
      6: { apply: oarc_remove_edges arc_e2. 
           rewrite inE. apply: contraNneq He => <-. by rewrite Iz !inE eqxx. }
      all: try done. 
      by rewrite edges_at_test edges_at_remove_edges -Iz mem_fsetD1.
    * rewrite /= !updateE //. rewrite add_edge_remove_edges ?inE 1?eq_sym //. 
      by rewrite -remove_vertex_add_test remove_edges_vertex add_test_edge.
  - (* V2 / E2 *) 
    case: (boolP (z \in [fset x'; y'])) => Hz.
    + (* complete overlap *) 
      wlog ? : x' y' e1' e2' u' v' e1De2' arc_e1' arc_e2' {Hz} / z = y'.
      { move => W. move: Hz. rewrite in_fset2. case/orb_sum => /eqP ?; last exact: W.
        subst x'. rewrite -> oarc_cnv in arc_e2', arc_e1'. 
        case: (W _ _ _ _ _ _ _ arc_e2' arc_e1'); rewrite 1?eq_sym //.
        move => Gl' [Gr'] [[Sl Sr] E]. e2split; [exact: Sl| |exact: E].
        rewrite-> fsetUC, maxnC, flip_step; eauto with vset.
        by rewrite cnvpar parC. }
      subst y'. 
      wlog ? : e1 e2 u v x y e1De2 arc_e1 arc_e2 xDz yDz Iz / e1' = e1.
      { move => W. move:(oarc_edge_atR arc_e1'). 
        rewrite Iz in_fset2. case/orb_sum => /eqP ? ; first exact: W.
        subst e1'. rewrite -> oarc_cnv in arc_e2, arc_e1. 
        case: (W _ _ _ _ _ _ _ arc_e2 arc_e1); rewrite // 1?eq_sym 1?fsetUC //.
        move => Gl [Gr] [[Sl Sr] E]. e2split; [ | exact: Sr|exact: E].
        rewrite->maxnC, flip_step; eauto with vset.
        by rewrite !cnvdot cnvtst dotA. }
      subst e1'. 
      have /eqP ? : e2' == e2; [|subst e2'].
      { move:(oarc_edge_atR arc_e2'). by rewrite Iz in_fset2 eq_sym (negbTE e1De2'). }
      have ? := oarc_injL arc_e1 arc_e1'. subst x'.
      rewrite -> oarc_cnv in arc_e2. have ? := (oarc_injL arc_e2 arc_e2'); subst y.
      have Eu : u ≡ u' by apply: oarc_eqv arc_e1 arc_e1'.
      have Ev : v° ≡ v' by apply: oarc_eqv arc_e2 arc_e2'.
      move => {arc_e1 arc_e1' arc_e2 arc_e2' yDz e1De2'}.
      e2split.
      * eapply ostep_step,ostep_e0. apply: oarc_added_edge.
      * eapply ostep_step,ostep_v1. 3: apply: oarc_added_edge. 
        all: try done. 
        by rewrite edges_at_add_edge ?edges_at_remove_edges -Iz ?fsetDv ?fsetU0 //= Iz maxn_fsetD.
      * rewrite /= !updateE.
        rewrite -remove_vertex_add_test add_edgeKr /= ?maxn_fsetD //.
        rewrite add_edge_remove_edgesK ?inE ?eqxx // remove_vertex_edges. 
        rewrite !remove_edges_vertexK ?fsubUset ?fsub1set ?Iz ?in_fset2 ?eqxx ?maxn_eq //.
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
        3:{ apply: oarc_add_edge. 2:exact: oarc_remove_vertex arc_e2'. 
            apply: fset2_maxn_neq. by rewrite -Iz. }
        2:{ apply: oarc_add_edge. 2:exact: oarc_remove_vertex arc_e1'. 
            apply: fset2_maxn_neq. by rewrite -Iz. } 
        done.
      * eapply ostep_step,ostep_v2. 
        7: { apply: oarc_add_edge. 2:exact: oarc_remove_edges arc_e2. 
             exact: fset2_maxn_neq. }
        6: { apply: oarc_add_edge. 2: exact: oarc_remove_edges arc_e1. 
             exact: fset2_maxn_neq. }
        all: try done.
        rewrite edges_at_add_edge' //= ?maxn_fsetD // edges_at_remove_edges. 
        by rewrite -fsetDDl !mem_fsetD1.
      * rewrite /=. 
        rewrite -remove_vertex_add_edge ?[z == _]eq_sym //= ?maxn_fsetD //.
        rewrite remove_edges_vertex add_edge_edge //.
        rewrite add_edge_remove_edges //. exact: mem_maxn.
  - (* E0 / E0 *)
    case: (altP (e =P e')) => [?|xDx']; first subst e'.
    + (* same loop *)
      have ? : x' = x by case: (same_oarc arc_e arc_e') => [[? ? ?]|[? ? ?]]; subst.
      subst. exact: close_same_step. 
    + (* two independent loops *)
      e2split.
      * eapply ostep_step,ostep_e0. apply: oarc_remove_edges arc_e'. by rewrite inE eq_sym.
      * eapply ostep_step,ostep_e0. apply: oarc_remove_edges arc_e. by rewrite inE.
      * rewrite /=. by rewrite -!remove_edges_add_test add_testC !remove_edges_edges fsetUC.
  - (* E0 / E2 *) 
    case: (boolP (e \in [fset e1'; e2'])) => He.
    + (* parallel loops *)
      wlog ? : e1' e2' u' v' x' y' arc_e1' arc_e2' e1De2' {He} / e = e1'.
      { move => W. move: He. rewrite in_fset2. case/orb_sum => /eqP E; first exact: W.
        case: (W _ _ _ _ _ _ arc_e2' arc_e1' _ E); rewrite 1?eq_sym //.
        move => Gl [Gr] [[Sl Sr] Elr]. e2split; [exact: Sl | | exact: Elr].
        by rewrite fsetUC maxnC parC. }
      subst e1'. move: (oarc_loop arc_e1' arc_e) => ?. subst y'.
      have ? : x' = x by case: (same_oarc arc_e arc_e1') => [] [? ? ?]; congruence.
      subst x'. 
      e2split. 
      * eapply ostep_step,ostep_e0. apply: oarc_remove_edges arc_e2'.
        by rewrite inE eq_sym.
      * eapply ostep_step,ostep_e0. apply: oarc_added_edge. 
      * rewrite /= !updateE. 
        rewrite -remove_edges_add_test remove_edges_edges add_edge_remove_edgesK ?inE ?eqxx //.
        rewrite remove_edges_edges [[fset _ ; _ ; _]]fsetUC [maxn _ _ |` _]mem_fset1U ?maxn_fset2 //.
        rewrite add_test_merge. apply: add_test_morphism => //.
        rewrite infer_testE /= (oarcxx_le arc_e1') (oarcxx_le arc_e2').
        by rewrite critical_pair2.
    + (* independent case *)
      set e' := maxn _ _. 
      have eDe' : e != e' by rewrite fset2_maxn_neq .
      e2split. 
      * eapply ostep_step,ostep_e2; [exact: e1De2'| |].
        -- apply: oarc_remove_edges arc_e1'. apply: contraNN He. by rewrite !inE eq_sym => ->.
        -- apply: oarc_remove_edges arc_e2'. apply: contraNN He. by rewrite !inE eq_sym => ->.
      * eapply ostep_step,ostep_e0. apply: oarc_add_edge eDe' _. exact: oarc_remove_edges arc_e.
      * rewrite /= -/e' updateE //. 
        rewrite -remove_edges_add_test add_edge_remove_edges ?remove_edges_edges ?inE 1?eq_sym //.
        by rewrite fsetUC -add_test_edge.
  - (* E2 / E2 *)
    case: (fset2_cases e1De2 e1De2') => [[E|D]|[e He]].
    + (* fully overlapping instances *)
      wlog [? ?] : e1' e2' u' v' e1De2' arc_e1' arc_e2' {E} / e1 = e1' /\ e2 = e2'.
      { move => W. case: (fset2_inv e1De2 E) => [|[? ?]]; first exact: W.
        subst e2' e1'. rewrite [[fset e2;e1]]fsetUC [maxn e2 e1]maxnC. 
        case: (W _ _ _ _ _ arc_e2' arc_e1') => // Gl [Gr] [[Sl Sr] EG].
        e2split; [exact: Sl| |exact: EG]. 
        by rewrite parC. }
      subst e1' e2'. 
      wlog [? ? Hu] : x' y' u' v' {arc_e1'} arc_e2' / [/\ x = x', y = y' & u ≡ u'].
      { move => W. 
        case: (same_oarc arc_e1 arc_e1') => [|[? ? Hu]]; first exact: W.
        subst x' y'. rewrite -> oarc_cnv in arc_e2'. case: (W _ _ u'° _ arc_e2') => //.
        move => Gl [Gr] [[Sl Sr] EG]. 
        e2split; [exact: Sl| |exact: EG]. 
        rewrite-> flip_step; eauto with vset. by rewrite cnvpar. }
      subst x' y'. 
      (* There are actually two cases here *)
      have [Hv|[? Hv]]: ((v ≡ v') \/ (x = y /\ v ≡ v'°)).
      { case: (same_oarc arc_e2 arc_e2'); firstorder. }
      * apply close_same_step. 1-2: apply: add_edge_graph'; eauto with vset.
        by rewrite Hu Hv.
      * subst y. e2split. 
        -- eapply ostep_step,ostep_e0. apply: oarc_added_edge.
        -- eapply ostep_step,ostep_e0. apply: oarc_added_edge.
        -- rewrite /= !updateE !add_edge_remove_edgesK ?in_fset1 ?eqxx //.
           apply: add_test_morphism => //. rewrite infer_testE Hu Hv.
           by rewrite parA par1tst par_tst_cnv parA.
    + (* independent instances *)
      move: (fdisjointP D) => D1. rewrite fdisjoint_sym in D. move: (fdisjointP D) => {D} D2.
      e2split. 
      * apply ostep_step,ostep_e2. 
        -- exact: e1De2'.
        -- apply: oarc_add_edge. 
           ++ apply: fset2_maxn_neq. by rewrite D2 // in_fset2 eqxx.
           ++ apply: oarc_remove_edges arc_e1'. by rewrite D2 // !inE eqxx.
        -- apply: oarc_add_edge. 
           ++ apply: fset2_maxn_neq. by rewrite D2 // in_fset2 eqxx.
           ++ apply: oarc_remove_edges arc_e2'. by rewrite D2 // !inE eqxx.
      * apply ostep_step,ostep_e2. 
        -- exact: e1De2.
        -- apply: oarc_add_edge. 
           ++ apply: fset2_maxn_neq. by rewrite D1 // in_fset2 eqxx.
           ++ apply: oarc_remove_edges arc_e1. by rewrite D1 // !inE eqxx.
        -- apply: oarc_add_edge. 
           ++ apply: fset2_maxn_neq. by rewrite D1 // !inE eqxx.
           ++ apply: oarc_remove_edges arc_e2. by rewrite D1 // !inE eqxx.
      * rewrite !add_edge_remove_edges ?D1 ?D2 ?maxn_fset2 //.
        rewrite !remove_edges_edges fsetUC add_edge_edge //. 
        case: maxnP => _; by rewrite fset2_maxn_neq // ?D1 ?D2 // !inE eqxx.
    + (* associativity case *)
      wlog ? : e1 e2 x y u v  arc_e1 arc_e2 e1De2 He / e = e2 ; [move => W|subst e]. 
      { have: e \in [fset e1;e2]. { move/fsetP : He => /(_ e). rewrite in_fset1 eqxx. by case/fsetIP. }
        rewrite inE. case/orb_sum => /fset1P => E; last exact: W.
        rewrite -> oarc_cnv in arc_e1,arc_e2. 
        move/(_ _ _ _ _ _ _ arc_e2 arc_e1) in W. rewrite fsetUC eq_sym in W.
        case: W => // Gl [Gr] [[S1 S2] WG]. exists Gl. exists Gr. do 2 (split => //). 
        rewrite-> maxnC, flip_step; eauto with vset.
        by rewrite !cnvpar parC. }
      wlog ? : e1' e2' x' y' u' v'  arc_e1' arc_e2' e1De2' He / e2 = e1' ; [move => W|subst e1'].
      { have: e2 \in [fset e1';e2']. { move/fsetP : He => /(_ e2). rewrite in_fset1 eqxx. by case/fsetIP. }
        rewrite inE. case/orb_sum => /fset1P => E; first exact: W.
        rewrite -> oarc_cnv in arc_e1',arc_e2'. 
        move/(_ _ _ _ _ _ _ arc_e2' arc_e1') in W. rewrite eq_sym [[fset e2';_]]fsetUC in W.
        case: W => // Gl [Gr] [[S1 S2] WG]. exists Gl. exists Gr. do 2 (split => //).
        rewrite-> maxnC, flip_step; eauto with vset.
        by rewrite !cnvpar parC. }
      have {He} E1 : e1 != e2'.
      { apply: contraNneq e1De2 => E. by rewrite -in_fset1 -He !inE E !eqxx. }
      (* until here, the reasoning is essentially the same as in the V2/V2 assoc. case *)
      wlog [? ? Hu] : x' y' u' v' {arc_e1'} arc_e2' / [/\ x' = x, y' = y & u' ≡ v].
      { move => W. case: (same_oarc arc_e1' arc_e2) => [|[? ? E]]; first exact: W.
        rewrite -> oarc_cnv in arc_e2'. subst x' y'.  
        case: (W _ _ u'° _ arc_e2'). split => //. by rewrite E cnvI.
        move => Gl [Gr] [[Sl Sr] EG]. e2split; [exact: Sl| |exact: EG].
        rewrite->flip_step; eauto with vset.
        by rewrite !cnvpar. }
      subst.
      have He2' : e2' \notin [fset e1; e2] by rewrite !inE negb_or ![e2' == _]eq_sym E1 e1De2'.
      have He1 : e1 \notin [fset e2; e2'] by rewrite !inE negb_or e1De2. 
      e2split.
      * eapply ostep_step,ostep_e2. 
        2: exact: oarc_added_edge.
        2: { apply: oarc_add_edge. 2:exact: oarc_remove_edges arc_e2'.
             exact: fset2_maxn_neq. }
        by case: maxnP.
      * eapply ostep_step,ostep_e2.
        3: exact: oarc_added_edge.
        2: { apply: oarc_add_edge. 2: exact: oarc_remove_edges arc_e1. 
             exact: fset2_maxn_neq. }
        by case: maxnP.
      * rewrite maxnA. set f := maxn (maxn _ _) _. 
        rewrite !add_edge_remove_edgesK ?inE ?eqxx // !remove_edges_edges. 
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
  - move => F G FG H. by eauto using eqvG_graph.
  - move => F G FG H. destruct FG. eauto using add_edge_graph''. 
  - move => F G FG isF. apply: ostep_graph FG.
  - move => F G H. tauto.
Qed.

Proposition local_confluence (F G1 G2 : pre_graph) (isF : is_graph F) : 
  ostep F G1 -> ostep F G2 -> exists H, osteps G1 H /\ osteps G2 H.
Proof.
  move => S1 S2.
  move: (local_confluence_aux isF S1 S2) => [H1] [H2] [[S1' S2'] I].
  exists H2. split => //. by rewrite-> S1', I. 
Qed.


End PttdomGraphTheory.
Notation "G ≡G H" := (eqvG G H) (at level 79).
Notation "G \ x" := (remove_vertex G x) (at level 29,left associativity) : open_scope.
Notation "G  ∔  [ x , a ]" := (add_vertex G x a) (at level 20,left associativity) : open_scope.
Notation "G - E" := (remove_edges G E) : open_scope.
Notation "G ∔ [ x , u , y ]" := (add_edge G x u y) (at level 20,left associativity) : open_scope.
Notation "G ∔ [ e , x , u , y ]" := (add_edge' G e x u y) (at level 20,left associativity) : open_scope.
Notation "G [adt x <- a ]" := (add_test G x a) 
   (at level 2, left associativity, format "G [adt  x  <-  a ]") : open_scope.

Hint Resolve in_vsetDV in_vsetDE in_vsetAV in_vsetAE in_vsetAV' : vset.
Hint Resolve is_edge_vsetL is_edge_vsetR oarc_vsetL oarc_vsetR : vset.
Hint Resolve osteps_refl : core.
