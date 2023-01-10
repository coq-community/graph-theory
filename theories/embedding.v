From mathcomp Require Import all_ssreflect.
From fourcolor Require Import hypermap geometry color coloring walkup combinatorial4ct cfmap.
Require Import edone preliminaries bij digraph sgraph connectivity minor hmap_ops smerge hcycle arc.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Lemma predIT (T : eqType) (A B : pred T) : B =1 predT -> predI A B =i A.
Proof. move => BT x. by rewrite !inE BT /= andbT. Qed.
Arguments predIT [T A B].

Lemma plain_face (D : hypermap) (x : D) :
  plain D -> face x = finv node (edge x).
Proof. by move=> plainD; rewrite -plain_eq' // finv_f. Qed.

(** * Hypermaps as Embeddings of (planar) Grahps *)

(** This is mainly usedful when takling about embeddings, as hypermaps
cannot represent isolated vertices. *)
Definition no_isolated (G : sgraph) := forall x : G, exists y : G, x -- y.

Lemma add_edge_no_isolated (G : sgraph) (x y : G) :
  no_isolated G -> no_isolated (add_edge x y).
Proof.
by move => no_isoG u; have [v uv] := no_isoG u; exists v; rewrite /edge_rel/= uv.
Qed.

(** In this file we define what it means for a hypermap to represent a simple graph. *)

Record embedding (G : sgraph) (D : hypermap) (f : D -> G) := 
  Embedding { 
      emb_plain : plain D;
      emb_surj x : x \in codom f;
      emb_vertex d1 d2 : cnode d1 d2 = (f d1 == f d2);
      emb_edge d1 d2 : adjn d1 d2 = f d1 -- f d2
    }.

(** Recall that the darts of a plain hypermap represent
"half-edges". In particular, every node cycle of [D] lists the
incident half edges. Thus, [emb_surj] entails that there are no
embeddings for graphs with isolated vertices. One could imagine
relaxing [emb_inj] exclude isolated vertices, but this would
conidertably complicate transferring results between a graph and its
embedding. Moreover, isolated vertices are ol little concern in the
study of planar graps. *)

(** Also note that we do *not* require that there be at most one edge
in the embedding representing a given edge in [G]. The reason for this
is two-fold: (1) redundant parrallel edges can easily be removed when
this is relevant; (2) this means that there are fewer properties to
be preserved by constructions on hypermaps, in particular when glueing
together hypermaps along "marker" edges. *)

Section Embedding.
Variables (G : sgraph) (D : hypermap) (f : D -> G) (emb_f : embedding f).

Lemma emb_vertexP d1 d2 : reflect (f d1 = f d2) (cnode d1 d2).
Proof. rewrite (emb_vertex emb_f). exact:eqP. Qed.

Definition emb_inv (x : G) : D := iinv (emb_surj emb_f x).

Lemma emb_invK : cancel emb_inv f. 
Proof. by move => z; rewrite f_iinv. Qed.

Lemma emb_inv_inj : injective emb_inv.
Proof. exact/can_inj/emb_invK. Qed.

Lemma adjn_irrefl : irreflexive (@adjn D).
Proof. move => x. by rewrite (emb_edge emb_f) sgP. Qed.

Lemma adjn_face (x : D) : adjn x (face x).
Proof.
apply/exists_inP; exists x; first exact: connect0.
rewrite in_applicative -plain_eq' -?cnode1r ?connect0 //.
exact: emb_plain emb_f.
Qed.

Lemma emb_loopless : loopless D. 
Proof. 
  apply/existsPn => x. apply: contraNN (negbT (adjn_irrefl x)) => H.
  apply/exists_inP; exists x => //. exact: connect0.
Qed.

Lemma emb_roots_inj : {in froots node &, injective f}.
Proof.
  move => x y root_x root_y /eqP. rewrite -emb_vertex //.
  move => /rootP - /(_ cnodeC). by rewrite (eqP root_x) (eqP root_y).
Qed.

Lemma emb_roots_bij : {in froots node, bijective f}.
Proof. 
  exists (froot node \o (emb_inv)). 
  - move => x /= /eqP {2}<-; apply/rootP; first exact cnodeC. 
    by rewrite (emb_vertex emb_f) f_iinv.
  - move => x /= _. rewrite -{2}[x]emb_invK. apply/emb_vertexP. 
    by rewrite cnodeC connect_root.
Qed.

Lemma emb_ncard : fcard node D = #|G|.
Proof. 
  rewrite /n_comp_mem /predI (eq_card (predIT _)) //=.
  apply/eqP; rewrite eqn_leq -{1}(card_in_imset emb_roots_inj) max_card /=.
  pose g := froot node \o (emb_inv).
  have inj_g : injective g. 
  { apply: (@can_inj _ _ _ f) => x. rewrite /g/=. 
    rewrite -{2}[x]emb_invK. apply/emb_vertexP. 
    by rewrite cnodeC connect_root. }
  rewrite -(card_imset _ inj_g) subset_leq_card //.
  apply/subsetP => ? /imsetP [x _ ->]. rewrite /g/=. 
  apply/eqP. apply: root_root. exact: cnodeC.
Qed.

Lemma cnode_lpath (x y : D) : 
  cnode x y -> exists p, [/\ path clink x p, last x p = y & {subset p <= cnode x}].
Proof.
rewrite -same_fconnect_finv // => /connectP [p pth_p lst_p]; exists p; split => //.
  by apply: sub_path pth_p; apply: subrelUl. 
by apply: closed_path_sub pth_p => //= z1 z2 /eqP<- ?; rewrite cnode1r f_finv.
Qed.

Lemma adj_lpath (x y : D) : plain D -> adjn x y -> 
  exists p, [/\ path clink x p, last x p = y & {subset p <= [predU cnode x & cnode y]}].
Proof.
move => plainD /exists_inP [z Z1 Z2]; rewrite inE in Z1. 
rewrite inE cnodeC -[edge z](f_finv nodeI) -cnode1 in Z2.
have [p [P1 P2 P3]] := cnode_lpath Z1; have [q [Q1 Q2 Q3]] := cnode_lpath Z2.
exists (p ++ finv node (edge z) :: q); split.
- by rewrite cat_path P1 P2 /= Q1 andbT -plain_eq' // finv_f ?clinkF.
- by rewrite last_cat.
- move => v. rewrite mem_cat !inE !app_predE => /or3P [/P3 ->//|/eqP->|/Q3 H].
  + by rewrite !inE [cnode y _]cnodeC Z2.
  + rewrite !inE in H *. by rewrite [cnode y v](connect_trans _ H) // cnodeC.
Qed.

Lemma edge_clink (x y : G) : x -- y ->
  exists p, [/\ path clink (emb_inv x) p, last (emb_inv x) p = (emb_inv y) & 
          {subset [set f z | z in p] <= [set x;y]}].
Proof.
rewrite -{1}[x]emb_invK -{1}[y]emb_invK -emb_edge //.
move/adj_lpath => /(_ (emb_plain emb_f)) [p [P1 P2 P3]].
exists p; split => // v /imsetP [z /P3 Hz] -> {v}; move: Hz.
by rewrite !inE !(emb_vertex emb_f) !f_iinv ![f _ == _]eq_sym.
Qed.

Lemma emb_path x y (p : Path x y) :
  exists (q : seq D), 
    [/\ path clink (emb_inv x) q, f (last (emb_inv x) q) = y & {in q, forall z, f z \in p}].
Proof.
have plainD := emb_plain emb_f.
elim/Path_ind : p => {x} => [|x z p xz [r [R1 R2 R3]]].
  by exists nil; split => //=; rewrite ?emb_invK. 
have [q [Q1 Q2 Q3]] := edge_clink xz.
exists (q++r); rewrite cat_path last_cat !Q1 Q2 R1 R2; split => // v.
rewrite !inE mem_cat => /orP [Hv|/R3->//].
by rewrite mem_edgep -in_set2 Q3 // imset_f.
Qed.

Lemma emb_path_f (x y : D) (p : Path (f x) (f y)) : 
  exists q, [/\ path clink x q, last x q = y & {in q, forall z, f z \in p}].
Proof.
have [q [Q1 /emb_vertexP Q2 Q3]] := emb_path p.
have Nx: cnode x (emb_inv (f x)) by rewrite (emb_vertex emb_f) emb_invK.
have [q1 [Q11 Q12 Q13]] := cnode_lpath Nx.
have [q2 [Q21 Q22 Q23]] := cnode_lpath Q2.
exists (q1 ++ q ++ q2); rewrite !cat_path !last_cat Q11 Q12 Q1 Q21 Q22.
split => // z; rewrite !mem_cat => /or3P[/Q13||/Q23]; try exact: Q3.
- by move/emb_vertexP<-.
- move/emb_vertexP<-. by rewrite (emb_vertexP _ _ Q2).
Qed.

(** This could be generalized to [k.+1.-connected] graphs allowing to
avoid up to [k] node nycles in [D]. The lemma proved here is
sufficient for our purposes, which is prove that the faces of
(embedded) 2-connected graphs are bounded by cycles. *)
Lemma two_connected_avoid_one : 2.-connected G -> avoid_one D.
Proof.
case => cardG sepG z x y cNzx cNzy.
have sepN : ~ vseparator [set f z] by move/sepG; rewrite cards1.
gen have N1,_ : x cNzx / f x \notin [set f z].
  by rewrite inE -emb_vertex // cnodeC.
have [p Ip av_p] := avoid_nonseperator sepN (N1 _ cNzx) (N1 _ cNzy).
rewrite disjoint_sym disjoints1 in av_p.
suff : connect (restrict [set v | f v \in p] clink) x y.
{ apply/connect_restrict_mono/subsetP => v; rewrite !inE.
  by apply: contraTN; rewrite (emb_vertex emb_f) => /eqP <-. }
have [q [Q1 Q2 Q3]] := emb_path_f p.
apply/connectP; exists q; last by rewrite Q2. 
apply: path_rpath => //; first by rewrite inE. 
move => z' /Q3; by rewrite inE.
Qed.


Lemma emb_inv_node d : cnode d (emb_inv (f d)).
Proof. by rewrite (emb_vertex (emb_f)) emb_invK. Qed.

Lemma emb_degree d : #|N(f d)| <= order node d.
Proof.
set x := f d.
have Nxd z : z \in N(x) -> exists ez, cnode (emb_inv z) (edge ez) && cnode (emb_inv x) ez.
{ rewrite in_opn -{1}[x]emb_invK -{1}[z]emb_invK -emb_edge /adjn //.
  case/exists_inP => dz; rewrite !inE. exists dz; apply/andP => //. }
pose h (z:G) := if @idP (z \in N(x)) is ReflectT zx then xchoose (Nxd _ zx) else d.
have I : {in N(x)&, injective h}. 
{ move => u v. rewrite /h. 
  case: {1}_ / idP => // ux _. case: {1}_ / idP => // vx _. 
  case: xchooseP' => du. case: xchooseP' => dv. 
  move=> /andP [C1 _] /andP[C2 _] E; subst dv; apply/eqP.
  rewrite -[u]emb_invK -[v]emb_invK -emb_vertex //.
  by apply: connect_trans C2 _; rewrite cnodeC. }
rewrite -(card_in_imset I).
apply/subset_leq_card/subsetP => dz /imsetP [z xz ->] {dz}.
rewrite /h; case: {-}_ / idP => [p|]; last by rewrite xz.
case: xchooseP' => dz /andP [_ D2]. exact: connect_trans (emb_inv_node _) _.
Qed.

Lemma emb_gcomp x y : gcomp x y = connect (--) (f x) (f y).
Proof.
have ? : plain D by apply: emb_plain emb_f.
rewrite -clink_glink; apply/idP/idP; move/connectP => [p].
- move=> pth_p ->; elim: p x pth_p => //= z p IHp x /andP [xz {}/IHp].
  apply: connect_trans; have [/eqP<-|/eqP<-] := orP xz.
  + by apply/eq_connect0/eqP; rewrite -emb_vertex // cnode1r f_finv.
  + by apply: connect1; rewrite -emb_edge //= adjn_face.  
- move => pth_p lst_p; have q := Path_of_path pth_p; rewrite -lst_p in q.
  by have [r [pth_r lst_r _]] := emb_path_f q; apply/connectP; exists r.
Qed.

Lemma emb_n_comp : n_comp glink D = n_comp (--) G.
Proof.
symmetry; have eq_D : D =1 [preim f of G] by [].
rewrite (eq_n_comp_r eq_D).
apply: adjunction_n_comp => //;[exact: sconnect_sym|exact: glinkC|].
split => [x _|x' y' _]; last exact: emb_gcomp.
by exists (emb_inv x); rewrite f_iinv connect0.
Qed.

Lemma hiso_embed (E : hypermap) (i : hiso E D) : 
  embedding f -> embedding (f \o i).
Proof.
case => E1 E2 E3 E4. split. 
- by rewrite (hiso_plain i).
- move => x; case/mapP : (E2 x) => x0 _ ->. by rewrite -[x0](bijK' i) codom_f.
- move => x y /=. by rewrite (hiso_cnode i).
- move => x y /=. by rewrite -E4 hiso_adjn.
Qed.

Lemma emb_fcycle_cycle p : fcycle face p -> cycle (--) [seq f z | z <- p].
Proof. 
case: p => //= x p; rewrite -map_rcons; apply: homo_path => {x} x y /eqP<-.
by rewrite -emb_edge // adjn_face.
Qed.

Lemma emb_face_cycle (x : D) : cycle (--) [seq f z | z <- orbit face x].
Proof. exact/emb_fcycle_cycle/cycle_orbit/faceI. Qed.

(** The remaining properties assume that there are no redundant parallel edges *)
Hypothesis simpleD : simple_hmap D.

Lemma emb_ecard : fcard edge D = #|E(G)|.
Proof.
have ? : plain D by apply: emb_plain emb_f.
rewrite /n_comp_mem (eq_card (predIT _)) //.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- pose h (x : D) := [set f x; f (edge x)].
  have h_inj :  {in froots edge &, injective h}. 
  { move=> x y root_x root_y. apply: contra_eq => xDy. 
    have : ~~ cedge x y. 
    rewrite -root_connect ?(eqP root_x) ?(eqP root_y) //. 
    exact: fconnect_sym.
    apply: contraNneq; rewrite /h doubleton_eq_iff !(rwP eqP) -!emb_vertex //.
    case => [[?]|[]]; first by rewrite (negPf (simpleD _ _)).
    have [->|xDey] := eqVneq x (edge y); first by rewrite -cedge1.
    by move/(simpleD xDey)/negPf; rewrite plain_eq // => ->. }
  rewrite -(card_in_imset h_inj); apply: subset_leq_card.
  apply/subsetP => z /imsetP [x _ ->].
  by rewrite in_edges -emb_edge ?adjn_edge.
- have [e0 /edgesP [x0 _]|->] := picksP E(G); last by rewrite cards0.
  pose d0 := emb_inv x0.
  have link x y : x -- y -> { d : D | f d = x & f (edge d) = y }. 
  { rewrite -[x]emb_invK -[y]emb_invK -emb_edge // => /existsP ex_d.
    exists (xchoose ex_d); apply/eqP; case/andP : (xchooseP ex_d) => ? ?.
    all: by rewrite -emb_vertex // cnodeC. }
  pose g (e : {set G}) : D := 
    if edgeP e is Edge x y xy _ then froot edge (s2val (link x y xy)) else d0.
  have g_inj : {in E(G)&, injective g}.
  { move=> e1 e2 E1 E2; rewrite /g.
    case: (edgeP e1) => [x y xy ->|]; last by rewrite {1}E1.
    case: (edgeP e2) => [u v uv ->|]; last by rewrite {1}E2.
    case: (link x y xy) => d1 /= f_d1 f_ed1.
    case: (link u v uv) => d2 /= f_d2 f_ed2. 
    move/eqP; rewrite root_connect; last exact: fconnect_sym.
    rewrite plain_orbit // !inE => /pred2P [?|?]; subst => //.
    by rewrite plain_eq // setUC. }
  rewrite -(card_in_imset g_inj); apply: subset_leq_card.
  apply/subsetP => z /imsetP [x E ->]; rewrite inE /g. 
  case: edgeP => [*|] ; rewrite ?E ?roots_root //. exact: fconnect_sym.
Qed.

Lemma card_emb : #|D| = #|E(G)|.*2.
Proof.
by rewrite -emb_ecard -muln2 fcard_order_set //; exact: emb_plain emb_f.
Qed.

(** it would be sufficient to assume that the vertices involved in the
face have arity 3 *)
Lemma emb_arity3 (x : D) : (forall y, 1 < #|N(f y)|) -> 2 < arity x.
Proof.
move => deg2.
apply: arity3 => //;[exact: emb_plain emb_f|exact: emb_loopless|].
move=> {x} x. apply: contraTF (deg2 x); rewrite -leqNgt => /eqP nxx.
apply: leq_trans (emb_degree _) _. exact: order_le_fix.
Qed.

End Embedding.


Lemma homo_cycle (aT rT : Type) (f : aT -> rT) (e1 : rel aT) (e2 : rel rT) (s : seq aT) :
  {homo f : x y / e1 x y >-> e2 x y} -> cycle e1 s -> cycle e2 (map f s).
Proof. 
case: s => //= a s hom_f; rewrite !rcons_path => /andP [pth_s /hom_f lst_s].
by rewrite (homo_path hom_f pth_s) last_map.
Qed.

(** ** Packaged plane embeddings *)

Record plane_embedding (G : sgraph) :=
  { emb_map : hypermap;
    emb_fun :> emb_map -> G;
    emb_embedding : embedding emb_fun;
    emb_planar : planar emb_map }.

#[export] Hint Resolve emb_embedding emb_planar : core.

Section PlaneEmbedding.
Variables (G : sgraph) (g : plane_embedding G).
Implicit Types (x y : G) (d : emb_map g).

Lemma plane_emb_plain : plain (emb_map g).
Proof. exact: emb_plain. Qed.

Lemma plane_emb_loopless : loopless (emb_map g).
Proof. exact: emb_loopless. Qed.

Lemma plane_emb_surj : forall x, x \in codom g.
Proof. exact: emb_surj. Qed.

Lemma plane_emb_vertex d1 d2 : cnode d1 d2 = (g d1 == g d2).
Proof. exact: emb_vertex. Qed.

Lemma plane_emb_edge d1 d2 : adjn d1 d2 = g d1 -- g d2.
Proof. exact: emb_edge. Qed.

Definition pinv := emb_inv (emb_embedding g).
Lemma pinvK : cancel pinv g.
Proof. exact: emb_invK. Qed.

End PlaneEmbedding.

(** In this section we define faces on plane graphs (i.e, simple
graphs [G] endowed with some plane embedding) and lift various
properties estblished on hypermaps. *)

Section Lifting.
Variables (G : sgraph) (g : plane_embedding G).
Implicit Types (s : seq G).

Let gedge := @edge (emb_map g).
Let gnode := @node (emb_map g).
Let gface := @face (emb_map g).

Notation "(--)" := (fun x y => x -- y).

Definition sface s := exists d : emb_map g, s = map g (orbit gface d).

Lemma sface_cyle s : sface s -> cycle (--) s.
Proof. 
case => d ->. apply: homo_cycle (cycle_orbit faceI _).
move => x y /=. rewrite -emb_edge // => /eqP <-. exact: adjn_face.
Qed.

Proposition face_uniq (s : seq G) : 2.-connected G -> sface s -> uniq s.
Proof.
move => tcG; have := @two_connected_cyle (emb_map g).
case/(_ _ _ _ _ )/Wrap; auto using plane_emb_plain, plane_emb_loopless.
- exact/(two_connected_avoid_one (emb_embedding g)).
- move=> Hg [x ->]; rewrite map_inj_in_uniq ?orbit_uniq //.
  move => u v; rewrite -!fconnect_orbit => Hu Hv. 
  apply: contra_eq => uDv; rewrite -plane_emb_vertex.
  apply: Hg uDv _. apply: connect_trans Hv. 
  by rewrite cfaceC.
Qed.  

Lemma rot_orbit (T : finType) (f : T -> T) x n (injf : injective f) :
  n < order f x -> rot n (orbit f x) = orbit f (iter n f x).
Proof.
move=> n_lt_ordx. 
rewrite [RHS](orbitE (cycle_orbit injf x)) -/(findex f _ _) ?findex_iter //.
by rewrite -fconnect_orbit fconnect_iter.
Qed.

Lemma rot_face n (s : seq G) : sface s -> sface (rot n s).
Proof.
have [n_lt_s face_s|?] := ltnP n (size s); last by rewrite rot_oversize.
case: face_s n n_lt_s => x -> n; rewrite size_map size_orbit => n_lt_o.
rewrite -map_rot rot_orbit; [by eexists|exact: faceI|done].
Qed.

Lemma rotr_face n (s : seq G) : sface s -> sface (rotr n s). 
Proof. exact: rot_face. Qed.


(** Always holds, [2 < arity x] can be obtained by removing parallel edges] *)
Lemma plane_emb_arity2 (d : emb_map g) : 1 < arity d.
Proof.
apply: loopless_arity. apply: plane_emb_plain. apply: plane_emb_loopless. 
Qed.

Lemma plane_emb_face x y : x -- y -> exists s, sface (x::y::s).
Proof.
have [dx /esym g_dx] := codomP (plane_emb_surj g x).
have [dy /esym g_dy] := codomP (plane_emb_surj g y).
rewrite -{1}g_dx -{1}g_dy -plane_emb_edge => /exists_inP [z]; rewrite !inE.
rewrite plane_emb_vertex => /eqP dx_z dx_ez.
set v := finv node (edge z).
have fz : face z = v. 
{ rewrite /v -plain_eq' ?finv_f //. exact: plane_emb_plain. }
exists (drop 2 (map g (orbit face z))), z ; rewrite /sface.
have X : 1 < arity z by apply plane_emb_arity2.
rewrite [in RHS](orbit_prefix X) /= map_drop; congr (_ :: _ :: _).
- by rewrite -g_dx.
- by apply/eqP; rewrite -g_dy fz /v -plane_emb_vertex cnode1r f_finv.
Qed.

End Lifting.

Prenex Implicits Icp.

(** ** Constructions on Plane Embeddings *)

(** Union *)

Lemma union_plane_embedding (G H : sgraph) : 
  plane_embedding G -> plane_embedding H -> plane_embedding (G ∔ H).
Proof.
move=> g h; pose D := (emb_map g ∔ emb_map h)%H.
pose g' : D -> (G ∔ H)%sg := sumf g h.
have emb_g' : embedding g'. 
{ split.
  - have ? := plane_emb_plain g; have ? := plane_emb_plain h.
    apply/plainP => -[x|x] _ /=; rewrite inj_eq ?plain_eq ?plain_neq //.
    exact: inl_inj. exact: inr_inj.
  - move=> [y|y]; apply/codomP. 
    + by have/codomP [x ->] := plane_emb_surj g y; exists (inl x).
    + by have/codomP [x ->] := plane_emb_surj h y; exists (inr x).
  - move => [x|x] [y|y].
    all: rewrite /= fconnect_sumf // ?(inj_eq inl_inj) ?(inj_eq inr_inj).
    all: exact/emb_vertex/emb_embedding.
  - move => [x|x] [y|y]; rewrite union_adjn //= /edge_rel/=.
    all: exact: plane_emb_edge.
 }
have : planar D by apply/union_planar; split; exact: emb_planar.
exact: Build_plane_embedding emb_g'.
Qed.

(** Adding a new node linked to another node *)

Lemma plane_add_node1 (G : sgraph) (g : plane_embedding G) (x : G) s : 
  sface g (x::s) -> 
  exists g' : plane_embedding (add_node G [set x]), 
    sface g' [:: Some x, None, Some x & map Some s].
Proof.
pose D := emb_map g.
case => z forbit_z. 
set G' := add_node G [set x].
pose D' := h_add_node z.
pose g' (z' : D') : G' := match z' with
                         | IcpX => Some (g z)
                         | IcpXe => None
                         | Icp z' => Some (g z')
                         end.
have gz : g z = x.
{ by move: forbit_z; rewrite /orbit -orderSpred /=; case=> -> _. }
have [plain_D surj_g vertex_g edge_g] := emb_embedding g.
have plain_D' := add_node_plain z plain_D : plain D'.
have embedding_g' : embedding g'.
{ split.
  - by apply: add_node_plain (plane_emb_plain _).
  - move => [u|]; last by apply/codomP; exists IcpXe.
    by have [d _ ->] := mapP (surj_g u); apply/codomP; exists (Icp d).
  - have ? := @nodeI D'.
    move => [||d1] [||d2]; rewrite /= ?connect0 ?eqxx //=.
    all: rewrite ?[_ _ IcpXe](@cnodeC D') ?add_node_cnodeXe //.
    all: rewrite ?[_ _ IcpX](@cnodeC D') ?Some_eqE ?[_ IcpX _]same_fconnect1 //=.
    all: rewrite ?(@add_node_cnodeE) -?cnode1 // 1?cnodeC //.
  - have adjn_Icp := @add_node_adjn D z. 
    pose m (d : D') := match d with IcpX => 1 | IcpXe => 2 | _ => 0 end.
    move => d1 d2; wlog: d1 d2 / m d1 <= m d2 => [W|].
    { have [|/ltnW] := leqP (m d1) (m d2); first exact: W.
      rewrite sg_sym adjnC //. exact: W. }
    move: d1 d2 => [||d1] [||d2] // _ ; rewrite /= ?sg_irrefl. 
    all: rewrite /edge_rel/= ?inE ?eqxx ?[in g z == x]gz ?eqxx.
    + by rewrite adjn_node1 adjn_node1r /= adjn_Icp edge_g sg_irrefl.
    + exact: adjn_edge.
    + exact: add_node_adjnXeXe.
    + by rewrite adjn_node1r /= adjn_Icp -adjn_node1r.
    + by rewrite -gz -vertex_g adjnC // add_node_adjnXe cnodeC.
    + by rewrite adjn_Icp.
 }
have planar_D' : planar D' by rewrite add_node_planar; apply: emb_planar.
exists (Build_plane_embedding embedding_g' planar_D').
exists (IcpX) => /=.
rewrite add_node_face_orbitE /= gz -map_cons forbit_z; congr ([:: _ , _ & _]).
by rewrite -!map_comp; apply: eq_map.
Qed.

(** Adding an Edge across a face *)

Lemma face_preim (G : sgraph) (g : plane_embedding G) (x0 : emb_map g) (p := orbit face x0) x (s : seq G) :
  s = [seq g x | x <- p] -> x \in s -> exists2 d, d \in p & x = g d.
Proof. by move=> -> /mapP. Qed.

Lemma arcEmap (aT rT : eqType) (f : aT -> rT) (x y : aT) (p : seq aT) (s := [seq f x | x <- p]) :
  uniq s -> uniq p -> 
  x != y -> x \in p -> y \in p -> arc s (f x) (f y) = [seq f x | x <- arc p x y].
Proof.
move=> uniq_s uniq_p xDy x_p y_p. 
have [i p1 p2 arc1 arc2 rot_i] := rot_to_arc uniq_p x_p y_p xDy.
rewrite /s -(arc_rot i) ?map_f // -map_rot rot_i /= map_cat /= -arc1 left_arc //.
by move: uniq_s; rewrite /s -(rot_uniq i) -map_rot rot_i /= map_cat.
Qed.

Lemma orbit_case (T : finType) (f : T -> T) (x : T) : exists o, orbit f x = x :: o.
Proof. by rewrite /orbit -orderSpred /=; eexists. Qed.

Lemma plane_add_edge (G : sgraph) (g : plane_embedding G) (x y : G) (s1 s2 : seq G) : 
  let s := x :: s1 ++ y :: s2 in
  x != y -> sface g s -> 
  exists2 g' : plane_embedding (add_edge x y), 
    sface g' [:: y, x & s1] & sface g' [:: x,y & s2].
Proof.
move=> s xDy sface_xy.
case: sface_xy => dx E.
set o := orbit face dx in E.
pose dy := nth dx o (size s1).+1.
have lt_size_o : (size s1).+1 < size o.
{ by rewrite -[size o](size_map g) -E /s -cat_cons size_cat /= addnS addSn !ltnS leq_addr. }
have g_y : g dy = y. 
{ rewrite /dy -(nth_map _ x) -?E //.
  by rewrite /s -cat_cons nth_cat ltnn subnn. }
have g_x : g dx = x. 
{ by move: E; rewrite /o/orbit/s -orderSpred/=; case => -> _. }
have dxDdy : dx != dy. 
{ by apply: contra_neq xDy => dxy; rewrite -g_x dxy g_y. }
have dx_dy : cface dx dy by rewrite fconnect_orbit mem_nth //.
set D := emb_map g in dx o E dy g_x lt_size_o g_y dxDdy dx_dy .
pose D' := h_add_edge dxDdy. 
pose g' (d : D') : add_edge x y :=
  match d with IcpX => x | IcpXe => y | Icp z => g z end.
have [plain_D surj_g vertex_g edge_g] := emb_embedding g.
have plain_D' : plain D' by apply: add_edge_plain. 
have embedding_g' : embedding g'. 
{ split => //. 
  - move=> z. have [dz ->] := codomP (surj_g z). by apply/codomP; exists (Icp dz).
  - have ? := @nodeI D'.
    have cnode_Icp := add_edge_cnodeE dxDdy.
    have fD' : add_edge_node dx dy = @node D' by [].
    move => [||d1] [||d2]; rewrite /= ?connect0 ?eqxx //= ?fD'.
    1,3: by rewrite ?[cnode _ (IcpX : D')]cnodeC add_edge_cnodeXXe 
            vertex_g g_x g_y ?[y == x]eq_sym.
    all: rewrite -?g_x -?g_y. 
    1-2: rewrite ?[_ _ IcpX](@cnodeC D') //. (* by fails ? *)
    1-2: rewrite (@cnode1 D'). 3-4: rewrite (@cnode1r D').
    1-5: by rewrite cnode_Icp -?cnode1 -?cnode1r.    
  - have adjn_Icp := @add_edge_adjn D _ _ dxDdy. 
    pose m (d : D') := match d with IcpX => 1 | IcpXe => 2 | _ => 0 end.
    move => d1 d2; wlog: d1 d2 / m d1 <= m d2 => [W|].
    { have [|/ltnW] := leqP (m d1) (m d2); first exact: W.
      rewrite sg_sym adjnC //. exact: W. }
    have dxdyF : cnode dx dy = false by rewrite vertex_g g_x g_y (negbTE xDy).
    move: d1 d2 => [||d1] [||d2] // _ ; rewrite /= ?sg_irrefl.
    + by rewrite adjn_node1 adjn_node1r /= adjn_Icp edge_g sg_irrefl -!cnode1 dxdyF.
    + by rewrite /edge_rel/= (negbTE xDy) !eq_refl orbT adjn_edge.
    + rewrite adjn_node1 adjn_node1r /= adjn_Icp edge_g sg_irrefl.
      by rewrite -!cnode1 cnodeC dxdyF.
    + rewrite adjn_node1r /= adjn_Icp -!cnode1 -adjn_node1r.
      rewrite dxdyF connect0 andbF andbT /=.
      rewrite edge_g [RHS]/edge_rel/=  g_x (negbTE xDy) !andbF eqxx /=.
      by apply:orb_id2l => _; rewrite vertex_g g_y andb_idl // => /eqP->.
    + rewrite adjn_node1r /= adjn_Icp -!cnode1 -adjn_node1r [cnode dy dx]cnodeC.
      rewrite dxdyF connect0 andbF andbT /= edge_g [RHS]/edge_rel/=.
      rewrite [y == x]eq_sym eqxx (negbTE xDy) !andbF !orbF !andbT g_y.
      by apply:orb_id2l => _; rewrite vertex_g g_x andb_idl // => /eqP->.
    + rewrite adjn_Icp [RHS]/edge_rel/= edge_g !vertex_g g_x g_y.
      apply: orb_id2l => _; rewrite ?[x == _]eq_sym ?[y == _]eq_sym.
      rewrite ![(_ != _) && _]andb_idl ?[(g d2 == x) && _]andbC //.
      all: by move=> /andP[/eqP-> /eqP->]. }
have planar_D := emb_planar g.
have planar_D' : planar D' by apply: add_edge_planar. 
have [o' def_o] := orbit_case face dx; rewrite -/o in def_o.
have dy_o' : dy \in o'.
{ by have := mem_nth dx lt_size_o; rewrite -/dy def_o inE eq_sym (negbTE dxDdy). }
pose o1 := take (index dy o') o'; pose o2 := drop (index dy o').+1 o'.
have size1 : size s1 = size o1. 
{ rewrite /o1 size_take index_mem dy_o' /dy def_o /= index_uniq //.
  - by rewrite -ltnS -[(size o').+1]/(size (dx::o')) -def_o. 
  - apply: subseq_uniq (orbit_uniq face dx). rewrite -/o def_o. exact: subseq_cons. }
have [def_s1 def_s2 def_o'] : 
  [/\ s1 = [seq g d | d <- o1], s2 = [seq g d | d <- o2] & o' = o1 ++ dy :: o2].
{ move: size1 E. rewrite def_o /o1 /o2 /s. 
  case/splitP : _ _ _ / dy_o' => [p1 p2 _] size1 /=.
  move/eqP; rewrite g_x eqseq_cons eqxx -cats1 -catA /= map_cat /=.
  by rewrite eqseq_cat ?size_map // eqseq_cons g_y eqxx /= => /andP[/eqP-> /eqP->]. }
rewrite def_o' in def_o; exists (Build_plane_embedding embedding_g' planar_D').
- exists (IcpXe) => /=. rewrite add_edge_orbitXe //= -/o. 
  rewrite def_o left_arc -?def_o ?orbit_uniq //= -map_comp g_x /=.
  by rewrite (@eq_map _ _ _ g) // def_s1.
- exists (IcpX) => /=. rewrite add_edge_orbitX //= -/o.
  rewrite def_o right_arc -?def_o ?orbit_uniq //= -map_comp g_y /=.
  by rewrite (@eq_map _ _ _ g) // def_s2.
Qed.

(* TOTHINK: using [arc], we would need [uniq s] *)
Lemma plane_add_edge' (G : sgraph) (g : plane_embedding G) (x y : G) (s : seq G) : 
  x != y -> sface g s -> x \in s -> y \in s -> uniq s ->
  exists g' : plane_embedding (add_edge x y), 
    sface g' (rcons (arc s x y) y) /\ sface g' (rcons (arc s y x) x).
Proof.
Abort.

(** Adding a "fan", i.e. a new vertex connected to a number of other vertices, all on the same face *)

Section AddEdges2.
Variables (G : sgraph) (U V : {set G}).
Definition add_edges2_rel := 
  [rel u v : G | u -- v || (u != v) && ((u \in U) && (v \in V) || (u \in V) && (v \in U))].

Fact add_edges2_irrefl : irreflexive add_edges2_rel.
Proof. by move=> x /=; rewrite sg_irrefl eqxx. Qed.

Fact add_edges2_sym : symmetric add_edges2_rel.
Proof. 
by move=> x y; rewrite /= ![_ && (x \in _)]andbC [_ && _ || _]orbC eq_sym sg_sym.
Qed.

Definition add_edges2 := SGraph add_edges2_sym add_edges2_irrefl.
End AddEdges2.

Arguments add_edges2 : clear implicits.

Lemma add_node_diso_proof (G : sgraph) (A : {set G}) (x : G) : x \in A ->
     @add_edges2_rel (add_node G [set x]) [set None] [set Some x | x in A :\ x] 
  =2 add_node_rel A.
Proof.
move=> x_A [u|] [v|] //=; rewrite [in LHS]/edge_rel/= ?inE //.
- rewrite andbT andFb /= mem_imset ?inE; last exact: Some_inj.
  by have [->|//] := eqVneq u x; rewrite x_A.
- rewrite andbF andTb orbF mem_imset ?inE; last exact: Some_inj.
  by have [->|//] := eqVneq v x; rewrite x_A.
Qed.

Lemma add_node_diso (G : sgraph) (A : {set G}) (x : G) : 
  x \in A -> 
  diso (add_edges2 (add_node G [set x]) [set None] (Some @: (A :\ x))) (add_node G A).
Proof. by move=> x_A; exact/eq_diso/add_node_diso_proof. Defined.

Lemma diso_embedding (G H : sgraph) (g : plane_embedding G) (i : diso G H) : embedding (i \o g).
Proof.
case: g => D g [G1 G2 G3 G4] _ /= ; split => //=.
- move=> x; have [d ? gd] := mapP (G2 (i^-1 x)). 
  apply/mapP; exists d => //=. by rewrite -gd bijK'.
- move=> d1 d2; by rewrite inj_eq.
- move=> d1 d2; by rewrite edge_diso.
Qed.

Definition diso_plane_embedding (G H : sgraph) (g : plane_embedding G) (i : diso G H) := 
  Build_plane_embedding (diso_embedding g i) (emb_planar g).

Lemma diso_plane_embedding_inh (G H : sgraph) : 
   inhabited (plane_embedding G) -> diso G H -> inhabited (plane_embedding H).
Proof. move => [g i]; constructor. exact: diso_plane_embedding i. Qed.

Lemma iff_exists (T : Type) (P Q: T -> Prop) : 
  (forall x, P x <-> Q x) -> (exists x : T, P x) <-> (exists x : T, Q x).
Proof. firstorder. Qed.

Lemma diso_face (G H : sgraph) (g : plane_embedding G) (i : diso G H) s : 
  sface g s <-> sface (diso_plane_embedding g i) (map i s). 
Proof.
apply: iff_exists => d /=. 
rewrite map_comp [map _ _ = _](rwP eqP) inj_eq -?(rwP eqP) //. 
exact: inj_map.
Qed.

Arguments add_edge : clear implicits.
Arguments add_edges2_rel : clear implicits.

Lemma add_edge1n_diso_proof (G : sgraph) (A : {set G}) (x y : G) :
  @add_edges2_rel (add_edge G x y) [set x] A =2 add_edges2_rel _ [set x] (y |: A).
Proof.
move=> u v. rewrite /= !inE /edge_rel/= /edge_rel /=.
case (sedge _ _) => //=. case: (eqVneq u v) => H; subst => //=. 
case: (eqVneq u x) => ?; subst => //=. 
all: case: (eqVneq v x) => ?; subst => //=. by rewrite eqxx in H.
Qed.

Lemma add_edge1n_diso (G : sgraph) (A : {set G}) (x y : G) :
  y \notin A -> diso (add_edges2 (add_edge G x y) [set x] A)
               (add_edges2 G [set x] (y |: A)).
Proof. by move=> yNA; apply: eq_diso; exact: add_edge1n_diso_proof. Defined.

Lemma add_edge11_diso_proof (G : sgraph) (x y : G) : 
  add_edge_rel x y =2 add_edges2_rel _ [set x] [set y].
Proof.
move => u v; rewrite /= !in_set1 andb_orr; congr [|| _ , _ | _]. 
by rewrite [v == u]eq_sym [(v == x) && _]andbC.
Qed.

Lemma add_edge11_diso (G : sgraph) (x y : G) : 
  diso (add_edge G x y) (add_edges2 G [set x] [set y]).
Proof. apply: eq_diso; exact: add_edge11_diso_proof. Defined.

Lemma set_nil (T : finType) : [set x in Nil T] = set0.
Proof. by apply/setP => x; rewrite inE. Qed.

Lemma subseq_notin (T : eqType) (z : T) (p s1 s2 : seq T) :
  z \notin s1 -> subseq (z :: p) (s1 ++ z :: s2) -> subseq p (z :: s2).
Proof.
elim: s1 => [_|a s1 IH]. 
- rewrite cat0s [X in X -> _]/= eqxx => sub_p.
  exact: subseq_trans sub_p (subseq_cons _ _).
- rewrite inE negb_or [X in _ -> X -> _]/= => /andP[/negPf-> zNs1].
  exact: IH.
Qed.

Lemma undup_subseq (T : eqType) (s : seq T) : subseq (undup s) s.
Proof. 
elim: s => // x s IHs; rewrite [undup _]/=; case: ifP; last by rewrite /= eqxx.
by move=> _; apply: subseq_trans IHs (subseq_cons _ _).
Qed.

Lemma plane_add_fan (G : sgraph) (g : plane_embedding G) x y s1 s2 (A : {set G}) : 
  x != y -> sface g (x :: s1 ++ y :: s2) -> x \notin A -> y \in A -> {subset A <= rcons s1 y} -> 
  exists g' : plane_embedding (add_edges2 G [set x] A), sface g' [:: x, y & s2].
Proof.
move=> xDy face_g xNA y_A subA.
pose As := undup [seq z <- s1 | z \in A :\ y].
have subAs : subseq As s1.
  by apply: subseq_trans (undup_subseq _) _; apply: filter_subseq.
have yNAs : y \notin As by rewrite mem_undup mem_filter !inE eqxx.
have xNAs : x \notin As by rewrite mem_undup mem_filter !inE (negPf xNA).
have -> : A = y |: [set z in As]. 
  apply/setP => u; rewrite !inE mem_undup mem_filter !inE. 
  have [-> //|/= uDy] := eqVneq u y. rewrite andb_idr // => /subA.
  by rewrite mem_rcons inE (negPf uDy).
have uniq_As : uniq As by apply: undup_uniq.
move: As subAs xNAs yNAs uniq_As => {A y_A xNA subA} As.
have [n Hn] := ubnP (size As).
elim: n G g x y s1 s2 xDy face_g As Hn => // n IH G g x y s1 s2 xDy face_g.
case => [_ _ _ _ _|z As /= /ltnSE lt_As_n].
- rewrite set_nil setU0. 
  have [h _ face_h] := plane_add_edge xDy face_g.
  set i := add_edge11_diso x y; exists (diso_plane_embedding h i). 
  by move/(diso_face h i): face_h; rewrite map_id_in.
- rewrite !inE !negb_or => subAs /andP[xDz xNAs] /andP [yDz yNAs] /andP[zNAs uniq_As].
  have z_s1 : z \in s1 by apply/(mem_subseq subAs)/mem_head.
  case/splitPr def_s1 : _ / z_s1 => [p1 p2 zNp1].
  have/plane_add_edge: sface g (x :: p1 ++ z :: p2 ++ y :: s2). 
   by move: face_g; rewrite def_s1 /= -catA.
  move/(_ xDz) => [g' _ face_g']. 
  have [//||//|//|//|h face_h] := IH (add_edge G x z) g' x y (z::p2) s2 xDy _ _ lt_As_n.
  + by move: subAs; rewrite def_s1; exact: subseq_notin. 
  + set G' := add_edges2 _ _ _. 
    have @i: diso (add_edges2 (add_edge G x z) [set x] (y |: [set z0 in As])) G'.
    { apply: eq_diso.
      abstract (rewrite set_cons setUA [[set _;_]]setUC -setUA; exact: add_edge1n_diso_proof). }
    exists (diso_plane_embedding h i). 
    by move/(diso_face h i): face_h; rewrite map_id_in.
Qed.

Lemma plane_add_node (G : sgraph) (g : plane_embedding G) (x y : G) s1 s2 (A : {set G}) :
  x != y -> sface g (x :: s1 ++ y :: s2) -> {subset A <= x :: rcons s1 y} -> x \in A -> y \in A ->
  exists (g' : plane_embedding (add_node G A)), sface g' [:: Some x, None & [seq Some z | z <- y::s2]].
Proof.
move=> xDy face_s subA x_A y_A.
suff [h face_h] : 
  exists h : plane_embedding (add_edges2 (add_node G [set x]) [set None] (Some @: (A :\ x))), 
        sface h [:: Some x, None & [seq Some z | z <- y :: s2]].
{ set i := add_node_diso x_A; exists (diso_plane_embedding h i). 
  by move: face_h; rewrite (diso_face _ i) map_id_in. }
have [g'] := plane_add_node1 face_s.
set G' := add_node _ _; rewrite map_cat /=.
set y' := Some y; set x' := Some x; set s1' := map Some s1; set s2' := map Some s2.
set A' := Some @: (A :\ x).
move/(rot_face 1) => face_g'.
have {face_g'} face_g' : sface g' (None :: (x'::s1') ++ y' :: rcons s2' x').
{ by move: face_g'; rewrite rot1_cons /= rcons_cat /=. }
have y_A' : y' \in A' by rewrite imset_f // !inE eq_sym xDy.
have subA' : {subset A' <= x' :: rcons s1' y'}.
{ move=> ? /imsetP [u /setD1P [uDx /subA uA] ->]. 
  by move: uA; rewrite -(mem_map Some_inj) /= map_rcons. }
have [//||h face_h] := plane_add_fan _ face_g' _ y_A' subA'.
  by apply/negP=>/imsetP [?].
exists h. move/(rotr_face 1) : face_h. by rewrite -!rcons_cons rotr1_rcons.
Qed.

Lemma plane_add_node' (G : sgraph) (g : plane_embedding G) (x y : G) s (A : {set G}) : 
  x \in s -> y \in s -> x != y -> sface g s -> {subset A <= rcons (arc s x y) y} -> uniq s ->
  x \in A -> y \in A -> 
  exists (g' : plane_embedding (add_node G A)), 
    sface g' [:: Some x, None & [seq Some z | z <- arc s y x]].
Proof.
move=> x_s y_s xDy face_s subA uniq_s x_A y_A.
have [i s1 s2 arc1 arc2 rot_i] := rot_to_arc uniq_s x_s y_s xDy.
rewrite -(arc_rot i) // rot_i right_arc -?rot_i ?rot_uniq //.
apply: (plane_add_node (g := g) (s1 := s1)) => //.
- rewrite -rot_i. exact: rot_face.
- by rewrite -(arc_rot i) // rot_i left_arc -?rot_i ?rot_uniq in subA.
Qed.



Lemma foo (T : finType) (s : seq T) (A : {set T}) : 
  1 < #|A| -> {subset A <= s} -> 
  exists x y s1 s2 s3, 
    [/\ x \in A, y \in A, x != y, s = s1 ++ x :: s2 ++ y :: s3 & [disjoint A & s2]].
Proof.
move=> lt1A; elim/(size_ind (@size T)) : s => s IH subAs.
have hasAs : has (mem A) s. 
{ case/card_gt0P : (ltnW lt1A) => x xA; apply/hasP; exists x => //. exact: subAs. }
case/split_find def_s : {-}s _ _ / hasAs => [/= x s1 s2 xA nAs1].
have hasAs2 : has (mem A) s2. 
{ apply: contraTT lt1A => nAs2; rewrite -leqNgt; apply/card_le1_eqP => u v uA vA.
  wlog suff eq_x : u uA / u = x; first by rewrite [v]eq_x // [u]eq_x.
  rewrite -!disjoint_has in nAs1 nAs2.
  move/subAs : (uA). rewrite def_s !(mem_cat,mem_rcons,inE).
  by rewrite (disjointFl nAs1) // (disjointFl nAs2) // !orbF => /eqP. }
case/split_find def_s2 : {-}s2 _ _ / hasAs2 => [/= y s21 s22 yA nAs21].
rewrite -!disjoint_has in nAs1 nAs21.
have [eq_xy|xDy] := eqVneq x y.
- subst y; have sub_A_s2 : {subset A <= s2}. 
  { move=> u uA; move/subAs : (uA).
    rewrite def_s mem_cat mem_rcons inE (disjointFl nAs1) ?orbF //.
    by case/predU1P => [->|//]; rewrite def_s2 mem_cat mem_rcons mem_head. }
  have size_s2 : size s2 < size s.
  { by rewrite def_s size_cat size_rcons addSn ltnS leq_addl. }
  have [u[v[p1[p2[p3[uA vA uDv def_s2' disAp2]]]]]] := IH s2 size_s2 sub_A_s2. 
  by exists u,v,(rcons s1 x ++ p1),p2,p3; split; rewrite // def_s def_s2' /= -catA. 
- exists x,y,s1,s21,s22; rewrite disjoint_sym nAs21; split => //.
  by rewrite def_s def_s2 -!cats1 /= -!catA.
Qed.

(* [0 < #|A|] is required sind hypermaps cant have isolated vertices *)
Lemma plane_add_node_simple (G : sgraph) (g : plane_embedding G) s (A : {set G}) x :
  x \in A -> sface g s -> {subset A <= s} -> inhabited (plane_embedding (add_node G A)).
Proof.
have [gt1A _ {x} face_s subA|le1A xA] := ltnP 1 #|A|; last first.
- have/eqP eq_A : A == [set x]; last subst A.
  { by apply/eq_set1P; split => // y yA; apply: (card_le1_eqP le1A). }
  move=> face_s subXs; have x_s : x \in s by apply: subXs; rewrite in_set1.
  have [i s' rot_i] := rot_to x_s; move/(rot_face i): face_s; rewrite rot_i.
  by case/plane_add_node1. 
- have : exists x y s1 s2 i, 
    rot i s = x :: s1 ++ y :: s2 /\ x != y /\ [disjoint A & s2] /\ x \in A /\ y \in A.
  { have [x [y [s1 [s2 [s3 [xA yA xDy def_s disA]]]]]] := foo gt1A subA.
    exists y,x,(s3++s1),s2,(size (s1 ++ x :: s2)). 
    by rewrite def_s -!cat_cons catA rot_size_cat eq_sym /= -catA. }
  move => [x] [y] [s1] [s2] [i] [rot_i [xDy [disjA [xA yA]]]].
  move/(rot_face i) in face_s; rewrite rot_i in face_s. 
  have [|//|//|//] := @plane_add_node _ _ _ _ _ _ A xDy face_s.
  move=> a aA; move: (aA) => /subA. 
  rewrite -(mem_rot i) rot_i !(inE,mem_cat,mem_rcons) (disjointFr disjA) //.
  by rewrite orbF => /or3P[->|->|->].
Qed.

(** Deleting vertex from a 2-connected plane graph yields a plane
graph with a face containing all the neighbors of the deleted node. *)

Section PlaneDelVertex.
Variables (G : sgraph) (g : plane_embedding G) (x : G).

Hypothesis connG : 2.-connected G.

Let D := emb_map g.
Let d := emb_inv (emb_embedding g) x.
Let G' := induced [set~ x].
Let D' := del_node d.
Let N := fclosure edge (cnode d).

Lemma del_vertex_emb_proof (z : D') : g (val z) \in [set~ x].
Proof.
case: z => z Hz /=; rewrite !inE. 
apply: contraNneq Hz => E. apply: mem_closure. 
by rewrite inE /d -E (emb_vertex (emb_embedding g)) (emb_invK).
Qed.

Definition del_vertex_emb (z : D') : G' := 
  Sub (g (val z)) (del_vertex_emb_proof z).

Let nxxF (z : D) : node z == z = false.
Proof.
have := kconnected_degree (g z) connG; rewrite ltnNge. 
apply: contraNF => /eqP /(@order_le_fix _ node 0 z).
exact/leq_trans/emb_degree/emb_embedding.
Qed.

Hypothesis simpleD : forall x y : D, x != y -> cnode x y -> ~~ cnode (edge x) (edge y).

Lemma del_vertex_emb_embedding : embedding del_vertex_emb.
Proof.
have [plainD surj_g vertex_g edge_g] := emb_embedding g.
rewrite -/D in plainD vertex_g edge_g.
split.
- exact/del_node_plain.
- move => y. have [y0 g_y0] := codomP (surj_g (val y)); apply/codomP.
  have Hy : ~~ cnode d y0. 
    by apply: contraTN (valP y); rewrite !inE negbK cnodeC vertex_g -g_y0 emb_invK.
  have [/del_node_neighbor1|y0N]:= boolP (y0 \in N).
  + case/(_ _ _ _ _)/Wrap => // ny0N. exists (Sub (node y0) ny0N). 
    by apply: val_inj; rewrite /= g_y0; apply/eqP; rewrite -vertex_g -cnode1r.
  + by exists (Sub y0 y0N); exact: val_inj. 
- by move=> d1 d2; rewrite del_node_cnode vertex_g /del_vertex_emb -val_eqE.
- by move=> d1 d2; rewrite del_node_adjn // edge_g /del_vertex_emb.
Qed.

Definition del_vertex_plane_embedding :=
  Build_plane_embedding del_vertex_emb_embedding (del_node_planar d (emb_planar g)).

Let g' := del_vertex_plane_embedding.


Lemma del_vertex_neighbor_face : 
  exists2 s : seq G', sface g' s & {subset N(x) <= map val s}.
Proof.
have fdN : face d \notin N. 
{ apply: wheel_proof => //.
  - apply: plane_emb_plain.
  - apply: plane_emb_loopless. }
set d' : D' := Sub (face d) fdN; set s := [seq g' i | i <- orbit face d'].
have H := @neighbor_face_aux D d _ _ simpleD nxxF. 
exists s; first by exists d'. 
move => z; rewrite inE /s -map_comp => xz. apply/mapP. 
rewrite -[x](pinvK g) -[z](pinvK g) -plane_emb_edge -[pinv g x]/d in xz.
have cycleD : forall x y : D, x != y -> cface x y -> ~~ cnode x y.
{ apply: two_connected_cyle => //. 
  apply: two_connected_avoid_one (emb_embedding g) connG.
  - exact: plane_emb_plain.
  - exact: plane_emb_loopless.
  - exact: emb_planar. }
have := @del_node_adjn_face 
          D d (plane_emb_plain g) (plane_emb_loopless g) simpleD nxxF cycleD.
move=> /(_ _ xz) => -[dz]; rewrite [wheel_proof _ _ _ _ _ ](bool_irrelevance _ fdN).
case => D1 D2. 
by exists dz => //=; apply/eqP; rewrite -[z](pinvK g) -plane_emb_vertex cnodeC.
Qed.

End PlaneDelVertex.

Arguments skip_hom [T] a [f] _.

Lemma subgraph_embedding (G H : sgraph) (D : hypermap) (g : D -> H) : 
  subgraph G H -> no_isolated G -> embedding g -> 
  exists (D' : hypermap) (g' : D' -> G), embedding g' /\ genus D' <= genus D.
Proof.
case => h inj_h hom_h no_isoG emb_g.
have plainD := emb_plain emb_g.
pose V := h @: G.
pose h' (x : H) : option G :=
  if boolP (x \in codom h) is AltTrue b then Some (iinv b) else None.
pose r := [rel u v : H | 
           if (h' u, h' v) is (Some u', Some v') then u' -- v' else false].
pose p := [pred x : D | r (g x) (g (edge x))].
pose e := frestrict (skip_hom p edgeI).
pose n := frestrict (skip_hom p nodeI).
pose f := finv n \o finv e.
have can3 : cancel3 e n f.
{ by move=> x; rewrite /f/= f_finv ?finv_f //; apply/frestrict_inj/skip_inj. }
pose D' := Hypermap can3. 
have cl_p : fclosed edge p.
{ move=> x y /eqP <- {y}. rewrite !inE plain_eq // /h'.
  case: {-}_ / boolP => [gx_h|gxNh]; case: {-}_ / boolP => [gex_h|gexNh] => //.
  by rewrite sgP. }
have eE (x : D') : val (edge x) = edge (val x).
{ rewrite val_frestrict skip1 // -(fclosed1 cl_p); exact: (valP x). }
have imG : forall x : D', g (val x) \in codom h. 
{ move=> x. have:= valP x. rewrite /p/=/h'. by case: {-}_ / boolP. }
pose g' (x : D') := iinv (imG x).
have leq_genus : genus D' <= genus D by apply: sub_genus => x; rewrite val_frestrict.
suff emb_g' : @embedding G D' g' by exists D',g'. 
have cnE (x y : D') : cnode x y = (g' x == g' y).
{ rewrite fconnect_frestrict fconnect_skip //; try apply: valP.
  rewrite /g' -(inj_eq inj_h) !f_iinv; exact/emb_vertex. }
split => //.
- apply/plainP => x _; split; last by rewrite -val_eqE eE plain_neq.
  by apply: val_inj; rewrite !eE plain_eq.
- move=> x; have [y xy] := no_isoG x.
  move/hom_h: (xy); rewrite inj_eq // sg_edgeNeq // => /(_ isT) hx_hy.
  have/codomP [dx hx_dx] := emb_surj emb_g (h x).
  have/codomP [dy hy_dy] := emb_surj emb_g (h y).
  move: hx_hy; rewrite hx_dx hy_dy -(emb_edge emb_g).
  case/exists_inP => [dz]; rewrite !inE => cn_xz cn_yz. 
  suff pz : p dz.
  { apply/codomP; exists (Sub dz pz). apply: inj_h. rewrite f_iinv /=. 
    by rewrite hx_dx (rwP eqP) -(emb_vertex emb_g). }
  rewrite !(emb_vertex emb_g) in cn_xz cn_yz.
  rewrite /p/=/h' altT -?(eqP cn_xz) -?hx_dx ?codom_f // => codom_x.
  rewrite altT -?(eqP cn_yz) -?hy_dy ?codom_f // => codom_y.
  by rewrite !iinv_f.
- move=> x y; apply/exists_inP/idP => [[z]|].
  + rewrite !inE !cnE /g' => /eqP-> /eqP->; have:= valP z; rewrite /p/=/h'. 
    case : {-}_ /boolP => // gz_h; case : {-}_ /boolP => // gez_h.
    move: (imG (e z)); rewrite /= eE => gez_h'.
    by rewrite (bool_irrelevance gz_h (imG z)) (bool_irrelevance gez_h gez_h'). 
  + move=> g'_xy.
    move/hom_h : (g'_xy); rewrite inj_eq // (sg_edgeNeq g'_xy) => /(_ isT) hg'_xy.
    move: (hg'_xy); rewrite !f_iinv => g_xy. 
    move: (g_xy); rewrite -(emb_edge emb_g) => /exists_inP[z].
    rewrite !inE => cn_xz cn_yz. 
    suff pz : p z. 
    { exists (Sub z pz); rewrite inE fconnect_frestrict fconnect_skip // ?eE //; try apply: valP.
      by rewrite -(fclosed1 cl_p). }
    rewrite !(emb_vertex emb_g) in cn_xz cn_yz.
    rewrite /p/=/h' altT -(eqP cn_xz) ?imG // => codom_x.
    rewrite altT -(eqP cn_yz) ?imG // => codom_y.
    move: g'_xy; rewrite /g'; move: (imG x) (imG y) => P1 P2.
    by rewrite (bool_irrelevance P1 codom_x) (bool_irrelevance P2 codom_y).
Qed.

Lemma subgraph_plane_embedding (G H : sgraph) : 
  subgraph G H -> no_isolated G -> 
  plane_embedding H -> inhabited (plane_embedding G).
Proof.
move=> sub_G_H no_isoG [D g emb_g] planarD. 
have [D'[g' [emb_g']]] := subgraph_embedding sub_G_H no_isoG emb_g.
rewrite (eqP planarD) (leqn0) -/(planar D') => planarD'.
by exists; apply: Build_plane_embedding emb_g' planarD'.
Qed.

(** Removing parallel edges *)

Section RemoveParallelEdges.
Variables (G : sgraph).

Lemma remove_parallel (D : hypermap) (g : D -> G) (emb_g : embedding g) : 
  exists (D' : hypermap) (g' : D' -> G), 
    [/\ simple_hmap D', embedding g' & genus D' <= genus D].
Proof.
elim/card_ind : D g emb_g => D IH g emb_g.
pose b := [exists x : D, exists y, [&& x != y, cnode x y & cnode (edge x) (edge y)]].
have [|simpleD] := boolP b; rewrite /b; last first.
{ exists D, g; split => // x y xDy n_x_y. 
  by move: simpleD => /existsPn /(_ x) /exists_inPn /(_ _ xDy); rewrite n_x_y. }
move=> /existsP [x /exists_inP [y xDy /andP[n_x_y n_ex_ey]]].
have plainD : plain D by apply: emb_plain emb_g.
have exF : edge x != x by rewrite plain_neq.
pose D' := @WalkupE (WalkupF x) (Sub (edge x) exF).
pose g' (z : D') := g (val (val z)).
suff emb_g' : embedding g'.
{ have leD : #|D'| < #|D|.
    by rewrite /D' -card_S_Walkup /WalkupF /= card_sig max_card.
  have [D'' [g'' [D1 D2 D3]]] := IH _ leD _  emb_g'. 
  exists D'', g''; split => //; apply: leq_trans D3 _. 
  exact: leq_trans (le_genus_WalkupE _) (le_genus_WalkupF _). }
rewrite eq_sym in xDy.
have plain_eq := plain_eq plainD.
have yDex : y != edge x. 
{ apply: contraNneq (emb_loopless emb_g) => y_ex. by apply/existsP; exists x; rewrite -y_ex. }
have inDpf (z : D) (zDx : z != x) (zDex : z != edge x) : 
  (Sub z zDx) != Sub (edge x) exF :> WalkupF x by rewrite -val_eqE.
pose inD' (z:D) (zDx : z != x) (zDex : z != edge x) : D' := 
  Sub (Sub z zDx) (inDpf z zDx zDex).
have plainD' : plain D'.
{ apply/plainP => u _; case: u => [[u U1] U2']. 
  have U2 : @edge D u != x by rewrite -!val_eqE /= -(inj_eq edgeI) /= plain_eq in U2'. 
  split.
  + do 2 apply: val_inj; rewrite /= ![sval (if _ then _ else _)]fun_if.
    rewrite -!val_eqE /= ![sval (if _ then _ else _)]fun_if.
    rewrite plain_eq !eqxx /=. 
    by rewrite (negbTE U2) plain_eq (negbTE U1).
  + rewrite -!val_eqE /= ![sval (if _ then _ else _)]fun_if /=.
    by rewrite -!val_eqE /= plain_eq !eqxx (negbTE U2) plain_neq. }
split => //.
- (* chose [y] (resp. [edge y]) if [x]/[edge x] is the preimage *)
  move=> v; have [z g_z] := codomP (emb_surj emb_g v).
  have [xVex|] := boolP (z \in pred2 x (edge x)).
  + case/pred2P : xVex => ?; subst z v; apply/codomP.
    * by exists (inD' _ xDy yDex); apply/eqP; rewrite -(emb_vertex emb_g).
    * rewrite -(inj_eq edgeI) in xDy; rewrite -(inj_eq edgeI) plain_eq in yDex.
      by exists (inD' _ yDex xDy); apply/eqP; rewrite -(emb_vertex emb_g).
  + rewrite !inE negb_or => /andP [zDx zDex]. by apply/codomP; exists (inD' _ zDx zDex).
- move => u v. by rewrite !walkup.fconnect_skip /= (emb_vertex emb_g).
- move => u v. 
  have edge_val (z : D') : @edge D (val (val z)) = val (val (edge z)).
  { rewrite /= ![sval (if _ then _ else _)]fun_if /= -!val_eqE /=.
    rewrite !plain_eq !eqxx ifF // -(inj_eq edgeI) plain_eq. 
    by move: (valP z); rewrite -val_eqE => /=/negbTE->. }
  suff -> : adjn u v = @adjn D (val (val u)) (val (val v)) by apply: emb_edge.
  apply/exists_inP/exists_inP => -[z]; rewrite !inE.
  + by rewrite !walkup.fconnect_skip; exists (val (val z)); rewrite // edge_val.
  + have [xVex|] := boolP (z \in pred2 x (edge x)).
    * wlog -> : z u v {xVex} / z = x => [W|].
      { case/pred2P : xVex => z_ex ; first exact: W.
        move=> n_u n_v. move: (W (edge z) v u); rewrite {1}z_ex !plain_eq.
        case => // z'. exists (edge z') => //. by rewrite (geometry.plain_eq plainD'). }
      exists (inD' _ xDy yDex); rewrite !inE !walkup.fconnect_skip //=.
        exact: connect_trans n_x_y.
      rewrite fun_if -val_eqE /= plain_eq !eqxx -(inj_eq edgeI) plain_eq (negbTE yDex).
      exact: connect_trans n_ex_ey.
    * rewrite inE negb_or => /andP[zDx zDex] n_u_z n_v_ez.
      by exists (inD' _ zDx zDex); rewrite !inE !walkup.fconnect_skip // -edge_val.
Qed.

Lemma le_genus_planar (D D' : hypermap) : genus D' <= genus D -> planar D -> planar D'.
Proof. rewrite /planar -!leqn0. exact: leq_trans. Qed.

Lemma simple_embedding (g : plane_embedding G) : 
  exists g' : plane_embedding G, simple_hmap (emb_map g').
Proof.
case: g => D g emb_g planarD.
have [D' [g' [simpleD' emb_g' le_genus]]] := remove_parallel emb_g.
have planarD' : planar D' by exact: le_genus_planar planarD.
by exists (Build_plane_embedding emb_g' planarD').
Qed.

End RemoveParallelEdges.


(** ** Obtaining plane embeddings for smerge2 *)
Section smerge_plane_embedding.
Variables (G : sgraph) (x y : G) (g : plane_embedding G).

Local Notation "'@cnode[' G ]" := (fconnect (@node G)) (at level 1, format "'@cnode[' G ]").
Local Notation "'@cface[' G ]" := (fconnect (@face G)) (at level 1, format "'@cface[' G ]").
Local Notation "'@adjn[' G ]" := (@adjn G) (at level 1, format "'@adjn[' G ]").

Let G' := smerge2 G x y.
Let D := emb_map g.

Section embeddging.
Variables (dx dy : D).
Let D' := merge D dx dy.

Hypothesis xNy : x -- y = false.
Hypothesis xDy : x != y.
Hypothesis g_dx : g dx = x.
Hypothesis g_dy : g dy = y.

Let plainD' : plain D'. Proof. by apply: plane_emb_plain. Qed.
Let dxDdy : dx != dy. Proof. by apply: contra_neq xDy; congruence. Qed.

Definition g' (dz : D') := 
  if @boolP ((g dz) == y) is AltFalse p then Sub (g dz) p else (Sub x xDy) : G'.

Lemma embedding_g' : embedding g'.
Proof.
have n_dxy : ~~ @cnode[D] dx dy. 
  by rewrite plane_emb_vertex g_dx g_dy.
have llD : loopless D by apply plane_emb_loopless.
have nAdydy : ~~ @adjn[D] dx dy by rewrite plane_emb_edge g_dx g_dy xNy.
have llD' : loopless D' by apply merge_loopless.
have subDD' : subrel @cnode[D] @cnode[D'] by apply: switch_subrel.
have adjnD' (d1 d2 : D) : g d1 = y -> @adjn[D'] d1 d2 = @adjn[D] d2 dx || @adjn[D] d2 dy.
{ move => g1_y. apply: adjn_merge1 => //. by rewrite (plane_emb_vertex) g_dy g1_y. }
have adjnD'' (d1 d2 : D) : g d1 = x -> @adjn[D'] d1 d2 = @adjn[D] d2 dx || @adjn[D] d2 dy.
{ move => g1_y. rewrite /D' adjn_mergeC orbC. apply: adjn_merge1 => //; first by rewrite eq_sym.
  by rewrite cnodeC. by rewrite adjnC. 
  by rewrite (plane_emb_vertex) g_dx g1_y. }
split => //.
- case => z zDy. have [z0 g_z0] := codomP (plane_emb_surj g z).
  by apply/codomP; exists z0; apply: val_inj; rewrite /g'/= -g_z0 altF.
- move => d1 d2; rewrite cnode_merge // !plane_emb_vertex /g'.
  case: {-}_ / boolP => [/eqP g1_y|g1Dy]; case: {-}_ / boolP => [/eqP g2_y|g2Dy].
  all: rewrite -val_eqE /= ?g1_y ?g2_y ?g_dx ?g_dy ?eqxx //.
  all: by rewrite ?[y == _]eq_sym ?[_ == x]eq_sym ?(negbTE xDy) ?(negbTE g2Dy) ?(negbTE g1Dy).
- move => d1 d2. rewrite /g'. 
  case: {-}_ / boolP => [/eqP g1_y|g1Dy]; case: {-}_ / boolP => [/eqP g2_y|g2Dy].
  + rewrite sgP. have n12 : @cnode[D] d1 d2 by rewrite (plane_emb_vertex) g1_y g2_y.
    apply: contraNF llD' => /exists_inP [z]; rewrite !inE => A1 A2. 
    rewrite cnodeC in A1. apply/existsP; exists z. 
    apply: connect_trans A2. apply: connect_trans A1 _. by apply: switch_subrel n12.
  + rewrite adjnD' //. rewrite /edge_rel/= eqxx andbF /= !plane_emb_edge g_dx g_dy.
    case: (eqVneq (g d2) x) => //= ->. by rewrite sgP.
  + rewrite adjnC // adjnD' // !plane_emb_edge g_dx g_dy [RHS]/edge_rel/= !eqxx andbF /=.
    case: (eqVneq (g d1) x) => //= ->. by rewrite sgP.
  + rewrite /edge_rel/=.
    have [|] := boolP ((g d1 == x) || (g d2 == x)).
    * case: (eqVneq (g d1) x) => [g1x|g1Dx]; case: (eqVneq (g d2) x) => [g2x|g2Dx] => //= _.
      -- rewrite g1x g2x sgP adjn_loopless //. apply: subDD'.
         by rewrite plane_emb_vertex g1x g2x.
      -- by rewrite adjnD'' // !plane_emb_edge g_dx g_dy.
      -- by rewrite adjnC // adjnD'' // !plane_emb_edge g_dx g_dy.
    * rewrite negb_or => /andP[g1Dx g2Dx]; rewrite (negbTE g1Dx) (negbTE g2Dx) /=.
      by rewrite adjn_merge2 // ?(plane_emb_vertex) ?g_dx ?g_dy // plane_emb_edge.
Qed.

Lemma planar1 : ~~ connect (--) x y -> planar D'.
Proof. 
move => nc_xy; apply: merge_planar; last exact: emb_planar.
by rewrite (emb_gcomp (emb_embedding g)) g_dx g_dy nc_xy.
Qed.

End embeddging.

(* simple version - taking any preimages of [x] and [y] *)
Lemma smerge_plane_embedding_disconnected :
  ~~ connect (--) x y -> inhabited (plane_embedding (smerge2 G x y)).
Proof.
move => n_xy. 
have [dx /esym g_dx] := codomP (plane_emb_surj g x).
have [dy /esym g_dy] := codomP (plane_emb_surj g y).
have xDy : x != y by apply: contraNneq n_xy => ->.
have emb_g' : embedding (@g' dx dy xDy).
 by apply: embedding_g' => //; apply: contraNF n_xy; exact: connect1. 
constructor; apply: Build_plane_embedding emb_g' _.
exact: planar1.
Qed.

Hint Extern 0 (embedding _) => exact: emb_embedding : core. (* TODO: move up *)

Lemma face_connect dx dy : @cface[D] dx dy -> connect (--) (g dx) (g dy).
Proof. by rewrite -emb_gcomp //; apply: gcompF. Qed.

Lemma smerge_plane_embedding_disconnected' xs ys :
  ~~ connect (--) x y -> sface g (x :: xs) -> sface g (y :: ys) -> 
  exists (g' : plane_embedding (smerge2 G x y)) s', 
    sface g' s' /\ {subset [predD1 x :: xs ++ ys & y] <= map val s'}.
Proof.
move => n_xy. 
case => dx. move: (fconnect_orbit face dx).
case: (orbit_case face dx) => dxs -> /= f_dx [/esym g_dx def_xs].
case => dy. move: (fconnect_orbit face dy).
case: (orbit_case face dy) => dys -> /= f_dy [/esym g_dy def_ys].

have xDy : x != y by apply: contraNneq n_xy => ->.
have dxDdy : dx != dy by apply: contra_neq xDy => E; rewrite -g_dx E g_dy.
have emb_g' : embedding (@g' dx dy xDy).
 by apply: embedding_g' => //; apply: contraNF n_xy; exact: connect1. 
pose D' := merge D dx dy.
have planarD' : planar D' by apply: planar1.
have fI := @faceI D.
have fxy : @cface[D'] (finv face dy) (finv face dx).
{ rewrite fconnect_switched // ?(inj_eq (finv_inj fI)) 1?eq_sym //.
  rewrite (@cface1 D) (@cface1r D) !f_finv // cfaceC. 
  apply: contraNN n_xy; rewrite -g_dx -g_dy. exact: face_connect. }
have subDD' : subrel @cface[D] @cface[D'].
{ apply switch_subrel; rewrite // -fconnect_switched //. 
  by rewrite ?(inj_eq (finv_inj fI)) 1?eq_sym. }
pose h := Build_plane_embedding emb_g' planarD'; exists h.
exists (map h (@orbit D' face (finv (@face D) dx))); split; first by exists (finv face dx).
move => z /andP [zDy /= Hz].
suff: exists2 dz : D, g dz = z & @cface[D'] (finv face dx) dz.
{ case => dz g_dz; rewrite fconnect_orbit -map_comp => orb_z.
  by apply/mapP; exists dz => //=; rewrite /g' altF ?g_dz. }
move: Hz; rewrite !(inE,mem_cat) def_xs def_ys => /or3P[/eqP -> {zDy z}||].
- exists dx => //. rewrite cfaceC. apply: connect_trans fxy. rewrite cfaceC.
  apply: connect1. by rewrite /= eqxx f_finv.
- case/mapP => dz Hdz /esym g_dz; exists dz => //. apply: subDD'.
  by rewrite cface1 f_finv // f_dx inE Hdz.
- case/mapP => dz Hdz /esym g_dz; exists dz => //; rewrite cfaceC. 
  apply: connect_trans fxy. apply: subDD'. 
  by rewrite cfaceC cface1 f_finv // f_dy inE Hdz. 
Qed.

Lemma smerge_plane_embedding_face s : x \in s -> y \in s -> x != y -> ~~ x -- y -> sface g s -> 
  inhabited (plane_embedding (smerge2 G x y)).
Proof.
move => x_s y_s xDy xNy []; rewrite -/D => dz def_s.
rewrite def_s in x_s y_s.
have [dx fdx /esym g_dx] := mapP x_s.
have [dy fdy /esym g_dy] := mapP y_s.
pose D' := merge D dx dy.
have emb_g' : embedding (@g' dx dy xDy).
 apply: embedding_g' => //. exact: negbTE.
constructor; apply: Build_plane_embedding emb_g' _.
apply: merge_planar; last exact: emb_planar.
rewrite plane_emb_vertex g_dx g_dy (negbTE xDy) /=.
rewrite -!fconnect_orbit in fdx fdy.
by rewrite (connect_trans _ fdy) // cfaceC.
Qed.

End smerge_plane_embedding.





(** ** Non-planarity proofs *)

Lemma connected_n_comp1 (G : sgraph) (x0 : G) : 
  connected [set: G] -> n_comp (--) G = 1.
Proof.
move/connectedTE => conG. 
have E: connect (--) x0 =i G by move => ?; rewrite inE (conG x0).
rewrite -(eq_n_comp_r E) n_comp_connect //. exact: sconnect_sym.
Qed.

Lemma n_comp_Knm n m : n_comp (--) 'K_n.+1,m.+1 = 1.
Proof.
set K := 'K__,_; pose x : K := inl ord0.
suff S : connect (--) x =i K. 
  by rewrite -(eq_n_comp_r S) n_comp_connect //; exact: sconnect_sym.
move => y; rewrite !inE. case: y => [y|y]; last exact: connect1.
by apply: (@connect_trans _ _ (inr ord0)); apply: connect1.
Qed.

Lemma n_comp_Kn n : n_comp (--) 'K_n.+1 = 1.
Proof.
apply: connected_n_comp1 (ord0 : 'K_n.+1) _.
apply: (@connected_center _ (ord0 : 'K_n.+1)) => // j _. 
by have [-> //|?] := eqVneq ord0 j; apply: connect1.
Qed.

Lemma K5nonplanar : ~ inhabited (plane_embedding 'K_5).
Proof.
move => [/simple_embedding [[D g emb_g planarD] /= simpleD]]. 
suff : Euler_lhs D - Euler_rhs D > 0 by rewrite -genus_gt0 (eqP planarD).
pose F := fcard face D.
have cD : #|D| = 20 by rewrite (card_emb emb_g simpleD) card_edge_Kn.
have -> : Euler_lhs D = 22.
  by rewrite /Euler_lhs (emb_n_comp emb_g) n_comp_Kn cD. 
have -> : Euler_rhs D = 15 + F. 
{ rewrite /Euler_rhs (emb_ncard emb_g) (emb_ecard emb_g simpleD).
  by rewrite card_ord card_edge_Kn. }
suff: F < 7 by case: F => [|[|[|[|[|[|[|]]]]]]].
apply: contra_eqT cD. rewrite eqn_leq negb_and -!ltnNge ltnS => F7.
apply/orP;left; rewrite (sum_roots_order faceI).
have bound : {in froots (@face D), forall x, 2 < arity x}.
{ apply:in1W => x; apply: emb_arity3 emb_g simpleD _ _ => {x} x.
  exact: leq_trans (deg_Kn _). }
apply: leq_trans (leq_sum _ bound); rewrite sum_nat_const.
have -> : #|froots (@face D)| = F by apply: eq_card => z; rewrite !inE andbT.
by apply: (@leq_trans (7 * 3)); rewrite // leq_mul2r F7.
Qed.

Lemma K33nonplanar : ~ inhabited (plane_embedding 'K_3,3).
Proof.
move => [/simple_embedding [[D g emb_g planarD] /= simpleD]]. 
suff : Euler_lhs D - Euler_rhs D > 0 by rewrite -genus_gt0 (eqP planarD).
pose F := fcard face D.
have cD : #|D| = 18 by rewrite (card_emb emb_g simpleD) card_edge_Knm.
have -> : Euler_lhs D = 20. 
  by rewrite /Euler_lhs (emb_n_comp emb_g) n_comp_Knm cD. 
have -> : Euler_rhs D = 15 + F. 
{ rewrite /Euler_rhs (emb_ncard emb_g) (emb_ecard emb_g simpleD).
  by rewrite card_sum card_ord card_edge_Knm. }
suff : F <= 4 by case: F => [|[|[|[|[|]]]]].
apply: contra_eqT (cD); rewrite -ltnNge eqn_leq negb_and -ltnNge => F5.
apply/orP;left; rewrite (sum_roots_order faceI).
suff bound : {in froots (@face D), forall x, 3 < arity x}.
{ apply: leq_trans (leq_sum _ bound) ; rewrite sum_nat_const.
  have -> : #|froots (@face D)| = F by apply: eq_card => z; rewrite !inE andbT.
  by apply: (@leq_trans (5 * 4)); rewrite // leq_mul2r F5. }
move=> x _; rewrite ltn_neqAle (emb_arity3 emb_g simpleD) ?andbT 1?eq_sym.
- have/even_cycle_Knm := emb_face_cycle emb_g x.
  by apply: contraNneq; rewrite size_map size_orbit => ->.
- move=> y. exact: leq_trans (deg_Knm _).
Qed.


(* TOTHINK: Finish or remove 

(** We show that every simple graph without isolated vertices can be
represented by a (plain) hypermap. This is mostly a sanity check, no
part of the proof relies in this construction *)

Module ExampleEmbedding.
Section Ex.
Variables (G : sgraph). 

Definition edart := { p : G * G | p.1 -- p.2 }.

Let swap (p : G * G) := (p.2,p.1).

Lemma eedge_proof (e : edart) : (swap (val e)).1 -- (swap (val e)).2.
Proof. case: e => /= [x y]; by rewrite sgP. Qed.

Definition eedge (e : edart) : edart := Sub (swap (val e)) (eedge_proof e).

Lemma eedgeI : injective eedge.
Proof. 
move => [[x y] /= [xy]] [[x' y'] /= [xy']]; case => ? ?. by apply: val_inj; subst.
Qed.

Let N (p : edart) : seq edart := enum [pred q | (val p).1 == (val q).1].

Let mem_N (x y : edart) : y \in N x = ((val x).1 == (val y).1).
Proof. by rewrite mem_enum inE. Qed.

Let Nxx x : x \in N x. Proof. by rewrite mem_N. Qed.

Definition enode (p : edart) : edart := next (N p) p.

Lemma enodeI : injective enode.
Proof. 
move => p1 p2 E. rewrite /enode in E.
suff S : N p1 = N p2.
{ move: E. rewrite S. apply/can_inj/prev_next. exact: enum_uniq. }
suff S: N p1 =i N p2 by apply: eq_enum => z; rewrite -mem_enum S mem_enum.
have V x : (val x).1 = (val (next (N x) x)).1 by apply/eqP; rewrite -mem_N mem_next.
have P : (val p1).1 == (val p2).1 by rewrite V E eq_sym -mem_N mem_next Nxx.
by move => z; rewrite !mem_N (eqP P).
Qed.

Definition eface : edart -> edart := finv enode \o finv eedge.

Lemma emb_can3 : cancel3 eedge enode eface.
Proof. 
move => x; rewrite /eface /= finv_f ?f_finv //; [exact: enodeI|exact: eedgeI].
Qed.

Definition default_embedding := Hypermap emb_can3.

Definition efun (e : default_embedding) : G := (val e).1.

Let cnodeN (d1 d2 : default_embedding) : cnode d1 d2 = (d2 \in N d1).
have fcN d : fcycle (next (N d)) (N d) by apply/cycle_next/enum_uniq.
apply/idP/idP.
+ case/connectP => p; elim: p d1 => /= [d1 _ -> //|d p IHp d1 /andP [nd1 pth_p] lst_p].
  have {pth_p lst_p IHp} IH := IHp _ pth_p lst_p.
  admit. (* same as above *)
+ admit.
Admitted.

Hypothesis no_iso : forall x : G, exists y : G, x -- y.

Lemma efun_emb : embedding efun.
Proof.
split.
- apply/plainP => [[[x y] H] _];split; first exact: val_inj.
  rewrite -val_eqE /=. apply: contraTneq H => [[-> _]]. by rewrite /= sgP.
- move => x; have [y xy] := no_iso x. 
  apply/mapP; exists (Sub (x,y) xy) => //. by rewrite mem_enum.
- move => d1 d2. by rewrite cnodeN mem_N.
- move => [[x y] /= xy] [[x' y'] /= xy']; rewrite /adjn /efun /=.
  apply/exists_inP/idP => [[[[z z'] /= zz']]|xx'].
  + by rewrite !inE !cnodeN !mem_N /= => /eqP-> /eqP->.
  + exists (Sub (x,x') xx'); by rewrite inE cnodeN mem_N.
Qed.

End Ex.
End ExampleEmbedding.
*)
