From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries bij digraph sgraph connectivity minor excluded.
From fourcolor Require Import hypermap geometry walkup color coloring combinatorial4ct.
Require Import set_tac.

Require Import hmap_ops smerge embedding arc K4plane.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(** These depend on [arc.v] which is pure mathcomp *)

Lemma connected_path0 (G : sgraph) (p : seq G) : 
  path0 (--) p -> sgraph.connected [set z in p].
Proof.
case: p => [|x p] => [_|/= pth_p]; first exact: connected0.
have -> : x::p = nodes (Path_of_path pth_p) by rewrite nodesE.
exact: connected_path.
Qed.

Lemma connected_arc (G : sgraph) (s : seq G) x1 x2 :
  ucycle (--) s -> x1 \in s -> x2 \in s -> x1 != x2 -> sgraph.connected [set z in arc s x1 x2].
Proof. by move=> *; exact/connected_path0/arc_path. Qed.

(** * Wagners Theorem (Main Direction) *)

(** This file contains the main argument for Wagner's theorem and, as a corollary, the four-colorability of ['K_5]-and ['K_3,3]-free graphs. However, the proof depends heavily on numberous other libraries:

- smerge: the operation of merging two vertices [x] and [y] in a simple graph (i.e., edge contraction if [x -- y]). This includes the proof that every 3-connected graph with at least 5 vertices has an edge whose contraction preserves 3-connectedness.
- embedding: the definition of plane embeddings using planar hypermaps and various constructions on plane embeddings, (e.g., deleting a vertex and obtaining its surrounding face or splitting a face by adding an edge).
- switch: various constructions on hypermaps underlying the constructions on plane embeddings and the proofs that they preserve planarity and have the desired properties (e.g., the right faces).
- K4plane: The plane embedding for ['K_4], providing the base case for Wagner's theorem.
- arc: various properties of the [arc] function (i.e., the one that selects arcs from cycles) that were needed and could be added to mathcomp.
- hycle: a proof that in a 2-connected (in the graph sense) hypermap, all the darts of every face cycle belong to different node cycles. This makes use of the Jordan curve theorem for hypermaps.

Further, we use some preexisting libraries
- sgraph: simple graphs and their isomporphisms
- minor: the definition of graph minors and various of their properties.
- connectivity: separators and separations. *)

(** ** Preliminaries *)


Definition kplanar G := ~ minor G ('K_3,3) /\ ~ minor G 'K_5.

Definition kplanar_minor G G' : minor G G' -> kplanar G -> kplanar G'.
Proof. 
move => G_G' [K1 K2]. 
split; [apply: contra_not K1|apply: contra_not K2]; exact: minor_trans G_G'.
Qed.

(** [prev] also refers to path reversal for packaged paths, which we don't use here *)
Local Notation prev := path.prev.
Local Notation mem_prev := path.mem_prev.

(** ** The 3-connected Case *)

(** Lemma 12 *)
Lemma wagner_no_cross (G : sgraph) (x y : G) (s : seq G) : 
  kplanar G -> ucycle (--) s ->
  x -- y -> x \notin s -> y \notin s ->
  let X := [seq z <- s | x -- z] in
  let Y := [seq z <- s | y -- z] in
  2 <= #|X| -> 2 <= #|Y| -> 
  exists2 z, z \in X & {subset Y <= rcons (arc s z (next X z)) (next X z) }. 
Proof.
move => [K33_free K5_free] ucycle_s xy xNs yNs X Y Xgt1 Ygt1.
have uniq_s := ucycle_uniq ucycle_s.
pose XY := [set z in X | z \in Y].
have sub_s : {subset XY <= s}. 
{ by move => z; rewrite !inE !mem_filter -!andbA=> /and3P [_ -> _]. }
have [X_sub_s Y_sub_s] : {subset X <= s} /\ {subset Y <= s}.
{ by split => u; rewrite mem_filter => /andP [_ ->]. }
have maxXY : #|XY| <= 2.
{ apply: contra_notT K5_free; rewrite leqNgt negbK => card_XY.
  (* TODO: simplify *)
  have [p []]:= subseq_of_subset (uniq_s) sub_s card_XY.
  move: p => [//|u1 [//|u2 [//|u3 [|//]]]] => P1 _ P2. 
  set u := _ :: _ in P1 P2.
  have: uniq u by apply: subseq_uniq P2 _. 
  rewrite /= !inE negb_or andbT -andbA [u1 == u3]eq_sym => /and3P [U1 U3 U2]. 
  have [N1 N2 N3] : [/\ next u u1 = u2, next u u2 = u3 & next u u3 = u1].
    by rewrite /= !eqxx !ifN // eq_sym. 
  pose phi (i : 'K_5) : {set G} := 
      match i with
      | Ordinal 0 _ => [set x]
      | Ordinal 1 _ => [set y]
      | Ordinal 2 _ => [set z in arc s u1 u2]
      | Ordinal 3 _ => [set z in arc s u2 u3]
      | Ordinal 4 _ => [set z in arc s u3 u1]
      | _ => set0
      end.
  apply: (@minor_of_rmap _ _ phi).
  have head_s := head_arc _ uniq_s.
  have [? ? ?] : [/\ u1 \in s, u2 \in s & u3 \in s].
  { by split;apply: (mem_subseq P2); rewrite !inE eqxx. }
  apply: ordered_rmap; first apply: ord_inj; split.
  - case;case => [|[|[|[|[|//]]]]] /= _; try exact: set10.
    all: match goal with |- is_true ([set _ in arc _ ?u1 _] != set0) => 
         by apply/set0Pn; exists u1; rewrite inE head_s end.
  - case;case => [|[|[|[|[|//]]]]] /= _; try exact: connected1.
    all: apply: connected_arc => //.
    all: by apply: (mem_subseq P2); rewrite !inE eqxx.
  - case;case => [|[|[|[|[|//]]]]] /= i; case;case => [|[|[|[|[|//]]]]] //= {i} _ _ _.
    1-7: rewrite disjoints1 ?in_set1 ?sg_edgeNeq //.
    1-3: by apply: contraNN xNs; rewrite inE; exact: mem_arc.
    1-3: by apply: contraNN yNs; rewrite inE; exact: mem_arc.
    all: repeat under eq_disjoint => z do rewrite inE //. 
    all: repeat under eq_disjoint_r => z do rewrite inE //. 
    1: rewrite -{1}N1 -{1}N2. 
    2: rewrite -{1}N1 -{3}N3.
    3: rewrite -{1}N2 -{1}N3.
    all: by apply: (arc_next_disjoint uniq_s) => //; rewrite 1?eq_sym // !inE eqxx.
  - have E z : z \in u -> (x -- z)*(y -- z). 
    { by move/P1;rewrite !inE !mem_filter => -/andP[/andP[? ?] /andP[? ?]]; split. }
    case;case => [|[|[|[|[|//]]]]] /= i; case;case => [|[|[|[|[|//]]]]] //= {i} _ _ _.
    1-7: apply/neighbor1P. 8-10: apply/neighborP.
    + by exists y; rewrite ?inE.
    + exists u1. by rewrite E ?inE ?eqxx. by rewrite inE head_s.
    + exists u2. by rewrite E ?inE ?eqxx. by rewrite inE head_s.
    + exists u3. by rewrite E ?inE ?eqxx. by rewrite inE head_s.
    + exists u1. by rewrite E ?inE ?eqxx. by rewrite inE head_s.
    + exists u2. by rewrite E ?inE ?eqxx. by rewrite inE head_s.
    + exists u3. by rewrite E ?inE ?eqxx. by rewrite inE head_s.
    + exists (last u1 (arc s u1 u2)), u2. by rewrite !inE last_mem head_s // arc_edge.
    + exists u1,(last u3 (arc s u3 u1)). by rewrite !inE last_mem head_s // sgP arc_edge.
    + exists (last u2 (arc s u2 u3)), u3. by rewrite !inE last_mem head_s // arc_edge. }
have no_cross : ~ exists x1 x2 y1 y2, [/\ x1 \in X, x2 \in X, y1 \in Y , y2 \in Y & subcycle [:: x1; y1; x2; y2] s].
{ apply: contra_not K33_free => -[x1] [x2] [y1] [y2] [x1X x2X y1Y y2Y sub]. 
  pose u := [:: x1; y1; x2; y2].
  pose phi (i : 'K_3,3) : {set G} := 
    match i with 
    | inl (Ordinal 0 _) => [set x]
    | inr (Ordinal 0 _) => [set y]
    | inl (Ordinal 1 _) => [set z in arc s y1 x2]
    | inl (Ordinal 2 _) => [set z in arc s y2 x1]
    | inr (Ordinal 1 _) => [set z in arc s x1 y1]
    | inr (Ordinal 2 _) => [set z in arc s x2 y2]
    |  _ => set0 
    end.
  suff: minor_rmap phi by apply minor_of_rmap.
  have head_s := head_arc _ uniq_s.
  have xz z : z \in X -> x -- z by rewrite !mem_filter => /andP[-> _].
  have yz z : z \in Y -> y -- z by rewrite !mem_filter => /andP[-> _].
  have : uniq u. apply: subcycle_uniq sub _. apply: ucycle_uniq ucycle_s.
  rewrite /u /= !inE !negb_or -!andbA andbT => /and5P[? ? ? ? /andP [? ?]].
  have u_sub_s := mem_subcycle sub.
  apply: ordered_rmap; first exact: pickle_Knn_inj; split.
  - case; case; case => [|[|[|//]]] /= _; try exact: set10.
    all: match goal with |- is_true ([set _ in arc _ ?u1 _] != set0) => 
         apply/set0Pn; exists u1; rewrite inE head_s // 1?eq_sym // end.
    all: by apply: u_sub_s; rewrite !inE eqxx.
  - case; case; case => [|[|[|//]]] /= _; try exact: connected1.
    all: apply: connected_arc; rewrite // 1?eq_sym //.
    all: by apply: u_sub_s; rewrite !inE eqxx.
  - case; case; case => [|[|[|//]]] /= i; case; case; case => [|[|[|//]]] //= {i} _ _ _.
    all: rewrite ?disjoints1 ?[[disjoint _ & [set _]]]disjoint_sym ?disjoints1 ?inE.
    3: by rewrite sg_edgeNeq.
    all: try solve [apply: contraNN xNs; apply: mem_arc].
    all: try solve [apply: contraNN yNs; apply: mem_arc].
    all: apply: (arc_subcycle_disjoints uniq_s sub). 
    all: by rewrite ?inE /= ?eqxx // ?ifN // 1?eq_sym.    
  - case; case; case => [|[|[|//]]] /= i; case; case; case => [|[|[|//]]] //= {i} _ _ _.
    4,7 : rewrite neighborC.
    1-5 : apply/neighbor1P. 
    6-9: apply/neighborP.
    + by exists y; rewrite ?inE.
    + by exists x1; rewrite ?xz // inE head_s // 1?eq_sym // u_sub_s ?inE ?eqxx. 
    + by exists x2; rewrite ?xz // inE head_s // 1?eq_sym // u_sub_s ?inE ?eqxx.
    + by exists y1; rewrite ?yz // inE head_s // 1?eq_sym // u_sub_s ?inE ?eqxx.
    + by exists y2; rewrite ?yz // inE head_s // 1?eq_sym // u_sub_s ?inE ?eqxx.
    + exists y1, (last x1 (arc s x1 y1)). 
      by rewrite sgP !inE last_mem head_s ?arc_edge // u_sub_s ?inE ?eqxx.
    + exists (last y1 (arc s y1 x2)), x2. 
      by rewrite !inE last_mem head_s ?arc_edge // u_sub_s ?inE ?eqxx.
    + exists (last y2 (arc s y2 x1)), x1.
      by rewrite !inE last_mem head_s ?arc_edge // 1?eq_sym // u_sub_s ?inE ?eqxx.
    + exists y2, (last x2 (arc s x2 y2)). 
      by rewrite sgP !inE last_mem head_s ?arc_edge // 1?eq_sym // u_sub_s ?inE ?eqxx. }
suff: ~ forall x, x \in X -> exists2 y, y \in Y & y \notin rcons (arc s x (next X x)) (next X x).
{ move => NC; apply/exists_inPP => [u|]; first exact/allP. 
  apply: contra_notT NC => /exists_inPn H u u_X.
  have [v v_Y ?] := allPn (H _ u_X); by exists v. }
apply: contra_not no_cross => not_contained.
have [uniq_X uniq_Y] : uniq X /\ uniq Y by rewrite filter_uniq // filter_uniq.
have subcycle_X : subcycle X s by rewrite subseq_subcyle // filter_subseq.
have size_X : 2 <= size X by rewrite -(card_uniqP _).
have [/allP Y_sub_X |/allPn [y1 y1_Y y1NX]] := (boolP (all (fun z => z \in X) Y)).
- (* case where [Y \subset X] *)
  have [y1 [y2 [defY y1Dy2]]]: exists y1 y2, Y = [:: y1; y2] /\ y1 != y2.
  { suff: size Y == 2.
      by move: uniq_Y; destruct Y as [|y1 [|y2 [|]]]; rewrite //= inE andbT; exists y1,y2.
   rewrite eqn_leq -(card_uniqP _) // Ygt1 andbT.
   apply: leq_trans maxXY. apply: subset_leq_card. 
   apply/subsetP => y1 inY. by rewrite inE Y_sub_X inY . }
  have {defY} eqY : Y =i [set y1;y2] by move=>?; rewrite defY !inE.
  have xDy xi yi : xi \notin Y -> yi \in Y -> xi == yi = false.
    by move=> xiNY; apply: contraTF => /eqP<-.
  gen have H,Py1 : y1 y2 eqY y1Dy2 / prev X y1 \notin Y. 
  { have ? : y1 \in X by rewrite Y_sub_X // eqY !inE eqxx.
    apply/negP => py_Y. 
    have E : prev X y1 = y2.
      by apply: contraTeq py_Y => C; rewrite eqY !inE negb_or C eq_sym prev_neq.
    move/Y_sub_X : (py_Y) => /not_contained [z z_Y]. 
    rewrite mem_rcons inE E negb_or => /andP[zDny2]. 
    move: z_Y; rewrite eqY => /set2P [z_y1|->]. 
    - by subst z; rewrite -E next_prev ?eqxx in zDny2. 
    - by rewrite head_arc // ?next_neq // ?X_sub_s // ?mem_next Y_sub_X // eqY !inE eqxx. }
  have := H y2 y1; rewrite setUC eq_sym => /(_ eqY y1Dy2) => {H} Py2.
  have [y1_X y1_Y y2_X y2_Y] : [/\ y1 \in X, y1 \in Y, y2 \in X & y2 \in Y]. 
    by rewrite !Y_sub_X !eqY !inE !eqxx.
  pose x1 := prev X y1; pose x2 := prev X y2. rewrite -/x1 -/x2 in Py1 Py2.
  exists x1, x2, y1, y2; rewrite !path.mem_prev; split => //. 
  apply: subcycle_trans subcycle_X. 
  have x1Dx2 : x1 != x2. 
  { apply:contra_neq y1Dy2 => eq_x.
    by rewrite -[y1](next_prev uniq_X) -/x1 eq_x next_prev. }
  have [x1_X x2_X] : x1 \in X /\ x2 \in X by rewrite !path.mem_prev !Y_sub_X.
  have [i X1 X2 arc1 arc2 rot_i] := rot_to_arc uniq_X x1_X x2_X x1Dx2.
  rewrite -(subcycle_rot_r i) rot_i; apply: subseq_subcyle. 
  rewrite /= eqxx -cat1s; apply: cat_subseq; rewrite /= ?eqxx sub1seq.
  + have := next_mem_arc uniq_X x1_X x2_X x1Dx2. 
    by rewrite next_prev // mem_rcons -arc1 !inE ![y1 == _]eq_sym !xDy.
  + rewrite eq_sym in x1Dx2; have := next_mem_arc uniq_X x2_X x1_X x1Dx2. 
    by rewrite next_prev // mem_rcons -arc2 !inE ![y2 == _]eq_sym !xDy. 
- (* case where [y1 \in Y :\: X] *)
  have y1_s : y1 \in s by move: y1_Y; rewrite mem_filter => /andP[_ ->].
  have [x1 x1_X x1_y1] := subcycle_get_arc y1_s uniq_s subcycle_X size_X.
  have [y2 y2_Y foo] := not_contained _ x1_X.
  set x2 := next X x1 in x1_y1 foo. 
  exists x1,x2,y1,y2. rewrite !mem_next; split => //.
  have [x1_s x2_s] : x1 \in s /\ x2 \in s by rewrite !X_sub_s // mem_next.
  have x1Dx2 : x1 != x2 by exact: next_neq.
  have [i s1 s2 def_s1 def_s2 rot_s] := rot_to_arc uniq_s x1_s x2_s x1Dx2.
  rewrite -(subcycle_rot_r i) rot_s subseq_subcyle //= eqxx -cat1s.
  apply: cat_subseq; rewrite /= ?eqxx sub1seq.
  + move: x1_y1. rewrite -def_s1 inE [_ == _](_ : _ = false) //.
    by apply: contraNF y1NX => /eqP ->.
  + have:= Y_sub_s _ y2_Y; rewrite -(mem_rot i) rot_s -cat_cons -[x2 :: _]cat1s.
    by rewrite catA cats1 def_s1 mem_cat (negbTE foo).
Qed.

(** Proposition 7 *)
Proposition wagner3 (G : sgraph) : 
  3.-connected G -> kplanar G -> inhabited (plane_embedding G).
Proof.
elim/card_ind : G => G IH conn_G kplanar_G. 
have [le_5_G|le_G_4] := (ltnP 4 #|G|); last first. 
{ suff i : diso 'K_4 G. 
    by exists; apply: diso_plane_embedding i; apply: K4_plane_emb.
  have/eqP -> : 4 == #|G| by rewrite eqn_leq le_G_4 (proj1 conn_G).
  by apply/diso_sym/diso_Kn; apply: kconnected_complete le_G_4. }
have [x [y [xy conn_G1]]] := contract_three_connected le_5_G conn_G.
set G1 := smerge2 G x y in conn_G1.
have kplanar_G1 := kplanar_minor (smerge2_minor xy) kplanar_G.
have [|g1] := IH G1 _ conn_G1 kplanar_G1.
  by rewrite card_sig [X in _ < X](@cardD1x _ _ y).
wlog simple_g1 : g1 / simple_hmap (emb_map g1).
{ move => W; have [g1'] := simple_embedding g1; exact: W. }
have xDy : x != y by rewrite (sg_edgeNeq xy).
pose v_xy : G1 := Sub x xDy.
pose G2 := induced [set~ v_xy].
have conn_G2 : 2.-connected G2 by apply/konnected_del1.
have G2Dx (u : G2) : val2 u != x. 
{ by apply: contraTneq (valP u); rewrite !inE negbK -val_eqE -/(val2 _) => ->. }
have conn2_G1 : 2.-connected G1 by apply: (@kconnectedW 1); rewrite addn1.
pose g2 := @del_vertex_plane_embedding _ g1 v_xy conn2_G1 simple_g1.
have := @del_vertex_neighbor_face G1 g1 v_xy conn2_G1 simple_g1.
rewrite -/G2 -/g2; case => [s2 face_s2 neighb_s2]. 
pose X : seq G2 := [seq z <- s2 | x -- val2 z].
pose Y : seq G2 := [seq z <- s2 | y -- val2 z].
have uniq_s2 : uniq s2 by apply:face_uniq face_s2.
have uniq_X : uniq X by apply: filter_uniq.
have uniq_Y : uniq Y by apply: filter_uniq.
have degG (z : G) : 3 <= #|N(z)| by apply: kconnected_degree.
have inG2P u (uDx : u != x) (uDy : u != y) : Sub u uDy \in [set~ v_xy].
  by rewrite !inE -val_eqE.
have eq_X : val2 @: X =i N(x) :\ y.
{ move=> z; rewrite !inE. apply/imsetP/andP => [[z0 z0X -> {z}]|[zDy xz]].
    move: z0X; rewrite mem_filter => /andP[-> _]; by rewrite (valP (val z0)).
  have zDx : z != x by apply: contraTneq xz => ->; rewrite sgP.
  exists (Sub (Sub z zDy) (inG2P _ zDx zDy)) => //. 
  rewrite /X mem_filter /= xz /= -(@mem_map G2 G1 val) //=.
  by apply: neighb_s2; rewrite /= inE /edge_rel/= eqxx zDx sg_sym xz. }
have sizeX : 1 < size X. 
{ rewrite -(card_uniqP _) // -!(card_imset _ val_inj) -imset_comp.
  rewrite (eq_card eq_X). apply: leq_trans (leq_cardsD1 _ _). 
  rewrite -ltnS; apply: leq_trans (degG x) _. exact: leqSpred. }
have eq_Y : val2 @: Y =i N(y) :\ x.
{ move=> z; rewrite !inE. apply/imsetP/andP => [[z0 z0X -> {z}]|[zDx yz]].
    by move: z0X; rewrite mem_filter => /andP[-> _].
 have zDy : z != y by apply: contraTneq yz => ->; rewrite sgP.
 exists (Sub (Sub z zDy) (inG2P _ zDx zDy)) => //. 
 rewrite /Y mem_filter /= yz -(@mem_map G2 G1 val) //.
 by apply: neighb_s2; rewrite /= inE /edge_rel/= eqxx zDx [z -- y]sgP yz orbT. }
have sizeY : 1 < size Y. 
{ rewrite -(card_uniqP _) //; rewrite -!(card_imset _ val_inj) -imset_comp.
  rewrite (eq_card eq_Y). apply: leq_trans (leq_cardsD1 _ _). 
  rewrite -ltnS; apply: leq_trans (degG y) _. exact: leqSpred. }
(* in particular, we can now get a default vertex in G2 for free *)
have v2 : G2 by move: sizeX; destruct X. 
pose inG2 (u : G) : G2 := insubd v2 (insubd v_xy u).
have inG2E u (uDx : u != x) (uDy : u != y) : inG2 u = Sub (Sub u uDy) (inG2P _ uDx uDy) :> G2.
{ rewrite /inG2 !insubdT ?inG2P // => p. exact: val_inj. }
have inG2K (u : G2) : inG2 (val (val u)) = u. 
{ rewrite inG2E ?(valP (val u)) // ?G2Dx // => p q. by do 2 apply: val_inj. }
(* Prove that Y2 is contained in of of the arcs spanned by X1 *)
have [x1 x1_X Y_segment] : exists2 x1, 
  x1 \in X & {subset Y <= rcons (arc s2 x1 (next X x1)) (next X x1) }. 
{ pose s := [seq val x | x <- [seq val x | x <- s2]].
  have uniq_s : uniq s by rewrite !map_inj_uniq //; exact: val_inj.
  have xNs : x \notin s. 
   by apply/negP => /mapP [? /mapP [x0] _ ->] /eqP; apply/negP; rewrite eq_sym G2Dx.
  have yNs : y \notin s. 
  { apply/negP => /mapP [? /mapP [y0 _ ->]] /eqP. 
    by apply/negP; rewrite eq_sym (valP (val y0)). }
  have ucycle_s : ucycle (--) s. 
  { apply: smerge2_ucycle xNs. 
    rewrite -ucycle_induced /ucycle uniq_s2 andbT. exact: sface_cyle face_s2. }
  pose X' := [seq z <- s | x -- z]. 
  pose Y' := [seq z <- s | y -- z].
  have size_X' : 2 <= #|X'|. 
  { suff -> : X' = map val (map val X). 
      by rewrite (card_uniqP _) ?map_inj_uniq // !size_map.
    by rewrite /X'/s/X !filter_map. }
  have size_y' : 2 <= #|Y'|. 
  { suff -> : Y' = map val (map val Y). 
      by rewrite (card_uniqP _) ?map_inj_uniq // !size_map.
    by rewrite /Y'/s/Y !filter_map. }
  (* Central Lemma on excluded minors *)
  have [z Z1 Z2] := wagner_no_cross kplanar_G ucycle_s xy xNs yNs size_X' size_y'.
  rewrite -/X' -/Y' in Z2.
  move: Z1; rewrite mem_filter => /andP [xz z_s].
  have zDy : z != y by apply: contraTneq z_s => ->.
  have zDv : (Sub z zDy : G1) \in [set~ v_xy] by rewrite !inE -val_eqE /= eq_sym sg_edgeNeq.
  pose x1 := Sub (Sub z zDy) zDv : G2.
  exists x1. 
  - rewrite mem_filter /= xz //=. 
    by move: z_s; rewrite -[z]/(val (val x1)) !mem_map. 
  - move => u u_Y. 
    rewrite -(@mem_map _ _ val2); last exact: val2_inj.
    rewrite map_rcons map_arc 1?map_comp -/s -!/(val2 _); last exact: val2_inj. 
    rewrite -next_map; last exact: val2_inj. 
    have -> : map val2 X = X' by rewrite /X' /s !filter_map /= -map_comp.
    apply: Z2. move: u_Y. rewrite !mem_filter => /andP[->] /=.
    by rewrite /s !mem_map. }
set x2 := next X x1 in Y_segment.
have x2_X : x2 \in X by rewrite mem_next.
have x1Dx2 : x1 != x2 by apply next_neq.
(* Reconstruct [G] (up to iso) from [G2] by first adding back [x] and
then adding back [y], while showing that this preserves the planarity
(of G2) *)
have [x1_s1 x2_s2] : x1 \in s2 /\ x2 \in s2. 
  split; [exact: sub_filter x1_X|exact: sub_filter x2_X].
have [] := @plane_add_node' _ g2 x2 x1 s2 [set z in X] => //.
- by rewrite eq_sym.
- by move=> z; rewrite inE; apply: arc_remainder => //; exact: filter_subseq.
- by rewrite inE. 
- by rewrite inE. 
- move => g' face_g'.
  set G' := add_node G2 _ in g' face_g'.
  set s2' := (Some _ :: _ : seq G') in face_g'.
  pose Y' : {set G'} := None |: Some @: [set z in Y].
  have [||g''] := @plane_add_node_simple G' g' _ Y' None _ face_g'.
  + by rewrite in_setU1 eqxx.
  + move=>z; rewrite !inE => /predU1P [->|/imsetP [z0]]; first by rewrite eqxx.
    rewrite !inE => /Y_segment.
    rewrite mem_rcons inE => /predU1P [-> -> //|z_arc ->]; first by rewrite eqxx.
    rewrite mem_map ?z_arc //; exact: Some_inj.
  + suff i: diso (add_node G' Y') G by exists; apply: diso_plane_embedding g'' i.
    set G'' := add_node _ _.
    pose fwd (x0 : G'') : G := 
      if x0 isn't Some z0 then y else
      if z0 isn't Some z then x else val2 z.
    pose bwd (x0 : G) : G'' := 
      if x0 == y then None else 
      if x0 == x then Some None else Some (Some (inG2 x0)).
    have can_fwd : cancel fwd bwd.
    { move => [[x0|]|]; rewrite /bwd ?eqxx ?(negPf xDy) //.
      by rewrite (negbTE (valP (val x0))) (negbTE (G2Dx x0)) inG2K. }
    have can_bwd : cancel bwd fwd. 
    { move=> u. rewrite /fwd/bwd. 
      have [-> //|yDu] := eqVneq u y; have [-> //|xDu] := eqVneq u x.
      by rewrite inG2E. }
    have dhom_fwd : is_dhom fwd. 
    { move => [[u|]|] [[v|]|] //=.
      - move => uv. by rewrite (@smerge2_val_edge _ x y) ?induced_val_edge //; exact: G2Dx.
      - by rewrite {1}/edge_rel/={1}/edge_rel/= inE mem_filter sgP => /andP[-> _].
      - by rewrite {1}/edge_rel/= !(inE, inj_imset) // orFb mem_filter sgP => /andP[-> _].
      - by rewrite {1}/edge_rel/={1}/edge_rel/= inE mem_filter => /andP[-> _].
      - by rewrite {1}/edge_rel/= !(inE, inj_imset) // orFb mem_filter => /andP[-> _].
      - by rewrite [y -- x]sgP. }
    have inG2Y u : u != x -> u != y -> u -- y -> inG2 u \in Y.
    { move=> uDx uDy uy. rewrite inG2E -!(@inj_imset _ _ val) // -imset_comp eq_Y /=.
      by rewrite !inE uDx sgP. }
    have inG2X u : u != x -> u != y -> u -- x -> inG2 u \in X.
    { move=> uDx uDy uy. rewrite inG2E -!(@inj_imset _ _ val) // -imset_comp eq_X /=.
      by rewrite !inE uDy sgP. }
    have dhom_bwd : is_dhom bwd. 
    { move => u v uv; rewrite /bwd. 
      have [?|uDy] := eqVneq u y; first subst u. 
        have [E|vDy] := eqVneq v y; first by rewrite E sgP in uv.
        have [?|vDx] := eqVneq v x; first by rewrite /edge_rel/= !inE eqxx.
        by rewrite /edge_rel/= inE inj_imset // inE inG2Y 1?sgP.
      have [?|uDx] := eqVneq u x;first subst u. 
        have [E|vDx] := eqVneq v x; first by rewrite E sgP in uv.
        have [?|vDy] := eqVneq v y; first by rewrite /edge_rel/= !inE eqxx.
        by rewrite /edge_rel/= /edge_rel/= inE inG2X 1?sgP.
      have [?|vDy] := eqVneq v y; first subst v. 
        by rewrite /edge_rel/= inE inj_imset // inE inG2Y.
      have [?|vDx] := eqVneq v x; first subst v.
        by rewrite /edge_rel/= /edge_rel/= inE inG2X.
      rewrite /edge_rel /= /edge_rel/= /edge_rel/=. 
      rewrite induced_val_edge. rewrite /edge_rel/= !inG2E /=.
      by rewrite -(@smerge2_val_edge _ x y). }
    exact: (@Diso _ _ (Bij can_fwd can_bwd) dhom_fwd dhom_bwd).
Qed.




(** ** The General Case *)


Lemma vertex_plane_embedding (G : sgraph) (V1 V2 : {set G}) (x : G) :
  V1 :&: V2 = [set x] -> separation V1 V2 ->
  plane_embedding (induced V1) -> plane_embedding (induced V2) ->
  inhabited (plane_embedding G).
Proof.
move => capV sepV g1 g2.
have [xV1 xV2] : x \in V1 /\ x \in V2 by split; set_tac.
pose G1 := induced V1; pose G2 := induced V2.
have : diso (smerge2 (G1 ∔ G2) (inl (Sub x xV1)) (inr (Sub x xV2))) G.
  exact: diso_separation1.
apply: diso_plane_embedding_inh. 
apply: smerge_plane_embedding_disconnected.
  by apply: union_plane_embedding.
exact: sjoin_disconnected.
Qed.

(** Lemma 31 *)
Lemma edge_plane_embedding (G : sgraph) (V1 V2 : {set G}) (x y : G) :
  x -- y -> V1 :&: V2 = [set x; y] -> separation V1 V2 ->
  plane_embedding (induced V1) -> plane_embedding (induced V2) ->
  inhabited (plane_embedding G).
Proof.
move => xy capV sepV.
have [xV1 xV2 yV1 yV2] : [/\ x \in V1, x \in V2, y \in V1 & y \in V2].
  by split; set_tac.
have xDy : x != y by rewrite (sg_edgeNeq xy).
set G1 := induced V1; set G2 := induced V2; move => g1 g2.
set G12 := (G1 ∔ G2)%sg.
have g12 := union_plane_embedding g1 g2.
pose x1 : G12 := inl (Sub x xV1); pose x2 : G12 := inr (Sub x xV2).
pose y1 : G12 := inl (Sub y yV1); pose y2 : G12 := inr (Sub y yV2).
have xy1 : x1 -- y1 by [].
have yx2 : y2 -- x2 by rewrite sgP.
have nc_x1_x2 : ~~ connect (--) x1 x2 by rewrite sjoin_disconnected.
have [xs face_xs] := plane_emb_face g12 xy1.
have [ys face_ys] : exists ys, sface g12 (x2 :: rcons ys y2).
{ have [ys face_ys] := plane_emb_face g12 yx2. 
  by exists ys; move/(rot_face 1) : face_ys; rewrite rot1_cons. } 
pose Gm := smerge2 G12 x1 x2.
have := smerge_plane_embedding_disconnected' nc_x1_x2 face_xs face_ys.
rewrite -/Gm => -[g' [s' [face_s' eq_val_s]]].
have y1Gm : y1 != x2 by [].
have y2Gm : y2 != x2 :> G12 by rewrite (inj_eq inr_inj) eq_sym -val_eqE.
pose y1' : Gm := Sub y1 y1Gm.
pose y2' : Gm := Sub y2 y2Gm.
pose Gm' := smerge2 Gm y1' y2'.
have [y1s' y2s'] : y1' \in s' /\ y2' \in s'. 
{ by rewrite -!(mem_map val_inj) !eq_val_s // !(inE,mem_cat,mem_rcons) /= !eqxx. }
have y1Dy2' : y1' != y2' by rewrite -val_eqE. 
have y1Ny2' : ~~ y1' -- y2'. 
{ by rewrite /edge_rel/= eq_sym (inj_eq inl_inj) -val_eqE /= (negbTE xDy). }
have : diso Gm' G by exact: diso_separation2.
apply: diso_plane_embedding_inh.
exact: smerge_plane_embedding_face face_s'.
Qed.

Lemma kplanar_add_edge (G : sgraph) (V1 V2 : {set G}) (x y : G) : 
  x != y -> proper_separation V1 V2 -> V1 :&: V2 = [set x; y] ->
  smallest vseparator (V1 :&: V2) -> kplanar G -> 
  kplanar (@induced (add_edge G x y) V1) /\ kplanar (@induced (add_edge G x y) V2).
Proof.
move => xDy psepV capVxy ssepV [K33G K5G].
have exV1 := add_edge_separation_excluded xDy psepV capVxy ssepV.
split; first by split; apply: exV1.
move/proper_separation_symmetry in psepV.
rewrite [V1 :&: V2]setIC in capVxy ssepV.
have exV2 := add_edge_separation_excluded xDy psepV capVxy ssepV.
by split; apply: exV2.
Qed.

Lemma separation_no_isolated (G: sgraph) (V1 V2 : {set G}) : 
  proper_separation V1 V2 -> smallest vseparator (V1 :&: V2) ->
  no_isolated G -> no_isolated (induced V1) /\ no_isolated (induced V2).
Proof.
move=> sepV smallV no_iso. 
wlog suff I : V1 V2 sepV smallV / no_isolated (induced V1).
{ move: (sepV) (smallV) => /proper_separation_symmetry ?; rewrite setIC => ?.
  by split; apply: I; eassumption. }
move=> x; have [xV2|xNV2] := boolP (val x \in V2).
- have xV : val x \in V1 :&: V2 by rewrite inE xV2 (valP x).
  have [y [? [yNV2 _ xy _]]] := svseparator_neighbours sepV smallV xV.
  have yV1 : y \in V1 by apply: sep_inL (sepV.1) yNV2. 
  by exists (Sub y yV1). 
- have [y xy] := no_iso (val x).
  suff yV1 : y \in V1 by exists (Sub y yV1).
  by apply: contraTT xy => ?; rewrite sepV.1.
Qed.

(** Theorem 8 / Theorem 31 *)
Theorem Wagner (G : sgraph) :
  no_isolated G -> ~ minor G 'K_3,3 /\ ~ minor G 'K_5 -> inhabited (plane_embedding G).
Proof.
elim/card_ind : G => G IH no_iso.
have [largeG|smallG _] := ltnP 4 #|G|; last first.
  exact: small_planar smallG no_iso.
have [|[S lt3S sepS]] := @connectedVseparator G 3 (ltnW largeG).
  exact: wagner3.
wlog ssepS : S lt3S {sepS} / smallest vseparator S.
{ move=> W; have [B smallB] := ex_smallest (@vseparatorP G) sepS.
  apply: (W B) => //. apply: leq_trans lt3S. exact: smallB.2. }
have [V1 [V2 [psepV defS]]] := vseparator_separation ssepS.1.
have [|no_is1 no_iso2] := separation_no_isolated psepV _ no_iso. 
  by rewrite -defS.
move=> kplG.
have [/cards2P[x[y [xDy Sxy]]]|SN2] := boolP (#|S| == 2).
{ (* minimal 2-separator, need xy-edge as marker *)
  pose G1 := @induced (add_edge G x y) V1; pose G2 := @induced (add_edge G x y) V2.
  have [ltG1 ltG2] : #|G1| < #|G| /\ #|G2| < #|G|.
    by rewrite !card_sig !(proper_separation_card psepV).
  have psepV' : @proper_separation (add_edge G x y) V1 V2.
    by apply: add_edge_proper_separation psepV; rewrite -defS Sxy !inE eqxx.
  have [no_iso1' no_iso2'] : no_isolated G1 /\ no_isolated G2.
  { apply: separation_no_isolated => //; last exact: add_edge_no_isolated.
    by rewrite -defS; apply: add_edge_smallest_vseparator; rewrite // Sxy !inE eqxx. }
  have [kplanar1 kplanar2] : kplanar G1 /\ kplanar G2.
    by apply: kplanar_add_edge; rewrite // -?defS.
  case: (IH G1) => // g1; case (IH G2) => // g2.
  have sepV : @separation (add_edge G x y) V1 V2.
    by apply: add_edge_separation psepV.1; rewrite -defS Sxy !inE eqxx.
  have [] : inhabited (plane_embedding (add_edge G x y)).
  { apply: (@edge_plane_embedding (add_edge G x y) _ _ x y) sepV g1 g2.
      by rewrite /edge_rel/= !eqxx xDy.
    by rewrite -defS. }
  exact: subgraph_plane_embedding (add_edge_subgraph _ _) no_iso. }
pose G1 := induced V1; pose G2 := induced V2.
have [ltG1 ltG2] : #|G1| < #|G| /\ #|G2| < #|G|.
  by rewrite !card_sig !(proper_separation_card psepV).
have [[g1] [g2]] : inhabited (plane_embedding G1) /\ inhabited (plane_embedding G2).
  split; apply: IH => //; apply: kplanar_minor kplG; exact: induced_minor.
have [/cards1P[x Sx]|SN1] := boolP (#|S| == 1).
{ (* minimal 1-separator *) 
  apply: vertex_plane_embedding (psepV.1) g1 g2; rewrite -defS; exact: Sx. }
have {lt3S SN1 SN2} S0  : S = set0.
{ apply/cards0_eq/eqP; move: lt3S. 
  by rewrite 4!(ltnS,leq_eqVlt) (negPf SN1) (negPf SN2) ltnS leqn0. }
constructor; apply: diso_plane_embedding (@diso_separation _ V1 V2 _ _).
- exact: union_plane_embedding.
- exact: psepV.1.
- by rewrite -setI_eq0 -defS S0.
Qed.

Print Assumptions Wagner.

(** ** Structural Four-Color Theorem *)

(** Turn the fixed four-element [color] type of the four-color theorem into a [finType] *)
Section color.
Let Cs := [:: Color0; Color1 ; Color2; Color3].
Lemma color_enumP : Finite.axiom Cs. Proof. by case. Qed.
Lemma color_pcanP : cancel (index^~ Cs) (nth Color0 Cs). Proof. by case. Qed.
Definition color_countMixin : Countable.mixin_of color := CanCountMixin color_pcanP.
Definition color_choiceMixin := Countable.ChoiceMixin color_countMixin.
Canonical color_choiceType := ChoiceType color color_choiceMixin.
Canonical color_countType := CountType color color_countMixin.
Definition color_finMixin := Finite.EnumMixin color_enumP. 
Canonical color_finType := FinType color color_finMixin.
End color.

Lemma adjn_color (D : hypermap) (k : D -> color) x y : 
  graph_coloring k -> adjn x y -> k x != k y.
Proof.
  case => inv_edge inv_node /exists_inP [z Z1 Z2].
  have -> : k x = k z by apply: fconnect_invariant Z1.
  have -> : k y = k (edge z) by apply: fconnect_invariant Z2.
  move: (inv_edge z) => /= E. by rewrite eq_sym E.
Qed.

Corollary graph_four_color (D : hypermap) : 
  loopless D -> planar D -> graph_four_colorable D.
Proof. 
  rewrite -four_colorable_dual -planar_dual -bridgeless_dual => ? ?.
  exact: four_color_hypermap.
Qed.

Definition sgraph_coloring (G : sgraph) (C : finType) (k : G -> C) := 
  forall x y : G, x -- y -> k x != k y.

Lemma coloring_of_embedding (G : sgraph) (D : hypermap) (f : D -> G) (k : D -> color) : 
  embedding f -> graph_coloring k -> exists k' : G -> color, sgraph_coloring k'.
Proof.
  move => emb_f [inv_edge inv_node]. exists (k \o emb_inv emb_f).
  move => x y /=. set dx := emb_inv _ x; set dy := emb_inv _ y.
  rewrite -[x](_ : f dx = x) -1?[y](_ : f dy = y); try exact: f_iinv.
  rewrite -emb_edge //. exact: adjn_color.
Qed.

(** Note that neither [emb_plain] nor [emb_vertex] is required to
prove the four-color theorem for simple graphs.

[emb_plain] : it doesn't matter whether vertices are adjecent due to
being on a large multiedge or due to different edges (and faces are
irrelevant, as long as the map is planar).

[emb_vertex] : if the map is planar even after collapsing vertices,
the original graph can still be colored. Conversely, when there are
two node cycles for a vertex, these are not adjecent (by [emb_edge])
and must both be adjacent to all node cycles representing their
neighborhood in [G]. Hence, one can pick any of the cycles
representing a vertex to obtain the coloring (using [emb_surj]). *)

(** Theorem 34 *)
Corollary sgraph_four_color (G : sgraph) : 
  kplanar G -> exists k : G -> color, sgraph_coloring k.
Proof.
move => kpl.
wlog no_iso : G kpl / no_isolated G; last first.
{ have [[D f emb_f planar_D]] := Wagner no_iso kpl.
  have loopless_D := emb_loopless emb_f.
  have [k col_k] := graph_four_color loopless_D planar_D.
  exact: coloring_of_embedding emb_f col_k. }
move=> W; pose A := [set x : G | [exists y, x -- y]].
have no_iso : no_isolated (induced A). 
{ move=> x'; have := valP x'; rewrite inE => /existsP [y xy].
  suff yA : y \in A by exists (Sub y yA).
  by rewrite !inE; apply/existsP; exists (val x'); rewrite sgP. }
have [|k col_k] := W _ _ no_iso.
  exact: kplanar_minor (induced_minor _) _.
pose k' (x : G) := 
  if boolP (x \in A) is AltTrue p then k (Sub x p) else Color0.
exists k'. move=> x y xy. rewrite /k' !altT ?inE => [||? ?].
- by apply/existsP; exists y.
- by apply/existsP; exists x; rewrite sgP.
- exact: col_k. 
Qed.

Fact card_color : #|color| = 4.
Proof. by rewrite cardT enumT unlock. Qed.
