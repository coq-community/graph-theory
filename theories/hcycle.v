From mathcomp Require Import all_ssreflect.

Require Import edone preliminaries digraph sgraph.
From fourcolor Require Import hypermap geometry jordan color coloring combinatorial4ct.
Require Import hmap_ops.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition kconnected_map (k : nat) (G : hypermap) := 
  k < fcard node G /\ 
  forall A : pred G, #|A| < k -> 
    {in [predC fclosure node A]&, forall x y, connect (restrict [predC fclosure node A] glink) x y}.

Lemma closed_connect (T : finType) (e : rel T) (A : pred T) : 
  closed e A -> {in A, subrel (connect e) (connect (restrict A e))}.
Proof.
move => clA x xA y.
case/connectP => p; elim: p x xA => [x _ _ -> //|z p IHp /= x xA /andP [xz pth_p] lst_p].
have zA: z \in A by rewrite -(clA _ _ xz).
by apply: connect_trans (IHp _ zA pth_p lst_p); apply:connect1; rewrite /= xA zA.
Qed.

Lemma in_connect_sym (T : finType) (e : rel T) (A : pred T) : 
  closed e A -> connect_sym e -> {in A&, connect_sym (restrict A e)}.
Proof. 
move => clA sym_e x y xA yA.
wlog suff : x y xA yA / connect (restrict A e) x y -> connect (restrict A e) y x.
{ by move => W; apply/idP/idP; apply: W. }
case/connectP => p; elim: p x xA => /= [x _ _ -> //| z p IHp x xA].
rewrite -!andbA => /and4P [_ zA x_z pth_p lst_p].
have {pth_p lst_p} IH := IHp _ zA pth_p lst_p. apply: connect_trans IH _.
have := (connect1 x_z); rewrite sym_e; exact: closed_connect.
Qed.

Lemma sub_restrict T (e1 e2 : rel T) (A : pred T) : 
  {in A&, subrel e1 e2} -> subrel (restrict A e1) (restrict A e2).
Proof. move => sub x y /=/andP[/andP [xA yA] xy]. by rewrite xA yA sub. Qed.

Lemma glinkN (G : hypermap) : subrel (frel node) (@glink G).
Proof. move => x y. by rewrite /glink /= => ->. Qed.

Lemma sub_node_clink {G : hypermap} : subrel (frel (finv node)) (@clink G).
Proof. move => x y /eqP <-. by rewrite /clink/= eqxx. Qed.

Lemma in_clink_glink (G : hypermap) (A : pred G) (plainG : plain G) : 
  fclosed node A -> {in A&, connect (restrict A clink) =2 connect (restrict A glink)}.
Proof.
move => clA x y xA yA. apply/idP/idP.
- case/connectP => [p]. elim: p x xA => [x xA _ -> //|z p IHp x xA /=].
  rewrite -!andbA => /and4P [_ zA xz pth_p lst_p]. 
  apply: connect_trans (IHp _ zA pth_p lst_p) => {pth_p lst_p}.
  case/clinkP : xz xA zA => [->|<-] => xA zA.
  + apply: connect_mono. apply: sub_restrict. apply: in2W. exact: glinkN.
    rewrite in_connect_sym // ?connect1 //=. exact: cnodeC.
  + by apply connect1; rewrite /= xA zA /glink/= eqxx.
- case/connectP => [p]. elim: p x xA => [x xA _ -> //|z p IHp x xA /=].
  rewrite -!andbA => /and4P [_ zA xz pth_p lst_p]. 
  apply: connect_trans (IHp _ zA pth_p lst_p) => {pth_p lst_p IHp}.
  gen have N,N': x z xA zA {xz} / node x == z -> connect (restrict A clink) x z.
  { move/eqP => E. rewrite -{}E in zA *. 
    apply: connect_mono. apply: sub_restrict. apply: in2W. exact: sub_node_clink.
    rewrite in_connect_sym // ?connect1 //= ?xA ?zA ?finv_f ?eqxx //.
    * move => u v /eqP <-. by rewrite (clA (finv node u) u) //= f_finv.
    * by apply/fconnect_sym/finv_inj. }
  gen have F,F': x z xA zA {xz N N'} / face x == z -> connect (restrict A clink) x z.
  { move/eqP => E; rewrite -{}E in zA *. by apply: connect1; rewrite /= xA zA clinkF. }
  case/or3P : xz => //= {N' F'}.
  rewrite -plain_eq' => // /eqP => E; rewrite -{}E in zA *. 
  have ? : face x \in A by rewrite (clA (face x) (node (face x))) //=.
  apply: connect_trans (N (face x) _ _ _ _) => //. exact: F.
Qed.

Definition avoid_one (G : hypermap) := 
  forall z x y : G , ~~ cnode z x -> ~~ cnode z y -> connect (restrict [predC cnode z] clink) x y.

Lemma two_connected_avoid (G : hypermap) (plainG : plain G) : 
  kconnected_map 2 G -> avoid_one G.
Proof.
case => _ tcG z x y Hx Hy.
have:= tcG (pred1 z) _; rewrite card1 => /(_ isT) {tcG} tcG.
have Nz : cnode z =i fclosure node (pred1 z) by apply/closure1/cnodeC.
have PNz : [predC cnode z] =i [predC fclosure node (pred1 z)]. 
{ by move => u; rewrite inE /= Nz. }
rewrite in_clink_glink //; last exact/predC_closed/connect_closed/cnodeC.
apply: connect_restrict_mono (tcG x y _ _); rewrite -?PNz //.
apply/subsetP => u. by rewrite -PNz.
Qed.

Definition drestrict (G : diGraph) (A : pred G) := DiGraph (restrict A (--)).

Lemma upathPR (G : diGraph) (x y : G) A :
  reflect (exists p : seq G, @upath (drestrict A) x y p)
          (connect (restrict A (--)) x y).
Proof. exact: (@upathP (drestrict A)). Qed.

Lemma upath_rconsE (G: diGraph) (x y : G) p : x != y ->
    upath x y p -> path (--) x (rcons (behead (belast x p)) y) /\ uniq (rcons (belast x p) y).
Proof.
rewrite /upath/pathp; elim/last_ind : p x y => [x y /negbTE-> //|p z ? x y ?]. 
rewrite !belast_rcons last_rcons /= -andbA => /and4P [H1 H2 H3 /eqP<-].
by rewrite H1 H2 H3.
Qed.

Lemma drestrict_upath (G : diGraph) (x y : G) (A : pred G) (p : seq G) :
  @upath (@drestrict G A) x y p -> @upath G x y p.
Proof.
elim: p x => // z p IH x /upath_consE [/= /andP [_ u1] u2 u3]. 
rewrite upath_cons u1 u2 /=. exact: IH.
Qed.

(* TODO: 
   - clean up digraph/sgraph connect/path lemmas
   - provide link between [p : Path x y] and [path e x (rcons q y)] *)
Lemma connect_inE (T : finType) (e : rel T) (A : pred T) (x y : T) : 
  x != y -> connect (restrict A e) x y -> 
  (exists p, [/\ path e x (rcons p y), uniq (x::rcons p y) & {subset x::rcons p y <= A}]).
Proof.
move => xDy. case/(@upathPR (DiGraph e)) => p U. 
move/upath_rconsE : (drestrict_upath U) => -/(_ xDy) [P1 P2].
have E : last x p = y by case/andP : U => _; apply: pathp_last.
rewrite -E -lastI in P2. 
exists (behead (belast x p)); split => //. 
- suff -> : rcons (behead (belast x p)) y = p by [].
  destruct p; rewrite -?E -?lastI //=. by rewrite -E /= eqxx in xDy. 
- move/upath_rconsE : (U) => /(_ xDy) => -[P _]. 
  apply/cons_subset; split; last exact: rpath_sub P. 
  destruct p; simpl in *. by rewrite E eqxx in xDy. 
  case/upath_consE : U => /=. by rewrite /edge_rel/=; case: (x \in A).
Qed.

Lemma sub_face_clink { G : hypermap } : @subrel G (frel face) clink.
Proof. by move => u v /eqP ?; apply/clinkP; right. Qed.

Lemma path_take_nth (T : eqType) (e : rel T) x s n : 
  n < size s -> path e x s -> e (last x (take n s)) (nth x s n).
Proof.
elim: s x n => // a s IH x [|n] /=; first by case (e x a).
rewrite ltnS => ? /andP [_ ?]; by rewrite (set_nth_default a x) ?IH.
Qed.

Lemma path_take (T : eqType) (e : rel T) x s n : 
  path e x s -> path e x (take n s).
Proof. by rewrite -{1}[s](cat_take_drop n) cat_path; case/andP. Qed.

Lemma disjoint_subpath (T : finType) (A B : pred T) (e : rel T) x y (p : seq T) :
  x \in A -> y \in B -> path e x (rcons p y) -> [disjoint A & B] ->
  exists u v q, [/\ u \in A, v \in B, path e u (rcons q v), 
              subseq (u:: rcons q v) (x:: rcons p y) & [disjoint q & [predU A & B]]].
Proof.
have [m Hm] := ubnP (size p); elim: m x y p Hm => // n IH x y p p_n xA xB pth_p disAB.
case: (boolP [disjoint p & [predU A & B]]) => [?|]; first by exists x; exists y; exists p.
case/pred0Pn => z /andP[z_in_p z_in_AB].
case/splitP def_p : p _ _ / z_in_p pth_p p_n => [p1 p2].
rewrite rcons_cat cat_path last_rcons => /andP [pth_p1 pth_p2].
rewrite size_cat size_rcons addSn ltnS => size_p. 
have {z_in_AB} [z_in_A|z_in_B] := orP z_in_AB.
- case:(IH z y p2) => //. apply: leq_ltn_trans size_p. exact: leq_addl. 
  move => u [v] [q] [uA vB Q1 Q2 Q3]; exists u; exists v; exists q. split => //. 
  apply: subseq_trans Q2 _. rewrite -(cats1 _ z) -catA cat1s -cat_cons.   
  exact: suffix_subseq.
- case:(IH x z p1) => //. apply: leq_ltn_trans size_p. exact: leq_addr. 
  move => u [v] [q] [uA vB Q1 Q2 Q3]; exists u; exists v; exists q. split => //. 
  apply: subseq_trans Q2 _. exact: prefix_subseq.
Qed.

Lemma last_belast (T : eqType) (x : T) (s : seq T) : 
  uniq (x :: s) -> last x s \in belast x s = false.
Proof. 
elim: s x => //= y s IH x /andP [Hx ?]. rewrite inE IH // orbF.
apply: contraNF Hx => /eqP <-. exact: mem_last.
Qed.

Lemma last_head_behead (T : eqType) (x : T) (p : seq T) : last (head x p) (behead (rcons p x)) = x.
Proof. case: p => //= ? ?. exact: last_rcons. Qed.

Lemma last_memE (T : eqType) (x : T) (s : seq T) (a : pred T) : 
  last x s \in a -> (x \in a) + { y | y \in s & y \in a}.
Proof. 
elim/last_ind : s => [|s y _]; first by left.
by rewrite last_rcons; right;exists y => //; rewrite mem_rcons mem_head.
Qed.


Lemma index_finv (T : finType) (f : T -> T) x : 
  findex f x (finv f x) = (order f x).-1.
Proof. by rewrite findex_iter // orderSpred. Qed.

Lemma bar (T : finType) (f : T -> T) x : 
  injective f -> findex f (f x) x = (order f (f x)).-1.
Proof. move => inj_f. have := index_finv f (f x). by rewrite finv_f. Qed.

(** Every face of a two connected loopless plain graph is bounded by a
cycle. In the hypermap representation, this amounts to showing that
distinct nodes on an f-cycle belong to different n-cycles *)
(* TODO: simplify further (use [rot_to_arc] for f-cycle) *)
Lemma two_connected_cyle (G : hypermap) :
  avoid_one G -> plain G -> loopless G -> planar G ->
  forall x y : G, x != y -> cface x y -> ~~ cnode x y.
Proof.
move => tcG plainG llG planarG x y xDy cf_xy; apply/negP => cn_xy.
wlog [p [path_p uniq_p disj_p]] : x xDy cf_xy cn_xy / 
  exists p, [/\ fpath (finv node) y (rcons p x), uniq p & [disjoint p & cface x]].
{ move => W. 
  pose o := orbit (finv node) y; pose a := cface x.
  have [o' def_o] : exists o', o = y :: o' by rewrite /o/orbit -orderSpred /=; eexists.
  have has_x : has a o'; first (apply/hasP; exists x; last exact: connect0). 
    suff: x \in o by rewrite def_o inE (negPf xDy).
    by rewrite -fconnect_orbit same_fconnect_finv // cnodeC.
  case/split_find def_o' : _ _ _ / has_x => [x' p q a_x' hasNp]; subst o'.
  have: uniq o by apply: orbit_uniq.
  have: fcycle (finv node) o by apply/cycle_orbit/finv_inj. 
  have cf_x'y: cface x' y by apply: connect_trans cf_xy; rewrite cfaceC.
  rewrite def_o /= rcons_path cat_path -!andbA => /andP [path_p _].
  rewrite cat_uniq rcons_uniq -!andbA mem_cat mem_rcons inE !negb_or -!andbA eq_sym.
  move => /andP[? /and5P[_ _ _ uniq_p _]]; apply: (W x') => //. 
  - rewrite cnodeC -same_fconnect_finv //; apply/connectP; exists (rcons p x') => //.
    by rewrite last_rcons.
  - exists p; split => //; rewrite disjoint_has // (eq_has (_ : cface x' =i cface x)) //.
    move=> z; rewrite !inE; apply: (same_connect cfaceC). 
    by apply: connect_trans cf_x'y _; rewrite cfaceC. }
(* Exibiting the f-cycle *)
have := cycle_orbit faceI x; have := orbit_uniq face x.
have : y \in orbit face x by rewrite -fconnect_orbit.
case def_c : (orbit face x) => [//|x0 c].
move: (def_c).
have {def_c} -> : x0 = x by move: def_c; rewrite /orbit -orderSpred; case. 
move => def_c y_in_c uniq_c cycle_c. 
rewrite inE eq_sym (negbTE xDy) /= in y_in_c.
(* Splitting the f-cycle *)
case/splitP def_c' : {1}c _ _ / y_in_c => [c1 c2].
move: uniq_c. rewrite def_c' /= cat_uniq has_sym has_rcons mem_cat mem_rcons rcons_uniq.
rewrite !inE (negbTE xDy) !negb_or /= -disjoint_has -!andbA disjoint_sym.
case/and5P => x_c1 x_c2 y_c1 uniq_c1 /and3P [y_c2 dis_c1_c2 uniq_c2].
move: path_p; rewrite rcons_path /= => /andP [path_p /eqP lst_p].
(* Obtain contour connecting [c1] and [c2] *)
have [u [v] [q] [path_q u_c v_c uniq_q disj_q]]: 
  exists u v q, [/\ path clink u (rcons q v), u \in c2, v \in c1, uniq q & [disjoint q & [predU cface x & p]]].
{  have [u [u_c1 Hu]] : exists u, u \in c1 /\ ~~ cnode x u. {
     destruct c1 as [|a ?]; move: cycle_c cn_xy; rewrite def_c'.
     - case/andP => /eqP <- _. by rewrite (negbTE (loopless_face _ _ _)). 
     - rewrite rcons_cons /= rcons_path => /and3P [/eqP<- _ _]. 
       exists (face x). by rewrite mem_head loopless_face. }
   have [v [v_c2 Hv]] : exists v, v \in c2 /\ ~~ cnode x v. { 
     elim/last_ind : c2 def_c' cycle_c cn_xy {x_c2 y_c2 dis_c1_c2 uniq_c2} => [|? a _] /= ->. 
     - rewrite cats0 /= rcons_path last_rcons => /andP [_ /eqP <-]. 
       by rewrite cnodeC (negbTE (loopless_face _ _ _)). 
     - rewrite !(rcons_path,cat_path) /= -!andbA last_cat !last_rcons => /and5P [_ _ _ _ /eqP E ?].
       exists (finv face x). by rewrite -E finv_f // mem_rcons mem_head cnodeC loopless_face. }
   have uDv : v != u. 
   { apply: contraTneq dis_c1_c2 => ?; subst. by apply/pred0Pn; exists u. }
   have [q [pth_q uniq_q sub_q]] := @connect_inE _ _ _ _ _ uDv (tcG x v u Hv Hu).
   have [u0 [v0] [q0] [A B C D E]] := disjoint_subpath  v_c2 u_c1 pth_q dis_c1_c2.
   exists u0; exists v0; exists q0; split => //. 
   - apply: subseq_uniq uniq_q. apply: subseq_trans D. 
     exact: subseq_trans (subseq_rcons _ _) (subseq_cons _ _).
   - move/mem_subseq in D. 
     apply/disjointP => z in_q0; apply/negP; rewrite !inE negb_or fconnect_orbit def_c.
     have Nz k : cnode y k -> z != k. 
     { move => Nyk. have:= connect_trans cn_xy Nyk.
       apply contraTneq => <-. by apply/sub_q/D; rewrite !(inE,mem_rcons) in_q0. }
     rewrite def_c' !(inE,mem_rcons,mem_cat) !negb_or !Nz 1?cnodeC //= -negb_or orbC. 
     move: (disjointFr E in_q0); rewrite inE => -> /=. 
     apply: contraTN (eqxx z) => z_p; apply/Nz. 
     rewrite -same_fconnect_finv //. 
     move/path_connect in path_p. by apply/path_p; rewrite !inE z_p. }
case/splitP def_c2 : {1}c2 _ _ / (u_c) => [c21 c22]. 
pose mp := rcons p x ++ rcons c1 y ++ rcons c21 u ++ q.
suff: Moebius_path mp by apply/negP; exact: planarP.
move: path_q; rewrite rcons_path => /andP [path_q lst_q].
have/andP [dis_q_f dis_q_p] : [disjoint q & (x::c)] && [disjoint p & q].
{ move: disj_q. rewrite disjoint_sym disjointU => /andP [A ->]; rewrite andbT disjoint_sym.
  by apply: disjointWl A; apply/subsetP => ?; rewrite -def_c -fconnect_orbit. }
rewrite /mp headI /Moebius_path -{2}headI /=.
apply/and3P; split.
- suff: uniq (rcons p x ++ c ++ q). 
  { apply: subseq_uniq. apply: cat_subseq => //. rewrite catA. apply: cat_subseq => //.
    rewrite def_c' def_c2. apply: cat_subseq => //. exact: prefix_subseq. }
  rewrite -cats1 -catA [[:: x] ++ _ ++ _]catA cat1s -def_c.
  rewrite cat_uniq has_cat negb_or -!disjoint_has uniq_p /=.
  rewrite ![[disjoint _ & p]]disjoint_sym dis_q_p (disjointWr _ disj_p). 
  2: by apply/subsetP => z; rewrite -fconnect_orbit.
  rewrite cat_uniq orbit_uniq -disjoint_has disjoint_sym uniq_q /= andbT.
  by rewrite disjoint_sym def_c.
- rewrite !catA cat_path !last_cat last_rcons path_q andbT -catA.
  rewrite cat_path last_head_behead (_ : path _ _ _) /=.
  + move/(sub_path sub_face_clink) : cycle_c. 
    by rewrite def_c' def_c2 !rcons_cat catA [in X in X -> _]cat_path => /andP [-> _].
  + move/(sub_path sub_node_clink): path_p lst_p. destruct p as [|z p] => //= /andP [A B] <-.
    by rewrite rcons_path B -{1}[last z p](f_finv nodeI) clinkN.
- rewrite 3!last_cat last_rcons. 
  have -> : node (head x p) = y. 
  { move: path_p lst_p. destruct p as [|z p]=> /= [_ <-|/andP[/eqP <- _] _]; exact: f_finv. }
  suff -> : finv node (last u q) = v. 
  { by rewrite !mem2_cat (_ : mem2 (rcons c1 y) v y) // -cats1 mem2_cat v_c !inE eqxx. }
  case/clinkP: lst_q => [->|def_v]; first by rewrite ?finv_f. 
  case: notF. (* the last step of [u::rcons q v] cannot be an f-step *)
  have: finv face v \in x::c1. 
  { have : fpath face x c1. 
    { move: cycle_c. rewrite def_c' -cat1s catA /= rcons_cat cat_path rcons_path. by case: (fpath _ _ c1). }
    case/splitP : v_c => [p1 p2 _]. rewrite cat_path !rcons_path last_rcons -andbA /=.
    case/and3P => _ /eqP <- _. by rewrite finv_f // -cats1 -catA /= -cat_cons mem_cat  mem_last. }
  rewrite -{}def_v finv_f //. case/last_memE => [|[z Z1]].
  + rewrite inE (disjointFr dis_c1_c2) // orbF => E. by rewrite -(eqP E) u_c in x_c2.
  + rewrite inE; case/predU1P => [?|H].
    * subst z. by rewrite (disjointFl dis_q_f) // mem_head in Z1.
    * by rewrite (disjointFl dis_q_f) // def_c' !(inE,mem_rcons,mem_cat) H in Z1. 
Qed.

