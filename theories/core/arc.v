From Coq Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma iter_id (T : Type) n : @iter T n id =1 id.
Proof. by elim: n. Qed.

Lemma iterK n (T : Type) (f g : T -> T) : 
  cancel f g -> cancel (iter n f) (iter n g).
Proof.
by move => can_fg; elim: n => // n IHn x; rewrite iterS iterSr IHn can_fg.
Qed.

Lemma leq_subl n m o : n <= m -> n - o <= m.
Proof. move => A. rewrite -[m]subn0. exact: leq_sub. Qed.

(** *** Lemmas on [index] and [subseq] *)
(** could go to seq.v *)

Lemma mem2_index (T : eqType) (x y : T) (s : seq T) : 
  uniq s -> y \in s -> mem2 s x y = (index x s <= index y s).
Proof.
have [|xNs _ y_s] := boolP (x \in s); last first.
  by rewrite mem2lf // (memNindex xNs) leqNgt index_mem y_s.
elim: s => //= z s IHs x_s /andP[zNs uniq_s] y_s; rewrite mem2_cons.
rewrite y_s; have [-> //|zDx] := eqVneq z x.
have [<-|zDy] := eqVneq z y;first by rewrite mem2rf. 
rewrite !inE ?[_ == z]eq_sym ?(negbTE zDy) ?(negbTE zDx) /= in x_s y_s.
exact: IHs.
Qed.

Lemma index_subseq (T : eqType) x y (s1 s2 : seq T) :
  y \in s1 -> subseq s1 s2 -> uniq s2 -> 
  index x s1 <= index y s1 -> index x s2 <= index y s2.
Proof.
move=> y_s1 sub_s1_s2 uniq_s2; have uniq_s1 := subseq_uniq sub_s1_s2 uniq_s2.
rewrite -!mem2_index ?mem2E // => [?|]; last exact: (mem_subseq sub_s1_s2).
exact: subseq_trans sub_s1_s2.
Qed.

Section Path.

Lemma eq_traject (T : Type) (f g : T -> T) : f =1 g -> traject f =2 traject g.
Proof. move=> fg x n; elim: n x => //= n IHn x. by rewrite IHn fg. Qed.

Variable (T : eqType). 
Implicit Types (s p : seq T) (x y : T).

Lemma head_rot s x0 n : n < size s -> head x0 (rot n s) = nth x0 s n.
Proof.
move=> n_lt_s; rewrite /rot -nth0 nth_cat size_drop subn_gt0 n_lt_s.
by rewrite -{2}[s](cat_take_drop n) nth_cat size_take n_lt_s ltnn subnn.
Qed.

Lemma next_cons x0 x s : next (x::s) x = head x0 (rcons s x).
Proof. by case: s => [|y s] /=; rewrite eqxx. Qed.

Lemma next_neq x p : x \in p -> uniq p -> 1 < size p -> x != next p x.
Proof. 
move => x_p; have [i p' rot_p uniq_p] := rot_to x_p.
move: (uniq_p); rewrite -(next_rot i) // -(size_rot i) -(rot_uniq i) {}rot_p.
case: p' => //= y p'. rewrite inE eqxx. by case: (x == y).
Qed.

Lemma prev_neq x p : x \in p -> uniq p -> 1 < size p -> x != prev p x.
Proof.
move => x_p uniq_p lt1p. have := @next_neq (prev p x) _ _ uniq_p lt1p.
by rewrite mem_prev next_prev // eq_sym; apply.
Qed.

Lemma iter_next_rot x0 s n :
  n < size s -> uniq s -> iter n (next s) (head x0 s) = head x0 (rot n s).
Proof.
elim: n s => [|n IHn] s; first by move => *; rewrite rot0.
case: s => [_ /= |x s]; first by rewrite (@eq_iter _ _ id) ?iter_id.
move => n_lt_s uniq_s. rewrite iterSr rotS 1?ltnW // rot_rot rot1_cons.
rewrite (next_cons x0).
under eq_iter => z do rewrite -(next_rot 1) ?rot1_cons //.
by rewrite IHn // ?size_rcons ?rcons_uniq // ltnW.
Qed.

Lemma iter_next_nth x0 s n : 
  uniq s -> n < size s -> iter n (next s) (head x0 s) = nth x0 s n.
Proof. by move => *; rewrite iter_next_rot // head_rot. Qed.

Lemma traject_next x0 s : 
  uniq s -> traject (next s) (head x0 s) (size s) = s.
Proof. 
move=> uniq_s; apply: (@eq_from_nth _ x0); rewrite size_traject // => i i_lt_s.
rewrite (set_nth_default (head x0 s)) ?size_traject //.
by rewrite nth_traject // iter_next_nth.
Qed.

Lemma mem_arc (p : seq T) (x y : T) : {subset arc p x y <= p}.
Proof. by move => z /mem_take; rewrite mem_rot. Qed.

End Path.

Lemma map_arc (aT rT : eqType) (f : aT -> rT) (s : seq aT) (x y : aT) : 
  injective f -> [seq f z | z <- arc s x y] = arc (map f s) (f x) (f y).
Proof. 
by move=> inj_f; rewrite /arc -map_rot !index_map // map_take.
Qed.

Lemma next_map (aT rT : eqType) (f : aT -> rT) (s : seq aT) (x : aT) : 
  injective f -> next (map f s) (f x) = f (next s x).
Proof.
move=> inj_f; case: s => //= a s.
by elim: s a {2 4}a => /= [|y s IHs] a b; rewrite inj_eq // ?IHs -fun_if.
Qed.

(** *** Lemmas on [index] *)
(** could go to [fingraph.v] *)

Lemma eq_findex (T : finType) (f g : T -> T) : 
  f =1 g -> findex f =2 findex g.
Proof. 
move=> fg x y; rewrite /findex /index /orbit /order (eq_traject fg). 
congr (_ _ (traject _ _ _)); exact/eq_card/eq_fconnect.
Qed.

Lemma findex_head (T : finType) (x y : T) (s : seq T) (uniq_xs : uniq (x::s)) :
  findex (next (x :: s)) x y = index y (x :: s).
Proof.
rewrite /findex (_ : orbit (next (x::s)) x = x::s) // /orbit.
rewrite (@order_cycle _ _ (x::s)) ?mem_head ?cycle_next //.
exact: (@traject_next _ x).
Qed.


From GraphTheory Require Import preliminaries.
Local Notation splitPr := path.splitPr.

(* Only the lemmas below are actually used: 
(* already on mathcomp master *)
Axiom card_gt1P : 
   forall {T : finType} {A : pred T}, reflect (exists x y : T, [/\ x \in A, y \in A & x != y]) (1 < #|A|).
Axiom disjointFr :  
  forall (T : finType) (A B : pred T), reflect (forall x : T, x \in A -> x \in B -> False) [disjoint A & B].
*)

Lemma head_arc (T: eqType) (s : seq T) (x y : T) (xDy : x != y) : 
  uniq s -> x \in s -> y \in s -> x \in arc s x y.
Proof.
move=>  uniq_s x_s y_s. case: (rot_to_arc uniq_s x_s y_s xDy) => i s1 s2 <- _ _. 
exact: mem_head.
Qed.

Lemma next_mem_arc (T : eqType) (s : seq T) (x y : T) : 
  uniq s -> x \in s -> y \in s -> x != y -> next s x \in rcons (arc s x y) y.
Proof.
move=> uniq_s x_s y_s xDy.
have [i s1 s2 arc1 arc2 rot_r] := rot_to_arc uniq_s x_s y_s xDy.
rewrite -arc1 -(next_rot i) // rot_r (next_cons x).
by case: s1 {arc1 rot_r} => [|z s1']; rewrite /= !inE eqxx orbT.
Qed.

(* Not used *)
Lemma arc_next (T : eqType) (s : seq T) (x : T) : 
  1 < size s -> uniq s -> x \in s -> arc s x (next s x) = [:: x].
Proof. 
move=> le2s uniq_s x_s. 
have xDnx : x != next s x by apply: next_neq.
have nx_s : next s x \in s by rewrite mem_next.
have [i s1 s2 A1 A2 rot_i] := rot_to_arc uniq_s x_s nx_s xDnx.
suff s1nil : s1 = [::] by rewrite -A1 s1nil.
move: (uniq_s); rewrite -(rot_uniq i) rot_i -(next_rot i) // rot_i (next_cons x).
by case: s1 {A1 A2 rot_i} => //= y s1'; rewrite !(inE,mem_cat) eqxx orbT andbF.
Qed.


Definition path0 (T : Type) (e : rel T) (s : seq T) :=
  if s is x::s then path e x s else true.

Lemma path_path0 (T : Type) (e : rel T) x (s : seq T) : 
  path e x s -> path0 e s.
Proof. by case: s => //= y s /andP [_]. Qed.


Section UcycleArc.
Variables (T : finType) (e : rel T) (s : seq T).

Lemma arc_path x y (xDy : x != y) :
  ucycle e s -> x \in s -> y \in s -> path0 e (arc s x y).
Proof.
move=> /andP[cycle_s uniq_s] x_s y_s. 
have [i s1 s2 <- _ E /=] := rot_to_arc uniq_s x_s y_s xDy.
move: cycle_s. rewrite -(rot_cycle i) E /= rcons_path cat_path.
by case: (path e x s1).
Qed.

Lemma arc_edge x y : 
  ucycle e s -> x \in s -> y \in s -> x != y -> e (last x (arc s x y)) y.
Proof.
move => /andP [cycle_s uniq_s] x_s y_s xDy.
have [n s1 s2 <- _ rot_s] := rot_to_arc uniq_s x_s y_s xDy.
move: cycle_s; rewrite -(rot_cycle n) {}rot_s /=.
by rewrite rcons_path cat_path /=; case: (e (last _ _) _); rewrite // andbF.
Qed.

Lemma arc_findex x y z (xDy : x != y) : 
  uniq s -> x \in s -> y \in s -> 
  (z \in arc s x y) = (findex (next s) x z < findex (next s) x y).
Proof.
move=> uniq_s x_s y_s; have [i s1 s2 A1 A2 R] := rot_to_arc uniq_s x_s y_s xDy.
under eq_findex => u do rewrite -(next_rot i) //.
under (@eq_findex _ (next s)) => u do rewrite -(next_rot i) //.
have uniq_xy : uniq (x :: s1 ++ y :: s2) by rewrite -R rot_uniq.
rewrite R !findex_head // -cat_cons !index_cat index_head.
rewrite -A1 [X in _ < X]ifN. 
  by case: ifP => [Hz|_]; rewrite ?ltn_add2l // addn0 index_mem Hz.
by apply: contraTN uniq_xy => C; rewrite -cat_cons cat_uniq /= C /= andbF.
Qed.

Lemma arc_disjoint2 x y : 
  uniq s -> x \in s -> y \in s -> x != y -> [disjoint arc s x y & arc s y x].
Proof.
move => uniq_s x_s y_s xDy.
have [n s1 s2 <- <- rot_s] := rot_to_arc uniq_s x_s y_s xDy.
move: uniq_s; rewrite -(rot_uniq n) rot_s -cat_cons cat_uniq. 
by rewrite disjoint_sym disjoint_has => /and3P [_ -> _].
Qed.

Lemma arc_disjoint x1 x2 y1 y2 : 
  uniq s -> x1 \in s -> x2 \in s -> y1 \in s -> y2 \in s -> x1 != x2 -> y1 != y2 ->
  findex (next s) x1 x2 <= findex (next s) x1 y1 ->
  findex (next s) y1 y2 <= findex (next s) y1 x1 ->
  [disjoint arc s x1 x2 & arc s y1 y2].
Proof.
move=> uniq_s x1_s x2_s y1_s y2_s x1Dx2 y1Dy2 index_x index_y.
have x1Dy1 : x1 != y1. 
{ apply: contraNneq x1Dx2 => ?; subst y1. 
  by move: index_x; rewrite findex0 leqn0 findex_eq0. }
apply/pred0Pn => -[x] /=; rewrite !arc_findex // => /andP [A1 A2].
have {A1 index_x} := leq_trans A1 index_x.
have {A2 index_y} := leq_trans A2 index_y.
rewrite -!arc_findex //= 1?eq_sym // => x_arc.
by apply/negP; rewrite (disjointFl (@arc_disjoint2 x1 y1  _ _ _ _)).
Qed.

Variable p : seq T.
Hypothesis uniq_s : uniq s.
Hypothesis p_sub_s : subseq p s.
Let p_in_s := mem_subseq p_sub_s.
Let uniq_p := subseq_uniq p_sub_s uniq_s.

Lemma findex_next_other (x y : T) :
  x \in p -> y \in p -> x != y -> findex (next s) x (next p x) <= findex (next s) x y.
Proof.
move=> x_p y_p xDy; have x_s : x \in s by apply: p_in_s.
have [n s' rot_n] := rot_to x_s.
under eq_findex => z do rewrite -(next_rot n) //.
under [X in _ <= X]eq_findex => z do rewrite -(next_rot n) //.
have uniq_xs : uniq (x :: s') by rewrite -rot_n rot_uniq.
have [m _ sub] := subseq_rot n p_sub_s.
rewrite rot_n !findex_head // -(next_rot m) //; rewrite rot_n in sub. 
have [p' P] : exists p', rot m p = x :: p'. 
{ rewrite -(mem_rot m) in x_p; rewrite -(rot_uniq m) in (uniq_p).
  case: (splitPr x_p) sub => p1 p2. rewrite -[x::s']cat0s.
  rewrite uniq_subseq_pivot // => /andP.
  by rewrite subseq0 => -[/eqP -> _]; exists p2. }
rewrite P next_nth mem_head index_head.
case: p' P => [|y' p' P]; first by rewrite /= eqxx leq0n.
rewrite [nth _ _ _]/= P in sub *; apply: index_subseq sub _ _ => //.
  by rewrite -P mem_rot.
by rewrite /= eqxx (negbTE xDy); case: (x == y').
Qed.

Lemma arc_next_disjoint x y : 
  x \in p -> y \in p -> x != y ->
  [disjoint arc s x (next p x) & arc s y (next p y)].
Proof.
move=> x_p y_p xDy. 
have x_s : x \in s by apply p_in_s.
have ? : 1 < size p.
{ apply: leq_trans (card_size _). by apply/card_gt1P; exists x,y. }
apply: arc_disjoint; try apply: p_in_s; rewrite ?mem_next //.
1-2: exact: next_neq.
all: by apply: findex_next_other; rewrite // eq_sym.
Qed.

Lemma arc_cover x y : x \in s -> y \in s -> x != y -> s =i [predU arc s x y & arc s y x].
Proof.
move=> x_s y_s xDy z; have [i s1 s2 A1 A2 def_s] := rot_to_arc uniq_s x_s y_s xDy.
by rewrite -(mem_rot i) def_s -cat_cons A1 A2 mem_cat.
Qed.

Lemma mem_arc_other x y z : x \in s -> y \in s -> z \in s -> x != y -> 
  (z \in arc s x y) = (z \notin arc s y x).
Proof.
move=> x_s y_s z_s xDy; have/esym := arc_cover x_s y_s xDy z; rewrite z_s inE /=.
have D := arc_disjoint2 uniq_s x_s y_s xDy.
by case/orP => z_arc; rewrite z_arc ?(disjointFr D) // ?(disjointFl D).
Qed.

Lemma arc_remainder x : 1 < size p -> x \in p -> {subset p <= rcons (arc s (next p x) x) x}.
Proof.
move=> gt1p x_p y y_p; rewrite mem_rcons inE; have [//|xDy/=] := eqVneq x y.
rewrite mem_arc_other ?p_in_s ?mem_next // 1?eq_sym ?next_neq //.
have D := arc_next_disjoint x_p y_p xDy. 
by rewrite (disjointFl D) // head_arc ?p_in_s ?next_neq ?mem_next.
Qed.

End UcycleArc.

Section SubCycle.
Variables (T : eqType).
Implicit Types (p s : seq T).

Definition subcycle p s := [exists n : 'I_(size p).+1, subseq (rot n p) s].

Lemma subcycleP p s : reflect (exists n, subseq (rot n p) s) (subcycle p s).
Proof.
apply: (iffP existsP) => [[n On]|[n rot_n]]; first by exists n.
have [lt_p|ge_p] := ltnP n (size p).+1; first by exists (Ordinal lt_p).
by exists (Ordinal (ltn0Sn _)); rewrite /= rot0 -[p](@rot_oversize _ n) // ltnW.
Qed.

Lemma subcycle_rot_l n p s : subcycle (rot n p) s = subcycle p s.
Proof. 
apply/subcycleP/subcycleP => [[m]|[m sub]].
  rewrite rot_rot_add => subs; eexists; exact: subs.
exists (rot_add (rot n p) ((size (rot n p)) - n) m). 
by rewrite -rot_rot_add -/(rotr _ _) rotK.
Qed.

Lemma subcycle_rot_r n p s : subcycle p (rot n s) = subcycle p s.
Proof.
apply/subcycleP/subcycleP => -[m sub].
  have [k _ sub'] := subseq_rot (size (rot n s) - n) sub.
  rewrite -/(rotr _ _) rotK rot_rot_add in sub'; eexists; exact sub'.
have [k _ sub'] := subseq_rot n sub. 
by exists (rot_add p m k); rewrite -rot_rot_add.
Qed.

Lemma subcycle_rot n m s p : subcycle (rot n p) (rot m s) = subcycle p s.
Proof. by rewrite subcycle_rot_l subcycle_rot_r. Qed.

Lemma subseq_subcyle p s : subseq p s -> subcycle p s.
Proof. by move => sub; apply/subcycleP; exists 0; rewrite rot0. Qed.

Lemma subcycle_trans : transitive subcycle.
Proof.
move=> r p q sub_p_r /subcycleP [m sub_r_q].
move: sub_p_r; rewrite -(subcycle_rot_r m) => /subcycleP [n] sub_p_r.
by apply/subcycleP; exists n; apply: subseq_trans sub_r_q.
Qed.

Lemma subcycle_uniq p s : subcycle p s -> uniq s -> uniq p.
Proof. 
move=> /subcycleP [n sub_p_s]; rewrite -(rot_uniq n p).
exact: subseq_uniq.
Qed.

Lemma mem_subcycle p s : subcycle p s -> {subset p <= s}.
Proof. 
move=> /subcycleP[n /mem_subseq sub_p_s] z z_p.
by apply: sub_p_s; rewrite mem_rot.
Qed.

Lemma subcycle_get_arc x p s :
  x \in s -> uniq s -> subcycle p s -> 1 < size p ->
  exists2 z, z \in p & x \in arc s z (next p z).
Proof.
wlog [s' -> _ {s}] : s / exists s', s = x::s'.
{ move=> W x_s uniq_s sub_p_s size_p; have [i s' rot_i] := rot_to x_s. 
  case: (W (rot i s)); rewrite ?mem_rot ?rot_uniq ?subcycle_rot_r //; first by exists s'.
  move=> z z_p; rewrite arc_rot ?(mem_subcycle sub_p_s) //; by exists z. }
move=> uniq_s sub_p_s size_p. 
have uniq_p : uniq p by apply: subcycle_uniq uniq_s.
have [x_p|xNp] := boolP (x \in p).
- exists x; rewrite ?head_arc ?mem_head //; first exact: next_neq. 
  apply: mem_subcycle sub_p_s _ _. by rewrite mem_next.
- have has_p : has (mem p) s'. 
  {  case: p => [//|z p] in size_p sub_p_s uniq_p xNp *.
     apply/hasP; exists z; rewrite /= ?mem_head //. 
     move:(mem_subcycle sub_p_s) => /(_ z (mem_head _ _)) /predU1P [zx|//].
     by rewrite zx inE eqxx in xNp. }
  case def_s : _ _ _ _ / (split_find_nth x has_p) => [/= nz s1 s2 nz_p Ns2].
  pose z := path.prev p nz. 
  have z_s2 : z \in s2. 
  { have z_p : z \in p by rewrite path.mem_prev. 
    move:(mem_subcycle sub_p_s z_p); rewrite inE => /predU1P[zx|].
      by subst; contrab.
    rewrite def_s. rewrite mem_cat mem_rcons inE eq_sym (negbTE (prev_neq _ _ _)) //=.
    by case/orP => [z_s1|//]; apply: contraNT Ns2 => _; apply/hasP; exists z. }
  exists z; rewrite ?path.mem_prev // next_prev // -cats1 -catA /=.
  case def_s2 : _ / (path.splitPr z_s2) => [p1 p2]. 
  have U1 : uniq (x :: s1 ++ nz :: p1 ++ z :: p2).
  { by rewrite -def_s2 -[nz :: _]cat1s catA cats1 -def_s. }
  move: (U1). rewrite -cat_cons -(rot_uniq (size (x :: s1))) rot_size_cat => U2.
  rewrite -cat_cons -(arc_rot (size (x :: s1))) // ?rot_size_cat ?(inE,mem_cat,eqxx,orbT)//.
  have E : ((nz :: p1) ++ z :: p2) ++ x :: s1 = nz :: p1 ++ z :: (p2 ++ x :: s1).
  { by rewrite /= -!cat_cons -!catA. }
  by rewrite E right_arc -?E// !(inE,mem_cat) eqxx /= !orbT.
Qed.



End SubCycle.


Lemma arc_iterP (T : eqType) (x y z : T) (s : seq T) (xDy : x != y) : 
  uniq s -> x \in s -> y \in s -> 
  reflect (exists2 n, iter n (next s) x = z 
                    & forall m, m <= n -> iter m (next s) x != y) 
          (z \in arc s x y).
Proof.
move=> uniq_s x_s y_s. 
have [i s1 s2 arc1 arc2 rot_i] := rot_to_arc uniq_s x_s y_s xDy.
have I k (lt_k_s : k < size (rot i s)) : iter k (next s) x = nth x (rot i s) k.
{ have -> : x = head z (rot i s) by rewrite rot_i.
  under eq_iter => u do rewrite -(next_rot i) //.
  by rewrite iter_next_nth // ?rot_uniq // (set_nth_default z). }
have yNarc1 : y \notin arc s x y. 
{ apply: contraTN uniq_s; rewrite -(rot_uniq i) rot_i -cat_cons arc1 cat_uniq.
  move=> y_arc1; rewrite [has _ _](_ : _ = true) ?andbF //.
  by apply/hasP; exists y => //=; apply: mem_head. }
apply: (iffP idP) => [z_arc1|[n iter_n min_n]].
- have z_s := mem_arc z_arc1; exists (index z (rot i s)) => [|m lt_m_z].
    rewrite I ?nth_index // ?mem_rot // index_mem. 
    by rewrite rot_i -cat_cons arc1 mem_cat z_arc1.
   have lt_m_a1 : m < size (arc s x y). 
   { apply: leq_ltn_trans lt_m_z _.
     by rewrite rot_i -cat_cons arc1 index_cat z_arc1 index_mem. }
   have m_lt_s : m < size (rot i s). 
     by apply: leq_trans lt_m_a1 _; rewrite rot_i -cat_cons arc1 size_cat leq_addr.
   apply: contraNneq yNarc1; rewrite I // => {1}<-.
   by rewrite rot_i -cat_cons arc1 nth_cat lt_m_a1 mem_nth.
- pose k := index y (rot i s); have lt_k_s : k < size (rot i s).
    by rewrite index_mem rot_i !(inE,mem_cat) eqxx !orbT.
  have lt_n_k : n < k. 
    rewrite ltnNge; apply/negP=> /min_n.
    by rewrite I // nth_index ?eqxx // rot_i !(inE,mem_cat) eqxx !orbT.
  rewrite -iter_n I ?(ltn_trans lt_n_k lt_k_s) // rot_i -cat_cons arc1 nth_cat.
  suff eq_k : k = size (arc s x y) by   rewrite -eq_k lt_n_k mem_nth // -eq_k.
  by rewrite /k rot_i -cat_cons arc1 index_cat (negbTE yNarc1) /= ?eqxx ?addn0.
Qed.

Lemma next_iter (T : eqType) (x y : T) (s : seq T) :
  uniq s -> x \in s -> y \in s -> exists n, iter n (next s) x == y.
Proof. 
move=> uniq_s x_s y_s; have [i s' rot_i] := rot_to x_s.
exists (index y (rot i s)); under eq_iter => z do rewrite -(next_rot i) //.
have -> : x = head y (rot i s) by rewrite rot_i. 
by rewrite iter_next_nth ?nth_index ?index_mem ?mem_rot ?rot_uniq.
Qed.

Lemma prev_iter (T : eqType) (x y : T) (s : seq T) :
  uniq s -> x \in s -> y \in s -> exists n, iter n (prev s) x == y.
Proof.
move=> uniq_s x_s y_s; have [n /eqP eq_x] := next_iter uniq_s y_s x_s.
by exists n; rewrite -eq_x iterK //; apply: prev_next.
Qed.

Lemma subcycle_get_arc' (T : eqType) x (p s : seq T) : 
  x \in s -> uniq s -> subcycle p s -> 1 < size p ->
  exists2 z, z \in p & x \in arc s z (next p z).
Proof.
move=> x_s uniq_s sub_p_s le2p. 
have mem_s := mem_subcycle sub_p_s.
have uniq_p : uniq p by apply: subcycle_uniq uniq_s.
have /ex_minnP [n iter_n min_n] : exists n, iter n (prev s) x \in p.
  move/leqW : le2p; rewrite ltnS -has_predT => /hasP [z z_p _].
  have [n /eqP it_n] := next_iter uniq_s (mem_s _ z_p) x_s.
  by exists n; rewrite -it_n iterK //; exact: prev_next.
set z := iter n _ _ in iter_n *; exists z => //. 
have [z_s nz_s] : z \in s /\ next p z \in s by rewrite ?mem_s // ?mem_next.
apply/arc_iterP; rewrite ?next_neq //.
have /ex_minnP [m /eqP iter_m min_m] := next_iter uniq_s z_s nz_s.
exists n => [|n'] ; first exact/iterK/next_prev.
apply: contraTN => /min_m => le_m_n'. rewrite -ltnNge.
apply: leq_trans le_m_n' => {n'}. apply: wlog_neg; rewrite -ltnNge => gt_m_n.
have gt0m : 0 < m. 
{ by rewrite lt0n; apply: contra_eq_neq iter_m => -> /=; apply: next_neq. }
have gt0n : 0 < n by apply: leq_trans gt0m _.
have/min_n : iter (n - m) (prev s) x \in p. 
{ have En : n = m + (n - m) by rewrite subnKC.
  move: iter_n. rewrite -mem_next -iter_m /z {1}En iterD iterK //.
  exact: next_prev. }
by rewrite leqNgt ltn_subrL gt0m gt0n.
Qed.

Lemma arc_subcycle_disjoint (T : finType) (p s : seq T) (x y : T) : 
  uniq s -> subcycle p s -> x \in p -> y \in p -> x != y -> 
  [disjoint arc s x (next p x) & arc s y (next p y)].
Proof.
move=> uniq_s /subcycleP [m sub_p_s].
wlog: p {sub_p_s} / subseq p s => [W|?]; last exact: arc_next_disjoint.
move: (W _ sub_p_s); rewrite !mem_rot !next_rot // -(rot_uniq m).
all: exact: subseq_uniq uniq_s.
Qed.

Lemma arc_subcycle_disjoints (T : finType) (p s : seq T) (x y nx ny : T) : 
  uniq s -> subcycle p s -> x \in p -> y \in p -> x != y -> nx = next p x -> ny = next p y ->
  [disjoint [set z in arc s x nx] & [set z in arc s y ny]].
Proof.
move=> uniq_s subcycle_p x_p y_p xDy next_x next_y.
under eq_disjoint => z do by rewrite !inE.
under eq_disjoint_r => z do by rewrite !inE.
by rewrite next_x next_y; apply: (arc_subcycle_disjoint uniq_s).
Qed.
