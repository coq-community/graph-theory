From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries digraph sgraph connectivity minor treewidth arc.
Require Import set_tac.

(* TOTHINK : arc is only included for the [path0] definition *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Canonical edge_app_pred (G : diGraph) (x : G) := ApplicativePred (edge_rel x).
Canonical sedge_app_pred (G : sgraph) (x : G) := ApplicativePred (sedge x).

(** If [S] is a smallest separator, then every (maximal) component of G-S 
    can be seen as one part of a proper separation *)
Lemma component_separation (G : sgraph) (A S : {set G}) x : 
  smallest vseparator S -> 
  x \in A -> [disjoint A & S] -> connected A -> {in A & ~: A, forall x y, x--y -> y \in S} ->
  proper_separation (A :|: S) (~: A :|: S).
Proof.
move=> [sepS minS] x_A dis_A_S conA compA. 
case: sepS => [u[v sep_uv]].
have Huv : (u \notin A) || (v \notin A).
{ apply: contraTT (dis_A_S); rewrite negb_or !negbK => /andP [u_A v_A].
  have uDv := separatesNeq sep_uv.
  have/(connect_irredRP uDv) [p Ip /subsetP subA] := conA _ _ u_A v_A.
  case: sep_uv => uNS vNS /(_ p) [z /subA ? ?]. by apply/pred0Pn; exists z. }
wlog uNA : u v sep_uv {Huv} / u \notin A => [W|].
{ case/orP: Huv; apply: W;[|rewrite separates_sym]; exact: sep_uv. }
case: (sep_uv) => uNS vNS sepS.
split; first split.
- by move => z; rewrite !inE; case: (z \in A).
- move => x1 x2. rewrite !inE !negb_or !negbK => /andP [x1_A x1NS] /andP [x2_A]. 
  by apply: contraNF => /compA; apply; rewrite ?inE.
- by exists x,u; rewrite !inE x_A (disjointFr dis_A_S) //= negb_or uNA uNS.
Qed.


(** * Merging Vertices  *)

(** The definition of [smerge2 G x y] is simply to remove [y] and
attach all edges of [y] to [x], regardless of whether [x -- y] holds
or not. We use both variants. Edge-constraction drives the main
argument for the 3-connected case of Wagner's theorem. On the other
hand, vertex merging is used extensively when extending the result
from 3-connected graphs to general graphs *)

Section SMerge2.
Variables (G : sgraph) (x y : G).

Definition smerge2_vertex := { z : G | z != y }.
Definition smerge2_rel := 
  [rel u v : smerge2_vertex | 
   if (val u == x) && (val v != x) then val v -- x || val v -- y else 
   if (val v == x) && (val u != x) then val u -- x || val u -- y else 
   val u -- val v].

Lemma smerge2_irrefl : irreflexive smerge2_rel. 
Proof. by move => u /=; case: (sval u == x); rewrite /= ?andbF ?sgP. Qed.

Lemma smerge2_sym : symmetric smerge2_rel.
Proof. 
move => u v /=; (case: (altP (sval u =P x)); case: (altP (sval v =P x)) => //=) => [-> -> //|].
by rewrite sgP.
Qed.

Definition smerge2 := SGraph smerge2_sym smerge2_irrefl.

Lemma smerge2_edge (u v : smerge2) : val u -- val v -> u -- v.
Proof.
move=> val_uv; rewrite /edge_rel/=. 
case: (boolP (_ && _)) => [/andP[/eqP<- _]|_]; first by rewrite sgP val_uv.
case: (boolP (_ && _)) => [/andP[/eqP<- _]|_]; by rewrite val_uv.
Qed.

Lemma smerge2_minor : x -- y -> minor G smerge2.
Proof. 
move => xy.
pose phi (z : smerge2) : {set G} := if val z == x then [set x;y] else [set val z].
suff: minor_rmap phi by apply: minor_of_rmap.
split.
- move => z; rewrite /phi; case: ifP => _; solve [exact: set10|exact: setU1_neq].
- move => z; rewrite /phi; case: ifP => _; solve [exact: connected1|exact: connected2].
- move => z1 z2 z1Dz2; rewrite /phi. 
  case: (eqVneq x (val z1)) => [->|xDz1]. 
  + rewrite eq_sym val_eqE (negbTE z1Dz2) disjoint_sym disjoints1 !inE negb_or.
    by rewrite eq_sym val_eqE (negbTE z1Dz2) (valP z2).
  + case: (eqVneq x (val z2)) => [->|xDz2]; rewrite disjoints1 !inE ?negb_or ?val_eqE //.
    by rewrite z1Dz2 (valP z1).
- have H z u v : sval u = x -> sval v != x -> sval v -- z -> z \in [set x; y] -> neighbor (phi u) (phi v).
  { move => eq_u eq_v v_z Hz. apply/neighborP; exists z; exists (sval v).  
    by rewrite /phi [val u]eq_u eqxx (negbTE eq_v) sgP v_z Hz inE eqxx. }
  move => u v. rewrite /edge_rel/=. 
  case: (altP (sval u =P x)); case: (altP (sval v =P x)) => //=.
  + move => -> ->. by rewrite sgP.
  + move => eq_v eq_u. by case/orP => ?; [apply: (H x)|apply: (H y)]; rewrite //= !inE !eqxx.
  + move => eq_v eq_u. rewrite neighborC. 
    by case/orP => ?; [apply: (H x)|apply: (H y)]; rewrite //= !inE !eqxx.
  + move => eq_v eq_u u_v. apply/neighborP; exists (val u); exists (val v).
    by rewrite /phi /= (negbTE eq_v) (negbTE eq_u) 2!sgP !inE !eqxx u_v.
Qed.

End SMerge2.
Arguments smerge2 : clear implicits.

Lemma card_smerge2 (G : sgraph) (x y : G) : 
  #|smerge2 G x y|.+1 = #|G|.
Proof. 
rewrite card_sig [RHS](cardD1 y) add1n; congr (_.+1).
by apply: eq_card => z; rewrite !inE.
Qed.

Lemma smerge2_val_edge (G : sgraph) (x y : G) (u v : smerge2 G x y) : 
  val u != x -> val v != x -> val u -- val v = u -- v.
Proof.
move: u v => [u uDy] [v vDy] /= uDx vDx.
by rewrite [RHS]/edge_rel/= (negbTE uDx) (negbTE vDx).
Qed.

(* not used, but it probably should by *)
Lemma smerge2_neighbor (G : sgraph) (x y : G) (xDy : x != y) : 
  val @: N(Sub x xDy : smerge2 G x y) = (N(x) :|: N(y)) :\: [set x;y]. 
Proof.
apply/setP => z; rewrite !inE; apply/imsetP/andP => [[z0 Hz0 ->]|[]].
  move: Hz0. rewrite !inE negb_or (valP z0) /edge_rel/= eqxx andbF /=.
  case: (eqVneq (sval z0) x) => /= [<-|]; by rewrite ?sg_irrefl ?[sval _ -- _]sg_sym.
rewrite negb_or => /andP [zDx zDy]; exists (Sub z zDy) => //. 
by rewrite inE /edge_rel/= eqxx andbF /= ![z -- _]sg_sym zDx.
Qed.

Lemma smerge2_path0 (G : sgraph) (x y : G) (s : seq (smerge2 G x y)) : 
  let s0 := [seq val x | x <- s] in path0 (--) s -> x \notin s0 -> path0 (--) s0.
Proof.
hnf; case: s => // u s; elim: s u => // v s /= IHs u /= /andP[uv pth_s].
rewrite !inE !negb_or => /and3P[xDu xDv xNs]. 
by rewrite smerge2_val_edge ?[_ == x]eq_sym // uv /= IHs // inE (negPf xDv).
Qed.

Lemma smerge2_ucycle (G : sgraph) (x y : G) (s : seq (smerge2 G x y)) : 
  let s0 := [seq val x | x <- s] in
  ucycle (--) s -> x \notin s0 -> ucycle (--) s0.
Proof.
hnf; case: s => // z s; rewrite /ucycle/cycle/= => /and3P[pth_s zNs uniq_s xNs].
rewrite map_inj_uniq ?uniq_s ?andbT; last exact: val_inj.
rewrite mem_map // zNs andbT -map_rcons.
apply: (@smerge2_path0 G x y (z::rcons s z)) => //=.
by move: xNs; rewrite !inE map_rcons mem_rcons inE !negb_or andbA andbb.
Qed.

Lemma smerge2edgeD (G : sgraph) (x y : G) (u v : smerge2 G x y) : 
  ~~ x -- y -> 
  u -- v = [|| val u -- val v, (val u == x) && val v -- y | (val v == x) && val u -- y].
Proof.
move => n_xy; rewrite [LHS]/edge_rel/= -![sval _]/(val _).
case: (eqVneq (val u) x) => [->|uDx]; case: (eqVneq (val v) x) => [->|vDx] //=.
- by rewrite sg_irrefl (negbTE n_xy).
- by rewrite orbF ![_ -- val _]sgP.
Qed.

Lemma smerge2edgeL (G : sgraph) (x y : G) (u v : smerge2 G x y) : 
  ~~ x -- y -> val u == x -> val v -- y -> u -- v.
Proof. 
move=> xNy uEx vy. rewrite /edge_rel/= -![sval _]/(val _) uEx andbF /= vy orbT.
case: (eqVneq (val v) x) => // E. by rewrite -E vy in xNy.
Qed.

(** wlog reasoning for edges of [smerge2 G x y] when the conclusion is symmetric *)
Lemma smerge2Ecase (G : sgraph) (x y : G) (G' := smerge2 G x y) (P : G' -> G' -> Prop) :
  ~~ x -- y -> (forall u v, P u v <-> P v u) -> 
  (forall u v, val u -- val v -> P u v) -> (forall u v, (val u == x) && val v -- y -> P u v) ->
  forall u v, u -- v -> P u v.
Proof.
move=> xNy Psym P1 P2 u v. rewrite smerge2edgeD //; case/or3P => //. exact: P1. exact: P2.
rewrite Psym. exact: P2.
Qed.


Lemma smerge2_separator (G : sgraph) (x y : G) (S : {set smerge2 G x y}) :
  vseparator S -> vseparator (y |: val @: S).
Proof.
move => [u[v [uNS vNS sep_uv]]]. 
exists (val u),(val v); split => [||p].
- rewrite !inE (negbTE (valP u)) /= inj_imset //; exact: val_inj.
- rewrite !inE (negbTE (valP v)) /= inj_imset //; exact: val_inj.
- have [|yNp] := boolP (y \in p); first by exists y => //; rewrite !inE eqxx.
  have [|//||q eq_q _] := lift_Path (p' := p).
  + exact: smerge2_edge.
  + move => z z_p. have zDy : z != y by apply: contraTneq z_p => ->.
    by apply/mapP; exists (Sub z zDy) => //; rewrite mem_enum.
  + have [z z_q z_S] := sep_uv q; exists (val z); last by rewrite !inE inj_imset ?z_S.
    by rewrite mem_path -eq_q mem_map.
Qed. 

Lemma smerge_konnected k (G : sgraph) (x y : G) : 
  x -- y -> k.+1.-connected G -> k.-connected (smerge2 G x y).
Proof.
move=> xy [lG vsG]; split => [|S sepS]; first by rewrite -ltnS card_smerge2.
have/vsG := smerge2_separator sepS.
rewrite cardsU1 card_imset // [_ \notin _](_ : _ = true) //.
by apply: contraTN isT => /imsetP -[[z zDy _ /= E]]; rewrite -E eqxx in zDy.
Qed.

(** ** Edge Contraction in 3-connected graphs *)


(** Any separator of [smerge2 G x y] that does not contain [x] can be
lifted to a separator in of [G] *)
Lemma separator_from_smerge2 (G : sgraph) (x y : G) (xDy : x != y) 
  (x' := Sub x xDy) (S : {set smerge2 G x y}) :
  vseparator S -> x' \notin S -> vseparator (val @: S).
Proof.
move=> /vseparator_separation [V1 [V2 [psepV def_S]]] xNS.
wlog x_V1 : V1 V2 psepV def_S / x' \notin V2 => [W|].
{ case: (boolP (x' \in V2)) => [x_V2|]; last exact: (W V1 V2).
  apply: (W V2 V1); rewrite 1?proper_separation_symmetry 1?setIC //.
  case: psepV => sepV _. apply: contraNN xNS => x_V1. by rewrite def_S inE x_V1 x_V2. }
suff: proper_separation (y |: val @: V1) (val @: V2).
{ move/proper_vseparator. 
  suff -> : (y |: val @: V1) :&: (val @: V2) = val @: S by [].
  apply/setP => u; rewrite def_S inE imsetI ?inE; last exact: (in2W val_inj).
  rewrite (@andb_id2r _ _ (u \in val @: V1)) // => /imsetP [u0 _ ->].
  by rewrite (negbTE (valP u0)). }
split; first split.
- move => u. case: (eqVneq u y) => [->|uDy]; rewrite !inE ?eqxx ?(negbTE uDy) //=.
  case: psepV => sepV _. have := sepV.1 (Sub u uDy). 
  by rewrite Sub_imset imsetU inE.  
- move => u v; rewrite !inE negb_or => u_V1 /andP [vDy v_V2].
  case: psepV => sepV _.
  have v'_V2 : (Sub v vDy) \notin V1.
  { by apply: contraNN v_V2 => H; apply/imsetP; exists (Sub v vDy). }
  have vDx : v != x. 
  { apply: contraNneq x_V1 => ?; subst v. apply: sep_inR sepV _. 
    by rewrite /x' (bool_irrelevance xDy vDy). }
  case: (eqVneq u y) => [?|uDy]; first subst u. 
  + apply: contraFF (sepV.2 _ _ x_V1 v'_V2) => yv. 
    by rewrite /edge_rel/= eqxx vDx [v -- y]sgP yv orbT.
  + have u'_V1 : (Sub u uDy) \notin V2.
  { by apply: contraNN u_V1 => H; apply/imsetP; exists (Sub u uDy). }
    apply: contraFF (sepV.2 _ _ u'_V1 v'_V2) => uv. 
  rewrite /edge_rel/=. rewrite (negbTE vDx) /= andbT.
  by case: (eqVneq u x) => [<-|//]; rewrite [v -- u]sgP uv.
- case: psepV => _ [u [v [u_V1 v_V2]]]. 
  exists (val u),(val v). by rewrite !(inE,inj_imset) // negb_or (valP v).
Qed.

Lemma edge_separator (G : sgraph) (x y : G) : 
  4 < #|G| -> 3.-connected G -> x -- y -> ~ 3.-connected (smerge2 G x y) -> 
  exists z, vseparatorb [set x;y;z].
Proof.
move => largeG conn3G xy nconn3Gxy. 
have conn2Gxy : 2.-connected (smerge2 G x y) by apply: smerge_konnected.
have [|S /cards2P [z[w [zDw ->] [sep_zw small_zw]]]] := 
  kconnected_bounds _ conn2Gxy nconn3Gxy; first by rewrite -ltnS card_smerge2.
have xDy : x != y by rewrite sg_edgeNeq.
pose x' : smerge2 G x y := Sub x xDy.
have x_in : x' \in [set z; w]. 
{ apply: contraPT conn3G => Hx [_ min3].
  have /min3 := separator_from_smerge2 sep_zw Hx.
  by rewrite card_imset // cards2; case: (_ == _). }
wlog have: z w zDw sep_zw {x_in small_zw} / w = x' => [W|]; last subst w.
{ case/set2P : x_in => /esym; last exact: W sep_zw.
  rewrite eq_sym setUC in sep_zw zDw. exact: W sep_zw. }
exists (val z); apply/vseparatorP. 
have := smerge2_separator sep_zw.
by rewrite imsetU !imset_set1 /= [[set _;x]]setUC setUA [[set _;x]]setUC.
Qed.


(* This could be an alterative to the direct argument in
[contract_three_connected] 
Lemma component_two_connected (G : sgraph) (x y a : G) (A : {set G}) (S := [set x; y]) : 
  2.-connected G -> vseparator S -> 
  a \in A -> [disjoint A & S] -> connected A -> {in A & ~: A, forall x y, x--y -> y \in S} ->
  forall w, connected ((S :|: A) :\ w). *)


(** The following proposition drives the inductive proof of Wagner's
Theorem, as it allows maintainig 3-connectedness thoughout the
induction. *)
Proposition contract_three_connected (G : sgraph) :
  5 <= #|G| ->
  3.-connected G -> exists x y, x -- y /\ 3.-connected (smerge2 G x y).
Proof.
move=> le5G connG. 
suff : ~ forall x y, x -- y -> ~ 3.-connected (smerge2 G x y).
{ move => A. (* TODO: simplify? *)
  setoid_rewrite (rwP (kconnectedP _ _)). 
  setoid_rewrite (rwP andP).
  do 2 setoid_rewrite (rwP existsP).
  apply: contra_notT A => C x y xy. 
  apply: contraNnot C => H. apply/existsP;exists x; apply/exists_inP;exists y => //.
  exact/kconnectedP. }
move => not3xy. 
pose cmp3 (x y z : G) F := 
  [/\ x -- y, vseparator [set x;y;z], connected F & [disjoint F & [set x;y;z]]].
have [x [y [z [F [[xy sepF connF disjF] max_xyF]]]]] : exists (x y z : G) (F : {set G}), 
    cmp3 x y z F /\ forall x' y' z' F', cmp3 x' y' z' F' -> #|F'| <= #|F|.
{ pose p := [pred xyz : G * G * G | let: ((x,y),z) := xyz in 
            x -- y && vseparatorb [set x;y;z]].
  have [xyz0 p_xyz0] : exists xyz , p xyz. 
  { have [x[y xy]] := kconnected_edge connG.
    have [z Hz] := edge_separator le5G connG xy (not3xy _ _ xy).
    by exists ((x,y),z); rewrite /= xy /= Hz. }
  pose p' (xyz : G * G * G) := 
    [pred A | let: ((x,y),z) := xyz in connectedb A && [disjoint A & [set x;y; z]]].
  pose mcmp (xyz : G * G * G) : nat := \max_(A | p' xyz A) #|A|.
  pose xyz := arg_max xyz0 p mcmp.
  have inh_p' (xyz' : G * G * G) : p' xyz' set0. 
  { case: xyz' => -[x y] z /=; rewrite disjoints0 ?andbT.
    exact/connectedP/connected0. }
  pose F : {set G} := arg_max set0 (p' xyz) (fun x => #|x|).
  pose x := xyz.1.1; pose y := xyz.1.2; pose z := xyz.2.
  exists x, y,z, F. revert xyz F x y z. 
  case: arg_maxnP => // -[[x y] z] /= /andP [P1 P2] max_xyz. 
  case: arg_maxnP => // F /= /andP [/connectedP connF disF] maxF.
  split; first by split => //; exact/vseparatorP.
  move => x' y' z' F' [F1 /vseparatorP F2 /connectedP F3 F4]. 
  have:= max_xyz (x',y',z'); rewrite F1 F2 => /(_ isT) le_mcp.
  apply: (@leq_trans (mcmp (x,y,z))). 
  - apply: leq_trans le_mcp. by apply: leq_bigmax_cond => /=; rewrite F3.
  - by apply/bigmax_leqP => A; apply: maxF. }
have [_ min3sep] := connG.
pose H := [set x; y] :|: F.
have min_xyz : smallest vseparator [set x;y;z].
{ split => // V /min3sep. apply: leq_trans. exact: cards3. }
move defXYZ : [set x;y;z] => XYZ.
have /set0Pn[f f_F] : F != set0.
{ apply: contraTneq le5G => eqF0; rewrite -leqNgt.
  suff /subset_leq_card S : G \subset [set x;y;z]. 
    by apply: leq_trans S _; rewrite leqW // cards3.
  apply: wlog_neg => /subsetPn [u _ Hu].
  have:= max_xyF x y z [set u]; rewrite cards1 eqF0 cards0 ltnn.
  case/(_ _)/Wrap => //; split; rewrite ?disjoints1 //. exact: connected1. }
have compF : {in F & ~: F, forall u v, u -- v -> v \in XYZ}.
{ move=> u v u_F; rewrite !inE -defXYZ => vNF uv. apply/negPn/negP => vXYZ.
  suff/max_xyF : cmp3 x y z (v |: F). 
    by rewrite leqNgt cardsU1 vNF add1n leqnn.
  split => //; last by rewrite disjointsU // disjoints1.
  rewrite setUC; apply: connectedU_edge uv _ _  => //; last exact: connected1.
  by rewrite !inE eqxx. }
have psepH : proper_separation (F :|: XYZ) (~: F :|: XYZ).
{ rewrite defXYZ in min_xyz disjF.
  exact: component_separation min_xyz f_F disjF connF compF. }
have [u zu uNH] : exists2 u, z -- u & u \notin H.
{ rewrite defXYZ in min_xyz.
  have := @svseparator_neighbours _ _ _ z psepH. 
  rewrite setUUC -{2}defXYZ !inE eqxx; case => // u [v] [_ Hz _ zv].
  exists v => //. apply: contraNN Hz => {zv}. apply/subsetP : v. 
  by rewrite /H setUC setUS // -defXYZ subsetUl. }
have/andP [xDz yDz] : (x != z) && (y != z).
{ move/min3sep : sepF. rewrite -setUA !cardsU1 cards1 !inE (sg_edgeNeq xy) /=.
  by do 2 case: (_ == _). }
have zNF : z \in F = false by rewrite (disjointFl disjF) // !inE eqxx.
have zNH : z \notin H by rewrite !inE ![z == _]eq_sym !negb_or xDz yDz zNF.
have x_H : x \in H by rewrite !inE eqxx.
suff connH w : connected (H :\ w).
{ (* extending the [z--u] to a separator contradicts the maximality of F *)
  have [v /vseparatorP V2] := edge_separator le5G connG zu (not3xy _ _ zu).
  pose F' := H :\ v.
  have cmp3_F : cmp3 z u v F'. 
  { split => //; first exact: connH; rewrite disjoint_sym disjoint_subset. 
    apply/subsetP => i; rewrite !inE -orbA => /or3P[] /eqP->.
    - by rewrite ![z == _]eq_sym (negbTE xDz) (negbTE yDz) zNF.
    - by move: uNH; rewrite !inE => /negbTE ->.
    - by rewrite eqxx. }
  have:= max_xyF z u v F' cmp3_F. 
  rewrite /F'/H -setUA => X; have {X} := leq_trans (leq_cardsD1 _ _) X.
  rewrite !cardsU1 !inE sg_edgeNeq //= !(disjointFl disjF) ?add1n ?ltnn //.
  all: by rewrite !inE eqxx. }
case: (boolP (w \in [set x; y])) => [w_xy|].
{ (* [x] and [y] cannot disconnect [H] *)
  case/set2P : w_xy => ->. 
  - have -> : H :\ x = F :|: [set y].
      apply/setP => i; rewrite setUC !inE. case: (eqVneq i x) => // ->. 
      by rewrite (sg_edgeNeq xy) /= (disjointFl disjF) // !inE eqxx.
    have [v vy v_F] : exists2 v, v -- y & v \in F.
    { rewrite defXYZ in min_xyz. 
      have := @svseparator_neighbours _ _ _ y psepH. 
      rewrite setUUC -{2}defXYZ !inE eqxx; case => // v [?] [Hv _ vy _].
      exists v; rewrite 1?sgP //. by move: Hv; rewrite !inE negb_or negbK => /andP[]//. }
    apply: connectedU_edge vy _ _ => //. by rewrite inE eqxx. exact: connected1.
  - (* same as above - TODO: symmetry reasoning *)
    have -> : H :\ y = F :|: [set x].
      apply/setP => i; rewrite setUC !inE. case: (eqVneq i y) => // ->. 
      by rewrite [y==x]eq_sym (sg_edgeNeq xy) /= (disjointFl disjF) // !inE eqxx.
    have [v vx v_F] : exists2 v, v -- x & v \in F.
    { rewrite defXYZ in min_xyz. 
      have := @svseparator_neighbours _ _ _ x psepH. 
      rewrite setUUC -{2}defXYZ !inE eqxx; case => // v [?] [Hv _ vx _].
      exists v; rewrite 1?sgP //. by move: Hv; rewrite !inE negb_or negbK => /andP[]//. }
    apply: connectedU_edge vx _ _ => //. by rewrite inE eqxx. exact: connected1. }
rewrite !inE negb_or => /andP [wDx wDy].
pose Cx := [set v | connect (restrict (H :\ w) sedge) x v ].
wlog [s /setD1P [sNw s_H] sNCx] : / exists2 s, s \in H:\ w & s \notin Cx.
{ have [/exists_inP ?|] := boolP [exists s in H :\ w, s \notin Cx]; first by apply.
  move/exists_inPnn => C _. 
  apply: (@connected_center _ x); last by rewrite !inE eqxx eq_sym wDx.
  by move=> v /C; rewrite !inE. }
suff : separates x s [set w;z]. 
{ by move/separates_vseparator/min3sep; rewrite cards2; case (_ == _). }
have sDx : s != x by apply: contraNneq sNCx => ->; rewrite inE connect0.
have sDy : s != y. 
{ apply: contraNneq sNCx => ->; rewrite inE connect1 //= xy andbT. 
  by rewrite !inE !eqxx ![_ == w]eq_sym wDx wDy. }
have s_F : s \in F by move: s_H; rewrite !inE (negbTE sDx) (negbTE sDy).
have sDz : s != z by apply: contraTneq s_F => ->; rewrite zNF.
apply: separatesI; split.
- by rewrite !inE negb_or xDz eq_sym wDx.
- rewrite !inE negb_or sNw /=. by apply: contraNneq zNH => <-.
- elim/card_ind => p IHp Ip. 
  have [z_p|zNp] := boolP (z \in p); first by exists z => //; rewrite !inE eqxx.
  have W_xs (q : Path x s) : q \subset H -> w \in q.
  { move/subsetP => qH; apply: contraNT sNCx => wNq; rewrite inE. 
    apply: (connectRI q) => i i_q. rewrite inE qH // andbT inE. 
    by apply: contraNneq wNq => <-. }
  have [/W_xs|/subsetPn [i i_p iNH]] := boolP (p \subset H).
  { by exists w => //; rewrite !inE eqxx. }
  case def_p : _ / (isplitP Ip i_p) => [p1 p2 Ip1 Ip2 E1].
  have y_p2 : y \in p2. 
  { case: psepH => sepH _. 
    have [] := @separation_separates _ s i _ _ sepH. 
    - by rewrite !inE negb_or negbK s_F -defXYZ !inE (negbTE sDx) (negbTE sDy) sDz.
    - rewrite -defXYZ setUA [F :|: _]setUC -/H inE negb_or iNH inE.
      by apply: contraTneq i_p => ->.
    - move => _ _ /(_ (prev p2)) [y']; rewrite setUUC mem_prev -defXYZ => y'_p2.
      rewrite !inE -orbA => /or3P[] /eqP ?; subst y' => //. 
      + by apply: contraNT iNH => _; rewrite -(E1 x).
      + by rewrite def_p !inE y'_p2 orbT in zNp. }
  case def_p2 : _ / (isplitP Ip2 y_p2) => [p21 p22 Ip21 Ip22 E2].
  pose q := pcat (edgep xy) p22. 
  have q_sub_p : {subset q <= p}.
  { by move=>j; case/edgeLP => [->|]; rewrite ?def_p ?def_p2 ?inE // => ->. }
  have [||j J1 J2] := IHp q. 
  + apply/proper_card/properP; split; first exact/subsetP.
    exists i => //. apply: contraNN iNH => /edgeLP [->//|i_p22]. 
    by rewrite [i]E2 ?inE // eqxx.
  + rewrite irred_edgeL Ip22 andbT. apply: contraTN iNH => x_p22.
    by rewrite -(E1 x) ?negbK // def_p2 inE x_p22.
  + exists j => //. rewrite -def_p2 -def_p. exact: q_sub_p. 
Qed.


(** ** Isomorphims for vertex merging *)

Arguments inl_inj {A B}.
Arguments inr_inj {A B}.

(** The case for overlap 1 - one [smerge2] operation *)

Lemma diso_separation1 (G : sgraph) (V1 V2 : {set G}) (x : G) (xV1 : x \in V1) (xV2 : x \in V2) : 
  separation V1 V2 -> V1 :&: V2 = [set x] -> 
  let G' := (induced V1 ∔ induced V2)%sg in
  diso (smerge2 G' (inl (Sub x xV1)) (inr (Sub x xV2))) G.
Proof.
move=> sepV capV G'.
have sepV' u v : u \in V1 -> v \in V2 -> u != x -> v != x -> u -- v = false.
{ move=> uV1 vV2 uDx vDx. apply: sepV.2. 
  - apply: contraNN uDx => uV2. by rewrite -in_set1 -capV !inE uV1.
  - apply: contraNN vDx => vV1. by rewrite -in_set1 -capV !inE vV2. }
set x1 : G' := inl (Sub x xV1); set x2 : G' := inr (Sub x xV2).
set H := smerge2 _ _ _.
have h_dec (u : G) :    ({ uV1 : u \in V1 | inl (Sub u uV1) != x2 }) 
                      + ({ uV2 : u \in V2 | inr (Sub u uV2) != x2 }). 
{ case: {-}_ /(boolP (u \in V1)) => [p|uNV1]; first by left; exists p.
  have uV2 : u \in V2 by apply: sep_inR sepV _.
  right; exists uV2; rewrite (inj_eq inr_inj) -val_eqE /=.
  by rewrite -in_set1 -capV inE negb_and uNV1. }
pose h (u : G) : H := 
  match h_dec u with 
    inl (exist uV1 uDx2) => Sub (inl (Sub u uV1)) uDx2
  | inr (exist uV2 uDx2) => Sub (inr (Sub u uV2)) uDx2
  end.
pose g (x : H) : G := match val x with inl z => val z | inr z => val z end.
have can_g : cancel g h.
{ move => [[u uDx2|u uDx2]]; rewrite /g/h/=; apply: val_inj => /=. 
  - case: (h_dec _) => -[uV uDx2']; first by rewrite valK'. 
    case: notF ; rewrite (inj_eq inr_inj) -val_eqE /= in uDx2'.
    by rewrite -in_set1 -capV inE (valP u) uV in uDx2'.
  - case: (h_dec _) => -[uV uDx2']; last by rewrite /= valK'.
    case: notF ; rewrite (inj_eq inr_inj) -val_eqE /= in uDx2.
      by rewrite -in_set1 -capV inE (valP u) uV in uDx2. }
have can_h : cancel h g.
{ by move => u; rewrite /h/g; case: (h_dec u) => -[uV uDx2]. }
have hom_g : is_dhom g.
{ move => u v. 
 rewrite {1}/edge_rel/= /g. 
 rewrite -[sval u]/(val u) -[sval v]/(val v).
 case: (eqVneq (val u) x1) => [->|_]; case: (eqVneq (val v) x1) => [->|_] /=.
 - by rewrite sgP.
 - by case: (sval v) => -[z Hz] /=; rewrite {1 2}/edge_rel/= ?orbF 1?sg_sym.
 - by case: (sval u) => -[z Hz]; rewrite {1 2}/edge_rel/= ?orbF.
 - by case: (sval u) => -[z Hz]; case: (sval v) => -[z' Hz']. }
have hom_h : is_dhom h.
{ move => u v uv; rewrite /h. 
  case: (h_dec u) => -[uV uDx2]; case: (h_dec v) => -[vV vDx2] => //.
  - by apply: smerge2_edge.
  - rewrite /edge_rel/= !(inj_eq inl_inj) -!val_eqE /=.
    rewrite (inj_eq inr_inj) -val_eqE /= in vDx2.
    case: (eqVneq u x) => [?|vDx] /=; first by subst u; rewrite sgP. 
    by rewrite sepV' in uv. (* violates separation property *)
  - have uDx : u != x by rewrite (inj_eq inr_inj) -val_eqE /= in uDx2.
    rewrite /edge_rel/= !(inj_eq inl_inj) -!val_eqE /=.
    case: (eqVneq v x) => [?|vDx] /=; first by subst v.
    by rewrite sgP sepV' in uv. (* violates separation property *) }
exact: Diso'' can_g can_h _ _.
Qed.

(** The case for overlap 2 - two [smerge2] operations *)

(** In the case of a proper separtion [(V1,V2)] that overlaps in a set
[[set x;y]] with [x -- y], we need two [smerge2] operations to
collapse [induced V1] and [induced V2]. Given the complex definition
of the edge relation for [smerge2], this leads to a rather messy
construction. To alleviate this somewhat, we introduce an intermediate
construction [glue2] that merges two vertices from different graphs in
one go. *)

Section Glue2.
Variables (G : sgraph) (x y : G) (H : sgraph) (x' y' : H).

Definition glue2_vertex : Type := G + { z | z \notin [set x';y'] }.

Definition glue2_rel (u v : glue2_vertex) :=
  match u,v with
  | inl u, inl v => u -- v
  | inr u, inr v => val u -- val v
  | inl u, inr v => (u == x) && x' -- val v || (u == y) && y' -- val v
  | inr v, inl u => (u == x) && x' -- val v || (u == y) && y' -- val v
  end.

Lemma glue2_sym : symmetric glue2_rel.
Proof. move => [u|u] [v|v] //=; by rewrite sgP. Qed.

Lemma glue2_irrefl : irreflexive glue2_rel.
Proof. by move => [u|u] /=; rewrite sgP. Qed.

Definition glue2 := SGraph glue2_sym glue2_irrefl.

(** injection for elements of H *)
Definition glue2_r (z : H) : glue2.
refine (
  if @boolP (z == x') isn't AltFalse b1 then inl x else
    if @boolP (z == y') isn't AltFalse b2 then inl y else
      inr (Sub z _)  
); abstract (by rewrite !inE negb_or b1 b2).
Defined.

End Glue2.
Arguments glue2 : clear implicits.
Arguments glue2_r [G x y H x' y'] _.

Open Scope implicit_scope.

Lemma smerge2_glue2 (G H : sgraph) (x1 y1 : G) (x2 y2 : H) (p1 : inl y1 != inr x2) (p2 : inr y2 != inr x2) :
  x1 != y1 -> x1 -- y1 ->
  diso (smerge2 (smerge2 (G ∔ H)%sg (inl x1) (inr x2)) (Sub (inl y1) p1) (Sub (inr y2) p2))
       (glue2 G x1 y1 H x2 y2).
Proof.
move=> x1Dy1 x1y1.
set U' := smerge2 (G ∔ H)%sg (inl x1) (inr x2).
set U := smerge2 _ _ _.
(* neither smerge2 operation contracts an edge *)
have x1Nx2 : ~~ inl x1 -- inr x2 :> (G ∔ H)%sg by [].
have y1Ny2 p q : ~~ (Sub (inl y1) p) -- (Sub (inr y2) q) :> U'.
{ by rewrite /edge_rel/= eq_sym (inj_eq inl_inj) (negbTE x1Dy1). }
set V := glue2 _ _ _ _ _ _.
pose f (u : U) : V :=
  match val (val u) with
  | inl z => inl z 
  | inr z => glue2_r z
  end.
pose y1' : U := (Sub (Sub (inl y1) isT) isT).
pose x1' : U' := (Sub (inl x1) isT).
pose g (v : V) : U := 
  match v with
  | inl z => Sub (Sub (inl z) isT) isT
  | inr z => insubd y1' (insubd x1' (inr (val z)))
  end.
have gP1 z : z \notin [set x2; y2] -> val (insubd x1' (inr z)) = inr z.
{ move=> ?; rewrite insubdK // -topredE/= (inj_eq inr_inj); set_tac. }
have gP2 z : z \notin [set x2; y2] -> val (val (insubd y1' (insubd x1' (inr z)))) = inr z.
{ move=> ?. rewrite val_insubd -val_eqE gP1 //= ifT ?gP1 // (inj_eq inr_inj). by set_tac. }
have can_f : cancel f g.
{ rewrite /f/g. move => [[[u|u] U2] U1] => /=; do 2 apply: val_inj => //=.
  rewrite /glue2_r altF altF. rewrite !insubdK //=.
  rewrite -val_eqE /= in U1. by rewrite -topredE/= -val_eqE insubdK. }
have can_g : cancel g f.
{ rewrite /f/g. move => [v|[v Hv]] //=. 
  move : {-}(Hv); rewrite !(inE,negb_or) => /andP[vDx2 vDy2]. 
  rewrite insubdK; last by rewrite -topredE/= -val_eqE /= val_insubd vDx2.
  rewrite insubdK // /glue2_r !altF; congr (inr _). exact: val_inj. }
have hom_g : is_dhom g.
{ move => [u|[u Hu]] [v|[v Hv]]; rewrite /g/=.
  - move => ?. by do 2 apply: smerge2_edge. 
  - rewrite {1}/edge_rel/=. case/orP => -/andP[/eqP-> ev].
    + apply: smerge2_edge. apply: smerge2edgeL => //; by rewrite gP2 // sgP.
    + apply: smerge2edgeL => //; first by rewrite -val_eqE.
      by apply: smerge2_edge; rewrite gP2 //= sgP.
  - rewrite {1}/edge_rel/=. case/orP => -/andP[/eqP-> ev].
    + rewrite sgP. apply: smerge2_edge. apply: smerge2edgeL => //. 
      by rewrite gP2 // sgP.
    + rewrite sgP. apply: smerge2edgeL => //; first by rewrite -val_eqE.
      by apply: smerge2_edge; rewrite gP2 //= sgP.
  - rewrite {1}/edge_rel/= => uv. do 2 apply: smerge2_edge. by rewrite !gP2. }
have hom_f : is_dhom f.
{ rewrite /is_dhom. apply: smerge2Ecase => //; first by move=> ? ?; rewrite sgP.
  - (* edge of inner smerge operation (megring x1 and x2 *)
    move => [u Hu] [v Hv] /= uv. move: Hu Hv. pattern u,v. 
    apply: smerge2Ecase => //= {u v uv}.
    + move=> u v; split => A Hu Hv; rewrite sgP; apply: A. 
    + (* original edge *)
      move => [[u|u] Hu] [[v|v] Hv] //; rewrite /f/=. 
      rewrite -?val_eqE /= !(inj_eq inr_inj) => uv uDy2 vDy2. 
      by rewrite /glue2_r !altF /edge_rel/=.
    + (* edge modified by inner smerge2 operation *)
      move => [[u|u] Hu] // [[v|v] Hv] //=; first by rewrite andbF.
      case/andP=> [eq_u vx2]; rewrite /f/= -val_eqE /= (inj_eq inr_inj) => _ vDy2.
      rewrite /glue2_r 2!altF /edge_rel/=; apply/orP;left; apply/andP; split => //.
      by rewrite sgP.       
  - (* edge modified by outer smerge2 operation *)
    move => [u Hu] [v Hv] /= => /andP[/eqP ?]; subst u; rewrite /f/=.
    rewrite smerge2edgeD // => /or3P [].
    + case: v Hv => -[v|v] Hv' Hv //= vy2. rewrite -val_eqE /= in Hv.
      rewrite /glue2_r 2!altF. rewrite /edge_rel/= eqxx [y2 -- _]sgP.
      by apply/orP; right.
    + case/andP => [def_v E]. rewrite (eqP def_v).
      by rewrite /edge_rel/= sgP.
    + done. }
exact: Diso'' can_f can_g hom_f hom_g.
Qed.

Lemma separation_capN (G : sgraph) (V1 V2 : {set G}) u v :
  separation V1 V2 -> u \in V1 -> v \in V2 -> u -- v -> (u \in V1 :&: V2) || (v \in V1 :&: V2).
Proof.
move => sepV uV1 vV2 uv; rewrite !inE uV1 vV2 andbT /=. 
by apply: contraTT uv; rewrite negb_or => /andP[uNV2 vNV1]; rewrite sepV.
Qed.

Lemma diso_separation2_glue (G : sgraph) (V1 V2 : {set G}) (x y : G) 
  (xV1 : x \in V1) (xV2 : x \in V2) (yV1 : y \in V1) (yV2 : y \in V2) : 
  separation V1 V2 -> V1 :&: V2 = [set x;y] -> 
  diso (glue2 (induced V1) (Sub x xV1) (Sub y yV1) (induced V2) (Sub x xV2) (Sub y yV2)) G.
Proof.
set x' := Sub x xV2; set y' := Sub y yV2.
move => sepV capV; set H := glue2 _ _ _ _ _ _.
pose g (u : H) : G := 
  match u with inl u => val u | inr u => val (val u) end.
have h_dec (u : G) : (u \in V1) + ({ uV2 : u \in V2 | Sub u uV2 \notin [set x';y'] }). 
{ case: (boolP (u \in V1)) => [|uV1]; [by left|right].
  by exists (sep_inR sepV uV1); rewrite in_set2 -!val_eqE /= -in_set2 -capV inE (negbTE uV1). }
have h_dec_l u (uV1 : u \in V1) : h_dec u = inl uV1.
{ case: (h_dec u) => [uV1'|[uV2 p]]; first by congr(inl _); exact: bool_irrelevance.
  case: notF. by rewrite in_set2 -!val_eqE /= -in_set2 -capV !inE uV1 uV2 in p. }
have h_dec_r u (uV2 : u \in V2) (p : Sub u uV2 \notin [set x';y']) : h_dec u = inr (Sub uV2 p).
{ case: (h_dec u) => [uV1|[uV2' p']]; last by congr (inr _); apply: val_inj; apply: bool_irrelevance.
  case: notF. by rewrite in_set2 -!val_eqE /= -in_set2 -capV !inE uV1 uV2 in p. }
pose h (u : G) : H := 
  match h_dec u with 
  | inl uV1 => inl (Sub u uV1) 
  | inr (exist uV2 p) => inr (Sub (Sub u uV2) p)
  end.
have can_g : cancel g h.
{ move => [[u uV1]|[[u uV2] p]]; rewrite /h/g/=. 
  + by rewrite h_dec_l.
  + by rewrite h_dec_r. }
have can_h : cancel h g.
{ by move => u; rewrite /h; case: (h_dec _) => [uV1|[uV1 p]]. }
have hom_g : is_dhom g.
{ move=> u v. rewrite [u -- v]/edge_rel/=.
  move: u v => [u|u] [v|v] //=. by case/orP => [/andP[/eqP->]|/andP[/eqP->]].
  case/orP => [/andP[/eqP->]|/andP[/eqP->]] //; by rewrite sgP. }
have hom_h : is_dhom h.
{ move => u v uv. rewrite /h/edge_rel/=. 
  case: (h_dec u) => [uV1|[uV2 p]]; case: (h_dec v) => [vV1|[vV2 q]] /=.
  1,4 : by rewrite induced_edge.
  - rewrite !inE -!val_eqE /= -in_set2 in q.
    rewrite -!val_eqE !induced_edge /=. 
    have := separation_capN sepV uV1 vV2 uv; rewrite capV (negbTE q) orbF.
    by case/set2P => ?; subst u; rewrite eqxx uv.
  - rewrite !inE -!val_eqE /= -in_set2  in p.
    rewrite -!val_eqE !induced_edge /=; rewrite sgP in uv.
    have := separation_capN sepV vV1 uV2 uv; rewrite capV (negbTE p) orbF.
    by case/set2P => ?; subst v; rewrite eqxx uv. }
exact: Diso'' hom_g hom_h.
Qed.

Lemma diso_separation2 (G : sgraph) (V1 V2 : {set G}) (x y : G) 
   (xV1 : x \in V1) (xV2 : x \in V2) (yV1 : y \in V1) (yV2 : y \in V2)
   (G1 := induced V1) (G2 := induced V2) (G12 := (G1 ∔ G2)%sg)
   (x1 : G12 := inl (Sub x xV1)) (x2 : G12 := inr (Sub x xV2))
   (y1 : G12 := inl (Sub y yV1)) (y2 : G12 := inr (Sub y yV2))
   (y1Gm : y1 != x2) (y2Gm : y2 != x2) :
  separation V1 V2 -> V1 :&: V2 = [set x; y] -> x -- y ->
  diso (smerge2 (smerge2 (G1 ∔ G2) x1 x2) (Sub y1 y1Gm) (Sub y2 y2Gm)) G.
Proof.
move=> sepV capV xy.
have := diso_separation2_glue xV1 xV2 yV1 yV2 sepV capV.
apply: diso_comp. apply: smerge2_glue2 => //.
by rewrite -val_eqE /= sg_edgeNeq.
Qed.
