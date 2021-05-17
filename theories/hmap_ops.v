From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries bij.
From fourcolor Require Import hypermap geometry cfmap jordan color coloring combinatorial4ct.
From fourcolor Require Import walkup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Combinatorial Hypermaps (requires coq-fourcolor) *)

(** ** Preliminaries *)

(** These lemmas depend only on definitions within the fourcolor
development. Among other thins, we provide dedicated lemmas for the
derived Walkup operations, to simplify their application *)

Lemma genus_walkupN_eq (G : hypermap) (z : G) : 
  ~~ cnode z (face z) -> genus (WalkupN z) = genus G.
Proof. 
move => ncross. 
rewrite /WalkupN genus_permF genus_WalkupE_eq ?genus_permN //.
by right.
Qed.

Lemma genus_walkupF_eq (G : hypermap) (z : G) : 
  ~~ cface z (edge z) -> genus (WalkupF z) = genus G.
Proof. 
move => ncross. 
rewrite /WalkupN genus_permN genus_WalkupE_eq ?genus_permF //.
by right.
Qed.

Lemma le_genus_WalkupF (G : hypermap) (x : G) : genus (WalkupF x) <= genus G.
Proof. by rewrite genus_permN -[X in _ <= X]genus_permF le_genus_WalkupE. Qed.

Lemma loopless_face (G : hypermap) (x : G) : plain G -> loopless G -> ~~ cnode x (face x).
Proof. move => plFG /existsPn llG. by rewrite cnode1r plain_eq'. Qed.

Lemma genus_gt0 (D : hypermap) : 
  (0 < genus D) = (0 < Euler_lhs D - Euler_rhs D).
Proof. by rewrite even_genusP -addnBA // subnn addn0 double_gt0. Qed.

Lemma EqHypermapEN (G : hypermap) (e n f : G -> G) (Eenf : cancel3 e n f) :
  edge =1 e -> node =1 n -> G =m Hypermap Eenf.
Proof.
move => eE nE; suff fE : face =1 f by apply: EqHypermap.
by move => x; rewrite -{1}[x](@faceK (Hypermap Eenf)) /= -eE -nE nodeK.
Qed.

#[export] Hint Resolve faceI nodeI edgeI : core.

Lemma gcompF (G : hypermap) : subrel (cface : rel G) gcomp. 
Proof. by apply: connect_sub => u v /= A; apply: connect1; rewrite /glink/= A. Qed.

Lemma gcompN (G : hypermap) : subrel (cnode : rel G) gcomp. 
Proof. by apply: connect_sub => u v /= A; apply: connect1; rewrite /glink/= A. Qed.


Lemma loopless_arity (G : hypermap) : 
  plain G -> loopless G -> forall x : G, 1 < arity x.
Proof. 
move=> plainG llG; apply/forallP; apply: contraNT llG.
case/forallPn => x; rewrite -leqNgt => ar_le_1.
have ar1 : arity x = 1 by apply/eqP; rewrite eqn_leq ar_le_1 order_gt0.
have := iter_face_arity x; rewrite ar1 /= => fx.
existsb x. by rewrite -plain_eq' // fx -cnode1r.
Qed.


(** ** Adjacency *)

(**We define adjaceny of nodes. In the four-color theorem [adj] is used to denote adjacency of face, hence we use [adjn] here. *)

Definition adjn {D : hypermap} (x y : D) := [exists z in cnode x, edge z \in cnode y].

Lemma adjnI (G : hypermap) (z x y : G) : 
  cnode x z -> cnode y (edge z) -> adjn x y.
Proof. by move => ? ?; apply/exists_inP; exists z. Qed.
Arguments adjnI G z [x y].

Lemma adjn_node1 (G : hypermap) (x y : G) : adjn x y = adjn (node x) y.
Proof. by apply: eq_existsb => z; rewrite !inE -cnode1. Qed.

Lemma adjn_node1r (G : hypermap) (x y : G) : adjn x y = adjn x (node y).
Proof. by apply: eq_existsb => z; rewrite !inE -cnode1. Qed.

Lemma adjn_edge (G : hypermap) (x : G) : adjn x (edge x).
Proof. exact: (adjnI G x). Qed.

Lemma adjnC (G : hypermap) (x y : G) : 
  plain G -> adjn x y = adjn y x.
Proof.
move=> plain_G.
wlog suff S : x y / adjn x y -> adjn y x; first by apply/idP/idP; exact: S.
case/exists_inP => z; rewrite !inE => x_z z_ez. 
by apply/exists_inP; exists (edge z); rewrite // plain_eq.
Qed.

Lemma adjn_loopless (D : hypermap) (x y : D) : 
  loopless D -> cnode x y -> adjn x y = false.
Proof.
move => llD n_xy. apply: contraNF llD => /exists_inP[z]; rewrite !inE => n_xz n_y_ez.
existsb z. apply: connect_trans n_y_ez. apply: connect_trans n_xy. by rewrite cnodeC.
Qed.


(** ** Isomorphims of Hypermaps *)

Arguments bij_injective [A B] f [_ _] _.
Arguments bij_injective' [A B] f [_ _] _.

Section HIso.
Variable (G H : hypermap).

Record hiso := Hiso { 
  hiso_dart :> bij G H;
  hiso_edge x : hiso_dart (edge x) = edge (hiso_dart x);
  hiso_node x : hiso_dart (node x) = node (hiso_dart x) }.

Lemma hiso_face (i : hiso) x : i (face x) = face (i x).
Proof. by rewrite -{2}[x]faceK hiso_edge hiso_node nodeK. Qed.

(** Commutation of the third permutation is a consequence. We could
provide "smart" constructors in case one of [hiso_edge] or [hiso_node]
is harder to establish than [hiso_face]. So far, this is not needed. *)

Hypothesis (i : hiso).

Lemma comm_adj (e' : rel H) (e : rel G) (a : pred H) :
  (forall x y, e' (i x) (i y) = e x y) -> rel_adjunction i e' e a.
Proof.
move => com. constructor; first by move => x _; exists (i^-1 x); rewrite bijK'.
move => x' y' _. apply/idP/idP; case/connectP. 
- move => p pth_p ->. elim: p x' pth_p => //= z' p IHp x' /andP [E pth_p].
  rewrite -com in E. exact: connect_trans (connect1 E) (IHp _ pth_p).
- move => p pth_p I. rewrite -[y'](bijK i) {}I.
  elim: p x' pth_p => //= [x' _|z' p IHp x' /andP [E pth_p]]; first by rewrite bijK.
  rewrite -[z'](bijK' i) com in E.
  apply: connect_trans (connect1 E) _. rewrite -[z'](bijK' i) in pth_p.
  move/IHp in pth_p. by rewrite bijK' in pth_p.
Qed.

Lemma hiso_fcard (f : G -> G) (f' : H -> H) : 
  injective f ->
  (forall x, i (f x) = f' (i x)) -> fcard f G = fcard f' H.
Proof.
move => inj_f com_f_f'.
have inj_f' : injective f'.
{ move => x y. rewrite -{1}[x](bijK' i) -{1}[y](bijK' i) -!com_f_f'.
  by move/(bij_injective i)/inj_f/(bij_injective' i). }
suff adj : fun_adjunction i f' f H. 
{ rewrite (adjunction_n_comp _ _ _ _ adj) //; exact: fconnect_sym. }
apply: comm_adj => //= x y. by rewrite -com_f_f' inj_eq.
Qed.

Lemma hiso_fconnect (f : G -> G) (f' : H -> H) : 
  (forall x, i (f x) = f' (i x)) -> 
  forall x y, fconnect f x y = fconnect f' (i x) (i y).
Proof. 
move => com x y. apply: rel_functor. apply: (comm_adj H). 2: done.
by move => {x y} x y; rewrite /= -com inj_eq.
Qed.

Definition hiso_cedge := hiso_fconnect (hiso_edge i).
Definition hiso_cnode := hiso_fconnect (hiso_node i).
Definition hiso_cface := hiso_fconnect (hiso_face i).

Lemma hiso_genus : genus G = genus H.
Proof.
have fcardF := hiso_fcard faceI (hiso_face i).
have fcardN := hiso_fcard nodeI (hiso_node i).
have fcardE := hiso_fcard edgeI (hiso_edge i).
rewrite /genus /Euler_rhs fcardF fcardN fcardE; do 2 f_equal.
rewrite /Euler_lhs. rewrite (card_bij i). 
suff adj : rel_adjunction i glink glink H. 
{ rewrite (adjunction_n_comp _ _ _ _ adj) //; exact: glinkC. }
apply: comm_adj => x y.
by rewrite /glink/= -hiso_edge -hiso_face -hiso_node !(inj_eq).
Qed.

Lemma hiso_plain : plain G = plain H.
Proof.
congr (is_true _); apply/plainP/plainP.
- move => plainG x _; have [G1 G2] := plainG (i^-1 x) isT.
  by rewrite -[x](bijK' i) -!hiso_edge G1 inj_eq.
- move => plainH x _; have [H1 H2] := plainH (i x) isT.
  rewrite -!hiso_edge inj_eq // in H1 H2.
  by rewrite H2 (bij_injective i H1).
Qed.

Lemma hiso_adjn x y : adjn (i x) (i y) = adjn x y.
Proof. 
apply/exists_inP/exists_inP => -[z Z1 Z2].
- exists (i^-1 z); first by rewrite inE hiso_cnode bijK'.
  by rewrite inE hiso_cnode hiso_edge bijK'.
- exists (i z); first by rewrite inE -hiso_cnode.
  by rewrite inE -hiso_edge -hiso_cnode.
Qed.

End HIso.

Tactic Notation "hiso" uconstr(f) :=
  match goal with |- hiso ?F ?G => apply (@Hiso F G f) end.

Lemma hiso_glink (G G' : hypermap) (h : hiso G G') x y : 
  glink x y = glink (h x) (h y).
Proof. 
by rewrite /glink/= -hiso_edge -hiso_node -hiso_face !inj_eq.
Qed.

(** Special case where the shape of both graphs is known and the
isomorphim is the identity. Used for symmetry reasoning with [merge] *)
Lemma hiso_id_glink (D : finType) e n f eK e' n' f' eK' :
  let G := @Hypermap D e n f eK in
  let G' := @Hypermap D e' n' f' eK' in 
  forall (i : hiso G' G), i =1 id -> @glink G' =2 @glink G.
Proof. 
move => G G' i iE x z. by rewrite (hiso_glink i) !iE.
Qed.
Arguments hiso_id_glink [D] [e n f]%function_scope [eK] [e' n' f']%function_scope [eK'].

(** ** Operations on Hypermaps *)

(** *** The Switch Construct *)

(** The switch function switches the successors of two elements of a
permutation. (The definition doesn't require injectivity, but we
mainly use it on the permutations making up hypermap). This is a
fairly basic operation and can be used to implement the spliting and
merging of nodes (node cycles) in a way that preserves planarity *)

Section switch.
Variable (G : finType).

Definition switch x y (f : G -> G) := [fun z => 
  if z == x then f y else
  if z == y then f x else f z].

Lemma switchxx x f : switch x x f =1 f.
Proof. move => z /=. by case (altP (z =P x)) => [->|]. Qed.

Lemma switchC x y f : switch x y f =1 switch y x f.
Proof. 
case: (altP (x =P y)) => [<-|xDy]; rewrite ?switchxx //= ?eqxx.
move => z /=. do ! (case (z =P _) => [->|] //); by rewrite (negbTE xDy). 
Qed.

Lemma fswitchC x y f : fconnect (switch x y f) =2 fconnect (switch y x f).
Proof. apply: eq_fconnect. exact: switchC. Qed.

Variables (x y : G).

Lemma switchK f : switch x y (switch x y f) =1 f.
Proof. 
move => z. case: (altP (x =P y)) => [<-|xDy]; rewrite ?switchxx //= ?eqxx.
case: (altP (z =P x)) => [->|zDx].
- by rewrite [_ == x]eq_sym (negbTE xDy).
- by case: (altP (z =P y)) => // ->.
Qed.

Lemma switchE f : {in [predC (pred2 x y)], switch x y f =1 f}.
Proof. move => z. rewrite !inE /switch/=. by do 2 (case (_ == _)). Qed.

Lemma switch_base f : fun_base id f (switch x y f) (pred2 x y).  
Proof. move=> u v ?. by rewrite [switch]lock /= -lock switchE. Qed.


Hypothesis (f : G -> G) (inj_f : injective f).
Local Notation xswitch := (switch x y f).

Lemma can_switch : cancel xswitch (switch (f y) (f x) (finv f)).
Proof. 
move => z; case: (altP (x =P y)) => [->|xDy]; rewrite ?switchxx ?finv_f //=.
case: (altP (z =P x)) => [->|zDx]; first by rewrite eqxx finv_f.
case: (altP (z =P y)) => [->|zDy]; first by rewrite (inj_eq inj_f) (negbTE xDy) eqxx finv_f.
by rewrite !(inj_eq inj_f) ?(negbTE zDy) ?(negbTE zDx) ?eqxx finv_f.
Qed.

Lemma switch_inj : injective xswitch.
Proof. exact: can_inj can_switch. Qed.  

Lemma fconnect_f_switch z : 
  ~~ fconnect f x z -> fconnect f z y -> fconnect xswitch z y.
Proof.
move => N /connectP [p]; elim: p z N => //= [_ _ _ -> //|u p IH z N /andP[/eqP E P L]].
have zDx : z != x by apply: contraNneq N => ->.
case: (altP (z =P y)) => [-> //|zDy].
apply: connect_trans (connect1 _) (IH _ _ P L) => /=.
- by rewrite (negbTE zDx) (negbTE zDy) E.
- by rewrite -E -same_fconnect1_r.
Qed.

Lemma iter_switchE z m : 
  (forall n, n < m -> iter n f z \in [predC pred2 x y]) -> 
  forall k, k <= m -> iter k xswitch z = iter k f z.
Proof.
move => H k lt_m. 
have {H lt_m m} : forall n : nat, n < k -> iter n f z \in [predC pred2 x y]. 
{ by  move => n Hn; apply: H; apply: leq_trans lt_m. }
elim: k z => // k IH z Hk; rewrite !iterSr switchE ?IH // ; last exact: (Hk 0).
move => n Hn; by rewrite -iterSr Hk // ltnS.
Qed.


Lemma fconnect_switched (xDy : x != y) : fconnect xswitch x y  = ~~ fconnect f x y.
Proof.
have ? := switch_inj.
apply/idP/idP.
- apply: contraTN => fc_xy; rewrite same_fconnect1 //= eqxx. 
  have [? ?] : fconnect f (f y) y /\ fconnect f (f y) x. 
  { by rewrite -!same_fconnect1 ?connect0 1?fconnect_sym. }
  pose m := findex f (f y) x; pose n := findex f (f y) y.
  have m_lt_n : m < n. 
  { rewrite /m /n ltn_neqAle; apply/andP; split.
    - apply: contra_neq (xDy). by apply: index_inj; rewrite -fconnect_orbit.
    - by rewrite -{3}[y](finv_f inj_f) findex_finv -ltnS orderSpred findex_max. }
  have switch_f k : k <= m -> iter k xswitch (f y) = iter k f (f y).
  { apply: iter_switchE => j j_lt_k. rewrite !inE negb_or. 
    rewrite !before_findex -?same_fconnect1 -1?fconnect_sym //.
    exact: ltn_trans j_lt_k _. }
  have: looping xswitch (f y) m.+1.
  { by rewrite /looping trajectS iterS switch_f // iter_findex /= ?eqxx ?mem_head. }
  apply: iter_looping => k k_lt_m. rewrite switch_f //. apply: before_findex => //.
  exact: leq_trans m_lt_n.
- move => N. rewrite same_fconnect1 //= eqxx. apply: fconnect_f_switch.
  + by rewrite -same_fconnect1_r.
  + by rewrite -same_fconnect1.
Qed.

Lemma fconnect_switchV z :  
  fconnect f z x -> fconnect xswitch z x || fconnect xswitch z y.
Proof. 
move => fc_zx; case: (boolP (fconnect (switch x y f) z x)) => //=. 
case/connectP : (fc_zx) => p; elim: p z fc_zx => /= [? _ _ <- //|]; first by rewrite connect0.
have ? := switch_inj; move => a p IHp z fc_zx /andP [/eqP<- P1 P2] sw_zx. 
wlog zDxy : / z \in [predC pred2 x y].
{ move => W; case: (altP (z =P y)) => [-> //|zDx]; apply: W; rewrite !inE (negbTE zDx) orbF.
  by apply: contraNneq sw_zx => ->. }
rewrite same_fconnect1 ?switchE // in sw_zx.
by rewrite same_fconnect1 ?switchE ?IHp // -?same_fconnect1.
Qed.

End switch.
Arguments switchK {G x y f}.
Arguments switchC {G x y f}.
Arguments eq_fclosure {T f f' a}.

Lemma closure_switched (G : finType) (x y : G) (f : G -> G) (inj_f : injective f) :
  fclosure f (pred2 x y) =i fclosure (switch x y f) (pred2 x y).
Proof.
wlog suff: f inj_f / {subset fclosure f (pred2 x y) <= fclosure (switch x y f) (pred2 x y)}.
{ move => W z; apply/idP/idP; first exact: W.
  move/W; rewrite (eq_fclosure switchK); apply; exact: switch_inj. }
move => z /closureP -[u] /pred2P [->|->] f_z; apply/closureP. 
- by have [A|A] := orP (fconnect_switchV y inj_f f_z); [exists x| exists y] => //; rewrite inE eqxx.
- have := (fconnect_switchV x inj_f f_z); rewrite ![fconnect (switch y x f) _ _](eq_fconnect switchC).
  by case/orP; [exists y| exists x] => //; rewrite inE eqxx.
Qed.

Section switch.
Hypothesis (G : finType) (f : G -> G) (inj_f : injective f).

Lemma fcard_switch x y (xDy : x != y) :
  fcard (switch x y f) G = if fconnect f x y then (fcard f G).+1 else (fcard f G).-1.
Proof.
pose xswitch := switch x y f.
have f_sym := fconnect_sym inj_f; have sw_sym := fconnect_sym (@switch_inj _ x y _ inj_f).
pose a := fclosure f (pred2 x y).
have cCa : fclosed f [predC a] by apply/predC_closed/closure_closed.
have eq_ab : a =i fclosure xswitch (pred2 x y) by apply: closure_switched.
rewrite (n_compC a) (eq_n_comp_r eq_ab) (n_comp_closure2 sw_sym).
rewrite (n_compC a) (n_comp_closure2 f_sym). 
have adj_f: fun_adjunction id f xswitch (predC a).
{ apply: strict_adjunction => //.
  - by apply/subsetP => z _; rewrite -[z]/(id z) codom_f.
  - move => u v H. apply: switch_base. apply: contraNN H. 
    rewrite [in X in _ -> X]/= negbK; exact: mem_closure. }
rewrite fconnect_switched // negbK (adjunction_n_comp _ f_sym sw_sym _ adj_f) //.
rewrite !(eq_n_comp_r (_ : _ =i [predC a])) //.
by case: (fconnect f x y); rewrite /= ?add2n ?add1n.
Qed.

(** More lemmas on [switch], mainly for the case where [~~ fconnect f
x y], mainly used when reasoning about adjacency in [merge G x y]. *)

Lemma fconnect_switch_x_fx x y : 
  ~~ fconnect f x y -> fconnect (switch x y f) x (f x).
Proof.
move=> n_xy; have xDy : x != y by apply: contraNneq n_xy => ->.
apply: (connect_trans (y := y)); first by rewrite fconnect_switched.
by apply: connect1; rewrite /= ?eqxx [_ == x]eq_sym (negbTE xDy).
Qed.

Lemma switch_subrel x y : 
  ~~ fconnect f x y -> subrel (fconnect f) (fconnect (switch x y f)).
Proof.
move => n_xy u v. 
case/connectP => p; elim: p u => [|z p IHp] u /=; first by move => _ ->.
move => /andP[/eqP fu pth_p] lst_p. 
apply: (connect_trans (y := z)); last exact: IHp.
rewrite -fu => {IHp z pth_p lst_p fu}. 
have [u_xy|uNxy] := boolP (u \in pred2 x y); last first.
  by apply: connect1; rewrite [switch]lock /= -lock switchE.
case/pred2P : u_xy => ->; first exact: fconnect_switch_x_fx.
by rewrite fswitchC; apply: fconnect_switch_x_fx; rewrite fconnect_sym.
Qed.

Variables (x y : G).

Lemma switch_disconnected_lr u v : 
  ~~ fconnect f x y -> fconnect f x u -> fconnect f y v -> fconnect (switch x y f) u v.
Proof.
case: (eqVneq x y) => [->|xDy]; first by rewrite connect0.
move => xy. move: (xy); rewrite -fconnect_switched // => sxy xu yv.
apply: connect_trans _ (switch_subrel xy yv).
apply: connect_trans sxy. apply: (switch_subrel xy).
by rewrite fconnect_sym.
Qed.

Lemma fconnect_switchE_aux u v : ~~ fconnect f x y -> 
  fconnect (switch x y f) u v -> 
  [|| fconnect f u v, fconnect f u x && fconnect f v y | fconnect f u y && fconnect f v x].
Proof.
move => n_xy. case: (boolP (fconnect f u v)) => //= fNuv sw_uv.
have [Cu Cv] : u \in fclosure f (pred2 x y) /\ v \in fclosure f (pred2 x y).
{ have sw_inj := @switch_inj _ x y _ inj_f.
  have ? := fconnect_sym sw_inj.
  wlog suff S : u v fNuv sw_uv / u \in fclosure f (pred2 x y).
    by split; [exact: (S u v)|apply: (S v u)]; rewrite fconnect_sym.
  rewrite closure_switched // closure_pred2 // inE /= -!closure1 //.
  apply: contraNT fNuv; rewrite negb_or !inE ![_ _ _ u]fconnect_sym //. 
  move/andP => [A B]. apply : sub_in_connect sw_uv => z Hz z' /=.
  rewrite /switch/= [z == x]rwF 1?[z == y]rwF //; by apply: contraTneq Hz => ->. }
case/closureP : Cu => /= ? /pred2P [-> f_ux|-> f_uy]. 
  case/closureP : Cv => /= ? /pred2P [-> f_vx|-> ->]; last by rewrite f_ux.
  apply: contraNT fNuv => _. apply: connect_trans f_ux _. by rewrite fconnect_sym.
case/closureP : Cv => /= ? /pred2P [-> ->|-> f_vy]; first by rewrite f_uy.
apply: contraNT fNuv => _. apply: connect_trans f_uy _. by rewrite fconnect_sym.
Qed.

Lemma fconnect_switchE u v : ~~ fconnect f x y -> 
  fconnect (switch x y f) u v =
  [|| fconnect f u v, fconnect f u x && fconnect f v y | fconnect f u y && fconnect f v x].
Proof.
move => n_xy. apply/idP/idP; first exact: fconnect_switchE_aux.
case/or3P; first exact: switch_subrel.
  by case/andP => ? ?; apply: switch_disconnected_lr => //; by rewrite fconnect_sym.
case/andP => ? ?. rewrite fconnect_sym; last exact: switch_inj.
apply: switch_disconnected_lr => //; by rewrite fconnect_sym.
Qed.

End switch.

(** *** The merge operation *)

(** When called on two darts [x] and [y] from distinct node cycles,
[merge G x y] merges the node cycles of [x] and [x] at [x] and [y] by
swapping their node successors, and adapting the face permutation
accordingly. This operation is clearly self-inverting, but for now we
only use it to merge nodes, and not to split nodes. *)

Section merge.
Variable (G : hypermap).

Lemma merge_cancel3 (x y : G) :
  cancel3 edge (switch x y node) (switch (finv face y) (finv face x) face).
Proof. 
move => z /=. rewrite !f_finv //. 
case: (altP (edge z =P finv face y)) => [|A].
  rewrite eqxx -{2}[y](f_finv faceI) => <-. exact: edgeK.
case: (altP (edge z =P finv face x)) => [e_z|B].
  by case: (altP (y =P x)) => [->|?]; rewrite ?eqxx -[z]edgeK e_z f_finv.
rewrite !ifF ?edgeK //. 
- apply: contra_neqF A => /eqP <-. by rewrite finv_f.
- apply: contra_neqF B => /eqP <-. by rewrite finv_f.
Qed. 

Definition merge (x y : G) := Hypermap (merge_cancel3 x y).

End merge.

Definition merge_inv (G : hypermap) (x y : G) : hiso (@merge (@merge G x y) x y) G.
Proof. hiso bij_id => //. exact: switchK. Defined.

Lemma merge_inv_eqm (G : hypermap) (x y : G) : @merge (@merge G x y) x y =m G.
Proof.
case: G x y => D e n f /= eK x y; apply: EqHypermapEN => //=. 
exact: switchK. 
Qed.

Definition mergeC (G : hypermap) (x y : G) : hiso (merge x y) (merge y x).
Proof. hiso bij_id => //. exact: switchC. Defined.

Lemma mergeC_eqm (G : hypermap) (x y : G) : merge x y =m merge y x.
Proof. apply: EqHypermapEN => //=. exact: switchC. Qed.

Arguments clinkF {G x}.

Arguments switch : simpl never.

(** The rest of this subsection is devoted to showing that [merge G x y]
 preserves the genus of [G] whenever we have either [~~ gcomp x y]
or [(cnode x y (+) cface x y)]. Here we went to route to pove this
direcly showing that the Euler formula is preserved. As an
alternative, it would be possible to express the "merge" direction as
an inverse-WalupF (splitting the face-cycle) followed by a WalkupN
operation (merging the node cycles). However, this would require
making the intermediate hypermap explicit and would not be a nice as
for other operations, that can be expressed as (inverse) double Walkup
operations. *)

(** This proof is unintelligible without [Set Printing Implicit.] *)
Set Printing Implicit.

Lemma closure_merged (G : hypermap) (x y : G) (xDy : x != y) :
  closure (@glink (merge x y)) (pred2 x y) =i closure glink (pred2 x y).
Proof.
wlog suff S : G x y xDy / 
  closure (@glink (merge x y)) (pred2 x y) \subset closure glink (pred2 x y).
{ apply/subset_eqP/andP; split; first exact: S. 
  suff E: @glink (@merge (merge x y) x y) =2 @glink G. 
    rewrite -(eq_subset (eq_closure _ (eq_connect E))). exact: S.
  case: G x y {xDy} => D e n f eK x y. 
  pose i := merge_inv x y. by apply: (hiso_id_glink i). }
apply/subsetP => z /closureP [x0]; rewrite !inE => x_or_y.
wlog -> : G x y xDy z x0 {x_or_y} / x0 = x.
{ move => W. case/pred2P : x_or_y => [|A B]; first exact: W. 
  have {B} B : (gcomp : rel (merge y x)) z x0 by rewrite -(eq_connect (hiso_id_glink (mergeC x y) _)).
  have {W} W := W G y x _ z x0 A B. 
  rewrite (eq_closure_r (_ : pred2 x y =i pred2 y x)) ?W 1?eq_sym //.
  by move => u ; rewrite !inE orbC. }
rewrite -clink_glink ; case/connectP => p. 
elim: p z => /=  [z _ -> |z p IH z' /andP [l_z'_z pth_p] lst_p]; first by apply: mem_closure; rewrite !inE eqxx.
have {IH pth_p lst_p} IHp := IH _ pth_p lst_p.
rewrite -(eq_closure _ (@clink_glink _)); rewrite -(eq_closure _ (@clink_glink _)) in IHp.
have [? ?] : x \in pred2 x y /\ y \in pred2 x y by rewrite !inE !eqxx.
case/clinkP : l_z'_z => [E|]. 
- rewrite {}E /=. case: (altP (z =P x)) => [Ez|zDx]; last case: (altP (z =P y)) => [Ez |zDy]. 
  + apply/closureP; exists y => //. by rewrite connect1 // clinkN.
  + apply/closureP; exists x => //. by rewrite connect1 // clinkN.
  + apply: closure_connect IHp. by rewrite connect1 // clinkN.
- have F (u:G) : connect clink (finv face u) u. 
  { apply: connect_trans (connect1 clinkF) _. by rewrite (f_finv faceI). }
  case: (altP (z' =P finv face y)) => [-> _|N1]; first by apply/closureP; exists y.
  case: (altP (z' =P finv face x)) => [-> _|N2 E]; first by apply/closureP; exists x.
  rewrite /= (negbTE N1) (negbTE N2) in E; rewrite -[z'](finv_f faceI) E. 
  apply: closure_connect IHp. apply: connect_trans (connect1 clinkF) _. 
  by rewrite (f_finv faceI).
Qed.

Unset Printing Implicit.

Lemma n_comp_merge_rest (G : hypermap) (x y : G) (xDy : x != y) : 
  n_comp glink [predC closure glink (pred2 x y)] = 
  n_comp (glink : rel (merge x y)) [predC closure (@glink (merge x y)) (pred2 x y)].
Proof.
set a := closure glink (pred2 x y).
set b := closure (@glink (merge x y)) (pred2 x y).
have eq_b_a : b =i a by apply closure_merged.
have C_ab : [predC b] =i [predC a] by move=>z;rewrite [in RHS]inE/= -eq_b_a.
have [? ?] : x \in pred2 x y /\ y \in pred2 x y by rewrite !inE !eqxx.
rewrite (eq_n_comp_r C_ab); apply: (@in_eq_n_comp).
- move => u v /=. exact: glinkC. 
- move => u v /=. exact: (@glinkC (merge x y)). 
- apply/predC_closed/closure_closed. exact: glinkC.
- apply/predC_closed; rewrite -(eq_closed_r eq_b_a).
  apply: closure_closed. exact: (@glinkC (merge x y)). 
- move => u v Hu _. rewrite !inE/= in Hu; rewrite /glink /= !ifF //.
  + apply: contraNF Hu => /eqP->. apply/closureP; exists x => //. 
    apply gcompF. by rewrite cface1 f_finv.
  + apply: contraNF Hu => /eqP->. apply/closureP; exists y => //. 
    apply gcompF. by rewrite cface1 f_finv.
  + apply: contraNF Hu => /eqP->. exact: mem_closure.
  + apply: contraNF Hu => /eqP->. exact: mem_closure. 
Qed.

Lemma n_comp_mergeX (G : hypermap) (x y : G) (xDy : x != y) : 
  cnode x y (+) cface x y -> n_comp glink (merge x y) = n_comp glink G.
Proof.
move => c_xy.
pose a := closure glink (pred2 x y).
pose b := closure (@glink (merge x y)) (pred2 x y).
have eq_b_a : b =i a by apply closure_merged.
rewrite (n_compC b) (n_compC a) !n_comp_closure2; try exact:glinkC.
rewrite (n_comp_merge_rest xDy). 
suff -> : (gcomp : rel G) x y = (gcomp : rel (merge x y)) x y by [].
apply/idP/idP => _; case: (boolP (cnode x y)) c_xy => /= N F.
- apply: (@gcompF (merge x y)) => /=. 
  eapply connect_trans with (finv face x).
  + apply: fconnect_f_switch => //; first by rewrite cface1 f_finv // cfaceC.
    by rewrite cface1r f_finv.
  + apply: connect1 => /=. rewrite eqxx. 
    by case: (finv face x =P _) => [->|]; rewrite f_finv.
- apply: (@gcompN (merge x y)) => /=. 
  eapply connect_trans with (node y). 
  + apply: connect1 => /=; by rewrite eqxx.
    apply: fconnect_f_switch => //; by rewrite -?cnode1r -?cnode1. 
  + exact: gcompN.
  + exact: gcompF.
Qed.

Lemma n_comp_mergeG (G : hypermap) (x y : G) : 
  ~~ gcomp x y -> (n_comp glink (merge x y)).+1 = (n_comp glink G).
Proof.
move=> gcNxy. 
have xDy : x != y by apply: contraNneq gcNxy => ->. 
pose a := closure glink (pred2 x y).
pose b := closure (@glink (merge x y)) (pred2 x y).
have eq_b_a : b =i a by apply closure_merged.
rewrite (n_compC b) (n_compC a) !n_comp_closure2; try exact:glinkC.
rewrite gcNxy /= add2n addSn -(n_comp_merge_rest xDy) -/a.
rewrite [connect _ _ _](_ : _ = true) //.
apply: (@gcompN (merge x y)). 
rewrite fconnect_switched => //; last exact: (@nodeI G).
apply: contraNN gcNxy. exact: gcompN.
Qed.

Lemma genus_mergeX (G : hypermap) (x y : G) :
  cnode x y (+) cface x y -> genus (merge x y) = genus G.
Proof.
move => cn_cf_xy.
have xDy : x != y by apply: contraTneq cn_cf_xy => ->; rewrite !connect0.
have fI := finv_inj faceI; have nI := finv_inj nodeI.
rewrite /genus /Euler_lhs /= (n_comp_mergeX xDy cn_cf_xy) -/(Euler_lhs G).
rewrite {1}/Euler_rhs /= !fcard_switch ?inj_eq // 1?eq_sym //; last exact: fI.
move: cn_cf_xy. rewrite -{2}[x](f_finv faceI) -{2}[y](f_finv faceI) -cface1 -cface1r cfaceC.
case: (boolP (cnode x y)) => /= => [_ /negbTE->|_ ->]. 
- rewrite addSnnS prednK //; apply/fcard0P => //; [exact: faceI|by exists x].
- rewrite -addSnnS prednK //; apply/fcard0P => //; [exact: nodeI|by exists x].
Qed.

Lemma genus_mergeG (G : hypermap) (x y : G) :
  ~~ gcomp x y -> genus (merge x y) = genus G.
Proof.
move=> gcNxy. 
have [? ?] := (@nodeI G, @faceI G).
have fI := finv_inj (@faceI G).
have xDy : x != y by apply: contraNneq gcNxy => ->. 
have cxyF : cnode x y = false. apply: contraNF gcNxy. exact: gcompN.
have fxyF : cface x y = false. apply: contraNF gcNxy. exact: gcompF.
rewrite /genus /Euler_lhs /= -(n_comp_mergeG gcNxy).
rewrite doubleS -add2n -addnA -/(Euler_lhs (merge x y)).
suff -> : Euler_rhs G = (Euler_rhs (merge x y)).+2.
  by rewrite -[(Euler_rhs (merge x y)).+2]addn2 addnC subnDr.
rewrite /Euler_rhs !fcard_switch // ?(inj_eq fI) 1?eq_sym //.
rewrite cxyF. rewrite (@cface1 G) (@cface1r G) !f_finv // cfaceC fxyF /=.
rewrite -2!addnS; congr (_ + _); rewrite -addnS -addSn !prednK //.
all: by apply/fcard0P => //; exists x.
Qed.

Lemma genus_merge (G : hypermap) (x y : G) :
  ~~ gcomp x y || (cnode x y (+) cface x y) -> genus (merge x y) = genus G.
Proof. case/orP; [exact: genus_mergeG|exact: genus_mergeX]. Qed.

Lemma merge_planar (G : hypermap) (x y : G) :
  ~~ gcomp x y || (cnode x y (+) cface x y) -> planar G -> planar (merge x y).
Proof. by rewrite /planar => /genus_merge->. Qed.

Arguments merge : clear implicits.


Section MergeAdjn.

Local Notation "'@cnode[' G ]" := (fconnect (@node G)) (at level 1, format "'@cnode[' G ]").
Local Notation "'@cface[' G ]" := (fconnect (@face G)) (at level 1, format "'@cface[' G ]").
Local Notation "'@adjn[' G ]" := (@adjn G) (at level 1, format "'@adjn[' G ]").

Lemma cnode_merge (G : hypermap) (x y u v : G) : 
  ~~ cnode x y -> 
  @cnode[merge G x y] u v = 
  [|| @cnode[G] u v , @cnode[G] u x && @cnode[G] v y | @cnode[G] u y && @cnode[G] v x ].
Proof. by apply: fconnect_switchE. Qed.

Lemma merge_loopless (D : hypermap) (x y : D) :
  plain D -> ~~ @cnode[D] x y -> ~~ @adjn[D] x y -> 
  loopless D -> loopless (merge D x y).
Proof.
move => plainD nNxy nAxy ; apply: contraNN => /existsP [z]. 
rewrite cnode_merge // => /or3P[?|/andP[Z1 Z2]|/andP[Z1 Z2]]; first by apply/existsP; exists z.
  apply: contraNT nAxy => _. by apply: (adjnI D z); rewrite cnodeC.
 apply: contraNT nAxy => _. by apply: (adjnI D (edge z)); rewrite cnodeC ?plain_eq.
Qed.

Lemma mergeC_hiso (G : hypermap) (x y : G) : hiso (merge G x y) (merge G y x).
Proof. hiso bij_id => // z; exact: (@switchC G x y (@node G) z). Defined.

Lemma adjn_mergeC (G : hypermap) (x y : G) : @adjn[merge G x y] =2 @adjn[merge G y x].
Proof. by move=> u v; rewrite -(hiso_adjn (mergeC_hiso x y)). Qed.

Variables (D : hypermap) (dx dy : D).
Variables (plainD : plain D) (llD : loopless D) (dxDxy : dx != dy).
Let D' := merge D dx dy.

(** [d1] is on one of the merged node cycles *)
Lemma adjn_merge1 (d1 d2 : D) : ~~ @cnode[D] dx dy -> ~~ @adjn[D] dx dy -> 
  @cnode[D] d1 dy -> @adjn[D'] d1 d2 = @adjn[D] d2 dx || @adjn[D] d2 dy.
Proof.
move=> n_dxy nAdydx d1y.
have llD' : loopless D' by apply: merge_loopless.
have dxdy : @cnode[D'] dx dy by rewrite fconnect_switched => //; exact: (@nodeI D). 
have subDD' : subrel @cnode[D] @cnode[D'] by apply: switch_subrel.
apply/idP/idP.
- case/exists_inP => z; rewrite !inE; set z' := edge z => C1.
  have {d1 d1y C1} Cz : @cnode[D'] dy z. 
  { apply: connect_trans C1. rewrite cnodeC. exact: switch_subrel d1y. }
  move: (Cz); rewrite cnode_merge // [_ dy dx]cnodeC (negbTE n_dxy) connect0 /=.    
  rewrite cnode_merge // [@cnode[D] z' dx]rwF 1?[@cnode[D] z' dy]rwF ?andbF ?orbF.
  + case/orP => H1 H2; apply/orP; [right|left]; apply/exists_inP; exists (edge z) => //.
    by rewrite plain_eq. by rewrite plain_eq // inE cnodeC.
  + apply: contraNN llD' => X; apply/existsP; exists z; rewrite cnodeC.
    apply: connect_trans Cz. exact: subDD'.
  + apply: contraNN llD' => X; apply/existsP; exists z; rewrite cnodeC.
    apply: connect_trans Cz. apply: connect_trans. exact: subDD' X. done.
- case/orP; case/exists_inP => z; rewrite !inE => d2_z d_ez.
  + apply/exists_inP; exists (edge z); rewrite inE.
    * apply: connect_trans (subDD' _ _ d_ez). 
      apply: connect_trans (subDD' _ _ d1y) _. by rewrite cnodeC.
    * rewrite plain_eq //. exact: subDD'.
  + apply/exists_inP; exists (edge z); rewrite inE.
    * apply: connect_trans (subDD' _ _ d_ez). exact: subDD'.
    * rewrite plain_eq //. exact: subDD'. 
Qed.

(** Neither [d1] nor [d2] is on one of the merged node cycles *)
Lemma adjn_merge2 (d1 d2 : D) : ~~ @cnode[D] dx dy -> ~~ @adjn[D] dx dy ->
 ~~ @cnode[D] d1 dx -> ~~ @cnode[D] d1 dy -> ~~ @cnode[D] d2 dx -> ~~ @cnode[D] d2 dy -> 
 @adjn[D'] d1 d2 = @adjn[D] d1 d2.
Proof.
move=> n_dxy nAdydx d1x d1y d2x d2y.
have llD' : loopless D' by apply: merge_loopless.
have dxdy : @cnode[D'] dx dy by rewrite fconnect_switched => //; exact: (@nodeI D). 
have subDD' : subrel @cnode[D] @cnode[D'] by apply: switch_subrel.
apply/exists_inP/exists_inP => -[z]; rewrite !inE.
- rewrite fconnect_switchE //; last exact: (@nodeI D).
  rewrite (negbTE d1x) (negbTE d1y) // fconnect_switchE //; last exact: (@nodeI D).
  rewrite (negbTE d2x) (negbTE d2y) /= !orbF. by exists z.
- move => d1z d2ez. exists z; apply: switch_subrel => //; exact: (@nodeI D).
Qed.


End MergeAdjn.

(** *** Disjoint Union *)

Arguments inl_inj {A B}.
Arguments inr_inj {A B}.

Section SumF.
Variables (T1 T2 : finType) (f1 : T1 -> T1) (f2 : T2 -> T2).
Notation sumf := (sumf f1 f2).
Variables (inj_f1 : injective f1) (inj_f2 : injective f2).

Lemma sumf_inj : injective sumf.
Proof. move => [u|u] [v|v] //= []; by [ move/inj_f1->| move/inj_f2 ->]. Qed.

Lemma sumf_connect_sym : connect_sym (frel sumf).
Proof. exact: fconnect_sym sumf_inj. Qed.

Lemma closed_sumf_l : fclosed sumf is_inl.
Proof. by move => [u|u] [v|v]. Qed.

Let csym1 := fconnect_sym inj_f1.
Let csym2 := fconnect_sym inj_f2.

Lemma adjunction_sumf_inl : fun_adjunction inl sumf f1 is_inl.
Proof. 
apply: strict_adjunction closed_sumf_l _ _ _  => //; first exact: inl_inj.
by apply/subsetP => -[u _|//]; rewrite codom_f.
Qed.

Lemma adjunction_sumf_inr : fun_adjunction inr sumf f2 [predC is_inl].
apply: strict_adjunction _ _ _  => //; try exact: inr_inj.
  by apply/predC_closed/closed_sumf_l.
by apply/subsetP => -[//|u _]; rewrite codom_f.
Qed.

Lemma fcard_sumf  :
  fcard sumf {:T1 + T2}  = fcard f1 T1 + fcard f2 T2.
Proof.
pose a (x : T1 + T2) := x : bool.
have ? := sumf_connect_sym; have ? := fconnect_sym inj_f1; have ? := fconnect_sym inj_f2.
have ? : fclosed sumf a by move => [u|u] [v|v].
have ? : fclosed sumf (predC a) by apply: predC_closed.
rewrite (n_compC a) (adjunction_n_comp _ _ _ _ adjunction_sumf_inl) //.
by rewrite (adjunction_n_comp _ _ _ _ adjunction_sumf_inr).
Qed.

Lemma fconnect_sumf_l x y : 
  fconnect sumf (inl x) (inl y) = fconnect f1 x y.
Proof. by symmetry; apply: rel_functor adjunction_sumf_inl _ _ _. Qed.

Lemma fconnect_sumf_r x y : 
  fconnect sumf (inr x) (inr y) = fconnect f2 x y.
Proof. by symmetry; apply: rel_functor adjunction_sumf_inr _ _ _. Qed.

Lemma fconnect_sumf_lr x y : fconnect sumf (inl x) (inr y) = false.
Proof.
apply/negbTE/negP => /connectP[p].
elim: p x => //= -[x|//] p IHp z /andP[_]; exact: IHp.
Qed.

Lemma fconnect_sumf_rl x y : fconnect sumf (inr x) (inl y) = false.
Proof.
apply/negbTE/negP => /connectP[p].
elim: p x => //= -[//|x] p IHp z /andP[_]; exact: IHp.
Qed.

Definition fconnect_sumf := 
  (fconnect_sumf_l, fconnect_sumf_r, fconnect_sumf_lr, fconnect_sumf_rl).

End SumF.

Lemma sumf_cancel3 T1 T2 (e1 n1 f1 : T1 -> T1) (e2 n2 f2 : T2 -> T2) :
  cancel3 e1 n1 f1 -> cancel3 e2 n2 f2 -> cancel3 (sumf e1 e2) (sumf n1 n2) (sumf f1 f2).
Proof. by move => can1 can2 [x|x] /=; rewrite ?can1 ?can2. Qed.

Definition hmap_union (G1 G2 : hypermap) := 
  Hypermap (sumf_cancel3 (@edgeK G1) (@edgeK G2)).

Declare Scope hmap_scope.
Notation "G ∔ H" := (hmap_union G H) (at level 20, left associativity) : hmap_scope.
Bind Scope hmap_scope with hypermap.
Delimit Scope hmap_scope with H.

Lemma union_genus (G1 G2 : hypermap) :
  genus (G1 ∔ G2) = genus G1 + genus G2.
Proof.
rewrite {1}/genus.
suff -> : Euler_lhs (G1 ∔ G2) = Euler_lhs G1 + Euler_lhs G2.
{ have -> : Euler_rhs (G1 ∔ G2) = Euler_rhs G1 + Euler_rhs G2.
    by rewrite /Euler_rhs !fcard_sumf //; ring.
  rewrite subnDA -addnBAC -1?addnBA ?Euler_le //.
  by rewrite halfD -!/(genus _) !even_genusP -2?addnBA // ?subnn !addn0 !odd_double. }
rewrite /Euler_lhs card_sum (n_compC (fun x : (G1 ∔ G2)%H => x)).
have ? := glinkC.
have cl_inl : closed (@glink (G1 ∔ G2)) is_inl by apply: intro_closed => // -[x|x] [y|y].
have cl_inr := predC_closed cl_inl.
have inl_adj : @rel_adjunction (G1 ∔ G2)%H G1 (@inl _ _) glink glink is_inl. 
{ apply: strict_adjunction => //; first exact: inl_inj.
  apply/subsetP=> -[z _|//]; exact: codom_f. }
have inr_adj : @rel_adjunction (G1 ∔ G2)%H G2 (@inr _ _) glink glink [predC is_inl].
{ apply: strict_adjunction => //; first exact: inr_inj.
  apply/subsetP=> -[//|z _]; exact: codom_f. }
rewrite (adjunction_n_comp _ _ _ _ inl_adj) ?(adjunction_n_comp _ _ _ _ inr_adj) //.
by rewrite doubleD -!addnA; congr (_ + _); rewrite [RHS]addnC [#|_| + #|_|]addnC -!addnA. 
Qed.

Lemma union_planar (G1 G2 : hypermap) : planar (G1 ∔ G2) <-> planar G1 /\ planar G2.
Proof. rewrite /planar union_genus addn_eq0. by do 2 case (_ == 0) => //=; firstorder. Qed.

Lemma union_plain (G H: hypermap) : plain G -> plain H -> plain (G ∔ H)%H.
Proof.
move => plainG plainH; apply/plainP => -[x|x] _ /=.
  by rewrite (inj_eq inl_inj) plain_eq ?plain_neq.
by rewrite (inj_eq inr_inj) plain_eq ?plain_neq.
Qed.

Lemma union_adjn_l (G H : hypermap) (x y : G) :
  @adjn (G ∔ H)%H (inl x) (inl y) = adjn x y.
Proof.
apply/exists_inP/exists_inP.
- by move=> [[z|z]]; rewrite !inE /= ?fconnect_sumf //; exists z.
- by move=> [z]; rewrite inE => Z1 Z2; exists (inl z); rewrite !inE /= ?fconnect_sumf.
Qed.

Lemma union_adjn_r (G H : hypermap) (x y : H) :
  @adjn (G ∔ H)%H (inr x) (inr y) = adjn x y.
Proof.
apply/exists_inP/exists_inP.
- by move=> [[z|z]]; rewrite !inE /= ?fconnect_sumf //; exists z.
- by move=> [z]; rewrite inE => Z1 Z2; exists (inr z); rewrite !inE /= ?fconnect_sumf.
Qed.

Lemma union_adjn_lr (G H : hypermap) (x : G) (y : H) :
  @adjn (G ∔ H)%H (inl x) (inr y) = false.
Proof.
by apply: (introF exists_inP); move => -[[z|z]]; rewrite !inE /= ?fconnect_sumf.
Qed.

Lemma union_adjn_rl (G H : hypermap) (x : H) (y : G) :
  @adjn (G ∔ H)%H (inr x) (inl y) = false.
Proof.
by apply: (introF exists_inP); move => -[[z|z]]; rewrite !inE /= ?fconnect_sumf.
Qed.

Definition union_adjn := (union_adjn_l,union_adjn_lr,union_adjn_r, union_adjn_rl).

(** *** Deleting a node (and incident edges) *)

(** [frestrict] restricts a function [T -> T] to a function [sig P ->
sig P], provided [P] is closed under [f]. *)
Section FRes.
Variables (T : Type) (P : pred T) (f : T -> T) (hom_f : {homo f : x / x \in P}).

Definition frestrict (x : sig P) : sig P := let: exist vx Px := x in Sub (f vx) (hom_f Px).

Lemma val_frestrict x : val (frestrict x) = f (val x). by case: x. Qed.

Lemma frestrict_inj : {in P&, injective f} -> injective frestrict.
Proof.
move => inj_f x y. move/(f_equal val); rewrite !val_frestrict.
move/inj_f/val_inj => -> //; exact: valP.
Qed.

End FRes.
Lemma fconnect_frestrict (T : finType) (P : pred T) (f : T -> T)  (x y : sig P) 
  (hom_f : {homo f : x / x \in P}) :
  fconnect (frestrict hom_f) x y = fconnect f (val x) (val y).
Proof.
apply/idP/idP => /iter_findex; move: (findex _ _ _) => n.
  move<-. elim: n x => [//|n IHn x]. rewrite iterSr. 
  by apply: connect_trans (connect1 _) (IHn _); rewrite /= val_frestrict.
move: x y => [x Px] [y Py] /=; rewrite -[exist _ _ _]/(Sub x Px) -[exist _ _ _]/(Sub y Py).
elim: n x Px y Py => [|n IHn] x Px y Py. 
  by move => ?; subst y; rewrite (eq_irrelevance Px Py).
rewrite iterSr => it_n. 
apply: connect_trans (IHn _ _ _ _ it_n) => [|Pfx] ; first exact: hom_f Px.
by apply: connect1; rewrite /= -val_eqE.
Qed.

Section Skip.
Variables (T : finType) (a : pred T) (f : T -> T).

(** The function [skip p f] behaves like [f], but skips over elements
that are NOT in [p] (if possible). In the general case, one needs to
assume that [f x] can reach some element in [p] by iteration. If [f]
is injective, one can assume [x \in p] instead. *)

Lemma skip_proof x : 
  [exists n : 'I_(order f (f x)), iter n.+1 f x \in a] -> exists n : nat, iter n.+1 f x \in a.
Proof. by case/existsP => n; exists n. Qed.

Definition skip (x : T) : T := 
  match @idP [exists n : 'I_(order f (f x)), iter n.+1 f x \in a] with
  | ReflectT E => iter (ex_minn (skip_proof E)).+1 f x
  | ReflectF _ => x
  end.

Lemma skip_exists' x y : 
  y \in a -> fconnect f (f x) y -> [exists n : 'I_(order f (f x)), iter n.+1 f x \in a].
Proof.
move => y_a c_xy; have:= iter_findex c_xy; rewrite -iterSr => E.
set n := findex _ _ _ in E.
have Hn : n < order f (f x) by apply: findex_max.
apply/existsP; exists (Ordinal Hn); by rewrite E.
Qed.

Variant skip_spec' x : T -> Type :=
  SkipSpec' (n:nat) of n < order f (f x) & iter n.+1 f x \in a 
         & (forall m, iter m.+1 f x \in a -> n <= m) : skip_spec' x (iter n.+1 f x).


Lemma skipP' x y : y \in a -> fconnect f (f x) y -> skip_spec' x (skip x).
Proof.
move => y_a c_xy; rewrite /skip.
case: {-}_ / idP => [p|]; last by rewrite (skip_exists' y_a c_xy).
case: ex_minnP => n N1 N2; constructor; auto. 
case/existsP : p => -[m Hm] /N2/= ?. exact: leq_trans Hm.
Qed.

Lemma skip1 x : f x \in a -> skip x = f x.
Proof. 
move => fx_a. case: (skipP' fx_a) => // n _ N1 N2.
move: (N2 0 fx_a). by rewrite leqn0 => /eqP->.
Qed.

Lemma skip_first x y : 
  y \in a -> fconnect f (f x) y -> f x \notin a -> skip x = skip (f x).
Proof.
move => y_a f_xy fxNa.
have f_xy' : fconnect f (f (f x)) y. 
{ move/iter_findex : f_xy. case: (findex _ _ _) => [/= dy|n]. 
    by rewrite dy y_a in fxNa.
  rewrite iterSr => <-. exact: fconnect_iter. }
case: (skipP' y_a f_xy) => n N0 N1 N2.
case: (skipP' y_a f_xy') => m M0 M1 M2. 
suff /eqP-> : n == m.+1 by rewrite iterSr.
rewrite eqn_leq N2 1?iterSr //=.
destruct n as [|n]; first by rewrite /= (negbTE fxNa) in N1.
by rewrite ltnS M2 // -iterSr.
Qed.

Hypothesis inj_f : injective f.

Lemma skip_exists x : x \in a -> [exists n : 'I_(order f (f x)), iter n.+1 f x \in a].
Proof.
move => x_a. apply: skip_exists' x_a _. by rewrite fconnect_sym // fconnect1.
Qed.

Lemma skipE x (x_a : x \in a) : 
  skip x = iter (ex_minn (skip_proof (skip_exists x_a))).+1 f x.
Proof.
rewrite /skip. case: {-}_ / idP => [p|]; last by rewrite (skip_exists x_a).
by rewrite (bool_irrelevance (skip_exists x_a) p). 
Qed.

Variant skip_spec x : T -> Type :=
  SkipSpec (n:nat) of n < order f (f x) & iter n.+1 f x \in a 
         & (forall m, iter m.+1 f x \in a -> n <= m) : skip_spec x (iter n.+1 f x).

Lemma skipP x (x_a : x \in a) : skip_spec x (skip x).
Proof. 
rewrite skipE. set p := skip_exists _. 
case: ex_minnP => n N1 N2; constructor; auto. 
case/existsP : p => k Hk. apply: leq_trans (ltn_ord k). exact: N2.
Qed.

Lemma skip_eq x y n :
  x \in a -> y \in a -> (forall m : nat, iter m.+1 f x \in a -> n <= m) -> iter n.+1 f x = y -> 
  skip x = y.
Proof.
move => x_a y_a min_n def_y; case: skipP => // m _ M1 M2. 
suff /eqP -> : m == n by []. by rewrite eqn_leq min_n // M2 // def_y.
Qed.


Lemma iter_inj n : injective (iter n f).
Proof. move => x y. by elim: n => // n IH /= /inj_f. Qed.

Lemma skip_hom : {homo skip : x / x \in a}.
Proof. move => x in_a. by case: skipP. Qed.

Lemma skip_inj : {in a&, injective skip}.
Proof.
move => x y x_a y_a. 
case: (skipP x_a) => n _ N1 N2. case: (skipP y_a) => m _ M1 M2 eqI.
suff/eqP ? : n == m by subst; apply: iter_inj eqI.
case: (ltngtP n m) => // n_lt_m. (* TODO: proper symmetry reasoning *)
- have eq_x : x = iter (m - n.+1).+1 f y. 
  { rewrite subnSK //. rewrite -(subnK (ltnW n_lt_m)) -addnS addnC iterD in eqI.
    exact: iter_inj eqI. }
  rewrite eq_x in x_a. move: (M2 _ x_a). destruct m => //. by rewrite subSS ltn_subrR.
- have eq_y : y = iter (n - m.+1).+1 f x. 
  { rewrite subnSK //. rewrite -(subnK (ltnW n_lt_m)) -addnS addnC iterD in eqI.
    symmetry. exact: iter_inj eqI. }
  rewrite eq_y in y_a. move: (N2 _ y_a). destruct n => //. by rewrite subSS ltn_subrR.
Qed.

Lemma fconnect_skip: {in a&, fconnect skip =2 fconnect f}.
Proof.
move => x y x_a y_a; apply/idP/idP. 
- move/iter_findex<-; move: (findex _ _ _) => n; elim: n x x_a => //= n IHn x x_a.
  apply: connect_trans (IHn _ x_a) _.
  case: skipP => [|m *]; last exact: fconnect_iter.
  by apply/iter_in => //; apply: skip_hom.
- move/iter_findex => E; rewrite -{}E in y_a *.
  move: (findex _ _ _) y_a => n. 
  have [m Hm] := ubnP n; elim: m n Hm x x_a {y} => // m IHm [//|n] /ltnSE n_leq_m x x_a iter_n_f.
  case: (boolP [exists k : 'I_n, (iter k.+1 f x \in a)]).
  + case/existsP => [[k Hk] iter_k_f]. 
    apply: connect_trans (IHm _ _ _ _ iter_k_f) _ => //. by apply: leq_trans n_leq_m.
    apply: connect_trans (IHm (n.+1 - k.+1) _ _ _ _) _ => //. 
    * apply: leq_trans n_leq_m. by rewrite subSS ltnS leq_subr.
    * by rewrite -iterD subnK // ltnW.
    * by rewrite -iterD subnK // ltnW.
  + move/existsPn => Hn. rewrite (_ : iter n.+1 f x = skip x) ?fconnect1 //.
    case: skipP => // k _ K1 K2. rewrite (_ : n = k) //; apply/eqP. 
    rewrite eqn_leq K2 // andbT leqNgt. 
    apply: contraTN K1 => Hk; exact: (Hn (Ordinal Hk)).
Qed.

End Skip.
Arguments skip_first [T a f x] y.

(** useful? *)
Lemma finv_skip (T : finType) (a : pred T) (f : T -> T) : 
  injective f -> {in a, finv (skip a f) =1 skip a (finv f)}.
Abort.

Section DelNode.
Variables (G : hypermap) (z : G).

Let N := fclosure edge (cnode z).

Definition del_dart := { x : G | x \notin N }.

Lemma del_edge_hom : {homo edge : x / x \notin N}.
Proof. 
move => x. by rewrite /N -(closure_closed cedgeC _ (eqxx _)).
Qed.

Definition del_node_hom : {homo skip [predC N] node : x / x \notin N}.
Proof. exact: skip_hom. Qed.

(** TOTHINK: This defintion makes no assumptions on the hypermap
(e.g., loopless, plain, etc.). However, the face permutation is
completely useless. This makes it hard to prove anything interesting
(e.g., preservation of planarity) for the general case. *)

Definition del_node_face_ := finv (frestrict del_node_hom) \o finv (frestrict del_edge_hom).

Lemma del_node_can3: 
  cancel3 (frestrict del_edge_hom) (frestrict del_node_hom) del_node_face_.
Proof. 
move => x; rewrite /del_node_face_ /= finv_f ?f_finv //.
- by apply/frestrict_inj/skip_inj.
- apply/frestrict_inj. exact: in2W edgeI.
Qed.

Definition del_node := Hypermap del_node_can3.

Hypothesis plainG : plain G.

Let NP x : reflect (cnode z x || cnode z (edge x)) (x \in N).
Proof using plainG.
apply: (iffP (closureP _ _ _)) => [[y /=]|]; last first.
  by case/orP; [exists x|exists (edge x); rewrite // -cedge1r].
by rewrite plain_orbit // !inE => zy /pred2P [?|?]; subst y; rewrite zy.
Qed.

Let edgeN x : edge x \in N = (x \in N). 
Proof using. symmetry. apply: closure_closed => //=. exact: cedgeC. Qed.

Lemma del_node_cnode (u v : del_node) : cnode u v = cnode (val u) (val v).
Proof. by rewrite fconnect_frestrict fconnect_skip //; apply: valP. Qed.

Lemma del_node_adjn (u v : del_node) : adjn u v = adjn (val u) (val v).
Proof using plainG.
apply/exists_inP/exists_inP => -[d]; rewrite !inE.
  by rewrite !del_node_cnode val_frestrict; exists (val d).
have [dN|dNN] := boolP (d \in N); last first.
  by exists (Sub d dNN); rewrite inE del_node_cnode ?val_frestrict.
move => n_u_d n_v_d; case:notF.
have/NP/orP[n_z_d|n_z_ed] := dN.
- apply: contraNT (valP u) => _. apply: mem_closure.
  by rewrite inE (connect_trans n_z_d _) // cnodeC.
- apply: contraNT (valP v) => _. apply: mem_closure.
  by rewrite inE (connect_trans n_z_ed _) // cnodeC.
Qed.

Definition del_node_face x := 
  if face x \in N then finv node (face x) else face x.

Hypothesis llG : loopless G.

Definition simple_hmap := forall x y : G, x != y -> cnode x y -> ~~ cnode (edge x) (edge y).
Hypothesis simple : simple_hmap.

Let simple' :  forall x y : G , x != y -> cnode x y -> ~~ cnode (face x) (face y).
Proof. by move=> x y xDy n_xy; rewrite cnode1 cnode1r !plain_eq' // simple. Qed.

Hypothesis deg2 : forall x : G, node x == x = false.

(* the following forbids two things:
   - parallel edges having one end at the removed node (would result in n-neighbors in N)
   - degreee 1 neighbors of the removed node (would consist of a single element in N) *)
Lemma del_node_neighbor1 x : ~~cnode z x -> x \in N -> node x \notin N.
Proof. 
move=> /negPf n_zxF /NP; rewrite n_zxF /= => n_z_ex. 
apply: contraTN isT => /NP; rewrite -cnode1r n_zxF /= => n_z_enx.
have /negbT := deg2 x; rewrite -(inj_eq edgeI) => /simple.
by rewrite !plain_eq // (connect_trans _ n_z_ex) cnodeC // -cnode1r connect0 => /(_ isT).
Qed.

Let del_node_neighbor1' x : ~~cnode z x -> x \in N -> finv node x \notin N.
Proof.
move => Hz; apply: contraTN => /del_node_neighbor1. 
by rewrite cnode1r !f_finv //; apply. 
Qed.

Arguments skipP [T a f] _ [x] _, [T] a [f] _ [x] _.

Let skip2 x : x \notin N -> node x \in N -> skip [predC N] node x = node (node x).
Proof. 
move => xN nxN. 
have xnZ : ~~ cnode z (node x). rewrite -cnode1r. apply: contraNN xN. exact: mem_closure.
have nnxN := del_node_neighbor1 xnZ nxN. 
case: (skipP [predC N] nodeI xN) => n _ N1 N2. 
suff/eqP -> : n == 1 by [].
rewrite eqn_leq N2 //= lt0n. by apply: contraNneq N1 => ->.
Qed.

Lemma del_face_hom : {homo del_node_face : x / x \notin N}.
Proof. 
move => x xN;rewrite /del_node_face; case: (boolP (face x \in N)) => //.
apply: del_node_neighbor1'. apply: contraNN xN. rewrite cnode1r plain_eq' // -edgeN. exact: mem_closure.
Qed.

Lemma del_node_faceE : @face del_node =1 (frestrict del_face_hom).
Proof.
suff: cancel3 (frestrict del_edge_hom) (frestrict del_node_hom) (frestrict del_face_hom).
{ move/canF_sym. apply: inj_can_eq (@faceK del_node) _. by move => x y /edgeI/nodeI. }
move => x. apply/val_inj; rewrite !val_frestrict /del_node_face. 
case: (boolP (face (edge (val x)) \in N)) => H.
- have Hz : ~~ cnode z (face (edge (val x))). 
  { apply: contraNN (valP x). rewrite cnode1r edgeK. exact: mem_closure. }
  have H' := del_node_neighbor1' Hz H. by rewrite skip2 // f_finv // edgeK.
- rewrite skip1 // edgeK //. exact: valP.
Qed.

Lemma del_node_plain : plain del_node.
Proof.
have pG := plainP plainG; apply/plainP => x _; split. 
- apply/val_inj => /=. rewrite !val_frestrict. by apply pG.
- rewrite -(inj_eq val_inj) !val_frestrict. by apply pG.
Qed.

Lemma del_node_loopless : loopless del_node.
Proof using llG.
move/existsPn : (llG) => llG'; apply/existsPn => x.
apply: contraNN (llG' (val x)) => loop_x.
suff S (u v : del_node) : cnode u v -> cnode (val u) (val v).
{ by rewrite -[X in cnode _ X](val_frestrict del_edge_hom) S. }
rewrite /= -(@fconnect_skip _ [predC N] _ nodeI); try exact: valP.
by apply: homo_connect => {u v} u v /= /eqP<-; rewrite val_frestrict. 
Qed.

Lemma wheel_proof x : cnode z x -> face x \notin N.
Proof using deg2 llG plainG simple.
have F := loopless_face _ plainG llG; rewrite cnodeC.
move => n_xz; apply: contraTN isT => /NP.
have/negPf -> /= : ~~ cnode z (face x). 
  by apply: contraNN (F x); apply: connect_trans.
set y := edge _ => n_zy.
have E : edge y = face x by rewrite plain_eq.
have [xy|xDy] := eqVneq x y.
  by rewrite -(deg2 (face x)) plain_eq' // {1}xy E.
have /simple -/(_ xDy): cnode x y by apply: connect_trans n_zy.
by rewrite plain_eq // cnode1r plain_eq' // connect0.
Qed.

Let z' : del_node := Sub (face z) (@wheel_proof z (connect0 _ _)).
Let inD (x : G) : del_node := insubd z' x.

(** This follows if [G] is 2-connected and planar, see [hcycle.v] *)
Hypothesis cycleG : forall x y : G, x != y -> cface x y -> ~~ cnode x y.

Let blG : bridgeless G.
Proof.
apply/negP => /existsP [x]; rewrite cface1r -[face _](finv_f nodeI) edgeK.
by move/cycleG; rewrite -(inj_eq nodeI) f_finv // deg2 fconnect_finv => /(_ isT).
Qed.

Lemma cycleG' : forall x y : G , x != y -> cnode x y -> ~~ cface (edge x) (edge y).
Proof. 
move => x y xDy; apply: contraTN; rewrite cface1 cface1r => /cycleG.
rewrite (inj_eq faceI) (inj_eq edgeI) => /(_ xDy).
by rewrite cnode1 cnode1r !edgeK.
Qed.

(* TOTHINK: is deg2 really necessary? *)
Lemma arity3 (x : G) : 2 < arity x.
Proof using llG plainG deg2 simple.
rewrite 1!ltn_neqAle ltnNge [2 != _]rwT /=.
- have:= loopless_face x plainG llG.
  apply: contraNN => /card_le1_eqP /(_ x) A.
  by rewrite [face x]A // inE -?cface1r.
- move/negbT/simple : (deg2 (face x)); rewrite -cnode1 connect0 => /(_ isT).
  apply: contraNneq => ar2; rewrite faceK -plain_eq' // -cnode1r.
  by rewrite -[face _]/(iter 2 face x) ar2 iter_face_arity.
Qed.

Lemma iter0 (T : Type) (f : T -> T) x : iter 0 f x = x. Proof. by []. Qed.

Lemma homo_fpath_in {T T' : eqType} (h : T -> T') (f : T -> T) (f' : T' -> T') x s :  
  {in belast x s, forall x : T, h (f x) = f' (h x)}  ->
  fpath f x s -> fpath f' (h x) [seq h i | i <- s].
Proof. 
elim: s x => //= u s IH x /all_cons [Hx {}/IH IH] /andP [/eqP fx path_s].
by rewrite -Hx fx IH ?eqxx.
Qed.



Lemma fpath_sub_belast (T : eqType) (f : T -> T) x (s : seq T) (p : {pred T}) :
  fpath f x s -> {subset x::s <= p} -> {in belast x s, forall y, p (f y)}.
Proof.
rewrite -[{subset _ <= _}]/({in x::s, forall y, p y}) !(rwP allP).
elim: s x => //= a s IHs x /andP [/eqP->] pth_s /and3P [_ pa all_s] /=. 
by rewrite pa IHs.
Qed.

Lemma wheel_segment x : cnode z x -> cface (inD (face x)) (inD (face (node x))).
Proof.
move=> n_z_x. 
have [xN nxN] : face x \notin N /\ face (node x) \notin N. 
  by split; apply: wheel_proof; rewrite -?cnode1r.
pose enx := edge (node x).
have enx_fx : enx = finv face x by apply: faceI; rewrite nodeK f_finv.
have f_x_enx : cface x enx by rewrite /enx cface1r nodeK.
have enxN : enx \in N by apply/NP; rewrite /enx plain_eq // -cnode1r n_z_x.
have [o orbit_fx] : exists o, orbit face (face x) = face x :: o ++ [:: enx; x].
{ have/(orbit_rot_iter 2 faceI):= (orbit_prefix (arity3 enx)).
  rewrite !iterS !iter0 !trajectS [traject _ _ 0]/= [drop]lock.
  rewrite !(rot1_cons,rcons_cat) /= -/cat enx_fx !f_finv // rcons_cat.
  by move->; eexists. }
have subF : {subset [predI cface x & N] <= [:: enx; x] }.
{ move => v; rewrite !inE => /andP[f_x_v /NP /orP[n_z_v|n_z_ev]].
  - rewrite [v == x]rwT // eq_sym; apply: wlog_neg => xDv.
    have := cycleG xDv f_x_v. by rewrite (connect_trans _ n_z_v) // cnodeC.
  - rewrite [v == enx]rwT //= enx_fx -(inj_eq faceI) f_finv // eq_sym.
    have A : cnode x (edge v) by apply: connect_trans n_z_ev; rewrite cnodeC.
    rewrite -plain_eq' // -cnode1r in A.
    rewrite cface1r in f_x_v. 
    apply: contraTT A => eqN. exact: cycleG f_x_v. }
have subN : {in face x :: o, forall y, y \notin N}.
{ move=> y Hy; apply: contraTN (orbit_uniq face (face x)) => yN.
  rewrite orbit_fx -cat_cons cat_uniq [has _ _]rwT //; apply/hasP; exists y => //.
  apply: subF; rewrite !inE /= yN cface1 fconnect_orbit orbit_fx.
  by rewrite -cat_cons mem_cat Hy. }
pose w := last (face x) o.
have [fpath_o face_w] : fpath face (face x) o /\ face w = enx.
{ have:= cycle_orbit faceI (face x). rewrite orbit_fx /cycle rcons_path cat_path /=.
  by rewrite -/w andbT => /andP[/and3P[-> /eqP->]]. }
have subN' : {in belast (face x) o, forall y, face y \notin N} 
  by apply: fpath_sub_belast fpath_o subN.
have wN : w \notin N by apply/subN; rewrite mem_last.
apply: (@connect_trans _ _ (inD w)); last first.
- rewrite /inD !insubdT. apply: connect1. 
  rewrite /= -[del_node_face_]/(@face del_node) del_node_faceE. (* bad simpl behavior *)
  rewrite -val_eqE /= /del_node_face face_w enxN.
  by rewrite /enx -plain_eq' // finv_f.
- apply/connectP; exists (map inD o); last by rewrite last_map.
  apply: homo_fpath_in fpath_o => y y_o. 
  rewrite /inD insubdT => [|fyN]; first exact/subN'.
  rewrite insubdT => [|yN]; first exact/subN/mem_belast.
  apply/val_inj; by rewrite del_node_faceE /del_node_face /= (negPf fyN).
Qed.

Lemma neighbor_face_aux x : cnode z x -> cface (inD (face z)) (inD (face x)).
Proof.
case/connectP => p pth_p ->; elim/last_ind: p pth_p => // p y IH. 
rewrite last_rcons rcons_path => /andP[A /eqP <-].
by apply: connect_trans (IH A) _; apply: wheel_segment; apply/connectP; exists p.
Qed.

Lemma del_node_adjn_face x : 
  adjn z x -> exists d' : del_node , d' \in orbit face z' /\ cnode (val d') x.
Proof.
case/exists_inP => y; rewrite !inE => n_z_y n_x_ey.
exists (Sub (face y) (wheel_proof n_z_y)); split. 
- rewrite -fconnect_orbit /z'; do 2 move: (wheel_proof _) => ?.
  by have:= neighbor_face_aux n_z_y; rewrite /inD !insubdT.
- by rewrite /= cnode1 plain_eq' // cnodeC.
Qed.

End DelNode.




Section sub_planar.


Set Bullet Behavior "Strict Subproofs".

Lemma skip_skip1 (G : hypermap) (p : pred G) (z : G) (f : G -> G) (injf : injective f) (x : G) (xDz : x != z) :
  let G' := WalkupF z in
  let p' := fun x : G' => p (val x) in 
  ~~ p z -> p x -> skip p f x = sval (skip p' (@walkup.skip (permF G) z f injf) (Sub x xDz)).
Proof.
move => G' p' npz px. 
symmetry. 
case: skipP => //. exact: inj_skip.
move => n _ N1 N2.
have [y Y1 Y2] : exists2 y, p y & fconnect f (f x) y. 
{ exists x => //. by rewrite -same_fconnect1. }
elim: n x xDz {px} Y2 N1 N2 => [|n IHn] x xDz Y2  N1 N2.
- rewrite /=. case: (altP (f x =P z)) => [EQ|NEQ]. 
  + rewrite (skip_first y) // EQ // skip1 //. 
    move: N1. by rewrite /walkup.skip unfold_in /= EQ eqxx.
  + rewrite skip1 //. move: N1. by rewrite /walkup.skip unfold_in /= (negbTE NEQ).
- rewrite iterSr. set wfx := walkup.skip _ _. 
  have npfx : ~~ p' wfx. apply/negP => pfx. move: (N2 0) => /=. by case/(_ _)/Wrap. 
  pose fx := (if f x == z then f z else f x).
  rewrite [n.+1]lock /wfx {2}/walkup.skip. move: (skip_subproof _ _) => /= fxDz.
  rewrite -[exist _ _ _]/(Sub fx fxDz). rewrite -lock IHn.
  + rewrite /fx. case: (altP (f x =P z)) => [EQ|NEQ]; last first.
    * rewrite [RHS](skip_first y) //. 
      apply: contraNN npfx. by rewrite /wfx/walkup.skip/p'/= (negbTE NEQ).
    * rewrite [RHS](skip_first y) // ?EQ //. 
      rewrite [RHS](skip_first y) //. by rewrite -EQ -same_fconnect1.
      apply: contraNN npfx. by rewrite /wfx/walkup.skip/p'/= EQ eqxx.
  + rewrite /fx. case: (altP (f x =P z)) => [EQ|NEQ]; last first.
    * by rewrite -same_fconnect1. 
    * by rewrite -EQ -2!(same_fconnect1 injf).
  + rewrite [Sub fx fxDz](_ : _ = wfx) /wfx -?iterSr //. exact: val_inj.
  + move => m. rewrite [Sub fx fxDz](_ : _ = wfx) /wfx -?iterSr. apply: N2. exact: val_inj.
Qed.

(** Any sub-map whose edge and node permutations only skip over the
removed darts has at most the genus of the original map, because this
only results in merging faces. Indeed, every such hypermap can be
obtained (up to isomporphism) by removing the darts one-by-one using
the [WalkupF] operation. *)
Theorem sub_genus (G : hypermap) (p : pred G) (e n f : sig p -> sig p) (can3enf : cancel3 e n f) :
  let H := Hypermap can3enf in
  (forall (x : H), val (edge x) = skip p edge (val x)) ->
  (forall (x : H), val (node x) = skip p node (val x)) -> 
  genus H <= genus G.
Proof.
elim/card_ind : G p e n f can3enf => G IH p e n f can3enf H sameE sameN.
case: (boolP [forall x, p x]) => [/forallP all_p|/forallPn [z npz]].
- suff I : hiso H G by rewrite (hiso_genus I).
  hiso (subT_bij all_p).
  + move => x /=; rewrite sameE skip1 //; exact: all_p.
  + move => x /=; rewrite sameN skip1 //; exact: all_p.
- pose G' := WalkupF z.
  apply: (@leq_trans (genus G')); last exact: le_genus_WalkupF.
  pose p' := (fun  x : G' =>  p (val x)).
  have skip_edge := @skip_hom _ p' _ (@edgeI G').
  have skip_node := @skip_hom _ p' _ (@nodeI G').
  pose e' := frestrict skip_edge.
  pose n' := frestrict skip_node.
  pose f' := finv n' \o finv e'. 
  have can3enf' : cancel3 e' n' f'. 
  { move => x. rewrite /f'/= finv_f ?f_finv //. 
    - apply/frestrict_inj/skip_inj/(@nodeI G').
    - apply/frestrict_inj/skip_inj/(@edgeI G'). }
  (* [H] and [Hypermap can3enf'] are the same up to sigma-nesting *)
  suff I : hiso H (Hypermap can3enf').
  { rewrite (hiso_genus I).
    (apply: leq_trans; last apply: (IH G' _ p' e' n' f' can3enf')) => //.
    - by rewrite /G' /WalkupF /= (card_S_Walkup z). 
    - by case.
    - by case. }
  have fwd_proof1 (x : sig p) : val x != z by apply: contraTneq (valP x) => ->.
  have fwd_proof2 (x : sig p) : p' (Sub (val x) (fwd_proof1 x)) by exact: (valP x).
  pose i_fwd (x : sig p) : sig p' := Sub _ (fwd_proof2 x).
  have bwd_proof (x : sig p') : p (val (val x)) by apply: (valP x).
  pose i_bwd (x : sig p') : sig p := Sub _ (bwd_proof x).
  have can_fwd : cancel i_fwd i_bwd by move => x; apply: val_inj.
  have can_bwd : cancel i_bwd i_fwd by move => x; do 2 apply: val_inj.
  hiso (Bij can_fwd can_bwd).
  * case => x px /=. do ! apply: val_inj => /=. rewrite sameE /=.
    move: (fwd_proof1 _) => /= xDz; rewrite -[exist _ _ _]/(Sub x xDz). 
    exact: skip_skip1.
  * case => x px /=. do ! apply: val_inj => /=. rewrite sameN /=.
    move: (fwd_proof1 _) => /= xDz; rewrite -[exist _ _ _]/(Sub x xDz). 
    exact: skip_skip1.
Qed.

Variables (G : hypermap) (p : pred G) (e n f : sig p -> sig p).
Hypothesis can3enf : cancel3 e n f.

Let H := Hypermap can3enf.

(** relative order of remaining darts in e- and n-cycles remains unchanged *)
Hypothesis sameE : forall (x : H), val (edge x) = skip p edge (val x).
Hypothesis sameN : forall (x : H), val (node x) = skip p node (val x).

Lemma sub_planar : planar G -> planar H.
Proof. rewrite /planar -!leqn0; exact/leq_trans/sub_genus. Qed.

End sub_planar.

Lemma del_node_planar (G : hypermap) (z : G) :
  planar G -> planar (del_node z).
Proof.
apply: sub_planar; last by move => x; rewrite val_frestrict.
case => x Nx /=. rewrite skip1 // unfold_in -fclosed1 //. 
exact/closure_closed/cedgeC.
Qed.

(** *** Adding an Edge. *)

(** [h_add_edge x y] connects [cnode x] and [cnode y] with an edge. The
darts of this edge [IcpX] and [IcpXe] are added to the nodes after [x]
and [y]. If [x] and [y] lie on a common f-cycle or on disconncted
components, this preserves planarity *)
Arguments IcpX {A}.
Arguments IcpXe {A}.

Section AddEdge.
Variables (G : hypermap) (x y : G).

Definition add_edge_edge (z : ecp_dart G) : ecp_dart G := 
  match z with 
  | IcpX => IcpXe
  | IcpXe => IcpX
  | Icp z' => Icp (edge z')
  end.

Definition add_edge_node (z : ecp_dart G) : ecp_dart G := 
  match z with 
  | IcpX => Icp (node x)
  | IcpXe => Icp (node y)
  | Icp z' => if z' == x then IcpX else 
             if z' == y then IcpXe else Icp (node z') 
  end.

Definition add_edge_face (z : ecp_dart G) : ecp_dart G := 
  match z with 
  | IcpX => Icp y
  | IcpXe => Icp x
  | Icp z' => if face z' == x then IcpX else 
             if face z' == y then IcpXe else Icp (face z')
  end.

Hypothesis xDy : x != y.

Lemma add_edge_can3 : cancel3 add_edge_edge add_edge_node add_edge_face.
Proof.
case => [||z]; rewrite /= ?eqxx ?[y == x]eq_sym ?(negbTE xDy) //.
case: (altP (face (edge z) =P x)) => /= [<-|Dx]; first by rewrite edgeK.
case: (altP (face (edge z) =P y)) => /= [<-|Dy]; first by rewrite edgeK.
by rewrite (negbTE Dx) (negbTE Dy) edgeK.
Qed.

Definition h_add_edge := Hypermap add_edge_can3.

Let H := h_add_edge.

Fact add_edge_node_x : node (Icp x : H) = IcpX.
Proof. by rewrite /= eqxx. Qed.
Fact add_edge_node_y : node (Icp y : H) = IcpXe.
Proof. by rewrite /= eqxx eq_sym (negbTE xDy). Qed.

(** The rest of this section is about proving that adding an edge
across a face (i.e., splitting a face) preserves planarity. To this
end, we show that (up to isomorphim) [G] can be obtained from [H] by a
double WalkupF operation. The second operation is degenerate: after
removing [IcpX], [IcpXe] has an e-loop. Thus, all three Walkup
operations coincide and we can use WalkupE, which involves no
permutaion of the hypermap components *)

Let SXe : IcpXe != IcpX :> H. done. Qed.
Definition G' := @WalkupE (WalkupF (IcpX : H)) (Sub IcpXe SXe).

Let S (z : G) : Icp z != IcpX. done. Qed.

Definition i (z : G) : G' := Sub (Sub (Icp z) (S z)) SXe.
Definition i_inv (z : G') : G := if val (val z) is Icp i then i else x.

Let vvE (z : G') : exists z', val (val z) = Icp z'. 
Proof. move: z; (do 3 case) => //= a. by exists a. Qed.

Let can_fwd : cancel i_inv i. 
Proof.
move => u; case: (vvE u) => u' E; rewrite /i /i_inv E.
do 2 apply: val_inj => /=. by symmetry.
Qed.

Let can_bwd : cancel i i_inv. done. Qed.

Let com_i_node u : i (node u) = node (i u).
Proof.
do 2 apply/val_inj; rewrite /= /walkup.skip /= !fun_if /=.
move: (skip_subproof _ _) => /=.
by case: (altP (u =P x)) => [->//|uDx]; case: (altP (u =P y)) => [->|].
Qed.

Let com_i_edge u : i (edge u) = edge (i u). Proof. by do 2 apply: val_inj. Qed.

Definition h_add_edge_iso : hiso G G' :=
  let I := Bij can_bwd can_fwd in
  @Hiso G G' I com_i_edge com_i_node.

(** this is [~~ cross_edge (IcpX : H)] for WalkupF (IcpX : H) ] *)
Lemma add_edge_no_cross : cface x y -> ~~ cface (IcpX : H) (IcpXe : H).
Proof.
move => f_x_y; rewrite /= -fconnect_switched //; last exact: (@faceI H).
rewrite same_fconnect1 /=; last by apply/switch_inj/(@faceI H).
rewrite -[y](f_finv faceI) -same_fconnect1_r // in f_x_y.
have := iter_findex (f_x_y).
have Hx: forall m, iter m.+1 face x = x -> findex face x (finv face y) <= m. 
{ move => m Ex. rewrite -ltnS.
  have L : looping face x m.+1 by rewrite /looping Ex /= inE eqxx.
  apply: leq_trans (order_le_looping L). exact: findex_max. }
move: (findex _ _ _) Hx => n Hx In.
elim: n {-3}x In Hx => [/= z|n IHn z In Hx]. 
- move => Ez _. apply: connect1 => /=. 
  by rewrite Ez f_finv // eqxx [_ == x]eq_sym (negbTE xDy).
- rewrite iterSr in In. move/IHn in In.
  rewrite same_fconnect1 /=; last by apply/switch_inj/(@faceI H).
  have/negbTE -> : face z != x.  move: (Hx 0). by apply: contraPneq => /= -> /(_ erefl).
  case:(altP (face z =P y)) => // fzy. apply In => m. rewrite -iterSr. by move/Hx.
Qed.

Lemma add_edge_genus : cface x y -> genus H = genus G.
Proof.
move => f_x_y; rewrite (hiso_genus h_add_edge_iso) /G' /H. 
rewrite genus_WalkupE_eq; last by left.
rewrite genus_walkupF_eq //. exact: add_edge_no_cross.
Qed.

Lemma add_edge_planar : cface x y -> planar G -> planar h_add_edge.
Proof. by move=> f_x_y; rewrite /planar add_edge_genus. Qed.

Let Ico_inj : injective (@Icp G). by move => ? ? []. Qed.

Lemma add_edge_cnodeE u v : cnode (Icp u : H) (Icp v) = cnode u v.
Proof.
apply/idP/idP; case/connectP => p.
- elim/(size_ind (@size H)) : p u => -[/= _ u _ [->] //|/= z p IH u].
  have [fuEx /andP[/eqP <-] {z}|fuDx] := eqVneq u x. 
  + case: p IH => [|z p] //= IH => /andP[/eqP<-] {z}. 
    by rewrite cnode1 fuEx; apply: IH.
  + have [fuEy /andP[/eqP <-] {z}|fuDy] := eqVneq u y. 
    * case: p IH => [|z p] //= IH => /andP[/eqP<-] {z}. 
      by rewrite cnode1 fuEy; apply: IH.
    * case: z => [||z]; rewrite // inj_eq // => /andP [/eqP fu_z pth_p lst_p].
    rewrite cnode1 fu_z. exact: IH pth_p lst_p.
- elim: p u => //= [u _ -> //|z p IHp u /andP[/eqP fu_z] pth_p lst_p].
  have ? := @nodeI h_add_edge; rewrite same_fconnect1 //=.
  have [fu_x|_] := eqVneq u x; first by rewrite same_fconnect1 //= -fu_x fu_z; exact: IHp.
  have [fu_y|_] := eqVneq u y; first by rewrite same_fconnect1 //= -fu_y fu_z; exact: IHp.
  by rewrite fu_z; exact: IHp.
Qed.

Lemma add_edge_adjn u v : 
  adjn (Icp u : H) (Icp v) = 
  [|| adjn u v , cnode u x && cnode v y | cnode u y && cnode v x].
Proof.
apply/exists_inP/idP => [[[||z]]|]; rewrite ?inE; last case/or3P.
- by rewrite [_ (Icp u) _]cnode1r [_ (Icp v) _]cnode1r !add_edge_cnodeE -!cnode1r => -> ->.
- by rewrite [_ (Icp u) _]cnode1r [_ (Icp v) _]cnode1r !add_edge_cnodeE -!cnode1r => -> ->.
- rewrite !add_edge_cnodeE => ? ?; rewrite (_ : adjn u v = true) //.
  by apply/exists_inP; exists z.
- by case/exists_inP => z; rewrite !inE -!add_edge_cnodeE => ? ?; exists (Icp z).
- rewrite -!add_edge_cnodeE [_ _ (Icp x)]cnode1r [_ _ (Icp y)]cnode1r /=.
  rewrite !eqxx eq_sym (negbTE xDy) => /andP [? ?]. by exists IcpX.
- rewrite -!add_edge_cnodeE [_ _ (Icp x)]cnode1r [_ _ (Icp y)]cnode1r /=.
  rewrite !eqxx eq_sym (negbTE xDy) => /andP [? ?]. by exists IcpXe.
Qed.

Lemma add_edge_cnodeXXe : cnode (IcpX : H) IcpXe = cnode x y.
Proof. by rewrite cnode1 cnode1r add_edge_cnodeE -cnode1 -cnode1r. Qed.

Lemma add_edge_orbitXe : cface x y ->
  orbit face (IcpXe : H) = IcpXe :: [seq Icp z | z <- arc (orbit face x) x y].
Proof.
set face' := add_edge_face; have faceI' : injective face' by apply: (@faceI H).
move=> cface_xy; rewrite arc_orbit // /orbit -orderSpred -findex_finv /=.
congr (_ :: _); rewrite -findex_f ?fconnect_finv //= f_finv // -/face'.
have F n :  n < findex face x y -> iter n face' (Icp x) = Icp (iter n face x).
{ elim: n => // n IHn lt_n_y. 
  rewrite iterS IHn 1?ltnW //= -iterS !ifF //.
  - by apply:negPf; apply: before_findex.
  - apply: contraTF (cface_xy) => /eqP it_n. apply: (iter_looping (m := n.+1)).
    + move => m Hm. apply: before_findex => //. exact: ltn_trans lt_n_y.
    + by rewrite /looping it_n /= mem_head. }
suff I : findex face' (Icp x) IcpXe = findex face x y.
{ rewrite I.
  apply: (@eq_from_nth _ (Icp x)); rewrite ?size_map !size_traject // => n Hn.
  by rewrite nth_traject // (nth_map x) ?size_traject // nth_traject ?F. }
have idx0 : 0 < findex face x y by rewrite lt0n findex_eq0.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- apply: findex_bound. rewrite -(prednK idx0) iterS F ?prednK //.
  rewrite -[iter _ _ _](finv_f faceI) -iterS prednK // iter_findex //=.
  by rewrite !f_finv // eqxx eq_sym (negPf xDy).
- rewrite leqNgt; apply/negP; set m := findex face' _ _ => /F.
  by rewrite iter_findex // same_fconnect1_r //= connect0.
Qed.

(** The proof of this lemma is (essentially) the same as above plus
some symmetry reasoning to swap [x] and [y]. *)
Lemma add_edge_orbitX  : cface x y ->
  orbit face (IcpX : H) = IcpX :: [seq Icp z | z <- arc (orbit face x) y x].
Proof.
set face' := add_edge_face; have faceI' : injective face' by apply: (@faceI H). 
rewrite cfaceC => cface_xy.
have -> : arc (orbit face x) y x = arc (orbit face y) y x.
{ have/orbit_rot_cycle : x \in orbit face y by rewrite -fconnect_orbit.
  move=> /(_ face); rewrite cycle_orbit // orbit_uniq => /(_ isT isT) [i ->].
  by rewrite arc_rot // in_orbit. }
rewrite arc_orbit // /orbit -orderSpred -findex_finv /=.
congr (_ :: _); rewrite -findex_f ?fconnect_finv //= f_finv // -/face'.
have F n :  n < findex face y x -> iter n face' (Icp y) = Icp (iter n face y).
{ elim: n => // n IHn lt_n_y. 
  rewrite iterS IHn 1?ltnW //= -iterS !ifF //; last first.
  - by apply:negPf; apply: before_findex.
  - apply: contraTF (cface_xy) => /eqP it_n. apply: (iter_looping (m := n.+1)).
    + move => m Hm. apply: before_findex => //. exact: ltn_trans lt_n_y.
    + by rewrite /looping it_n /= mem_head. }
suff I : findex face' (Icp y) IcpX = findex face y x.
{ rewrite I.
  apply: (@eq_from_nth _ (Icp y)); rewrite ?size_map !size_traject // => n Hn.
  by rewrite nth_traject // (nth_map y) ?size_traject // nth_traject ?F. }
have idx0 : 0 < findex face y x by rewrite lt0n findex_eq0 eq_sym.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- apply: findex_bound. rewrite -(prednK idx0) iterS F ?prednK //.
  rewrite -[iter _ _ _](finv_f faceI) -iterS prednK // iter_findex //=.
  by rewrite !f_finv // eqxx. 
- rewrite leqNgt; apply/negP; set m := findex face' _ _ => /F.
  by rewrite iter_findex // same_fconnect1_r //= connect0.
Qed.

Lemma add_edge_plain : plain G -> plain H.
Proof.
move=> plainG; apply/plainP => -[||z] _ //=.
by rewrite (rwP eqP) !inj_eq // plain_eq // plain_neq.
Qed.

End AddEdge.

(** The consruction [h_add_node G x] extends the hypermap [G] with an
addional node on the inside of the face of [x] and connected only to
[cnode x] *)

Section AddNode.
Variables (G : hypermap) (x : G).

Definition add_node_edge (z : ecp_dart G) : ecp_dart G := 
  match z with 
  | IcpX => IcpXe
  | IcpXe => IcpX
  | Icp z => Icp (edge z)
  end.

Definition add_node_node (z : ecp_dart G) : ecp_dart G := 
  match z with 
  | IcpX => Icp (node x)
  | IcpXe => IcpXe
  | Icp z => if z == x then IcpX else Icp (node z) 
  end.

Definition add_node_face (z : ecp_dart G) : ecp_dart G := 
  match z with 
  | IcpX => IcpXe
  | IcpXe => Icp x
  | Icp z => if face z == x then IcpX else Icp (face z)
  end.

Lemma add_node_can3 : cancel3 add_node_edge add_node_node add_node_face.
Proof.
case => [||z]; rewrite /= ?eqxx //. 
case: (eqVneq (face (edge z)) x) => /= [<-|Dx]; by rewrite ?(negbTE Dx) edgeK.
Qed.

Definition h_add_node := Hypermap add_node_can3.

Let Ico_inj : injective (@Icp G). Proof. by move => u v []. Qed.

Lemma add_node_plain : plain G -> plain h_add_node.
Proof.
move/plainP => plain_G; apply/plainP => -[||z] //= _.
by move/(_ z isT) : plain_G => [-> ->].
Qed.

Lemma add_node_genus : genus h_add_node = genus G.
Proof.
set H := h_add_node.
have SX : IcpX != IcpXe :> H by [].
pose G' := @WalkupE (WalkupE (IcpXe : H)) (Sub IcpX SX).
suff i : hiso G G'. 
{ rewrite (hiso_genus i) !genus_WalkupE_eq //. 
  - rewrite glinkN; tauto. 
  - have E : Sub IcpX SX = @edge (WalkupE (IcpXe : H)) (Sub IcpX SX).
      exact: val_inj.
    by rewrite {2}E glinkE; tauto. }
have S (z : G) : Icp z != IcpX by done. 
pose i (z : G) : G' := Sub (Sub (Icp z) (S z)) SX.
pose i_inv (z : G') : G := if val (val z) is Icp i then i else x.
have vvE (z : G') : exists z', val (val z) = Icp z'. 
{ move: z; (do 3 case) => //= a. by exists a. } 
have can_fwd : cancel i_inv i. 
{ move => u; case: (vvE u) => u' E; rewrite /i /i_inv E.
  do 2 apply: val_inj => /=. by symmetry. }
have can_bwd : cancel i i_inv by done. 
have com_i_node u : i (node u) = node (i u).
{ do 2 apply/val_inj; rewrite /= !fun_if /= -val_eqE /=.
  by case: (eqVneq u x) => //= ->. }
have com_i_edge u : i (edge u) = edge (i u). 
{ do 2 apply: val_inj => //=; by case: (eqVneq (face (edge u)) x). }
exact: (@Hiso _ _ (Bij can_bwd can_fwd) com_i_edge com_i_node).
Qed.

Lemma add_node_planar : planar h_add_node = planar G.
Proof. by rewrite /planar add_node_genus. Qed.

Lemma add_node_cfaceE u v : 
  cface (Icp u : h_add_node) (Icp v) = cface u v.
Proof.
apply/idP/idP; case/connectP => p.
- elim/(size_ind (@size h_add_node)) : p u => -[/= _ u _ [->] //|/= z p IH u].
  have [fuEx /andP[/eqP <-] {z}|fuDx] := eqVneq (face u) x. 
  + case: p IH => [|z p] //= IH => /andP[/eqP<-] {z}.
    case: p IH => [|z p] //= IH => /andP[/eqP<-].
    by rewrite cface1 fuEx; apply: IH; rewrite -addn2 leq_addr.
  + case: z => [||z]; rewrite // inj_eq // => /andP [/eqP fu_z pth_p lst_p].
    rewrite cface1 fu_z. exact: IH pth_p lst_p.
- elim: p u => //= [u _ -> //|z p IHp u /andP[/eqP fu_z] pth_p lst_p].
  have ? := @faceI h_add_node; rewrite same_fconnect1 //=.
  have [fu_x|_] := eqVneq (face u) x; last by rewrite fu_z; exact: IHp.
  rewrite same_fconnect1 //= same_fconnect1 //= -fu_x fu_z. exact: IHp.
Qed.

Lemma add_node_cnodeE u v : 
  cnode (Icp u : h_add_node) (Icp v) = cnode u v.
Proof.
apply/idP/idP; case/connectP => p.
- elim/(size_ind (@size h_add_node)) : p u => -[/= _ u _ [->] //|/= z p IH u].
  have [fuEx /andP[/eqP <-] {z}|fuDx] := eqVneq u x. 
  + case: p IH => [|z p] //= IH => /andP[/eqP<-] {z}. 
    by rewrite cnode1 fuEx; apply: IH.
  + case: z => [||z]; rewrite // inj_eq // => /andP [/eqP fu_z pth_p lst_p].
    rewrite cnode1 fu_z. exact: IH pth_p lst_p.
- elim: p u => //= [u _ -> //|z p IHp u /andP[/eqP fu_z] pth_p lst_p].
  have ? := @nodeI h_add_node; rewrite same_fconnect1 //=.
  have [fu_x|_] := eqVneq u x; last by rewrite fu_z; exact: IHp.
  rewrite same_fconnect1 //= -fu_x fu_z. exact: IHp.
Qed.

Lemma add_node_cnodeXe u :  
  cnode (IcpXe : h_add_node) u = (u == IcpXe).
Proof.
by apply/idP/eqP => [/connectP []|-> //]; elim => //= a p IH /andP[/eqP<-].
Qed.

Lemma add_node_adjn u v : 
  adjn (Icp u : h_add_node) (Icp v) = adjn u v.
Proof.
apply/exists_inP/exists_inP => [|[z Z1 Z2]]; last by exists (Icp z); rewrite inE add_node_cnodeE.
move=> [[||z] Z1 Z2]; rewrite !inE [edge _]/= in Z1 Z2. 
- by rewrite cnodeC add_node_cnodeXe in Z2.
- by rewrite cnodeC add_node_cnodeXe in Z1.
- by exists z; rewrite inE -add_node_cnodeE.
Qed.

Lemma add_node_adjnXeXe : adjn (IcpXe : h_add_node) IcpXe = false.
Proof.
apply/negbTE/negP=>/exists_inP [z]; rewrite inE add_node_cnodeXe => /eqP->.
by rewrite inE add_node_cnodeXe. 
Qed.

Lemma add_node_adjnXe u : adjn (IcpXe : h_add_node) (Icp u) = cnode x u.
Proof.
apply/exists_inP/idP => [[z]|x_u].
  rewrite !inE add_node_cnodeXe cnodeC => /eqP->. 
  by rewrite cnode1 add_node_cnodeE -cnode1.
exists IcpXe; rewrite !inE // cnode1r [edge _]/=.
by rewrite add_node_cnodeE -cnode1r cnodeC.
Qed.

Lemma add_node_face_orbitE : 
  orbit add_node_face IcpX = [:: IcpX, IcpXe & [seq Icp z | z <- orbit face x]].
Proof.
rewrite /orbit. 
have -> : order add_node_face IcpX = (arity x).+2. 
{ rewrite /order -[in RHS](card_imset _ Ico_inj).
  set IcpF := [set _ _ | _ in _].
  rewrite [LHS](eq_card (_ : _ =i [set IcpX; IcpXe] :|: IcpF)).
  - rewrite -setUA !cardsU1 !inE /= 2![_ \in IcpF](negbTE _) //.
    all: by apply/negP => /imsetP [?].
  - move => z; rewrite !inE. 
    case: (eqVneq z IcpX) => [->|]; first by rewrite connect0.
    case: (eqVneq z IcpXe) => [->|]; first by rewrite connect1.
    have ? := @faceI h_add_node.
    case: z => [z||]//= z _ _; rewrite same_fconnect1 //= same_fconnect1 //=.
    rewrite /IcpF mem_imset_eq // inE. exact: add_node_cfaceE. }
rewrite /=; congr [:: _ , _ & _].
apply: (@eq_from_nth _ (Icp x)); first by rewrite size_map !size_traject.
move => n; rewrite size_traject => lt_n_st. 
rewrite nth_traject // (nth_map x) ?size_traject // nth_traject //.
elim: n lt_n_st => // n IHn lt_Sn_x. rewrite iterS IHn 1?ltnW //= -iterS ifF //.
apply: contraTF (lt_Sn_x) => /eqP; rewrite -leqNgt => fix_x.
exact: order_le_fix.
Qed.

End AddNode.
