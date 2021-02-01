From mathcomp Require Import all_ssreflect.
From fourcolor Require Import hypermap geometry.
Require Import preliminaries digraph sgraph hmap_ops embedding.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma order_max (T : finType) (f : T -> T) (x : T) : order f x <= #|T|.
Proof. by rewrite -size_orbit -(card_uniqP _) ?max_card ?orbit_uniq. Qed.



Section Dfs.
Variables (T : finType) (g : T -> seq T).

(* not used *)
Lemma dfs_uniq  (v : seq T) x n : 
  uniq v -> uniq (dfs g n v x).
Proof.
elim: n v x => [|/= n IHn] v x uniq_v ; first by rewrite /= if_same.
have [//|xNv] := boolP (x \in v).
have: uniq (x::v) by rewrite /= xNv.
elim: (g x) (x::v) => //= => {v x uniq_v xNv} y gx IHgx v uniq_v.
exact/IHgx/IHn.
Qed.

Lemma dfs_start x : x \in dfs g #|T| [::] x.
Proof. by apply/dfsP; exists [::]. Qed.

(** To actually run [dfs] we need to have [#|T|] as an explicit number *)
Variable k : nat.
Hypothesis kT : k = #|T|.

Definition connect_dfs x := dfs g k [::] x.

Lemma connectEdfs x : connect (grel g) x =i connect_dfs x.
Proof. by move=> y;rewrite /connect_dfs kT; apply/connectP/dfsP. Qed.

Fixpoint n_comp_dfs_rec n (s: seq T) :=
  if n isn't n'.+1 then 0 else
  if s is y::s' then
    let p := connect_dfs y in 
    (n_comp_dfs_rec n' (filter [predC p] s')).+1 else 0.

Definition n_comp_dfs s := n_comp_dfs_rec (size s) s.

Lemma n_comp_dfsP (s: seq T) : 
  connect_sym (grel g) -> closed (grel g) s -> n_comp (grel g) s = n_comp_dfs s.
Proof.
move=> csym_g; rewrite /n_comp_dfs; move: {-1}(size s) (leqnn (size s)) => n.
have [m Hm] := ubnP (size s); elim: m s Hm n => // m IH [_|y s /ltnSE Hm [//|n]].
  by move => n _ _; rewrite n_comp0 //; case: n.
move=> leq_s_n closed_y; set p := connect_dfs y.
have y_p : y \in p by rewrite /p/connect_dfs kT; exact: dfs_start. 
have Hp : p =i connect (grel g) y by move => ?; apply/esym/connectEdfs.
have sub_p : {subset p <= y::s}.
{ move=> z; rewrite Hp inE => con_yz. 
  by rewrite -(closed_connect closed_y con_yz) mem_head. }
rewrite (n_compD (mem p)) [RHS]/= -/p -add1n; congr(_ + _).
- suff S : [predI y :: s & mem p] =i connect (grel g) y.
    by rewrite (eq_n_comp_r S) n_comp_connect.
  by move=> z; rewrite -[RHS]Hp inE /= andb_idl//; exact: sub_p.
- rewrite -IH.
  + apply: eq_n_comp_r => z; rewrite mem_filter !inE.
    have [//|zNp/=] := boolP (z \in p); rewrite (_ : z == y = false) //.
    by apply: contraNF zNp => /eqP->. 
  + by apply: leq_trans Hm; rewrite size_filter /= ltnS count_size.
  + rewrite /= ltnS in leq_s_n. apply: leq_trans leq_s_n. 
    by rewrite size_filter count_size.
  + have -> : [seq x <- s | [predC p] x] = [seq x <- y::s | [predC p] x].
      by rewrite /= y_p.
    have i : [seq x <- y :: s | [predC p] x] =i [predD (y :: s) & p].
      by move=> z; rewrite mem_filter /= !inE. 
    rewrite (eq_closed_r i); apply: predD_closed => //.
    by rewrite (eq_closed_r Hp); apply: connect_closed.
Qed.

End Dfs.

(** TODO: this uses nothing that is specific to ['I_n], all we use is
that [#|'I_n| = n] and that we habe a concrete enumeration, i.e., one
where all elements of the list are of the form [Ordinal n (isT : _)].
Hence, it would be preferrabe to introduce a class or structure for
this. *)

Section ComputeOrd.
Variable (n : nat).

Definition ord_enum_eq : seq 'I_n := pmap (insub_eq _) (iota 0 n).

Lemma eq_ord_enum : ord_enum_eq = ord_enum n.
Proof. apply:eq_in_pmap => k _. exact: insub_eqE. Qed.

Lemma ord_enum_eqT : ord_enum_eq =i 'I_n.
Proof. by move => i; rewrite eq_ord_enum mem_ord_enum. Qed.

Lemma forall_all_ord (p : {pred 'I_n}) : 
  [forall x : 'I_n, p x] = all p ord_enum_eq.
Proof. 
by rewrite forall_all; apply/eq_all_r => x; rewrite mem_enum ord_enum_eqT. 
Qed.

Lemma exists_has_ord (p : {pred 'I_n}) : 
  [exists x : 'I_n, p x] = has p ord_enum_eq.
Proof. 
by rewrite exists_has ; apply/eq_has_r => x; rewrite mem_enum ord_enum_eqT. 
Qed.

Implicit Types (e: rel 'I_n) (f : 'I_n -> 'I_n) (x : 'I_n).

Definition sseq e x := [seq y <- ord_enum_eq | e x y].

Let eq_sseq e : e =2 grel (sseq e).
Proof.
by move=> x y /=; rewrite mem_filter eq_ord_enum mem_ord_enum andbT.
Qed.

Definition n_comp_ord e (s : seq 'I_n)  := n_comp_dfs (sseq e) n s.

Lemma n_compEord_seq e (s : seq 'I_n) (a : {pred 'I_n}) : 
  connect_sym e -> closed e a -> s =i a -> n_comp e a = n_comp_ord e s.
Proof.
move=> sym_e cl_a eq_a_s; rewrite -(eq_n_comp_r eq_a_s).
rewrite (eq_n_comp (eq_connect (eq_sseq e))). 
apply: n_comp_dfsP; rewrite ?card_ord //.
  exact: eq_connect_sym sym_e.
by rewrite -(eq_closed (eq_sseq e)) (eq_closed_r eq_a_s).
Qed.

Definition order_ord f x := size (undup (traject f x n)).

Lemma orderEord f x : order f x = order_ord f x.
Abort.

Definition orbit_ord f x := traject f x (order_ord f x).

Lemma orbitEord f x : orbit f x = orbit_ord f x.
(* Proof. by rewrite /orbit_ord -orderEord. Qed. *)
Abort.

Definition connect_ord (e : rel 'I_n) x y := y \in dfs (sseq e) n [::] x.

Lemma connectEord (e : rel 'I_n) : connect e =2 connect_ord e.
Proof. 
move => x y; rewrite (eq_connect (eq_sseq e)); apply: connectEdfs.
by rewrite card_ord.
Qed.

Definition fcard_ord f := n_comp_dfs (fun x => [:: f x]) n ord_enum_eq.

Lemma n_compEord e : 
  connect_sym e -> n_comp e 'I_n = n_comp_ord e (ord_enum_eq).
Proof. move=> sym_s; exact: n_compEord_seq ord_enum_eqT. Qed.

(** we don't use [n_compEord_seq], because doing so would require
proving extensionality of [dfs] and the SCC algorithm *)
Lemma fcardEord f : injective f -> fcard f 'I_n = fcard_ord f.
Proof. 
have eq_f : frel f =2 grel (fun x => [:: f x]).
  by move => u v; rewrite /= !inE eq_sym.
move=> inj_f; rewrite (eq_n_comp (eq_connect eq_f)).
rewrite -(eq_n_comp_r ord_enum_eqT).
rewrite (n_comp_dfsP (k := n)) ?card_ord //.
- apply: eq_connect_sym eq_f _. exact: fconnect_sym. 
- move => x y. by rewrite !ord_enum_eqT.
Qed.

End ComputeOrd.

Section D4.

Definition n := 12.
Notation "''d' m" := (@Ordinal n m is_true_true) (at level 0, m at level 8, format "''d' m").

Definition D4_edge (x : 'I_n) : 'I_n :=
  match val x with
    | 0 => 'd4
    | 1 => 'd7
    | 2 => 'd10
    | 3 => 'd8
    | 4 => 'd0
    | 5 => 'd9
    | 6 => 'd11
    | 7 => 'd1
    | 8 => 'd3
    | 9 => 'd5
    | 10 => 'd2
    | 11 => 'd6
    | _ => 'd0
  end.

Definition D4_node (x : 'I_n) : 'I_n :=
  match val x with
  | 0 => 'd1
  | 1 => 'd2
  | 2 => 'd0
  | 3 => 'd4
  | 4 => 'd5
  | 5 => 'd3
  | 6 => 'd7
  | 7 => 'd8
  | 8 => 'd6
  | 9 => 'd10
  | 10 => 'd11
  | 11 => 'd9
  | _ => 'd0
  end.

Definition D4_face (x : 'I_n) : 'I_n := 
  match val x with
  | 0 => 'd3
  | 1 => 'd6
  | 2 => 'd9
  | 3 => 'd7
  | 4 => 'd2
  | 5 => 'd11
  | 6 => 'd10
  | 7 => 'd0
  | 8 => 'd5
  | 9 => 'd4
  | 10 => 'd1
  | 11 => 'd8
  | _ => 'd0
  end.


Lemma D4can : cancel3 D4_edge D4_node D4_face.
Proof. 
move=>x; apply/eqP; move: x; apply/forallP.
by rewrite forall_all_ord.
Qed.

Definition D4 := Hypermap D4can.

Lemma D4_planar : planar D4.
Proof. 
rewrite /planar/genus/Euler_lhs/Euler_rhs. 
rewrite (n_compEord (@glinkC D4)) (fcardEord (@faceI D4)).
by rewrite (fcardEord (@edgeI D4)) (fcardEord (@nodeI D4)) card_ord.
Qed.

Lemma D4_plain : plain D4.
Proof. 
apply/plainP => x _; rewrite (rwP eqP) (rwP andP); move: x.
by apply/forallP; rewrite forall_all_ord. 
Qed.

Definition D4_g (x : D4) : 'K_4 := 
  match val x with
  | 0 => ord0
  | 1 => ord0
  | 2 => ord0
  | 3 => ord1
  | 4 => ord1 
  | 5 => ord1
  | 6 => ord2
  | 7 => ord2
  | 8 => ord2
  | 9 => ord3
  | 10 => ord3
  | 11 => ord3
  | _ => ord0
  end.


Lemma D4_embedding : embedding D4_g.
Proof.
split; first exact D4_plain.
- move=> x. apply/codomP. setoid_rewrite (rwP eqP). apply/existsP; rewrite exists_has_ord. 
  move: x. apply/forallP. rewrite forall_all_ord. reflexivity.
- move => x y. rewrite connectEord (rwP eqP). 
  move: y; apply/forallP; rewrite forall_all_ord.
  move: x; apply/forallP; rewrite forall_all_ord. reflexivity.
- move => x y. rewrite /adjn; under eq_existsb => z do rewrite !inE !connectEord.
  rewrite exists_has_ord (rwP eqP).
  move: y; apply/forallP; rewrite forall_all_ord.
  move: x; apply/forallP; rewrite forall_all_ord. reflexivity.
Qed.

Definition K4_plane_emb := Build_plane_embedding D4_embedding D4_planar.

End D4.

(** Any subgraph of K4 is planar as well *)
Lemma small_planar (G : sgraph) : 
  #|G| <= 4 -> no_isolated G -> inhabited (plane_embedding G).
Proof.
move=> smallG no_isoG.
exact: subgraph_plane_embedding (sub_Kn smallG) no_isoG K4_plane_emb.
Qed.



