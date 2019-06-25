Require Import Setoid CMorphisms Morphisms.
From mathcomp Require Import all_ssreflect.

Require Import edone set_tac finite_quotient preliminaries bij equiv.
Require Import multigraph_new liso.

Require Import mathcomp.finmap.finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 


Definition VT := nat.
Definition ET := nat.

Section inject.
Variable (T : finType).

Definition inj_v (x : T) : VT := enum_rank x.
Definition inj_e (x : T) : ET := enum_rank x.
Definition v0 : VT := 0.

Lemma inj_v_inj : injective inj_v. 
Proof. move => x y. by move/ord_inj/enum_rank_inj. Qed.

Lemma inj_e_inj : injective inj_e. 
Proof. move => x y. by move/ord_inj/enum_rank_inj. Qed.
End inject.

Record pre_graph := { vset : {fset VT};
                      eset : {fset ET};
                      src : ET -> VT;
                      tgt : ET -> VT;
                      lv : VT -> test;
                      le : ET -> term;
                      p_in : VT;
                      p_out : VT }.

Class is_graph (G : pre_graph) := 
  { srcP (e:ET) : e \in eset G -> src G e \in vset G;
    tgtP (e:ET) : e \in eset G -> tgt G e \in vset G;
    p_inP : p_in G \in vset G;
    p_outP : p_out G \in vset G}.

Open Scope fset_scope.

Section Open.
Variable (G : lgraph).

(** G may be edgeless, so there is no way to avoid the option type here *)
Definition proj_e (e : ET) : option (edge G) := 
  omap enum_val (insub e : option 'I_#|edge G|).

Lemma inj_eK (e : edge G) : proj_e (inj_e e) = Some e.
Proof. 
  rewrite /proj_e /inj_e /=. 
  have P : enum_rank e < #|edge G| by [].
  case: insubP => [k _ /ord_inj -> /=|]; by rewrite ?P ?enum_rankK.
Qed.

Definition proj_v (v : VT) : G :=
  odflt input (omap enum_val (insub v : option 'I_#|G|)).

Lemma inj_vK (v : G) : proj_v (inj_v v) = v.
Proof.
  rewrite /proj_v /inj_v /=. 
  have P : enum_rank v < #|G| by [].
  case: insubP => [k _ /ord_inj -> /=|]; by rewrite ?P ?enum_rankK.
Qed.

Definition open : pre_graph := 
  {| vset := [fset inj_v x | x in G];
     eset := [fset inj_e x | x in edge G];
     src (e:ET) := if proj_e e is Some e' then inj_v (source e') else v0;
     tgt (e:ET) := if proj_e e is Some e' then inj_v (target e') else v0;
     lv v := vlabel (proj_v v);
     le e := if proj_e e is Some e' then elabel e' else one;
     p_in := inj_v (input : G);
     p_out := inj_v (output : G) |}.

Global Instance open_is_graph : is_graph open.
Proof.
  split.
  - move => e'. case/imfsetP => /= e _ ->. by rewrite inj_eK in_imfset.
  - move => e'. case/imfsetP => /= e _ ->. by rewrite inj_eK in_imfset.
  - by rewrite /= in_imfset.
  - by rewrite /= in_imfset.
Qed.

End Open.

Section Close.
Variable (G : pre_graph).
Context {graph_G : is_graph G}.

Lemma source_proof (e : eset G) : src G (val e) \in vset G.
Admitted.

Lemma target_proof (e : eset G) : tgt G (val e) \in vset G.
Admitted.

Definition close' : graph test_setoid term_setoid := Eval simpl in 
  {| vertex := [finType of vset G];
     edge := [finType of eset G];
     source e := Sub (src G (val e)) (source_proof e);
     target e := Sub (tgt G (val e)) (target_proof e);
     vlabel v := lv G (val v);
     elabel e := le G (val e) |}.

Definition close := Eval hnf in
  @LGraph close' (Sub (p_in G) p_inP) (Sub (p_out G) p_outP).

End Close.
Arguments close G [_].

Notation "G ≅ H" := (liso G H) (at level 45).
Notation "'Σ' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p%type)) ..))
  (at level 200, x binder, y binder, right associativity).

Lemma in_imfsetT (aT : finType) (rT : choiceType) (f : aT -> rT) (x : aT) : 
  f x \in [fset f x | x in aT].
Proof. by rewrite in_imfset. Qed.

Lemma imfset_inv (aT : finType) (rT : choiceType) (f : aT -> rT) (y : [fset f x | x in aT]) : 
  Σ x : aT, f x = val y.
Admitted.

Section Bij.
Variable (G : finType) (T : choiceType) (g : G -> T).
Hypothesis g_inj : injective g.
Let vset := [fset g x | x in G].
Let f (x : G) : vset := Sub (g x) (in_imfsetT g x).
Let f_inv (x : vset) : G := tag (imfset_inv x).

Lemma can_vset : cancel f f_inv.
Proof. 
  move => x. rewrite /f_inv /f /=. set S := Sub _ _. 
  apply: g_inj. by rewrite (tagged (imfset_inv S)).
Qed.

Lemma can_vset' : cancel f_inv f.
Proof.
  move => [x Hx]. rewrite /f /f_inv. apply: val_inj => /=.
  by rewrite (tagged (imfset_inv [` Hx])).
Qed.

Definition imfset_bij := Bij can_vset can_vset'.
End Bij.

Lemma openK (G : lgraph) : G ≅ close (open G). 
apply: (@Liso G (close (open G)) 
              (imfset_bij (@inj_v_inj G)) 
              (imfset_bij (@inj_e_inj (edge G)))
              (fun => false)
        ) => /=.
- move => v. by rewrite inj_vK.
- move => e. by rewrite inj_eK.
- move => e. apply: val_inj => /=. by rewrite inj_eK.
- move => e. apply: val_inj => /=. by rewrite inj_eK.
- exact: val_inj.
- exact: val_inj.
Defined.

Definition oliso (G H : pre_graph) :=
  Σ (graph_G : is_graph G) (graph_H : is_graph H), close G ≅ close H.

Notation "G ⩭ H" := (oliso G H) (at level 45).
