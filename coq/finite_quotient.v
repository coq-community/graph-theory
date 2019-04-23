Require Import Setoid CMorphisms.
Require Import mathcomp.ssreflect.all_ssreflect.
Require Import preliminaries.
Local Open Scope quotient_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs". 

(** [finType] instances for {eq_quot} *)

Section FinEncodingModuloRel.

Variables (D : Type) (C : finType) (CD : C -> D) (DC : D -> C).
Variables (eD : equiv_rel D) (encD : encModRel CD DC eD).
Notation eC := (encoded_equiv encD).

Notation ereprK := (@EquivQuot.ereprK D C CD DC eD encD). 

Fact eq_quot_finMixin : Finite.mixin_of [eqType of {eq_quot encD}].
Proof. apply: CanFinMixin. exact: ereprK. Qed.

Canonical eq_quot_finType := Eval hnf in FinType {eq_quot encD} eq_quot_finMixin.

End FinEncodingModuloRel.

(** wrapper around ssreflect quotients *)

Local Open Scope quotient_scope.

Module Type QUOT.
  Parameter quot: forall T: finType, equiv_rel T -> finType.
  Parameter pi: forall (T: finType) (e: equiv_rel T), T -> quot e.
  Parameter repr: forall (T: finType) (e: equiv_rel T), quot e -> T.
  Parameter reprK: forall (T: finType) (e: equiv_rel T), cancel (@repr _ e) (pi e). 
  Parameter eqquotP: forall (T: finType) (e: equiv_rel T) (x y: T), reflect (pi e x = pi e y) (e x y).
End QUOT.
Module Export quot: QUOT.
Section s.
  Variables (T: finType) (e: equiv_rel T).
  Definition quot: finType := [finType of {eq_quot e}].
  Definition pi (x: T): quot := \pi x.
  Definition repr(x: quot): T := repr x.
  Lemma reprK: cancel repr pi.
  Proof. exact: reprK. Qed.
  Lemma eqquotP (x y : T): reflect (pi x = pi y) (e x y).
  Proof. exact: eqquotP. Qed.
End s.
End quot.
Notation "\pi x" := (pi _ x) (at level 30).
Notation "x = y %[mod e ]" := (pi e x = pi e y).
Notation "x == y %[mod e ]" := (pi e x == pi e y).

Lemma piK (T: finType) (e: equiv_rel T) (x: T): e (repr (pi e x)) x.
Proof. apply /eqquotP. by rewrite reprK. Qed.
Lemma piK' (T: finType) (e: equiv_rel T) (x: T): e x (repr (pi e x)).
Proof. rewrite equiv_sym; apply piK. Qed.

(* TODO: only used once in skeleton ; remove? *)
Lemma eqmodE (T: finType) (e: equiv_rel T) (x y : T): (x == y %[mod e]) = e x y.
Admitted.

(* TODO: only used in extraction_iso ; remove? *)
CoInductive pi_spec (T : finType) (e : equiv_rel T) (x : T) : T -> Type :=
  PiSpec : forall y : T, x = y %[mod e] -> pi_spec e x y.
Lemma piP (T: finType) (e: equiv_rel T) (x: T): pi_spec e x (repr (pi e x)).
Proof. constructor. by rewrite reprK. Qed.

Lemma pi_surj (T : finType) (e : equiv_rel T) : surjective (pi e).
Proof. move => y. exists (repr y). by rewrite reprK. Qed.

Lemma mod_exchange (T : finType) (e1 e2 : equiv_rel T) x y : 
  e1 =2 e2 -> x = y %[mod e2] -> x = y %[mod e1].
Proof. move => E M1. apply/eqquotP. rewrite E. by apply/eqquotP. Qed.

(** various bijections about quotients *)

Section t.
  Variables (S: finType) (e f: equiv_rel S).
  Hypothesis H: e =2 f. 
  Definition quot_same: bij (quot e) (quot f).
    exists
      (fun x => \pi (repr x))
      (fun x => \pi (repr x)).
    abstract by move=>x; rewrite -{2}(reprK x); apply /eqquotP; rewrite H; apply piK. 
    abstract by move=>x; rewrite -{2}(reprK x); apply /eqquotP; rewrite -H; apply piK. 
  Defined.
  Lemma quot_sameE (x: S): quot_same (\pi x) = \pi x.
  Proof. simpl. apply /eqquotP. rewrite -H. apply piK. Qed.
End t.
Global Opaque quot_same. 

Section map_equiv.
  Variables (S T: Type) (h: T -> S) (e: equiv_rel S).
  Definition map_equiv_rel: rel T := fun x y => e (h x) (h y).
  Lemma map_equiv_class: equiv_class_of map_equiv_rel.
  Proof. split => [x|x y|x y z]. apply: equiv_refl. apply: equiv_sym. apply: equiv_trans. Qed.
  Canonical Structure map_equiv := EquivRelPack map_equiv_class.
  Lemma map_equivE x y: map_equiv x y = e (h x) (h y).
  Proof. by []. Qed.
End map_equiv. 

Section b.
  Variables (S T: finType) (h: bij S T) (e: equiv_rel S).
  Definition quot_bij: bij (quot e) (quot (map_equiv h^-1 e)).
    exists
      (fun x => \pi h (repr x))
      (fun x => \pi h^-1 (repr x)).
    abstract by move=>x; rewrite -{2}(reprK x) -{2}(bijK h (repr x));
                        apply /eqquotP; apply: (piK (map_equiv h^-1 e)).
    abstract by move=>x; rewrite -{2}(reprK x); apply /eqquotP;
                        rewrite map_equivE bijK; apply piK. 
  Defined.
  Lemma quot_bijE (x: S): quot_bij (\pi x) = \pi h x.
  Proof. simpl. apply /eqquotP. rewrite map_equivE 2!bijK. apply piK. Qed.
End b.
Global Opaque quot_bij.

Section quot_quot.
  Variables (T: finType) (e: equiv_rel T) (e': equiv_rel (quot e)).
  Definition equiv_comp := map_equiv (pi e) e'.
  Lemma equiv_compE (x y: T): equiv_comp x y = e' (\pi x) (\pi y).
  Proof. apply map_equivE. Qed.
  Lemma equiv_comp_pi (x: T): repr (repr (pi e' (pi e x))) = x %[mod equiv_comp].
  Proof. apply/eqquotP. rewrite /equiv_comp map_equivE reprK. apply: piK. Qed.
  Definition quot_quot: bij (quot e') (quot equiv_comp).
  Proof.
    exists (fun x => \pi repr (repr x)) (fun x => \pi (\pi repr x)).
    abstract by move=>x; rewrite -{2}(reprK x); apply /eqquotP; 
                        rewrite -{2}(reprK (repr x)); apply (piK equiv_comp).
    abstract by move=>x; rewrite equiv_comp_pi; apply reprK. 
  Defined.
  Lemma quot_quotE (x: T): quot_quot (\pi (\pi x)) = \pi x.
  Proof. apply equiv_comp_pi. Qed.
End quot_quot.
Global Opaque quot_quot.

Section quot_id.
  Variables (T: finType) (e: equiv_rel T).
  Hypothesis H: forall x y, e x y -> x=y.
  Definition quot_id: bij (quot e) T.
  Proof.
    exists (@repr _ e) (pi e). apply reprK.
    move=>x. apply H, piK.
  Defined.
  Lemma quot_idE (x: T): quot_id (\pi x) = x.
  Proof. apply H, piK. Qed.
End quot_id.
Global Opaque quot_id.

Section union_quot_l.
  Variables (S T: finType) (e: equiv_rel S).
  Definition union_equiv_l_rel: rel (S+T) :=
    fun x y => match x,y with
               | inl x,inl y => e x y
               | inr x,inr y => x==y
               | _,_ => false
               end.
  Lemma union_equiv_l_class: equiv_class_of union_equiv_l_rel.
  Proof.
    split => [[x|x]|[x|x] [y|y]|[x|x] [y|y] [z|z]]//=.
    apply: equiv_sym. apply: equiv_trans. by move=>/eqP ->. 
  Qed.
  Canonical Structure union_equiv_l := EquivRelPack union_equiv_l_class.
  Definition union_quot_l: bij (quot e + T) (quot union_equiv_l).
  Proof.
    exists
      (fun x => \pi match x with inl x => inl (repr x) | inr x => inr x end)
      (fun x => match repr x with inl x => inl (\pi x) | inr x => inr x end).
    - case => [x|x].
      + generalize (piK union_equiv_l (inl (repr x))).
        case (repr (pi union_equiv_l (inl (repr x))))=> y E//=.
        f_equal. rewrite -(reprK x). by apply /eqquotP.
      + generalize (piK union_equiv_l (inr x)).
        case (repr (pi union_equiv_l (inr x)))=> y /eqP E//=. congruence.
    - move=>x. rewrite -{2}(reprK x).
      case (repr x)=> y//. apply /eqquotP. apply piK.
  Defined.
  Lemma union_quot_lEl (x: S): union_quot_l (inl (\pi x)) = \pi (inl x).
  Proof. simpl. apply /eqquotP. apply piK. Qed.
  Lemma union_quot_lEr (x: T): union_quot_l (inr x) = \pi (inr x).
  Proof. simpl. apply /eqquotP=>//=. Qed.
End union_quot_l.
Global Opaque union_quot_l.

Section union_quot_r.
  Variables (S T: finType) (e: equiv_rel T).
  Definition union_equiv_r: equiv_rel (S+T) := map_equiv sumC (union_equiv_l _ e).
  Definition union_quot_r: bij (S + quot e) (quot union_equiv_r).
  Proof.
    eapply bij_comp. apply bij_sumC.
    eapply bij_comp. apply union_quot_l.
    apply (quot_bij bij_sumC). 
  Defined.
  Lemma union_quot_rEr (x: T): union_quot_r (inr (\pi x)) = \pi (inr x).
  Proof. simpl. by rewrite union_quot_lEl quot_bijE. Qed.
  Lemma union_quot_rEl (x: S): union_quot_r (inl x) = \pi (inl x).
  Proof. simpl. by rewrite union_quot_lEr quot_bijE. Qed.
End union_quot_r.
Global Opaque union_quot_r.

Section quot_union_K.
  Variables (S K: finType) (e: equiv_rel (S+K)) (k: K -> S).
  Hypothesis kh: forall x: K, inr x = inl (k x) %[mod e].
  Definition union_K_equiv: equiv_rel S := map_equiv inl e.
  Definition quot_union_K: bij (quot e) (quot union_K_equiv).
  Proof.
    exists
      (fun x => \pi match repr x with inl x => x | inr x => k x end)
      (fun x => \pi inl (repr x)).
    - move=>x.
      rewrite -{2}(reprK x).
      case (repr x)=>y//=; rewrite ?kh; apply /eqquotP; apply (piK union_K_equiv).
    - move=>x.
      rewrite -{2}(reprK x).
      generalize (piK e (inl (repr x))).
      case (repr (pi e (inl (repr x)))) => y H//=.
        by apply /eqquotP=>//.
        move: H=>/eqquotP H. rewrite kh in H.
        apply /eqquotP. rewrite /=map_equivE. by apply /eqquotP.
  Defined.
  Lemma quot_union_KEl (x: S): quot_union_K (\pi inl x) = \pi x.
  Proof.
    simpl. generalize (piK e (inl x)).
    case (repr (pi e (inl x))) => y H//=.
      by apply /eqquotP=>//.
      move: H=>/eqquotP H. rewrite kh in H.
      apply /eqquotP. rewrite /=map_equivE. by apply /eqquotP.
  Qed.
  Lemma quot_union_KEr (x: K): quot_union_K (\pi inr x) = \pi (k x).
  Proof.
    simpl. generalize (piK e (inr x)).
    case (repr (pi e (inr x))) => y H//=; apply /eqquotP; rewrite /=map_equivE; apply /eqquotP;
    rewrite -!kh; by apply /eqquotP.
  Qed.
End quot_union_K.
Global Opaque quot_union_K.

