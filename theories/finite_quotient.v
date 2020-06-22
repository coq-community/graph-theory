Require Import Setoid CMorphisms.
Require Import mathcomp.ssreflect.all_ssreflect.
Require Import preliminaries bij.
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
  Definition quot: finType := [finType of {eq_quot e}]. (* TODO: avoid clones? (under module abstraction anyway *)
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

Lemma eqmodE (T: finType) (e: equiv_rel T) (x y : T): (x == y %[mod e]) = e x y.
by apply/eqP/idP => /(eqquotP e). Qed.

(* TODO: only used in extraction_iso ; remove? *)
CoInductive pi_spec (T : finType) (e : equiv_rel T) (x : T) : T -> Type :=
  PiSpec : forall y : T, x = y %[mod e] -> pi_spec e x y.
Lemma piP (T: finType) (e: equiv_rel T) (x: T): pi_spec e x (repr (pi e x)).
Proof. constructor. by rewrite reprK. Qed.

Lemma pi_surj (T : finType) (e : equiv_rel T) : forall x, x \in codom (pi e).
Proof. move => y. by rewrite -[y]reprK codom_f. Qed.

(** Lifting a function between finite types to a function between quotients *)

Section QuotFun.
Variables (T1 T2 : finType) (e1 : equiv_rel T1) (e2 : equiv_rel T2) (h1 : T1 -> T2).
Definition quot_fun (x : quot e1) : quot e2 := \pi (h1 (repr x)).
End QuotFun.
Arguments quot_fun [T1 T2 e1 e2].

Lemma quot_fun_can (T1 T2 : finType) (e1 : equiv_rel T1) (e2 : equiv_rel T2) (h1 : T1 -> T2) (h2 : T2 -> T1) :
  {homo h2 : x y / x = y %[mod e2] >-> x = y %[mod e1]} ->
  (forall x, h2 (h1 x) = x %[mod e1]) ->
  @cancel (quot e2) (quot e1) (quot_fun h1) (quot_fun h2).
Proof.
  move => h2_hom h1_can x.
  rewrite /quot_fun -{2}[x]reprK -[\pi (repr x)]h1_can.
  apply: h2_hom. by rewrite reprK.
Qed.

(** Turning a bijection up to equivalence into a bijection on quotients *)
Section QuotBij.
  Variables (T1 T2 : finType) (e1 : equiv_rel T1) (e2 : equiv_rel T2).
  Variables (h : T1 -> T2) (h_inv : T2 -> T1).

  (** All 4 assumptions are necessary *)
  Hypothesis h_homo : {homo h : x y / x = y %[mod e1] >-> x = y %[mod e2]}.
  Hypothesis h_inv_homo : {homo h_inv : x y / x = y %[mod e2] >-> x = y %[mod e1]}. 

  Hypothesis h_can : forall x, h_inv (h x) = x %[mod e1].
  Hypothesis h_inv_can : forall x, h (h_inv x) = x %[mod e2].

  Definition bij_quot : bij (quot e1) (quot e2).
  Proof. exists (quot_fun h) (quot_fun h_inv); abstract exact: quot_fun_can. Defined.

  Lemma bij_quotE (x: T1): bij_quot (\pi x) = \pi h x.
  Proof. simpl. apply: h_homo. by rewrite reprK. Qed.
  
  Lemma bij_quotE' (x: T2): bij_quot^-1 (\pi x) = \pi h_inv x.
  Proof. simpl. apply: h_inv_homo. by rewrite reprK. Qed.
End QuotBij.
Global Opaque bij_quot.

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
  Proof. apply/eqquotP; rewrite -H; exact: piK. Qed.
  Lemma quot_sameE' (x: S): quot_same^-1 (\pi x) = \pi x.
  Proof. apply/eqquotP; rewrite H; exact: piK. Qed.
End t.
Global Opaque quot_same. 

Definition kernel {A B} (f: A -> B): A -> A -> Prop := fun x y => f x = f y.
Definition kernelb A (B : eqType) (f : A -> B) := [rel x y | f x == f y].

Lemma kernelP A (B : eqType) (f : A -> B) x y : reflect (kernel f x y) (kernelb f x y).
Proof. exact: (iffP eqP). Qed.

Lemma kernel_equivalence A (B : eqType) (f : A -> B) : equiv_class_of (kernelb f).
Proof. by split => [x|x y|x y z] //= => /eqP->/eqP->. Qed.

Section quot_kernel.
 Context {A: finType} {B: Type}.
 Variables (r: equiv_rel A) (f: A -> B) (f': B -> A).
 Hypothesis Hr: forall x y, reflect (kernel f x y) (r x y).
 Hypothesis Hf: cancel f' f.
 Lemma surj_repr_pi x: f (@repr _ r (\pi x)) = f x.
 Proof. by move:(piK r x)=>/Hr. Qed.
 Lemma quot_kernel_can: cancel (fun c => f (@repr _ r c)) (fun b => \pi f' b).
 Proof. intro. rewrite -{2}(reprK x); apply /eqquotP. by apply/Hr. Qed.
 Lemma quot_kernel_can': cancel (fun b => \pi f' b) (fun c => f (@repr _ r c)).
 Proof. intro. by rewrite surj_repr_pi. Qed.
 Definition quot_kernel: bij (quot r) B := Bij quot_kernel_can quot_kernel_can'.
 Lemma quot_kernelE x: quot_kernel (\pi x) = f x.
 Proof. exact: surj_repr_pi. Qed.
 Lemma quot_kernelE' x: quot_kernel^-1 x = \pi f' x.
 Proof. by []. Qed.
End quot_kernel.
Global Opaque quot_kernel.

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
  Lemma quot_bijE' (x: T): quot_bij^-1 (\pi x) = \pi h^-1 x.
  Proof.  apply/eqquotP. rewrite -map_equivE. apply piK. Qed.
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
  Lemma union_quot_lE' (x: S+T):
    union_quot_l^-1 (\pi x) =
    match x with inl y => inl (\pi y) | inr y => inr y end.
  Proof.
    case x=>y.
    by rewrite -(union_quot_lEl y) bijK. 
    by rewrite -(union_quot_lEr y) bijK. 
  Qed.
End union_quot_l.
Global Opaque union_quot_l.

Section union_quot_r.
  (* unused for now *)
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

Definition sum_left {A B} (k: B -> A): A+B -> A :=
  fun x => match x with inl x => x | inr x => k x end.
Section quot_union_K.
  Variables (S K: finType) (e: equiv_rel (S+K)) (k: K -> S).
  Hypothesis kh: forall x: K, inr x = inl (k x) %[mod e].
  Definition union_K_equiv: equiv_rel S := map_equiv inl e.
  Definition quot_union_K: bij (quot e) (quot union_K_equiv).
  Proof.
    exists
      (fun x => \pi (sum_left k (repr x)))
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
  Lemma quot_union_KE (x: S+K): quot_union_K (\pi x) = \pi (sum_left k x).
  Proof.
    simpl. generalize (piK e x).
    case (repr (pi e x)); case x => z y H/=. 
      by apply /eqquotP.
      move: H=>/eqquotP H. rewrite kh in H.
      apply /eqquotP. rewrite /=map_equivE. by apply /eqquotP.
      all: apply /eqquotP; rewrite /=map_equivE; apply /eqquotP;
        rewrite -!kh; by apply /eqquotP.
  Qed.
End quot_union_K.
Global Opaque quot_union_K.

(** Bijections between [sig U + sig V] and [sig (U :|: V)]. We handle
both the case where [U] and [V] are disjoint and the case where we
have a quotient on [sig U + sig V] identifying the elements occurring
both in [U :&: V]. *)

(* TODO: Better naming conventions *)

Arguments Sub : simpl never.

Section sig_sum_bij.
Variables (T : finType) (U V : {set T}).
Notation sig S := ({ x : T | x \in S}) (only parsing).

Lemma union_bij_proofL x : x \in U -> x \in U :|: V.
Proof. apply/subsetP. exact: subsetUl. Qed.

Lemma union_bij_proofR x : x \in V -> x \in U :|: V.
Proof. apply/subsetP. exact: subsetUr. Qed.

Definition merge_union_fwd (x : sig U + sig V) : sig (U :|: V) :=
  match x with 
  | inl x => Sub (val x) (union_bij_proofL (valP x))
  | inr x => Sub (val x) (union_bij_proofR (valP x))
  end.

Lemma setU_dec x : x \in U :|: V -> ((x \in U) + (x \notin U)*(x \in V))%type.
Proof. case E : (x \in U); last rewrite !inE E; by [left|right]. Qed.

Definition merge_union_bwd (x : sig (U :|: V)) : sig U + sig V :=
  match setU_dec (valP x) with 
  | inl p => inl (Sub (val x) p) 
  | inr p => inr (Sub (val x) p.2) 
  end.

Inductive merge_union_bwd_spec : sig (U :|: V) -> sig U + sig V ->  Type :=
| merge_union_bwdL x (inU : x \in U) (inUV : x \in U :|: V) : 
    merge_union_bwd_spec (Sub x inUV) (inl (Sub x inU))
| merge_union_bwdR x (inV : x \in V) (inUV : x \in U :|: V) : 
    x \notin U -> merge_union_bwd_spec (Sub x inUV) (inr (Sub x inV)).

Lemma merge_union_bwdP x : merge_union_bwd_spec x (merge_union_bwd x).
Proof.
  rewrite /merge_union_bwd. 
  case: (setU_dec _) => p.
  - rewrite {1}[x](_ : x = Sub (val x) (valP x)). exact: merge_union_bwdL. 
    by rewrite valK'.
  - rewrite {1}[x](_ : x = Sub (val x) (valP x)). apply: merge_union_bwdR. 
    by rewrite p.  by rewrite valK'.
Qed.

Definition merge_union_bwdEl x (p : x \in U :|: V) (inU : x \in U) : 
  merge_union_bwd (Sub x p) = inl (Sub x inU).
Proof.
  rewrite /merge_union_bwd. case: (setU_dec _) => p'. 
  - rewrite /=. congr inl. exact: val_inj.
  - exfalso. move: p'. rewrite /= inU. by case.
Qed.
Arguments merge_union_bwdEl [x p].

Definition merge_union_bwdEr x (p : x \in U :|: V) (inV : x \in V) : 
  x \notin U -> 
  merge_union_bwd (Sub x p) = inr (Sub x inV).
Proof.
  move => xNU. rewrite /merge_union_bwd. case: (setU_dec _) => p'. 
  - exfalso. move: p'. by rewrite /= (negbTE xNU). 
  - rewrite /=. congr inr. exact: val_inj.
Qed.
Arguments merge_union_bwdEr [x p].

Hint Extern 0 (is_true (sval _ \in _)) => exact: valP : core.
Hint Extern 0 (is_true (val _ \in _)) => exact: valP : core.

Section Disjoint.
  Hypothesis disUV : [disjoint U & V].

  Lemma merge_disjoint_union_can : cancel merge_union_fwd merge_union_bwd.
  Proof. 
    move => [x|x] /=. 
    - by rewrite merge_union_bwdEl // valK'.
    - by rewrite merge_union_bwdEr ?valK' // (disjointFl disUV).
  Qed.
  
  Lemma merge_disjoint_union_can' : cancel merge_union_bwd merge_union_fwd.
  Proof. move => x. case: merge_union_bwdP => //= {x} x *; exact: val_inj. Qed.

  Definition merge_disjoint_union := Bij merge_disjoint_union_can merge_disjoint_union_can'.

End Disjoint.

Section NonDisjoint.
  Variables (e : equiv_rel (sig U + sig V)).
  Definition merge_union_rel := map_equiv merge_union_bwd e.

  Hypothesis eqvI : forall x (inU : x \in U) (inV : x \in V), 
      inl (Sub x inU) = inr (Sub x inV) %[mod e].

  Lemma merge_union_can x : merge_union_bwd (merge_union_fwd x) = x %[mod e].
  Proof.
    case: x => /= => x. 
    - by rewrite merge_union_bwdEl valK'.
    - case: (boolP (val x \in U)) => H. rewrite (merge_union_bwdEl H). 
      + case: x H => x p H. exact: eqvI.
      + by rewrite (merge_union_bwdEr _ H) // valK'.
  Qed.

  Lemma merge_union_can' x : merge_union_fwd (merge_union_bwd x) = x %[mod merge_union_rel].
  Proof. case: merge_union_bwdP => {x} *; congr pi; exact: val_inj. Qed.

  Lemma merge_union_fwd_hom : 
    {homo merge_union_fwd : x y / x = y %[mod e] >-> x = y %[mod merge_union_rel]}.
  Proof.
    move => x y H. apply/eqquotP. rewrite map_equivE. apply/eqquotP. 
    by rewrite !merge_union_can.
  Qed.

  Lemma merge_union_bwd_hom : 
    {homo merge_union_bwd : x y / x = y %[mod merge_union_rel] >-> x = y %[mod e]}.
  Proof. move => x y /eqquotP. rewrite map_equivE. by move/eqquotP. Qed.

  Definition merge_union : bij (quot e) (quot merge_union_rel) := 
    bij_quot merge_union_fwd_hom merge_union_bwd_hom merge_union_can merge_union_can'.

  Lemma merge_unionE x: merge_union (\pi x) = \pi merge_union_fwd x.
  Proof. exact: bij_quotE. Qed.
End NonDisjoint.

End sig_sum_bij.
Global Opaque merge_union.
