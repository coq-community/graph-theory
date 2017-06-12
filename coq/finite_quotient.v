Require Import mathcomp.ssreflect.all_ssreflect.
Local Open Scope quotient_scope.

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


