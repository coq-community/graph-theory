(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)

(** * A slightly more powerful done tactic 

We replace the default implementation of [done] by one that
- tries setoid reflexivity
- uses [eassumption] rather than [assumption]
- applies the right hand side simplifications for Boolean operations 
*)

Require Import Setoid Morphisms.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool.

Ltac done := trivial; hnf in |- *; intros;
(
  solve [
    (do !
      [ reflexivity
      | solve [ trivial | apply : sym_equal; trivial ]
      | discriminate
      | contradiction
      | split
      | apply/andP;split
      | rewrite ?andbT ?andbF ?orbT ?orbF ]
    )
    | case not_locked_false_eq_true; assumption
    | match goal with
        | H:~ _ |- _ => solve [ case H; trivial ]
      end
  ]
).
