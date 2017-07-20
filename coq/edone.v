(* (c) Copyright Christian Doczkal, Saarland University                   *)
(* Distributed under the terms of the CeCILL-B license                    *)

(** * A slightly more powerful done tactic 

We replace the default implementation of [done] by one that uses [eassumption]
rather than [assumption] and also applis the right hand side simplifications for
boolean operations *)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool.

Ltac done := trivial; hnf in |- *; intros;
(
  solve [
    (do !
      [ solve [ trivial | apply : sym_equal; trivial ]
      | discriminate
      | contradiction
      | eassumption
      | split
      | rewrite ?andbT ?andbF ?orbT ?orbF ]
    )
    | case not_locked_false_eq_true; assumption
    | match goal with
        | H:~ _ |- _ => solve [ case H; trivial ]
      end
  ]
).
