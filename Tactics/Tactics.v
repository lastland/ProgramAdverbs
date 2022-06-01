Require Import Coq.Program.Tactics.

Require Import Fix.

Ltac destruct_match :=
  match goal with
  | |- context[match ?x with _ => _ end] =>
    destruct x
  end.

Ltac solve_obligation_by_destructs :=
  program_simpl; repeat destruct_match; reflexivity.

Ltac eqConstruct :=
  intros; apply inFRel, injRel; try solve [econstructor; eauto].

Ltac destructs :=
  match goal with
  | [H : exists _, _ |- _] => destruct H
  | [H : _ /\ _ |- _] => destruct H
  | [H : _ \/ _ |- _] => destruct H
  end.

Ltac inverts :=
  match goal with
  | [H : inl _ = _ |- _] => inversion H; clear H
  | [H : inr _ = _ |- _] => inversion H; clear H
  end.
