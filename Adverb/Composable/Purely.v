Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.
Set Universe Polymorphism.

From Equations Require Import Equations.

From Coq Require Import
     Relation_Definitions
     RelationClasses
.

Require Import Fix.
Require Import GHC.Base.
Require Import Adverb.Composable.Adverb.
Require Import ClassesOfFunctors.DictDerive.
Require Import ClassesOfFunctors.Laws.

Open Scope composable_adverb_scope.

Require Import Tactics.Tactics.

(* begin hide *)
Local Ltac solve :=
  Tactics.program_simplify; Equations.CoreTactics.equations_simpl; try Tactics.program_solve_wf;
  repeat destruct_match; reflexivity.

Local Obligation Tactic := solve.
(* end hide *)


Variant PurelyAdv (K : Set -> Set) (R : Set) : Set :=
| Pure (r : R).

Arguments Pure {_} {_}.

#[export] Program Instance Functor1__PurelyAdv : Functor1 PurelyAdv :=
  {| fmap1 := fun _ _ _ _ a =>
                match a with
                | Pure a => Pure a
                end
  |}.

#[export] Instance PurelyAdverbSim :
  PurelyAdv ⊧ Applicative__Dict UNDER IdT :=
  {| interpAlg := fun I D _ a =>
                    match a with
                    | Pure r => @pure _
                                     (apdict_functor I D)
                                     (apdict_applicative I D) _ r
                    end |}.
