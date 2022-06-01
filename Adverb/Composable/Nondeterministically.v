Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.
Set Universe Polymorphism.

From Coq Require Import
     Relation_Definitions
     RelationClasses
.

Require Import Fix.
Require Import GHC.Base.
Require Import ClassesOfFunctors.DictDerive.
Require Import ClassesOfFunctors.Laws.
Require Import ClassesOfFunctors.FunctorPlus.

Require Import Adverb.Composable.Adverb.
Require Import Adverb.Composable.Streamingly.
Require Import Adverb.Composable.Statically.
Require Import Adverb.Composable.Dynamically.

Open Scope composable_adverb_scope.

Require Import Tactics.Tactics.

(* begin hide *)
Local Ltac solve :=
  Tactics.program_simplify; Equations.CoreTactics.equations_simpl; try Tactics.program_solve_wf;
  repeat destruct_match; reflexivity.

Local Obligation Tactic := solve.
(* end hide *)

(* begin nondeterministically_adv *)
Variant ReifiedPlus (K : Set -> Set) (R : Set) : Set :=
| Plus : K R -> K R -> ReifiedPlus K R.
(* end nondeterministically_adv *)

Arguments Plus {_} {_}.

#[export] Program Instance Functor1__ReifiedPlus :
  Functor1 ReifiedPlus :=
  {| fmap1 := fun _ _ _ f a =>
                match a with
                | Plus a b => Plus (f _ a) (f _ b)
                end
  |}.

Section Instances.

  Variable D : (Set -> Set) -> Set -> Set.

  Context `{ReifiedPlus -≪ D} `{Functor1 D}.

  Section WithFunctor.

    Context `{Functor (Fix1 D)}.

    Global Instance FunctorPlus__Nondeterministically : FunctorPlus (Fix1 D) :=
      fun _ k => k {| fplus__ := fun _ a b => @inF1 _ _ _ (inj1 (Plus a b)) |}.

  End WithFunctor.

  Instance ReifiedPluserbSim :
    ReifiedPlus ⊧ FunctorPlus__Dict UNDER IdT :=
    {| interpAlg := fun I D _ a =>
                      match a with
                      | Plus a b => @fplus__ I D _ a b
                      end |}.
End Instances.
