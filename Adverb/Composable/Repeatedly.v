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
Require Import ClassesOfFunctors.DictDerive.
Require Import ClassesOfFunctors.Laws.
Require Import ClassesOfFunctors.AppKleenePlus.

Require Import Adverb.Composable.Adverb.

Open Scope composable_adverb_scope.

Require Import Tactics.Tactics.

(* begin hide *)
Local Ltac solve :=
  Tactics.program_simplify; Equations.CoreTactics.equations_simpl; try Tactics.program_solve_wf;
  repeat destruct_match; reflexivity.

Local Obligation Tactic := solve.
(* end hide *)

(* begin repeatedly_adv *)
Variant ReifiedKleenePlus (K : Set -> Set) (R : Set) : Set :=
| KPlus : K R -> ReifiedKleenePlus K R.
(* end repeatedly_adv *)

Arguments KPlus {_} {_}.

Program Instance Functor1__ReifiedKleenePlus : Functor1 ReifiedKleenePlus :=
  {| fmap1 := fun _ _ _ f a =>
                match a with
                | KPlus a => KPlus (f _ a)
                end
  |}.

Section Instances.

  Variable D : (Set -> Set) -> Set -> Set.

  Context `{ReifiedKleenePlus -≪ D} `{Functor1 D}.

  (** TODO: adverb simulation. *)
  Local Definition kplus {A : Set} (a : Fix1 D A) : Fix1 D A :=
    @inF1 _ _ _ (inj1 (KPlus a)).

  Context `{Functor (Fix1 D)}.
  Context `{Applicative (Fix1 D)}.

  Global Instance FunctorKleenePlus__Repeatedly : AppKleenePlus (Fix1 D) :=
    fun _ k => k {| kleenePlus__ := fun _ => kplus |}.

End Instances.
