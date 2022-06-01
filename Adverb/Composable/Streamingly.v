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

Require Import Adverb.Composable.Adverb.
Require Import Adverb.Composable.Purely.

Open Scope composable_adverb_scope.

Require Import Tactics.Tactics.

(* begin hide *)
Local Ltac solve :=
  Tactics.program_simplify; Equations.CoreTactics.equations_simpl; try Tactics.program_solve_wf;
  repeat destruct_match; reflexivity.

Local Obligation Tactic := solve.

Variant StreaminglyAdv (K : Set -> Set) (R : Set) : Set :=
| FMap {X : Set} (g : X -> R) (f : K X).

Arguments FMap {_} {_} {_}.

#[export] Program Instance Functor1__StreaminglyAdv : Functor1 StreaminglyAdv :=
  {| fmap1 := fun _ _ _ f a =>
                match a with
                | FMap g a => FMap g (f _ a)
                end
  |}.

Definition fmap_ff {E} {A B : Set} `{StreaminglyAdv -≪ E} `{Functor1 E}
           (f : A -> B) (a : Fix1 E A) : Fix1 E B :=
  @inF1 _ _ _ (inj1 (FMap f a)).

#[export] Instance Functor__FunctorT {E} `{StreaminglyAdv -≪ E} `{Functor1 E} : Functor (Fix1 E) | 0 :=
  fun r k => k {| fmap__      := fun {a} {b} => fmap_ff ;
               op_zlzd____ := fun {a} {b} => fmap_ff ∘ const |}.

(* We don't need [Functor__Dict] here because [Functor] has no dependency. *)
#[export] Instance StreaminglyAdverbSim :
  StreaminglyAdv ⊧ Functor UNDER IdT :=
  {| interpAlg := fun I D _ a =>
                    match a with
                    | FMap f a => @fmap I _ _ _ f a
                    end |}.
