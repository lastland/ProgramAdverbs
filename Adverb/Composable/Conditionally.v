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
Require Import Adverb.Composable.Statically.

Open Scope composable_adverb_scope.

Require Import Tactics.Tactics.

(* begin hide *)
Local Ltac solve :=
  Tactics.program_simplify; Equations.CoreTactics.equations_simpl; try Tactics.program_solve_wf;
  repeat destruct_match; reflexivity.

Local Obligation Tactic := solve.

Variant ConditionallyAdv (K : Set -> Set) (R : Set) : Set :=
| Branch : forall {X Y : Set}, K (sum X Y) -> K (X -> R) -> K (Y -> R)
    -> ConditionallyAdv K R.

Arguments Branch {_}{_}{_}{_}.

#[export] Program Instance Functor1__ConditionallyAdv : Functor1 ConditionallyAdv :=
  {| fmap1 := fun s s0 s1 f x =>
       match x with
       | Branch g a b => Branch (f _ g) (f _ a) (f _ b)
       end
  |}.

Section ConditionallyAdv.

Section SmartConstructors.

  Variable E : (Set -> Set) -> Set -> Set.
  Variable A B C : Set.
  Context `{ConditionallyAdv -≪ E} `{PurelyAdv -≪ E} `{StaticallyAdv -≪ E} `{Functor1 E}.

  Definition branch_fa {X Y A : Set} (a : Fix1 E (sum X Y)) (b:Fix1 E (X -> A)) (c:Fix1 E (Y -> A)) :
    Fix1 E A :=
    @inF1 _ _ _ (inj1 (Branch a b c)).

Arguments branch_fa {_} {_}{_}.

  Definition ifS {A} (b : Fix1 E bool) (t e : Fix1 E A) : Fix1 E A :=
    branch_fa (fmap (fun b : bool => if b then inl tt else inr tt) b)
           (fmap (fun a _ => a) t) (fmap (fun a _ => a) e).

Arguments ifS {_}.

  Definition pand (x y : Fix1 E bool) : Fix1 E bool :=
    ifS x y (pure false).


End SmartConstructors.

End ConditionallyAdv.
