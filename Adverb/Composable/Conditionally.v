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
  | SelectBy : forall {X Y : Set} (f : X -> ((Y -> R) + R)),
      K X -> K Y -> ConditionallyAdv K R.

Arguments SelectBy {_}{_}{_}{_}.

#[export] Program Instance Functor1__ConditionallyAdv : Functor1 ConditionallyAdv :=
  {| fmap1 := fun s s0 s1 f x =>
       match x with
       | SelectBy g a b => SelectBy g (f _ a) (f _ b)
       end
  |}.

Section ConditionallyAdv.

Section SmartConstructors.

  Variable E : (Set -> Set) -> Set -> Set.
  Context `{ConditionallyAdv -≪ E} `{PurelyAdv -≪ E} `{StaticallyAdv -≪ E} `{Functor1 E}.

  Definition selectBy {X Y A : Set} (f : X -> ((Y -> A) + A))
    (a : Fix1 E X) (b : Fix1 E Y) :
    Fix1 E A :=
    @inF1 _ _ _ (inj1 (SelectBy f a b)).

  Arguments selectBy {_} {_} {_}.

  Definition select {X Y : Set} : Fix1 E (X + Y) -> Fix1 E (X -> Y) -> Fix1 E Y :=
    selectBy (fun x => match x with
                    | inl x => inl (fun y => y x)
                    | inr y => inr y
                    end).

  Arguments select {_} {_}.

  Definition fmap {X Y : Set} (f : X -> Y) (x : Fix1 E X) : Fix1 E Y :=
    selectBy inl (pure f) x.

  Arguments fmap {_} {_}.

  Definition fmapSum {A B C} (f : A -> B) (a : sum C A) : sum C B :=
  match a with
  | inl c => inl c
  | inr a => inr (f a)
  end.

  Definition branch {X Y A : Set}
    (a : Fix1 E (X + Y)) (b : Fix1 E (X -> A)) (c : Fix1 E (Y -> A)) :
    Fix1 E A :=
    select (select (fmap (fmapSum inl) a) (fmap (fun f a => inr (f a)) b)) c.

  Arguments branch {_} {_} {_}.

  Definition ifS {A} (b : Fix1 E bool) (t e : Fix1 E A) : Fix1 E A :=
    branch (fmap (fun b : bool => if b then inl tt else inr tt) b)
           (fmap (fun a _ => a) t) (fmap (fun a _ => a) e).

  Arguments ifS {_}.

  Definition pand (x y : Fix1 E bool) : Fix1 E bool :=
    ifS x y (pure false).

End SmartConstructors.

End ConditionallyAdv.
