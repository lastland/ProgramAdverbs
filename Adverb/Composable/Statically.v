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

Variant StaticallyAdv (K : Set -> Set) (R : Set) : Set :=
| LiftA2 {X Y : Set} (f : X -> Y -> R)(g : K X) (a : K Y).

Arguments LiftA2 {_} {_} {_} {_}.

#[export] Program Instance Functor1__StaticallyAdv : Functor1 StaticallyAdv :=
  {| fmap1 := fun _ _ _ f a =>
                match a with
                | LiftA2 g a b => LiftA2 g (f _ a) (f _ b)
                end
  |}.

Section SmartConstructors.

  Variable E : (Set -> Set) -> Set -> Set.
  Variable A B C : Set.
  Context `{PurelyAdv -≪ E} `{StaticallyAdv -≪ E} `{Functor1 E}.

  Definition pure_fa (r : A) : Fix1 E A :=
    @inF1 _ _ _ (inj1 (Pure r)).

  Definition liftA2_fa (f : (A -> B -> C)) (a : Fix1 E A) (b : Fix1 E B) : Fix1 E C :=
    @inF1 _ _ _ (inj1 (LiftA2 f a b)).

End SmartConstructors.

Arguments pure_fa {_} {_} {_} {_}.
Arguments liftA2_fa {_} {_} {_} {_} {_} {_}.

Definition fmap_fa {E} {A B : Set} `{PurelyAdv -≪ E} `{StaticallyAdv -≪ E}
           `{Functor1 E} (f : A -> B) (a : Fix1 E A) : Fix1 E B :=
  liftA2_fa id (pure_fa f) a.

#[export] Instance Functor__Statically {E} `{PurelyAdv -≪ E} `{StaticallyAdv -≪ E}
         `{Functor1 E} : Functor (Fix1 E) | 1 :=
  fun r k => k {| fmap__      := fun {a} {b} => fmap_fa ;
               op_zlzd____ := fun {a} {b} => fmap_fa ∘ const |}.

#[export] Program Instance Applicative__Statically {E} `{PurelyAdv -≪ E} `{StaticallyAdv -≪ E} `{Functor1 E}
  : Applicative (Fix1 E) | 0 :=
  fun r k => k {| liftA2__ := fun {a b c} => liftA2_fa ;
               op_zlztzg____ := fun {a b} => liftA2_fa id ;
               op_ztzg____ := fun {a b} fa => liftA2_fa id (id <$ fa) ;
               pure__ := fun {a} => pure_fa |}.

#[export] Instance StaticallyAdverbSim :
  StaticallyAdv ⊧ Applicative__Dict UNDER IdT :=
  {| interpAlg := fun I D _ a =>
                    match a with
                    | LiftA2 f a b => @liftA2 _
                                     (apdict_functor I D)
                                     (apdict_applicative I D)
                                     _ _ _ f a b
                    end |}.
