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

Variant DynamicallyAdv (K : Set -> Set) (R : Set) : Set :=
| Bind {X : Set} (m : K X) (g : X -> K R).

Arguments Bind {_} {_} {_}.

#[export] Program Instance Functor1__DynamicallyAdv : Functor1 DynamicallyAdv :=
  {| fmap1 := fun _ _ _ f m =>
         match m with
         | Bind m g => Bind (f _ m) (fun x => f _ (g x))
         end
  |}.


Section SmartConstructors.

  Variable E : (Set -> Set) -> Set -> Set.
  Variable A B : Set.
  Context `{PurelyAdv -≪ E} `{DynamicallyAdv -≪ E} `{Functor1 E}.

  Definition return_fm (r : A) : Fix1 E A :=
    @inF1 _ _ _ (inj1 (Pure r)).

  Definition bind_fm (m : Fix1 E A) (g : A -> Fix1 E B) : Fix1 E B :=
    @inF1 _ _ _ (inj1 (Bind m g)).

End SmartConstructors.

Arguments return_fm {_} {_} {_} {_}.
Arguments bind_fm  {_} {_} {_} {_} {_}.

Definition MonadDict_Dynamically {E : (Set -> Set) -> Set -> Set}
  `{PurelyAdv -≪ E} `{DynamicallyAdv -≪ E} `{Functor1 E} :
  Monad__Dict (Fix1 E) :=
  {| op_zgzg____ := fun {a} {b} m k => bind_fm m (fun _ => k) ;
     op_zgzgze____ := fun {a} {b} => bind_fm ;
     return___ := fun {a} => return_fm |}.

Global Instance Functor__DynamicallyAdv {E}
         `{PurelyAdv -≪ E} `{DynamicallyAdv -≪ E} `{Functor1 E}
  : Functor (Fix1 E) | 2 := monaddict_functor (Fix1 E) MonadDict_Dynamically.

Global Instance Applicative__DynamicallyAdv {E}
         `{PurelyAdv -≪ E} `{DynamicallyAdv -≪ E} `{Functor1 E}
  : Applicative (Fix1 E) | 1 := monaddict_applicative (Fix1 E) MonadDict_Dynamically.

Global Instance Monad__DynamicallyAdv {E}
         `{PurelyAdv -≪ E} `{DynamicallyAdv -≪ E} `{Functor1 E}
  : Monad (Fix1 E) | 0 := monaddict_monad (Fix1 E) MonadDict_Dynamically.

#[global] Instance DynamicallyAdvSim :
  DynamicallyAdv ⊧ Monad__Dict UNDER IdT :=
  {| interpAlg := fun I D _ a =>
                    match a with
                    | Bind m k => @op_zgzgze__ _
                                     (monaddict_functor I D)
                                     (monaddict_applicative I D)
                                     (monaddict_monad I D)
                                     _ _ m k
                    end |}.
