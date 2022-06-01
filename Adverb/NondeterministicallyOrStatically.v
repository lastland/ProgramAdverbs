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
Require Import PretendTypeClasses.Monad.
Require Import Adverb.Adverb.
Require Import Eq.EqEq.
Require Import Eq.EqApCong.
Require Import Eq.EqInParallel.

(** * NondeterministicallyAdv. *)

(* begin nondeterministically_adv *)
Inductive NonDeterministicallyOrStaticallyAdv (E : Type -> Type) :
  Type -> Type :=
| EmbedN {R} (e : E R) : NonDeterministicallyOrStaticallyAdv E R
| Pure {R} : R -> NonDeterministicallyOrStaticallyAdv E R
| Choice {X Y R : Type} (f : X + Y -> R)
         (a : NonDeterministicallyOrStaticallyAdv E X)
         (b : NonDeterministicallyOrStaticallyAdv E Y) :
    NonDeterministicallyOrStaticallyAdv E R
| LiftA2 {X Y R : Type} (f : X -> Y -> R)
         (a : NonDeterministicallyOrStaticallyAdv E X)
         (b : NonDeterministicallyOrStaticallyAdv E Y) :
    NonDeterministicallyOrStaticallyAdv E R.

Definition embedN {E A} : E A -> NonDeterministicallyOrStaticallyAdv E A
  := EmbedN.

Definition pureN {E A} : A -> NonDeterministicallyOrStaticallyAdv E A
  := Pure.

Definition choiceN {E A B C} :
  (A + B -> C) ->
  NonDeterministicallyOrStaticallyAdv E A ->
  NonDeterministicallyOrStaticallyAdv E B ->
  NonDeterministicallyOrStaticallyAdv E C :=
  Choice.

Definition liftA2N {E A B C} :
  (A -> B -> C) ->
  NonDeterministicallyOrStaticallyAdv E A ->
  NonDeterministicallyOrStaticallyAdv E B ->
  NonDeterministicallyOrStaticallyAdv E C :=
  LiftA2.

Definition fmapN {E A B}
           (f : A -> B)
           (a : NonDeterministicallyOrStaticallyAdv E A) :
  NonDeterministicallyOrStaticallyAdv E B :=
  liftA2N id (pureN f) a.


Definition alternate {E A}
           (a b : NonDeterministicallyOrStaticallyAdv E A) :
  NonDeterministicallyOrStaticallyAdv E A :=
  choiceN (fun s => match s with
                | inl a => a
                | inr a => a
                end) a b.
(* end nondeterministically_adv *)

Class Alternative (F : Type -> Type) `{Applicative F} :=
  { alt {A} : F A -> F A -> F A}.

Fixpoint interpS {E F : Type -> Type} `{Alternative F} {A : Type}
         (interpE : forall A, E A -> F A)
         (t : NonDeterministicallyOrStaticallyAdv E A) : F A :=
  match t with
  | EmbedN e => interpE _ e
  | Pure a => pure a
  | LiftA2 f a b => liftA2 f (interpS interpE a) (interpS interpE b)
  | Choice f a b => alt (fmap (fun t => f (inl t)) (interpS interpE a))
                       (fmap (fun t => f (inr t)) (interpS interpE b))
  end.
