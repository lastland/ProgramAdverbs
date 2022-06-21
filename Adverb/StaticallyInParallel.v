Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.
Set Universe Polymorphism.

From Coq Require Import
     Relation_Definitions
     RelationClasses
     Morphisms
.

Require Import Fix.
Require Import GHC.Base.
Require Import Adverb.Adverb.
Require Import ClassesOfFunctors.DictDerive.
Require Import ClassesOfFunctors.Laws.

Require Import Transformers.Par.

Open Scope adverbI_scope.

(** * StaticallyInParallel. *)

(** The adverb data type of [StaticallyInParallel] is just [ReifiedApp] from
[Statically]. *)
Require Import Adverb.Statically.

Definition interpA
  {E I : Type -> Type} `{Applicative I}
  {EqI : forall (A : Type), relation (I A)}
  {EqIEq : forall (A : Type), Equivalence (EqI A)}
  {A : Type}
  (interpE : forall A, E A -> I A) :=
  let fix go {A : Type} (t : ReifiedApp E A) : PowerSetI I EqI A :=
    match t with
    | EmbedA e => embedPowerSetI EqIEq (interpE _ e)
    | Pure a => pure a
    | LiftA2 f a b => liftA2 f (go a) (go b)
    end
  in @go A.

(** * The adverb simulation. *)
Global Instance StaticallyInParallelAdverbSimI :
  ReifiedApp ⊫ Applicative__Dict UNDER PowerSetI :=
  {| interpI := fun _ I D =>
                 @interpA _ _ (apdict_functor I D) (apdict_applicative I D)
  |}.

Declare Scope staticallyInParallel_scope.

Reserved Notation "a ≅ b" (at level 42).

Inductive StaticallyInParallelBisim {E A} : relation (ReifiedApp E A) :=
| staticallyInParallel_congruence :
    forall {X Y} a1 a2 b1 b2 (f : X -> Y -> A),
      a1 ≅ a2 -> b1 ≅ b2 -> liftA2 f a1 b1 ≅ liftA2 f a2 b2
| staticallyInParallel_left_id :
    forall {X} (a : X) (b : ReifiedApp E A),
      liftA2 (fun _ => id) (pure a) b ≅ b
| staticallyInParallel_right_id :
    forall {X} (a : ReifiedApp E A) (b : X),
      liftA2 (fun x _ => x) a (pure b) ≅ a
| staticallyInParallel_comm :
    forall {X Y} a b (f : X -> Y -> A),
      liftA2 f a b ≅ liftA2 (flip f) b a
| staticallyInParallel_refl : forall a, a ≅ a
| staticallyInParallel_sym : forall a b, a ≅ b -> b ≅ a
| staticallyInParallel_trans : forall a b c, a ≅ b -> b ≅ c -> a ≅ c
where "a ≅ b" := (StaticallyInParallelBisim a b) : staticallyInParallel_scope.

Global Program Instance ReifiedApperb : Adverb ReifiedApp :=
  {| Bisim := fun _ _ => StaticallyInParallelBisim ;
     Refines := fun _ _ => StaticallyInParallelBisim
  |}.
Next Obligation.
  constructor.
  - intros a. constructor.
  - intros a b. constructor. assumption.
  - intros a b c ? ?. econstructor; eassumption.
Qed.
Next Obligation.
  constructor.
  - intros a. constructor.
  - intros a b c ? ?. econstructor; eassumption.
Qed.

(* begin staticallyInParallel_soundness *)
Theorem soundness_of_staticallyInParallel :
  forall {E I : Type -> Type} {A : Type}
    {EqI : forall (A : Type), relation (I A) }
    {EqIEq : forall A, Equivalence (EqI A) }
    {D : Applicative__Dict I}
    {_ : @ApplicativeLaws I EqI (apdict_functor _ D) (apdict_applicative _ D)}
    {_ : @ApplicativeCongruenceLaws I EqI (apdict_functor _ D) (apdict_applicative _ D)}
    (interpE : forall A, E A -> I A) (x y : ReifiedApp E A),
    (* The theorem states that [≅] is an under-approximation of
       [EqPowerSetI]. *)
    x ≅ y ->
    EqPowerSetI (interpI (C0:=D) interpE x) (interpI (C0:=D) interpE y).
(* end staticallyInParallel_soundness *)
Proof.
  intros until y. induction 1.
  - unfold interp. cbn.
    pose proof (@liftA2_cong (PowerSetI I EqI) (@EqPowerSetI I EqI)
                  (@Functor__PowerSetIApplicative I
                     (apdict_functor _ D) (apdict_applicative _ D)
                     EqI EqIEq)
                  (@Applicative__PowerSetIApplicative I
                     (apdict_functor _ D) (apdict_applicative _ D)
                     EqI EqIEq) _) as Hcong.
    apply Hcong; assumption.
  - unfold interp. cbn.
    pose proof (@comm_left_id (PowerSetI I EqI) (@EqPowerSetI I EqI)
                  (@Functor__PowerSetIApplicative I
                     (apdict_functor _ D) (apdict_applicative _ D)
                     EqI EqIEq)
                  (@Applicative__PowerSetIApplicative I
                     (apdict_functor _ D) (apdict_applicative _ D)
                     EqI EqIEq)
                  (@CommNonAssocApplicativeLaws__PowerSetApplicative I
                     (apdict_functor _ D) (apdict_applicative _ D)
                     EqI EqIEq _ _)) as Hid.
    apply Hid.
  - unfold interp. cbn.
    pose proof (@comm_right_id (PowerSetI I EqI) (@EqPowerSetI I EqI)
                  (@Functor__PowerSetIApplicative I
                     (apdict_functor _ D) (apdict_applicative _ D)
                     EqI EqIEq)
                  (@Applicative__PowerSetIApplicative I
                     (apdict_functor _ D) (apdict_applicative _ D)
                     EqI EqIEq)
                  (@CommNonAssocApplicativeLaws__PowerSetApplicative I
                     (apdict_functor _ D) (apdict_applicative _ D)
                     EqI EqIEq _ _)) as Hid.
    apply Hid.
  - unfold interp. cbn.
    pose proof (@commutativity (PowerSetI I EqI) (@EqPowerSetI I EqI)
                  (@Functor__PowerSetIApplicative I
                     (apdict_functor _ D) (apdict_applicative _ D)
                     EqI EqIEq)
                  (@Applicative__PowerSetIApplicative I
                     (apdict_functor _ D) (apdict_applicative _ D)
                     EqI EqIEq)
                  (@CommNonAssocApplicativeLaws__PowerSetApplicative I
                     (apdict_functor _ D) (apdict_applicative _ D)
                     EqI EqIEq _ _)) as Hcomm.
    apply Hcomm.
  - unfold interp. cbn. reflexivity.
  - unfold interp. cbn. symmetry. assumption.
  - unfold interp. cbn. etransitivity; eassumption.
Qed.
