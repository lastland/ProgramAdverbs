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
Require Import Adverb.Adverb.
Require Import ClassesOfFunctors.FunctorPlus.
Require Import ClassesOfFunctors.DictDerive.
Require Import ClassesOfFunctors.Laws.

Require Import Transformers.FunctorPlus.

Open Scope adverb_scope.

(** * NondeterministicallyAdv. *)

(* begin nondeterministically_adv *)
Inductive ReifiedPlus (E : Type -> Type) (R : Type) : Type :=
| EmbedN (e : E R) : ReifiedPlus E R
| Plus (a b : ReifiedPlus E R) : ReifiedPlus E R.
(* end nondeterministically_adv *)

Definition embed {E A} : E A -> ReifiedPlus E A := EmbedN.

Definition plus {E A} :
  ReifiedPlus E A ->
  ReifiedPlus E A ->
  ReifiedPlus E A :=
  Plus.

(** * Adverb Simulation *)

Definition interpNondetermistically {E I : Type -> Type}
  {D : FunctorPlus__Dict I}
  {EqI : forall A, relation (I A)} {A : Type}
  (interpE: forall (A : Type), E A -> I A) :=
  let fix go (n : ReifiedPlus E A) : PowerSet I A :=
    match n with
    | EmbedN e => embedPowerSet _ EqI (interpE _ e)
    | Plus a b => plusPowerSet (go a) (go b)
    end
  in go.

#[global] Instance ReifiedPlusSim :
  ReifiedPlus ⊧ FunctorPlus__Dict UNDER PowerSet :=
  {| interp := @interpNondetermistically |}.

Declare Scope nondeterministically_scope.

Reserved Notation "a ≅ b" (at level 42).

Inductive NondeterministicallyBisim {E A} : relation (ReifiedPlus E A) :=
| nondeterministically_congruence :
    forall a1 a2 b1 b2,
      a1 ≅ a2 -> b1 ≅ b2 -> plus a1 b1 ≅ plus a2 b2
| nondeterministically_comm :
  forall a b, plus a b ≅ plus b a
| nondeterministically_assoc :
  forall a b c, plus a (plus b c) ≅ plus (plus a b) c
| nondeterministically_refl : forall a, a ≅ a
| nondeterministically_sym : forall a b, a ≅ b -> b ≅ a
| nondeterministically_trans : forall a b c, a ≅ b -> b ≅ c -> a ≅ c
where "a ≅ b" := (NondeterministicallyBisim a b) : nondeterministically_scope.

Reserved Notation "a ⊆ b" (at level 42).

Inductive NondeterministicallyRefines {E A} : relation (ReifiedPlus E A) :=
| nondeterministically_eq :
  forall a b, a ≅ b -> a ⊆ b
| nondeterministically_choice :
  forall a b c, a ⊆ c -> b ⊆ c -> plus a b ⊆ c
| nondeterministically_left :
  forall a b, a ⊆ plus a b
| nondeterministically_right :
  forall a b, b ⊆ plus a b
| nondeterministically_refines_trans : forall a b c, a ⊆ b -> b ⊆ c -> a ⊆ c
where "a ⊆ b" := (NondeterministicallyRefines a b) : nondeterministically_scope.

Global Program Instance NondetermisticallyAdverb : Adverb ReifiedPlus :=
  {| Bisim := fun _ _ => NondeterministicallyBisim ;
     Refines := fun _ _ => NondeterministicallyRefines
  |}.
Next Obligation.
  constructor.
  - intros a. constructor.
  - intros a b. constructor. assumption.
  - intros a b c ? ?. econstructor; eassumption.
Qed.
Next Obligation.
  constructor.
  - intros a. apply nondeterministically_eq.
    constructor.
  - intros a b c ? ?. econstructor; eassumption.
Qed.

Theorem soundness_of_nondeterministically_eq :
  forall {E I : Type -> Type} {A : Type}
    {EqI : forall (A : Type), relation (I A) } `{forall A, Equivalence (EqI A) }
    {D : Functor I} {D' : FunctorPlus__Dict I}
    {_ : @FunctorLaws I EqI D}
    (interpE : forall A, E A -> I A) (x y : ReifiedPlus E A)
    (Hbisim : x ≅ y),
    EqPowerSet (interp (C0:=D')(EqI:=EqI) interpE x) (interp (C0:=D')(EqI:=EqI) interpE y).
Proof.
  intros. induction Hbisim.
  - unfold interp. cbn.
    unfold plusPowerSet, EqPowerSet. intros a. split.
    + destruct 1.
      * left. apply IHHbisim1. assumption.
      * right. apply IHHbisim2. assumption.
    + destruct 1.
      * left. apply IHHbisim1. assumption.
      * right. apply IHHbisim2. assumption.
  - unfold interp. cbn.
    pose proof (@FplusComm I _ EqI) as Hcomm.
    unfold fplus in Hcomm. cbn in Hcomm. apply Hcomm.
  - unfold interp. cbn.
    pose proof (@FplusAssoc I _ EqI) as Hassoc.
    unfold fplus in Hassoc. cbn in Hassoc. apply Hassoc.
  - reflexivity.
  - symmetry; assumption.
  - etransitivity; eassumption.
Qed.

Theorem soundness_of_nondeterministically_refines :
  forall {E I : Type -> Type} {A : Type}
    {EqI : forall (A : Type), relation (I A) } `{forall A, Equivalence (EqI A) }
    {D : Functor I} {D' : FunctorPlus__Dict I}
    {_ : @FunctorLaws I EqI D}
    (interpE : forall A, E A -> I A) (x y : ReifiedPlus E A)
    (Hrefines : x ⊆ y),
    RefinesPowerSet (interp (C0:=D')(EqI:=EqI) interpE x) (interp (C0:=D')(EqI:=EqI) interpE y).
Proof.
  intros. induction Hrefines.
  - unfold interp. cbn.
    pose proof (@soundness_of_nondeterministically_eq E I A EqI H D D' H0
                  interpE a b H1).
    unfold EqPowerSet in H2. unfold RefinesPowerSet. intros.
    apply H2. assumption.
  - unfold interp. cbn.
    pose proof (@RefinesFplus I _ EqI) as Hchoice.
    apply Hchoice; assumption.
  - unfold interp. cbn.
    pose proof (@RefinesLeft I _ EqI) as Hleft.
    apply Hleft; assumption.
  - unfold interp. cbn.
    pose proof (@RefinesRight I _ EqI) as Hright.
    apply Hright; assumption.
  - unfold RefinesPowerSet in *. intuition.
Qed.
