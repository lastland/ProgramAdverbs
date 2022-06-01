Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.

From Coq Require Import
     Relation_Definitions
     RelationClasses
     Morphisms
.

Require Import GHC.Base.
Require Import Fix.
Require Import Tactics.Tactics.

Require Import Adverb.Composable.Adverb.
Require Import Adverb.Composable.Purely.
Require Import Adverb.Composable.Dynamically.

Section EqBindK.

  Variable D : (Set -> Set) -> Set -> Set.
  Context `{PurelyAdv -≪ D} `{DynamicallyAdv -≪ D} `{Functor1 D}.

  Definition DynamicallyK {A B : Set} := A -> Fix1 D B.

  Variable R : (forall (A : Set), relation (Fix1 D A)) ->
               forall (A : Set), relation (Fix1 D A).

  Definition EqDynamicallyK (A B : Set) :
      relation (DynamicallyK) :=
    fun (x y : A -> Fix1 D B) => forall (a : A), FixRel R _ (x a) (y a).

  Global Instance OrderEqDynamicallyK {A B : Set}
         `{forall (A : Set), PreOrder (FixRel R A)} :
    PreOrder (@EqDynamicallyK A B).
  Proof.
    constructor.
    - intros x ?. reflexivity.
    - intros x y z Hxy Hyz ?.
      etransitivity; auto.
  Qed.

  Global Instance EquivEqDynamicallyK {A B : Set}
         `{forall (A : Set), Equivalence (FixRel R A)} :
    Equivalence (@EqDynamicallyK A B).
  Proof.
    constructor.
    - intros x ?. reflexivity.
    - intros x y Hxy ?. symmetry. apply Hxy.
    - intros x y z Hxy Hyz ?.
      etransitivity; auto.
  Qed.

End EqBindK.
