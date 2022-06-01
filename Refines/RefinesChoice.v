Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.

From Coq Require Import
     Relation_Definitions
     RelationClasses
.

Require Import Fix.
Require Import GHC.Base.

Require Import ClassesOfFunctors.FunctorPlus.
Require Import Adverb.Composable.Nondeterministically.

Section RefinesFplusLaws.

    Variable D : (Set -> Set) -> Set -> Set.
    Context `{ReifiedPlus -≪ D} `{Functor1 D}.
    Context `{Functor (Fix1 D)}.

    Variant RefinesFplusLaws
            (Kr : forall (A : Set), relation (Fix1 D A))
            {A : Set} : relation (Fix1 D A) :=
    | RefinesFplusL : forall (a b : Fix1 D A),
        RefinesFplusLaws Kr a (fplus a b)
    | RefinesFplusR : forall (a b : Fix1 D A),
        RefinesFplusLaws Kr b (fplus a b)
    | RefinesFplus : forall (a b c : Fix1 D A),
        Kr _ a c ->
        Kr _ b c ->
        RefinesFplusLaws Kr (fplus a b) c.

    Global Instance FunctorRel__RefinesFplusLaws :
      FunctorRel (F:=Fix1 D) RefinesFplusLaws.
    constructor. intros.
    destruct H3; constructor; auto.
    Qed.

End RefinesFplusLaws.

Section RefinesFplusLaws_SmartConstructors.

  Variable D : (Set -> Set) -> Set -> Set.
  Context `{ReifiedPlus -≪ D} `{Functor1 D}.
  Context `{Functor (Fix1 D)}.

  Variable R : (forall (A : Set), relation (Fix1 D A)) ->
               forall (A : Set), relation (Fix1 D A).
  Context `{FunctorRel _ R} `{RefinesFplusLaws -⋘ R}.

  Lemma refinesFplusL :
    forall {A : Set} (a b : Fix1 D A),
      FixRel R _ a (fplus a b).
  Proof.
    intros. apply inFRel, injRel.
    constructor; assumption.
  Qed.

  Lemma refinesFplusR :
    forall {A : Set} (a b : Fix1 D A),
      FixRel R _ b (fplus a b).
  Proof.
    intros. apply inFRel, injRel.
    constructor; assumption.
  Qed.

  Lemma refinesFplus :
    forall {A : Set} (a b c : Fix1 D A),
      FixRel R _ a c ->
      FixRel R _ b c ->
      FixRel R _ (fplus a b) c.
  Proof.
    intros. apply inFRel, injRel.
    constructor; assumption.
  Qed.

End RefinesFplusLaws_SmartConstructors.
