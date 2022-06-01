Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.

From Coq Require Import
     Relation_Definitions
     RelationClasses
.

Require Import Fix.
Require Import GHC.Base.

Require Import Adverb.Composable.Repeatedly.
Require Import ClassesOfFunctors.AppKleenePlus.

Section RefinesKleenePlusLaws.

    Variable D : (Set -> Set) -> Set -> Set.
    Context `{ReifiedKleenePlus -≪ D} `{Functor1 D}.
    Context `{Monad (Fix1 D)}.

    Fixpoint seq {A : Set} (a : Fix1 D A) (n : nat) : Fix1 D A :=
      match n with
      | 0 => a
      | S n => a >> @seq _ a n
      end.

    Variant RefinesKleenePlusLaws
            (Kr : forall (A : Set), relation (Fix1 D A))
            {A : Set} : relation (Fix1 D A) :=
    | RefinesSeq : forall (a b : Fix1 D A) n,
        Kr _ a b ->
        RefinesKleenePlusLaws Kr (@seq _ a n) (@kleenePlus _ _ _ _ _ b)
    | RefinesKleenePlus : forall (a b : Fix1 D A),
        Kr _ a (@kleenePlus _ _ _ _ _ b) ->
        RefinesKleenePlusLaws Kr (@kleenePlus _ _ _ _ _ a) (@kleenePlus _ _ _ _ _ b)
    (* TODO: move to a separate data type. *)
    | RefinesKleenePlusCong : forall (a b : Fix1 D A),
        Kr _ a b ->
        RefinesKleenePlusLaws Kr (@kleenePlus _ _ _ _ _ a) (@kleenePlus _ _ _ _ _ b).

    Global Instance FunctorRel__RefinesKleenePlusLaws :
      FunctorRel (F:=Fix1 D) RefinesKleenePlusLaws.
    constructor. intros. destruct H5.
    - constructor; auto.
    - constructor; auto.
    - apply RefinesKleenePlusCong. auto.
    Qed.

End RefinesKleenePlusLaws.

Section RefinesKleenePlusLaws_SmartConstructors.

  Variable D : (Set -> Set) -> Set -> Set.
  Context `{ReifiedKleenePlus -≪ D} `{Functor1 D}.
  Context `{Monad (Fix1 D)}.

  Variable R : (forall (A : Set), relation (Fix1 D A)) ->
               forall (A : Set), relation (Fix1 D A).
  Context `{FunctorRel _ R} `{RefinesKleenePlusLaws -⋘ R}.

  Lemma refinesSeq :
    forall {A : Set} (a b : Fix1 D A) n,
      FixRel R _ a b ->
      FixRel R _ (@seq _ _ _ _ _ a n) (@kleenePlus _ _ _ _ _ b).
  Proof.
    intros. apply inFRel, injRel.
    constructor; assumption.
  Qed.

  Lemma refinesKleenePlus :
    forall {A : Set} (a b : Fix1 D A),
      FixRel R _ a (@kleenePlus _ _ _ _ _ b) ->
      FixRel R _ (@kleenePlus _ _ _ _ _ a) (@kleenePlus _ _ _ _ _ b).
  Proof.
    intros. apply inFRel, injRel.
    constructor; assumption.
  Qed.

  Lemma refinesKleenePlusCong :
    forall {A : Set} (a b : Fix1 D A),
      FixRel R _ a b ->
      FixRel R _ (@kleenePlus _ _ _ _ _ a) (@kleenePlus _ _ _ _ _ b).
  Proof.
    intros. apply inFRel, injRel.
    constructor; assumption.
  Qed.

End RefinesKleenePlusLaws_SmartConstructors.
