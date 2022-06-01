Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.

From Coq Require Import
     Relation_Definitions
     RelationClasses
.

Require Import GHC.Base.
Require Import Fix.
Require Import Tactics.Tactics.

Require Import ClassesOfFunctors.FunctorPlus.
Require Import Adverb.Composable.Nondeterministically.

Section EqFplusLaws.

Variable D : (Set -> Set) -> Set -> Set.
Context `{ReifiedPlus -≪ D} `{Functor1 D}.
Context `{Functor (Fix1 D)}.

Variant EqFplusLaws
        (Kr : forall (A : Set), relation (Fix1 D A))
        {A : Set} : relation (Fix1 D A) :=
| EqFplusComm : forall (a b : Fix1 D A),
    EqFplusLaws Kr (fplus a b) (fplus b a)
| EqFplusAssoc : forall (a b c : Fix1 D A),
    EqFplusLaws Kr (fplus (fplus a b) c) (fplus a (fplus b c)).

Global Instance FunctorRel__EqNondeterministically
  : FunctorRel (F:=Fix1 D) (@EqFplusLaws).
constructor. intros. destruct H3; constructor; assumption.
Qed.

End EqFplusLaws.

Section EqFplusLaws_SmartConstructors.

Variable D : (Set -> Set) -> Set -> Set.
Context `{ReifiedPlus -≪ D} `{Functor1 D}.
Context `{Functor (Fix1 D)}.

Variable R : (forall (A : Set), relation (Fix1 D A)) ->
             forall (A : Set), relation (Fix1 D A).

Context `{FunctorRel _ R} `{@EqFplusLaws _ _ _ _  -⋘ R}.

Lemma eqFplusComm : forall {A : Set} (a b : Fix1 D A),
    FixRel R _ (fplus a b) (fplus b a).
Proof. eqConstruct. Qed.

Lemma eqFplusAssoc : forall {A : Set} (a b c : Fix1 D A),
    FixRel R _ (fplus (fplus a b) c) (fplus a (fplus b c)).
Proof. eqConstruct. Qed.

End EqFplusLaws_SmartConstructors.
