From Coq Require Import
     Relation_Definitions
     RelationClasses
.

Require Import Fix.
Require Import GHC.Base.

Variant RefinesOrder {F : Set -> Set}
        (Kr : forall (A : Set), relation (F A))
        {A : Set} : relation (F A) :=
| RefinesRefl : forall (a : F A), RefinesOrder Kr a a
| RefinesTrans : forall (a b c : F A),
    Kr _ a b -> Kr _ b c -> RefinesOrder Kr a c.

#[export] Instance FunctorRel__RefinesOrder {F : Set -> Set} :
  FunctorRel (F:=F) RefinesOrder.
constructor. intros. destruct H0.
- apply RefinesRefl.
- eapply RefinesTrans; apply H; eassumption.
Qed.

Section RefinesOrder_SmartConstructors.

  Variable F : Set -> Set.
  Variable R : (forall (A : Set), relation (F A)) ->
               forall (A : Set), relation (F A).

  Context `{FunctorRel F R} `{RefinesOrder -⋘ R}.

  Lemma refinesRefl : forall {A : Set} (a : F A),
      FixRel R _ a a.
  Proof.
    intros. apply inFRel, injRel.
    apply RefinesRefl.
  Qed.

  Lemma refinesTrans : forall {A : Set} (a b c : F A),
      FixRel R _ a b -> FixRel R _ b c -> FixRel R _ a c.
  Proof.
    intros. apply inFRel, injRel.
    eapply RefinesTrans; eassumption.
  Qed.

  Global Instance PreOrder_RefinesOrder {A : Set} : PreOrder (FixRel R A).
  Proof.
    constructor.
    - intros a. apply refinesRefl.
    - intros a b c. apply refinesTrans.
  Qed.

End RefinesOrder_SmartConstructors.
