From Coq Require Import
     Relation_Definitions
     RelationClasses
.

Require Import Fix.
Require Import GHC.Base.

Variant RefinesEq {F : Set -> Set}
        (Eq : forall (A : Set), relation (F A))
        (Equiv : forall (A : Set), Equivalence (Eq A))
        (Kr : forall (A : Set), relation (F A))
        {A : Set} : relation (F A) :=
| RefinesEquiv : forall (a b : F A),
    Eq _ a b ->
    RefinesEq Eq Equiv Kr a b.

#[export] Instance FunctorRel__RefinesEq
         {F : Set -> Set} {Eq : forall (A : Set), relation (F A)}
         {Equiv : forall (A : Set), Equivalence (Eq A)} :
  FunctorRel (F:=F) (RefinesEq Eq Equiv).
constructor. intros. destruct H0.
constructor; assumption.
Qed.

Section RefinesEq_SmartConstructors.

  Variable F : Set -> Set.
  Variable R : (forall (A : Set), relation (F A)) ->
               forall (A : Set), relation (F A).

  Variable Eq : (forall (A : Set), relation (F A)).
  Variable EqEquiv : (forall (A : Set), Equivalence (Eq A)).

  Context `{FunctorRel F R} `{RefinesEq Eq EqEquiv -⋘ R}.

  Lemma refinesEq : forall {A : Set} (a b : F A),
      Eq _ a b ->
      FixRel R _ a b.
  Proof.
    intros. apply inFRel, injRel.
    constructor; assumption.
  Qed.

End RefinesEq_SmartConstructors.
