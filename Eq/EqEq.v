From Coq Require Import
     Relation_Definitions
     RelationClasses
.

Require Import Fix.
Require Import GHC.Base.

Variant EqEq {F : Set -> Set}
        (Kr : forall (A : Set), relation (F A))
        {A : Set} : relation (F A) :=
| EqRefl : forall (a : F A), EqEq Kr a a
| EqSym  : forall (a b : F A), Kr _ a b -> EqEq Kr b a
| EqTrans : forall (a b c : F A), Kr _ a b -> Kr _ b c -> EqEq Kr a c.

#[export] Instance FunctorRel__EqEq {F : Set -> Set} : FunctorRel (F:=F) EqEq.
constructor. intros. destruct H0.
- apply EqRefl.
- apply EqSym. auto.
- eapply EqTrans; apply H; eassumption.
Qed.

Section EqEq_SmartConstructors.

  Variable F : Set -> Set.
  Variable R : (forall (A : Set), relation (F A)) ->
               forall (A : Set), relation (F A).

  Context `{FunctorRel F R} `{EqEq -⋘ R}.

  Lemma eqEq : forall {A : Set} (a : F A),
      FixRel R _ a a.
  Proof.
    intros. apply inFRel, injRel.
    apply EqRefl.
  Qed.

  Lemma eqSym : forall {A : Set} (a b : F A),
      FixRel R _ a b -> FixRel R _ b a.
  Proof.
    intros. apply inFRel, injRel.
    apply EqSym. assumption.
  Qed.

  Lemma eqTrans : forall {A : Set} (a b c : F A),
      FixRel R _ a b -> FixRel R _ b c -> FixRel R _ a c.
  Proof.
    intros. apply inFRel, injRel.
    eapply EqTrans; eassumption.
  Qed.

  Global Instance Equivalence_EqEq {A : Set} : Equivalence (FixRel R A).
  Proof.
    constructor.
    - intros a. apply eqEq.
    - intros a b. apply eqSym.
    - intros a b c. apply eqTrans.
  Qed.

End EqEq_SmartConstructors.
