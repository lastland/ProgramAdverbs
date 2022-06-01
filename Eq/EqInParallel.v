From Coq Require Import
     Relation_Definitions
     RelationClasses
.

Require Import GHC.Base.
Require Import Fix.


Variant EqInParallel {F} `{Applicative F}
        (Kr : forall (A : Set), relation (F A))
        {A : Set} : relation (F A) :=
| EqLiftA2 : forall {X Y} (a : F X) (b : F Y) f,
    EqInParallel Kr (liftA2 f a b) (liftA2 (flip f) b a).

Global Instance FunctorRel__EqInParallel {F : Set -> Set} `{Applicative F}
  : FunctorRel (F:=F) EqInParallel.
constructor. intros. destruct H2. apply EqLiftA2.
Qed.

Section EqInParallel_SmartConstructors.

  Variable F : Set -> Set.
  Variable R : (forall (A : Set), relation (F A)) ->
               forall (A : Set), relation (F A).
  Context {HF : Functor F} {HA : Applicative F}.

  Context `{FunctorRel F R} `{@EqInParallel F HF HA -⋘ R}.

  Lemma eqLiftA2 : forall {A B C : Set} (f : A -> B -> C)
                     (a : F A) (b : F B),
      FixRel R _ (liftA2 f a b) (liftA2 (flip f) b a).
  Proof.
    intros. apply inFRel, injRel.
    apply @EqLiftA2.
  Qed.

End EqInParallel_SmartConstructors.
