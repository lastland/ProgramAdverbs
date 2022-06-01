From Coq Require Import
     Relation_Definitions
     RelationClasses
.

Require Import GHC.Base.
Require Import Fix.
Require Import Tactics.Tactics.

Variant EqApLaws {F} `{Applicative F}
        (Kr : forall (A : Set), relation (F A))
        {A : Set} : relation (F A) :=
| EqApId : forall (a : F A),
    EqApLaws Kr (pure id <*> a) a
| EqApHomo : forall {X : Set} (f : X -> A) (x : X),
    EqApLaws Kr (pure f <*> pure x) (pure (f x))
| EqApInter : forall {X : Set} (g : F (X -> A)) (x : X),
    EqApLaws Kr (g <*> pure x) (pure (fun f => f x) <*> g)
| EqApComp : forall {X Y : Set} (u : F (Y -> A)) (v : F (X -> Y)) (w : F X),
    EqApLaws Kr (pure op_z2218U__ <*> u <*> v <*> w) (u <*> (v <*> w)).

#[export] Instance FunctorRel__EqApT {F} {HF : Functor F} {HA : Applicative F}
  : FunctorRel (F:=F) (@EqApLaws _ HF HA).
constructor. intros. destruct H0; constructor.
Qed.

Section EqApLaws_SmartConstructors.

  Variable F : Set -> Set.
  Context {HF : Functor F} {HA : Applicative F}.

  Variable R : (forall (A : Set), relation (F A)) ->
               forall (A : Set), relation (F A).

  Context `{FunctorRel F R} `{@EqApLaws _ HF HA -⋘ R}.

  Lemma eqApId : forall {A : Set} (a : F A),
      FixRel R _ (pure id <*> a) a.
  Proof. eqConstruct. Qed.

  Lemma eqApHomomorphism : forall {A B : Set} (f : A -> B) (a : A),
      FixRel R _ (pure f <*> pure a) (pure (f a)).
  Proof. eqConstruct. Qed.

  Lemma eqApInterchange : forall {A B : Set} (g : F (A -> B)) (x : A),
      FixRel R _ (g <*> pure x) (pure (fun f => f x) <*> g).
  Proof. eqConstruct. Qed.

  Lemma eqApComposition : forall {A B C : Set}
                            (u : F (B -> C)) (v : F (A -> B)) (w : F A),
      FixRel R _ (pure op_z2218U__ <*> u <*> v <*> w) (u <*> (v <*> w)).
  Proof. eqConstruct. Qed.

End EqApLaws_SmartConstructors.
