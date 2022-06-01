From Coq Require Import
     Relation_Definitions
     RelationClasses
.

Require Import GHC.Base.
Require Import Fix.
Require Import Tactics.Tactics.

Variant EqLiftA2Laws {F : Set -> Set} `{Applicative F}
        (Kr : forall (A : Set), relation (F A))
        {A : Set} : relation (F A) :=
| EqLiftA2LeftId : forall {X : Set} (a : X) (b : F A),
    EqLiftA2Laws Kr (liftA2 (fun _ => id) (pure a) b) b
| EqLiftA2RightId : forall {X : Set} (a : F A) (b : X),
    EqLiftA2Laws Kr (liftA2 (fun x _ => x) a (pure b)) a
| EqLiftA2Assoc :  forall {X Y Z : Set} a b c (f : X -> Y -> Z -> A) g,
    (forall x y z, f x y z = g y z x) ->
    EqLiftA2Laws Kr (liftA2 id (liftA2 f a b) c)
                    (liftA2 (fun a b => b a) a (liftA2 g b c))
| EqLiftA2Natural : forall {X Y Z T P : Set} a b c
                      p (q : X -> Y -> T) f (g : Y -> Z -> P),
    (forall x y z, p (q x y) z = f x (g y z)) ->
    EqLiftA2Laws Kr (liftA2 p (liftA2 q a b) c)
                    (liftA2 f a (liftA2 g b c)).

#[export] Instance FunctorRel__EqStatically {F} {HF : Functor F} {HA : Applicative F}
  : FunctorRel (F:=F) (@EqLiftA2Laws _ HF HA).
constructor. intros. destruct H0; constructor; assumption.
Qed.

Section EqLiftA2Laws_SmartConstructors.

  Variable F : Set -> Set.
  Context {HF : Functor F} {HA : Applicative F}.

  Variable R : (forall (A : Set), relation (F A)) ->
               forall (A : Set), relation (F A).

  Context `{FunctorRel F R} `{@EqLiftA2Laws _ HF HA -⋘ R}.

  Lemma eqLiftA2LeftId : forall {A B : Set} (a : A) (b : F B),
      FixRel R _ (liftA2 (fun _ => id) (pure a) b) b.
  Proof. eqConstruct. Qed.

  Lemma eqLiftA2RightId : forall {A B : Set} (a : F A) (b : B),
      FixRel R _ (liftA2 (fun x _ => x) a (pure b)) a.
  Proof. eqConstruct. Qed.

  Lemma eqLiftA2Assoc : forall {A B C D : Set}
                          (a : F A) (b : F B) (c : F C)
                          (f : A -> B -> C -> D) g,
      (forall x y z, f x y z = g y z x) ->
      FixRel R _
             (liftA2 id (liftA2 f a b) c)
             (liftA2 (fun a b => b a) a (liftA2 g b c)).
  Proof. eqConstruct. Qed.

  Lemma eqLiftA2Natural : forall {A B C X Y Z : Set}
                            (a : F A) (b : F B) (c : F C)
                            (p : X -> C -> Z) (q : A -> B -> X)
                            (f : A -> Y -> Z) (g : B -> C -> Y),
      (forall x y z, p (q x y) z = f x (g y z)) ->
      FixRel R _
             (liftA2 p (liftA2 q a b) c)
             (liftA2 f a (liftA2 g b c)).
  Proof. eqConstruct. Qed.

End EqLiftA2Laws_SmartConstructors.
