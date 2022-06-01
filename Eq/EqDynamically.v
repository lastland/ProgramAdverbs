From Coq Require Import
     Relation_Definitions
     RelationClasses
.

Require Import GHC.Base.
Require Import Fix.
Require Import Tactics.Tactics.

Variant EqBindLaws {F} `{Monad F}
        (Kr : forall (A : Set), relation (F A))
        {A : Set} : relation (F A) :=
| EqBindLeftId : forall {X : Set} (a : X) (b : X -> F A),
    EqBindLaws Kr (return_ a >>= b) (b a)
| EqBindRightId : forall (a : F A),
    EqBindLaws Kr (a >>= return_) a
| EqBindAssco : forall {X Y : Set} (a : F X) (b : X -> F Y) (c : Y -> F A),
    EqBindLaws Kr ((a >>= b) >>= c) (a >>= (fun x => b x >>= c)).

Instance FunctorRel__EqBindLaws {F}
         {HF : Functor F} {HA : Applicative F} {HM : Monad F}
  : FunctorRel (F:=F) (@EqBindLaws _ HF HA HM).
constructor. intros. destruct H0; constructor.
Qed.

Section EqBindLaws_SmartConstructors.

  Variable F : Set -> Set.
  Context {HF : Functor F} {HA : Applicative F} {HM : Monad F}.

  Variable R : (forall (A : Set), relation (F A)) ->
               forall (A : Set), relation (F A).

  Context `{FunctorRel F R} `{@EqBindLaws _ HF HA HM -⋘ R}.

  Lemma eqBindLeftId : forall {A B : Set} (a : A) (b : A -> F B),
      FixRel R _ (return_ a >>= b) (b a).
  Proof. eqConstruct. Qed.

  Lemma eqBindRightId : forall {A : Set} (a : F A),
      FixRel R _ (a >>= return_) a.
  Proof. eqConstruct. Qed.

  Lemma eqBindAssoc : forall {A B C : Set}
                        (a : F A) (b : A -> F B) (c : B -> F C),
      FixRel R _ ((a >>= b ) >>= c) (a >>= (fun x => b x >>= c)).
  Proof. eqConstruct. Qed.


End EqBindLaws_SmartConstructors.
