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

Require Import Adverb.Composable.Adverb.
Require Import Adverb.Composable.Purely.
Require Import Adverb.Composable.Dynamically.

Section EqBindLaws.

  Variable D : (Set -> Set) -> Set -> Set.
  Context `{PurelyAdv -≪ D} `{DynamicallyAdv -≪ D} `{Functor1 D}.

  Variant EqBindLaws
          (Kr : forall (A : Set), relation (Fix1 D A))
          {A : Set} : relation (Fix1 D A) :=
  | EqBindLeftId : forall {X : Set} (a : X) (b : X -> Fix1 D A),
      EqBindLaws Kr (return_ a >>= b) (b a)
  | EqBindRightId : forall (a : Fix1 D A),
      EqBindLaws Kr (a >>= return_) a
  | EqBindAssoc : forall {X Y : Set}
                    (a : Fix1 D X)
                    (b : X -> Fix1 D Y)
                    (c : Y -> Fix1 D A),
      EqBindLaws Kr ((a >>= b) >>= c) (a >>= (fun x => b x >>= c)).

  Global Instance FunctorRel__EqBindLaws
    : FunctorRel (F:=Fix1 D) EqBindLaws.
  constructor. intros. destruct H3; constructor.
  Qed.

End EqBindLaws.

Section EqBindLaws_SmartConstructors.

  Variable D : (Set -> Set) -> Set -> Set.
  Context `{PurelyAdv -≪ D} `{DynamicallyAdv -≪ D} `{Functor1 D}.

  Variable R : (forall (A : Set), relation (Fix1 D A)) ->
               forall (A : Set), relation (Fix1 D A).

  Context `{FunctorRel _ R} `{@EqBindLaws D _ _ _ -⋘ R}.

  Lemma eqBindLeftId : forall {A B : Set} (a : A) (b : A -> Fix1 D B),
      FixRel R _ (return_ a >>= b) (b a).
  Proof. eqConstruct. Qed.

  Lemma eqBindRightId : forall {A : Set} (a : Fix1 D A),
      FixRel R _ (a >>= return_) a.
  Proof. eqConstruct. Qed.

  Lemma eqBindAssoc : forall {A B C : Set}
                        (a : Fix1 D A) (b : A -> Fix1 D B) (c : B -> Fix1 D C),
      FixRel R _ ((a >>= b ) >>= c) (a >>= (fun x => b x >>= c)).
  Proof. eqConstruct. Qed.

  Lemma PureRet : forall {A : Set} (a : A),
      pure (f:=Fix1 D) a = return_ a.
  Proof. intros; reflexivity. Qed.

End EqBindLaws_SmartConstructors.
