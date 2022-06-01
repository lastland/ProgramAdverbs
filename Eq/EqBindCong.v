Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.

From Coq Require Import
     Relation_Definitions
     RelationClasses
     Morphisms
.

Require Import GHC.Base.
Require Import Fix.
Require Import Tactics.Tactics.

Require Import Adverb.Composable.Adverb.
Require Import Adverb.Composable.Purely.
Require Import Adverb.Composable.Dynamically.

Require Export Eq.EqBindK.

Section EqBindCong.

  Variable D : (Set -> Set) -> Set -> Set.
  Context `{PurelyAdv -≪ D} `{DynamicallyAdv -≪ D} `{Functor1 D}.

  (* begin eq_bind_cong *)
  Variant EqBindCong
          (Kr : forall (A : Set), relation (Fix1 D A))
          {A : Set} : relation (Fix1 D A) :=
  | EqMBindCong : forall {B : Set} (a b : Fix1 D B) (f g : B -> Fix1 D A),
      Kr _ a b ->
      (forall a, Kr _ (f a) (g a)) ->
      EqBindCong Kr (a >>= f) (b >>= g).
  (* end eq_bind_cong *)

  Global Instance FunctorRel__EqBindCong
    : FunctorRel (F:=Fix1 D) EqBindCong.
  constructor. intros ? ? ? ? ? ? [].
  constructor; auto.
  Qed.

End EqBindCong.

Section EqBindCong_SmartConstructors.

  Variable D : (Set -> Set) -> Set -> Set.
  Context {HP : PurelyAdv -≪ D} {HD : DynamicallyAdv -≪ D} {HF : Functor1 D}.

  Variable R : (forall (A : Set), relation (Fix1 D A)) ->
               forall (A : Set), relation (Fix1 D A).

  Context `{FunctorRel _ R} `{@EqBindCong D HP HD HF -⋘ R}.

  Lemma eqBindCong : forall {A B : Set} (a b : Fix1 D A) (f g : A -> Fix1 D B),
    FixRel R _ a b ->
    (forall a, FixRel R _ (f a) (g a)) ->
    FixRel R _ (a >>= f) (b >>= g).
  Proof. eqConstruct. Qed.

  Global Instance BindProper {A B : Set} :
    Proper (FixRel R A ==>
           @EqDynamicallyK _ R A B ==>
           FixRel R B) op_zgzgze__.
  intros m1 m2 Hm k1 k2 Hk.
  apply eqBindCong; assumption.
  Qed.

  Global Instance CongProper {A : Set}
         `{forall (A : Set), Equivalence (FixRel R A)} :
    Proper (FixRel R A ==>
            FixRel R A ==>
            iff) (FixRel R A).
  intros a1 a2 Ha b1 b2 Hb. split; intros.
  - etransitivity. symmetry. eassumption.
    etransitivity; eassumption.
  - etransitivity. eassumption. symmetry.
    etransitivity. eassumption. symmetry. assumption.
  Qed.

End EqBindCong_SmartConstructors.
