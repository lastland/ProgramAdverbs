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

Section RefinesBindCong.

  Variable D : (Set -> Set) -> Set -> Set.
  Context `{PurelyAdv -≪ D} `{DynamicallyAdv -≪ D} `{Functor1 D}.

  (* begin eq_bind_cong *)
  Variant RefinesBindCong
          (Kr : forall (A : Set), relation (Fix1 D A))
          {A : Set} : relation (Fix1 D A) :=
  | RefinesMBindCong : forall {B : Set} (a b : Fix1 D B) (f g : B -> Fix1 D A),
      Kr _ a b ->
      (forall a, Kr _ (f a) (g a)) ->
      RefinesBindCong Kr (a >>= f) (b >>= g).
  (* end eq_bind_cong *)

  Global Instance FunctorRel__RefinesBindCong
    : FunctorRel (F:=Fix1 D) RefinesBindCong.
  constructor. intros ? ? ? ? ? ? [].
  constructor; auto.
  Qed.

End RefinesBindCong.

Section RefinesBindCong_SmartConstructors.

  Variable D : (Set -> Set) -> Set -> Set.
  Context `{PurelyAdv -≪ D} `{DynamicallyAdv -≪ D} `{Functor1 D}.

  Variable R : (forall (A : Set), relation (Fix1 D A)) ->
               forall (A : Set), relation (Fix1 D A).

  Context `{FunctorRel _ R} `{@RefinesBindCong D _ _ _ -⋘ R}.

  Lemma eqBindCong : forall {A B : Set} (a b : Fix1 D A) (f g : A -> Fix1 D B),
    FixRel R _ a b ->
    (forall a, FixRel R _ (f a) (g a)) ->
    FixRel R _ (a >>= f) (b >>= g).
  Proof. eqConstruct. Qed.

  Global Instance BindProper {A B : Set} :
    Proper (FixRel R A ==>
           @RefinesDynamicallyK _ R A B ==>
           FixRel R B) op_zgzgze__.
  intros m1 m2 Hm k1 k2 Hk.
  apply eqBindCong; assumption.
  Qed.

  Global Instance CongProper {A : Set}
         `{forall (A : Set), Refinesuivalence (FixRel R A)} :
    Proper (FixRel R A ==>
            FixRel R A ==>
            iff) (FixRel R A).
  intros a1 a2 Ha b1 b2 Hb. split; intros.
  - etransitivity. symmetry. eassumption.
    etransitivity; eassumption.
  - etransitivity. eassumption. symmetry.
    etransitivity. eassumption. symmetry. assumption.
  Qed.

End RefinesBindCong_SmartConstructors.
