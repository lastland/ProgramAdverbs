Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.
Set Universe Polymorphism.

From Coq Require Import
  Relation_Definitions
  RelationClasses
  Psatz
  Morphisms
  FunctionalExtensionality
.

From ClassesOfFunctors Require Import
  DictDerive
  FunctorPlus
  Laws
.

From Transformers Require Export PowerSet.

Require Import Tactics.Tactics.

Require Import GHC.Base.

(** * The [FunctorPlus] transformer based on [PowerSet] *)

Section FunctorPlusTransformer.

  (** [I] is the functor that [PowerSet] transforms. *)
  Variable I : Type -> Type.
  Variable FI : Functor I.

  (** The equivalence relation on [I] and theorems. *)
  Variable EqI : forall (A : Type), relation (I A).
  Variable EqIEq : forall (A : Type), Equivalence (@EqI A).

  (** The refinement relation on [I]. *)
  Variable RefinesI : forall (A : Type), relation (I A).
  Variable RefinesIPreOrder : forall (A : Type), PreOrder (@RefinesI A).

  (** The equivalence relation on [PowerSet I]. *)
  Definition EqPowerSet {A} : relation (PowerSet I A) :=
    fun p q => forall a, p a <-> q a.

  (** An invariance that all [PowerSet I A] satisfies as long as they
      are constructed using functions that maintain the invariance. We
      also show in this section that all functions we define on this
      data type maintain the invariance. *)
  Definition Invariance {A} (p : PowerSet I A) :=
    forall a b, EqI a b -> p a <-> p b.

  (** The refinement relation on [PowerSet I]. *)
  Definition RefinesPowerSet {A} : relation (PowerSet I A) :=
    fun p q =>  forall a, p a -> q a.

  Global Instance Equiv__EqPowerSet {A} : Equivalence (@EqPowerSet A).
  constructor.
  - intros a. unfold EqPowerSet. tauto.
  - intros a b. unfold EqPowerSet. intros. split; apply H.
  - intros a b c. unfold EqPowerSet.
    intros; split.
    + intros. apply H0. apply H. assumption.
    + intros. apply H. apply H0. assumption.
  Qed.

  Global Instance PreOrder__RefinesPowerSet {A} : PreOrder (@RefinesPowerSet A).
  constructor.
  - intros a p q. assumption.
  - intros a b c Hab Hbc.
    unfold RefinesPowerSet in *. intros i Hi.
    specialize (Hab i Hi).  specialize (Hbc i Hab).
    assumption.
  Qed.

  Definition embedPowerSet {A} (a : I A) : PowerSet I A :=
    fun r => EqI r a.

  (** [embedPowerSet] maintains the invariance. *)
  Theorem embedInvariance {A} (a : I A) :
    Invariance (embedPowerSet a).
  Proof.
    intros x y Hxy. unfold embedPowerSet. split.
    - intros <-. symmetry. assumption.
    - intros <-. assumption.
  Qed.

  Definition fmapPowerSet {A B} (f : A -> B) (a : PowerSet I A) : PowerSet I B :=
    fun r => exists a', a a' /\ EqI (fmap f a') r.

  (** [fmapPowerSet] maintains the invariance. *)
  Theorem fmapInvariance {A B} (f : A -> B) (a : PowerSet I A) :
    Invariance (fmapPowerSet f a).
  Proof.
    intros x y Hxy. unfold fmapPowerSet. split.
    - intros (a' & Ha & HEq).
      exists a'. split; try assumption.
      transitivity x; assumption.
    - intros (a' & Ha & HEq).
      exists a'. split; try assumption.
      symmetry in Hxy.
      transitivity y; assumption.
  Qed.

  (** [plusPowerSet] maintains the invariance. *)
  Definition plusPowerSet {A} (a b : PowerSet I A) : PowerSet I A :=
    fun r => a r \/ b r.

  Theorem plusInvariance {A} (a b : PowerSet I A) :
    Invariance a -> Invariance b ->
    Invariance (plusPowerSet a b).
  Proof.
    intros Ha Hb x y Hxy. unfold plusPowerSet. split.
    - destruct 1.
      + specialize (Ha x y Hxy).
        apply Ha in H. tauto.
      + specialize (Hb x y Hxy).
        apply Hb in H. tauto.
    - destruct 1.
      + specialize (Ha x y Hxy).
        apply Ha in H. tauto.
      + specialize (Hb x y Hxy).
        apply Hb in H. tauto.
  Qed.

  Instance Functor__PowerSet__FunctorPlus : Functor (PowerSet I) :=
    fun _ r => r {| fmap__ := fun _ _ => fmapPowerSet ;
                 op_zlzd____ := fun _ _ => fmapPowerSet ∘ const
              |}.

  Instance FunctorPlus__PowerSet : FunctorPlus (PowerSet I) :=
    fun _ r => r {| fplus__ := fun _ => plusPowerSet |}.

  (** * Theorems

      These are useful for proving the soundness of [Nondeterministically]. *)

  Lemma FplusComm : forall {A} (a b : PowerSet I A),
      EqPowerSet (fplus a b) (fplus b a).
  Proof.
    intros ? a b p. unfold fplus; cbn.
    unfold plusPowerSet. intuition.
  Qed.

  Lemma FplusAssoc : forall {A} (a b c : PowerSet I A),
      EqPowerSet (fplus a (fplus b c)) (fplus (fplus a b) c).
  Proof.
    intros ? a b c p. unfold fplus; cbn.
    unfold plusPowerSet. intuition.
  Qed.

  Lemma RefinesLeft : forall {A} (a b : PowerSet I A),
      RefinesPowerSet a (fplus a b).
  Proof.
    intros ? a b p Hp. left. assumption.
  Qed.

  Lemma RefinesRight : forall {A} (a b : PowerSet I A),
      RefinesPowerSet b (fplus a b).
  Proof.
    intros ? a b p Hp. right. assumption.
  Qed.

  Lemma RefinesFplus : forall {A} (a b c : PowerSet I A),
      RefinesPowerSet a c ->
      RefinesPowerSet b c ->
      RefinesPowerSet (fplus a b) c.
  Proof.
    intros. unfold fplus, RefinesPowerSet.
    cbn. unfold plusPowerSet.
    intros. intuition.
  Qed.

End FunctorPlusTransformer.
