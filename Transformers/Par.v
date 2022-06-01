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
  AppKleenePlus
  Laws
.

Require Export Transformers.PowerSet.

Require Import Tactics.Tactics.

Require Import GHC.Base.

(** * The [Applicative] transformer based on [PowerSet] *)

Section ParTransformer.

  (** [I] is the applicative functor that [PowerSet] transforms. *)
  Variable I : Type -> Type.
  Variable FI : Functor I.
  Variable AI : Applicative I.

  (** The equivalence relation on [I] and theorems that [I] satisfy
      certain laws. *)
  Variable EqI : forall (A : Type), relation (I A).
  Variable EqIEq : forall (A : Type), Equivalence (@EqI A).
  Variable ALI : @ApplicativeLaws I (@EqI) (@FI) (@AI).
  Variable ACI : @ApplicativeCongruenceLaws I (@EqI) (@FI) (@AI).

  (** The refinement relation on [I]. *)
  Variable RefinesI : forall (A : Type), relation (I A).
  Variable RefinesIPreOrder : forall (A : Type), PreOrder (@RefinesI A).

  Global Instance liftA2Proper :
    forall A B C, Proper (eq ==> @EqI A ==> @EqI B ==> @EqI C) liftA2.
  Proof.
    intros A B C f g -> a1 a2 HEqa b1 b2 HEqb.
    apply liftA2_cong; assumption.
  Qed.

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

  Definition purePowerSet {A} (a : A) : PowerSet I A :=
    fun r => EqI r (pure a).

  (** [purePowerSet] maintains the invariance. *)
  Theorem pureInvariance {A} (a : A) :
    Invariance (purePowerSet a).
  Proof.
    intros x y Hxy. unfold purePowerSet. split.
    - intros <-. symmetry. assumption.
    - intros <-. assumption.
  Qed.

  Definition liftA2Par {A B C}
    (f : A -> B -> C) (a : PowerSet I A) (b : PowerSet I B) : PowerSet I C :=
    fun r => exists a', a a' /\
                  exists b', b b' /\
                          (EqI (liftA2 f a' b') r \/ EqI (liftA2 (flip f) b' a') r).

  (** [liftA2Par] maintains the invariance. *)
  Theorem liftA2ParInvariance {A B C}
    (f : A -> B -> C) (a : PowerSet I A) (b : PowerSet I B) :
    Invariance (liftA2Par f a b).
  Proof.
    intros x y Hxy. unfold liftA2Par. split.
    - intros H0. destruct H0 as (a' & Ha & b' & Hb & HEq). destruct HEq.
      + exists a'. intuition. exists b'. intuition.
        left. transitivity x; assumption.
      + exists a'. intuition. exists b'. intuition.
        right. transitivity x; assumption.
    - intros H0. destruct H0 as (a' & Ha & b' & Hb & HEq). destruct HEq.
      + exists a'. intuition. exists b'. intuition.
        left. transitivity y; try assumption.
        symmetry; assumption.
      + exists a'. intuition. exists b'. intuition.
        right. transitivity y; try assumption.
        symmetry; assumption.
  Qed.

  (** [liftA2Par] is commutative. *)
  Lemma liftA2Par_comm : forall {A B C} (f : A -> B -> C)
                           (a : PowerSet I A) (b : PowerSet I B),
      EqPowerSet (liftA2Par f a b) (liftA2Par (flip f) b a).
  Proof.
    intros. unfold EqPowerSet, liftA2Par; intros.
    split; intros.
    - repeat destructs; subst.
      + exists x0. intuition. exists x. intuition.
      + exists x0. intuition. exists x. intuition.
    - repeat destructs; subst.
      + exists x0. intuition. exists x. intuition.
      + exists x0. intuition. exists x. intuition.
  Qed.

  Definition PowerSetApplicative__AppDict : Applicative__Dict (PowerSet I) :=
    {| liftA2__ := fun _ _ _ => liftA2Par ;
       op_zlztzg____ := fun _ _ => liftA2Par id ;
       op_ztzg____ := fun _ _ => liftA2Par (fun _ => id) ;
       pure__ := fun _ => @purePowerSet _
    |}.

  Instance Functor__PowerSetApplicative : Functor (PowerSet I) :=
    apdict_functor _ PowerSetApplicative__AppDict.

  Instance Applicative__PowerSetApplicative : Applicative (PowerSet I) :=
    apdict_applicative _ PowerSetApplicative__AppDict.

End ParTransformer.

(** We cannot show that all the [PowerSet I A] satisfy the laws we desire (like
    left identity law of applicative functors). This is because an arbitrary
    [PowerSet I A] might not maintain the invariance (the [Invariance] we
    defined in the previous section). Instead of proving that [PowerSet I A] are
    instances of [CommNonAsscoApplicativeLaws] and [ApplicativeCongruenceLaws],
    we show that all [PowerSet I A] that maintain the invariance are instances
    of them. We do that by using a subset type [PowerSetI] defined below. *)
Section CommNonAssocApplicativeLaws.

  (** [PowerSetI] is a subset of [PowerSet] where all elements satisfy the
      invariance defined by [Invariance]. *)
  Definition PowerSetI
    (I : Type -> Type) (EqI : forall A, relation (I A)) (A : Type) :=
    { p : PowerSet I A | Invariance EqI p }.

  Variable I : Type -> Type.
  Variable FI : Functor I.
  Variable AI : Applicative I.

  Variable EqI : forall (A : Type), relation (I A).
  Variable EqIEq : forall (A : Type), Equivalence (@EqI A).
  Variable ALI : @ApplicativeLaws I (@EqI) (@FI) (@AI).
  Variable ACI : @ApplicativeCongruenceLaws I (@EqI) (@FI) (@AI).

  Variable RefinesI : forall (A : Type), relation (I A).
  Variable RefinesIPreOrder : forall (A : Type), PreOrder (@RefinesI A).

  (* The rest are functions refined on [PowerSetI]. *)
  Program Definition EqPowerSetI {A} : relation (PowerSetI I (@EqI) A) :=
    EqPowerSet.

  Global Instance Equiv__EqPowerSetI {A} : Equivalence (@EqPowerSetI A).
  constructor.
  - intros a. unfold EqPowerSetI.
    destruct a. simpl. reflexivity.
  - intros a b. unfold EqPowerSetI. intros. split; apply H.
  - intros a b c. unfold EqPowerSet.
    intros; split.
    + intros. apply H0. apply H. assumption.
    + intros. apply H. apply H0. assumption.
  Qed.

  Program Definition embedPowerSetI {A} : I A -> PowerSetI I (@EqI) A :=
    (@embedPowerSet I (@EqI) A).
  Next Obligation.
    apply embedInvariance. apply (@EqIEq).
  Qed.

  Program Definition purePowerSetI {A} : A -> PowerSetI I (@EqI) A :=
    (@purePowerSet I (@FI) (@AI) (@EqI) A).
  Next Obligation.
    apply pureInvariance. apply (@EqIEq).
  Qed.

  Program Definition liftA2ParI {A B C} :
    (A -> B -> C) ->
    PowerSetI I (@EqI) A -> PowerSetI I (@EqI) B -> PowerSetI I (@EqI) C :=
    (@liftA2Par I (@FI) (@AI) (@EqI) A B C).
  Next Obligation.
    apply liftA2ParInvariance. apply (@EqIEq).
  Qed.

  Definition PowerSetIApplicative__AppDict :
    Applicative__Dict (PowerSetI I (@EqI)) :=
    {| liftA2__ := fun _ _ _ => liftA2ParI ;
       op_zlztzg____ := fun _ _ => liftA2ParI id ;
       op_ztzg____ := fun _ _ => liftA2ParI (fun _ => id) ;
       pure__ := fun _ => purePowerSetI
    |}.

  Global Instance Functor__PowerSetIApplicative : Functor (PowerSetI I (@EqI)) :=
    apdict_functor _ PowerSetIApplicative__AppDict.

  Global Instance Applicative__PowerSetIApplicative :
    Applicative (PowerSetI I (@EqI)) :=
    apdict_applicative _ PowerSetIApplicative__AppDict.

  (** * Core theorems. *)

  (** Lemma 3.7 *)
  Global Instance CommNonAssocApplicativeLaws__PowerSetApplicative :
    @CommNonAssocApplicativeLaws (PowerSetI I (@EqI)) (@EqPowerSetI) _ _.
  constructor.
  - (* liftA2_left_id *)
    intros. cbn. split.
    + cbn. unfold liftA2Par, purePowerSet.
      destruct b as (b & HIb).
      intros (a' & Eqa' & b' & Hb & HEq). destruct HEq.
      * rewrite Eqa' in H. rewrite (@liftA2_left_id _ _ _ _ ALI) in H.
        simpl. simpl in Hb. specialize (HIb b' a0 H).
        apply HIb. assumption.
      * rewrite Eqa' in H. rewrite (@liftA2_right_id _ _ _ _ ALI) in H.
        simpl. simpl in Hb. specialize (HIb b' a0 H).
        apply HIb. assumption.
    + cbn. unfold liftA2Par, purePowerSet.
      destruct b as (b & HIb). simpl. intros Hb.
      exists (pure a). split; [reflexivity|].
      exists a0. intuition. left. apply (@liftA2_left_id _ _ _ _ ALI).
  - (* liftA2_right_id *)
    intros. cbn. split.
    + cbn. unfold liftA2Par, purePowerSet.
      destruct a as (a & HIa).
      intros (a' & Ha & b' & Eqb' & HEq). destruct HEq.
      * rewrite Eqb' in H. rewrite (@liftA2_right_id _ _ _ _ ALI) in H.
        simpl. simpl in Ha. specialize (HIa a' a0 H).
        apply HIa. assumption.
      * rewrite Eqb' in H. rewrite (@liftA2_left_id _ _ _ _ ALI) in H.
        simpl. simpl in Ha. specialize (HIa a' a0 H).
        apply HIa. assumption.
    + cbn. unfold liftA2Par, purePowerSet.
      destruct a as (a & HIa). simpl. intros Ha.
      exists a0. intuition. exists (pure b). split; [reflexivity|].
      left. apply (@liftA2_right_id _ _ _ _ ALI).
  - (* commutativity *)
    intros. unfold EqPowerSetI.
    destruct a as [a HIa]. destruct b as [b HIb].
    simpl. apply (@liftA2Par_comm _ _ _ _).
  Qed.

  (** Lemma 3.7 *)
  Global Instance ApplicativeCongruenceLaws__PowerSetApplicative :
    @ApplicativeCongruenceLaws (PowerSetI I (@EqI)) (@EqPowerSetI) _ _.
  constructor. intros.
  destruct a1 as [a1 HIa1].
  destruct a2 as [a2 HIa2].
  destruct b1 as [b1 HIb1].
  destruct b2 as [b2 HIb2].
  unfold EqPowerSetI in *. simpl in *. split.
  - intros Hlift. destruct Hlift as (a' & Ha' & b' & Hb' & HEq).
    destruct HEq.
    + exists a'; split; [apply H; assumption|].
      exists b'; split; [apply H0; assumption|].
      tauto.
    + exists a'; split; [apply H; assumption|].
      exists b'; split; [apply H0; assumption|].
      tauto.
  - intros Hlift. destruct Hlift as (a' & Ha' & b' & Hb' & HEq).
    destruct HEq.
    + exists a'; split; [apply H; assumption|].
      exists b'; split; [apply H0; assumption|].
      tauto.
    + exists a'; split; [apply H; assumption|].
      exists b'; split; [apply H0; assumption|].
      tauto.
  Qed.
End CommNonAssocApplicativeLaws.
