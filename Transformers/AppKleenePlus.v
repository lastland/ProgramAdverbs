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

From Transformers Require Export PowerSet.

Require Import Tactics.Tactics.

Require Import GHC.Base.

(** * The [AppKleenePlus] transformer based on [PowerSet] *)

Section AppKleenePlusTransformer.

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

  Definition liftA2PowerSet {A B C} (f : A -> B -> C)
    (a : PowerSet I A) (b : PowerSet I B) : PowerSet I C :=
    fun r => exists a' b', a a' /\ b b' /\ (EqI (liftA2 f a' b') r).

  (** [liftA2PowerSet] maintains the invariance. *)
  Theorem liftA2Invariance {A B C} (f : A -> B -> C)
    (a : PowerSet I A) (b : PowerSet I B) :
    Invariance (liftA2PowerSet f a b).
  Proof.
    intros x y Hxy. unfold liftA2PowerSet. split.
    - intros (a' & b' & Ha & Hb & HEq).
      exists a'. exists b'. intuition. transitivity x; assumption.
    - intros (a' & b' & Ha & Hb & HEq).
      exists a'. exists b'. intuition. transitivity y.
      + assumption.
      + symmetry. assumption.
  Qed.

  Definition seqPowerSet {A B}
    (a : PowerSet I A) (b : PowerSet I B) : PowerSet I B :=
    liftA2PowerSet (fun _ => id) a b.

  (** [seqPowerSet] maintains the invariance. *)
  Theorem seqInvariance {A B}
    (a : PowerSet I A) (b : PowerSet I B) :
    Invariance (seqPowerSet a b).
  Proof.
    unfold seqPowerSet.
    exact (@liftA2Invariance _ _ _ (fun _ : A => id) a b).
  Qed.

  Fixpoint repeatPowerSet {A} (a : PowerSet I A) (n : nat) : PowerSet I A :=
    match n with
    | 0 => a
    | S n => seqPowerSet a (repeatPowerSet a n)
    end.

  (** [repeatPowerSet] maintains the invariance. *)
  Theorem repeatInvariance {A} (a : PowerSet I A) (n : nat) :
    Invariance a ->
    Invariance (repeatPowerSet a n).
  Proof.
    intro HI. induction n.
    - cbn. assumption.
    - cbn. apply (@seqInvariance _ _ a (repeatPowerSet a n)).
  Qed.

  Definition kplusPowerSet {A} (a : PowerSet I A) : PowerSet I A :=
    fun r => exists n, repeatPowerSet a n r.

  (** [kplusPowerSet] maintains the invariance. *)
  Theorem kplusInvariance {A} (a : PowerSet I A) :
    Invariance a ->
    Invariance (kplusPowerSet a).
  Proof.
    intros HI x y Hxy. unfold kplusPowerSet. split.
    - intros (n & Hr). exists n.
      pose proof (@repeatInvariance _ a n HI x y Hxy) as Ha.
      tauto.
    - intros (n & Hr). exists n.
      pose proof (@repeatInvariance _ a n HI x y Hxy) as Ha.
      tauto.
  Qed.

  Definition PowerSetAppKleenePlusApp__Dicts : Applicative__Dict (PowerSet I) :=
    {| liftA2__ := fun _ _ _ => liftA2PowerSet ;
       op_zlztzg____ := fun _ _ => liftA2PowerSet id ;
       op_ztzg____ := fun _ _ => liftA2PowerSet (fun _ => id) ;
       pure__ := fun _ => purePowerSet
    |}.

  Instance Functor__PowerSet__AppKleenePlus : Functor (PowerSet I) :=
    apdict_functor _ PowerSetAppKleenePlusApp__Dicts.

  Instance Applicative__PowerSet__AppKleenePlus : Applicative (PowerSet I) :=
    fun _ r => r PowerSetAppKleenePlusApp__Dicts.

  Instance AppKleenePlus__PowerSet : AppKleenePlus (PowerSet I) :=
    fun _ r => r {| kleenePlus__ := fun _ => kplusPowerSet |}.

  (** * Theorems

  These are useful for proving the soundness of [Repeatedly]. *)

  Lemma RefinesSingleStep : forall {A} (a : PowerSet I A),
      RefinesPowerSet a (kleenePlus a).
  Proof.
    intros ? a v. intros. unfold kleenePlus.
    cbn. unfold kplusPowerSet.
    exists 0. cbn. assumption.
  Qed.

  Lemma RefinesRepeat : forall {A} n (a : PowerSet I A),
      RefinesPowerSet (repeatPowerSet a n) (kleenePlus a).
  Proof.
    induction n.
    - apply (@RefinesSingleStep).
    - intros. intros p ?. unfold kleenePlus.
      cbn. unfold kplusPowerSet.
      exists (S n). assumption.
  Qed.

  Lemma seqPowerSet_dist : forall {A} m n (a : PowerSet I A) b,
      seqPowerSet (repeatPowerSet a m) (repeatPowerSet a n) b ->
      seqPowerSet a (repeatPowerSet a (m + n)) b.
  Proof.
    induction m; cbn.
    - intros. assumption.
    - intros; unfold seqPowerSet in *.
      destruct H as (m' & k' & Hm & ? & ?).
      destruct Hm as (m'' & k'' & ? & ? & ?).
      exists m''. exists (liftA2 (fun _ => id) k'' k').
      split; [assumption|]. split.
      + apply IHm. exists k''. exists k'. intuition.
        reflexivity.
      + rewrite <- H3 in H0.
        etransitivity; [|apply H0].
        destruct ALI. symmetry. apply naturality.
        intros. reflexivity.
  Qed.

  Lemma RefinesKplus : forall {A} (a b : PowerSet I A),
      RefinesPowerSet a (kleenePlus b) ->
      RefinesPowerSet (kleenePlus a) (kleenePlus b).
  Proof.
    intros. intros p Hp.
    unfold RefinesPowerSet, kleenePlus in H.
    cbn in H. unfold kplusPowerSet in H.
    unfold kleenePlus in Hp. cbn in Hp. unfold kplusPowerSet in Hp.
    destruct Hp.
    revert p H0. induction x; intros.
    - cbn in H0. apply H; assumption.
    - cbn in H0. unfold seqPowerSet in H0.
      destruct H0 as (a1 & a2 & ? & ? & ?).
      specialize (H a1 H0). destruct H as (n & ?).
      specialize (IHx _ H1). unfold kleenePlus in IHx.
      cbn in IHx. unfold kplusPowerSet in IHx.
      destruct IHx as (m & ?).
      exists (S (n + m))%nat. cbn.
      apply seqPowerSet_dist.
      unfold seqPowerSet. exists a1. exists a2. intuition.
  Qed.

End AppKleenePlusTransformer.

(** We cannot show that all the [PowerSet I A] satisfy the laws we desire (like
    left identity law of applicative functors). This is because an arbitrary
    [PowerSet I A] might not maintain the invariance (the [Invariance] we
    defined in the previous section). Instead of proving that [PowerSet I A] are
    instances of [ApplicativeLaws] and [ApplicativeCongruenceLaws], we show that
    all [PowerSet I A] that maintain the invariance are instances of them. We do
    that by using a subset type [PowerSetI] defined below. *)

Section ApplicativeLaws.

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

  Program Definition RefinesPowerSetI {A} : relation (PowerSetI I (@EqI) A) :=
    RefinesPowerSet.

  Global Instance PreOrder__RefinesPowerSetI {A} : PreOrder (@RefinesPowerSetI A).
  constructor.
  - intros a p q. assumption.
  - intros a b c Hab Hbc.
    unfold RefinesPowerSetI in *. intros i Hi.
    specialize (Hab i Hi).  specialize (Hbc i Hab).
    assumption.
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

  Program Definition liftA2PowerSetI {A B C} :
    (A -> B -> C) ->
    PowerSetI I (@EqI) A -> PowerSetI I (@EqI) B -> PowerSetI I (@EqI) C :=
    (@liftA2PowerSet I (@FI) (@AI) (@EqI) A B C).
  Next Obligation.
    apply liftA2Invariance. apply (@EqIEq).
  Qed.

  Program Definition repeatPowerSetI {A} :
    PowerSetI I (@EqI) A -> nat -> PowerSetI I (@EqI) A :=
    (@repeatPowerSet I (@FI) (@AI) (@EqI) A).
  Next Obligation.
    apply repeatInvariance.
    - apply (@EqIEq).
    - destruct x. simpl. apply i.
  Qed.

  Program Definition kplusPowerSetI {A} :
    PowerSetI I (@EqI) A -> PowerSetI I (@EqI) A :=
    (@kplusPowerSet I (@FI) (@AI) (@EqI) A).
  Next Obligation.
    apply kplusInvariance.
    - apply (@EqIEq).
    - destruct x. simpl. apply i.
  Qed.

  Definition PowerSetIApplicative__AppDict :
    Applicative__Dict (PowerSetI I (@EqI)) :=
    {| liftA2__ := fun _ _ _ => liftA2PowerSetI ;
       op_zlztzg____ := fun _ _ => liftA2PowerSetI id ;
       op_ztzg____ := fun _ _ => liftA2PowerSetI (fun _ => id) ;
       pure__ := fun _ => purePowerSetI
    |}.

  Global Instance Functor__PowerSetIKleenePlus : Functor (PowerSetI I (@EqI)) :=
    apdict_functor _ PowerSetIApplicative__AppDict.

  Global Instance Applicative__PowerSetIKleenePlus :
    Applicative (PowerSetI I (@EqI)) :=
    apdict_applicative _ PowerSetIApplicative__AppDict.

  (** * Core theorems

   These are used for proving the soundness of [Repeatedly]. *)

  Global Instance ApplicativeLaws__PowerSetKleenePlus :
    @ApplicativeLaws (PowerSetI I (@EqI)) (@EqPowerSetI) _ _.
  constructor.
  - (* liftA2_left_id *)
    intros. cbn. split.
    + cbn. unfold liftA2PowerSet, purePowerSet.
      destruct b as (b & HIb).
      intros (a' & b' & HEqa' & Hb & HEq). simpl in *.
      rewrite HEqa' in HEq. rewrite liftA2_left_id in HEq; [|assumption].
      specialize (HIb b' a0 HEq). apply HIb. assumption.
    + cbn. unfold liftA2PowerSet, purePowerSet.
      destruct b as (b & HIb). simpl. intros.
      exists (pure a). exists a0. repeat split.
      * reflexivity.
      * assumption.
      * apply liftA2_left_id. assumption.
  - (* liftA2_right_id *)
    intros. cbn. split.
    + cbn. unfold liftA2PowerSet, purePowerSet.
      destruct a as (a & HIa).
      intros (a' & b' & Ha & HEqb' & HEq). simpl in *.
      rewrite HEqb' in HEq. rewrite liftA2_right_id in HEq; [|assumption].
      specialize (HIa a' a0 HEq). apply HIa. assumption.
    + cbn. unfold liftA2PowerSet, purePowerSet.
      destruct a as (a & HIa). simpl. intros.
      exists a0. exists (pure b). repeat split.
      * assumption.
      * reflexivity.
      * apply liftA2_right_id. assumption.
  - (* associativity *)
    intros.
    destruct a as [a HIa].
    destruct b as [b HIb].
    destruct c as [c HIc].
    split; simpl.
    + unfold liftA2PowerSet, purePowerSet.
      intros. repeat destructs; subst.
      rewrite <- H4 in H2. exists x1. exists (liftA2 g x2 x0).
      split; [assumption|]. split.
      * exists x2. exists x0. repeat split; try assumption. reflexivity.
      * rewrite <- H2. symmetry. apply assoc.
        -- destruct ALI. constructor; assumption.
        -- assumption.
    + unfold liftA2PowerSet, purePowerSet.
      intros. repeat destructs; subst.
      rewrite <- H4 in H2. exists (liftA2 f x x1). exists x2. split.
      * exists x. exists x1. repeat split; try assumption. reflexivity.
      * split; [assumption|]. rewrite <- H2. apply assoc.
        -- destruct ALI. constructor; assumption.
        -- assumption.
  - (* naturality *)
    intros.
    destruct a as [a HIa].
    destruct b as [b HIb].
    destruct c as [c HIc].
    split; simpl.
    + unfold liftA2PowerSet, purePowerSet.
      intros. repeat destructs; subst.
      rewrite <- H4 in H2. exists x1. exists (liftA2 g x2 x0).
      split; [assumption|]. split.
      * exists x2. exists x0. repeat split; try assumption. reflexivity.
      * rewrite <- H2. symmetry. apply naturality.
        -- destruct ALI. constructor; assumption.
        -- assumption.
    + unfold liftA2PowerSet, purePowerSet.
      intros. repeat destructs; subst.
      rewrite <- H4 in H2. exists (liftA2 q x x1). exists x2. split.
      * exists x. exists x1. repeat split; try assumption. reflexivity.
      * split; [assumption|]. rewrite <- H2. apply naturality.
        -- destruct ALI. constructor; assumption.
        -- assumption.
  Qed.

  Lemma LiftA2RefinesCongruence :
    forall {A B C} (f : A -> B -> C)
      (a1 a2 : PowerSetI I (@EqI) A) (b1 b2 : PowerSetI I (@EqI) B),
    RefinesPowerSetI a1 a2 ->
    RefinesPowerSetI b1 b2 ->
    RefinesPowerSetI (liftA2 f a1 b1) (liftA2 f a2 b2).
  Proof.
    intros.
    destruct a1 as [a1 HIa1].
    destruct a2 as [a2 HIa2].
    destruct b1 as [b1 HIb1].
    destruct b2 as [b2 HIb2].
    unfold RefinesPowerSetI in *. simpl in *.
    intros ? Hlift. destruct Hlift as (a' & b' & Ha' & Hb' & HEq).
    exists a'. exists b'. repeat split.
    + apply H; assumption.
    + apply H0; assumption.
    + assumption.
  Qed.

  Global Instance ApplicativeCongruenceLaws__PowerKleenePlus :
    @ApplicativeCongruenceLaws (PowerSetI I (@EqI)) (@EqPowerSetI) _ _.
  constructor. intros.
  destruct a1 as [a1 HIa1].
  destruct a2 as [a2 HIa2].
  destruct b1 as [b1 HIb1].
  destruct b2 as [b2 HIb2].
  unfold EqPowerSetI in *. simpl in *. split.
  - intros Hlift. destruct Hlift as (a' & b' & Ha' & Hb' & HEq).
    exists a'. exists b'. repeat split.
    + apply H; assumption.
    + apply H0; assumption.
    + assumption.
  - intros Hlift. destruct Hlift as (a' & b' & Ha' & Hb' & HEq).
    exists a'. exists b'. repeat split.
    + apply H; assumption.
    + apply H0; assumption.
    + assumption.
  Qed.
End ApplicativeLaws.
