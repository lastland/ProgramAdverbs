Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.
Set Universe Polymorphism.

From Coq Require Import
     Relation_Definitions
     RelationClasses
.

Require Import Fix.
Require Import GHC.Base.
Require Import Adverb.Adverb.
Require Import ClassesOfFunctors.DictDerive.
Require Import ClassesOfFunctors.AppKleenePlus.
Require Import ClassesOfFunctors.Laws.

Require Import Transformers.AppKleenePlus.

Open Scope adverb_scope.

(** * Repeatedly. *)

(* begin repeatedly_adv *)
Inductive ReifiedKleenePlus (E : Type -> Type) (R : Type) : Type :=
| EmbedR (e : E R)
| KPlus (a : ReifiedKleenePlus E R).
(* end repeatedly_adv *)

Definition embed {E A} : E A -> ReifiedKleenePlus E A := EmbedR.

Definition kplus {E A} : ReifiedKleenePlus E A -> ReifiedKleenePlus E A := KPlus.

(** As stated in the paper, [Repeatedly] is an add-on adverb that should be used
    with other adverbs. Here, we show a combined version of it with
    [Statically] to demonstrate adverb simulation and soundness. *)

Reset ReifiedKleenePlus.

Inductive ReifiedKleenePlus (E : Type -> Type) (R : Type) : Type :=
| EmbedR (e : E R)
| Pure (r : R)
| LiftA2 {X Y : Type} (f : X -> Y -> R)
         (a : ReifiedKleenePlus E X) (b : ReifiedKleenePlus E Y)
| KPlus (a : ReifiedKleenePlus E R).

Definition embed {E A} : E A -> ReifiedKleenePlus E A := EmbedR.

Definition pure {E A} : A -> ReifiedKleenePlus E A := Pure.

Definition liftA2 {E A B C} : (A -> B -> C) ->
                              ReifiedKleenePlus E A ->
                              ReifiedKleenePlus E B ->
                              ReifiedKleenePlus E C := LiftA2.

Definition seq {E A B} : ReifiedKleenePlus E A ->
                         ReifiedKleenePlus E B ->
                         ReifiedKleenePlus E B :=
  liftA2 (fun _ x => x).

Fixpoint repeat {E A}
  (a : ReifiedKleenePlus E A) (n : nat) : ReifiedKleenePlus E A :=
  match n with
  | O => a
  | S n => seq a (repeat a n)
  end.

Definition kplus {E A} : ReifiedKleenePlus E A -> ReifiedKleenePlus E A := KPlus.

(** * The adverb simulation. *)

Open Scope adverbI_scope.

Definition interpRepeatedly {E I : Type -> Type}
  `{D : AppKleenePlus I}
  {EqI : forall A, relation (I A)}
  {EqIEq : forall (A : Type), Equivalence (EqI A)}
  {A : Type}
  (interpE: forall (A : Type), E A -> I A) :=
  let fix go {A : Type} (n : ReifiedKleenePlus E A) : PowerSetI I EqI A :=
    match n with
    | EmbedR e => embedPowerSetI EqIEq (interpE _ e)
    | Pure a => purePowerSetI _ EqIEq a
    | LiftA2 f a b => liftA2PowerSetI _ EqIEq f (go a) (go b)
    | KPlus a => kplusPowerSetI _ EqIEq (go a)
    end
  in @go A.

Polymorphic Cumulative Record AppKleeneCombined (F : Type -> Type) : Type :=
  BuildAppKleeneCombined
    { applicativePart : Applicative__Dict F ;
       kleenePlusPart : AppKleenePlus__Dict F
    }.

#[export] Instance ReifiedKleenePlus__Sim :
  ReifiedKleenePlus ⊫ AppKleeneCombined UNDER PowerSetI :=
  {| interpI := fun _ I D =>
                 @interpRepeatedly _ _
                   (apdict_functor _ (applicativePart D))
                   (apdict_applicative _ (applicativePart D))
                   (fun r k => k (kleenePlusPart D))
  |}.

Declare Scope repeatedly_scope.

Reserved Notation "a ≅ b" (at level 42).

Inductive RepeatedlyBisim {E A} : relation (ReifiedKleenePlus E A) :=
| repeatedly_statically_congruence :
    forall {X Y} a1 a2 b1 b2 (f : X -> Y -> A),
      a1 ≅ a2 -> b1 ≅ b2 -> liftA2 f a1 b1 ≅ liftA2 f a2 b2
| repeatedly_statically_left_id :
    forall {X} (a : X) (b : ReifiedKleenePlus E A),
      liftA2 (fun _ => id) (pure a) b ≅ b
| repeatedly_statically_right_id :
    forall {X} (a : ReifiedKleenePlus E A) (b : X),
      liftA2 (fun x _ => x) a (pure b) ≅ a
| repeatedly_statically_assoc :
    forall {X Y Z} a b c (f : X -> Y -> Z -> A) g,
      (forall x y z, f x y z = g y z x) ->
      liftA2 id (liftA2 f a b) c ≅ liftA2 (flip id) a (liftA2 g b c)
| repeatedly_statically_natural :
    forall {X Y Z T P} a b c p (q : X -> Y -> T) f (g : Y -> Z -> P),
      (forall x y z, p (q x y) z = f x (g y z)) ->
      liftA2 p (liftA2 q a b) c ≅ liftA2 f a (liftA2 g b c)
| repeatedly_congruence :
    forall a1 a2,
      a1 ≅ a2 -> kplus a1 ≅ kplus a2
| repeatedly_refl : forall a, a ≅ a
| repeatedly_sym : forall a b, a ≅ b -> b ≅ a
| repeatedly_trans : forall a b c, a ≅ b -> b ≅ c -> a ≅ c
where "a ≅ b" := (RepeatedlyBisim a b) : repeatedly_scope.

Reserved Notation "a ⊆ b" (at level 42).

Inductive RepeatedlyRefines {E A} : relation (ReifiedKleenePlus E A) :=
| repeatedly_eq :
  forall a b, a ≅ b -> a ⊆ b
| repeatedly_repeat :
  forall a n, repeat a n ⊆ kplus a
| repeatedly_kplus :
  forall a b, a ⊆ kplus b -> kplus a ⊆ kplus b
| repeatedly_refines_trans : forall a b c, a ⊆ b -> b ⊆ c -> a ⊆ c
where "a ⊆ b" := (RepeatedlyRefines a b) : repeatedly_scope.

Global Program Instance NondetermisticallyAdverb : Adverb ReifiedKleenePlus :=
  {| Bisim := fun _ _ => RepeatedlyBisim ;
     Refines := fun _ _ => RepeatedlyRefines
  |}.
Next Obligation.
  constructor.
  - intros a. constructor.
  - intros a b. constructor. assumption.
  - intros a b c ? ?. econstructor; eassumption.
Qed.
Next Obligation.
  constructor.
  - intros a. apply repeatedly_eq.
    constructor.
  - intros a b c ? ?. econstructor; eassumption.
Qed.

Theorem soundness_of_repeatedly_eq :
  forall {E I : Type -> Type} {A : Type}
    {EqI : forall (A : Type), relation (I A) }
    {EqIEq : forall A, Equivalence (EqI A) }
    {D : AppKleeneCombined I}
    {_ : @ApplicativeLaws I EqI
           (apdict_functor _ (applicativePart D))
           (apdict_applicative _ (applicativePart D))}
    {_ : @ApplicativeCongruenceLaws I EqI
           (apdict_functor _ (applicativePart D))
           (apdict_applicative _ (applicativePart D))}
    (interpE : forall A, E A -> I A) (x y : ReifiedKleenePlus E A),
    (* The theorem states that [≅] is an under-approximation of
       [EqPowerSetI]. *)
    x ≅ y ->
    EqPowerSetI (interpI (C0:=D) interpE x) (interpI (C0:=D) interpE y).
Proof.
  intros until y. destruct D as [DA DK].
  intro Hbisim. induction Hbisim.
  - unfold interp. cbn.
    pose proof (@liftA2_cong (PowerSetI I EqI) (@EqPowerSetI I EqI)
                  (@Functor__PowerSetIKleenePlus _
                     (apdict_functor _ DA)
                     (apdict_applicative _ DA) EqI EqIEq) _
                  (@ApplicativeCongruenceLaws__PowerKleenePlus _
                     (apdict_functor _ DA)
                     (apdict_applicative _ DA) EqI _)) as Hcong.
    apply Hcong; assumption.
  - unfold interp. cbn.
    pose proof (@liftA2_left_id (PowerSetI I EqI) (@EqPowerSetI I EqI)
                  (@Functor__PowerSetIKleenePlus _
                     (apdict_functor _ DA)
                     (apdict_applicative _ DA) EqI EqIEq) _
                  (@ApplicativeLaws__PowerSetKleenePlus _
                     (apdict_functor _ DA)
                     (apdict_applicative _ DA) EqI EqIEq _ _)) as Hid.
    apply Hid; assumption.
  - unfold interp. cbn.
    pose proof (@liftA2_right_id (PowerSetI I EqI) (@EqPowerSetI I EqI)
                  (@Functor__PowerSetIKleenePlus _
                     (apdict_functor _ DA)
                     (apdict_applicative _ DA) EqI EqIEq) _
                  (@ApplicativeLaws__PowerSetKleenePlus _
                     (apdict_functor _ DA)
                     (apdict_applicative _ DA) EqI EqIEq _ _)) as Hid.
    apply Hid; assumption.
  - unfold interp. cbn.
    pose proof (@assoc (PowerSetI I EqI) (@EqPowerSetI I EqI)
                  (@Functor__PowerSetIKleenePlus _
                     (apdict_functor _ DA)
                     (apdict_applicative _ DA) EqI EqIEq) _
                  (@ApplicativeLaws__PowerSetKleenePlus _
                     (apdict_functor _ DA)
                     (apdict_applicative _ DA) EqI EqIEq _ _)) as Hassoc.
    apply Hassoc; assumption.
  - unfold interp. cbn.
    pose proof (@naturality (PowerSetI I EqI) (@EqPowerSetI I EqI)
                  (@Functor__PowerSetIKleenePlus _
                     (apdict_functor _ DA)
                     (apdict_applicative _ DA) EqI EqIEq) _
                  (@ApplicativeLaws__PowerSetKleenePlus _
                     (apdict_functor _ DA)
                     (apdict_applicative _ DA) EqI EqIEq _ _)) as Hnatural.
    apply Hnatural; assumption.
  - unfold interp. cbn.
    remember (interpRepeatedly interpE a1) as a1'.
    remember (interpRepeatedly interpE a2) as a2'.
    destruct a1' as [x Hx]; destruct a2' as [y Hy].
    assert (EqPowerSet x y).
    { unfold interpI in IHHbisim. cbn in IHHbisim.
      rewrite <- Heqa1' in IHHbisim.
      rewrite <- Heqa2' in IHHbisim.
      unfold EqPowerSetI in IHHbisim. simpl in *.
      assumption. }
    unfold EqPowerSetI, kplusPowerSetI.
    simpl. unfold kplusPowerSet. split.
    + intros (n & Hr). exists n. revert a Hr. induction n.
      * simpl in *. apply H1.
      * simpl in *. unfold seqPowerSet.
        pose proof (@LiftA2RefinesCongruence I
                      (apdict_functor _ DA)
                      (apdict_applicative _ DA) EqI EqIEq) as Hcong.
        specialize (Hcong A A A (fun _ : A => id)
                      (exist _ x Hx) (exist _ y Hy)).
        unfold Base.liftA2 in Hcong. cbn in Hcong.
        unfold RefinesPowerSetI, liftA2PowerSetI in Hcong.
        simpl in Hcong.
        assert (RefinesPowerSet x y).
        { intros u ?.  specialize (H1 u). apply H1. assumption. }
        assert (Invariance EqI (repeatPowerSet (apdict_applicative I DA) EqI x n)).
        { apply repeatInvariance; assumption. }
        assert (Invariance EqI (repeatPowerSet (apdict_applicative I DA) EqI y n)).
        { apply repeatInvariance; assumption. }
        specialize (Hcong (exist _
                             (repeatPowerSet (apdict_applicative I DA) EqI x n) H3)
                          (exist _
                             (repeatPowerSet (apdict_applicative I DA) EqI y n) H4)
                          H2).
        unfold RefinesPowerSet in Hcong. simpl in Hcong.
        specialize (Hcong IHn). apply Hcong.
    + intros (n & Hr). exists n. revert a Hr. induction n.
      * simpl in *. apply H1.
      * simpl in *. unfold seqPowerSet.
        pose proof (@LiftA2RefinesCongruence I
                      (apdict_functor _ DA)
                      (apdict_applicative _ DA) EqI EqIEq) as Hcong.
        specialize (Hcong A A A (fun _ : A => id)
                      (exist _ y Hy) (exist _ x Hx)).
        unfold Base.liftA2 in Hcong. cbn in Hcong.
        unfold RefinesPowerSetI, liftA2PowerSetI in Hcong.
        simpl in Hcong.
        assert (RefinesPowerSet y x).
        { intros u ?.  specialize (H1 u). apply H1. assumption. }
        assert (Invariance EqI (repeatPowerSet (apdict_applicative I DA) EqI x n)).
        { apply repeatInvariance; assumption. }
        assert (Invariance EqI (repeatPowerSet (apdict_applicative I DA) EqI y n)).
        { apply repeatInvariance; assumption. }
        specialize (Hcong (exist _
                             (repeatPowerSet (apdict_applicative I DA) EqI y n) H4)
                          (exist _
                             (repeatPowerSet (apdict_applicative I DA) EqI x n) H3)
                          H2).
        unfold RefinesPowerSet in Hcong. simpl in Hcong.
        specialize (Hcong IHn). apply Hcong.
  - reflexivity.
  - symmetry; assumption.
  - etransitivity; eassumption.
Qed.

Theorem soundness_of_repeatedly_refines :
  forall {E I : Type -> Type} {A : Type}
    {EqI : forall (A : Type), relation (I A) }
    {EqIEq : forall A, Equivalence (EqI A) }
    {D : AppKleeneCombined I}
    {_ : @ApplicativeLaws I EqI
           (apdict_functor _ (applicativePart D))
           (apdict_applicative _ (applicativePart D))}
    {_ : @ApplicativeCongruenceLaws I EqI
           (apdict_functor _ (applicativePart D))
           (apdict_applicative _ (applicativePart D))}
    (interpE : forall A, E A -> I A) (x y : ReifiedKleenePlus E A),
    (* The theorem states that [⊆] is an under-approximation of
       [RefinesPowerSet]. *)
    x ⊆ y ->
    RefinesPowerSetI (interpI (C0:=D) interpE x) (interpI (C0:=D) interpE y).
Proof.
  intros until y. intro Hrefines. induction Hrefines.
  - unfold interpI. cbn.
    pose proof (@soundness_of_repeatedly_eq E I A EqI EqIEq D _ _
                  interpE a b H1).
    unfold EqPowerSetI, EqPowerSet in H2.
    unfold RefinesPowerSetI, RefinesPowerSet. intros.
    apply H2. assumption.
  - unfold interpI. cbn.
    unfold RefinesPowerSetI, kplusPowerSetI. simpl.
    pose proof (@RefinesRepeat I
                  (apdict_functor _ (applicativePart D))
                  (apdict_applicative _ (applicativePart D))
                  EqI A n) as Hrep.
    cbn in Hrep.
    specialize (Hrep (proj1_sig
                        (@interpRepeatedly _ _
                           (apdict_functor _ (applicativePart D))
                           (apdict_applicative _ (applicativePart D))
                           (fun r k => k (kleenePlusPart D))
                           EqI EqIEq _
                           interpE a))).
    intros ? ?. apply Hrep. clear Hrep. revert a0 H1. induction n.
    + tauto.
    + simpl. unfold seqPowerSet. intros a0.
      pose proof (@LiftA2RefinesCongruence I
                    (apdict_functor _ (applicativePart D))
                    (apdict_applicative _ (applicativePart D)) EqI EqIEq) as Hcong.
      specialize (Hcong A A A (fun _ x : A => x)
                    (@interpRepeatedly _ _
                       (apdict_functor _ (applicativePart D))
                       (apdict_applicative _ (applicativePart D))
                       (fun r k => k (kleenePlusPart D))
                       EqI EqIEq _
                       interpE a)
                    (@interpRepeatedly _ _
                       (apdict_functor _ (applicativePart D))
                       (apdict_applicative _ (applicativePart D))
                       (fun r k => k (kleenePlusPart D))
                       EqI EqIEq _
                       interpE a)).
      unfold Base.liftA2 in Hcong. cbn in Hcong.
      specialize (Hcong
                    (@interpRepeatedly _ _
                       (apdict_functor _ (applicativePart D))
                       (apdict_applicative _ (applicativePart D))
                       (fun r k => k (kleenePlusPart D))
                       EqI EqIEq _
                       interpE (repeat a n))).
      unfold liftA2PowerSetI, RefinesPowerSetI in Hcong.  cbn in Hcong.
      specialize (Hcong (@repeatPowerSetI _
                           (apdict_functor _ (applicativePart D))
                           (apdict_applicative _ (applicativePart D))
                           EqI EqIEq _
                           (@interpRepeatedly _ _
                              (apdict_functor _ (applicativePart D))
                              (apdict_applicative _ (applicativePart D))
                              (fun r k => k (kleenePlusPart D))
                              EqI EqIEq _
                              interpE a) n)).
      unfold repeatPowerSetI in Hcong.
      specialize (Hcong ltac:(reflexivity)).
      apply Hcong. simpl. unfold RefinesPowerSet.
      intros a' ?. apply IHn; assumption.
  - unfold interpI. cbn. unfold kplusPowerSetI, RefinesPowerSetI. cbn.
    pose proof (@RefinesKplus _
                  (apdict_functor _ (applicativePart D))
                  (apdict_applicative _ (applicativePart D))
                  EqI EqIEq _ _).
    unfold kleenePlus in H1. cbn in H1.
    apply H1. apply IHHrefines.
  - etransitivity; eassumption.
Qed.
