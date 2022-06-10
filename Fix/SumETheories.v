Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.

Require Import GHC.Base.

Require Import Fix.Fix.
Require Import Fix.SumE.

From Coq Require Import
  Relation_Definitions
  RelationClasses
  FinFun
.

(** * Theories for ⊕ *)

Definition commMapping {F G : (Set -> Set) -> Set -> Set}
  {E : Set -> Set} {R : Set} (a : (F ⊕ G) E R) : (G ⊕ F) E R :=
  match a with
  | Inl1 f => Inr1 f
  | Inr1 g => Inl1 g
  end.

Lemma Bijective__commMapping :
  forall {F G : (Set -> Set) -> Set -> Set} {E : Set -> Set} {R : Set},
    Bijective (@commMapping F G E R).
Proof.
  intros. exists commMapping. split.
  - destruct x; cbn; reflexivity.
  - destruct y; cbn; reflexivity.
Qed.

Definition assocMapping {F G H : (Set -> Set) -> Set -> Set}
  {E : Set -> Set} {R : Set} (a : ((F ⊕ G) ⊕ H) E R) : (F ⊕ (G ⊕ H)) E R :=
  match a with
  | Inl1 (Inl1 f) => Inl1 f
  | Inl1 (Inr1 g) => Inr1 (Inl1 g)
  | Inr1 h => Inr1 (Inr1 h)
  end.

Lemma Bijective__assocMapping :
  forall {F G H : (Set -> Set) -> Set -> Set} {E : Set -> Set} {R : Set},
    Bijective (@assocMapping F G H E R).
Proof.
  intros.
  exists (fun a => match a with
           | Inl1 f => Inl1 (Inl1 f)
           | Inr1 (Inl1 g) => Inl1 (Inr1 g)
           | Inr1 (Inr1 h) => Inr1 h
           end).
  split.
  - destruct x as [[f | g] | h]; cbn; reflexivity.
  - destruct y as [f | [g | h]]; cbn; reflexivity.
Qed.

Definition equiv1 (F G : (Set -> Set) -> Set -> Set) :=
  forall (E : Set -> Set) (R : Set),
  exists (f : F E R -> G E R), Bijective f.

Instance Equivalence__equiv1 : Equivalence equiv1.
Proof.
  constructor.
  - intros x E R. exists id. exists id.
    split; reflexivity.
  - intros x y Hxy E R.
    specialize (Hxy E R). destruct Hxy as (f & g & Hf & Hg).
    exists g. exists f. tauto.
  - intros x y z Hxy Hyz E R.
    specialize (Hxy E R). specialize (Hyz E R).
    destruct Hxy as (f & g & Hf & Hg).
    destruct Hyz as (h & i & Hh & Hi).
    exists (h ∘ f). exists (g ∘ i). split; unfold "∘"; intros a.
    + rewrite Hh. apply Hf.
    + rewrite Hg. apply Hi.
Qed.

Notation "x ≈ y" := (equiv1 x y) (at level 43, right associativity).

Theorem comm__Sum1 : forall (F G : (Set -> Set) -> Set -> Set),
    F ⊕ G ≈ G ⊕ F.
Proof.
  intros F G E R. eapply ex_intro. apply Bijective__commMapping.
Qed.

Theorem assoc__Sum1 : forall (F G H : (Set -> Set) -> Set -> Set),
    (F ⊕ G) ⊕ H ≈ F ⊕ (G ⊕ H).
Proof.
  intros F G H E R. eapply ex_intro. apply Bijective__assocMapping.
Qed.

(** * Theories for ⊎ *)

Definition equivRel {F : Set -> Set}
  (P Q : (forall (A : Set), relation (F A)) -> forall (A : Set), relation (F A)) :=
  forall (K : forall (A : Set), relation (F A)) (A : Set) (a b : F A),
    P K _ a b <-> Q K _ a b.

Instance Equivalence__equivRel {F : Set -> Set} : Equivalence (@equivRel F).
Proof.
  constructor.
  - intros P K A a b. reflexivity.
  - intros P Q HPQ K A a b. symmetry. apply HPQ.
  - intros P Q R HPQ HQR K A a b. etransitivity.
    + apply HPQ.
    + apply HQR.
Qed.

Notation "P ⇔ Q" := (equivRel P Q) (at level 43, right associativity).

Theorem comm__SumRel {F : Set -> Set} :
  forall (P Q : (forall (A : Set), relation (F A)) -> forall (A : Set), relation (F A)),
    P ⊎ Q ⇔ Q ⊎ P.
Proof.
  intros P Q K A a b. split; destruct 1; (left + right); assumption.
Qed.

Theorem assoc__SumRel {F : Set -> Set} :
  forall (P Q R : (forall (A : Set), relation (F A)) -> forall (A : Set), relation (F A)),
    (P ⊎ Q) ⊎ R ⇔ P ⊎ (Q ⊎ R).
Proof.
  intros P Q R K A a b. split; intros.
  all: repeat match goal with
       | H : context[?P ⊎ ?Q] |- _ =>
           destruct H
         end.
  all: (left + right); (assumption + left + right); assumption.
Qed.

Theorem idem__SumRel {F : Set -> Set} :
  forall (P : (forall (A : Set), relation (F A)) -> forall (A : Set), relation (F A)),
    P ⇔ P ⊎ P.
Proof.
  intros P K A a b. split.
  - left. assumption.
  - destruct 1; assumption.
Qed.
