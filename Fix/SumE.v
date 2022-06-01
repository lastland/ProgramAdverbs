Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.

Require Import GHC.Base.

Require Import Fix.Fix.
Require Import Fix.Functor.

From Coq Require Import
     Relation_Definitions
.

(** Based on Section 2.5 of [Meta-theory à la Carte]. *)

Variant Sum (F G : Set -> Set) R :=
  Inl (a : F R) | Inr (a : G R).

Variant Sum1 (F G : (Set -> Set) -> Set -> Set) K R :=
  Inl1 (a : F K R) | Inr1 (a : G K R).

Variant SumRel {F : Set -> Set}
        (P Q : (forall (A : Set), relation (F A)) -> forall (A : Set), relation (F A))
        (K : forall (A : Set), relation (F A)) : forall (A : Set), relation (F A) :=
| InlRel {A : Set} {a b : F A} : P K _ a b -> SumRel P Q K _ a b
| InrRel {A : Set} {a b : F A} : Q K _ a b -> SumRel P Q K _ a b.

Notation "F + G" := (Sum F G) : tlon_scope.
Notation "F ⊕ G" := (Sum1 F G) (at level 42, right associativity) : tlon_scope.
Notation "F ⊎ G" := (SumRel F G) (at level 42, right associativity) : tlon_scope.

Delimit Scope tlon_scope with tlon.

Class Inj (F G : Set -> Set) :=
  { inj {A} : F A -> G A }.

Class Inj1 (F G : (Set -> Set) -> Set -> Set) :=
  { inj1 {E A} : F E A -> G E A }.

Class InjRel {F : Set -> Set}
      (P Q : (forall (A : Set), relation (F A)) -> forall (A : Set), relation (F A)) :=
  { injRel {K : forall (A : Set), relation (F A)} : forall (A : Set) (a b : F A), P K _ a b -> Q K _ a b }.

Notation "F -< G" := (Inj F G) (at level 51).
Notation "F -≪ G" := (Inj1 F G) (at level 43).
Notation "F -⋘ G" := (InjRel F G) (at level 43).

Open Scope tlon_scope.

(** * Basic injection inference rules. *)

#[export] Instance Inj_Id F : F -< F | 0 :=
  {| inj := fun _ => id |}.

#[export] Instance Inj_Sum_l {F G H} `{F -< G} : F -< G + H | 1 :=
  {| inj := fun _ => Inl ∘ inj |}.

#[export] Instance Inj_Sum_r {F G H} `{F -< G} : F -< H + G | 2 :=
  {| inj := fun _ => Inr ∘ inj |}.

#[export] Instance Inj1_Id F : F -≪ F | 0 :=
  {| inj1 := fun _ _ => id |}.

#[export] Instance Inj1_Sum1_l {F G H} `{F -≪ G} : F -≪ G ⊕ H | 1 :=
  {| inj1 := fun _ _ => Inl1 ∘ inj1 |}.

#[export] Instance Inj1_Sum1_r {F G H} `{F -≪ G} : F -≪ H ⊕ G | 2 :=
  {| inj1 := fun _ _ => Inr1 ∘ inj1 |}.

Section InjRelRules.

Variable F : Set -> Set.

Variables P Q R : (forall (A : Set), relation (F A)) -> forall (A : Set), relation (F A).

#[global] Instance InjRel_Id : P -⋘ P | 0 :=
  {| injRel := fun _ _ _ _ => id |}.

#[global] Instance InjRel_SumRel_l : P -⋘ (P ⊎ R) | 1 :=
  {| injRel := fun _ A a b => InlRel ∘ injRel A a b |}.

#[global] Instance InjRel_SumRel_r `{P -⋘ R} : P -⋘ (Q ⊎ R) | 2 :=
  {| injRel := fun _ A a b => InrRel ∘ injRel A a b |}.

End InjRelRules.

(** * The composition algebras. *)

Definition Sum1_Comm {F G : (Set -> Set) -> Set -> Set}
           {E : Set -> Set} {A : Set}
           (a : (F ⊕ G) E A) : (G ⊕ F) E A :=
  match a with
  | Inl1 f => Inr1 f
  | Inr1 g => Inl1 g
  end.

Definition Sum1_Assoc {F G I : (Set -> Set) -> Set -> Set}
           {E : Set -> Set} {A : Set}
           (a : (F ⊕ G ⊕ I) E A) : ((F ⊕ G) ⊕ I) E A :=
  match a with
  | Inl1 f => Inl1 (Inl1 f)
  | Inr1 b => match b with
             | Inl1 g => Inl1 (Inr1 g)
             | Inr1 i => Inr1 i
             end
  end.

Definition Sum1_Assoc_inverse {F G I : (Set -> Set) -> Set -> Set}
           {E : Set -> Set} {A : Set}
           (a : ((F ⊕ G) ⊕ I) E A) : (F ⊕ G ⊕ I) E A :=
  match a with
  | Inr1 i => Inr1 (Inr1 i)
  | Inl1 b => match b with
             | Inl1 f => Inl1 f
             | Inr1 g => Inr1 (Inl1 g)
             end
  end.

(** * Some other useful rules. *)

Definition Inj1_Sum1_l_rev {F G H} `{F ⊕ G -≪ H} : F -≪ H :=
  {| inj1 := fun _ _ => inj1 ∘ Inl1 |}.

Definition Inj1_Sum1_r_rev {F G H} `{F ⊕ G -≪ H} : G -≪ H :=
  {| inj1 := fun _ _ => inj1 ∘ Inr1 |}.

#[export] Instance Inj1_Sum1_t {F G H} `{F -≪ G} : H ⊕ F -≪ H ⊕ G | 3 :=
  {| inj1 := fun _ _ a => match a with
                       | Inl1 a => Inl1 a
                       | Inr1 a => Inr1 (inj1 a)
                       end |}.

#[export] Program Instance Functor1__SumE {E F} `{Functor1 E} `{Functor1 F} : Functor1 (E ⊕ F) :=
  {| fmap1 := fun _ _ _ f s =>
                match s with
                | Inl1 a => Inl1 (fmap1 f a)
                | Inr1 a => Inr1 (fmap1 f a)
                end
  |}.
Next Obligation.
  intros x. destruct x; rewrite fmap1_id; reflexivity.
Defined.
Next Obligation.
  intros x. destruct x; rewrite fmap1_comp; reflexivity.
Defined.

#[export] Instance FunctorRel__SumRel {F : Set -> Set}
         {P Q : (forall (A : Set), relation (F A)) -> forall (A : Set), relation (F A)}
         `{FunctorRel F P} `{FunctorRel F Q} : FunctorRel (P ⊎ Q).
Proof.
  constructor; intros. destruct H2.
  - left. eapply fmapRel; eassumption.
  - right. eapply fmapRel; eassumption.
Qed.

Definition lift {A : Set} {E F : (Set -> Set) -> Set -> Set} `{E -≪ F}
           (e : Fix1 E A) : Fix1 F A :=
  fun _ alg => foldFix1 (fun _ x => alg _ (inj1 x)) e.
