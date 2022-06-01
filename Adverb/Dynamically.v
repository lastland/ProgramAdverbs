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
Require Import ClassesOfFunctors.Laws.

Open Scope adverb_scope.

(* begin dynamically_adv *)
(* Dynamically *)
Inductive ReifiedMonad (E : Type -> Type) (R : Type) : Type :=
| EmbedM (e : E R)
| Ret (r : R)
| Bind {X : Type} (m : ReifiedMonad E X) (k : X -> ReifiedMonad E R).
(* end dynamically_adv *)

Definition embedM {E A} : E A -> ReifiedMonad E A := EmbedM.

Definition returnM {E A} : A -> ReifiedMonad E A := Ret.

Definition bindM {E A B} : ReifiedMonad E A -> (A -> ReifiedMonad E B) ->
                           ReifiedMonad E B :=
  Bind.

Definition MonadDict__ReifiedMonad {E} : Monad__Dict (ReifiedMonad E) :=
  {| op_zgzg____ := fun _ _ m k => bindM m (fun _ => k) ;
     op_zgzgze____ := fun _ _ => bindM ;
     return___ := fun _ => returnM
  |}.

Global Instance Functor__ReifiedMonad {E : Type -> Type} : Functor (ReifiedMonad E) :=
  @monaddict_functor _ MonadDict__ReifiedMonad.

Global Instance Applicative__ReifiedMonad {E : Type -> Type} : Applicative (ReifiedMonad E) :=
  @monaddict_applicative _ MonadDict__ReifiedMonad.

Global Instance Monad__ReifiedMonad {E : Type -> Type} : Monad (ReifiedMonad E) :=
  @monaddict_monad _ MonadDict__ReifiedMonad.

Definition interpM
  {E I : Type -> Type} `{Monad I}
  {EqI : forall (A : Type), relation (I A)} {A : Type}
  (interpE : forall A, E A -> I A) :=
  let fix go {A : Type} (t : ReifiedMonad E A) : I A :=
    match t with
    | EmbedM e => interpE _ e
    | Ret a => return_ a
    | Bind m k => go m >>= (fun r => go (k r))
    end
  in @go A.

(** * The adverb simulation. *)
Global Instance ReifiedMonaderbSim :
  ReifiedMonad ⊧ Monad__Dict UNDER IdT :=
  {| interp := fun _ I D =>
                 @interpM _ _
                   (monaddict_functor I D)
                   (monaddict_applicative I D)
                   (monaddict_monad I D)
  |}.

Reserved Notation "a ≅ b" (at level 42).

Declare Scope dynamically_scope.

Inductive DynamicallyBisim {E} : forall {A}, relation (ReifiedMonad E A) :=
| dynamically_congruence :
  forall {A B} (m1 m2 : ReifiedMonad E A) (k1 k2 : A -> ReifiedMonad E B),
    m1 ≅ m2 ->
    (forall a, k1 a ≅ k2 a) ->
    (m1 >>= k1) ≅ (m2 >>= k2)
| dynamically_left_id :
  forall A B (a : A) (h : A -> ReifiedMonad E B),
    (return_ a >>= h) ≅ h a
| dynamically_right_id :
  forall A (m : ReifiedMonad E A),
    (m >>= return_) ≅ m
| dynamically_assoc :
  forall A B C (m : ReifiedMonad E A)
    (g : A -> ReifiedMonad E B)
    (h : B -> ReifiedMonad E C),
      ((m >>= g) >>= h) ≅ (m >>= (fun x => g x >>= h))
| dynamically_refl : forall A (a : ReifiedMonad E A), a ≅ a
| dynamically_sym : forall A (a b : ReifiedMonad E A), a ≅ b -> b ≅ a
| dynamically_trans : forall A (a b c : ReifiedMonad E A), a ≅ b -> b ≅ c -> a ≅ c
where "a ≅ b" := (DynamicallyBisim a b) : dynamically_scope.

Global Program Instance ReifiedMonaderb : Adverb ReifiedMonad :=
  {| Bisim := fun _ _ => DynamicallyBisim ;
     Refines := fun _ _ => DynamicallyBisim
  |}.
Next Obligation.
  constructor.
  - intros a. constructor.
  - intros a b. constructor. assumption.
  - intros a b c ? ?. econstructor; eassumption.
Qed.
Next Obligation.
  constructor.
  - intros a. constructor.
  - intros a b c ? ?. econstructor; eassumption.
Qed.

Theorem soundness_of_dynamically :
  forall {E I : Type -> Type} {A : Type}
    {EqI : forall (A : Type), relation (I A) } `{forall A, Equivalence (EqI A) }
    {D : Monad__Dict I}
    {_ : @MonadLaws I EqI (monaddict_functor _ D) (monaddict_applicative _ D) (monaddict_monad _ D)}
    {_ : @MonadCongruenceLaws I EqI (monaddict_functor _ D) (monaddict_applicative _ D) (monaddict_monad _ D)}
    (interpE : forall A, E A -> I A) (x y : ReifiedMonad E A)
    (Hbisim : x ≅ y),
    EqI _ (interp (C0:=D)(EqI:=EqI) interpE x) (interp (C0:=D)(EqI:=EqI) interpE y).
Proof.
  intros. induction Hbisim.
  - unfold interp. cbn.
    apply bind_cong; assumption.
  - unfold interp. cbn.
    apply (@monad_left_id _ _ _ _ _ H0).
  - unfold interp. cbn.
    apply monad_right_id; assumption.
  - unfold interp. cbn.
    apply monad_assoc; assumption.
  - unfold interp. cbn. reflexivity.
  - unfold interp. cbn. symmetry. assumption.
  - unfold interp. cbn. etransitivity; eassumption.
Qed.
