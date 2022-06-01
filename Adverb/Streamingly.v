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

(* begin streamingly_adv *)
(* Streamingly *)
Inductive ReifiedFunctor (E : Type -> Type) (R : Type) : Type :=
| EmbedF (e : E R)
| FMap {X : Type} (g : X -> R) (f : ReifiedFunctor E X).
(* end streamingly_adv *)

Definition embedF {E A} : E A -> ReifiedFunctor E A := EmbedF.

Definition fmapF {E A B} :
  (A -> B) -> ReifiedFunctor E A -> ReifiedFunctor E B :=
  FMap.

Global Instance Functor__ReifiedFunctor {E : Type -> Type} : Functor (ReifiedFunctor E) :=
  fun r k => k {| fmap__ := fun _ _ => fmapF ;
               op_zlzd____ := fun _ _ a => fmapF (fun _ => a)
            |}.

Definition interpF
  {E I : Type -> Type} `{Functor I}
  {EqI : forall (A : Type), relation (I A)} {A : Type}
  (interpE : forall A, E A -> I A) :=
  let fix go {A : Type} (t : ReifiedFunctor E A) : I A :=
    match t with
    | EmbedF e => interpE _ e
    | FMap f a => fmap f (go a)
    end
  in @go A.

(** * The adverb simulation. *)
Global Instance ReifiedMonaderbSim :
  ReifiedFunctor ⊧ Functor UNDER IdT :=
  {| interp := @interpF |}.

Reserved Notation "a ≅ b" (at level 42).

Declare Scope streamingly_scope.

Inductive StreaminglyBisim {E} : forall {A}, relation (ReifiedFunctor E A) :=
| streamingly_congruence :
  forall {A B} (f : A -> B) (a1 a2 : ReifiedFunctor E A),
    a1 ≅ a2 ->
    fmap f a1 ≅ fmap f a2
| streamingly_fmap_id :
  forall {A} (a : ReifiedFunctor E A), fmap id a ≅ a
| streamingly_fmap_comp :
  forall {A B C} (f : B -> C) (g : A -> B) (a : ReifiedFunctor E A),
      fmap (fun x => f (g x)) a ≅ fmap f (fmap g a)
| streamingly_refl : forall A (a : ReifiedFunctor E A), a ≅ a
| streamingly_sym : forall A (a b : ReifiedFunctor E A), a ≅ b -> b ≅ a
| streamingly_trans : forall A (a b c : ReifiedFunctor E A), a ≅ b -> b ≅ c -> a ≅ c
where "a ≅ b" := (StreaminglyBisim a b) : streamingly_scope.

Global Program Instance ReifiedFunctorAdverb : Adverb ReifiedFunctor :=
  {| Bisim := fun _ _ => StreaminglyBisim ;
     Refines := fun _ _ => StreaminglyBisim
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

Theorem soundness_of_streamingly :
  forall {E I : Type -> Type} {A : Type}
    {EqI : forall (A : Type), relation (I A) } `{forall A, Equivalence (EqI A) }
    {D : Functor I}
    {_ : @FunctorLaws I EqI D}
    {_ : @FunctorCongruenceLaws I EqI D}
    (interpE : forall A, E A -> I A) (x y : ReifiedFunctor E A)
    (Hbisim : x ≅ y),
    EqI _ (interp (C0:=D)(EqI:=EqI) interpE x) (interp (C0:=D)(EqI:=EqI) interpE y).
Proof.
  intros. induction Hbisim.
  - unfold interp. cbn.
    apply fmap_cong; assumption.
  - unfold interp. cbn.
    apply fmap_id; assumption.
  - unfold interp. cbn.
    apply fmap_comp; assumption.
  - reflexivity.
  - symmetry. assumption.
  - etransitivity; eassumption.
Qed.
