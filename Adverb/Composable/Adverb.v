Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.
Set Universe Polymorphism.

Require Import GHC.Base.
Require Import Fix.

From Coq Require Import
     Relation_Definitions
     RelationClasses
.

Class AdverbAlg (D : (Set -> Set) -> Set -> Set) (R : Set -> Set) (name : nat) :=
  { adverbAlg : Alg1 D R }.

(** A helper method to interpret sums of a composed adverb by
    interpreting each individual adverb. *)

#[export] Instance AdverbAlgSum
         (D1 D2 : (Set -> Set) -> Set -> Set) (R : Set -> Set) (name : nat)
         `{AdverbAlg D1 R name} `{AdverbAlg D2 R name} :
  AdverbAlg (D1 ⊕ D2) R name :=
  {| adverbAlg := fun _ a => match a with
                          | Inl1 a => adverbAlg _ a
                          | Inr1 a => adverbAlg _ a
                          end
  |}.

(* begin composable_adverb *)
Class ComposableAdverb (F : (Set -> Set) -> Set -> Set) :=
  { Bisim {E} `{F -≪ E} `{Functor1 E} :
      (forall (A : Set), relation (Fix1 E A)) ->
      forall (A : Set), relation (Fix1 E A) ;
    equiv {E} `{F -≪ E} `{Functor1 E} {A} : Equivalence (FixRel Bisim A) ;
    Refines {E} `{F -≪ E} `{Functor1 E} :
      (forall (A : Set), relation (Fix1 E A)) ->
      forall (A : Set), relation (Fix1 E A) ;
    pre {E} `{F -≪ E} `{Functor1 E} {A} : PreOrder (FixRel Refines A) ;
  }.
(* end composable_adverb *)

Declare Scope composable_adverb_scope.
Delimit Scope composable_adverb_scope with composable_adverb.

Notation "a ≅ b" := (FixRel Bisim _ a b) (at level 42)
                    : composable_adverb_scope.
Notation "a ⊆ b" := (FixRel Refines _ a b) (at level 42)
                    : composable_adverb_scope.


Class ComposableAdverbSim
      (D : (Set -> Set) -> Set -> Set)
      (C : (Set -> Type) -> Type)  (* Would I run into trouble here? *)
      (T : (Set -> Set) -> Set -> Set) :=
  { interpAlg {I : Set -> Set} `{C I} : Alg1 D (T I) }.

Definition IdT (C : Set -> Set) : Set -> Set := C.

Notation "D ⊧ C 'UNDER' T" := (ComposableAdverbSim D C T) (at level 39) : composable_adverb_scope.
