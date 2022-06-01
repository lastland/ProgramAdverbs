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

(** * Program Adverb *)

(* A type class for program adverbs. The adverb data type is represented by [F]
   in the parameter. The adverb theory is defined in the [Bisim] field. In
   addition, we show in the [equiv] field that [Bisim] is indeed an equivalence
   relation.

   In addition to Definition 3.1, we also define a refinement relation [Refines]
   and a field [pre] showing that [Refines] is a pre-order. For all basic
   adverbs described in Section 3, [Refines] is the same as [Bisim]. [Refines]
   is only useful later in Section 4.3, when we introduce add-on adverbs. Here
   we just define both relations as part of an adverb so that these adverbs have
   a uniform representation in Coq. *)

(* begin adverb *)
Class Adverb (F : (Type -> Type) -> Type -> Type) :=
  { Bisim {E A} : relation (F E A) ;
    equiv {E A} : Equivalence (@Bisim E A) ;
    Refines {E A} : relation (F E A) ;
    pre {E A} : PreOrder (@Refines E A)
  }.
(* end adverb *)


Declare Scope adverb_scope.
Delimit Scope adverb_scope with adverb.

Notation "a ≅ b" := (Bisim a b) (at level 42) : adverb_scope.
Notation "a ⊆ b" := (Refines a b) (at level 42) : adverb_scope.

(** * Adverb Simulation *)

Class AdverbSim
      (F : (Type -> Type) -> Type -> Type)
      (C : (Type -> Type) -> Type)
      (T : (Type -> Type) -> Type -> Type) :=
  { interp {E : Type -> Type} {I : Type -> Type} `{C I}
           {EqI : forall (A : Type), relation (I A)} {A : Type} :
    (forall A : Type, E A -> I A) -> F E A -> T I A }.


Definition IdT (C : Type -> Type) : Type -> Type := C.

Notation "D ⊧ C 'UNDER' T" := (AdverbSim D C T) (at level 39) : adverb_scope.

Close Scope adverb_scope.

(* In addition to [AdverbSim], we define an extra dependently typed version of
   adverb simulation [AdverbSimI] here. This definition is essentially the same
   as [AdverbSim], except that parameter [T] is a "functor" that also
   parameterized by a relation. This is useful for some [T] that is
   dependently-typed with an invariance that relies on an equivalence
   relation. We can find an example of this in
   [Adverb/StaticallyInParallel.v]. *)

Declare Scope adverbI_scope.
Delimit Scope adverbI_scope with adverbI.


Class AdverbSimI
      (F : (Type -> Type) -> Type -> Type)
      (C : (Type -> Type) -> Type)
      (T : forall (I : Type -> Type),
          (forall (A: Type), relation (I A)) -> Type -> Type) :=
  { interpI {E : Type -> Type} {I : Type -> Type}  `{C I}
      {EqI : forall (A : Type), relation (I A)}
      {EqIEq : forall (A : Type), Equivalence (EqI A)} {A : Type} :
    (forall A : Type, E A -> I A) -> F E A -> T I EqI A }.

Notation "D ⊫ C 'UNDER' T" := (AdverbSimI D C T) (at level 39) : adverbI_scope.

Close Scope adverbI_scope.
