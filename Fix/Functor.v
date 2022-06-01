Require Import GHC.Base.

From Coq Require Import
     Relation_Definitions
     ssrfun
.

Class FunctorE (F : Set -> Set) :=
  { fmapE {A B : Set} : (A -> B) -> F A -> F B ;
    fmapE_id : forall {A : Set}, @fmapE A A id =1 id ;
    fmapE_comp : forall {A B C : Set} (g : B -> C) (f : A -> B),
        fmapE (g ∘ f) =1 fmapE g ∘ fmapE f
  }.

Definition id1 {F : Set -> Set} : forall (A : Set), F A -> F A := fun _ x => x.

Definition comp1 {F G H : Set -> Set}
           (g : forall X, G X -> H X) (f : forall X, F X -> G X) :
  forall X, F X -> H X :=
  fun _ x => g _ (f _ x).

Class Functor1 (E : (Set -> Set) -> Set -> Set) :=
  { fmap1 {F G : Set -> Set} {A : Set} :
      (forall (X : Set), F X -> G X) -> E F A -> E G A;
    fmap1_id : forall {F : Set -> Set} {A : Set}, @fmap1 F F A id1 =1 id;
    fmap1_comp : forall {F G H : Set -> Set} {A : Set}
                    (g : forall X, G X -> H X) (f : forall X, F X -> G X),
        @fmap1 _ _ A (comp1 g f) =1 fmap1 g ∘ fmap1 f
  }.

(** Do I need the functor laws for proofs? *)
Class FunctorRel {F : Set -> Set}
      (R : (forall (A : Set), relation (F A)) -> forall (A : Set), relation (F A)) :=
  { fmapRel {A : Set} {a b : F A} {P Q : forall (A : Set), relation (F A)} :
      (forall {A : Set}(a b : F A), P _ a b -> Q _ a b) -> R P _ a b -> R Q _ a b
  }.

Arguments FunctorRel F R.
