From Coq Require Import
     Relation_Definitions
     RelationClasses
.

Require Import GHC.Base.

Section FunctorLaws.

Variable F : Type -> Type.

Variable EqF : forall {A : Type}, relation (F A).

Context `{forall {A}, Equivalence (@EqF (F A))}.

Context `{Functor F}.

Notation "x ≡ y" := (EqF x y) (at level 42, no associativity).

Class FunctorLaws :=
  { fmap_id : forall A (a : F A), fmap id a ≡ a ;
    fmap_comp : forall A B C (f : B -> C) (g : A -> B) (a : F A),
      fmap (fun x => f (g x)) a ≡ fmap f (fmap g a)
  }.

Class FunctorCongruenceLaws :=
  { fmap_cong : forall A B (f : A -> B) (a b : F A),
      a ≡ b -> fmap f a ≡ fmap f b }.

End FunctorLaws.

Section ApplicativeLaws.

Variable F : Type -> Type.

Variable EqF : forall {A : Type}, relation (F A).

Context `{forall {A}, Equivalence (@EqF (F A))}.

Context `{Applicative F}.

Notation "x ≡ y" := (EqF x y) (at level 42, no associativity).

Class ApplicativeLaws :=
  { liftA2_left_id : forall A B (a : A) (b : F B),
      liftA2 (fun _ => id) (pure a) b ≡ b ;
    liftA2_right_id : forall A B (a : F A) (b : B),
      liftA2 (fun x _ => x) a (pure b) ≡ a ;
    assoc : forall A B C D (f : A -> B -> C -> D) g (a : F A) (b : F B) (c : F C),
        (forall x y z, f x y z = g y z x) ->
        liftA2 id (liftA2 f a b) c ≡ liftA2 (flip id) a (liftA2 g b c) ;
    naturality : forall {A B C X Y Z} a b c
                   (p : X -> C -> Z) (q : A -> B -> X)
                   (f : A -> Y -> Z) (g : B -> C -> Y),
      (forall x y z, p (q x y) z = f x (g y z)) ->
      liftA2 p (liftA2 q a b) c ≡ liftA2 f a (liftA2 g b c)
  }.

Class CommNonAssocApplicativeLaws :=
  { comm_left_id : forall A B (a : A) (b : F B),
      liftA2 (fun _ => id) (pure a) b ≡ b ;
    comm_right_id : forall A B (a : F A) (b : B),
      liftA2 (fun x _ => x) a (pure b) ≡ a ;
    commutativity : forall A B C (f : A -> B -> C) a b,
      liftA2 f a b ≡ liftA2 (flip f) b a
  }.

Class ApplicativeCongruenceLaws :=
  { liftA2_cong : forall A B C (f : A -> B -> C) a1 a2 b1 b2,
      a1 ≡ a2 -> b1 ≡ b2 ->
      liftA2 f a1 b1 ≡ liftA2 f a2 b2
  }.

End ApplicativeLaws.

Section MonadLaws.

Variable F : Type -> Type.

Variable EqF : forall {A : Type}, relation (F A).

Context `{forall {A}, Equivalence (@EqF (F A))}.

Context `{Monad F}.

Notation "x ≡ y" := (EqF x y) (at level 42, no associativity).

Class MonadLaws :=
  { monad_left_id : forall A B (a : A) (h : A -> F B),
      (return_ a >>= h) ≡ h a ;
    monad_right_id : forall A (m : F A),
      (m >>= return_) ≡ m ;
    monad_assoc : forall A B C (m : F A) (g : A -> F B) (h : B -> F C),
      ((m >>= g) >>= h) ≡ (m >>= (fun x => g x >>= h))
  }.

Class MonadCongruenceLaws :=
  { bind_cong : forall A B (m1 m2 : F A) (k1 k2 : A -> F B),
      m1 ≡ m2 ->
      (forall a, k1 a ≡ k2 a) ->
      (m1 >>= k1) ≡ (m2 >>= k2)
  }.

End MonadLaws.
