Set Universe Polymorphism.

Require Import GHC.Base.

(** * Deriving from applicative functors *)

Definition apdict_fmap {I : Type -> Type} `{D : Applicative__Dict I}
           {A B : Type} (f : A -> B) (a : I A) : I B :=
  @liftA2__ I D _ _ _ id (@pure__ I D _ f) a.

#[global] Instance apdict_functor (I : Type -> Type) (D : Applicative__Dict I) : Functor I :=
  fun r k => k {| fmap__      := fun {a} {b} => apdict_fmap (D := D) ;
               op_zlzd____ := fun {a} {b} => apdict_fmap (D := D) ∘ const |}.

#[global] Instance apdict_applicative (I : Type -> Type) (D : Applicative__Dict I) :
  @Applicative I (apdict_functor I D) :=
  fun r k => k D.

(** * Deriving from monads *)

Definition monaddict_fmap {I : Type -> Type} `{D : Monad__Dict I}
           {A B : Type} (f : A -> B) (a : I A) : I B :=
  @op_zgzgze____ I D _ _ a (@return___ I D _ ∘ f).

#[global] Instance monaddict_functor (I : Type -> Type) (D : Monad__Dict I) : Functor I :=
  fun r k => k {| fmap__      := fun {a} {b} => monaddict_fmap (D := D) ;
               op_zlzd____ := fun {a} {b} => monaddict_fmap (D := D) ∘ const |}.

Definition monaddict_ap {I : Type -> Type} `{D : Monad__Dict I}
           {A B : Type} (f : I (A -> B)) (a : I A) : I B :=
  @op_zgzgze____ I D _ _ a
                 (fun a => @op_zgzgze____ I D _ _ f
                                       (fun f => @return___ I D _ (f a))).

#[global] Instance monaddict_applicative (I : Type -> Type) (D : Monad__Dict I) :
  @Applicative I (monaddict_functor I D) :=
  fun r k => k {| liftA2__ := fun {a b c} g fa fb =>
                             monaddict_ap (D := D)
                                          (monaddict_fmap (D := D) g fa) fb ;
               op_zlztzg____ := fun {a b} => monaddict_ap (D := D) ;
               op_ztzg____ := fun {a b} fa => monaddict_ap (D := D) (op_zlzd__
                                                           (g__0__ := monaddict_functor I D) id fa) ;
               pure__ := fun {a} => @return___ I D _ |}.

#[global] Instance monaddict_monad (I : Type -> Type) (D : Monad__Dict I) :
  @Monad I (monaddict_functor I D) (monaddict_applicative I D) :=
  fun r k => k D.
