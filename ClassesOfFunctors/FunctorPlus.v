Set Universe Polymorphism.

Require Import GHC.Base.

(** * The beautiful version for presentation. *)
(* begin functorplus *)
Class FunctorPlus (F : Type -> Type) `{Functor F} :=
  { fplus {A} : F A -> F A -> F A }.
(* end functorplus *)

Reset FunctorPlus.

(** For technical reasons, many type classes we used are defined as
    follow: we first define a [Dict] version that has no dependencies
    of other type classes, then we declare a version that has
    dependencies based on the [Dict] version. The [Dict] version is
    useful because all [Dict]s have the same type [(Type -> Type) ->
    Type]: the uniformity in their types is important for defining
    [AdverbSim] and [AdverbSimI] using the same interfaces. *)

(** * The actual version we use. *)
Polymorphic Cumulative Record FunctorPlus__Dict (F : Type -> Type) :=
  FunctorPlus__Dict_Build {
      fplus__ {A} : F A -> F A -> F A }.

Polymorphic Definition FunctorPlus (F : Type -> Type) `{Functor F} :=
  forall (r__ : Type), (FunctorPlus__Dict F -> r__) -> r__.
Existing Class FunctorPlus.

Polymorphic Definition fplus {F} `{g : FunctorPlus F} :
  forall {A}, F A -> F A -> F A :=
  g _ (fplus__ F).
