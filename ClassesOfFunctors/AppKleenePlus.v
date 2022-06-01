Set Universe Polymorphism.

Require Import GHC.Base.

(** * The beautiful version for presentation. *)
(* begin star *)
Class AppKleenePlus (F : Type -> Type) `{Applicative F} :=
  { kleenePlus {A} : F A -> F A }.
(* end star *)

Reset AppKleenePlus.

(** For technical reasons, many type classes we used are defined as
    follow: we first define a [Dict] version that has no dependencies
    of other type classes, then we declare a version that has
    dependencies based on the [Dict] version. The [Dict] version is
    useful because all [Dict]s have the same type [(Type -> Type) ->
    Type]: the uniformity in their types is important for defining
    [AdverbSim] and [AdverbSimI] using the same interfaces. *)

(** * The actual version we use. *)
Polymorphic Cumulative Record AppKleenePlus__Dict (F : Type -> Type) :=
  AppKleenePlus__Dict_Build {
      kleenePlus__ {A} : F A -> F A }.

Polymorphic Definition AppKleenePlus (F : Type -> Type) `{Applicative F} :=
  forall (r__ : Type), (AppKleenePlus__Dict F -> r__) -> r__.
Existing Class AppKleenePlus.

Polymorphic Definition kleenePlus {F} `{g : AppKleenePlus F} : forall {A}, F A -> F A :=
  g _ (kleenePlus__ F).
