Set Universe Polymorphism.

Require Import GHC.Base.

Open Scope type_scope.

(** For technical reasons, many type classes we used are defined as
    follow: we first define a [Dict] version that has no dependencies
    of other type classes, then we declare a version that has
    dependencies based on the [Dict] version. The [Dict] version is
    useful because all [Dict]s have the same type [(Type -> Type) ->
    Type]: the uniformity in their types is important for defining
    [AdverbSim] and [AdverbSimI] using the same interfaces. *)

Polymorphic Cumulative Record Selective__Dict@{i j} (F : Type@{i} -> Type@{j}) :=
  Selective__Dict_Build { select__ : forall {A B : Type@{i}},
        F (A + B) -> F (A -> B) -> F B }.

Polymorphic Definition Selective@{i j k} (F : Type@{i} -> Type@{j}) `{Applicative@{i j k} F} :=
  forall (r__ : Type@{k}), (Selective__Dict F -> r__) -> r__.
Existing Class Selective.

Polymorphic Definition select {F : Type -> Type} `{g : Selective F} :
  forall {A B : Type}, F (A + B) -> F (A -> B) -> F B :=
  g _ (select__ F).

#[export] Polymorphic Instance Selective__eta@{i j k a} (F : Type@{i} -> Type@{j})
            `{Selective@{i j k} F} `{Applicative@{a j k} (fun A => F A)} : Selective@{a j k} (fun A => F A).
intros r k. apply k, H1.
intros AF. destruct AF.
constructor.
- intros a b. exact (select__0 a b).
Defined.
