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

(** * Statically. *)

(* begin statically_adv *)
(* Statically and StaticallyInParallel *)
Inductive ReifiedApp (E : Type -> Type) (R : Type) : Type :=
| EmbedA (e : E R)
| Pure (r : R)
| LiftA2 {X Y : Type} (f : X -> Y -> R)
         (a : ReifiedApp E X) (b : ReifiedApp E Y).
(* end statically_adv *)

(* begin statically_methods *)
Definition embed {E A} : E A -> ReifiedApp E A := EmbedA.

Definition pure {E A} : A -> ReifiedApp E A := Pure.

Definition liftA2 {E A B C} :
  (A -> B -> C) -> ReifiedApp E A -> ReifiedApp E B -> ReifiedApp E C :=
  LiftA2.

Definition fmap {E A B} (f : A -> B) (a : ReifiedApp E A) : ReifiedApp E B :=
  liftA2 id (pure f) a.
(* end statically_methods *)

(** The above code is for illustration purpose. In real code, we do not use
    thoses names because they conflict with the type class names. We reset these
    definitions to use non-conflicting names here. *)
Reset pure.

Definition pureS {E A} (a : A) : ReifiedApp E A :=
  Pure a.

Definition liftA2S {E A B C} (f : A -> B -> C)
           (a : ReifiedApp E A) (b : ReifiedApp E B) : ReifiedApp E C :=
  LiftA2 f a b.

Definition apS {E A B} (f : ReifiedApp E (A -> B))
           (a : ReifiedApp E A) : ReifiedApp E B :=
  liftA2S id f a.

Definition fmapS {E A B} (f : A -> B) (a : ReifiedApp E A) : ReifiedApp E B :=
  apS (pureS f) a.

Global Instance Functor_Statically {E : Type -> Type} : Functor (ReifiedApp E) :=
  fun r k => k {| fmap__      := fun {a} {b} => fmapS ;
               op_zlzd____ := fun {a} {b} => fmapS ∘ const |}.

Global Instance Applicative_Statically {E : Type -> Type} : Applicative (ReifiedApp E) :=
  fun r k => k {| liftA2__ := fun {a b c} => liftA2S ;
               op_zlztzg____ := fun {a b} => apS ;
               op_ztzg____ := fun {a b} fa => liftA2S id ((fmapS ∘ const) id fa) ;
              pure__ := fun {a} => pureS |}.

(* begin interpA *)
Fixpoint interpA {E I : Type -> Type} `{Applicative I} {A : Type}
  (interpE : forall A, E A -> I A) (t : ReifiedApp E A) : I A :=
  match t with
  | EmbedA e => interpE _ e
  | Pure a => pure a
  | LiftA2 f a b => liftA2 f (interpA interpE a) (interpA interpE b)
  end.
(* end interpA *)

Reset interpA.

(** The above code is for illustration purpose. In real code, [interpA] is also
parameterized over an equivalence relation. *)

Definition interpA
  {E I : Type -> Type} `{Applicative I}
  {EqI : forall (A : Type), relation (I A)} {A : Type}
  (interpE : forall A, E A -> I A) :=
  let fix go {A : Type} (t : ReifiedApp E A) : I A :=
    match t with
    | EmbedA e => interpE _ e
    | Pure a => pure a
    | LiftA2 f a b => liftA2 f (go a) (go b)
    end
  in @go A.

(** * The adverb simulation. *)
#[global] Instance ReifiedApperbSim :
  ReifiedApp ⊧ Applicative__Dict UNDER IdT :=
  {| interp := fun E I D =>
                 @interpA E I (apdict_functor I D) (apdict_applicative I D)
  |}.

Declare Scope statically_scope.

Reserved Notation "a ≅ b" (at level 42).

Inductive StaticallyBisim {E A} : relation (ReifiedApp E A) :=
| statically_congruence :
    forall {X Y} a1 a2 b1 b2 (f : X -> Y -> A),
      a1 ≅ a2 -> b1 ≅ b2 -> liftA2 f a1 b1 ≅ liftA2 f a2 b2
| statically_left_id :
    forall {X} (a : X) (b : ReifiedApp E A),
      liftA2 (fun _ => id) (pure a) b ≅ b
| statically_right_id :
    forall {X} (a : ReifiedApp E A) (b : X),
      liftA2 (fun x _ => x) a (pure b) ≅ a
| statically_assoc :
    forall {X Y Z} a b c (f : X -> Y -> Z -> A) g,
      (forall x y z, f x y z = g y z x) ->
      liftA2 id (liftA2 f a b) c ≅ liftA2 (flip id) a (liftA2 g b c)
| statically_natural :
    forall {X Y Z T P} a b c p (q : X -> Y -> T) f (g : Y -> Z -> P),
      (forall x y z, p (q x y) z = f x (g y z)) ->
      liftA2 p (liftA2 q a b) c ≅ liftA2 f a (liftA2 g b c)
| statically_refl : forall a, a ≅ a
| statically_sym : forall a b, a ≅ b -> b ≅ a
| statically_trans : forall a b c, a ≅ b -> b ≅ c -> a ≅ c
where "a ≅ b" := (StaticallyBisim a b) : statically_scope.

Global Program Instance ReifiedApperb : Adverb ReifiedApp :=
  {| Bisim := fun _ _ => StaticallyBisim ;
     Refines := fun _ _ => StaticallyBisim
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

(* begin statically_soundness *)
Theorem soundness_of_statically :
  forall {E I : Type -> Type} {A : Type}
    {EqI : forall (A : Type), relation (I A) } `{forall A, Equivalence (EqI A) }
    {D : Applicative__Dict I}
    {_ : @ApplicativeLaws I EqI (apdict_functor _ D) (apdict_applicative _ D)}
    {_ : @ApplicativeCongruenceLaws I EqI (apdict_functor _ D) (apdict_applicative _ D)}
    (interpE : forall A, E A -> I A) (x y : ReifiedApp E A)
    (Hbisim : x ≅ y),
    EqI _ (interp (C0:=D)(EqI:=EqI) interpE x) (interp (C0:=D)(EqI:=EqI) interpE y).
(* end statically_soundness *)
Proof.
  intros. induction Hbisim.
  - unfold interp. cbn.
    apply liftA2_cong; assumption.
  - unfold interp. cbn.
    apply liftA2_left_id; assumption.
  - unfold interp. cbn.
    apply liftA2_right_id; assumption.
  - unfold interp. cbn.
    apply assoc; assumption.
  - unfold interp. cbn.
    apply naturality; assumption.
  - unfold interp. cbn. reflexivity.
  - unfold interp. cbn. symmetry. assumption.
  - unfold interp. cbn. etransitivity; eassumption.
Qed.
