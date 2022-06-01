Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.

Require Import GHC.Base.
Require Import Fix.Functor.

From Coq Require Import
     Relation_Definitions
     RelationClasses
     FunctionalExtensionality
     ssrfun
.

(** Based on Section 2.2 of [Meta-theory à la Carte]. *)

(** * Core definitions *)

Section Fix.

(** * Definitions. *)

(* begin fix *)
Definition Alg (F : Set -> Set) (A : Set) : Set := F A -> A.
Definition Fix (F : Set -> Set) : Set := forall {A : Set}, Alg F A -> A.
Definition foldFix {F : Set -> Set } {A : Set}
           (alg : Alg F A) (f : Fix F) : A := f _ alg.
(* end fix *)

(** * In and out *)

(* begin in_out_F *)
Definition inF {F : Set -> Set} `{FunctorE F} (fexp : F (Fix F)) : Fix F :=
  fun _ alg => alg (fmapE (foldFix alg) fexp).

Definition outF {F : Set -> Set} `{FunctorE F} (exp : Fix F) : F (Fix F) :=
  foldFix (fmapE inF) exp.
(* end in_out_F *)

End Fix.


Section Fix1.

(** * Definitions. *)

(* begin fix1 *)
(* Least fixpoint for program adverbs and effects. *)
Definition Alg1 (F : (Set -> Set) -> Set -> Set) (E : Set -> Set) : Type :=
  forall {A : Set}, F E A -> E A.
Definition Fix1 (F : (Set -> Set) -> Set -> Set) (A : Set) :=
  forall (E : Set -> Set), Alg1 F E -> E A.
(* end fix1 *)

Variable F : (Set -> Set) -> Set -> Set.

Definition Alg1M (E : Set -> Set) : Set :=
  forall {E' : Set -> Set} {X : Set}, (E' X -> E X) -> F E' X -> E X.

Definition Fix1M (A : Set) := forall {E : Set -> Set}, Alg1M E -> E A.

Definition foldFix1 {E A} (alg : Alg1 F E) (f : Fix1 F A) : E A := f _ alg.

Definition foldFix1M {E A} (alg : Alg1M E) (f : Fix1M A) : E A := f _ alg.

Context `{Functor1 F}.

(** * In and out *)

Definition inF1 {A : Set} (fexp : F (Fix1 F) A) : Fix1 F A :=
  fun _ alg => alg _ (fmap1 (fun _ => foldFix1 alg) fexp).

Definition outF1 {A : Set} (exp : Fix1 F A) : F (Fix1 F) A :=
  foldFix1 (fun _ => fmap1 (fun _ => inF1)) exp.

End Fix1.


Section FixRel.

(** * Definitions. *)

(* begin fixRel *)
(* Least fixpoint for equivalence relations of program adverbs and effects. *)
Definition AlgRel {F : Set -> Set}
           (R : (forall (A : Set), relation (F A)) -> forall (A : Set), relation (F A))
           (K : forall (A : Set), relation (F A)) : forall (A : Set), relation (F A) :=
  fun A (a b : F A) => R K _ a b -> K _ a b.

Definition FixRel {F : Set -> Set}
           (R : (forall (A : Set), relation (F A)) -> forall (A : Set), relation (F A))
  : forall (A : Set), relation (F A) :=
  fun A (a b : F A) => forall (K : forall (A : Set), relation (F A)),
      (forall (A : Set) (a b : F A), AlgRel R K _ a b) -> K _ a b.
(* end fixRel *)

Variable F : Set -> Set.

Variable R : (forall (A : Set), relation (F A)) -> forall (A : Set), relation (F A).

Variable K : (forall (A : Set), relation (F A)).


Definition foldFixRel {A : Set}
           (alg : forall (A : Set) (a b : F A), AlgRel R (@K) _ a b) :
  forall (a b : F A), FixRel (@R) A a b -> K a b.
  intros a b f. apply f. apply alg.
Defined.

End FixRel.

Section FixRelInOut.

Variable F : Set -> Set.

Variable R : (forall (A : Set), relation (F A)) -> forall (A : Set), relation (F A).

Context `{FunctorRel F (@R)}.

(** This one feels odd. *)
Theorem inFRel {A : Set} (a b : F A) (frel : R (FixRel (@R)) a b) : FixRel R _ a b.
  intros K alg. apply alg.
  eapply fmapRel; [| exact frel].
  intros ? x y f.
  exact (foldFixRel alg f).
Defined.

Theorem outFRel {A : Set} (a b : F A) (frel : FixRel R _ a b) : R (FixRel R) a b.
  refine (foldFixRel _ frel).
  intros ? x y r.
  eapply fmapRel; [|exact r].
  intros. eapply inFRel. assumption.
Defined.
End FixRelInOut.



(** * Equivalence *)

Section Equivalence.

  Variable F : (Set -> Set) -> Set -> Set.
  Variable A : Set.

  Set Implicit Arguments.

  Definition Fix_eq (a b : Fix1 F A) : Prop := forall (E : Set -> Set), a E =1 b E.

  Instance Reflexive_Fix_eq : Reflexive Fix_eq.
  constructor.
  Defined.

  Instance Symmetric_Fix_eq : Symmetric Fix_eq.
  intros x y. cbv. intros. symmetry. auto.
  Defined.

  Instance Transitive_Fix_eq : Transitive Fix_eq.
  intros x y z. cbv. intros. etransitivity; [apply H | auto].
  Defined.

  Instance Equivalence_Fix_eq : Equivalence Fix_eq.
  constructor; typeclasses eauto.
  Defined.
End Equivalence.

Notation "f =f g" := (Fix_eq f g) (at level 70, g at next level).
