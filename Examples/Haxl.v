Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.

From Coq Require Import
     List
     Psatz
     Relation_Definitions
     RelationClasses
.

Require Import GHC.Base.
Require Import Fix.
Require Import Tactics.Tactics.
Require Import ClassesOfFunctors.FunctorPlus.
Require Import ClassesOfFunctors.DictDerive.

Require Import Adverb.Composable.Adverb.
Require Import Adverb.Composable.Purely.
Require Import Adverb.Composable.Statically.
Require Import Adverb.Composable.Dynamically.

Definition var := nat.

Definition val := nat.

(** * Effect. *)

Variant DataEff (K : Set -> Set) : Set -> Set :=
| GetData : var -> DataEff K val.

Arguments GetData {_}.

Definition fmap1_DataEff {F G : Set -> Set} {A : Set}
           (f : forall X, F X -> G X)
           (a : DataEff F A) : DataEff G A :=
  match a with
  | GetData v => GetData v
  end.

#[global] Program Instance Functor1__DataEff : Functor1 DataEff :=
  {| fmap1 := @fmap1_DataEff |}.
Next Obligation.
  destruct x; reflexivity.
Qed.
Next Obligation.
  destruct x; reflexivity.
Qed.

Section SmartConstructor.

  Variable F : (Set -> Set) -> Set -> Set.
  Context `{Functor1 F}.
  Context `{DataEff -≪ F}.

  Definition getData (x : var) : Fix1 F val :=
    @inF1 _ _ _ (inj1 (GetData x)).

End SmartConstructor.

(** * Adverbs used. *)

Definition LanAdverbs := PurelyAdv ⊕ StaticallyAdv ⊕ DynamicallyAdv ⊕ DataEff.

Definition Lan := Fix1 LanAdverbs.

(** A helper method to interpret sums of a composed adverb by
    interpreting each individual adverb. *)

#[global] Instance AdverbAlgSum
         (D1 D2 : (Set -> Set) -> Set -> Set) (R : Set -> Set) (name : nat)
         `{AdverbAlg D1 R name} `{AdverbAlg D2 R name} :
  AdverbAlg (D1 ⊕ D2) R name :=
  {| adverbAlg := fun _ a => match a with
                          | Inl1 a => adverbAlg _ a
                          | Inr1 a => adverbAlg _ a
                          end
  |}.

(** * The DB monad

    As shown in Fig. 14. *)

Definition DB (A : Set) : Set := ((var -> val) -> A * nat).

Open Scope nat_scope.

Definition retDB {A : Set} (a : A) : DB A := fun map => (a, 0).

Definition bindDB {A B : Set}
           (m : DB A) (k : A -> DB B) : DB B :=
  fun map =>
    match m map with
    | (i, n) =>
      match (k i map) with
      | (r, n') => (r, n + n')
      end
    end.

Definition parDB {A B C : Set}
           (f : A -> B -> C) (a : DB A) (b : DB B) : DB C :=
  fun map =>
    match (a map, b map) with
    | ((a, n1), (b, n2)) => (f a b, Nat.max n1 n2)
    end.

Definition getDB (v : var) : DB val :=
  fun map => (map v, 1).

Goal forall {A B C : Set} (f : A -> B -> C) a b,
    forall m, parDB f a b m = parDB (flip f) b a m.
Proof.
  intros. unfold parDB.
  remember (a m) as am. remember (b m) as bm.
  destruct am; destruct bm. unfold flip.
  f_equal. apply Nat.max_comm.
Qed.

(** Give a name to [AdverbAlg], a technical way to tell apart
    different adverb interpretations. *)

Definition numFetchName : nat := 0.

(** * Interpreting Composed Adverbs

    We define the interpreter of our composed adverb [LanAdverbs] by
    defining an interpretation for each individual adverb and then
    compose their interpretation together (automatically composed via
    the [AdverbAlgSum] instance shown earlier). *)

#[global] Instance NumFetchS : AdverbAlg StaticallyAdv DB numFetchName :=
  {| adverbAlg := fun _ c =>
                    match c with
                    | LiftA2 f a b =>
                      parDB f a b
                    end
  |}.

#[global] Instance NumFetchD : AdverbAlg DynamicallyAdv DB numFetchName :=
  {| adverbAlg := fun _ c =>
                    match c with
                    | Bind m k =>
                      bindDB m k
                    end
  |}.

#[global] Instance NumFetchP : AdverbAlg PurelyAdv DB numFetchName :=
  {| adverbAlg := fun _ c =>
                    match c with
                    | Pure a => retDB a
                    end
  |}.

#[global] Instance NumFetchData : AdverbAlg DataEff DB numFetchName :=
  {| adverbAlg := fun _ c =>
                    match c in (DataEff _ N) return (DB N) with
                    | GetData v => getDB v
                    end
  |}.

(** The composed interpreter. *)

Definition numFetchAlg : Alg1 LanAdverbs DB := adverbAlg (name := numFetchName).

Definition numFetch {A : Set} : Lan A -> DB A := foldFix1 (@numFetchAlg).

(** * Examples. *)

Definition test1 : Lan bool := liftA2 (fun _ _ => true)
                              (@getData _ _ _ 0)
                              (@getData _ _ _ 1).

Definition test2 : Lan val := (@getData _ _ _ 0) >> (@getData _ _ _ 1).

Definition test3 : Lan bool := liftA2 (fun _ _ => true)
                              (@test2)
                              ((@test1) >> (@test2)).

(** Uncomment the following to see results: *)

(*
Compute (numFetch (@test1)).

Compute (numFetch (@test2)).

Compute (numFetch (@test3)).
*)

(* cost (the second value in the product) of [test1] should be 1 *)
(* cost (the second value in the product) of [test2] should be 2 *)
(* cost (the second value in the product) of [test3] should be 3 *)
