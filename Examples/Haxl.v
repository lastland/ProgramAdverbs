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

(** * The Update monad

    As shown in Fig. 14a. *)

Definition Update (A : Set) : Set := ((var -> val) -> A * nat).

Open Scope nat_scope.

Definition retUpdate {A : Set} (a : A) : Update A := fun map => (a, 0).

Definition bindUpdate {A B : Set}
           (m : Update A) (k : A -> Update B) : Update B :=
  fun map =>
    match m map with
    | (i, n) =>
      match (k i map) with
      | (r, n') => (r, n + n')
      end
    end.

Definition parUpdate {A B C : Set}
           (f : A -> B -> C) (a : Update A) (b : Update B) : Update C :=
  fun map =>
    match (a map, b map) with
    | ((a, n1), (b, n2)) => (f a b, Nat.max n1 n2)
    end.

(* [getUpdate] is [get] in Fig. 14a. *)
Definition getUpdate (v : var) : Update val :=
  fun map => (map v, 1).

Goal forall {A B C : Set} (f : A -> B -> C) a b,
    forall m, parUpdate f a b m = parUpdate (flip f) b a m.
Proof.
  intros. unfold parUpdate.
  remember (a m) as am. remember (b m) as bm.
  destruct am; destruct bm. unfold flip.
  f_equal. apply Nat.max_comm.
Qed.

Definition MonadDict__Update : Monad__Dict Update :=
  (* [bindUpdate] is [bind] in Fig. 14a. *)
  {| op_zgzg____ := fun _ _ m k => bindUpdate m (fun _ => k) ;
     op_zgzgze____ := fun _ _ => bindUpdate ;
  (* [retUpdate] is [ret] in Fig. 14a. *)
     return___ := fun _ => retUpdate
  |}.

Definition ApDict__Update : Applicative__Dict Update :=
  (* [parUpdate] is [liftA2] in Fig. 14a. *)
  {| liftA2__ := fun _ _ _ => parUpdate ;
     op_zlztzg____ := fun _ _ => parUpdate id ;
     op_ztzg____ := fun _ _ => parUpdate (fun _ => id) ;
     pure__ := fun _ => retUpdate
  |}.

(** Give a name to [AdverbAlg], a technical way to tell apart
    different adverb interpretations. *)

Definition costName : nat := 0.

(** * Interpreting Composed Adverbs

    Fig. 14b. We define the interpreter of our composed adverb [LanAdverbs] by
    defining an interpretation for each individual adverb and then compose their
    interpretation together (automatically composed via the [AdverbAlgSum]
    instance shown earlier). *)

#[global] Instance CostApp : AdverbAlg StaticallyAdv Update costName :=
  {| adverbAlg := fun _ c =>
                    match c with
                    | LiftA2 f a b =>
                      parUpdate f a b
                    end
  |}.

#[global] Instance CostMonad : AdverbAlg DynamicallyAdv Update costName :=
  {| adverbAlg := fun _ c =>
                    match c with
                    | Bind m k =>
                      bindUpdate m k
                    end
  |}.

#[global] Instance CostPure : AdverbAlg PurelyAdv Update costName :=
  {| adverbAlg := fun _ c =>
                    match c with
                    | Pure a => retUpdate a
                    end
  |}.

#[global] Instance CostData : AdverbAlg DataEff Update costName :=
  {| adverbAlg := fun _ c =>
                    match c in (DataEff _ N) return (Update N) with
                    | GetData v => getUpdate v
                    end
  |}.

(** The composed interpreter. *)

Definition costAlg : Alg1 LanAdverbs Update := adverbAlg (name := costName).

Definition cost {A : Set} : Lan A -> Update A := foldFix1 (@costAlg).

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
Compute (cost (@test1)).

Compute (cost (@test2)).

Compute (cost (@test3)).
*)

(* cost (the second value in the product) of [test1] should be 1 *)
(* cost (the second value in the product) of [test2] should be 2 *)
(* cost (the second value in the product) of [test3] should be 3 *)
