Require Import GHC.Base.
Require Import Fix.
Require Import Fix.WFFunctor.
Require Import ProofAlgebra.ProofAlgebra.

Require Import Adverb.Composable.Purely.
Require Import Adverb.Composable.Streamingly.
Require Import Adverb.Composable.Statically.
Require Import Adverb.Composable.Dynamically.

(** * Proof Algebras *)

Section ProofAlgebras.

  Variable F : (Set -> Set) -> Set -> Set.
  Variable P : forall (A : Set), Fix1 F A -> Prop.
  Context `{Functor1 F}.

  (** * Functor *)

  Section FunctorT.

    Context `{StreaminglyAdv -≪ F}.
    Context `{@WFFunctor1 StreaminglyAdv F Functor1__StreaminglyAdv _ _}.

    Variable Hm : forall (A B : Set) (g : A -> B) f, P _ f -> P _ (fmap g f).

    Definition p_alg1_StreaminglyAdv : Alg1 StreaminglyAdv (fun T => sig (P T)).
      intros ? t. destruct t.
      destruct f as [f ?]. exists (fmap g f). auto.
    Defined.

    Program Instance FunctorT_ProofAlgebra
      : ProofAlg1 StreaminglyAdv P :=
      {| p_alg1 := p_alg1_StreaminglyAdv |}.
    Next Obligation.
      destruct e. destruct f as [f ?].
      cbn. reflexivity.
    Defined.

  End FunctorT.

  Context `{PurelyAdv -≪ F}.
  Context `{@WFFunctor1 PurelyAdv F Functor1__PurelyAdv _ _}.

  Variable Hp : forall (A : Set) (a : A), P _ (@inF1 _ _ _ (inj1 (Pure a))).

  Definition p_alg1_PurelyAdv : Alg1 PurelyAdv (fun T => sig (P T)).
    intros ? t. destruct t.
    exists (@inF1 _ _ _ (inj1 (Pure r))).
    apply Hp.
  Defined.

  Program Instance Pure_ProofAlgebra
    : ProofAlg1 PurelyAdv P :=
    {| p_alg1 := p_alg1_PurelyAdv |}.
  Next Obligation.
    destruct e. cbn. reflexivity.
  Defined.

  Section ApT.

    Context `{StaticallyAdv -≪ F}.
    Context `{@WFFunctor1 StaticallyAdv F Functor1__StaticallyAdv _ _}.

    (* Variable Hp : forall (A : Set) (a : A), P _ (pure a). *)
    Variable Ha : forall (A B C : Set) (f : A -> B -> C) (a : Fix1 F A) (b : Fix1 F B),
        P _ a -> P _ b -> P _ (liftA2 f a b).

    Definition p_alg1_StaticallyAdv : Alg1 StaticallyAdv (fun T => sig (P T)).
      intros ? t. destruct t.
      destruct g as [g ?]. destruct a as [a ?].
      exists (liftA2 f g a). apply Ha; eauto.
    Defined.

    Program Instance ApT_ProofAlgebra
      : ProofAlg1 StaticallyAdv P :=
      {| p_alg1 := p_alg1_StaticallyAdv |}.
    Next Obligation.
      destruct e.
      destruct g as [g ?]. destruct a as [a ?].
      cbn. reflexivity.
    Defined.
  End ApT.

  Section MonadT.

    Context `{DynamicallyAdv -≪ F}.
    Context `{@WFFunctor1 DynamicallyAdv F Functor1__DynamicallyAdv _ _}.

    Variable Hb : forall (A B : Set) (g : A -> Fix1 F B) m,
        P _ m -> (forall a, P _ (g a)) -> P _ (m >>= g).

    Definition p_alg1_DynamicallyAdv : Alg1 DynamicallyAdv (fun T => sig (P T)).
      intros ? t. destruct t.
      destruct m as [m ?].
      pose (@proj1_sig _ _ ∘ g) as k.
      exists (m >>= k). apply Hb; eauto.
      intros. unfold k, "∘". apply proj2_sig.
    Defined.

    Program Instance MonadT_ProofAlgebra
      : ProofAlg1 DynamicallyAdv P :=
      {| p_alg1 := p_alg1_DynamicallyAdv |}.
    Next Obligation.
      destruct e.
      destruct m as [m ?]. cbn. reflexivity.
    Defined.
  End MonadT.

End ProofAlgebras.
