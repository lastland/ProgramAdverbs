Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.

Require Import GHC.Base.

Require Import Fix.Functor.
Require Import Fix.SumE.

Class WFFunctor1 (F G : (Set -> Set) -> Set -> Set) `{Functor1 F} `{Functor1 G} (I : F -≪ G) :=
  { wf_functor : forall (A B : Set -> Set) (h : forall X, A X -> B X) (X : Set) (e : F A X),
      fmap1 h (inj1 e) = inj1 (fmap1 h e) }.

Arguments WFFunctor1 F G {_} {_} I.

Section WFFunctor1Inference.
  Variables F G H : (Set -> Set) -> Set -> Set.
  Context `{Functor1 F} `{Functor1 G} `{Functor1 H}.

  Global Instance WFFunctor1_Id : WFFunctor1 F F Inj1_Id | 0.
  constructor. reflexivity.
  Defined.

  Global Instance WFFunctor1_SumE_l {I : F -≪ G} {W : WFFunctor1 F G I}
    : WFFunctor1 F (G ⊕ H) Inj1_Sum1_l | 1.
  constructor. intros. cbn. unfold "∘".
  rewrite wf_functor. reflexivity.
  Defined.

  Global Instance WFFunctor1_SumE_r {I : F -≪ G} {W : WFFunctor1 F G I}
    : WFFunctor1 F (H ⊕ G) Inj1_Sum1_r | 2.
  constructor. intros. cbn. unfold "∘".
  rewrite wf_functor. reflexivity.
  Defined.

  Global Instance WFFunctor1_SumE_l_rev {I : F ⊕ G -≪ H} {W : WFFunctor1 (F ⊕ G) H I}
    : WFFunctor1 F H Inj1_Sum1_l_rev | 2.
  constructor. intros. cbn. unfold "∘".
  rewrite wf_functor. reflexivity.
  Defined.

  Global Instance WFFunctor1_SumE_r_rev {I : F ⊕ G -≪ H} {W : WFFunctor1 (F ⊕ G) H I}
    : WFFunctor1 G H Inj1_Sum1_r_rev | 2.
  constructor. intros. cbn. unfold "∘".
  rewrite wf_functor. reflexivity.
  Defined.
End WFFunctor1Inference.
