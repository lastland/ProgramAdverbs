Require Import GHC.Base.

Require Import Tlon.Tlon.
Require Import Fix.Fix.
Require Import Fix.SumE.

Class WFTlonAlg1 (F G : (Set -> Set) -> Set -> Set) (I : Set -> Set)
      `{F -≪ G} `{TlonAlg1 F I} `{TlonAlg1 G I} :=
  { wf_tlon_alg1 : forall (A : Set) (e : F I A), reflectAlg1 _ (inj1 e) = reflectAlg1 _ e }.

Section WFTlonAlg1Inference.
  Variables F G H : (Set -> Set) -> Set -> Set.
  Variable I : Set -> Set.
  Context `{TlonAlg1 F I} `{TlonAlg1 G I} `{TlonAlg1 H I}.

  Global Instance WFTlonAlg1_Id : WFTlonAlg1 F F I | 0.
  constructor. reflexivity.
  Defined.

  Global Instance WFTlonAlg1_SumE_l : WFTlonAlg1 F (F ⊕ G) I | 1.
  constructor. reflexivity.
  Defined.

  Global Instance WFTlonAlg1_SumE_r `{WFTlonAlg1 F G I} : WFTlonAlg1 F (H ⊕ G) I | 2.
  constructor. intros. simpl. unfold "∘". f_equal. apply H6.
  Defined.
End WFTlonAlg1Inference.
