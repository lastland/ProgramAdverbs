Require Import Fix.SumE.
Require Import Fix.Functor.
Require Import Fix.WFFunctor.

Class WFInj1 (F G H : (Set -> Set) -> Set -> Set) `{WFFunctor1 F G} `{WFFunctor1 G H} `{F -≪ H} :=
  { wf_inj1 : forall E A (a : F E A), inj1 (inj1 a) = inj1 a }.

Section WFInj1Inference.
  Variables F G H I : (Set -> Set) -> Set -> Set.
  Context `{WFFunctor1 F G} `{Functor1 H}.

  Global Instance WFInj1_Id : WFInj1 F G G | 0.
  constructor; reflexivity.
  Defined.

  (*
  Global Instance WFInj1_SumE : WFInj1 F G (H ⊕ G).
  constructor; reflexivity.
  Defined.
  *)
End WFInj1Inference.
