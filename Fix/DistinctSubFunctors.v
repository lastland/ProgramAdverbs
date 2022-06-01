Require Import Fix.SumE.
Require Import Fix.Functor.

Class DistinctSubFunctors (F G H : (Set -> Set) -> Set -> Set)
      `{F -≪ H} `{G -≪ H} `{Functor1 H} :=
  { inj_discrminate : forall E A (f : F E A) (g : G E A),
      inj1 f <> inj1 g }.

Section DistinctSubFunctorsInference.
  Variables F G H I : (Set -> Set) -> Set -> Set.
  Context `{Functor1 G} `{Functor1 I}.

  Global Instance DistinctSubFunctors_SumE
         `{F -≪ G} `{H -≪ I} :
    DistinctSubFunctors F H (G ⊕ I).
  constructor. intros. inversion 1.
  Defined.

  Global Instance DistinctSubFunctors_SumE'
         `{F -≪ G} `{H -≪ I} :
    DistinctSubFunctors F H (I ⊕ G).
  constructor. intros. inversion 1.
  Defined.

  Global Instance DistinctSubFunctors_inl
         `{F -≪ G} `{H -≪ G}
         {DSF : DistinctSubFunctors F H G} :
    DistinctSubFunctors F H (G ⊕ I).
  constructor. intros. inversion 1.
  destruct DSF as [ijd].
  specialize (ijd _ _ f g). contradiction.
  Defined.

  Global Instance DistinctSubFunctors_inr
         `{F -≪ G} `{H -≪ G}
         {DSF : DistinctSubFunctors F H G} :
    DistinctSubFunctors F H (I ⊕ G).
  constructor. intros. inversion 1.
  destruct DSF as [ijd].
  specialize (ijd _ _ f g). contradiction.
  Defined.
End DistinctSubFunctorsInference.
