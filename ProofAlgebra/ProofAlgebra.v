Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.

Require Import Fix.Fix.
Require Import Fix.SumE.
Require Import Fix.Functor.
Require Import Fix.WFFunctor.

From Coq Require Import
     ssrfun
     Relation_Definitions
     FunctionalExtensionality
.

Section ProofAlg.

  Variables F G : Set -> Set.
  Context `{FunctorE F} `{FunctorE G} `{F -< G}.
  Variable P : Fix G -> Prop.

  Class ProofAlg :=
    { p_alg : Alg F (sig P) ;
      proj_eq : forall e,
          proj1_sig (p_alg e) = @inF _ _ (inj (fmapE (@proj1_sig _ _) e))
    }.

End ProofAlg.

Arguments ProofAlg F {_} {_} {_} {_} P.

Section ProofAlg1.

  Variables F G : (Set -> Set) -> Set -> Set.
  Context `{Functor1 F} `{Functor1 G} `{F -≪ G}.
  Variable P : forall (A : Set), Fix1 G A -> Prop.

  Class ProofAlg1 :=
    { p_alg1 : Alg1 F (fun T => sig (@P T)) ;
      proj_eq1 : forall (A : Set) e,
          proj1_sig (@p_alg1 A e) =
          @inF1 _ _ _ (inj1 (fmap1 (fun _ => @proj1_sig _ _) e)) }.

End ProofAlg1.

Arguments ProofAlg1 F {_} {_} {_} {_} P.

Section ProofAlgRel.

  Variable F : Set -> Set.

  Variable R Q : (forall (A : Set), relation (F A)) ->
                 forall (A : Set), relation (F A).

  Context `{FunctorRel F R} `{FunctorRel F Q} `{R -⋘ Q}.

  Variable P : forall (A : Set) (a b : F A), FixRel Q A a b -> Prop.

  Class ProofAlgRel :=
    { p_algRel : forall (A : Set) (a b : F A),
        AlgRel R (fun A a b => sig (@P A a b)) _ a b
    }.

End ProofAlgRel.
