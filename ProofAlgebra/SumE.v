Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.

Require Import Fix.
Require Import ProofAlgebra.ProofAlgebra.

Section ProofAlg1_Sum1.

Variables (F G H : (Set -> Set) -> Set -> Set).
Context `{Functor1 F} `{Functor1 G} `{Functor1 H}.
Context `{F ⊕ G -≪ H}.
Variable P : forall (A : Set), Fix1 H A -> Prop.
Variable PF : ProofAlg1 (H1 := Inj1_Sum1_l_rev) F (@P).
Variable PG : ProofAlg1 (H1 := Inj1_Sum1_r_rev) G (@P).

Instance ProofAlg1_Sum1 : ProofAlg1 (F ⊕ G) (@P).
econstructor. Unshelve.
2: { intros ? [].
     - apply PF; assumption.
     - apply PG; assumption. }
intros ? []; [apply PF | apply PG].
Defined.

End ProofAlg1_Sum1.
