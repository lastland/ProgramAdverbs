# Main claims of the paper

## Section 2

All the key definitions in this section are in `Examples/Section2.v`.

- The four properties discussed are named `lemma1`-`lemma4`.
- The four types of semantic embeddings and their relevant definitions shown in
  Fig. 2 can be found in this file, with the same names as in the paper.

## Section 3

- Definition 3.1: `Adverb/Adverb.v`, the `Adverb` type class.
- Definition 3.2: `Adverb/Adverb.v`, the `AdverbSim` and `AdverbSimI` (a
  dependent type version, the detail is explained in the comments of the file)
  type classes.
- Definition 3.3: `Adverb/Adverb.v`, the `interp` and `interpI` methods for
  `AdverbSim` and `AdverbSimI`, respectively.
- Definition 3.4: We do not have a uniform definition for the soundness
    theorem. Instead, each adverb is proved sound in their individual files (all
    of these files are under `Adverb` directory).
- Definition 3.5: This is basically the same definition as 3.4.
- Theorem 3.6: `Adverb/Statically.v`, the theorem `soundness_of_statically`.
- Lemma 3.7: `Transformers/Par.v`, the instance
  `CommNonAssocApplicativeLaws__PowerSetApplicative` and the instance
  `ApplicativeCongruenceLaws__PowerSetApplicative`.
- Theorem 3.8: `Adverb/StaticallyInParallel.v`, the theorem
  `soundness_of_staticallyInParallel`.
- Soundness of `Streamingly`: `Adverb/Streamingly.v`, the theorem
  `soundness_of_streamingly`.
- Soundness of `Dynamically`: `Adverb/Dynamically.v`, the theorem
  `soundness_of_dynamically`.
- Soundness of `Conditionally`: `Adverb/Conditionally.v`, the theorem
  `soundness_of_conditionally`.
- Fig. 5: In the individual files under `Adverb` directory.
- Fig. 6: `Adverb/Statically.v`, the definition `StaticallyBisim`.
- Fig. 7: `Adverb/Statically.v`, the definition `interpA`.
- Fig. 8: `Transformers/Par.v`, inside section `ParTransformer`. There is also a
  dependently typed version `PowerSetI` that maintains an invariance in the
  `CommNonAssocApplicativeLaws` section---why we need this version is explained
  in the comments of the file.

## Section 4

- Definition of ⊕: `Fix/SumE.v`, the definition `Sum1`.
- Fig. 9: `Fix/Fix.v`, with the same names as in the paper.
- Fig. 10: in individual files under `Adverb/Composable` directory.
- Fig. 11: the type classes are in individual files under `ClassesOfFunctors`
  directory; the adverbs are in individual files under `Adverb/Composable`
  directory.
- Fig. 12: `Adverb/Repeatedly.v` and `Adverb/Nondeterministically`, definitions
  `RepeatedlyBisim`, `RepeatedlyRefines`, `NondeterministicallyBisim`, and
  `NondeterministicallyRefines`.
- Soundness of `Repeatedly` (`ReifiedKleenePlus |= PowerSet AppKleenePlus`):
  `Adverb/Repeatedly.v`, theorems `soundness_of_repeatedly_eq` and
  `soundness_of_repeatedly_refines`.
- Soundness of `Nondeterministically` (`ReifiedPlus |=PowerSet FunctorPlus`):
  `Adverb/Nondeterministically.v`, theorems
  `soundness_of_nondeterministically_eq` and
  `soundness_of_nondeterministically_refines`.
- Fig. 13: the `FunctorPlus` transformer is in `Transformers/FunctorPlus.v`.
- Fig. 13: the `AppKleenePlus` transformer is in `Transformers/AppKleenePlus.v`.

## Section 5

- Section 5.1: `Examples/Haxl.v`.
- Section 5.2: `Examples/NetImp.v`.
- The NetImp language: `Examples/NetImp.v`, definitions `exp`, `ev`, `command`.
- The specification language: `Examples/NetImp.v`, definition `commandS`.
- Fig. 14: `Examples/Haxl.v`.
- Fig. 15(a): `Examples/NetImp.v`, definition `process`.
- Fig. 15(b): `Examples/NetImp.v`, definition `processSpec`.
- Tlön embeddings of the networked server: `Examples/NetImp.v`, definitions
  `denote_command` and `denote_command_Spec`
- Refinement proofs of the networked server: `Examples/NetImp.v`, theorems
  `refinesL1`-`refinesL4`.
