# Program Adverbs and Tlön Embeddings (artifact)

This artifact contains the Coq formalization of the paper [Program
Adverbs and Tlön Embeddings](https://doi.org/10.1145/3547632) by Yao Li and Stephanie Weirich, published at ICFP 2022.

Here is the abstract of the paper:

> Free monads (and their variants) have become a popular general-purpose tool
> for representing the semantics of effectful programs in proof
> assistants. These data structures support the compositional definition of
> semantics parameterized by uninterpreted events, while admitting a rich
> equational theory of equivalence. But monads are not the only way to structure
> effectful computation, why should we limit ourselves?
>
> In this paper, inspired by applicative functors, selective functors, and other
> structures, we define a collection of data structures and theories, which we
> call program adverbs, that capture a variety of computational
> patterns. Program adverbs are themselves composable, allowing them to be used
> to specify the semantics of languages with multiple computation patterns. We
> use program adverbs as the basis for a new class of semantic embeddings called
> Tlön embeddings. Compared with embeddings based on free monads, Tlön
> embeddings allow more flexibility in computational modeling of effects, while
> retaining more information about the program’s syntactic structure.

This artifact contains a Coq implementation of all the key definitions, theorems
and proofs, as well as examples described in the paper.

## How to use this artifact

### Dependencies

If you are accessing the artifact via the VM image we provide, you should have
all the dependencies installed already.

The artifact requires [the Coq proof assistant](https://coq.inria.fr/). The
artifact is known to work with Coq versions 8.14.1 and 8.15.1.

The artifact also requires the [Equations
library](https://github.com/mattam82/Coq-Equations). To install it via
OPAM:

``` shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-equations
```
The artifact is known to work with Equations 1.3.

### Proof check

To check all the proofs contained in the artifact, you just need to
run `make`:

``` shell
make
```
or run `make` in parallel:
``` shell
make -j
```

This will invoke Coq to check the proofs in all the `.v` files. Some warnings
are expected but there should not be any errors.

The actual execution time may vary depending on the machine and the Coq version
you are using.

### Checking axioms

Our Coq formalization relies on Coq's [impredicative set
extension](https://github.com/coq/coq/wiki/Impredicative-Set), as stated in
Section 4.2 of our paper, and the [functional extensionality
axiom](https://coq.inria.fr/library/Coq.Logic.FunctionalExtensionality.html).

The artifact does not contain any unfinished/admitted proofs. There are two ways
to check the axioms our proofs rely on:

(1) You can search keywords such as `admit` or `Axiom`:

``` shell
grep -ri admit ./*.v
grep -ri axiom ./*.v
```

(The `-i` option ignores the cases. By searching `admit` with this option, both
the `admit` and `Admitted` keywords are covered.)

(2) You can use the `Print Assumptions` command [provided by
Coq](https://coq.inria.fr/refman/proof-engine/vernacular-commands.html#coq:cmd.Print-Assumptions). For
example, you can add the following lines to the end of the `Examples/NetImp.v`
file:

``` coq
Print Assumptions refinesL1.
Print Assumptions refinesL2.
Print Assumptions refinesL3.
Print Assumptions refinesL4.
```

You should see that they rely only on impredicative sets.

### Checking main claims of the paper

A paper draft has also been provided in the submission. We have listed all the
main claims in the paper and where to find them in a separate file
[`Claims.markdown`](Claims.markdown).

## Organization

### Libraries

- `GHC`: some helper functions from GHC, translated using
  [hs-to-coq](https://github.com/plclub/hs-to-coq) but manually modified.
- `Tactics`: some custom tactics.
- `ClassesOfFunctors`: some classes of functors in addition to those defined in
  `GHC`.
- `Transformers`: the `PowerSet` data type (Fig. 8) and its three types of
  transformers.

### Meta-theory à la Carte

These files contain the relevant definitions to implement composable adverbs
(Section 4) from adapting [Meta-theory à la
carte](https://doi.org/10.1145/2480359.2429094):

- `Fix` and `Fix.v`: least fixpoint operators, sum data types, functors, etc.
- `ProofAlgebra` and `ProofAlgebra.v`: for induction principles.
- `UP`: universal property.

### Definitions of Adverbs

#### Adverbs

- `Adverb`: adverbs discussed in Section 3 as well as some standalone versions
  of add-on adverbs (Section 4.3). These files include definitions of the adverb
  data types, adverb theories, as well as soundness proofs.

#### Adverb data types of composable adverbs

- `Adverb/Composable`: adverb data types for composable adverbs.

#### Adverb theories of composable adverbs

- `Eq`: equivalence relations.
- `Refines`: refinement relations.

### Examples

- `Examples`: The examples in the paper (including those in Section 2 and
  Section 5).
