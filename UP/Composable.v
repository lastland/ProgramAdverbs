Require Import GHC.Base.
Require Import Fix.

Require Import Adverb.Composable.Purely.
Require Import Adverb.Composable.Streamingly.
Require Import Adverb.Composable.Statically.
Require Import Adverb.Composable.Dynamically.

Require Import ProofAlgebra.ProofAlgebra.
Require Import ProofAlgebra.Composable.
Require Import UP.Fix.

From Coq Require Import
     FunctionalExtensionality
.

Section UPs.

  Variable F : (Set -> Set) -> Set -> Set.
  Context `{Functor1 F} `{PurelyAdv -≪ F}.
  Context `{@WFFunctor1 PurelyAdv F Functor1__PurelyAdv _ _}.

  Lemma pure_UP : forall (A : Set) (a : A),
      UP1 F (@inF1 _ _ _ (inj1 (Pure a))).
  Proof.
    intros. constructor. intros.
    rewrite H2. unfold inF1. unfold foldFix1.
    rewrite !wf_functor. reflexivity.
  Qed.

  Global Instance ProofAlg_PurelyAdv_UP1 : ProofAlg1 PurelyAdv (@UP1 F _) :=
    Pure_ProofAlgebra _ _ pure_UP.

  Definition pure' {A : Set} (a : A) : {e : Fix1 F A | UP1 F e} :=
    inF'1 (HP:=ProofAlg_PurelyAdv_UP1) (Pure a).

  Section Functor.

    Context `{StreaminglyAdv -≪ F}.
    Context `{@WFFunctor1 StreaminglyAdv F Functor1__StreaminglyAdv _ _}.

    Lemma fmap_UP : forall (A B : Set) (g : A -> B) f,
        UP1 F f -> UP1 F (fmap g f).
    Proof.
      intros. constructor. intros.
      unfold fmap. cbn. unfold fmap_ff.
      specialize (H5 _ (inj1 (FMap g f))) as Hmap.
      rewrite H5. unfold inF1. rewrite !wf_functor. cbn.
      destruct H4. erewrite -> UP1_implies_fold. 2: { intros; apply H5. }
      reflexivity.
    Qed.

    Global Instance ProofAlg_StreaminglyAdv_UP1 : ProofAlg1 StreaminglyAdv (@UP1 F _) :=
      FunctorT_ProofAlgebra _ _ fmap_UP.

    Definition fmap' {A B : Set} (f : A -> B) (a : {e : Fix1 F A | UP1 F e})
      : {e : Fix1 F B | UP1 F e} :=
      inF'1 (HP:=ProofAlg_StreaminglyAdv_UP1) (FMap f a).

    Global Instance Functor_StreaminglyAdv' :
      Functor (fun A => {e : Fix1 F A | UP1 F e }) :=
      fun _ k => k {| fmap__      := fun {a} {b} => fmap' ;
                   op_zlzd____ := fun {a} {b} => fmap' ∘ const |}.
  End Functor.

  Section Applicative.

    Context `{StaticallyAdv -≪ F}.
    Context `{@WFFunctor1 StaticallyAdv F Functor1__StaticallyAdv _ _}.

    Lemma liftA2_UP : forall (A B C : Set) (f : A -> B -> C) a b,
        UP1 F a -> UP1 F b -> UP1 F (liftA2 f a b).
    Proof.
      intros. constructor. intros.
      unfold liftA2. cbn. unfold liftA2_fa.
      rewrite H6. unfold inF1. rewrite !wf_functor. cbn.
      destruct H4. erewrite -> UP1_implies_fold.
      2: { intros. apply H6. }
      destruct H5. erewrite -> UP1_implies_fold0.
      2: { intros. apply H6. }
      reflexivity.
    Qed.

    Global Instance ProofAlg_StaticallyAdv_UP1 : ProofAlg1 StaticallyAdv (@UP1 F _) :=
      ApT_ProofAlgebra _ _ liftA2_UP.

    Definition liftA2' {A B C : Set}
               (f : A -> B -> C)
               (a : {e : Fix1 F A | UP1 F e})
               (b : {e : Fix1 F B | UP1 F e})
      : {e : Fix1 F C | UP1 F e} :=
      inF'1 (HP:=ProofAlg_StaticallyAdv_UP1) (LiftA2 f a b).

    Definition fmap'A {A B : Set} (f : A -> B)
               (a : {e : Fix1 F A | UP1 F e}) : {e : Fix1 F B | UP1 F e} :=
      liftA2' id (pure' f) a.

    Global Instance Functor_StaticallyAdv' :
      Functor (fun A => {e : Fix1 F A | UP1 F e }) :=
      fun _ k => k {| fmap__      := fun {a} {b} => fmap'A ;
                   op_zlzd____ := fun {a} {b} => fmap'A ∘ const |}.

    Global Instance Applicative_StaticallyAdv' :
      Applicative (fun A => {e : Fix1 F A | UP1 F e }) :=
      fun _ k => k {| liftA2__ := fun {a b c} => liftA2' ;
               op_zlztzg____ := fun {a b} => liftA2' id ;
               op_ztzg____ := fun {a b} fa => liftA2' id (id <$ fa) ;
               pure__ := fun {a} => pure' |}.

  End Applicative.

  Section Monad.

    Context `{DynamicallyAdv -≪ F}.
    Context `{@WFFunctor1 DynamicallyAdv F Functor1__DynamicallyAdv _ _}.

    Lemma ret_UP : forall (A : Set) (a : A),
        UP1 F (return_ a).
    Proof.
      exact pure_UP.
    Qed.

    Lemma bind_UP : forall (A B : Set) (g : A -> Fix1 F B) m,
        UP1 F m -> (forall a, UP1 F (g a)) -> UP1 F (m >>= g).
    Proof.
      intros. constructor. intros.
      unfold ">>=". cbn. unfold bind_fm.
      rewrite H6. unfold inF1. rewrite !wf_functor. cbn.
      destruct H4. erewrite -> UP1_implies_fold.
      2: { intros. apply H6. }
      replace (fun x : A => h B (g x))
        with (fun x : A => foldFix1 alg (g x)).
      2: { apply functional_extensionality.
           intro a. specialize (H5 a).
           destruct H5. erewrite -> UP1_implies_fold0.
           reflexivity. intros. apply H6. }
      reflexivity.
    Qed.

    Global Instance ProofAlg_DynamicallyAdv_UP1 : ProofAlg1 DynamicallyAdv (@UP1 F _) :=
      MonadT_ProofAlgebra _ _ bind_UP.


    Definition return_' {A : Set} (a : A) : {e : Fix1 F A | UP1 F e} :=
      pure' a.

    Definition bind' {A B : Set}
               (m : {e : Fix1 F A | UP1 F e})
               (k : A -> {e : Fix1 F B | UP1 F e}) : {e : Fix1 F B | UP1 F e} :=
      inF'1 (HP:=ProofAlg_DynamicallyAdv_UP1) (Bind m k).

    Definition fmap'M {A B : Set} (f : A -> B)
               (a : {e : Fix1 F A | UP1 F e}) : {e : Fix1 F B | UP1 F e} :=
      bind' a (return_' ∘ f).

    Definition ap'M {A B : Set}
               (f : {e : Fix1 F (A -> B) | UP1 F e})
               (a : {e : Fix1 F A | UP1 F e}) : {e : Fix1 F B | UP1 F e} :=
      bind' f (fun f => bind' a (fun a => return_' (f a))).

    Global Instance Functor_DynamicallyAdv' :
      Functor (fun A => {e : Fix1 F A | UP1 F e }) :=
      fun _ k => k {| fmap__      := fun {a} {b} => fmap'M ;
                   op_zlzd____ := fun {a} {b} => fmap'M ∘ const |}.

    Global Instance Applicative_DynamicallyAdv' :
      Applicative (fun A => {e : Fix1 F A | UP1 F e }) :=
      fun _ k => k {| liftA2__ := fun {a b c} g fa fb => ap'M (fmap'M g fa) fb ;
               op_zlztzg____ := fun {a b} => ap'M ;
               op_ztzg____ := fun {a b} fa => ap'M (id <$ fa) ;
               pure__ := fun {a} => return_' |}.

    Global Instance Monad_FMonaT' :
      Monad (fun A => {e : Fix1 F A | UP1 F e }) :=
      fun _ k => k {| op_zgzg____ := fun {a} {b} m k => bind' m (fun _ => k) ;
                   op_zgzgze____ := fun {a} {b} => bind' ;
                   return___ := fun {a} => return_' |}.
  End Monad.

End UPs.
