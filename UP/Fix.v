From Coq Require Import
     ssrfun
     FunctionalExtensionality.

Require Import GHC.Base.
Require Import Fix.
Require Import ProofAlgebra.ProofAlgebra.

(** * Properties for [Fix]. *)

(** * The universal property of folds, in one direction. *)
Theorem UP_fold_implies : forall {F : Set -> Set} {A : Set} `{FunctorE F}
               (alg : Alg F A) (h : Fix F -> A),
    (forall e, h e = foldFix alg e) ->
    (forall e, h (@inF _ _ e) = alg (fmapE h e)).
Proof.
  intros. specialize (H0 (@inF _ _ e)) as H1.
  rewrite H0. unfold foldFix, inF.
  replace (foldFix alg) with h.
  2: { apply functional_extensionality. apply H0. }
  reflexivity.
Qed.

(** * The universal property of folds, in other direction.

    We will instantiate this when defining each F. *)
Class UP (F : Set -> Set) `{FunctorE F} e :=
  { UP_implies_fold : forall {A : Set} (alg : Alg F A) (h : Fix F -> A),
      (forall e, h (@inF _ _ e) = alg (fmapE h e)) ->
      h e = foldFix alg e }.

Arguments UP F {_} e.

Theorem ReflectLaw {F : Set -> Set} e `{UP F e} :
  foldFix inF e = e.
Proof.
  intros. symmetry.
  apply UP_implies_fold with (h:=id).
  intros. rewrite fmapE_id. reflexivity.
Qed.

Theorem FusionLaw {F : Set -> Set} e `{UP F e} :
  forall (A B : Set) (f : A -> B) (alg1 : Alg F A) (alg2 : Alg F B),
    (forall e, f (alg1 e) = alg2 (fmapE f e)) ->
    f (foldFix alg1 e) = foldFix alg2 e.
Proof.
  intros.
  epose proof (UP_implies_fold alg2 (f ∘ foldFix alg1)).
  apply H2. intros e0.
  specialize (H1 (fmapE (foldFix alg1) e0)).
  rewrite fmapE_comp.
  unfold inF, "∘".  rewrite <- H1.
  reflexivity.
Qed.

(** * Smart constructors using [UP]. *)

Definition inF' {F G : Set -> Set} `{FunctorE F} `{FunctorE G}
           `{F -< G} {HP : ProofAlg F (UP G)}
           (fexp : F ({e | UP G e})) : {e | UP G e} :=
  p_alg (ProofAlg := HP) fexp.


(** * Properties for [Fix]. *)

(** * The universal property of folds, in one direction. *)
Theorem UP1_fold_implies :
  forall {F : (Set -> Set) -> Set -> Set} {E : Set -> Set} `{Functor1 F}
    (alg : Alg1 F E) (h : forall (A : Set), Fix1 F A -> E A),
    (forall A e, h A e = foldFix1 alg e) ->
    (forall A e, h _ (@inF1 _ _ _ e) = alg _ (fmap1 (A:=A) h e)).
Proof.
  intros. specialize (H0 _ (@inF1 _ _ _ e)) as H1.
  rewrite H0. unfold foldFix1, inF1.
  replace ((@foldFix1 F E)^~ alg) with h.
  2: { apply functional_extensionality_dep. intros X.
       apply functional_extensionality. intros x.
       apply H0. }
  reflexivity.
Qed.

(** * The universal property of folds, in other direction.

    We will instantiate this when defining each F. *)
Class UP1 {F : (Set -> Set) -> Set -> Set}  `{Functor1 F} A e :=
  { UP1_implies_fold : forall {E : Set -> Set} (alg : Alg1 F E)
                        (h : forall (A : Set), Fix1 F A -> E A),
    (forall A e, h _ (@inF1 _ _ _ e) = alg _ (fmap1 (A:=A) h e)) ->
    h A e = foldFix1 alg e }.

Arguments UP1 F {_} {_} e.

Lemma ReflectLaw1 {F : (Set -> Set) -> Set -> Set} {A : Set} e `{UP1 F A e} :
  forall {E : Set -> Set} (f : Alg1 F E),
    foldFix1 (@inF1 _ _) e = e.
Proof.
  intros. symmetry.
  apply UP1_implies_fold with (h:=fun _ => id).
  intros. rewrite fmap1_id. reflexivity.
Qed.

Lemma FusionLaw1 {F : (Set -> Set) -> Set -> Set} {A : Set} e `{UP1 F A e} :
  forall (E G : Set -> Set) (alg1 : Alg1 F E) (alg2 : Alg1 F G)
    (f : forall (X : Set), E X -> G X),
    (forall A e, f _ (alg1 _ e) = alg2 _ (@fmap1 _ _ _ _ A f e)) ->
    f A (foldFix1 alg1 e) = foldFix1 alg2 e.
Proof.
  intros.
  epose proof (UP1_implies_fold alg2 (fun A => f A ∘ foldFix1 alg1)).
  cbn in H2. apply H2. intros A' e'.
  specialize (H1 _ (fmap1 (fun A => @foldFix1 F E A alg1) e')).
  replace (fun A0 : Set => f A0 ∘ foldFix1 alg1)
    with(comp1 f (fun A => @foldFix1 F E A alg1)) by reflexivity.
  rewrite fmap1_comp. unfold "∘". rewrite <- H1. reflexivity.
Qed.

(** * Smart constructors using [UP1]. *)

Definition inF'1 {F G : (Set -> Set) -> Set -> Set}
           `{Functor1 F} `{Functor1 G} `{F -≪ G}
           {HP : ProofAlg1 F (fun T => UP1 G)} {A : Set}
           (fexp : F (fun T => { e : Fix1 G T | UP1 G e} ) A)
  : {e : Fix1 G A | UP1 G e} :=
  p_alg1 (ProofAlg1 := HP) fexp.
