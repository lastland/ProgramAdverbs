Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.
Set Universe Polymorphism.

From Coq Require Import
     Relation_Definitions
     RelationClasses
.

Require Import Fix.
Require Import GHC.Base.
Require Import Adverb.Adverb.
Require Import ClassesOfFunctors.DictDerive.
Require Import ClassesOfFunctors.Laws.
Require Import ClassesOfFunctors.Selective.

Open Scope adverb_scope.


(* begin conditionally_adv *)
(* Conditionally *)
Inductive ReifiedSelective (E : Type -> Type) (R : Type) : Type :=
| EmbedS (e : E R)
| PureS (r : R)
| SelectBy {X Y : Type} (f : X -> ((Y -> R) + R))
           (a : ReifiedSelective E X) (b : ReifiedSelective E Y).
(* end conditionally_adv *)

Definition selectByCA {E A B C} :
  (A -> ((B -> C) + C)) -> ReifiedSelective E A -> ReifiedSelective E B -> ReifiedSelective E C :=
  SelectBy.

Definition selectCA {E A B} (a : ReifiedSelective E (A + B)) (b : ReifiedSelective E (A -> B)) : ReifiedSelective E B :=
  selectByCA (fun x => match x with
                  | inl x => inl (fun y => y x)
                  | inr x => inr x
                  end) a b.

Definition pureCA {E A} : A -> ReifiedSelective E A := PureS.

Definition fmap__CA {E A B}
           (f : A -> B) (a : ReifiedSelective E A) : ReifiedSelective E B :=
  selectByCA inl (pureCA f) a.

Definition ap__CA {E A B} (f : ReifiedSelective E (A -> B))
           (a : ReifiedSelective E A) : ReifiedSelective E B :=
  selectCA (fmap__CA inl f) (fmap__CA (fun a f => f a) a).

Definition liftA2__CA {E A B C} (f : A -> B -> C)
           (a : ReifiedSelective E A) (b : ReifiedSelective E B) : ReifiedSelective E C :=
  ap__CA (ap__CA (pureCA f) a) b.

Global Instance Functor__CA {E : Type -> Type} : Functor (ReifiedSelective E) :=
  fun r k => k {| fmap__      := fun {a} {b} => fmap__CA ;
              op_zlzd____ := fun {a} {b} => fmap__CA ∘ const |}.

Global Program Instance Applicative__ReifiedSelective {E : Type -> Type} :
  Applicative (ReifiedSelective E) :=
  fun r k => k {| liftA2__ := fun {a b c} => liftA2__CA ;
               op_zlztzg____ := fun {a b} => ap__CA ;
               op_ztzg____ := fun {a b} fa => liftA2__CA id ((fmap__CA ∘ const) id fa) ;
               pure__ := fun {a} => pureCA |}.

Global Program Instance Selective__ReifiedSelective {E : Type -> Type} :
  Selective (ReifiedSelective E) :=
  fun r k => k {| select__ := fun _ _ => selectCA |}.

Definition fmapSum {A B C} (f : A -> B) (a : sum C A) : sum C B :=
  match a with
  | inl c => inl c
  | inr a => inr (f a)
  end.

Definition branch {E A B C} (b : ReifiedSelective E (A + B))
           (l : ReifiedSelective E (A -> C))
           (r : ReifiedSelective E (B -> C)) : ReifiedSelective E C :=
  selectCA (selectCA (fmap (fmapSum inl) b) (fmap (fun f a => inr (f a)) l)) r.

Definition ifS {E A} (b : ReifiedSelective E bool)
           (t e : ReifiedSelective E A) : ReifiedSelective E A :=
  branch (fmap (fun b : bool => if b then inl tt else inr tt) b)
         (fmap (fun a _ => a) t) (fmap (fun a _ => a) e).

Definition pand {E} (x y : ReifiedSelective E bool) : ReifiedSelective E bool :=
  ifS x y (pureCA false).

Definition interpS
  {E I : Type -> Type} `{Monad I}
  {EqI : forall (A : Type), relation (I A)} {A : Type}
  (interpE : forall A, E A -> I A) :=
  let fix go {A : Type} (t : ReifiedSelective E A) : I A :=
    match t with
    | EmbedS e => interpE _ e
    | PureS a => return_ a
    | SelectBy f a b =>  go a >>= (fun x =>
                                    match f x with
                                    | inl y => fmap y (go b)
                                    | inr r => return_ r
                                    end)
    end
  in @go A.

(** * The adverb simulation. *)
Global Instance ReifiedSelectiveSim :
  ReifiedSelective ⊧ Monad__Dict UNDER IdT :=
  {| interp := fun _ I D =>
                 @interpS _ _
                   (monaddict_functor I D)
                   (monaddict_applicative I D)
                   (monaddict_monad I D)
  |}.

Reserved Notation "a ≅ b" (at level 42).

Declare Scope conditionally_scope.

Inductive ConditionallyBisim {E : Type -> Type}
  : forall {A : Type}, relation (ReifiedSelective E A) :=
| conditionally_congruence :
  forall {A B} (a1 a2 : ReifiedSelective E (A + B))
    (b1 b2 : ReifiedSelective E (A -> B)),
    a1 ≅ a2 ->
    b1 ≅ b2 ->
    select a1 b1 ≅ select a2 b2
| conditionally_id : forall {A} (a : ReifiedSelective E (A + A)),
    select a (pure id) ≅ fmap (fun x => match x with
                                     | inl x => x
                                     | inr x => x
                                     end) a
| conditioanlly_distr : forall {A B} (x : A + B)
                          (y z : ReifiedSelective E (A -> B)),
    select (pure x) (y *> z) ≅ (select (pure x) y *> select (pure x) z)
| conditionally_assoc : forall {A B C}
                          (x : ReifiedSelective E (A + B))
                          (y : ReifiedSelective E (C + (A -> B)))
                          (z : ReifiedSelective E (C -> A -> B))
                          (f : (A + B) -> ((A + A) + (C * A + B)))
                          g (h : (C -> A -> B) -> (C * A) -> B),
    (forall x, f x = match x with
                | inl x => inl (inr x)
                | inr x => inr (inr x)
                end) ->
    (forall (y : C + (A -> B)) (a : A + A),
        g y a = let i a :=
                  match y with
                  | inl c => inl (c, a)
                  | inr k => inr (k a)
                  end in
                match a with
                | inl a => i a
                | inr a => i a
                end) ->
    (forall f p, h f p = f (fst p) (snd p)) ->
      select x (select y z) ≅ select (select (fmap f x) (fmap g y)) (fmap h z)
| conditionally_force : forall {A B} (a : ReifiedSelective E B) (b : ReifiedSelective E (A -> B)),
    select (fmap inr a) b ≅ a
| conditionally_refl : forall A (a : ReifiedSelective E A), a ≅ a
| conditionally_sym : forall A (a b : ReifiedSelective E A), a ≅ b -> b ≅ a
| conditionally_trans : forall A (a b c : ReifiedSelective E A), a ≅ b -> b ≅ c -> a ≅ c
where "a ≅ b" := (ConditionallyBisim a b) : conditionally_scope.

Global Program Instance ReifiedConditionally__Adverb : Adverb ReifiedSelective :=
  {| Bisim := fun _ _ => ConditionallyBisim ;
     Refines := fun _ _ => ConditionallyBisim
  |}.
Next Obligation.
  constructor.
  - intros a. constructor.
  - intros a b. constructor. assumption.
  - intros a b c ? ?. econstructor; eassumption.
Qed.
Next Obligation.
  constructor.
  - intros a. constructor.
  - intros a b c ? ?. econstructor; eassumption.
Qed.

Theorem soundness_of_conditionally :
  forall {E I : Type -> Type} {A : Type}
    {EqI : forall (A : Type), relation (I A) } `{forall A, Equivalence (EqI A) }
    {D : Monad__Dict I}
    {_ : @MonadLaws I EqI (monaddict_functor _ D) (monaddict_applicative _ D)
           (monaddict_monad _ D)}
    {_ : @MonadCongruenceLaws I EqI (monaddict_functor _ D)
           (monaddict_applicative _ D) (monaddict_monad _ D)}
    (interpE : forall A, E A -> I A) (x y : ReifiedSelective E A)
    (Hbisim : Bisim (Adverb:=ReifiedConditionally__Adverb) x y),
    EqI _ (interp (C0:=D)(EqI:=EqI)(AdverbSim:=ReifiedSelectiveSim) interpE x)
      (interp (C0:=D)(EqI:=EqI)(AdverbSim:=ReifiedSelectiveSim) interpE y).
Proof.
  intros.
  induction Hbisim.
  - unfold interp. cbn.
    apply bind_cong.
    + apply H1.
    + apply IHHbisim1.
    + intros. destruct a.
      * unfold monaddict_fmap.
        pose proof bind_cong. unfold ">>=" in H2.
        specialize (H2 I EqI _ _ _ H1 (A -> B) B).
        unfold monaddict_monad in H2. apply H2.
        -- rewrite <- IHHbisim2. reflexivity.
        -- reflexivity.
      * reflexivity.
  - unfold interp. cbn.
    rewrite monad_left_id; [|assumption].
    unfold monaddict_fmap.
    pose proof bind_cong. unfold ">>=" in H2.
    specialize (H2 I EqI _ _ _ H1 (A + A) A).
    unfold monaddict_monad in H2. apply H2.
    + reflexivity.
    + intros. destruct a0.
      * pose proof monad_left_id. unfold ">>=" in H3.
        specialize (H3 I EqI _ _ _ H0 (A -> A) A).
        unfold monaddict_monad in H3. rewrite H3.
        reflexivity.
      * reflexivity.
  - unfold interp. cbn.
    rewrite !monad_left_id.
    pose proof monad_assoc as assoc. unfold ">>=" in assoc.
    specialize (assoc I EqI _ _ _ H0).
    unfold monaddict_monad in assoc.
    pose proof monad_left_id as left_id. unfold ">>=" in left_id.
    specialize (left_id I EqI _ _ _ H0).
    unfold monaddict_monad in left_id.
    pose proof left_id as left_id'.
    unfold return_ in left_id'.
    destruct x.
    + unfold monaddict_fmap. unfold ">>=", monaddict_monad.
      rewrite !assoc.
      pose proof (assoc ((B -> B) -> (B -> B) + B) ((B -> B) + B) B) as Ht;
        rewrite !Ht; clear Ht.
      rewrite !left_id.
      pose proof (left_id ((B -> B) -> (B -> B) + B) B) as Ht; rewrite !Ht; clear Ht.
      rewrite !assoc, !left_id.
      pose proof (left_id (((B -> B) -> B -> B) -> ((B -> B) -> B -> B) + (B -> B)) B) as Ht;
        rewrite !Ht; clear Ht.
      rewrite !assoc, !left_id.
      pose proof (left_id ((B -> B) -> B -> B) B) as Ht; rewrite !Ht; clear Ht.
      unfold "∘". rewrite !left_id'.
      rewrite !assoc, !left_id.
      pose proof (left_id ((B -> B) -> ((B -> B) -> B -> B) -> B -> B) B) as Ht.
      rewrite !Ht; clear Ht.
      rewrite !assoc, !left_id.
      pose proof (left_id (B -> B -> B) B) as Ht; rewrite !Ht; clear Ht.
      rewrite !assoc.
      pose proof (left_id (A + B) B) as Ht; rewrite !Ht; clear Ht.
      rewrite !assoc.
      pose proof bind_cong as cong. unfold ">>=" in cong.
      specialize (cong I EqI _ _ _ H1).
      unfold monaddict_monad in cong. apply cong; [reflexivity|]. intros.
      rewrite !left_id'. repeat rewrite !assoc, !left_id.
      rewrite !assoc. apply cong; [reflexivity|]. intros.
      rewrite !left_id'. reflexivity.
    + unfold monaddict_fmap. unfold ">>=", monaddict_monad.
      repeat rewrite !assoc, !left_id. unfold "∘".
      rewrite !left_id'. repeat rewrite !assoc, !left_id.
      rewrite !left_id'. repeat rewrite !assoc, !left_id.
      rewrite !left_id'. reflexivity.
    + assumption.
  - unfold interp. cbn. unfold monaddict_fmap. unfold ">>=", monaddict_monad.
    pose proof monad_assoc as assoc. unfold ">>=" in assoc.
    specialize (assoc I EqI _ _ _ H0).
    unfold monaddict_monad in assoc.
    pose proof monad_left_id as left_id. unfold ">>=" in left_id.
    specialize (left_id I EqI _ _ _ H0).
    unfold monaddict_monad in left_id.
    pose proof left_id as left_id'.
    unfold return_ in left_id'.
    repeat rewrite !assoc, !left_id. rewrite !assoc.
    pose proof monad_right_id as right_id.
    specialize (right_id I EqI _ _ _ H0).
    pose proof bind_cong as cong. unfold ">>=" in cong.
    specialize (cong I EqI _ _ _ H1).
    unfold monaddict_monad in cong. apply cong; [reflexivity|]. intros [].
    + unfold "∘". rewrite !assoc, !left_id'. simpl.
      rewrite H2. repeat rewrite !assoc, !left_id.
      rewrite !assoc. apply cong; [reflexivity|]. intros.
      destruct a0.
      * rewrite !assoc, !left_id'. rewrite H3. simpl.
        repeat rewrite !assoc, !left_id. rewrite !assoc.
        apply cong; [reflexivity|]. intros.
        rewrite !left_id'. rewrite H4. cbn. reflexivity.
      * rewrite !left_id, !left_id'. rewrite H3. simpl.
        reflexivity.
    + unfold "∘". rewrite !left_id'.
      rewrite H2. rewrite !left_id. reflexivity.
  - unfold interp. cbn. unfold monaddict_fmap. unfold ">>=", monaddict_monad.
    pose proof monad_assoc as assoc. unfold ">>=" in assoc.
    specialize (assoc I EqI _ _ _ H0).
    unfold monaddict_monad in assoc.
    pose proof monad_left_id as left_id. unfold ">>=" in left_id.
    specialize (left_id I EqI _ _ _ H0).
    unfold monaddict_monad in left_id.
    pose proof left_id as left_id'.
    unfold return_ in left_id'.
    repeat rewrite !assoc, !left_id. rewrite !assoc.
    pose proof monad_right_id as right_id.
    specialize (right_id I EqI _ _ _ H0).
    pose proof (right_id _ (@interpS E I (monaddict_functor I D)
                              (monaddict_applicative I D)
                              (fun (r : Type) (k : Monad__Dict I -> r) => k D) EqI B interpE a)).
    etransitivity; [|apply H2].
    pose proof bind_cong as cong. unfold ">>=" in cong.
    specialize (cong I EqI _ _ _ H1).
    unfold monaddict_monad in cong.
    unfold ">>=". unfold monaddict_monad.
    apply cong; [reflexivity|]. intros.
    unfold "∘". rewrite left_id'. reflexivity.
  - unfold interp. cbn. reflexivity.
  - unfold interp. cbn. symmetry. assumption.
  - unfold interp. cbn. etransitivity; eassumption.
Qed.
