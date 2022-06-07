Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.

From Coq Require Import
     List
     Psatz
     Relation_Definitions
     RelationClasses
.

Require Import GHC.Base.
Require Import Fix.
Require Import Tactics.Tactics.
Require Import ClassesOfFunctors.DictDerive.

Require Import Nat.

Open Scope nat_scope.

(** * Deep Embedding *)

Section FMAP.

Definition ret {m}`{Monad m}{a} (x:a) : m a := return_  x.

(* begin fmap_monad *)
Definition fmap_monad {m} `{Monad m} {a b} (f : a -> b) (x : m a) : m b :=
  x >>= (fun y => ret (f y)).
(* end fmap_monad *)
(* begin fmap_ap *)
Definition fmap_ap {t}`{Applicative t}{a b} (f: a -> b) (x : t a) : t b :=
  liftA2 id (pure f) x.
(* end fmap_ap *)

End FMAP.
Reset FMAP.

Definition var := nat.

Section Deep.

(* begin deep_embedding *)
Inductive term :=
| Var (v : var)
| Lit (b : bool)
| Neg (t : term)
| And (t : term) (u : term)
| Or (t : term) (u : term).
(* end deep_embedding *)


Example term1 := And (Var 0) (Var 0).
Example term2 := Var 0.
Example term3 := And (Var 0) (Lit true).


(* begin depth *)
Fixpoint depth (t : term) : nat :=
  match t with
   | Var _ => 0
   | Lit _ => 0
   | Neg t => depth t + 1
   | And t u => max (depth t) (depth u) + 1
   | Or t u => max (depth t) (depth u) + 1
   end.
(* end depth *)

(* begin numVar *)
Fixpoint numVar (t : term) : nat :=
  match t with
   | Var _ => 1
   | Lit _ => 0
   | And t u => (numVar t) + (numVar u)
   | Or t u => (numVar t) + (numVar u)
   | Neg t => numVar t
   end.
(* end numVar *)

Lemma times_two : forall n, n * 2 = n + n.
Proof. intros. lia. Qed.
Lemma plus_le_compat : forall n1 m1 n2 m2,
    n1 <= n2 -> m1 <= m2 -> n1 + m1 <= n2 + m2.
Proof. intros. lia. Qed.

(* A proof about syntax *)
Theorem heightAndVar : forall (l : term),
    numVar l <= Nat.pow 2 (depth l).
Proof.
  induction l; simpl; try lia.
  + transitivity (2 ^ depth l); auto.
    apply Nat.pow_le_mono_r; auto.
    lia.
  + rewrite Nat.pow_add_r; simpl.
    rewrite times_two.
    apply plus_le_compat.
    ++ transitivity (2 ^ depth l1); auto.
       apply Nat.pow_le_mono_r; auto.
       apply Nat.le_max_l.
    ++ transitivity (2 ^ depth l2); auto.
       apply Nat.pow_le_mono_r; auto.
       apply Nat.le_max_r.
  + rewrite Nat.pow_add_r; simpl.
    rewrite times_two.
    apply plus_le_compat.
    ++ transitivity (2 ^ depth l1); auto.
       apply Nat.pow_le_mono_r; auto.
       apply Nat.le_max_l.
    ++ transitivity (2 ^ depth l2); auto.
       apply Nat.pow_le_mono_r; auto.
       apply Nat.le_max_r.
Qed.

End Deep.

(** * Shallow Embedding *)

(* begin reader *)
Definition Reader (A : Type) : Type :=
  (var -> bool) -> A.
Definition ret {A} (a : A) : Reader A :=
  fun _ => a.
Definition bind {A B} (m : Reader A)
  (k : A -> Reader B) : Reader B :=
    fun v => k (m v) v.
Definition ask (k : var) : Reader bool :=
  fun m => m k.
(* end reader *)

Definition Monad__Dict__Reader : Monad__Dict Reader :=
  {| op_zgzg____ := fun _ _ m k => bind m (fun _ => k) ;
     op_zgzgze____ := fun _ _ => bind ;
     return___ := fun _ => ret |}.

Global Instance RMFunctor : Functor Reader :=
  monaddict_functor _ Monad__Dict__Reader.

Global Instance RMApplicative : Applicative Reader :=
  monaddict_applicative _ Monad__Dict__Reader.

Global Instance RMMonad : Monad Reader :=
  monaddict_monad _ Monad__Dict__Reader.

(* begin eq_Reader *)
Definition eq_Reader {A} : Reader A -> Reader A -> Prop :=
  fun f1 f2 => forall m, f1 m = f2 m.
(* end eq_Reader *)

Goal forall A (a b : Reader A) (k : A -> A -> A),
    eq_Reader (bind a (fun x => bind b (fun y => ret (k x y))))
      (bind b (fun y => bind a (fun x => ret (k x y)))).
Proof.
  intros. intros m. unfold bind, ret. reflexivity.
Qed.

(* The translation from B to shallow embeddings. Because we have already modeled
   B in Coq using deep embeddings, the translation function coincides with the
   interpreter from deep embeddings to the reader monad. This would not be the
   case if B is defined in another language and there is no deep embedding of
   B. *)

(* begin interp_Reader *)
Fixpoint interp_Reader (t : term) : Reader bool :=
  match t with
  | Var x => ask x
  | Lit b => return_ b
  | And t u => (interp_Reader t) >>=
                   (fun t' => (interp_Reader u) >>=
                                (fun u' => return_ (andb t' u')))
  | Or t u => (interp_Reader t) >>=
                   (fun t' => (interp_Reader u) >>=
                                (fun u' => return_ (orb t' u')))
  | Neg t => (interp_Reader t) >>= (fun t' => return_ (negb t'))
  end.
(* end interp_Reader *)


Fixpoint applicative_denote (t : term) : Reader bool :=
  match t with
  | Var x => ask x
  | Lit b => return_ b
  | And t u => liftA2 andb (applicative_denote t) (applicative_denote u)
  | Or t u => liftA2 orb (applicative_denote t) (applicative_denote u)
  | Neg t => fmap negb (applicative_denote t)
  end.

(* begin eq_Deep *)
Definition eq_Deep t1 t2 := eq_Reader (interp_Reader t1) (interp_Reader t2).
(* end eq_Deep *)

Example lemma1 : eq_Deep term1 term2.
cbv.  intro m. destruct (m 0); auto.
Qed.

Example lemma2 : eq_Deep term3 term2.
cbv.  intro m. destruct (m 0); auto.
Qed.


Example lemma3 : forall x y, eq_Deep (And x y) (And y x).
Proof.
  intros.
  induction x; induction y.
  all: unfold eq_Deep; cbn.
  all: unfold bind, ask, ret, eq_Reader.
  all: intuition.
Qed.

Reset bind.

(** * Freer Monad Embedding *)

Section Freer.

(* begin Freer *)
Inductive FreerMonad (E : Type -> Type) R :=
| Ret (r : R)
| Bind {X} (m : E X)
    (k : X -> FreerMonad E R).
Fixpoint bind {E A B} (m : FreerMonad E A)
  (k : A -> FreerMonad E B) : FreerMonad E B :=
  match m with
  | Ret r => k r
  | Bind m' k' =>
      Bind m' (fun a => bind (k' a) k) end.
Variant DataEff : Type -> Type :=
| GetData (v : var) : DataEff bool.
(* end Freer *)

Definition embed {E A} (e : E A) : FreerMonad E A :=
  Bind e Ret.

Definition fmap {E : Type -> Type}{a b} (f : a -> b)
    (x : FreerMonad E a) : FreerMonad E b :=
  bind x (fun y => Ret (f y)).

Definition Monad__Dict__FreerMonad {E} : Monad__Dict (FreerMonad E).
econstructor.
exact (fun {a}{b} x y => bind x (fun _ => y)).
exact (@bind E).
exact (@Ret E).
Defined.

Global Instance FreerMonadFunctor {E} : Functor (FreerMonad E) :=
  monaddict_functor _ Monad__Dict__FreerMonad.

Global Instance FreerMonadApplicative {E} : Applicative (FreerMonad E) :=
  monaddict_applicative _ Monad__Dict__FreerMonad.

Global Instance FreerMonadMonad {E} : Monad (FreerMonad E) :=
  monaddict_monad _ Monad__Dict__FreerMonad.

(* The translation from B to freer monads. Because we have already modeled B in
   Coq using deep embeddings, the translation function coincides with the
   interpreter from deep embeddings to freer monads. This would not be the case
   if B is defined in another language and there is no deep embedding of B. *)

Fixpoint monad_denote (t : term) : FreerMonad DataEff bool :=
  match t with
  | Var x => Bind (GetData x) Ret
  | Lit b => return_ b
  | And t u => (monad_denote t) >>=
                   (fun t' => (monad_denote u) >>=
                                (fun u' => return_ (andb t' u')))
  | Or t u => (monad_denote t) >>=
                   (fun t' => (monad_denote u) >>=
                                (fun u' => return_ (orb t' u')))
  | Neg t => (monad_denote t) >>= (fun t' => return_ (negb t'))
  end.

Inductive eq_FreerMonad {E}{A} : FreerMonad E A -> FreerMonad E A -> Prop :=
  | eq_Ret : forall r, eq_FreerMonad r r
  | eq_Bind : forall X (m: E X) k1 k2,
      (forall x, eq_FreerMonad (k1 x) (k2 x)) ->
      eq_FreerMonad (Bind m k1) (Bind m k2).


Example lemma1 : eq_FreerMonad (monad_denote term1) (monad_denote term2).
cbn.
eapply eq_Bind.
intro x.
(* Not provable. Intentionally abort. *)
Abort.

Example lemma2 : eq_FreerMonad (monad_denote term3) (monad_denote term2).
cbv.
eapply eq_Bind.
intro x. destruct x; eapply eq_Ret.
Qed.


Example lemma3 : forall x y,  eq_FreerMonad (monad_denote (And x y)) (monad_denote (And y x)).
Proof.
intros.
cbn.
(* Not provable. Intentionally abort. *)
Abort.


Reset bind.
Reset fmap.
End Freer.

(** * Reified Applicative Embedding *)

Section Applicative.

(* begin applicative *)
Inductive ReifiedApp (E : Type -> Type) R :=
  | EmbedA (e : E R)
  | Pure (r : R)
  | LiftA2 {X Y} (f : X -> Y -> R)
    (a : ReifiedApp E X) (b : ReifiedApp E Y).
(* end applicative *)

Definition fmap {E X Y} : (X -> Y)
    -> ReifiedApp E X -> ReifiedApp E Y :=
  fun f x => LiftA2 id (Pure f) x.

Global Instance ReifiedAppFunctor {E} : Functor (ReifiedApp E).
cbv. intros r X. apply X. econstructor. exact (@fmap E).
exact (fun {a}{b} x b => fmap (fun _ => x) b).
Defined.

Global Instance ReifiedAppApplicative {E} : Applicative (ReifiedApp E).
intros r X. apply X. constructor.
- intros a b c. exact LiftA2.
- intros a b. exact (LiftA2 id).
- intros a b. exact (LiftA2 (fun _ x => x)).
- intros a. exact Pure.
Defined.

(* The translation from B to reified applicative. Because we have already
   modeled B in Coq using deep embeddings, the translation function coincides
   with the interpreter from deep embeddings to reified applicative. This
   would not be the case if B is defined in another language and there is no
   deep embedding of B. *)

Fixpoint toReifiedApp ( t : term ) : ReifiedApp DataEff bool :=
  match t with
  | Var v => EmbedA (GetData v)
  | Lit x => Pure x
  | And a b => LiftA2 andb (toReifiedApp a) (toReifiedApp b)
  | Or a b => LiftA2 orb (toReifiedApp a) (toReifiedApp b)
  | Neg b => fmap negb (toReifiedApp b)
  end.

(* begin eq_ReifiedApp *)
Inductive eq_ReifiedApp {E R} : ReifiedApp E R -> ReifiedApp E R -> Prop :=

  | eq_ReifiedApp_Refl : forall  (a: ReifiedApp E R), eq_ReifiedApp a a
  | eq_ReifiedApp_Sym : forall  (a b: ReifiedApp E R), eq_ReifiedApp a b -> eq_ReifiedApp b a
  | eq_ReifiedApp_Trans : forall  (a b c: ReifiedApp E R), eq_ReifiedApp a b -> eq_ReifiedApp b c -> eq_ReifiedApp a c

  | Congruence : forall {X Y} (f: X -> Y -> R) v1 v2 g1 g2,
      eq_ReifiedApp (LiftA2 f v1 g1) (LiftA2 f v2 g2)
  | LeftIdentity : forall {X} (a: X) (b: ReifiedApp E R) f,
      (forall y, (fun _ x => x) a y = f a y) ->
      eq_ReifiedApp (LiftA2 f (Pure a) b) b
  | RightIdentity : forall {X} (a: ReifiedApp E R) (b: X) f,
      (forall x, (fun x _ => x) x b = f x b) ->
      eq_ReifiedApp (LiftA2 f a (Pure b)) a
  (* not included in "free" applicative, but can be added *)
  | LiftA2_Comm : forall {X Y} (f:X -> Y -> R) h v g,
      (forall x y, f x y = h y x) ->
      eq_ReifiedApp (LiftA2 f v g) (LiftA2 h g v).
(* end eq_ReifiedApp *)

(* Cannot show, as desired. *)
Example lemma1 : eq_ReifiedApp (toReifiedApp term1) (toReifiedApp term2).
cbn.
Abort.

Example lemma2 : eq_ReifiedApp (toReifiedApp term3) (toReifiedApp term2).
cbn.
apply RightIdentity. intros. destruct x; tauto.
Qed.

Example lemma3 : forall x y,  eq_ReifiedApp (toReifiedApp (And x y)) (toReifiedApp (And y x)).
Proof.
intros.
cbn.
eapply LiftA2_Comm.
intros. destruct x0; destruct y0; auto.
Qed.

(* begin app_depth *)
Fixpoint app_depth {E A} (t : ReifiedApp E A) : nat :=
  match t with
   | EmbedA _ => 0
   | Pure _ => 0
   | LiftA2 _ t u => 1 + max (app_depth t) (app_depth u)
   end.
(* end app_depth *)

(* begin app_numVar *)
Fixpoint app_numVar {E A} (t : ReifiedApp E A) : nat :=
  match t with
   | EmbedA _ => 1
   | Pure _ => 0
   | LiftA2 _ t u => (app_numVar t) + (app_numVar u)
   end.
(* end app_numVar *)

Lemma same_depth : forall t, depth t = app_depth (toReifiedApp t).
Proof.
  induction t; simpl; auto.
  rewrite IHt. lia.
  rewrite IHt1. rewrite IHt2. lia.
  rewrite IHt1. rewrite IHt2. lia.
Qed.

Lemma same_numVar : forall t, numVar t = app_numVar (toReifiedApp t).
Proof.
  induction t; simpl; auto.
Qed.

Theorem app_heightAndVar : forall E R (l : ReifiedApp E R),
    app_numVar l <= Nat.pow 2 (app_depth l).
Proof.
  intros.
  induction l.
  simpl. auto.
  simpl. auto.
  simpl. apply plus_le_compat.
  transitivity (2 ^ app_depth l1); auto.
  apply Nat.pow_le_mono_r; auto.
  apply Nat.le_max_l.
  transitivity (2 ^ app_depth l2); auto.
  rewrite <- plus_n_O.
  apply Nat.pow_le_mono_r; auto.
  apply Nat.le_max_r.
Qed.

Definition CostSem A := (var -> (bool * nat)%type) -> (A * nat)%type.

Definition pureC {A} (a : A) : CostSem A := fun m => (a, 0).

Definition parC {A B C}
  (f : A -> B -> C) (a : CostSem A) (b : CostSem B) : CostSem C :=
  fun m => match a m, b m with
        | (a', n1), (b', n2) =>
            let n := match n1, n2 with
                     (* No effect on one side, go through with no extra cost *)
                     | O, m => m
                     | m, O => m
                     (* Effects on both sides, computation required *)
                     | m1, m2 => 1 + max m1 m2
                     end in
            (f a' b', n)
        end.

Definition interpCost {E A} (a : ReifiedApp E A)
  (interpE : forall A, E A -> CostSem A) : CostSem A :=
  let fix go {A} (a : ReifiedApp E A) :=
    match a with
    | EmbedA e => interpE _ e
    | Pure a => pureC a
    | LiftA2 f a b => parC f (go a) (go b)
    end in
  go a.

Definition interpDataEff (A : Type) (e : DataEff A) : CostSem A :=
  match e with
  | GetData v => fun m => m v
  end.

(* Cannot show, as desired. *)
Theorem assoc : forall (x y a b : var),
    eq_ReifiedApp (toReifiedApp (And (And (And (Var x) (Var y)) (Var a)) (Var b)))
      (toReifiedApp (And (And (Var x) (Var y)) (And (Var a) (Var b)))).
Proof.
  intros. cbn.
Abort.

(* Indeed, there exists a cost semantics where associativity is not desired. *)
Theorem notAssoc : forall (x y a b : var) (env : var -> bool),
  exists (c : var -> nat), forall m,
    (forall v, m v = (env v, c v)) ->
    interpCost (toReifiedApp
                  (And (And (And (Var x) (Var y)) (Var a)) (Var b))) (@interpDataEff) m <>
      interpCost (toReifiedApp
                    (And (And (Var x) (Var y)) (And (Var a) (Var b)))) (@interpDataEff) m.
Proof.
  intros. cbn. unfold parC, pureC, interpDataEff.
  exists (fun _ => 1). intros.
  rewrite !H. intro. inversion H0.
Qed.

End Applicative.
