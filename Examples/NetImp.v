Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Contextual Implicit.

From Coq Require Import
     List
     Psatz
     Relation_Definitions
     RelationClasses
     Morphisms
.


Require Import GHC.Base.
Require Import Fix.
Require Import Tactics.Tactics.
Require Import ClassesOfFunctors.FunctorPlus.
Require Import ClassesOfFunctors.AppKleenePlus.
Require Import ClassesOfFunctors.DictDerive.

(** * NetImp

    We first define the NetImp language used to implement the web server shown
    in Fig. 15(a).  *)

Record Connection : Set :=
  MkConn { id : nat ;
           state : nat }.

Definition var : Set -> Set := fun _ => nat.

Inductive exp : Set -> Set :=
| expr {A : Set} : A -> exp A
| avar {A : Set} : var A -> exp (var A)
| deref {A : Set} : var A -> exp A
| proj : nat -> var Connection -> exp nat
| record : exp nat -> exp nat -> exp Connection
| beq : exp nat -> exp nat -> exp bool
| not : exp bool -> exp bool.

Inductive ev : Set -> Set :=
| accept : ev nat
| read : exp nat -> ev nat
| write : exp nat -> exp nat -> ev nat.

Inductive command : Set :=
| Assign {A : Set} : exp (var A) -> exp A -> command
| Run : exp (var nat) -> ev nat -> command
| LAdd : var Connection -> var (list (var Connection)) -> command
| UpdateProj : nat -> exp (var Connection) -> exp nat -> command
| Seq : command -> command -> command
| If : exp bool -> command -> command -> command
| For : var (var Connection) -> var (list (var Connection)) -> command -> command
| Skip : command.

Definition idP := 0.
Definition stateP := 1.

Notation "v ::= e" := (Assign v e) (at level 42).
Notation "v ::<- e" := (Run v e) (at level 42).
Notation "v ::++ e" := (LAdd v e) (at level 42).
Notation "v '::=id' e" := (UpdateProj idP v e) (at level 42).
Notation "v '::=state' e" := (UpdateProj stateP v e) (at level 42).
Notation "c1 ;; c2" := (Seq c1 c2) (at level 43, right associativity).
Notation "'IFB' b 'THEN' c 'END'" := (If b c Skip) (at level 44).
Notation "'IFB' b 'THEN' c1 'ELSE' c2 'END'" := (If b c1 c2) (at level 44).
Notation "'FOR' x 'IN' y 'DO' c 'END'" := (For x y c) (at level 45).


(* local variables *)
Definition y : var (var Connection) := 1.
Definition r : var nat := 5.
Definition newconn : var nat := 10.
Definition newconn_rec : var Connection := 15.

(* global variables *)
Definition s : var nat := 20.
Definition conns : var (list (var Connection)) := 21.


Definition State := nat.
Definition READING := 0.
Definition WRITING := 1.
Definition CLOSED := 2.

(** * A test program. *)
Definition process_test : command :=
  avar s ::= expr 0 ;;
  avar newconn ::<- accept.

(** * The Implementation.

    This is the one shown in Fig. 15(a). *)

Definition process : command :=
  avar newconn ::<- accept ;;
  IFB (not (beq (deref newconn) (expr 0))) THEN
      avar newconn_rec ::= record (deref newconn) (expr READING) ;;
      conns ::++ newconn_rec
  END ;;
  FOR y IN conns DO
      IFB (beq (proj stateP y) (expr WRITING)) THEN
          avar r ::<- write (proj idP y) (deref s) ;;
          deref y ::=state expr CLOSED
      END ;;
      IFB (beq (proj stateP y) (expr READING)) THEN
          avar r ::<- read (proj idP y) ;;
          IFB (beq (deref r) (expr 0)) THEN
              deref y ::=state expr CLOSED
          ELSE
               avar s ::= deref r ;;
               deref y ::=state expr WRITING
          END
      END
  END.

(** * Effects *)

Variant NetworkEff (K : Set -> Set) : Set -> Set :=
| AcceptE : NetworkEff K nat
| ReadE : nat -> NetworkEff K nat
| WriteE : nat -> nat -> NetworkEff K nat.

Arguments AcceptE {_}.
Arguments ReadE {_}.
Arguments WriteE {_}.

Variant MemoryEff (K : Set -> Set) : Set -> Set :=
| SetE {A : Set} : var A -> A -> MemoryEff K unit
| GetE {A : Set}: var A -> MemoryEff K A.

Arguments SetE {_} {_}.
Arguments GetE {_} {_}.

Variant FailEff (K : Set -> Set) : Set -> Set :=
| ErrorE {A : Set} : FailEff K A.

Arguments ErrorE {_} {_}.


Definition fmap1_NetWorkEff {F G : Set -> Set} {A : Set}
           (f : forall X, F X -> G X)
           (a : NetworkEff F A) : NetworkEff G A :=
  match a with
  | AcceptE => AcceptE
  | ReadE c => ReadE c
  | WriteE c n => WriteE c n
  end.

#[global] Program Instance Functor1__NetworkEff : Functor1 NetworkEff :=
  {| fmap1 := @fmap1_NetWorkEff |}.
Next Obligation.
  intros x; destruct x; reflexivity.
Qed.
Next Obligation.
  intros x; destruct x; reflexivity.
Qed.

Definition fmap1_MemoryEff {F G : Set -> Set} {A : Set}
           (f : forall X, F X -> G X)
           (a : MemoryEff F A) : MemoryEff G A :=
  match a with
  | SetE variable va => SetE variable va
  | GetE variable => GetE variable
  end.

#[global] Program Instance Functor1__MemoryEff : Functor1 MemoryEff :=
  {| fmap1 := @fmap1_MemoryEff |}.
Next Obligation.
  intros x; destruct x; reflexivity.
Qed.
Next Obligation.
  intros x; destruct x; reflexivity.
Qed.

Definition fmap1_FailEff {F G : Set -> Set} {A : Set}
           (f : forall X, F X -> G X)
           (a : FailEff F A) : FailEff G A :=
  match a with
  | ErrorE => ErrorE
  end.

#[global] Program Instance Functor1__FailEff : Functor1 FailEff :=
  {| fmap1 := @fmap1_FailEff |}.
Next Obligation.
  intros x; destruct x; reflexivity.
Qed.
Next Obligation.
  intros x; destruct x; reflexivity.
Qed.

(** Smart constructors for effects. *)
Section SmartConstructors.

  Variable F : (Set -> Set) -> Set -> Set.
  Context `{Functor1 F}.

  Section NetworkConstructors.

    Context `{NetworkEff -≪ F}.

    Definition acceptE : Fix1 F nat :=
      @inF1 _ _ _ (inj1 AcceptE).

    Definition readE (conn : nat) : Fix1 F nat :=
      @inF1 _ _ _ (inj1 (ReadE conn)).

    Definition writeE (conn : nat) (val : nat) : Fix1 F nat :=
      @inF1 _ _ _ (inj1 (WriteE conn val)).

  End NetworkConstructors.

  Section MemoryConstructors.

    Context `{MemoryEff -≪ F}.
    Variable A : Set.

    Definition setE (v : var A) (val : A) : Fix1 F unit :=
      @inF1 _ _ _ (inj1 (SetE v val)).

    Definition getE (v : var A) : Fix1 F A :=
      @inF1 _ _ _ (inj1 (GetE v)).

  End MemoryConstructors.

  Section FailConstructors.

    Context `{FailEff -≪ F}.
    Variable A : Set.

    Definition errorE : Fix1 F A :=
      @inF1 _ _ _ (inj1 ErrorE).

  End FailConstructors.

End SmartConstructors.

(** * Program Adverbs. *)

Require Import Adverb.Composable.Purely.
Require Import Adverb.Composable.Dynamically.

Definition LanAdverbs := PurelyAdv ⊕ DynamicallyAdv ⊕
                                   NetworkEff ⊕ MemoryEff ⊕ FailEff.

Definition Lan : Set -> Set := Fix1 LanAdverbs.


Definition getProj (n : nat) (c : Connection) : Lan nat :=
  if (Nat.eqb n idP) then
    pure (id c)
  else if (Nat.eqb n stateP) then
         pure (state c)
       else @errorE _ _ _ _.

(** Denoting [exp] using [Lan]. *)
Fixpoint denote_exp {A : Set} (e : exp A) : Lan A.
  destruct e.
  - exact (pure a).
  - exact (pure v).
  - exact (@getE _ _ _ _ v).
  - exact (@getE _ _ _ _ v >>= getProj n).
  - exact (@denote_exp _ e1 >>=
                       (fun val1 =>
                          @denote_exp _ e2 >>=
                                      (fun val2 => pure (MkConn val1 val2)))).
  - exact (@denote_exp _ e1 >>=
                       (fun val1 =>
                          @denote_exp _ e2 >>=
                                      (fun val2 => pure (Nat.eqb val1 val2)))).
  - exact (fmap negb (@denote_exp _ e)).
Defined.

(** Denoting [av] using [Lan]. *)
Definition denote_ev {A : Set} (e : ev A) : Lan nat :=
  match e with
  | accept => @acceptE _ _ _
  | read e => @denote_exp _ e >>= @readE _ _ _
  | write c e => @denote_exp _ c >>= (fun conn =>
                   (@denote_exp _ e >>= @writeE _ _ _ conn))
  end.

(** Denoting [command] using [Lan]. *)
Fixpoint denote_command (c : command) : Lan unit.
  destruct c.
  - (* Assign *)
    refine (@denote_exp _ e >>=
                            (fun v => @denote_exp _ e0 >>= _)).
    exact (@setE _ _ _ _ v).
  - (* Run *)
    exact (@denote_exp _ e >>=
               (fun v => @denote_ev _ e0 >>= @setE _ _ _ _ v)).
  - (* LAdd *)
    refine (@getE _ _ _ _ v0 >>= _).
    refine (fun xs => @setE _ _ _ _ v0 (v :: xs)).
  - (* UpdateProj *)
    refine (@denote_exp _ e >>= (fun v => _)).
    refine (@getE _ _ _ _ v >>=
                  (fun c => @denote_exp _ e >>= (fun val => _))).
    exact (if (Nat.eqb n idP) then
              @setE _ _ _ _ v (MkConn val (state c))
            else if (Nat.eqb n stateP) then
                   @setE _ _ _ _ v (MkConn (id c) val)
                 else @errorE _ _ _ _).
  - (* Seq *)
    exact (denote_command c1 >> denote_command c2).
  - (* If *)
    exact (@denote_exp _ e >>= (fun b => if b then denote_command c1
                                      else denote_command c2)).
  - (* For *)
    refine (@getE _ _ _ _ v0 >>= (fun xs => _)).
    (** The loop variable is a pointer. *)
    pose (@mapM _ _ _ Functor__DynamicallyAdv
                Applicative__DynamicallyAdv
                Monad__DynamicallyAdv (fun v' =>
                   @setE _ _ _ _ v v' >> denote_command c) xs).
    exact (fmap (fun _ => tt) f).
  - (* Skip *)
    exact (pure tt).
Defined.

(** * Adverb Theories. *)

Require Import Eq.EqEq.
Require Import Eq.EqBindLaws.
Require Import Eq.EqBindK.
Require Import Eq.EqBindCong.

Unset Implicit Arguments.

Definition EqRel (D : (Set -> Set) -> Set -> Set)
           `{PurelyAdv -≪ D} `{DynamicallyAdv -≪ D} `{Functor1 D}
  := EqEq (F:=Fix1 D) ⊎ EqBindLaws ⊎ EqBindCong.

Set Implicit Arguments.

Definition EqLanRel := EqRel LanAdverbs.

Definition EqLan := FixRel EqLanRel.

#[global] Instance Equivalence_EqLan {A : Set} : Equivalence (@EqLan A).
typeclasses eauto.
Qed.

(** A test program written in adverbs. *)
Definition process_testEmbedded : Lan unit :=
  @setE _ _ _ _ s 0 >>
  @acceptE _ _ _ >>= (fun val =>
  @setE _ _ _ _ newconn val).

(** * Custom tactics. *)
(* In the case that the part before [>>=] are equal, we move on *)
Ltac forward :=
  apply eqBindCong; [reflexivity|intros].

Ltac simplify_rets :=
  repeat (rewrite ?(@PureRet LanAdverbs _ _ _),
      ?(@eqBindLeftId LanAdverbs _ _ _ EqLanRel _ _ _ _)).

(** * A test.

    We show that denoting [process_test] into [Lan] gives us
    [process_testEmbedded].  *)

Goal EqLan (@denote_command process_test) (@process_testEmbedded).
Proof.
  unfold process_test, process_testEmbedded.
  unfold denote_command, denote_exp.
  assert (forall (a b : Lan unit) , (a >> b) = (a >>= (fun _ => b)))
    by reflexivity.
  rewrite !H.
  simplify_rets. unfold denote_exp.
  simplify_rets. forward.
  simplify_rets. unfold denote_ev, "∘". reflexivity.
Qed.

(** * The specification language.

    We only refine the commands. We reuse [exp] and [ev] from NetImp. *)

Inductive commandS : Set :=
| AssignS {A : Set} : exp (var A) -> exp A -> commandS
| RunS : exp (var nat) -> ev nat -> commandS
| LAddS : var Connection -> var (list (var Connection)) -> commandS
| UpdateProjS : nat -> exp (var Connection) -> exp nat -> commandS
| SeqS : commandS -> commandS -> commandS
| IfS : exp bool -> commandS -> commandS -> commandS
| SomeS : commandS -> commandS
| OrS : commandS -> commandS -> commandS
| OneOfS : var (list (var Connection)) ->
           var (var Connection) -> commandS -> commandS
| SkipS : commandS.

Declare Scope spec_scope.

Notation "v ::= e" := (AssignS v e) (at level 42) : spec_scope.
Notation "v ::<- e" := (RunS v e) (at level 42) : spec_scope.
Notation "v ::++ e" := (LAddS v e) (at level 42) : spec_scope.
Notation "v '::=id' e" := (UpdateProjS idP v e) (at level 42) : spec_scope.
Notation "v '::=state' e" := (UpdateProjS stateP v e) (at level 42) : spec_scope.
Notation "c1 ;; c2" := (SeqS c1 c2) (at level 43, right associativity) : spec_scope.
Notation "'IFB' b 'THEN' c 'END'" := (IfS b c SkipS) (at level 44) : spec_scope.
Notation "'IFB' b 'THEN' c1 'ELSE' c2 'END'" := (IfS b c1 c2) (at level 44) : spec_scope.

Open Scope spec_scope.
Delimit Scope spec_scope with spec.

(** * The specification. *)

Definition processSpec' : commandS :=
  OrS (avar newconn ::<- accept ;;
      IFB (not (beq (deref newconn) (expr 0))) THEN
          avar newconn_rec ::= record (deref newconn) (expr READING) ;;
          conns ::++ newconn_rec
      END)
     (OneOfS (conns) y (
          OrS (IFB (beq (proj stateP y) (expr WRITING)) THEN
                  avar r ::<- write (proj idP y) (deref s) ;;
                  deref y ::=state expr CLOSED
              END)
             (IFB (beq (proj stateP y) (expr READING)) THEN
                  avar r ::<- read (proj idP y) ;;
                  IFB (beq (deref r) (expr 0)) THEN
                      deref y ::=state expr CLOSED
                  ELSE
                       avar s ::= deref r ;;
                       deref y ::=state expr WRITING
                  END
                  END))).

Definition processSpec := SomeS processSpec'.

(** * Adverbs for the specification language.

    We need a few additional adverbs for embedding the specification
    language. *)

Require Import Adverb.Composable.Nondeterministically.
Require Import Adverb.Composable.Repeatedly.

Definition SpecAdverbs := ReifiedKleenePlus ⊕ ReifiedPlus ⊕ LanAdverbs.

Definition Spec : Set -> Set := Fix1 SpecAdverbs.

Definition lanToSpec {A : Set} (l : Lan A) : Spec A :=
  foldFix1 (fun _ s => @inF1 _ _ _ (inj1 s)) l.

Definition getProjS (n : nat) (c : Connection) : Spec nat :=
  if (Nat.eqb n idP) then
    pure (id c)
  else if (Nat.eqb n stateP) then
         pure (state c)
       else @errorE _ _ _ _.

(** Re-denote [exp] and [ev] using the [Spec] adverb. *)

Fixpoint denote_expS {A : Set} (e : exp A) : Spec A.
  destruct e.
  - exact (pure a).
  - exact (pure v).
  - exact (@getE _ _ _ _ v).
  - exact (@getE _ _ _ _ v >>= getProjS n).
  - exact (@denote_expS _ e1 >>=
                       (fun val1 =>
                          @denote_expS _ e2 >>=
                                      (fun val2 => pure (MkConn val1 val2)))).
  - exact (@denote_expS _ e1 >>=
                       (fun val1 =>
                          @denote_expS _ e2 >>=
                                      (fun val2 => pure (Nat.eqb val1 val2)))).
  - exact (fmap negb (@denote_expS _ e)).
Defined.

Definition denote_evS {A : Set} (e : ev A) : Spec nat :=
  match e with
  | accept => @acceptE _ _ _
  | read e => @denote_expS _ e >>= @readE _ _ _
  | write c e => @denote_expS _ c >>= (fun conn =>
                   (@denote_expS _ e >>= @writeE _ _ _ conn))
  end.

(** Denoting [command]. *)

Fixpoint denote_command' (c : command) : Spec unit.
  destruct c.
  - (* Assign *)
    refine (@denote_expS _ e >>=
                            (fun v => @denote_expS _ e0 >>= _)).
    exact (@setE _ _ _ _ v).
  - (* Run *)
    exact (@denote_expS _ e >>=
               (fun v => @denote_evS _ e0 >>= @setE _ _ _ _ v)).
  - (* LAdd *)
    refine (@getE _ _ _ _ v0 >>= _).
    refine (fun xs => @setE _ _ _ _ v0 (v :: xs)).
  - (* UpdateProj *)
    refine (@denote_expS _ e >>= (fun v => _)).
    refine (@getE _ _ _ _ v >>=
                  (fun c => @denote_expS _ e >>= (fun val => _))).
    exact (if (Nat.eqb n idP) then
              @setE _ _ _ _ v (MkConn val (state c))
            else if (Nat.eqb n stateP) then
                   @setE _ _ _ _ v (MkConn (id c) val)
                 else @errorE _ _ _ _).
  - (* Seq *)
    exact (denote_command' c1 >> denote_command' c2).
  - (* If *)
    exact (@denote_expS _ e >>= (fun b => if b then denote_command' c1
                                      else denote_command' c2)).
  - (* For *)
    refine (@getE _ _ _ _ v0 >>= (fun xs => _)).
    (** The loop variable is a pointer. *)
    refine (foldr (fun vc s => @setE _ _ _ _ v vc >>
                                  denote_command' c >> s)
                  (pure tt) xs).
  - (* Skip *)
    exact (pure tt).
Defined.

(** Denoting [commandS]. *)

Fixpoint denote_command_Spec (c : commandS) : Spec unit.
  destruct c.
  - (* Assign *)
    refine (@denote_expS _ e >>=
                            (fun v => @denote_expS _ e0 >>= _)).
    exact (@setE _ _ _ _ v).
  - (* Run *)
    exact (@denote_expS _ e >>=
               (fun v => @denote_evS _ e0 >>= @setE _ _ _ _ v)).
  - (* LAdd *)
    refine (@getE _ _ _ _ v0 >>= _).
    refine (fun xs => @setE _ _ _ _ v0 (v :: xs)).
  - (* UpdateProj *)
    refine (@denote_expS _ e >>= (fun v => _)).
    refine (@getE _ _ _ _ v >>=
                  (fun c => @denote_expS _ e >>= (fun val => _))).
    exact (if (Nat.eqb n idP) then
              @setE _ _ _ _ v (MkConn val (state c))
            else if (Nat.eqb n stateP) then
                   @setE _ _ _ _ v (MkConn (id c) val)
                 else @errorE _ _ _ _).
  - (* Seq *)
    exact (denote_command_Spec c1 >> denote_command_Spec c2).
  - (* If *)
    exact (@denote_expS _ e >>= (fun b => if b then denote_command_Spec c1
                                           else denote_command_Spec c2)).
  - (* Some *)
    exact (@kleenePlus _ _ _ _ _ (denote_command_Spec c)).
  - (* Or *)
    exact (@kleenePlus _ _ _ _ _ (fplus (denote_command_Spec c1) (denote_command_Spec c2))).
  - (* OneOf *)
    refine (@getE _ _ _ _ v >>= (fun xs => _)).
    refine (@kleenePlus _ _ _ _ _
                        (foldr (fun vc s => fplus (@setE _ _ _ _ v0 vc >>
                                                (denote_command_Spec c)) s)
                               (pure tt) xs)).
  - (* Skip *)
    exact (pure tt).
Defined.

(** * The theories for the [Spec] adverb. *)

Require Import Eq.EqChoiceLaws.

Definition EqSpecRel := EqFplusLaws ⊎ (EqRel SpecAdverbs).

Definition EqSpec := FixRel EqSpecRel.

#[global] Instance Equivalence_EqSpec {A : Set} : Equivalence (@EqSpec A).
typeclasses eauto.
Qed.

Require Import Refines.RefinesEq.
Require Import Refines.RefinesOrder.
Require Import Refines.RefinesChoice.
Require Import Refines.RefinesStar.

Definition RefinesRel := RefinesEq (@EqSpec) _ ⊎ RefinesOrder ⊎
                                   RefinesFplusLaws ⊎ RefinesKleenePlusLaws ⊎
                                   EqBindCong.

Definition refines := FixRel RefinesRel.

#[global] Instance PreOrder_RefinesRel {A : Set} : PreOrder (@refines A).
typeclasses eauto.
Qed.


Notation "a ⊆ b" := (refines a b) (at level 50).

Close Scope spec_scope.

(** * The refinement proofs. *)

(** Our refinement proofs work as follow: we first abstract the program as three
    fragments. *)

Definition fragmentA : command :=
  avar newconn ::<- accept ;;
  IFB (not (beq (deref newconn) (expr 0))) THEN
      avar newconn_rec ::= record (deref newconn) (expr READING) ;;
      conns ::++ newconn_rec
  END.

Definition fragmentB : command :=
  IFB (beq (proj stateP y) (expr WRITING)) THEN
    avar r ::<- write (proj idP y) (deref s) ;;
    deref y ::=state expr CLOSED
  END.

Definition fragmentC : command :=
  IFB (beq (proj stateP y) (expr READING)) THEN
    avar r ::<- read (proj idP y) ;;
    IFB (beq (deref r) (expr 0)) THEN
      deref y ::=state expr CLOSED
    ELSE
      avar s ::= deref r ;;
      deref y ::=state expr WRITING
    END
  END.

(** Now we prove that our implementation refines our specification by
    layers. Here is the first layer: *)

(** * The first layer. *)

Definition process_l1 :=
  fragmentA ;;
  FOR y IN conns DO
      fragmentB ;;
      fragmentC
  END.

Global Instance CongProper {A : Set}
       `{forall (A : Set), Equivalence (FixRel EqSpecRel A)} :
  Proper (FixRel EqSpecRel A ==>
          FixRel EqSpecRel A ==>
          iff) (FixRel EqSpecRel A).
typeclasses eauto.
Defined.

(** We show that [process] refines [process_l1]. *)

Lemma refinesL1 :
  (@denote_command' process) ⊆ (@denote_command' process_l1).
Proof.
  apply (@refinesEq _ _ (@EqSpec) _ _ _).
  unfold process, process_l1, fragmentA, fragmentB, fragmentC.
  unfold denote_command', denote_command_Spec, denote_expS.
  assert (forall (a b : Spec unit) , (a >> b) = (a >>= (fun _ => b)))
    by reflexivity.
  assert (forall {A B : Set} (f : A -> B)(a : Spec A),
             fmap f a = (a >>= (fun a => return_ (f a))))
    by reflexivity.
  rewrite !(@PureRet SpecAdverbs _ _ _).
  rewrite !H, !H0.
  rewrite !(@eqBindAssoc SpecAdverbs _ _ _ EqSpecRel _ _).
  rewrite !(@eqBindAssoc SpecAdverbs _ _ _ EqSpecRel _ _ _ _ _ (return_ newconn)).
  repeat forward.
  rewrite !(@eqBindAssoc SpecAdverbs _ _ _ EqSpecRel _ _ _ _ _ (@denote_evS nat accept >>= setE a)).
  reflexivity.
Qed.

(** Similarly, we also divide the specification into three fragments. *)

Open Scope spec_scope.

Definition fragmentAS : commandS :=
  avar newconn ::<- accept ;;
  IFB (not (beq (deref newconn) (expr 0))) THEN
      avar newconn_rec ::= record (deref newconn) (expr READING) ;;
      conns ::++ newconn_rec
  END.

Definition fragmentBS : commandS :=
  IFB (beq (proj stateP y) (expr WRITING)) THEN
    avar r ::<- write (proj idP y) (deref s) ;;
    deref y ::=state expr CLOSED
  END.

Definition fragmentCS : commandS :=
  IFB (beq (proj stateP y) (expr READING)) THEN
    avar r ::<- read (proj idP y) ;;
    IFB (beq (deref r) (expr 0)) THEN
      deref y ::=state expr CLOSED
    ELSE
      avar s ::= deref r ;;
      deref y ::=state expr WRITING
    END
    END.

(** We show that each fragment of the implementation refines a fragment of the
    specification. *)

Lemma fragmentA_refines :
  (@denote_command' fragmentA) ⊆ (@denote_command_Spec fragmentAS).
Proof. reflexivity. Qed.

Lemma fragmentB_refines :
  (@denote_command' fragmentB) ⊆ (@denote_command_Spec fragmentBS).
Proof. reflexivity. Qed.

Lemma fragmentC_refines :
  (@denote_command' fragmentC) ⊆ (@denote_command_Spec fragmentCS).
Proof. reflexivity. Qed.


Opaque fragmentA.
Opaque fragmentB.
Opaque fragmentC.
Opaque fragmentAS.
Opaque fragmentBS.
Opaque fragmentCS.

(** * The second layer. *)

Definition process_l2 :=
  fragmentAS ;;
  OneOfS conns y
         (fragmentBS ;; fragmentCS).

Opaque fplus.
Opaque kleenePlus.

Open Scope nat_scope.

Lemma refinesL2 :
  (@denote_command' process_l1) ⊆ (@denote_command_Spec process_l2).
Proof.
  cbn. repeat forward.
  etransitivity.
  2: { apply (@refinesSeq SpecAdverbs _ _ _ _ _ (@RefinesRel) _ _) with (n:=(length a0)).
       reflexivity.
  }
  induction a0.
  - reflexivity.
  - cbn. etransitivity.
    + apply (@refinesEq _ _ (@EqSpec) _ _ _). symmetry.
      apply (@eqBindAssoc SpecAdverbs _ _ _ EqSpecRel _ _).
    + apply eqBindCong.
      * apply (@refinesFplusL SpecAdverbs _ _ _ (@RefinesRel) _ _).
      * intros []. etransitivity.
        -- apply IHa0.
        -- remember (foldr
          (fun (vc : var Connection) (s0 : Fix1 SpecAdverbs unit) =>
           fplus
             (bind_fm (@setE SpecAdverbs Functor1__SumE Inj1_Sum1_r (var Connection) y vc)
                (fun _ : unit =>
                 bind_fm (@denote_command_Spec fragmentBS) (fun _ : unit => @denote_command_Spec fragmentCS))) s0)
          (return_fm tt) a1) as x. clear IHa0. clear Heqx.
          induction a1.
           ++ cbn. apply (@refinesFplusR SpecAdverbs _ _ _ (@RefinesRel) _ _).
           ++ cbn. apply eqBindCong.
              ** apply (@refinesFplusR SpecAdverbs _ _ _ (@RefinesRel) _ _).
              ** intros []. apply IHa1.
Qed.

(** * The third layer. *)

Definition process_l3 :=
  fragmentAS ;;
  OneOfS conns y
         (OrS fragmentBS fragmentCS).

Lemma refinesL3 :
  (@denote_command_Spec process_l2) ⊆ (@denote_command_Spec process_l3).
Proof.
  cbn. repeat forward.
  apply refinesKleenePlus.
  induction a0.
  - cbn. replace (return_fm tt) with (@seq SpecAdverbs _ _ _ _ (return_fm tt) 0).
    + apply refinesSeq; reflexivity.
    + reflexivity.
  - cbn. apply refinesFplus.
    + etransitivity.
      * Unshelve.
         2: {
           exact (bind_fm
                    (@setE SpecAdverbs Functor1__SumE Inj1_Sum1_r (var Connection) y a0)
                    (fun _ : unit => bind_fm
                                    (fplus (@denote_command_Spec fragmentBS) (@denote_command_Spec fragmentCS))
                                    (fun _ : unit => (fplus (@denote_command_Spec fragmentBS) (@denote_command_Spec fragmentCS))))).
         }
         repeat forward. apply eqBindCong.
        -- apply refinesFplusL.
        -- intros. apply refinesFplusR.
      * etransitivity.
        -- Unshelve.
           2: {
             exact ((bind_fm (@setE SpecAdverbs Functor1__SumE Inj1_Sum1_r (var Connection) y a0)
                             (fun _ : unit => kleenePlus (fplus (@denote_command_Spec fragmentBS) (@denote_command_Spec fragmentCS))))).
           }
           repeat forward.
           replace ((bind_fm (fplus (@denote_command_Spec fragmentBS) (@denote_command_Spec fragmentCS))
                             (fun _ : unit => fplus (@denote_command_Spec fragmentBS) (@denote_command_Spec fragmentCS))))
             with (@seq SpecAdverbs _ _ _ _ (fplus (@denote_command_Spec fragmentBS) (@denote_command_Spec fragmentCS)) 1) by reflexivity.
           apply refinesSeq; reflexivity.
        -- replace ((bind_fm (@setE SpecAdverbs Functor1__SumE Inj1_Sum1_r (var Connection) y a0)
                             (fun _ : unit => kleenePlus (fplus (@denote_command_Spec fragmentBS) (@denote_command_Spec fragmentCS)))))
             with (@seq SpecAdverbs _ _ _ _ (bind_fm (@setE SpecAdverbs Functor1__SumE Inj1_Sum1_r (var Connection) y a0)
                                                     (fun _ : unit => kleenePlus (fplus (@denote_command_Spec fragmentBS) (@denote_command_Spec fragmentCS)))) 0) by reflexivity.
           apply refinesSeq, refinesFplusL.
    + replace (foldr (fun (vc : var Connection) (s0 : Fix1 SpecAdverbs unit) =>
        fplus
          (bind_fm (@setE SpecAdverbs Functor1__SumE Inj1_Sum1_r (var Connection) y vc)
             (fun _ : unit => bind_fm (@denote_command_Spec fragmentBS) (fun _ : unit => @denote_command_Spec fragmentCS)))
          s0) (return_fm tt) a1) with
          (@seq SpecAdverbs _ _ _ _ (foldr (fun (vc : var Connection) (s0 : Fix1 SpecAdverbs unit) =>
        fplus
          (bind_fm (@setE SpecAdverbs Functor1__SumE Inj1_Sum1_r (var Connection) y vc)
             (fun _ : unit => bind_fm (@denote_command_Spec fragmentBS) (fun _ : unit => @denote_command_Spec fragmentCS)))
          s0) (return_fm tt) a1) 0) by reflexivity.
      etransitivity. exact IHa0.
      eapply refinesKleenePlusCong.
      apply refinesFplusR.
Qed.

(** * The fourth layer. *)

Definition process_l4 :=
  SomeS (OrS fragmentAS (OneOfS conns y (OrS fragmentBS fragmentCS))).

Lemma refinesL4 :
  (@denote_command_Spec process_l3) ⊆ (@denote_command_Spec process_l4).
Proof.
  cbn.
  etransitivity.
  2: { apply (@refinesSeq SpecAdverbs _ _ _ _ _ (@RefinesRel) _ _) with (n:=1).
       reflexivity.
  }
  cbn. eapply eqBindCong.
  - replace (@denote_command_Spec fragmentAS)
      with (@seq SpecAdverbs _ _ _ _ (@denote_command_Spec fragmentAS) 0) by reflexivity.
    apply refinesSeq, refinesFplusL.
  - intros [].
    replace ((bind_fm (@getE SpecAdverbs Functor1__SumE Inj1_Sum1_r (list (var Connection)) conns)
       (fun xs : list (var Connection) =>
        kleenePlus
          (foldr
             (fun (vc : var Connection) (s0 : Fix1 SpecAdverbs unit) =>
              fplus
                (bind_fm (@setE SpecAdverbs Functor1__SumE Inj1_Sum1_r (var Connection) y vc)
                   (fun _ : unit =>
                    kleenePlus (fplus (@denote_command_Spec fragmentBS) (@denote_command_Spec fragmentCS)))) s0)
             (return_fm tt) xs))))
      with (@seq SpecAdverbs _ _ _ _ (bind_fm (@getE SpecAdverbs Functor1__SumE Inj1_Sum1_r (list (var Connection)) conns)
       (fun xs : list (var Connection) =>
        kleenePlus
          (foldr
             (fun (vc : var Connection) (s0 : Fix1 SpecAdverbs unit) =>
              fplus
                (bind_fm (@setE SpecAdverbs Functor1__SumE Inj1_Sum1_r (var Connection) y vc)
                   (fun _ : unit =>
                    kleenePlus (fplus (@denote_command_Spec fragmentBS) (@denote_command_Spec fragmentCS)))) s0)
             (return_fm tt) xs))) 0) by reflexivity.
    apply refinesSeq, refinesFplusR.
Qed.

(** The fourth layer is the spec. *)

Lemma fourth_is_spec :
  process_l4 = processSpec.
Proof. reflexivity. Qed.
