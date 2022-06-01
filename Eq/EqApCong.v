From Coq Require Import
     Relation_Definitions
     RelationClasses
.

Require Import GHC.Base.
Require Import Fix.
Require Import Tactics.Tactics.

(* begin eq_ap_cong *)
Variant EqApCong {F} `{Applicative F}
        (Kr : forall (A : Set), relation (F A))
        {A : Set} : relation (F A) :=
| EqApApCong : forall {B : Set} (f g : F (B -> A)) (a b: F B),
    Kr _ f g ->
    Kr _ a b ->
    EqApCong Kr (f <*> a) (g <*> b).
(* end eq_ap_cong *)

#[export] Instance FunctorRel__EqApT {F} {HF: Functor F} {HA : Applicative F}
  : FunctorRel (F:=F) (@EqApCong _ HF HA).
constructor. intros ? ? ? ? ? ? [].
constructor; auto.
Qed.

Section EqApCong_SmartConstructors.

  Variable F : Set -> Set.

  Context {HF : Functor F} {HA : Applicative F}.

  Variable R : (forall (A : Set), relation (F A)) ->
               forall (A : Set), relation (F A).

  Context `{FunctorRel F R} `{@EqApCong _ HF HA -⋘ R}.

  Lemma eqApCong : forall {A B : Set} (f g : F (A -> B)) (a b : F A),
      FixRel R _ f g ->
      FixRel R _ a b ->
      FixRel R _ (f <*> a) (g <*> b).
  Proof. eqConstruct. Qed.

End EqApCong_SmartConstructors.
