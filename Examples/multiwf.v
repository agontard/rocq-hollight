From mathcomp Require Import ssreflect ssrnat cardinality.
Require Export HOLLight.HOL.mappings.

Lemma WFP_def {_184264 : Type'} : @Acc _184264 = (fun lt2' : _184264 -> _184264 -> Prop => fun a : _184264 => forall WFP' : _184264 -> Prop, (forall a' : _184264, (forall y : _184264, (lt2' y a') -> WFP' y) -> WFP' a') -> WFP' a).
Proof. ind_align. Qed.

(*****************************************************************************)
(* Multisets *)
(*****************************************************************************)

Lemma empty_mempty_domain {A : Type} : (fun _ : A => 0 <> 0) = set0.
Proof. by ext. Qed.

Definition is_fmultiset {A : Type'} : (A -> nat) -> Prop :=
  fun f => @finite_set A (@GSPEC A (fun GEN_PVAR_433 : A => exists a : A, @SETSPEC A GEN_PVAR_433 (~ ((f a) = (NUMERAL 0))) a)).

Lemma is_fmultiset0 (A : Type') : is_fmultiset (fun (_ : A) => 0).
Proof.
  unfold is_fmultiset. rewrite SPEC_elim finite_setE empty_mempty_domain.
  exact (finite'_set0 _).
Qed.

Definition Multiset (A : Type') := subtype (is_fmultiset0 A).

Definition multiset {A : Type'} := mk (is_fmultiset0 A).
Definition multiplicity {A : Type'} := dest (is_fmultiset0 A).

Lemma _mk_dest_Multiset : forall {A : Type'} (a : Multiset A), (@multiset A (@multiplicity A a)) = a.
Proof. intros. apply mk_dest. Qed.

Lemma _dest_mk_Multiset : forall {A : Type'} (r : A -> nat), ((fun f : A -> nat => @finite_set A (@GSPEC A (fun GEN_PVAR_433 : A => exists a : A, @SETSPEC A GEN_PVAR_433 (~ ((f a) = (NUMERAL 0))) a))) r) = ((@multiplicity A (@multiset A r)) = r).
Proof. intros. apply dest_mk. Qed.

Definition mempty {A : Type'} : Multiset A := multiset (fun _ => 0).
Lemma mempty_def {_183533 : Type'} : mempty = (@multiset _183533 (fun b : _183533 => NUMERAL 0)).
Proof. reflexivity. Qed.

Definition mmember {A : Type'} (a : A) (m : Multiset A) := multiplicity m a <> 0.
Lemma mmember_def {_183543 : Type'} : mmember = (fun _203992 : _183543 => fun _203993 : Multiset _183543 => ~ ((@multiplicity _183543 _203993 _203992) = (NUMERAL 0))).
Proof. reflexivity. Qed.

Definition msing {A : Type'} : A -> Multiset A := fun a => multiset (fun a' => COND (a'=a) 1 0).

Lemma msing_def {_183559 : Type'} : msing = (fun _204004 : _183559 => @multiset _183559 (fun b : _183559 => @COND nat (b = _204004) (NUMERAL (BIT1 0)) (NUMERAL 0))).
Proof. reflexivity. Qed.

Definition munion {A : Type'} := fun (m m' : Multiset A) => 
  multiset (fun a => multiplicity m a + (multiplicity m' a)).

Lemma munion_def {_183578 : Type'} : (@munion _183578) = (fun _204009 : Multiset _183578 => fun _204010 : Multiset _183578 => @multiset _183578 (fun b : _183578 => addn (@multiplicity _183578 _204009 b) (@multiplicity _183578 _204010 b))).
Proof. reflexivity. Qed.

Definition mdiff {A : Type'} := fun (m m' : Multiset A) => 
  multiset (fun a => multiplicity m a - (multiplicity m' a)). 

Lemma mdiff_def {_183597 : Type'} : (@mdiff _183597) = (fun _204021 : Multiset _183597 => fun _204022 : Multiset _183597 => @multiset _183597 (fun b : _183597 => subn (@multiplicity _183597 _204021 b) (@multiplicity _183597 _204022 b))).
Proof. reflexivity. Qed.

(* given an order relation R on A, define the order relation Rm on Multiset A by :
   Rm m m' <-> (exists a in m, forall a' in m', a' is in m\{a} or R a a'.) *)
Definition morder {A : Type'} : (A -> A -> Prop) -> (Multiset A) -> (Multiset A) -> Prop := 
  fun R m m' => exists m0 a m1, (m' = munion m0 (msing a)) /\ 
  (m = munion m0 m1) /\ forall a', mmember a' m1 -> R a' a.
Lemma morder_def {_184446 : Type'} : (@morder _184446) = (fun _204323 : _184446 -> _184446 -> Prop => fun _204324 : Multiset _184446 => fun _204325 : Multiset _184446 => exists M0 : Multiset _184446, exists a : _184446, exists K : Multiset _184446, (_204325 = (@munion _184446 M0 (@msing _184446 a))) /\ ((_204324 = (@munion _184446 M0 K)) /\ (forall b : _184446, (@mmember _184446 b K) -> _204323 b a))).
Proof. reflexivity. Qed.