From Stdlib Require Import Relation_Operators.
Require Export HOLLight.init.

Lemma TC_def {A : Type'} : (@Relation_Operators.clos_trans A) = (fun R' : A -> A -> Prop => fun a0 : A => fun a1 : A => forall TC' : A -> A -> Prop, (forall a0' : A, forall a1' : A, ((R' a0' a1') \/ (exists y : A, (TC' a0' y) /\ (TC' y a1'))) -> TC' a0' a1') -> TC' a0 a1).
Proof. ind_align. Qed.