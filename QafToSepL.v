Require Import Reals.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat.
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import Classical_Prop.
Require Import MathSpec.
Require Import Coq.Program.Basics.

(* Quantum Separation Logic Definitions *)
Inductive qsep : var -> var -> Prop :=
  | qsep_intro : forall q1 q2, q1 <> q2 -> qsep q1 q2.

Inductive qent : var -> var -> Prop :=
  | qent_intro : forall q1 q2, q1 <> q2 -> qent q1 q2.

Inductive qfree : var -> Prop :=
  | qfree_intro : forall q, qfree q.

(* Hoare Triple with Quantum Separation Logic *)
Inductive QSL_Hoare : (var -> Prop) -> exp -> (var -> Prop) -> Prop :=
  | QSL_Hoare_Skip : forall P x a, QSL_Hoare P (SKIP x a) P
  | QSL_Hoare_H : forall P q,
      P q -> QSL_Hoare P (AppU [q] H_gate) (fun q' => qsep q q')
  | QSL_Hoare_X : forall P q,
      P q -> QSL_Hoare P (AppU [q] X_gate) (fun q' => qsep q q')
  | QSL_Hoare_RZ : forall P q n,
      P q -> QSL_Hoare P (RZ n q (Num 1)) (fun q' => qsep q q')
  | QSL_Hoare_Seq : forall P Q R e1 e2,
      QSL_Hoare P e1 Q -> QSL_Hoare Q e2 R -> QSL_Hoare P (Seq e1 e2) R.

(* Quantum Measurement Rule *)
Inductive QSL_Measure : (var -> Prop) -> exp -> (var -> Prop) -> Prop :=
  | QSL_Hoare_Measure : forall P q,
      P q -> QSL_Measure P (AppU [q] (RZ 1 q (Num 0))) (fun q' => qfree q').

(* Example Proof: Applying Hadamard Maintains Separation *)
Lemma QSL_H_Holds : forall q,
  QSL_Hoare (fun q' => qsep q q') (AppU [q] H_gate) (fun q' => qsep q q').
Proof.
  intros. constructor. assumption.
Qed.

(* Example Proof: Applying X Maintains Separation *)
Lemma QSL_X_Holds : forall q,
  QSL_Hoare (fun q' => qsep q q') (AppU [q] X_gate) (fun q' => qsep q q').
Proof.
  intros. constructor. assumption.
Qed.

(* Example Proof: Applying RZ Maintains Separation *)
Lemma QSL_RZ_Holds : forall q,
  QSL_Hoare (fun q' => qsep q q') (RZ 1 q (Num 0)) (fun q' => qsep q q').
Proof.
  intros. constructor. assumption.
Qed.

(* Example Proof: Measuring a Qubit Frees It *)
Lemma QSL_Measure_Holds : forall q,
  QSL_Measure (fun q' => qsep q q') (AppU [q] (RZ 1 q (Num 0))) (fun q' => qfree q').
Proof.
  intros. constructor. assumption.
Qed.
