(* Import necessary modules *)
Require Import String.
Require Import Nat.
Require Import List.
Require Import Bool.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
(* Define variables and arrays *)
Inductive var := 
  | Scalar (name : string) (* Scalar variable *)
  | Array (name : string) (index : nat). (* Array variable with index *)

(* Define expressions *)
Inductive expr :=
  | Const (n : nat) (* Constant *)
  | VarExpr (v : var) (* Variable *)
  | Plus (e1 e2 : expr) (* Addition *)
  | Minus (e1 e2 : expr). (* Subtraction *)

(* Define the state *)
Definition state := var -> option nat.

(* Evaluate expressions *)
Fixpoint eval (e : expr) (s : state) : option nat :=
  match e with
  | Const n => Some n
  | VarExpr v => s v
  | Plus e1 e2 =>
      match eval e1 s, eval e2 s with
      | Some n1, Some n2 => Some (n1 + n2)
      | _, _ => None
      end
  | Minus e1 e2 =>
      match eval e1 s, eval e2 s with
      | Some n1, Some n2 => Some (n1 - n2)
      | _, _ => None
      end
  end.
(* Define equality comparison for variables *)
Definition eqb_var (v1 v2 : var) : bool :=
  match v1, v2 with
  | Scalar n1, Scalar n2 => String.eqb n1 n2
  | Array n1 i1, Array n2 i2 => String.eqb n1 n2 && Nat.eqb i1 i2
  | _, _ => false
  end.
(* Define commands *)
Inductive cmd :=
  | Skip (* No operation *)
  | Assign (v : var) (e : expr) (* Variable assignment *)
  | ArrayWrite (name : string) (index : expr) (value : expr) (* Array write operation *)
  | Seq (c1 c2 : cmd) (* Sequential composition *)
  | If (b : expr) (c1 c2 : cmd) (* Conditional *)
  | While (b : expr) (c : cmd). (* While loop *)

(* Define execution semantics with a fuel parameter *)
Fixpoint exec (fuel : nat) (c : cmd) (s : state) : option state :=
  match fuel with
  | 0 => None (* Out of fuel *)
  | S fuel' =>
      match c with
      | Skip => Some s
      | Assign v e =>
          match eval e s with
          | Some val => Some (fun x => if eqb_var x v then Some val else s x)
          | None => None
          end
      | ArrayWrite name idx val =>
          match eval idx s, eval val s with
          | Some i, Some v =>
              Some (fun x =>
                if eqb_var x (Array name i) then Some v else s x)
          | _, _ => None
          end
      | Seq c1 c2 =>
          match exec fuel' c1 s with
          | Some s' => exec fuel' c2 s'
          | None => None
          end
      | If b c1 c2 =>
          match eval b s with
          | Some n => if Nat.eqb n 0 then exec fuel' c2 s else exec fuel' c1 s
          | None => None
          end
      | While b c =>
          match eval b s with
          | Some n =>
              if Nat.eqb n 0 then Some s
              else
                match exec fuel' c s with
                | Some s' => exec fuel' (While b c) s'
                | None => None
                end
          | None => None
          end
      end
  end.
(* Define substitution function *)
Fixpoint subst (e : expr) (v : var) (e_subst : expr) : expr :=
  match e with
  | Const n => Const n
  | VarExpr x => if eqb_var x v then e_subst else VarExpr x
  | Plus e1 e2 => Plus (subst e1 v e_subst) (subst e2 v e_subst)
  | Minus e1 e2 => Minus (subst e1 v e_subst) (subst e2 v e_subst)
  end.
(* Definition of cbexp *)
Inductive cbexp : Type :=
  | CBTrue : cbexp                (* Represents a constant true condition *)
  | CBVar : var -> cbexp          (* Represents a Boolean variable *)
  | CBAnd : cbexp -> cbexp -> cbexp. (* Represents a conjunction (AND) of two `cbexp` expressions *)

(* Evaluation of cbexp *)
Fixpoint eval_cbexp (env : var -> bool) (e : cbexp) : bool :=
  match e with
  | CBTrue => true                          (* True always evaluates to true *)
  | CBVar v => env v                        (* Lookup the value of the variable in the environment *)
  | CBAnd e1 e2 => (eval_cbexp env e1) && (eval_cbexp env e2) (* Evaluate both sides and take AND *)
  end.

(* Define assertions as cpred *)
Definition cpred := list cbexp.
Definition assertion := cpred.

(* Define Hoare triples *)
Inductive hoare_triple : assertion -> cmd -> assertion -> Prop :=
  | skip_rule : forall P,
      hoare_triple P Skip P
  | seq_rule : forall P Q R c1 c2,
      hoare_triple P c1 Q ->
      hoare_triple Q c2 R ->
      hoare_triple P (Seq c1 c2) R
  | assign_rule : forall Q v e,
      hoare_triple Q (Assign v e) Q
  | if_rule : forall P Q b c1 c2,
      hoare_triple P c1 Q ->
      hoare_triple P c2 Q ->
      hoare_triple P (If b c1 c2) Q
  | while_rule : forall P b c,
      hoare_triple P c P ->
      hoare_triple P (While b c) P
  | array_write_rule : forall P name idx val,
      hoare_triple P (ArrayWrite name idx val) P.



(*
(* Define Hoare triples *)
Definition assertion := state -> Prop.

Definition hoare_triple (P : assertion) (fuel : nat) (c : cmd) (Q : assertion) : Prop :=
  forall (s s' : state),
    P s ->
    exec fuel c s = Some s' ->
    Q s'.
(* Proof rules for Hoare logic *)
Axiom hoare_skip : forall P fuel,
  hoare_triple P fuel Skip P.
Axiom hoare_assign : forall P v e fuel,
  hoare_triple
    (fun s => P (fun x => if eqb_var x v then eval e s else s x))
    fuel
    (Assign v e)
    P.
Axiom hoare_array_write : forall P name idx val fuel,
  hoare_triple
    (fun s => exists i v,
       eval idx s = Some i /\
       eval val s = Some v /\
       P (fun x => if eqb_var x (Array name i) then Some v else s x))
    fuel
    (ArrayWrite name idx val)
    P.
Axiom hoare_seq : forall P Q R c1 c2 fuel,
  hoare_triple P fuel c1 Q ->
  hoare_triple Q fuel c2 R ->
  hoare_triple P fuel (Seq c1 c2) R.
Axiom hoare_if : forall P Q b c1 c2 fuel,
  hoare_triple (fun s => P s /\ eval b s <> Some 0) fuel c1 Q ->
  hoare_triple (fun s => P s /\ eval b s = Some 0) fuel c2 Q ->
  hoare_triple P fuel (If b c1 c2) Q.
Axiom hoare_while : forall P b c fuel,
  hoare_triple (fun s => P s /\ eval b s <> Some 0) fuel c P ->
  hoare_triple P fuel (While b c) (fun s => P s /\ eval b s = Some 0).
(* Example: Proof of array write *)
Example array_write_example :
  hoare_triple
    (fun s => True) (* Precondition: no specific requirement *)
    10 (* Fuel: maximum 10 steps *)
    (ArrayWrite "a" (Const 0) (Const 42))
    (fun s => s (Array "a" 0) = Some 42). (* Postcondition: the value at index 0 is updated to 42 *)
Proof.
  unfold hoare_triple.
  intros s s' H_pre H_exec.
  simpl in H_exec.
  destruct (eval (Const 0) s) eqn:E1; try discriminate.
  destruct (eval (Const 42) s) eqn:E2; try discriminate.
  inversion H_exec.
  subst.
  simpl.
  reflexivity.
Qed.
Theorem hoare_pre_strengthening : forall (P' P Q : assertion) (c : cmd) (fuel : nat),
  (forall s, P' s -> P s) ->
  hoare_triple P fuel c Q ->
  hoare_triple P' fuel c Q.
Proof.
  intros P' P Q c fuel Himp Hht.
  unfold hoare_triple in *.
  intros s s' HP' Hexec.
  apply Himp in HP'.
  apply Hht with (s := s); assumption.
Qed.
Theorem hoare_post_weakening : forall (P Q Q' : assertion) (c : cmd) (fuel : nat),
  (forall s, Q s -> Q' s) ->
  hoare_triple P fuel c Q ->
  hoare_triple P fuel c Q'.
Proof.
  intros P Q Q' c fuel Himp Hht.
  unfold hoare_triple in *.
  intros s s' HP Hexec.
  apply Hht in Hexec; try assumption.
  apply Himp. assumption.
Qed.
Theorem hoare_skip_trivial : forall P fuel,
  hoare_triple P fuel Skip P.
Proof.
  intros P fuel.
  apply hoare_skip.
Qed.
Theorem hoare_seq_assign : forall P Q R v1 e1 v2 e2 fuel,
  hoare_triple P fuel (Assign v1 e1) Q ->
  hoare_triple Q fuel (Assign v2 e2) R ->
  hoare_triple P fuel (Seq (Assign v1 e1) (Assign v2 e2)) R.
Proof.
  intros P Q R v1 e1 v2 e2 fuel Hht1 Hht2.
  apply hoare_seq with (Q := Q); assumption.
Qed.
Theorem hoare_loop_invariant : forall P b c fuel,
  hoare_triple (fun s => P s /\ eval b s <> Some 0) fuel c P ->
  hoare_triple P fuel (While b c) (fun s => P s /\ eval b s = Some 0).
Proof.
  intros P b c fuel Hht.
  apply hoare_while; assumption.
Qed.
Theorem array_write_updates_index : forall P name idx val fuel,
  hoare_triple
    (fun s => P s)
    fuel
    (ArrayWrite name idx val)
    (fun s' => exists i v,
       eval idx s = Some i /\
       eval val s = Some v /\
       s' (Array name i) = Some v).
Proof.
  intros P name idx val fuel.
  unfold hoare_triple.
  intros s s' HP Hexec.
  simpl in Hexec.
  destruct (eval idx s) eqn:Hidx, (eval val s) eqn:Hval; try discriminate.
  inversion Hexec. subst.
  exists n, n0. split; [assumption |].
  split; [assumption | reflexivity].
Qed.

*)
















