(* Import necessary modules *)
Require Import String.
Require Import Nat.
Require Import List.
Require Import Bool.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Reals.
Require Import Psatz.
Require Import Complex.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat Permutation. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import Classical_Prop.
Require Import MathSpec.
Require Import QafnySyntax.
Require Import LocusDef.
Require Import LocusKind.
Require Import LocusType.
Require Import LocusSem.
Require Import LocusProof.
Require Import LocusTypeProof.
Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Declare Scope pexp_scope.
Delimit Scope pexp_scope with pexp.
Local Open Scope pexp_scope.
Local Open Scope nat_scope.
(* Import necessary modules *)
Require Import String.
Require Import Nat.
Require Import List.
Require Import Bool.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Import LocusProof.
(* Define variables and arrays *)
Inductive var := 
  | Scalar (name : string) (* Scalar variable *)
  | Array (name : string) (index : nat). (* Array variable with index *)
Inductive expr :=
  | VarExpr (v : var)
  | Const (n : nat)
  | Plus (e1 e2 : expr)
  | Minus (e1 e2 : expr)
  | Mult (e1 e2 : expr)
  | EEq (e1 e2 : expr)    (* renamed from Eq *)
  | ELt (e1 e2 : expr).   (* renamed from Lt *)
(*
Inductive expr :=
  | VarExpr (v : var) (* Variable *)
  | Const (n : nat) (* Natural number constant *)
  | Plus (e1 e2 : expr) (* Addition *)
  | Minus (e1 e2 : expr) (* Subtraction *)
  | Mult (e1 e2 : expr). (* Multiplication *)
*)
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
      | Some n1, Some n2 => if n1 <? n2 then None else Some (n1 - n2)
      | _, _ => None
      end
  | Mult e1 e2 =>
      match eval e1 s, eval e2 s with
      | Some n1, Some n2 => Some (n1 * n2)
      | _, _ => None
      end
  | EEq e1 e2 =>
      match eval e1 s, eval e2 s with
      | Some n1, Some n2 => Some (if Nat.eqb n1 n2 then 1 else 0)
      | _, _ => None
      end
  | ELt e1 e2 =>
      match eval e1 s, eval e2 s with
      | Some n1, Some n2 => Some (if n1 <? n2 then 1 else 0)
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
(* Equality check for expressions *)
Fixpoint expr_eqb (e1 e2 : expr) : bool :=
  match e1, e2 with
  | Const n1, Const n2 => Nat.eqb n1 n2
  | VarExpr v1, VarExpr v2 => eqb_var v1 v2
  | Plus e1a e1b, Plus e2a e2b => expr_eqb e1a e2a && expr_eqb e1b e2b
  | Minus e1a e1b, Minus e2a e2b => expr_eqb e1a e2a && expr_eqb e1b e2b
  | _, _ => false
  end.
(*
Fixpoint expr_eqb (e1 e2 : expr) : bool :=
  match e1, e2 with
  | Const n1, Const n2 => Nat.eqb n1 n2
  | VarExpr v1, VarExpr v2 => eqb_var v1 v2
  | Plus a1 b1, Plus a2 b2 => expr_eqb a1 a2 && expr_eqb b1 b2
  | Minus a1 b1, Minus a2 b2 => expr_eqb a1 a2 && expr_eqb b1 b2
  | Mult a1 b1, Mult a2 b2 => expr_eqb a1 a2 && expr_eqb b1 b2
  | _, _ => false
  end.
*)
(* Reflexivity *)
Lemma eqb_var_refl : forall v, eqb_var v v = true.
Proof.
  destruct v; simpl.
  - apply String.eqb_refl.
  - rewrite String.eqb_refl, Nat.eqb_refl. reflexivity.
Qed.
(* Soundness *)
Lemma eqb_var_eq : forall v1 v2, eqb_var v1 v2 = true -> v1 = v2.
Proof.
  destruct v1, v2; simpl; try discriminate; intros H.
  - apply String.eqb_eq in H. subst. reflexivity.
  - apply andb_true_iff in H as [H1 H2].
    apply String.eqb_eq in H1. apply Nat.eqb_eq in H2. subst. reflexivity.
Qed.

(* Contrapositive *)
Lemma eqb_var_neq : forall v1 v2, eqb_var v1 v2 = false -> v1 <> v2.
Proof.
  intros v1 v2 Hcontra Heq. subst.
  rewrite eqb_var_refl in Hcontra. discriminate.
Qed.
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
(*
Fixpoint subst (x : var) (e_sub e : expr) : expr :=
  match e with
  | Const n => Const n
  | VarExpr v => if eqb_var v x then e_sub else VarExpr v
  | Plus e1 e2 => Plus (subst x e_sub e1) (subst x e_sub e2)
  | Minus e1 e2 => Minus (subst x e_sub e1) (subst x e_sub e2)
  | Mult e1 e2 => Mult (subst x e_sub e1) (subst x e_sub e2)
  end.
*)
(* Define substitution function *)
Fixpoint subst (e : expr) (v : var) (e_subst : expr) : expr :=
  match e with
  | Const n => Const n
  | VarExpr x => if eqb_var x v then e_subst else VarExpr x
  | Plus e1 e2 => Plus (subst e1 v e_subst) (subst e2 v e_subst)
  | Minus e1 e2 => Minus (subst e1 v e_subst) (subst e2 v e_subst)
  | Mult e1 e2 => Mult (subst e1 v e_subst) (subst e2 v e_subst)
  | EEq e1 e2 => EEq (subst e1 v e_subst) (subst e2 v e_subst)
  | ELt e1 e2 => ELt (subst e1 v e_subst) (subst e2 v e_subst)
  end.
Fixpoint subst_array_expr (e : expr) (name : string) (idx : expr) (val : expr) : expr :=
  match e with
  | Const _ => e
  | VarExpr (Array n i) =>
      if String.eqb n name && expr_eqb (Const i) idx then val
      else VarExpr (Array n i)
  | VarExpr _ => e
  | Plus e1 e2 => Plus (subst_array_expr e1 name idx val) (subst_array_expr e2 name idx val)
  | Minus e1 e2 => Minus (subst_array_expr e1 name idx val) (subst_array_expr e2 name idx val)
  | Mult e1 e2 => Mult (subst_array_expr e1 name idx val) (subst_array_expr e2 name idx val)
  | EEq e1 e2 => EEq (subst_array_expr e1 name idx val) (subst_array_expr e2 name idx val)
  | ELt e1 e2 => ELt (subst_array_expr e1 name idx val) (subst_array_expr e2 name idx val)
  end.
Fixpoint eval_expr (e : expr) (s : state) : option nat :=
  match e with
  | Const n => Some n
  | VarExpr v => s v
  | Plus e1 e2 =>
      match eval_expr e1 s, eval_expr e2 s with
      | Some n1, Some n2 => Some (n1 + n2)
      | _, _ => None
      end
  | Minus e1 e2 =>
      match eval_expr e1 s, eval_expr e2 s with
      | Some n1, Some n2 => if n1 <? n2 then None else Some (n1 - n2)
      | _, _ => None
      end
  | Mult e1 e2 =>
      match eval_expr e1 s, eval_expr e2 s with
      | Some n1, Some n2 => Some (n1 * n2)
      | _, _ => None
      end
  | EEq e1 e2 =>
      match eval_expr e1 s, eval_expr e2 s with
      | Some n1, Some n2 => Some (if Nat.eqb n1 n2 then 1 else 0)
      | _, _ => None
      end
  | ELt e1 e2 =>
      match eval_expr e1 s, eval_expr e2 s with
      | Some n1, Some n2 => Some (if n1 <? n2 then 1 else 0)
      | _, _ => None
      end
  end.
Inductive cbexpr :=
  | CEq (x : expr) (y : expr)
  | CLt (x : expr) (y : expr).
Definition cpredr := list cbexpr.

Fixpoint subst_expr (e : expr) (name : string) (idx : nat) (val : expr) : expr :=
  match e with
  | Const _ => e
  | VarExpr (Array n i) =>
      if String.eqb n name && Nat.eqb i idx then val
      else VarExpr (Array n i)
  | VarExpr _ => e
  | Plus e1 e2 => Plus (subst_expr e1 name idx val) (subst_expr e2 name idx val)
  | Minus e1 e2 => Minus (subst_expr e1 name idx val) (subst_expr e2 name idx val)
  | Mult e1 e2 => Mult (subst_expr e1 name idx val) (subst_expr e2 name idx val)
  | EEq e1 e2 => EEq (subst_expr e1 name idx val) (subst_expr e2 name idx val)
  | ELt e1 e2 => ELt (subst_expr e1 name idx val) (subst_expr e2 name idx val)
  end.
Definition subst_cbexpr (b : cbexp) (name : string) (idx : nat) (val : expr) : cbexpr :=
  match b with
  | CEq e1 e2 => CEq (subst_expr e1 name idx val) (subst_expr e2 name idx val)
  | CLt e1 e2 => CLt (subst_expr e1 name idx val) (subst_expr e2 name idx val)
  end.
Definition eval_cbexpr (b : cbexpr) (s : state) : option bool :=
  match b with
  | CEq e1 e2 =>
      match eval_expr e1 s, eval_expr e2 s with
      | Some n1, Some n2 => Some (Nat.eqb n1 n2)
      | _, _ => None
      end
  | CLt e1 e2 =>
      match eval_expr e1 s, eval_expr e2 s with
      | Some n1, Some n2 => Some (n1 <? n2)
      | _, _ => None
      end
  end.
Fixpoint subst_expr_var (e : expr) (v : var) (e_subst : expr) : expr :=
  match e with
  | Const n => Const n
  | VarExpr v' => if eqb_var v' v then e_subst else VarExpr v'
  | Plus e1 e2 => Plus (subst_expr_var e1 v e_subst) (subst_expr_var e2 v e_subst)
  | Minus e1 e2 => Minus (subst_expr_var e1 v e_subst) (subst_expr_var e2 v e_subst)
  | Mult e1 e2 => Mult (subst_expr_var e1 v e_subst) (subst_expr_var e2 v e_subst)
  end.

Definition subst_cbexp (b : cbexpr) (v : var) (e_subst : expr) : cbexpr :=
  match b with
  | CEq e1 e2 => CEq (subst_expr_var e1 v e_subst) (subst_expr_var e2 v e_subst)
  | CLt e1 e2 => CLt (subst_expr_var e1 v e_subst) (subst_expr_var e2 v e_subst)
  end.

Definition subst_array (b : cbexpr) (name : string) (idx : nat) (val : expr) : cbexpr :=
  match b with
  | CEq e1 e2 => CEq (subst_expr e1 name idx val) (subst_expr e2 name idx val)
  | CLt e1 e2 => CLt (subst_expr e1 name idx val) (subst_expr e2 name idx val)
  end.

Definition subst_assertion_array (P : cpredr) (name : string) (idx : nat) (val : expr) : cpredr :=
  map (fun b => subst_array b name idx val) P.
Definition subst_assertion_array_expr (P : cpredr) (name : string) (idx : expr) (val : expr) (s : state) : cpredr :=
  match eval idx s with
  | Some n => subst_assertion_array P name n val
  | None => P (* Fallback if idx doesn't evaluate *)
  end.
Definition subst_assertion (P : cpredr) (v : var) (e_subst : expr) : cpredr :=
  map (fun b => subst_cbexp b v e_subst) P.
Check eval_cbexpr.
(* Define logical entailment for assertions (as conjunctions of cbexprs) *)
Definition entails (P Q : cpredr) : Prop :=
  forall s,
    (forall b, In b P -> eval_cbexpr b s = Some true) ->
    (forall b, In b Q -> eval_cbexpr b s = Some true).
Lemma entails_refl : forall P, entails P P.
Proof.
  intros P s HP b Hb. apply HP; assumption.
Qed.
Lemma entails_trans : forall P Q R,
  entails P Q -> entails Q R -> entails P R.
Proof.
  intros P Q R HPQ HQR s HP b Hb.
  apply HQR; [apply HPQ |]; assumption.
Qed.

(* Hoare logic with classical predicates and consequence rule *)
Inductive hoare_triple : cpredr -> cmd -> cpredr -> Prop :=
  | skip_rule : forall P,
      hoare_triple P Skip P
  | seq_rule : forall P Q R c1 c2,
      hoare_triple P c1 Q ->
      hoare_triple Q c2 R ->
      hoare_triple P (Seq c1 c2) R
  | assign_rule : forall P v e,
      hoare_triple (subst_assertion P v e) (Assign v e) P
  | if_rule : forall P Q b c1 c2,
      hoare_triple (CEq b (Const 0) :: P) c2 Q ->
      hoare_triple (CLt (Const 0) b :: P) c1 Q ->
      hoare_triple P (If b c1 c2) Q
  | while_rule : forall P b c,
      hoare_triple (CLt (Const 0) b :: P) c P ->
      hoare_triple P (While b c) P
  | array_write_rule : forall P name idx e,
      hoare_triple (subst_assertion_array P name idx e) (ArrayWrite name (Const idx) e) P
  | consequence_rule : forall P P' Q Q' c,
      entails P P' ->
      hoare_triple P' c Q' ->
      entails Q' Q ->
      hoare_triple P c Q.


(* Theorem: Hoare rule for skip *)
Theorem hoare_skip : forall P,
  hoare_triple P Skip P.
Proof.
  intros. apply skip_rule.
Qed.

(* Theorem: Hoare rule for sequential composition *)
Theorem hoare_seq : forall P Q R c1 c2,
  hoare_triple P c1 Q ->
  hoare_triple Q c2 R ->
  hoare_triple P (Seq c1 c2) R.
Proof.
  intros. apply seq_rule with Q; assumption.
Qed.

(* Theorem: Hoare rule for assignment *)
Theorem hoare_assign : forall P v e,
  hoare_triple (subst_assertion P v e) (Assign v e) P.
Proof.
  intros. apply assign_rule.
Qed.

(* Theorem: Hoare rule for conditional statements *)
Theorem hoare_if : forall P Q b c1 c2,
  hoare_triple P c1 Q ->
  hoare_triple P c2 Q ->
  hoare_triple P (If b c1 c2) Q.
Proof.
  intros P Q b c1 c2 H H0.
  apply if_rule.
  - (* Prove hoare_triple (CEq b (Const 0) :: P) c2 Q *)
    apply consequence_rule with (P' := P) (Q' := Q).
    + (* Prove entails (CEq b (Const 0) :: P) P *)
      unfold entails.
      intros s HP' b' Hb'.
      apply HP'.
      simpl In in Hb'.
      right; assumption.
    + (* Use H0 : hoare_triple P c2 Q *)
      apply H0.
    + (* Prove entails Q Q *)
      apply entails_refl.
  - (* Prove hoare_triple (CLt (Const 0) b :: P) c1 Q *)
    apply consequence_rule with (P' := P) (Q' := Q).
    + (* Prove entails (CLt (Const 0) b :: P) P *)
      unfold entails.
      intros s HP' b' Hb'.
      apply HP'.
      simpl In in Hb'.
      right; assumption.
    + (* Use H : hoare_triple P c1 Q *)
      apply H.
    + (* Prove entails Q Q *)
      apply entails_refl.
Qed.

(* Theorem: Hoare rule for while loops *)
Theorem hoare_while : forall P b c,
  hoare_triple P c P ->
  hoare_triple P (While b c) P.

Proof.
  intros P b c H.
  apply while_rule.
  (* Prove hoare_triple (CLt (Const 0) b :: P) c P *)
  apply consequence_rule with (P' := P) (Q' := P).
  - (* Prove entails (CLt (Const 0) b :: P) P *)
    unfold entails.
    intros s HP' b' Hb'.
    apply HP'.
    simpl In in Hb'.
    right; assumption.
  - (* Use H : hoare_triple P c P *)
    apply H.
  - (* Prove entails P P *)
    apply entails_refl.
Qed.
Theorem hoare_array_write : forall P name idx val,
  hoare_triple (subst_assertion_array P name idx val) 
               (ArrayWrite name (Const idx) val) 
               P.
Proof.
  intros P name idx val.
  apply array_write_rule.
Qed.
Theorem hoare_consequence : forall P P' Q Q' c,
  entails P P' ->
  hoare_triple P' c Q' ->
  entails Q' Q ->
  hoare_triple P c Q.
Proof.
  intros P P' Q Q' c Hpre Hcmd Hpost.
  apply consequence_rule with (P' := P') (Q' := Q'); assumption.
Qed.
Theorem hoare_assign_consequence  :
  forall v e Q P,
    entails P (subst_assertion P v e) ->
    hoare_triple (subst_assertion P v e) (Assign v e) Q ->
    entails Q P ->
    hoare_triple P (Assign v e) P.
Proof.
  intros.
  apply hoare_consequence with (P' := subst_assertion P v e) (Q' := Q); assumption.
Qed.


(* Conversion function from BasicUtility.var to var *)
Definition convert_var (v : BasicUtility.var) : var :=
  match v with
  | _ => Scalar "default"
  end.
Fixpoint translate_aexp (e: aexp) : expr :=
  match e with
  | BA x => VarExpr (convert_var x)  (* Convert BasicUtility.var to var *)
  | Num n => Const n 
  | MNum r n => Const n 
  | APlus e1 e2 => Plus (translate_aexp e1) (translate_aexp e2)
  | AMult e1 e2 => Mult (translate_aexp e1) (translate_aexp e2)
  end.
Fixpoint expr_to_aexp (e : expr) : aexp :=
  match e with
  | Const n => Num n
  | VarExpr (Scalar name) => Num 0 (* Fallback; variables problematic *)
  | VarExpr (Array name idx) => Num 0 (* Arrays unsupported in aexp *)
  | Plus e1 e2 => APlus (expr_to_aexp e1) (expr_to_aexp e2)
  | Mult e1 e2 => AMult (expr_to_aexp e1) (expr_to_aexp e2)
  | Minus e1 e2 => Num 0 (* No subtraction in aexp *)
  end.


Fixpoint aexp_to_expr (e : aexp) : expr :=
  match e with
  | BA x => VarExpr (convert_var x)
  | Num n => Const n
  | MNum r n => Const n (* Still ignoring r *)
  | APlus e1 e2 => Plus (aexp_to_expr e1) (aexp_to_expr e2)
  | AMult e1 e2 => Mult (aexp_to_expr e1) (aexp_to_expr e2)
  end.

Definition extract_var (e : aexp) : option var :=
  match e with
  | BA v => Some (convert_var v)  
  | _ => None 
  end.
Definition convert_cbexp (c : QafnySyntax.cbexp) : cbexpr :=
  match c with
  | QafnySyntax.CEq e1 e2 =>
      CEq (aexp_to_expr e1) (aexp_to_expr e2)
  | QafnySyntax.CLt e1 e2 =>
      CLt (aexp_to_expr e1) (aexp_to_expr e2)
  end.
Definition convert_cpred (W : list QafnySyntax.cbexp) : cpredr :=
  map convert_cbexp W.
Definition translate_cbexp (c : QafnySyntax.cbexp) : expr :=
  match c with
  | QafnySyntax.CEq x y => Eq (aexp_to_expr x) (aexp_to_expr y)
  | QafnySyntax.CLt x y => Lt (aexp_to_expr x) (aexp_to_expr y)
  end.

Fixpoint translate_bexp (b : bexp) : expr :=
  match b with
  | CB c => translate_cbexp (convert_cbexp c) 
  | BEq e1 e2 i a => 
      let left := translate_aexp (convert_varia_to_aexp e1) in
      let right := translate_aexp (convert_varia_to_aexp e2) in
      Minus (Const 1) (Plus (Minus left right) (Minus right left)) 
  | BLt e1 e2 i a => 
      let left := translate_aexp (convert_varia_to_aexp e1) in
      let right := translate_aexp (convert_varia_to_aexp e2) in
      Const (if (Nat.ltb (safe_eval left (fun _ => None)) (safe_eval right (fun _ => None))) then 1 else 0)
  | BTest i a => VarExpr (convert_var i)
  | BNeg b' => Minus (Const 1) (translate_bexp b') 
  end.


Fixpoint eval_cbexpr (b : cbexp) (s : state) : option bool :=
  match b with
  | CEq e1 e2 =>
      match eval_aexp e1 s, eval_aexp e2 s with
      | Some n1, Some n2 => Some (Nat.eqb n1 n2)
      | _, _ => None
      end
  | CLt e1 e2 =>
      match eval_aexp e1 s, eval_aexp e2 s with
      | Some n1, Some n2 => Some (n1 <? n2)
      | _, _ => None
      end
  end.

Fixpoint translate_cbexp (c : cbexp) : expr :=
  match c with
  | CEq x y => Eq (aexp_to_expr x) (aexp_to_expr y)
  | CLt x y => Lt (aexp_to_expr x) (aexp_to_expr y)
  end.

Lemma translate_cbexp_sound : forall c s,
  match eval_cbexpr c s, eval (translate_cbexp c) s with
  | Some true, Some 1 => True
  | Some false, Some 0 => True
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros c s. destruct c as [x y | x y]; simpl.
  - unfold eval_cbexpr, translate_cbexp.
    rewrite !aexp_to_expr_sound.
    destruct (eval_aexp x s) as [n|]; [|auto].
    destruct (eval_aexp y s) as [m|]; [|auto].
    destruct (Nat.eqb n m) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst m.
      rewrite Nat.eqb_refl. auto.
    + apply Nat.eqb_neq in Heq.
      rewrite <- Nat.eqb_neq in Heq. rewrite Heq. auto.
  - unfold eval_cbexpr, translate_cbexp.
    rewrite !aexp_to_expr_sound.
    destruct (eval_aexp x s) as [n|]; [|auto].
    destruct (eval_aexp y s) as [m|]; [|auto].
    destruct (n <? m) eqn:Hlt.
    + auto.
    + auto.
Qed.
Definition extract_var (e : aexp) : option var :=
  match e with
  | BA v => Some (convert_var v)  
  | _ => None 
  end.
Definition convert_cbexp (c : QafnySyntax.cbexp) : cbexp :=
  match c with
  | QafnySyntax.CEq e1 e2 =>
      match extract_var e1, extract_var e2 with
      | Some v1, Some v2 => CBAnd (CBVar v1) (CBVar v2) 
      | _, _ => CBTrue 
      end
  | QafnySyntax.CLt e1 e2 =>
      match extract_var e1, extract_var e2 with
      | Some v1, Some v2 => CBAnd (CBVar v1) (CBVar v2) 
      | _, _ => CBTrue
      end
  end.
Print varia.
Definition convert_varia_to_aexp (v : varia) : aexp :=
  match v with
  | AExp e => e  
  | Index var exp => APlus (BA var) exp  
  end.
Definition safe_eval (e : expr) (s : state) : nat :=
  match eval e s with
  | Some n => n
  | None => 0 
  end.



















(* Hoare logic with classical predicates and consequence rule *)
Inductive hoare_triple : cpredr -> cmd -> cpredr -> Prop :=
  | skip_rule : forall P,
      hoare_triple P Skip P

  | seq_rule : forall P Q R c1 c2,
      hoare_triple P c1 Q ->
      hoare_triple Q c2 R ->
      hoare_triple P (Seq c1 c2) 







