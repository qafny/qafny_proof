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
(* Extend cbexp syntax to handle ArrayWrite *)
Inductive cbexp : Type :=
  | CBTrue : cbexp                (* Represents a constant true condition *)
  | CBVar : var -> cbexp          (* Represents a Boolean variable *)
  | CBArrayWrite : string -> expr -> expr -> cbexp (* Represents an array write operation *)
  | CBAnd : cbexp -> cbexp -> cbexp. (* Represents a conjunction (AND) of two `cbexp` expressions *)
(* Define evaluation of cbexp *)
Fixpoint eval_cbexp (s : state) (b : cbexp) : bool :=
  match b with
  | CBTrue => true
  | CBVar v => match s v with Some n => Nat.ltb 0 n | None => false end
  | CBArrayWrite name idx val => false (* Array writes are not directly evaluable conditions *)
  | CBAnd b1 b2 => andb (eval_cbexp s b1) (eval_cbexp s b2)
  end.
Fixpoint subst_cbexp (b : cbexp) (v : var) (e_subst : expr) : cbexp :=
  match b with
  | CBTrue => CBTrue
  | CBVar x => if eqb_var x v then CBVar v else CBVar x
  | CBArrayWrite name idx val =>
      CBArrayWrite name (subst idx v e_subst) (subst val v e_subst)
  | CBAnd b1 b2 => CBAnd (subst_cbexp b1 v e_subst) (subst_cbexp b2 v e_subst)
  end.

(* Define assertions as cpred *)
Definition cpred := list cbexp.
Definition assertion := cpred.
(* Equality check for expressions *)
Fixpoint expr_eqb (e1 e2 : expr) : bool :=
  match e1, e2 with
  | Const n1, Const n2 => Nat.eqb n1 n2
  | VarExpr v1, VarExpr v2 => eqb_var v1 v2
  | Plus e1a e1b, Plus e2a e2b => expr_eqb e1a e2a && expr_eqb e1b e2b
  | Minus e1a e1b, Minus e2a e2b => expr_eqb e1a e2a && expr_eqb e1b e2b
  | _, _ => false
  end.

Fixpoint subst_array (b : cbexp) (name : string) (idx : expr) (val : expr) : cbexp :=
  match b with
  | CBTrue => CBTrue
  | CBVar v => CBVar v
  | CBArrayWrite n i v =>
      if String.eqb n name && expr_eqb i idx then CBArrayWrite name idx val
      else CBArrayWrite n i v
  | CBAnd b1 b2 => CBAnd (subst_array b1 name idx val) (subst_array b2 name idx val)
  end.

Definition subst_assertion_array (P : assertion) (name : string) (idx : expr) (val : expr) : assertion :=
  map (fun b => subst_array b name idx val) P.

Definition subst_assertion (P : assertion) (v : var) (e_subst : expr) : assertion :=
  map (fun b => subst_cbexp b v e_subst) P.

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
      hoare_triple (subst_assertion_array P name idx val) 
                   (ArrayWrite name idx val) 
                   P.

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
Theorem hoare_assign : forall Q v e,
  hoare_triple Q (Assign v e) Q.
Proof.
  intros. apply assign_rule.
Qed.

(* Theorem: Hoare rule for conditional statements *)
Theorem hoare_if : forall P Q b c1 c2,
  hoare_triple P c1 Q ->
  hoare_triple P c2 Q ->
  hoare_triple P (If b c1 c2) Q.
Proof.
  intros. apply if_rule; assumption.
Qed.

(* Theorem: Hoare rule for while loops *)
Theorem hoare_while : forall P b c,
  hoare_triple P c P ->
  hoare_triple P (While b c) P.
Proof.
  intros. apply while_rule; assumption.
Qed.

(* Theorem: Hoare rule for array writes *)
Theorem hoare_array_write : forall P name idx val,
      hoare_triple (subst_assertion_array P name idx val) 
                   (ArrayWrite name idx val) 
                   P.
Proof.
  intros. apply array_write_rule.
Qed.

(* Axiom stating that BasicUtility.var can be converted to var *)
Axiom var_equiv : BasicUtility.var -> var.
Axiom aexp_to_expr : aexp -> expr.
Axiom pexp_to_expr : pexp -> expr.
Axiom pexp_to_maexp : pexp -> maexp.
Axiom pexp_to_exp : pexp -> exp.
Axiom pexp_to_cmd : pexp -> cmd.
Inductive translate_pexp_rel : pexp -> cmd -> Prop :=
  | TransSkip : 
      translate_pexp_rel PSKIP Skip

  | TransLet : forall (x : BasicUtility.var) (e : aexp) (s : pexp) (c : cmd),
      translate_pexp_rel s c ->
      translate_pexp_rel (Let x (AE e) s) (Seq (Assign (var_equiv x) (aexp_to_expr e)) c)

  | TransAppU : forall l e c,
      translate_pexp_rel e c ->
      translate_pexp_rel (AppU l (pexp_to_exp e)) c

  | TransIf : forall (b : pexp) (s1 s2 : cmd) (c1 c2 : cmd),
      translate_pexp_rel s1 c1 ->
      translate_pexp_rel s2 c2 ->
      translate_pexp_rel (If (pexp_to_expr b)s1 s2) (If (pexp_to_expr b) c1 c2)

  | TransSeq : forall s1 s2 c1 c2,
      translate_pexp_rel s1 c1 ->
      translate_pexp_rel s2 c2 ->
      translate_pexp_rel (PSeq s1 s2) (Seq c1 c2)

  | TransWhile : forall b s c,
      translate_pexp_rel s c ->
      translate_pexp_rel (While b s) (While b c)

  | TransDiffuse : forall (x : BasicUtility.var),
      translate_pexp_rel (Diffuse x) (Assign (var_equiv x) (Const 0)).







