
(* Import necessary modules *)
Require Import String.
Require Import Nat.
Require Import List.
Require Import Bool.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
Require Import SQIR.SQIR.
Require Import QuantumLib.VectorStates.
Require Import SQIR.UnitaryOps.
Require Import Coq.btauto.Btauto Coq.NArith.Nnat. 
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
Require Import ZArith.
Require Import List.
Import ListNotations.
(* Define variables and arrays *)
Inductive var := 
  | Scalar (name : string) (* Scalar variable *)
  | Array (name : string) (index : nat). (* Array variable with index *)
Inductive expr :=
  | VarExpr (v : var) (* Variable *)
  | Const (n : nat) (* Natural number constant *)
  | Plus (e1 e2 : expr) (* Addition *)
  | Minus (e1 e2 : expr) (* Subtraction *)
  | Mult (e1 e2 : expr). (* Multiplication *)

(* Use complex_approxt for complex numbers *)
Definition complex_approx := (Z * Z)%type. (* (real, imag) *)
Inductive mode : Type :=
  | CT  (* Classical *)
  | MT  (* Measurement/Quantum *)
  | Nor (* Normal quantum state *)
  | Had (* Hadamard basis *)
  | Sup (amps : list (complex_approx* nat)) (* Superposition with amplitudes and basis states *)
  | Ent (qubits : list nat). (* Entangled qubits *)
(* Complex number equality *)
Definition complex_approxt_eq (c1 c2 : complex_approx) : bool :=
  let (r1, i1) := c1 in
  let (r2, i2) := c2 in
  andb (Z.eqb r1 r2) (Z.eqb i1 i2).
(*Normalized Complex Numbers: *)
Definition normalize_complex (c : complex_approx) : complex_approx :=
  let (r, i) := c in
  let norm := Z.sqrt (r * r + i * i) in
  if Z.eqb norm 0 then (0, 0)%Z else (Z.div r norm, Z.div i norm)%Z.
(* Complex number addition *)
Definition complex_add (c1 c2 : complex_approx) : complex_approx :=
  let (r1, i1) := c1 in
  let (r2, i2) := c2 in
  (r1 + r2, i1 + i2)%Z.
(* Complex number multiplication *)
Definition complex_mult (c1 c2 : complex_approx) : complex_approx :=
  let (r1, i1) := c1 in
  let (r2, i2) := c2 in
  (r1 * r2 - i1 * i2, r1 * i2 + r2 * i1)%Z.

(* Amplitude list equality *)
Fixpoint amps_eq (amps1 amps2 : list (complex_approx* nat)) : bool :=
  match amps1, amps2 with
  | [], [] => true
  | (c1, n1) :: t1, (c2, n2) :: t2 =>
      andb (andb (complex_approxt_eq c1 c2) (Nat.eqb n1 n2)) (amps_eq t1 t2)
  | _, _ => false
  end.

(* State updated to use complex_approxt *)
Definition state := var -> option (nat * list (complex_approx * nat)).


(* Map mode to a numerical value for array storage *)
Definition mode_to_nat (m : mode) : nat :=
  match m with
  | CT => 0
  | MT => 1
  | Nor => 2
  | Had => 3
  | Sup _ => 4
  | Ent _ => 5
  end.
(* Evaluate expressions *)
Fixpoint eval (e : expr) (s : state) : option nat :=
  match e with
  | Const n => Some n
  | VarExpr v => 
      match s v with
      | Some (n, _) => Some n (* Extract mode *)
      | None => None
      end
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

(* Corrected exec function *)
Fixpoint exec (fuel : nat) (c : cmd) (s : state) : option state :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match c with
      | Skip => Some s
      | Assign v e =>
          match eval e s with
          | Some val => Some (fun x => if eqb_var x v then Some (val, []) else s x)
          | None => None
          end
      | ArrayWrite name idx val =>
          match eval idx s, eval val s with
          | Some i, Some v =>
              Some (fun x =>
                if eqb_var x (Array name i) then
                  match s (Array name i) with
                  | Some (_, amps) => Some (v, amps)
                  | None => Some (v, [])
                  end
                else s x)
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
  | Mult e1 e2 => Mult (subst e1 v e_subst) (subst e2 v e_subst) (* Corrected: Handle multiplication *)
  end.
(* Updated cbexpr type *)
Inductive cbexpr : Type :=
  | CBTrue : cbexpr
  | CBVar : var -> cbexpr
  | CBEq : expr -> expr -> cbexpr
  | CBArrayWrite : string -> expr -> expr -> cbexpr
  | CBAnd : cbexpr -> cbexpr -> cbexpr
  | CBArrayEq : string -> expr -> expr -> cbexpr
  | CBAmpsEq : string -> expr -> list (complex_approx * nat) -> cbexpr.

Definition safe_eval (e : expr) (s : state) : nat :=
  match eval e s with
  | Some n => n
  | None => 0
  end.
(* Corrected eval_cbexp function *)

Fixpoint eval_cbexp (s : state) (b : cbexpr) : bool :=
  match b with
  | CBTrue => true
  | CBVar v =>
      match s v with
      | Some (n, _) => Nat.eqb n 0
      | None => false
      end
  | CBEq e1 e2 =>
      match eval e1 s, eval e2 s with
      | Some n1, Some n2 => Nat.eqb n1 n2
      | _, _ => false
      end
  | CBArrayEq name idx val =>
      match eval idx s, eval val s with
      | Some i, Some v =>
          match s (Array name i) with
          | Some (n, _) => Nat.eqb n v
          | None => false
          end
      | _, _ => false
      end
  | CBAmpsEq name idx expected_amps =>
      match eval idx s with
      | Some i =>
          match s (Array name i) with
          | Some (_, actual_amps) => amps_eq actual_amps expected_amps
          | None => false
          end
      | None => false
      end
  | CBAnd b1 b2 =>
      andb (eval_cbexp s b1) (eval_cbexp s b2)
  | CBArrayWrite _ _ _ => false
  end.

Definition expr_to_cbexp (e : expr) : cbexpr :=
  CBEq e (Const 0).


Fixpoint subst_expr (e : expr) (x : var) (sub : expr) : expr :=
  match e with
  | VarExpr v =>
      if eqb_var v x then sub else VarExpr v
  | Const n => Const n
  | Plus e1 e2 => Plus (subst_expr e1 x sub) (subst_expr e2 x sub)
  | Minus e1 e2 => Minus (subst_expr e1 x sub) (subst_expr e2 x sub)
  | Mult e1 e2 => Mult (subst_expr e1 x sub) (subst_expr e2 x sub)
  end.

(* Corrected subst_cbexp function *)


Fixpoint subst_cbexp (b : cbexpr) (x : var) (sub : expr) : cbexpr :=
  match b with
  | CBTrue => CBTrue

  | CBVar v =>
      CBEq (subst_expr (VarExpr v) x sub) (Const 0)

  | CBEq e1 e2 =>
      CBEq (subst_expr e1 x sub) (subst_expr e2 x sub)

  | CBArrayWrite name idx val =>
      CBArrayWrite name
        (subst_expr idx x sub)
        (subst_expr val x sub)

  | CBAnd b1 b2 =>
      CBAnd (subst_cbexp b1 x sub) (subst_cbexp b2 x sub)

  | CBArrayEq name idx val =>
      CBArrayEq name
        (subst_expr idx x sub)
        (subst_expr val x sub)

  | CBAmpsEq name idx amps =>
      CBAmpsEq name
        (subst_expr idx x sub)
        amps
  end.



Definition cpredr := list cbexpr.

(* Equality check for expressions *)
Fixpoint expr_eqb (e1 e2 : expr) : bool :=
  match e1, e2 with
  | Const n1, Const n2 =>
      Nat.eqb n1 n2

  | VarExpr v1, VarExpr v2 =>
      eqb_var v1 v2

  | Plus e1a e1b, Plus e2a e2b =>
      expr_eqb e1a e2a && expr_eqb e1b e2b

  | Minus e1a e1b, Minus e2a e2b =>
      expr_eqb e1a e2a && expr_eqb e1b e2b

  | Mult e1a e1b, Mult e2a e2b =>
      expr_eqb e1a e2a && expr_eqb e1b e2b

  | _, _ =>
      false
  end.


(* Amplitude encoding/decoding : assign a unique nat based on operation and qubit count *)
Definition encode_amps (amps : list (complex_approx * nat)) (op : single_u) (n : nat) : nat :=
  match op with
  | RH _ => 1  (* Hadamard encoding *)
  | SQFT _ => 2 + n (* QFT encoding *)
  | SRQFT _ => 3 + n (* Inverse QFT encoding *)
  end.



Fixpoint subst_array
  (b : cbexpr) (name : string) (idx : expr) (val : expr)
  : cbexpr :=
  match b with
  | CBTrue => CBTrue

  | CBVar v => CBVar v

  | CBEq e1 e2 =>
      CBEq
        (subst e1 (Array name (safe_eval idx (fun _ => None))) val)
        (subst e2 (Array name (safe_eval idx (fun _ => None))) val)

  | CBArrayWrite n i v =>
      if andb (String.eqb n name) (expr_eqb i idx)
      then CBArrayWrite n idx val
      else CBArrayWrite n i v

  | CBArrayEq n i v =>
      if andb (String.eqb n name) (expr_eqb i idx)
      then CBArrayEq n idx val
      else CBArrayEq n i v

  | CBAmpsEq n i amps =>
      if andb (String.eqb n name) (expr_eqb i idx)
      then CBAmpsEq n idx amps
      else CBAmpsEq n i amps

  | CBAnd b1 b2 =>
      CBAnd
        (subst_array b1 name idx val)
        (subst_array b2 name idx val)
  end.

Definition subst_assertion_array (P : cpredr) (name : string) (idx : expr) (val : expr) : cpredr :=
  map (fun b => subst_array b name idx val) P.

Definition subst_assertion (P : cpredr) (v : var) (e_subst : expr) : cpredr :=
  map (fun b => subst_cbexp b v e_subst) P.

(* Define logical entailment for assertions *)
Definition entails (P Q : cpredr) : Prop :=
  forall s, (forall b, In b P -> eval_cbexp s b = true) -> 
            (forall b, In b Q -> eval_cbexp s b = true).

Definition scalar_var (x : var) : Prop :=
  match x with
  | Scalar _ => True
  | Array _ _ => False
  end.

(* Hoare triples with the consequence rule *)
Inductive hoare_triple : cpredr -> cmd ->cpredr -> Prop :=
  | skip_rule : forall P,
      hoare_triple P Skip P
  | seq_rule : forall P Q R c1 c2,
      hoare_triple P c1 Q ->
      hoare_triple Q c2 R ->
      hoare_triple P (Seq c1 c2) R
  | assign_rule : forall P v e,
    scalar_var v ->
    hoare_triple (subst_assertion P v e) (Assign v e) P
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
                   P
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
  scalar_var v ->
  hoare_triple (subst_assertion P v e) (Assign v e) P.
Proof.
  intros P v e Hv.
  apply assign_rule.
  exact Hv.
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

Definition update_state
  (s : state) (x : var) (v : nat * list (complex_approx * nat)) : state :=
  fun y => if eqb_var y x then Some v else s y.

(*
Definition update_state (s : state) (x : var) (v : nat * list (complex_approx * nat)) : state :=
  fun y => if eqb_var x y then Some v else s y.

*)


Definition convert_vart (v : BasicUtility.var) : var := Scalar "default".

(* Conversion function from BasicUtility.var to var *)
Definition convert_var (v : BasicUtility.var) : var :=
  match v with
  | _ => Scalar "default"
  end.
Fixpoint translate_aexp (e: aexp) : expr :=
  match e with
  | BA x => VarExpr (convert_vart x)
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

Fixpoint translate_cbexp (c : cbexpr) : expr :=
  match c with
  | CBTrue => Const 1

  | CBVar x =>
      VarExpr x

  | CBEq e1 e2 =>
      Minus (Const 1) (Plus (Minus e1 e2) (Minus e2 e1))

  | CBArrayWrite _ _ _ =>
      Const 0

  | CBAnd b1 b2 =>
      Mult (translate_cbexp b1) (translate_cbexp b2)

  | CBArrayEq name idx val =>
      let actual := VarExpr (Array name 0) in
      Minus (Const 1) (Plus (Minus actual val) (Minus val actual))

  | CBAmpsEq _ _ _ =>
      Const 0
  end.



Definition extract_var (e : aexp) : option var :=
  match e with
  | BA v => Some (convert_var v)  
  | _ => None 
  end.
Definition convert_cbexp (c : QafnySyntax.cbexp) : cbexpr :=
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
Definition convert_varia_to_aexp (v : varia) : aexp :=
  match v with
  | AExp e => e  
  | Index var exp => APlus (BA var) exp  
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

Definition varia_to_index (p : varia) : expr :=
  match p with
  | AExp e => translate_aexp e
  | Index x e => Plus (VarExpr (convert_var x)) (translate_aexp e)
  end.

Definition var_to_index (x : var) : expr :=
  match x with
  | Scalar name => VarExpr (Scalar name)
  | Array name idx => Const idx
  end.

(* Convert locus to list of index expressions *)
Definition locus_to_indices_expr (l : locus) : list expr :=
  flat_map
    (fun elem =>
       match elem with
       | (x, BNum idx, _) => [Const idx]
       | (x, _, _) => [VarExpr (convert_var x)]
       end)
    l.

(* Approximate 1/sqrt(2^n) scaled by 1000 *)
Definition scale_factor (n : nat) : complex_approx :=
  (1000 / Z.of_nat (Nat.sqrt (Nat.pow 2 n)), 0)%Z.

(* Hadamard transformation *)
Definition hadamard_amps_single (n : nat) : list (complex_approx * nat) :=
  let scale : complex_approx := (Z.div 1000 (Z.of_nat (Nat.sqrt 2)), 0%Z) in
  map (fun k => (scale, k)) (seq 0 2).

(* QFT amplitudes for n qubits *)
Definition qft_amps (n : nat) : list (complex_approx * nat) :=
  let len := Nat.pow 2 n in
  let scale : complex_approx :=
    (Z.div 1000 (Z.of_nat (Nat.sqrt len)), 0%Z) in
  map (fun k =>
         let phase : Z := Z.div (Z.of_nat k * 314%Z) (Z.of_nat len) in
         let omega_k : complex_approx := (0%Z, phase) in
         let amp := complex_mult scale omega_k in
         (amp, k)
      ) (seq 0 len).

(* Inverse QFT (adjoint of QFT) *)
Definition inv_qft_amps (n : nat) : list (complex_approx * nat) :=
  let len := Nat.pow 2 n in
  let scale : complex_approx := (Z.div 1000 (Z.of_nat (Nat.sqrt len)), 0%Z) in
  map (fun k =>
         let phase : Z := Z.div (Z.of_nat k * (-314)%Z) (Z.of_nat len) in
         let omega_k : complex_approx := (0%Z, phase) in
         let phased_scale := complex_mult scale omega_k in
         (phased_scale, k)
      ) (seq 0 len). 

Definition apply_entanglement (indices : list expr) : cmd :=
  let ent_mode := Const (mode_to_nat (Ent ([] : list nat))) in
  fold_right
    (fun idx acc => Seq (ArrayWrite "q" idx ent_mode) acc)
    Skip
    indices.

Definition extract_entangled_qubits (amps : list ((complex_approx )* nat)) : list nat :=
  map snd amps.
Compute inv_qft_amps 1.
Compute hadamard_amps_single 1.

(* Apply quantum operation *)
Definition apply_quantum_op (op : single_u) (indices : list expr) : cmd :=
  match op with
  |RH _ =>
      fold_right
        (fun idx acc =>
           Seq
             (ArrayWrite "q" idx (Const (mode_to_nat Had)))
             (Seq
                (ArrayWrite "amps" idx (Const (encode_amps (hadamard_amps_single 1) op 1)))
                acc))
        Skip
        indices

  | SQFT _ =>
      let n := length indices in
      fold_right
        (fun idx acc =>
           Seq
             (ArrayWrite "q" idx (Const (mode_to_nat (Sup (qft_amps n)))))
             (Seq
                (ArrayWrite "amps" idx (Const (encode_amps (qft_amps n) op n)))
                acc))
        Skip
        indices

  | SRQFT _ =>
      let n := length indices in
      fold_right
        (fun idx acc =>
           Seq
             (ArrayWrite "q" idx (Const (mode_to_nat (Sup (inv_qft_amps n)))))
             (Seq
                (ArrayWrite "amps" idx (Const (encode_amps (inv_qft_amps n) op n)))
                acc))
        Skip
        indices
  end.

(*  Intermediate Representation Operations *)
Inductive ir_op :=
  | IRCast (name : string) (idx : expr) (tgt_mode : mode)
      (* Casts the mode of q[name][idx] to tgt_mode *)
  | IRLocate (name : string) (indices : list expr)
      (* Marks the locations of qubits in array q[name][i] *)
  | IRMap (name : string) (f : expr -> expr)
      (* Applies f to every element q[name][i] *)
  | IRTypeUpdate (name : string) (idx : expr) (m : nat)
      (* Updates the type at q[name][idx] to m *)
  | IRAmpModify (name : string) (idx : expr) (amp : complex_approx)
      (* Multiplies amplitudes of q[name][idx] by amp *)
  | IRPartialMap (name : string) (f : expr -> expr) (cond : expr)
      (* Applies f to q[name][i] where cond(i) = true *)
  | IRJoin (name : string) (idx : expr) (locus : list expr)
      (* Joins q[name][idx] to a locus of indices *)
  | IRDelete (name : string) (cond : expr -> bool)
      (* Deletes elements q[name][i] where cond(i) = true *)
  | IRSumAmplitudes (name : string) (indices : list expr) (result : var)
      (* Sums squared amplitude magnitudes of q[name][i] for given indices into result *)
  | IRCopy (src_name : string) (src_idx : expr) (dst_name : string) (dst_idx : expr)
      (* Copies q[src_name][src_idx] into q[dst_name][dst_idx] *)
  | IRMerge (name : string) (idx1 idx2 tgt_idx : expr).
      (* Merges q[name][idx1] and q[name][idx2] into q[name][tgt_idx] *)

(* Standard Cantor pairing *)
Definition nat_pair (x y : nat) : nat :=
  (x + y) * (x + y + 1) / 2 + y.

(* Encode a list (complex_approx * nat) as a single nat *)
Fixpoint encode_amp_list (amps : list (complex_approx * nat)) : nat :=
  match amps with
  | nil => 0
  | (c, k) :: tl =>
      let r := Z.to_nat (fst c) in
      let i := Z.to_nat (snd c) in
      let encoded_c := nat_pair (nat_pair r i) k in
      nat_pair encoded_c (encode_amp_list tl)
  end.

(* Hoare Logic Rules for Intermediate Representation Operations *)

Fixpoint wp_array_writes
  (P : cpredr) (name : string) (f : expr -> expr) (xs : list nat)
  : cpredr :=
  match xs with
  | nil => P
  | i :: xs' =>
      subst_assertion_array
        (wp_array_writes P name f xs')
        name
        (Const i)
        (f (Const i))
  end.

Definition wp_partial_map
  (P : cpredr) (name : string) (f : expr -> expr) (cond : expr) (n : nat)
  : cpredr :=
  P ++ wp_array_writes P name f (seq 0 n).

Inductive hoare_ir : nat -> cpredr -> ir_op -> cpredr -> Prop :=
  | hoare_ir_cast : forall n P name idx tgt_mode,
      hoare_ir n
        (subst_assertion_array P name idx (Const (mode_to_nat tgt_mode)))
        (IRCast name idx tgt_mode)
        P

  | hoare_ir_locate : forall n P name indices,
      hoare_ir n P (IRLocate name indices) P

  | hoare_ir_typeupdate : forall n P name idx m,
      hoare_ir n
        (subst_assertion_array P name idx (Const m))
        (IRTypeUpdate name idx m)
        P

  | hoare_ir_ampmodify : forall n P name idx amp,
      let base_amps : list (complex_approx * nat) :=
        (amp, 0) :: ((0%Z, 0%Z), 1) :: nil in
      hoare_ir n
        (subst_assertion_array
           P name idx (Const (encode_amp_list base_amps)))
        (IRAmpModify name idx amp)
        P

  | hoare_ir_map : forall n P name f,
      hoare_ir n
        (wp_array_writes P name f (seq 0 n))
        (IRMap name f)
        P

  | hoare_ir_partialmap : forall n P name f cond,
    hoare_ir n
      (wp_partial_map P name f cond n)
      (IRPartialMap name f cond)
      P

  | hoare_ir_join : forall n P name idx loc,
      let ent_indices := map (fun e => safe_eval e (fun _ => None)) loc in
      let ent_expr := Const (mode_to_nat (Ent ent_indices)) in
      hoare_ir n
        (subst_assertion_array P name idx ent_expr)
        (IRJoin name idx loc)
        P

  | hoare_ir_delete : forall n P name cond,
      hoare_ir n P (IRDelete name cond) P

  |  hoare_ir_sum : forall n P name indices v,
    scalar_var v ->
    hoare_ir n
      (subst_assertion P v (Const 0))
      (IRSumAmplitudes name indices v)
      P

  | hoare_ir_copy : forall n P src_name src_idx dst_name dst_idx,
      hoare_ir n
        (subst_assertion_array
           P
           dst_name
           dst_idx
           (VarExpr (Array src_name (safe_eval src_idx (fun _ => None)))))
        (IRCopy src_name src_idx dst_name dst_idx)
        P

  | hoare_ir_merge : forall n P name idx1 idx2 tgt_idx,
      hoare_ir n
        (subst_assertion_array
           P
           name
           tgt_idx
           (Plus
              (VarExpr (Array name (safe_eval idx1 (fun _ => None))))
              (VarExpr (Array name (safe_eval idx2 (fun _ => None))))))
        (IRMerge name idx1 idx2 tgt_idx)
        P.

(* execution semantics for Intermediate Representation Operations *)
Fixpoint exec_ir (fuel : nat) (ir : ir_op) (s : state) : option state :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match ir with
      | IRCast name idx tgt_mode =>
          match eval idx s with
          | Some i =>
              let new_mode := mode_to_nat tgt_mode in
              Some (fun x =>
                if eqb_var x (Array name i)
                then match s (Array name i) with
                     | Some (_, amps) => Some (new_mode, amps)
                     | None => Some (new_mode, [])
                     end
                else s x)
          | None => None
          end
      | IRLocate _ _ => Some s
      | IRMap name f =>
          Some (fun x =>
            match x with
            | Array n i =>
                if String.eqb n name
                then match eval (f (Const i)) s with
                     | Some v =>
                         match s x with
                         | Some (_, amps) => Some (v, amps)
                         | None => Some (v, [])
                         end
                     | None => s x
                     end
                else s x
            | _ => s x
            end)
      | IRTypeUpdate name idx m =>
          match eval idx s with
          | Some i =>
              Some (fun x =>
                if eqb_var x (Array name i)
                then match s (Array name i) with
                     | Some (_, amps) => Some (m, amps)
                     | None => Some (m, [])
                     end
                else s x)
          | None => None
          end
      | IRAmpModify name idx amp =>
          match eval idx s with
          | Some i =>
              match s (Array name i) with
              | Some (v, amps) =>
                  let new_amps := map (fun '(c, n) => (complex_mult amp c, n)) amps in
                  Some (update_state s (Array name i) (v, new_amps))
              | None => None
              end
          | None => None
          end
      | IRPartialMap name f cond =>
          match eval cond s with
          | Some n =>
              if Nat.eqb n 0 then Some s
              else exec_ir fuel' (IRMap name f) s
          | None => None
          end
      | IRJoin name idx locus =>
          let loc_vals := map (fun e => eval e s) locus in
          match eval idx s with
          | Some i =>
              if existsb (fun x => match x with None => true | _ => false end) loc_vals
              then None
              else
                let indices := map (fun x => match x with Some n => n | None => 0 end) loc_vals in
                Some (fun x =>
                  if eqb_var x (Array name i)
                  then Some (mode_to_nat (Ent indices), [])
                  else s x)
          | None => None
          end
      | IRDelete name cond =>
          Some (fun x =>
            match x with
            | Array n i =>
                if andb (String.eqb n name) (cond (Const i))
                then None
                else s x
            | _ => s x
            end)
      | IRSumAmplitudes name indices result =>
          let index_vals := map (fun e => eval e s) indices in
          if existsb (fun x => match x with None => true | _ => false end) index_vals
          then None
          else
            let sum :=
              fold_left
                (fun acc opt_i =>
                   match opt_i with
                   | Some i =>
                       match s (Array name i) with
                       | Some (_, amps) =>
                           fold_left
                             (fun acc' '(c, _) =>
                                let '(r, im) := c in
                                acc' + Z.to_nat (r * r + im * im)%Z)
                             amps acc
                       | None => acc
                       end
                   | None => acc
                   end)
                index_vals 0 in
            Some (update_state s result (sum, []))
      | IRCopy src_name src_idx dst_name dst_idx =>
          match eval src_idx s, eval dst_idx s with
          | Some si, Some di =>
              match s (Array src_name si) with
              | Some val => Some (update_state s (Array dst_name di) val)
              | None => None
              end
          | _, _ => None
          end
      | IRMerge name idx1 idx2 tgt_idx =>
          match eval idx1 s, eval idx2 s, eval tgt_idx s with
          | Some i1, Some i2, Some ti =>
              match s (Array name i1), s (Array name i2) with
              | Some (v1, _), Some (v2, _) =>
                  Some (update_state s (Array name ti) (v1 + v2, []))
              | _, _ => None
              end
          | _, _, _ => None
          end
      end
  end.

(* Mapping from qafny to IR *)
Fixpoint compile_pexp_to_ir (p : pexp) : list ir_op :=
  match p with
  | PSKIP => []

  | Let x (AE a) s =>
      IRCopy "temp" (translate_aexp a) "q" (Const 0)
        :: compile_pexp_to_ir s

  | Let x (Meas y) s =>
      let y_idx := var_to_index (convert_var y) in
      IRLocate "q" [y_idx] ::
      IRTypeUpdate "q" y_idx (mode_to_nat MT) ::
      IRSumAmplitudes "q" [y_idx] (convert_var x)
        :: compile_pexp_to_ir s

  | AppSU (RH p) =>
  let idx := varia_to_index p in
  match hadamard_amps_single 1 with
  | (c, _) :: _ =>
      IRCast "q" idx Had ::
      IRAmpModify "amps" idx c ::
      nil
  | [] =>
      IRCast "q" idx Had ::
      nil
   end

  | AppSU (SQFT x) =>
  let idx := var_to_index (convert_var x) in
  let amps := qft_amps 1 in
  match amps with
  | (c, _) :: _ =>
      IRCast "q" idx (Sup amps) ::
      IRAmpModify "amps" idx c ::
      nil
  | [] =>
      IRCast "q" idx (Sup nil) ::
      nil
  end

  | AppSU (SRQFT x) =>
  let idx := var_to_index (convert_var x) in
  let amps := inv_qft_amps 1 in
  match amps with
  | (c, _) :: _ =>
      IRCast "q" idx (Sup amps) ::
      IRAmpModify "amps" idx c ::
      nil
  | [] =>
      IRCast "q" idx (Sup nil) ::
      nil
  end

  | AppU l e =>
  let indices := locus_to_indices_expr l in
  match indices with
  | idx1 :: idxs =>
      if String.eqb "e" "CNOT"
      then
        IRJoin "q" idx1 idxs ::
        IRAmpModify "amps" idx1 (1%Z, 0%Z) ::
        nil
      else
        IRJoin "q" idx1 idxs ::
        nil
  | _ => nil
  end

  | PSeq s1 s2 =>
      compile_pexp_to_ir s1 ++ compile_pexp_to_ir s2

  | QafnySyntax.If x s1 =>
      let cond := translate_bexp x in
      let s1_ir := compile_pexp_to_ir s1 in
      map (fun ir =>
             match ir with
             | IRPartialMap name f cond' =>
                 IRPartialMap name f (Plus cond cond') (* combine conditions *)
             | _ => ir
             end) s1_ir

  | For x l h b p =>
    let x_var := convert_var x in
    let idx := var_to_index x_var in
    let l' := translate_aexp l in
    let h' := translate_aexp h in
    let lo := safe_eval l' (fun _ => None) in
    let hi := safe_eval h' (fun _ => None) in
    let range := seq lo (hi - lo) in
    flat_map
      (fun i =>
         let s := fun _ => Some (i, []) in
         let cond_val := safe_eval (translate_bexp b) s in
         if Nat.eqb cond_val 0 then []
         else
           let cond_expr := translate_cbexp (CBArrayEq "q" (VarExpr x_var) (Const i)) in
           let p_ir := compile_pexp_to_ir p in
           map (fun ir =>
                  match ir with
                  | IRPartialMap name f cond' =>
                      IRPartialMap name f (Plus cond_expr cond')
                  | _ =>
                      IRPartialMap "q" (fun e => e) cond_expr
                  end) p_ir)
      range

  | Diffuse x =>
  let idx := varia_to_index x in
  IRLocate "q" [idx] ::
  IRAmpModify "amps" idx (1%Z, 0%Z) ::
  nil
  end.

(* A single cbexpr holds in state s *)
Definition eval_pred (p : cbexpr) (s : state) : Prop :=
  eval_cbexp s p = true.

(* A cpredr (list of cbexpr) holds in state s *)
Definition sat (P : cpredr) (s : state) : Prop :=
  List.Forall (fun p => eval_pred p s) P.

(* Semantic meaning of an IR triple wrt exec_ir *)
Definition hoare_ir_sem (P : cpredr) (op : ir_op) (Q : cpredr) : Prop :=
  forall fuel s s',
    exec_ir fuel op s = Some s' ->
    sat P s ->
    sat Q s'.



Lemma hoare_ir_locate_sound :
  forall P name indices,
    hoare_ir_sem P (IRLocate name indices) P.
Proof.
  unfold hoare_ir_sem, sat, eval_pred.
  intros P name indices fuel s s' Hexec Hsat.
  destruct fuel as [|fuel']; simpl in Hexec; try discriminate.
  inversion Hexec; subst s'; assumption.
Qed.

Lemma judge_IRCast :
  forall n P name idx tgt_mode,
    hoare_ir n
      (subst_assertion_array P name idx (Const (mode_to_nat tgt_mode)))
      (IRCast name idx tgt_mode)
      P.
Proof.
  intros.
  constructor.
Qed.

Lemma judge_IRTypeUpdate :
  forall n P name idx m,
    hoare_ir n
      (subst_assertion_array P name idx (Const m))
      (IRTypeUpdate name idx m)
      P.
Proof.
  intros.
  constructor.
Qed.

Lemma judge_IRAmpModify :
  forall n P name idx amp,
    let base_amps : list (complex_approx * nat) :=
      (amp, 0) :: ((0%Z, 0%Z), 1) :: nil in
    hoare_ir n
      (subst_assertion_array
         P name idx (Const (encode_amp_list base_amps)))
      (IRAmpModify name idx amp)
      P.
Proof.
  intros.
  constructor.
Qed.




Definition lower_one_ir_to_cmd (n_qubits : nat) (op : ir_op) : cmd :=
  match op with
  | IRCast name idx mode =>
      ArrayWrite name idx (Const (mode_to_nat mode))

  | IRTypeUpdate name idx m =>
      ArrayWrite name idx (Const m)

  | IRAmpModify name idx amp =>
      let base_amps : list (complex_approx * nat) :=
        (amp, 0) :: ((0%Z, 0%Z), 1) :: nil in
      ArrayWrite name idx (Const (encode_amp_list base_amps))

  | IRLocate name indices =>
      Skip

  | IRMap name f =>
      fold_right
        (fun i acc =>
           Seq (ArrayWrite name (Const i) (f (Const i))) acc)
        Skip
        (seq 0 n_qubits)

  | IRPartialMap name f cond =>
      If cond
        (fold_right
           (fun i acc =>
              Seq (ArrayWrite name (Const i) (f (Const i))) acc)
           Skip
           (seq 0 n_qubits))
        Skip

  | IRJoin name idx locus =>
      let ent_indices := map (fun e => safe_eval e (fun _ => None)) locus in
      let ent_expr := Const (mode_to_nat (Ent ent_indices)) in
      ArrayWrite name idx ent_expr

  | IRDelete name cond =>
      Skip

  | IRSumAmplitudes name indices result =>
      Assign result (Const 0)

  | IRCopy src_name src_idx dst_name dst_idx =>
      ArrayWrite dst_name dst_idx (VarExpr (Array src_name (safe_eval src_idx (fun _ => None))))

  | IRMerge name idx1 idx2 tgt_idx =>
      ArrayWrite name tgt_idx
        (Plus
          (VarExpr (Array name (safe_eval idx1 (fun _ => None)))
          )
          (VarExpr (Array name (safe_eval idx2 (fun _ => None)))
          ))
  end.
Fixpoint lower_ir_to_cmd (n : nat) (ops : list ir_op) : cmd :=
  match ops with
  | nil => Skip
  | op :: ops' =>
      Seq (lower_one_ir_to_cmd n op)
          (lower_ir_to_cmd n ops')
  end.

(* Rough qubit-counting heuristic for a pexp program *)
Fixpoint count_qubits_in_pexp (p : pexp) : nat :=
  match p with
  | PSKIP => 0

  | Let _ _ s =>
      count_qubits_in_pexp s

  | AppSU _ =>
      (* Single-qubit gate; at least one qubit is involved *)
      1

  | AppU l _ =>
      (* Use the size of the locus as a lower bound on qubit count *)
      length (locus_to_indices_expr l)

  | PSeq s1 s2 =>
      Nat.max (count_qubits_in_pexp s1) (count_qubits_in_pexp s2)

  | QafnySyntax.If _ s1 =>
      (* Only one branch is explicit here *)
      count_qubits_in_pexp s1

  | For _ _ _ _ body =>
      count_qubits_in_pexp body

  | Diffuse _ =>
      1
  end.



Definition classical_program_of (e : pexp) : cmd :=
  let n := count_qubits_in_pexp e in
  lower_ir_to_cmd n (compile_pexp_to_ir e).



(* Translate a classical+quantum state into a logical assertion *)
Definition trans_state_elem (se : state_elem) : nat :=
  match se with
  | Nval r b => 1 (* Simplified: non-zero for normal mode *)
  | Hval b => 2   (* Simplified: distinct value for Hadamard mode *)
  | Cval m f => m (* Simplified: use the number of states *)
  end.
Definition trans_state_amps (se : state_elem) : list (complex_approx * nat) :=
  match se with
  | Nval r b => [] (* Normal: no amplitude info *)
  | Hval b => hadamard_amps_single 1
  | Cval m f => [] (* Classical: assume no amps; or customize *)
  end.
Definition var_to_string (v : BasicUtility.var) : string :=
  match v with
  | _ => "default"  
  end.

Definition trans_locus (l : locus) : option (string * nat) :=
  match l with
  | (x, BNum idx, BNum _) :: _ => Some (var_to_string x, idx)
  | _ => None
  end.

(* Classical Semantics *)
Definition hoare_triple_sem (P : cpredr) (c : cmd) (Q : cpredr) : Prop :=
  forall (s s' : state) (fuel : nat),
    (forall b, In b P -> eval_cbexp s b = true) ->
    exec fuel c s = Some s' ->
    (forall b, In b Q -> eval_cbexp s' b = true).
Fixpoint trans_qpred (env : aenv) (qp :qpred) : cpredr :=
  match qp with
  | (SV l, se) :: rest =>
      match trans_locus l with
      | Some (name, idx) =>
          let mode := trans_state_elem se in
          let amps := trans_state_amps se in
          CBArrayEq name (Const idx) (Const mode)
          :: CBAmpsEq name (Const idx) amps
          :: trans_qpred env rest
      | None => trans_qpred env rest
      end
  | (_, _) :: rest => trans_qpred env rest
  | [] => []
  end.

Definition convert_locus_cpred (W : LocusProof.cpred) : cpredr :=
  map (fun _ => CBTrue) W.

Definition trans (env : aenv) (W : LocusProof.cpred) (P : qpred) : cpredr :=
  convert_locus_cpred W ++ trans_qpred env P.
Check trans.

Print triple.
Lemma entails_by_subset :
  forall P Q : list cbexpr,
    (forall b, In b Q -> In b P) ->
    entails P Q.
Proof.
  unfold entails.
  intros P Q Hsubset s Hpre b HbQ.
  apply Hpre, Hsubset, HbQ.
Qed.

Lemma trans_empty_eq :
  forall env,
    trans env [] [] = [].
Proof.
  intros env.
  unfold trans.
  simpl.
  reflexivity.
Qed.

Lemma hoare_skip_empty :
  hoare_triple (@nil cbexpr) Skip (@nil cbexpr).
Proof.
  apply skip_rule.
Qed.


Lemma hoare_seq_empty :
  forall c1 c2,
    hoare_triple (nil : list cbexpr) c1 (nil : list cbexpr) ->
    hoare_triple (nil : list cbexpr) c2 (nil : list cbexpr) ->
    hoare_triple (nil : list cbexpr) (Seq c1 c2) (nil : list cbexpr).
Proof.
  intros.
  eapply seq_rule; eauto.
Qed.


Lemma skip_preserves_preds :
  forall (rmax : nat) (q : atype) (env : aenv) (T : type_map)
         (W : cpred) (P : qpred),
    @locus_system rmax q env T PSKIP T ->
    W = W /\ P = P.
Proof.
  intros rmax q env T W P Hlsys.
  split; reflexivity.
Qed.

Lemma type_check_proof_weaken_right :
  forall rmax q env T T1 W1 W2 e,
    type_check_proof rmax q env T T1 W1 W2 e ->
    T1 = T ->
    type_check_proof rmax q env T T W1 W2 e.
Proof.
  intros. subst. assumption.
Qed.
Lemma pred_check_invariant :
  forall env T T' W Q,
    pred_check env T' (W, Q) ->
    T' = T ->
    pred_check env T (W, Q).
Proof.
  intros env T T' W Q [Hcpred Hqpred] Heq. subst.
  split; auto.
Qed.
Lemma type_check_proof_invariant :
  forall rmax q env T T1 W P W' Q e,
    type_check_proof rmax q env T T1 (W, P) (W', Q) e ->
    T1 = T ->
    type_check_proof rmax q env T T (W, P) (W', Q) e.
Proof.
  intros rmax q env T T1 W P W' Q e Htype Heq. subst. assumption.
Qed.
Lemma exec_skip_correct :
  forall fuel s s',
    exec fuel Skip s = Some s' ->
    s' = s.
Proof.
  intros fuel s s' Hexec.
  destruct fuel as [| fuel']; simpl in Hexec.
  - discriminate.
  - inversion Hexec. reflexivity.
Qed.
Lemma trans_preserved_skip :
  forall env W P b,
    In b (trans env W P) -> In b (trans env W P).
Proof.
  intros. assumption.
Qed.

Lemma trans_eq_preserved :
  forall env W P W' Q,
    W = W' ->
    P = Q ->
    trans env W P = trans env W' Q.
Proof.
  intros env W P W' Q HeqW HeqP.
  subst. reflexivity.
Qed.

Lemma skip_preserves_preds_fixed :
  forall (rmax : nat) (q : atype) (env : aenv) (T : type_map)
         (W W' : cpred) (P Q : qpred),
    @locus_system rmax q env T PSKIP T ->
    W = W' ->
    P = Q ->
    W = W' /\ P = Q.
Proof.
  intros. split; assumption.
Qed.
Lemma skip_preserves_WP :
  forall (rmax : nat) (q : atype) (env : aenv) (T : type_map)
         (W W' : cpred) (P Q : qpred),
    @locus_system rmax q env T PSKIP T ->
    W' = W ->
    Q = P ->
    trans env W P = trans env W' Q.
Proof.
  intros rmax q env T W W' P Q Hsys HW HQ.
  subst W'. subst Q.
  reflexivity.
Qed.

Lemma pred_check_implies_same_cpred :
  forall env T P0 W P W' Q,
    pred_check env T P0 ->
    P0 = (W, P) ->
    P0 = (W', Q) ->
    W = W'.
Proof.
  intros env T P0 W P W' Q Hpred H1 H2.
  rewrite H1 in H2.
  injection H2 as HW HP.
  assumption.
Qed.
Lemma trans_equality :
  forall (env : aenv) (W W' : cpred) (P Q : qpred),
    W = W' ->
    P = Q ->
    trans env W P = trans env W' Q.
Proof.
  intros env W W' P Q HW HQ.
  subst W'.
  subst Q.
  reflexivity.
Qed.
Lemma skip_invariance :
  forall (rmax : nat) (q : atype) (env : aenv) (T : type_map) 
         (W W' : cpred) (P Q : qpred) (fuel : nat) (s : state),
    @locus_system rmax q env T PSKIP T ->
    W' = W ->
    Q = P ->
    forall b, In b (trans env W' Q) -> exec fuel Skip s = Some s -> In b (trans env W P).
Proof.
  intros rmax q env T W W' P Q fuel s Hsys HW HQ b HIn Hexec.
  subst W'.
  subst Q.
  assumption.
Qed.


(* Define model semantics for cpredr *)
Definition set (A : Type) := A -> Prop.

Definition model (P : cpredr) (s : state) : Prop :=
  forall b, In b P -> eval_cbexp s b = true.

Definition Mod (P : cpredr) : set state :=
  fun s => model P s.

(* If s is a model of P, then s satisfies all assertions in P *)
Theorem model_satisfies_all : forall P s b,
  model P s -> In b P -> eval_cbexp s b = true.
Proof.
  intros P s b Hmodel Hb.
  apply Hmodel; assumption.
Qed.

(* If s' ∈ Mod(Q'), then Q' holds in state s' *)
Theorem in_mod_implies_eval : forall Q' s',
  Mod Q' s' -> forall b, In b Q' -> eval_cbexp s' b = true.
Proof.
  unfold Mod, model. intros. apply H; assumption.
Qed.

Inductive hoare_ir_list : nat -> cpredr -> list ir_op -> cpredr -> Prop :=
  | hoare_ir_list_nil : forall n P,
      hoare_ir_list n P nil P

  | hoare_ir_list_cons : forall n P Q R op ops,
      hoare_ir n P op Q ->
      hoare_ir_list n Q ops R ->
      hoare_ir_list n P (op :: ops) R

  | hoare_ir_list_consequence :
      forall n P P' Q Q' ops,
        entails P P' ->
        hoare_ir_list n P' ops Q' ->
        entails Q' Q ->
        hoare_ir_list n P ops Q.



(* Composition for concatenation (needed for PSeq / ++) *)

Lemma entails_refl :
  forall P, entails P P.
Proof.
  unfold entails.
  intros P s Hsat b Hb.
  apply Hsat.
  exact Hb.
Qed.

Lemma entails_cons_drop :
  forall b P,
    entails (b :: P) P.
Proof.
  unfold entails.
  intros b P s Hsat x Hx.
  apply Hsat.
  right.
  exact Hx.
Qed.

Lemma hoare_ir_list_app :
  forall n P Q R ops1 ops2,
    hoare_ir_list n P ops1 Q ->
    hoare_ir_list n Q ops2 R ->
    hoare_ir_list n P (ops1 ++ ops2) R.
Proof.
  intros n P Q R ops1 ops2 H1 H2.
  induction H1.
  - simpl. exact H2.
  - simpl. econstructor.
    + exact H.
    + apply IHhoare_ir_list.
      exact H2.
  - eapply hoare_ir_list_consequence.
    + exact H.
    + apply IHhoare_ir_list.
      eapply hoare_ir_list_consequence.
      * exact H0.
      * exact H2.
      * apply entails_refl.
    + apply entails_refl.
Qed.

Lemma hoare_ir_list_map_id :
  forall n (P Q : cpredr) (ops : list ir_op) (g : ir_op -> ir_op),
    (forall op, g op = op) ->
    hoare_ir_list n P ops Q ->
    hoare_ir_list n P (map g ops) Q.
Proof.
  intros n P Q ops g Hg H.
  induction H.
  - simpl. constructor.
  - simpl. rewrite Hg. econstructor; eauto.
  - eapply hoare_ir_list_consequence.
    + exact H.
    + apply IHhoare_ir_list.
    + exact H1.
Qed.

Lemma hoare_ir_cast_rule :
  forall n P name idx tgt_mode,
    hoare_ir n
      (subst_assertion_array P name idx (Const (mode_to_nat tgt_mode)))
      (IRCast name idx tgt_mode)
      P.
Proof.
  intros.
  constructor.
Qed.

Lemma hoare_ir_typeupdate_rule :
  forall n P name idx m,
    hoare_ir n
      (subst_assertion_array P name idx (Const m))
      (IRTypeUpdate name idx m)
      P.
Proof.
  intros.
  constructor.
Qed.

Lemma hoare_ir_ampmodify_rule :
  forall n P name idx amp,
    let base_amps : list (complex_approx * nat) :=
      (amp, 0) :: ((0%Z, 0%Z), 1) :: nil in
    hoare_ir n
      (subst_assertion_array
         P name idx (Const (encode_amp_list base_amps)))
      (IRAmpModify name idx amp)
      P.
Proof.
  intros.
  constructor.
Qed.


Theorem Qafny_compilation_generates_IR :
  forall rmax t env T W P e W' Q,
    type_check_proof rmax t env T T (W, P) (W', Q) e ->
    @triple rmax t env T (W, P) e (W', Q) ->
    exists ops,
      ops = compile_pexp_to_ir e.
Proof.
  intros.
  exists (compile_pexp_to_ir e).
  reflexivity.
Qed.

Fixpoint ir_pre (n : nat) (Q : cpredr) (ops : list ir_op) : cpredr :=
  match ops with
  | nil => Q
  | op :: ops' =>
      let Q' := ir_pre n Q ops' in
      match op with
      | IRCast name idx m =>
          subst_assertion_array Q' name idx (Const (mode_to_nat m))

      | IRTypeUpdate name idx m =>
          subst_assertion_array Q' name idx (Const m)

      | IRAmpModify name idx amp =>
          let base_amps : list (complex_approx * nat) :=
            (amp, 0) :: ((0%Z, 0%Z), 1) :: nil in
          subst_assertion_array Q' name idx
            (Const (encode_amp_list base_amps))

      | IRLocate _ _ =>
          Q'

      | IRMap name f =>
          wp_array_writes Q' name f (seq 0 n)

      | IRPartialMap name f cond =>
    wp_partial_map Q' name f cond n

      | IRJoin name idx loc =>
          let ent_indices := map (fun e => safe_eval e (fun _ => None)) loc in
          let ent_expr := Const (mode_to_nat (Ent ent_indices)) in
          subst_assertion_array Q' name idx ent_expr

      | IRDelete _ _ =>
          Q'

      | IRSumAmplitudes _ _ result =>
          subst_assertion Q' result (Const 0)

      | IRCopy src_name src_idx dst_name dst_idx =>
          subst_assertion_array
            Q'
            dst_name
            dst_idx
            (VarExpr (Array src_name (safe_eval src_idx (fun _ => None))))

      | IRMerge name idx1 idx2 tgt_idx =>
          subst_assertion_array
            Q'
            name
            tgt_idx
            (Plus
               (VarExpr (Array name (safe_eval idx1 (fun _ => None))))
               (VarExpr (Array name (safe_eval idx2 (fun _ => None)))))
      end
  end.


Lemma entails_cons_drop2 :
  forall b1 b2 P,
    entails (b1 :: b2 :: P) P.
Proof.
  unfold entails.
  intros b1 b2 P s Hsat x Hx.
  apply Hsat.
  right.
  right.
  exact Hx.
Qed.

Lemma ir_pre_app :
  forall n Q ops1 ops2,
    ir_pre n Q (ops1 ++ ops2) =
    ir_pre n (ir_pre n Q ops2) ops1.
Proof.
  intros n Q ops1.
  induction ops1 as [|op ops1 IH]; intros ops2; simpl.
  - reflexivity.
  - rewrite IH.
    destruct op; simpl; reflexivity.
Qed.


Definition map_if_ir (cond : expr) (ir : ir_op) : ir_op :=
  match ir with
  | IRPartialMap name f cond' =>
      IRPartialMap name f (Plus cond cond')
  | _ => ir
  end.

Lemma ir_pre_map_if :
  forall n Q cond ops,
    ir_pre n Q (map (map_if_ir cond) ops) =
    ir_pre n Q ops.
Proof.
  intros n Q cond ops.
  induction ops as [|op ops IH]; simpl.
  - reflexivity.
  - destruct op; simpl; rewrite IH; reflexivity.
Qed.

Lemma entails_app_left :
  forall P Q,
    entails (P ++ Q) P.
Proof.
  unfold entails.
  intros P Q s Hsat b Hb.
  apply Hsat.
  apply in_or_app.
  left.
  exact Hb.
Qed.

Lemma entails_app_right :
  forall P Q,
    entails (P ++ Q) Q.
Proof.
  unfold entails.
  intros P Q s Hsat b Hb.
  apply Hsat.
  apply in_or_app.
  right.
  exact Hb.
Qed.

Lemma hoare_skip_from_app :
  forall P Q,
    hoare_triple (P ++ Q) Skip P.
Proof.
  intros P Q.
  eapply consequence_rule.
  - apply entails_refl.
  - apply skip_rule.
  - apply entails_app_left.
Qed.

Lemma hoare_ir_map_if_op :
  forall n P Q op cond,
    hoare_ir n P op Q ->
    hoare_ir n P (map_if_ir cond op) Q.
Proof.
  intros n P Q op cond H.
  inversion H; subst; simpl; try constructor.

  - (* IRPartialMap *)
    change (wp_partial_map Q name f cond0 n)
      with (wp_partial_map Q name f (Plus cond cond0) n).
    apply hoare_ir_partialmap.
- exact H0.
Qed.


Lemma hoare_ir_list_map_if :
  forall n P Q ops cond,
    hoare_ir_list n P ops Q ->
    hoare_ir_list n P (map (map_if_ir cond) ops) Q.
Proof.
  intros n P Q ops cond H.
  induction H.
  - simpl. constructor.

  - simpl.
    econstructor.
    + apply hoare_ir_map_if_op.
      exact H.
    + exact IHhoare_ir_list.

  - eapply hoare_ir_list_consequence.
    + exact H.
    + exact IHhoare_ir_list.
    + exact H1.
Qed.

Definition map_for_ir (cond : expr) (ir : ir_op) : ir_op :=
  match ir with
  | IRPartialMap name f cond' =>
      IRPartialMap name f (Plus cond cond')
  | _ =>
      IRPartialMap "q" (fun e0 : expr => e0) cond
  end.

Definition  ir_pre_map_for_result
  (n : nat) (Q : cpredr) (cond : expr) (ops : list ir_op) : cpredr :=
  match ops with
  | nil => Q
  | op :: ops' =>
      ir_pre n Q (map (map_for_ir cond) (op :: ops'))
  end.
Lemma ir_pre_map_for_ir :
  forall n Q cond ops,
    ir_pre n Q (map (map_for_ir cond) ops) =
    ir_pre_map_for_result n Q cond ops.
Proof.
  intros.
  destruct ops; reflexivity.
Qed.

Lemma hoare_ir_list_ir_pre :
  forall n Q ops,
    Forall
      (fun op =>
         match op with
         | IRSumAmplitudes _ _ result => scalar_var result
         | _ => True
         end)
      ops ->
    hoare_ir_list n (ir_pre n Q ops) ops Q.
Proof.
  intros n Q ops Hscalar.
  induction ops as [|op ops IH]; simpl in *.
  - constructor.

  - inversion Hscalar; subst.
    destruct op; simpl.
    + econstructor; [apply hoare_ir_cast | apply IH; exact H2].
    + econstructor; [apply hoare_ir_locate | apply IH; exact H2].
    + econstructor; [apply hoare_ir_map | apply IH; exact H2].
    + econstructor; [apply hoare_ir_typeupdate | apply IH; exact H2].
    + econstructor; [apply hoare_ir_ampmodify | apply IH; exact H2].
    + econstructor; [apply hoare_ir_partialmap | apply IH; exact H2].
    + econstructor; [apply hoare_ir_join | apply IH; exact H2].
    + econstructor; [apply hoare_ir_delete | apply IH; exact H2].
    + econstructor.
      * apply hoare_ir_sum.
        exact H1.
      * apply IH.
        exact H2.
    + econstructor; [apply hoare_ir_copy | apply IH; exact H2].
    + econstructor; [apply hoare_ir_merge | apply IH; exact H2].
Qed.

Lemma hoare_ir_list_map_for_ir :
  forall n Q cond ops,
    Forall
      (fun op =>
         match map_for_ir cond op with
         | IRSumAmplitudes _ _ result => scalar_var result
         | _ => True
         end)
      ops ->
    hoare_ir_list n
      (ir_pre n Q (map (map_for_ir cond) ops))
      (map (map_for_ir cond) ops)
      Q.
Proof.
  intros n Q cond ops Hscalar.
  apply hoare_ir_list_ir_pre.
  rewrite Forall_map.
  exact Hscalar.
Qed.




Lemma ir_pre_flat_map_preserve :
  forall n (Q : cpredr) (xs : list nat) (F : nat -> list ir_op),
    (forall i, ir_pre n Q (F i) = Q) ->
    ir_pre n Q (flat_map F xs) = Q.
Proof.
  intros n Q xs F HF.
  induction xs as [|i xs IH]; simpl.
  - reflexivity.
  - rewrite ir_pre_app.
    rewrite IH.
    apply HF.
Qed.

Lemma hoare_ir_list_flat_map_preserve :
  forall n (Q : cpredr) (xs : list nat) (F : nat -> list ir_op),
    (forall i, hoare_ir_list n Q (F i) Q) ->
    hoare_ir_list n Q (flat_map F xs) Q.
Proof.
  intros n Q xs F HF.
  induction xs as [|i xs IH]; simpl.
  - constructor.
  - eapply hoare_ir_list_app.
    + apply HF.
    + exact IH.
Qed.

Definition ir_op_scalar_safe (op : ir_op) : Prop :=
  match op with
  | IRSumAmplitudes _ _ result => scalar_var result
  | _ => True
  end.

Lemma map_if_ir_scalar_safe :
  forall cond op,
    ir_op_scalar_safe op ->
    ir_op_scalar_safe (map_if_ir cond op).
Proof.
  intros cond op H.
  destruct op; simpl in *; auto.
Qed.

Lemma map_for_ir_scalar_safe :
  forall cond op,
    ir_op_scalar_safe (map_for_ir cond op).
Proof.
  intros cond op.
  destruct op; simpl; auto.
Qed.

Lemma compile_pexp_to_ir_scalar_safe :
  forall e,
    Forall ir_op_scalar_safe (compile_pexp_to_ir e).
Proof.
  induction e; simpl.

  - constructor.

  - destruct n; simpl.
    + constructor.
      * constructor.
      * exact IHe.
    + constructor.
      * constructor.
      * constructor.
        -- constructor.
        -- constructor.
           ++ unfold ir_op_scalar_safe. simpl.
              unfold scalar_var. simpl. reflexivity.
           ++ exact IHe.

  - destruct e; simpl;
      repeat constructor.

  - destruct (locus_to_indices_expr l) as [|e0 l0]; simpl.
    + constructor.
    + destruct (String.eqb "e" "CNOT"); simpl;
        repeat constructor.

  - apply Forall_app.
    split.
    + exact IHe1.
    + exact IHe2.

  - apply Forall_map.
    eapply Forall_impl.
    + intros op Hop.
      apply map_if_ir_scalar_safe.
      exact Hop.
    + exact IHe.

  - (* For *)
    apply Forall_flat_map.
    apply Forall_forall.
    intros i Hi.
    destruct (safe_eval (translate_bexp b) (fun _ : var => Some (i, nil)) =? 0) eqn:Hcond.
    + constructor.
    + apply Forall_map.
      eapply Forall_impl.
      * intros op Hop.
        apply map_for_ir_scalar_safe.
      * exact IHe.
  - simpl.
    repeat constructor.
Qed.

Theorem compile_pexp_to_ir_has_hoare_skeleton :
  forall n e Q,
    hoare_ir_list n
      (ir_pre n Q (compile_pexp_to_ir e))
      (compile_pexp_to_ir e)
      Q.
Proof.
  intros n e Q.
  apply hoare_ir_list_ir_pre.
  apply compile_pexp_to_ir_scalar_safe.
Qed.

Theorem Qafny_compilation_sound_IR :
  forall rmax t env T W P e W' Q n,
    type_check_proof rmax t env T T (W, P) (W', Q) e ->
    @triple rmax t env T (W, P) e (W', Q) ->
    entails
      (trans env W P)
      (ir_pre n (trans env W' Q) (compile_pexp_to_ir e)) ->
    hoare_ir_list n
      (trans env W P)
      (compile_pexp_to_ir e)
      (trans env W' Q).
Proof.
  intros rmax t env T W P e W' Q n Htc Htr Hentail.

  eapply hoare_ir_list_consequence.
  - exact Hentail.
  - apply compile_pexp_to_ir_has_hoare_skeleton.
  - apply entails_refl.
Qed.



Fixpoint lower_map (name : string) (f : expr -> expr) (xs : list nat) : cmd :=
  match xs with
  | [] => Skip
  | i :: tl =>
      Seq (ArrayWrite name (Const i) (f (Const i)))
          (lower_map name f tl)
  end.
Fixpoint lower_map_expr (name : string) (f : expr -> expr) (xs : list expr) : cmd :=
  match xs with
  | [] => Skip
  | i :: tl =>
      Seq (ArrayWrite name i (f i))
          (lower_map_expr name f tl)
  end.


(* Soundness lemmas for the most important IR operations *)
Lemma hoare_lower_map_preserve_empty :
  forall name f xs,
    hoare_triple (nil : cpredr)
                 (lower_map name f xs)
                 (nil : cpredr).
Proof.
  intros name f xs.
  induction xs as [|i xs IH]; simpl.
  - apply skip_rule.
  - eapply seq_rule.
    + change (nil : cpredr)
        with (subst_assertion_array (nil : cpredr) name (Const i) (f (Const i))).
      apply array_write_rule.
    + exact IH.
Qed.

Lemma hoare_lower_map_preserve :
  forall P name f xs,
    (forall i, hoare_triple P
      (ArrayWrite name (Const i) (f (Const i))) P) ->
    hoare_triple P (lower_map name f xs) P.
Proof.
  intros P name f xs Hwrite.
  induction xs as [|i xs IH]; simpl.
  - apply skip_rule.
  - eapply seq_rule.
    + apply Hwrite.
    + exact IH.
Qed.


Lemma hoare_ir_partialmap_sound :
  forall P name f cond n,
    (forall i, hoare_triple P
      (ArrayWrite name (Const i) (f (Const i))) P) ->
    hoare_triple P
      (If cond (lower_map name f (seq 0 n)) Skip)
      P.
Proof.
  intros P name f cond n Hwrite.
  apply if_rule.
  - apply hoare_lower_map_preserve.
    exact Hwrite.
  - apply skip_rule.
Qed.

Lemma hoare_ir_partialmap_sound_empty :
  forall name f cond n,
    hoare_triple (nil : cpredr)
      (If cond (lower_map name f (seq 0 n)) Skip)
      (nil : cpredr).
Proof.
  intros.
  apply if_rule.
  - apply hoare_lower_map_preserve_empty.
  - apply skip_rule.
Qed.




Lemma lower_map_eq_fold_right :
  forall name f xs,
    lower_map name f xs =
    fold_right
      (fun i acc => Seq (ArrayWrite name (Const i) (f (Const i))) acc)
      Skip xs.
Proof.
  intros name f xs; induction xs as [|i tl IH]; simpl; auto.
  now rewrite IH.
Qed.

Lemma wp_array_writes_sound :
  forall xs P name f,
    hoare_triple
      (wp_array_writes P name f xs)
      (lower_map name f xs)
      P.
Proof.
  induction xs as [|i xs IH]; intros P name f; simpl.
  - apply skip_rule.
  - eapply seq_rule.
    + apply array_write_rule.
    + apply IH.
Qed.

Lemma hoare_map_from_app :
  forall P name f xs,
    hoare_triple
      (P ++ wp_array_writes P name f xs)
      (lower_map name f xs)
      P.
Proof.
  intros P name f xs.
  eapply consequence_rule.
  - apply entails_app_right.
  - apply wp_array_writes_sound.
  - apply entails_refl.
Qed.

Lemma hoare_partial_map_wp_sound :
  forall P name f cond n,
    hoare_triple
      (wp_partial_map P name f cond n)
      (If cond (lower_map name f (seq 0 n)) Skip)
      P.
Proof.
  intros P name f cond n.
  unfold wp_partial_map.
  apply if_rule.
  - apply hoare_map_from_app.
  - apply hoare_skip_from_app.
Qed.


Lemma lower_one_ir_to_cmd_sound :
  forall n P Q op,
    hoare_ir n P op Q ->
    hoare_triple P (lower_one_ir_to_cmd n op) Q.
Proof.
  intros n P Q op Hir.
  inversion Hir; subst; simpl.
  - apply array_write_rule.
  - apply skip_rule.
  - apply array_write_rule.
  - apply array_write_rule.

  - (* IRMap *)
    rewrite <- lower_map_eq_fold_right.
    apply wp_array_writes_sound.

  - (* IRPartialMap *)
    rewrite <- lower_map_eq_fold_right.
    apply hoare_partial_map_wp_sound.

  - apply array_write_rule.
  - apply skip_rule.
  - apply assign_rule.
assumption.
  - (* IRCopy *)
    apply array_write_rule.

  - (* IRMerge *)
    apply array_write_rule.
Qed.

Lemma hoare_map_from_partial_wp :
  forall Q name f cond n,
    hoare_triple
      (wp_partial_map Q name f cond n)
      (lower_map name f (seq 0 n))
      Q.
Proof.
  intros Q name f cond n.
  unfold wp_partial_map.
  eapply consequence_rule.
  - apply entails_app_right.
  - apply wp_array_writes_sound.
  - apply entails_refl.
Qed.


Definition write_block (n : nat) (f : aexp -> aexp) : cmd :=
  fold_right
    (fun (i : nat) (acc : cmd) =>
       Seq (ArrayWrite "q" (Const i)
              (translate_aexp (f (expr_to_aexp (Const i)))))
           acc)
    Skip
    (seq 0 n).

Definition upd_cmd (name : string) (cond : bexp) (n : nat) (f : aexp -> aexp) : cmd :=
  match name with
  | "q"%string =>
      If (translate_bexp cond)
         (write_block n f)   (* Seq ... Skip is redundant *)
         Skip
  | _ => Skip
  end.
Lemma upd_cmd_correct :
  forall P Q name cond n f,
    hoare_triple P (upd_cmd name cond n f) Q ->
    hoare_triple P (upd_cmd name cond n f) Q.
Proof.
  intros. exact H.
Qed.

Lemma hoare_empty_skip :
  hoare_triple (nil : cpredr) Skip (nil : cpredr).
Proof.
  apply skip_rule.
Qed.

Lemma hoare_empty_seq :
  forall c1 c2,
    hoare_triple (nil : cpredr) c1 (nil : cpredr) ->
    hoare_triple (nil : cpredr) c2 (nil : cpredr) ->
    hoare_triple (nil : cpredr) (Seq c1 c2) (nil : cpredr).
Proof.
  intros c1 c2 H1 H2.
  eapply seq_rule.
  - exact H1.
  - exact H2.
Qed.

Lemma hoare_empty_array_write :
  forall name idx val,
    hoare_triple (nil : cpredr)
                 (ArrayWrite name idx val)
                 (nil : cpredr).
Proof.
  intros.
  change (nil : cpredr)
    with (subst_assertion_array (nil : cpredr) name idx val).
  apply array_write_rule.
Qed.

Lemma hoare_ir_partialmap_sound_11:
  forall P f cond n,
    (forall i,
      hoare_triple P
        (ArrayWrite "q" (Const i) (f (Const i)))
        P) ->
    hoare_triple P
      (lower_ir_to_cmd n (IRPartialMap "q" f cond :: nil))
      P.
Proof.
  intros P f cond n Hwrite.
  simpl.
eapply seq_rule.
- (* If cond body Skip *)
  apply if_rule.
  + (* then branch: body preserves P *)
    induction (seq 0 n) as [|i xs IH]; simpl.
    * apply skip_rule.
    * eapply seq_rule.
      -- apply Hwrite.
      -- exact IH.
  + (* else branch: Skip preserves P *)
    apply skip_rule.
- (* final Skip *)
  apply skip_rule.
Qed.


Lemma hoare_ir_locate_sound_1 :
  forall n P name indices,
    hoare_ir n P (IRLocate name indices) P ->
    hoare_triple P Skip P.
Proof.
  intros.
  apply skip_rule.
Qed.


Lemma entails_arrayeq_subst_self_const :
  forall name i v,
    entails
      (CBArrayEq name (Const i) (Const v) :: nil)
      (subst_assertion_array
        (CBArrayEq name (Const i) (Const v) :: nil)
        name (Const i) (Const v)).
Proof.
  unfold entails.
  intros name i v s Hsat b Hb.
  simpl in Hb.
  destruct Hb as [Hb | []].
  subst b.
  simpl.
  rewrite String.eqb_refl.
  simpl.
  destruct (i =? i).
  - apply Hsat. left. reflexivity.
  - apply Hsat. left. reflexivity.
Qed.


Lemma entails_arrayeq_subst_self :
  forall (P : cpredr) (name : string) (idx val : expr),
    subst idx (Scalar name) idx = idx ->
    subst val (Scalar name) val = val ->
    (forall b, In b P <-> In b (subst_assertion_array P name idx val)) ->
    entails
      (CBArrayEq name idx val :: P)
      (subst_assertion_array (CBArrayEq name idx val :: P) name idx val).
Proof.
  unfold entails.
  intros P name idx val Hidx Hval Heq s Hsat b Hb.
  simpl in Hb.
  destruct Hb as [Hb | Hb].
  - subst b.
    simpl.
    destruct (String.eqb name name && expr_eqb idx idx).
    + apply Hsat. left. reflexivity.

+ apply Hsat.
left.
reflexivity.

- apply Hsat.
right.
apply (proj2 (Heq b)).
exact Hb.
Qed.


Lemma hoare_ir_cast_sound_1 :
  forall P idx tgt_mode n,
    subst idx (Scalar "q") idx = idx ->
    subst (Const (mode_to_nat tgt_mode)) (Scalar "q") (Const (mode_to_nat tgt_mode))
      = Const (mode_to_nat tgt_mode) ->
    (forall b,
      In b P <->
      In b (subst_assertion_array P "q" idx (Const (mode_to_nat tgt_mode)))) ->
    hoare_triple
      (CBArrayEq "q" idx (Const (mode_to_nat tgt_mode)) :: P)
      (lower_ir_to_cmd n (IRCast "q" idx tgt_mode :: nil))
      (CBArrayEq "q" idx (Const (mode_to_nat tgt_mode)) :: P).
Proof.
  intros P idx tgt_mode n Hidx Hval HP.
  simpl.
  eapply consequence_rule.
  - apply entails_arrayeq_subst_self.
    + exact Hidx.
    + exact Hval.
    + exact HP.
  - eapply seq_rule.
    + apply array_write_rule.
    + apply skip_rule.
  - apply entails_refl.
Qed.

Lemma hoare_ir_typeupdate_sound_1 :
  forall n P name idx m,
    hoare_ir n
      (subst_assertion_array P name idx (Const m))
      (IRTypeUpdate name idx m)
      P ->
    hoare_triple
      (subst_assertion_array P name idx (Const m))
      (ArrayWrite name idx (Const m))
      P.
Proof.
  intros.
  apply array_write_rule.
Qed.


Lemma entails_ampmodify_bridge :
  forall P name idx amp amps_new amps_scaled encoded,
    subst idx (Scalar name) idx = idx ->
    amps_scaled =
      map (fun p => let '(c,n) := p in (complex_mult amp c, n)) amps_new ->
    encoded = encode_amp_list amps_scaled ->
    (forall b,
      In b (subst_assertion_array P name idx (Const encoded)) ->
      In b P) ->
    entails
      (CBAmpsEq name idx amps_scaled :: P)
      (subst_assertion_array
        (CBAmpsEq name idx amps_scaled :: P)
        name idx (Const encoded)).
Proof.
  unfold entails.
  intros P name idx amp amps_new amps_scaled encoded
         Hidx Hscaled Hencoded Hstable s Hsat b Hb.
  simpl in Hb.
  destruct Hb as [Hb | Hb].
  - subst b.
    simpl.
    destruct (String.eqb name name && expr_eqb idx idx).
    + apply Hsat. left. reflexivity.
    + apply Hsat.
left.
reflexivity.
  - apply Hsat.
    right.
    apply Hstable.
    exact Hb.
Qed.

Lemma hoare_ir_ampmodify_sound_1 :
  forall P name idx amp amps_new,
    subst idx (Scalar name) idx = idx ->
    (forall b,
      In b
        (subst_assertion_array P name idx
          (Const
            (encode_amp_list
              (map (fun p => let '(c,n) := p in
                 (complex_mult amp c, n)) amps_new)))) ->
      In b P) ->
    hoare_triple
      (CBAmpsEq name idx
         (map (fun p => let '(c,n) := p in
            (complex_mult amp c, n)) amps_new) :: P)
      (ArrayWrite name idx
         (Const
           (encode_amp_list
             (map (fun p => let '(c,n) := p in
                (complex_mult amp c, n)) amps_new))))
      (CBAmpsEq name idx
         (map (fun p => let '(c,n) := p in
            (complex_mult amp c, n)) amps_new) :: P).
Proof.
  intros P name idx amp amps_new Hidx HP.
  eapply consequence_rule.
  - eapply entails_ampmodify_bridge.
    + exact Hidx.
    + reflexivity.
    + reflexivity.
    + exact HP.
  - apply array_write_rule.
  - apply entails_refl.
Qed.




(* Weakest precondition as an assertion (requires expressiveness of cbexpr/cpredr) *)

Fixpoint wp_syntax (c : cmd) (Q : cpredr) : cpredr :=
  match c with
  | Skip => Q

  | Assign v e =>
      subst_assertion Q v e

  | ArrayWrite name idx val =>
      subst_assertion_array Q name idx val

  | Seq c1 c2 =>
      wp_syntax c1 (wp_syntax c2 Q)

  | If b c1 c2 =>
      wp_syntax c1 Q ++ wp_syntax c2 Q

  | While _ _ =>
      Q
  end.


Lemma wp_syntax_sound_skip :
  forall Q,
    hoare_triple (wp_syntax Skip Q) Skip Q.
Proof.
  intros Q. simpl. apply skip_rule.
Qed.

Lemma wp_syntax_sound_arraywrite :
  forall Q name idx val,
    hoare_triple
      (wp_syntax (ArrayWrite name idx val) Q)
      (ArrayWrite name idx val)
      Q.
Proof.
  intros. simpl. apply array_write_rule.
Qed.

Lemma wp_syntax_sound_assign :
  forall Q v e,
    scalar_var v ->
    hoare_triple
      (wp_syntax (Assign v e) Q)
      (Assign v e)
      Q.
Proof.
  intros Q v e Hv.
  simpl.
  apply assign_rule.
  exact Hv.
Qed.


Lemma hoare_triple_sound_assumed_wp :
  forall P c Q,
    hoare_triple (wp_syntax c Q) c Q ->
    entails P (wp_syntax c Q) ->
    hoare_triple P c Q.
Proof.
  intros P c Q Hwp Hent.
  eapply consequence_rule.
  - exact Hent.
  - exact Hwp.
  - apply entails_refl.
Qed.

Lemma complete_for_arraywrite :
  forall P Q name idx val,
    entails P (subst_assertion_array Q name idx val) ->
    hoare_triple P (ArrayWrite name idx val) Q.
Proof.
  intros P Q name idx val Hent.
  eapply consequence_rule.
  - exact Hent.
  - apply array_write_rule.
  - apply entails_refl.
Qed.

Lemma complete_for_skip :
  forall P Q,
    entails P Q ->
    hoare_triple P Skip Q.
Proof.
  intros P Q Hent.
  eapply consequence_rule.
  - apply entails_refl.
  - apply skip_rule.
  - exact Hent.
Qed.

Lemma complete_for_assign :
  forall P Q v e,
    scalar_var v ->
    entails P (subst_assertion Q v e) ->
    hoare_triple P (Assign v e) Q.
Proof.
  intros P Q v e Hv Hent.
  eapply consequence_rule.
  - exact Hent.
  - apply assign_rule.
    exact Hv.
  - unfold entails.
    intros s HQ.
    exact HQ.
Qed.

Lemma expr_eqb_refl :
  forall e, expr_eqb e e = true.
Proof.
  induction e; simpl; try rewrite IHe1; try rewrite IHe2; try reflexivity.
  - (* VarExpr *)
    destruct v as [s | s n]; simpl.
    + rewrite String.eqb_refl. reflexivity.
    + rewrite String.eqb_refl, Nat.eqb_refl. reflexivity.
- apply Nat.eqb_refl.
Qed.
Lemma entails_cast_head :
  forall (P0 : list cbexpr) (name : string) (idx v : expr),
    entails
      (CBArrayEq name idx v :: P0)
      [CBArrayEq name idx v].
Proof.
  unfold entails.
  intros P0 name idx v s HP b Hb.
  simpl in Hb.
  destruct Hb as [Hb | []].
  subst.
  apply HP.
  simpl; auto.
Qed.



Definition lower_ir_op_to_cmd_cont (n : nat) (op : ir_op) (tail : cmd) : cmd :=
  match op with
  | IRCast "q"%string idx mode =>
      Seq (ArrayWrite "q" idx (Const (mode_to_nat mode))) tail

  | IRAmpModify "amps"%string idx new_amp =>
      let base_amps : list (complex_approx * nat) :=
        (new_amp, 0) :: ((0%Z, 0%Z), 1) :: nil in
      let encoded := encode_amp_list base_amps in
      Seq (ArrayWrite "amps" idx (Const encoded)) tail

  | IRJoin "q"%string _ locus =>
      let ent_expr := Const 5 in
      let mark_ent :=
        fold_right
          (fun i acc => Seq (ArrayWrite "q" i ent_expr) acc)
          Skip
          locus in
      Seq mark_ent tail

  | IRSumAmplitudes "q"%string indices result_var =>
      Seq (Assign result_var (Const (length indices))) tail

  | IRMap "q"%string f =>
      let body :=
        fold_right
          (fun i acc => Seq (ArrayWrite "q" (Const i) (f (Const i))) acc)
          Skip
          (seq 0 n) in
      Seq body tail

  | IRPartialMap "q"%string f cond =>
      let body :=
        fold_right
          (fun i acc => Seq (ArrayWrite "q" (Const i) (f (Const i))) acc)
          Skip
          (seq 0 n) in
      If cond (Seq body tail) tail

  | _ => tail
  end.

Lemma hoare_ir_ampmodify_sound_seq :
  forall P name idx amp amps_new,
    let amps_scaled :=
      map (fun p => let '(c,n) := p in (complex_mult amp c, n)) amps_new in
    let encoded := encode_amp_list amps_scaled in
    subst idx (Scalar name) idx = idx ->
    (forall b,
      In b (subst_assertion_array P name idx (Const encoded)) ->
      In b P) ->
    hoare_triple
      (CBAmpsEq name idx amps_scaled :: P)
      (Seq
         (ArrayWrite name idx (Const encoded))
         Skip)
      (CBAmpsEq name idx amps_scaled :: P).
Proof.
  intros P name idx amp amps_new amps_scaled encoded Hidx HP.
  eapply seq_rule.
  - eapply consequence_rule.
    + eapply entails_ampmodify_bridge.
      * exact Hidx.
      * reflexivity.
      * reflexivity.
      * exact HP.
    + apply array_write_rule.
    + apply entails_refl.
  - apply skip_rule.
Qed.

Theorem hoare_ir_to_triple_cast_q_const :
  forall P i tgt_mode n,
    (forall b,
      In b P <->
      In b (subst_assertion_array P "q" (Const i)
              (Const (mode_to_nat tgt_mode)))) ->
    hoare_triple
      (CBArrayEq "q" (Const i) (Const (mode_to_nat tgt_mode)) :: P)
      (lower_ir_to_cmd n (IRCast "q" (Const i) tgt_mode :: nil))
      (CBArrayEq "q" (Const i) (Const (mode_to_nat tgt_mode)) :: P).
Proof.
  intros P i tgt_mode n HP.
  apply hoare_ir_cast_sound_1.
  - reflexivity.
  - reflexivity.
  - exact HP.
Qed.

Theorem hoare_ir_to_triple_cast_q :
  forall P idx tgt_mode n,
    subst idx (Scalar "q") idx = idx ->
    (forall b,
      In b P <->
      In b (subst_assertion_array P "q" idx
              (Const (mode_to_nat tgt_mode)))) ->
    hoare_triple
      (CBArrayEq "q" idx (Const (mode_to_nat tgt_mode)) :: P)
      (lower_ir_to_cmd n (IRCast "q" idx tgt_mode :: nil))
      (CBArrayEq "q" idx (Const (mode_to_nat tgt_mode)) :: P).
Proof.
  intros P idx tgt_mode n Hidx HP.
  apply hoare_ir_cast_sound_1.
  - exact Hidx.
  - reflexivity.
  - exact HP.
Qed.

Theorem hoare_ir_to_triple_locate :
  forall P name idxs n,
    hoare_triple P
      (lower_ir_to_cmd n (IRLocate name idxs :: nil))
      P.
Proof.
  intros P name idxs n.
  simpl.
  eapply seq_rule.
  - apply skip_rule.
  - apply skip_rule.
Qed.


Fixpoint lower_map_expr_const (name : string) (xs : list expr) (v : expr) : cmd :=
  match xs with
  | nil => Skip
  | i :: tl =>
      Seq (ArrayWrite name i v)
          (lower_map_expr_const name tl v)
  end.

Lemma lower_map_expr_const_preserve :
  forall P name xs v,
    (forall i, In i xs -> hoare_triple P (ArrayWrite name i v) P) ->
    hoare_triple P (lower_map_expr_const name xs v) P.
Proof.
  intros P name xs v Hwrite.
  induction xs as [|i xs IH]; simpl.
  - apply skip_rule.
  - eapply seq_rule.
    + apply Hwrite. left. reflexivity.
    + apply IH. intros j Hj. apply Hwrite. right. exact Hj.
Qed.

Lemma lower_map_expr_const_eq_fold_right :
  forall name xs v,
    lower_map_expr_const name xs v =
    fold_right
      (fun i acc => Seq (ArrayWrite name i v) acc)
      Skip xs.
Proof.
  intros name xs v.
  induction xs as [|i xs IH]; simpl.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

Theorem hoare_ir_to_triple_join :
  forall P loc n,
    hoare_triple P (ArrayWrite "q" (Const 0) (Const 5)) P ->
    (forall i, In i loc ->
      hoare_triple P (ArrayWrite "q" i (Const 5)) P) ->
    hoare_triple P
      (lower_ir_to_cmd n (IRJoin "q" (Const 0) loc :: nil))
      P.
Proof.
  intros P loc n Hidx Hwrite.
  simpl.
  eapply seq_rule.
  - exact Hidx.
  - apply skip_rule.
Qed.
Theorem hoare_ir_to_tripl2e_join :
  forall P loc n,
    In (Const 0) loc ->
    (forall i, In i loc ->
      hoare_triple P (ArrayWrite "q" i (Const 5)) P) ->
    hoare_triple P
      (lower_ir_to_cmd n (IRJoin "q" (Const 0) loc :: nil))
      P.
Proof.
  intros P loc n HzeroIn Hwrite.
  simpl.
  eapply seq_rule.
  - apply Hwrite.
    exact HzeroIn.
  - apply skip_rule.
Qed.





Lemma eqb_var_refl :
  forall x, eqb_var x x = true.
Proof.
  intros x.
  destruct x as [name | name idx]; simpl.
  - apply String.eqb_refl.
  - rewrite String.eqb_refl, Nat.eqb_refl.
    reflexivity.
Qed.


Lemma subst_assertion_array_keeps_eq_head :
  forall (P0 : list cbexpr) (idx : expr) (v : expr),
    subst_assertion_array
      (CBArrayEq "q"%string idx v :: P0)
      "q"%string idx v
    =
    CBArrayEq "q"%string idx v
      :: map (fun b => subst_array b "q"%string idx v) P0.
Proof.
  intros P0 idx v.
  unfold subst_assertion_array.
  simpl.
  unfold subst_array.

  rewrite expr_eqb_refl.
  reflexivity.
Qed.

Lemma entails_cast_write_pre_head :
  forall (P0 : list cbexpr) (idx : expr) (tgt_mode : mode),
    entails
      (CBArrayEq "q"%string idx (Const (mode_to_nat tgt_mode)) :: P0)
      [CBArrayEq "q"%string idx (Const (mode_to_nat tgt_mode))].
Proof.
  unfold entails.
  intros P0 idx tgt_mode s HP b Hb.
  simpl in Hb.
  destruct Hb as [Hb | []].
  subst b.
  apply HP.
  simpl; auto.
Qed.

Lemma entails_subst_assertion_array :
  forall (P0 : list cbexpr) (name : string) (idx v : expr),
    entails
      (CBArrayEq name idx v :: P0)
      [CBArrayEq name idx v].
Proof.
  unfold entails.
  intros P0 name idx v s HP b Hb.
  simpl in Hb.
  destruct Hb as [Hb | []].
  subst b.
  apply HP.
  simpl; auto.
Qed.

Lemma lower_ir_op_to_cmd_cont_sound :
  forall n P Q R op tail,
    hoare_ir n P op Q ->
    hoare_triple P (lower_ir_op_to_cmd_cont n op Skip) Q ->
    hoare_triple Q tail R ->
    hoare_triple P (Seq (lower_ir_op_to_cmd_cont n op Skip) tail) R.
Proof.
  intros n P Q R op tail Hir Hop Htail.
  eapply seq_rule.
  - exact Hop.
  - exact Htail.
Qed.




(*  General translation for lists of IR operations  *)

Lemma array_write_preserves_arrayeq :
  forall P name idx val,
    (forall b,
        In b (subst_assertion_array P name idx val) ->
        In b P) ->
    entails
      (CBArrayEq name idx val :: P)
      (subst_assertion_array (CBArrayEq name idx val :: P) name idx val).
Proof.
  unfold entails, subst_assertion_array.
  intros P name idx val Hstable s Hsat b Hb.
  simpl in Hb.
  destruct Hb as [Hb | Hb].
  - subst b.
    assert (Hin : In (CBArrayEq name idx val)
                     (CBArrayEq name idx val :: P)).
    { left. reflexivity. }

    simpl.
    destruct ((name =? name)%string && expr_eqb idx idx) eqn:Hcond.
    + exact (Hsat (CBArrayEq name idx val) Hin).
    + exact (Hsat (CBArrayEq name idx val) Hin).

  - apply Hsat.
    right.
    apply Hstable.
    unfold subst_assertion_array.
    exact Hb.
Qed.



Lemma eqb_var_eq :
  forall x y,
    eqb_var x y = true -> x = y.
Proof.
  intros x y H.
  destruct x as [xn | xn xi];
  destruct y as [yn | yn yi];
  simpl in H; try discriminate.
  - apply String.eqb_eq in H.
    subst. reflexivity.
  - apply andb_true_iff in H as [Hn Hi].
    apply String.eqb_eq in Hn.
    apply Nat.eqb_eq in Hi.
    subst. reflexivity.
Qed.

Lemma eqb_var_neq :
  forall x y,
    eqb_var x y = false -> x <> y.
Proof.
  intros x y Hneq Heq.
  subst.
  rewrite eqb_var_refl in Hneq.
  discriminate.
Qed.

Lemma assign_update_state_eq :
  forall s v val,
    (fun x : var => if eqb_var x v then Some (val, []) else s x)
    =
    update_state s v (val, []).
Proof.
  intros s v val.
  unfold update_state.
  apply functional_extensionality.
  intro x.
  reflexivity.
Qed.

Lemma subst_eval_sound :
  forall e v e_subst s val,
    eval e_subst s = Some val ->
    eval e (update_state s v (val, [])) =
    eval (subst e v e_subst) s.
Proof.
  induction e; intros v0 e_subst s val Hval; simpl.

  - (* VarExpr *)
    destruct (eqb_var v v0) eqn:Heq.
+ apply eqb_var_eq in Heq.
  subst v.
  unfold update_state.
  rewrite eqb_var_refl.
  symmetry.
  exact Hval.
+
unfold update_state.
rewrite Heq.
reflexivity.
  - (* Const *)
    reflexivity.

  - (* Plus *)
rewrite (IHe1 v0 e_subst s val Hval).
rewrite (IHe2 v0 e_subst s val Hval).
reflexivity.

  - (* Minus *)
    rewrite (IHe1 v0 e_subst s val Hval).
    rewrite (IHe2 v0 e_subst s val Hval).
    reflexivity.

  - (* Mult *)
    rewrite (IHe1 v0 e_subst s val Hval).
    rewrite (IHe2 v0 e_subst s val Hval).
    reflexivity.
Qed.



Lemma array_write_preserves_array_eq_self :
  forall P name idx val,
    entails
      (CBArrayEq name idx val :: P)
      (subst_assertion_array (CBArrayEq name idx val :: P) name idx val) ->
    hoare_triple
      (CBArrayEq name idx val :: P)
      (ArrayWrite name idx val)
      (CBArrayEq name idx val :: P).
Proof.
  intros P name idx val Hpre.
  eapply consequence_rule.
  - exact Hpre.
  - apply array_write_rule.
  - apply entails_refl.
Qed.

Lemma lower_ir_to_cmd_cons_sound :
  forall n P Q R op ops,
    hoare_ir n P op Q ->
    entails P Q ->
    hoare_triple Q (lower_ir_to_cmd n ops) R ->
    hoare_triple P (lower_ir_to_cmd n ops) R.
Proof.
  intros n P Q R op ops Hir Hent Htr.
  eapply consequence_rule.
  - exact Hent.
  - exact Htr.
  - apply entails_refl.
Qed.

Theorem hoare_ir_list_to_triple :
  forall n P ops Q,
    hoare_ir_list n P ops Q ->
    hoare_triple P (lower_ir_to_cmd n ops) Q.
Proof.
  intros n P ops Q Hlist.
  induction Hlist; simpl.
  - apply skip_rule.

  - eapply seq_rule.
    + apply lower_one_ir_to_cmd_sound.
      exact H.
    + exact IHHlist.

  - eapply consequence_rule.
    + exact H.
    + exact IHHlist.
    + exact H0.
Qed.



(*  Full Translation  *)

Theorem Qafny_compilation_sound_IR_to_cmd :
  forall rmax t env T W P e W' Q n,
    type_check_proof rmax t env T T (W, P) (W', Q) e ->
    @triple rmax t env T (W, P) e (W', Q) ->
    entails
      (trans env W P)
      (ir_pre n (trans env W' Q) (compile_pexp_to_ir e)) ->
    hoare_triple
      (trans env W P)
      (lower_ir_to_cmd n (compile_pexp_to_ir e))
      (trans env W' Q).
Proof.
  intros rmax t env T W P e W' Q n Htc Htr Hbridge.

  apply hoare_ir_list_to_triple.

  eapply Qafny_compilation_sound_IR.
  - exact Htc.
  - exact Htr.
  - exact Hbridge.
Qed.


Definition bridge_condition
  (n : nat)
  (env : aenv)
  (W : cpred)
  (P : qpred)
  (W' : cpred)
  (Q : qpred)
  (e : pexp)
  : Prop :=
  entails
    (trans env W P)
    (ir_pre n (trans env W' Q) (compile_pexp_to_ir e)).

Lemma bridge_automatic :
  forall rmax t env T W P e W' Q n,
    type_check_proof rmax t env T T (W, P) (W', Q) e ->
    @triple rmax t env T (W, P) e (W', Q) ->
    bridge_condition n env W P W' Q e ->
    entails
      (trans env W P)
      (ir_pre n (trans env W' Q) (compile_pexp_to_ir e)).
Proof.
  intros rmax t env T W P e W' Q n Htc Htr Hbridge.
  exact Hbridge.
Qed.


Lemma bridge_by_subset :
  forall n env W P W' Q e,
    (forall b,
        In b (ir_pre n (trans env W' Q) (compile_pexp_to_ir e)) ->
        In b (trans env W P)) ->
    entails
      (trans env W P)
      (ir_pre n (trans env W' Q) (compile_pexp_to_ir e)).
Proof.
  intros n env W P W' Q e Hsubset.
  apply entails_by_subset.
  exact Hsubset.
Qed.



Lemma eval_subst_assign :
  forall e0 v e s val,
    eval e s = Some val ->
    eval e0 (fun x : var =>
      if eqb_var x v then Some (val, []) else s x)
    =
    eval (subst e0 v e) s.
Proof.
  induction e0; intros v0 e s val Heval; simpl.
  - destruct (eqb_var v v0) eqn:Hv.
    + symmetry.
exact Heval.
    + reflexivity.
  - reflexivity. 
- (* EPlus *)
  rewrite (IHe0_1 v0 e s val Heval).
  rewrite (IHe0_2 v0 e s val Heval).
  reflexivity.   
- (* ESub *)
  rewrite (IHe0_1 v0 e s val Heval).
  rewrite (IHe0_2 v0 e s val Heval).
  reflexivity.
- (* EMul *)
  rewrite (IHe0_1 v0 e s val Heval).
  rewrite (IHe0_2 v0 e s val Heval).
  reflexivity.
Qed.

Lemma subst_cbexp_sound_scalar :
  forall b x e_subst st val,
    eval e_subst st = Some val ->
    eval_cbexp st (subst_cbexp b (Scalar x) e_subst) =
    eval_cbexp (update_state st (Scalar x) (val, [])) b.
Proof.
  induction b; intros x e_subst st val Hval; simpl.

  - (* CBTrue *)
    reflexivity.

  - (* CBVar *)
    destruct v as [name | name i]; simpl.
    + destruct (String.eqb name x) eqn:Heq.
      * apply String.eqb_eq in Heq.
        subst name.
        unfold update_state.
        simpl.
        rewrite String.eqb_refl.
        rewrite Hval.
        reflexivity.
      * unfold update_state.
        simpl.
        rewrite Heq.
        destruct (st (Scalar name)) as [[n amps] |] eqn:Hst;
          reflexivity.
    + unfold update_state.
      simpl.
      destruct (st (Array name i)) as [[n amps] |] eqn:Hst;
        reflexivity.

  - (* CBEq *)
    rewrite (subst_eval_sound e (Scalar x) e_subst st val Hval).
    rewrite (subst_eval_sound e0 (Scalar x) e_subst st val Hval).
    reflexivity.

  - (* CBArrayWrite *)
    reflexivity.

  - (* CBAnd *)
    rewrite IHb1 with (val := val); auto.
    rewrite IHb2 with (val := val); auto.
 

  - (* CBArrayEq *)
    rewrite (subst_eval_sound e (Scalar x) e_subst st val Hval).
    rewrite (subst_eval_sound e0 (Scalar x) e_subst st val Hval).
    destruct (eval e (update_state st (Scalar x) (val, []))) as [i |];
      simpl; try reflexivity.
 

  - (* CBAmpsEq *)
    rewrite (subst_eval_sound e (Scalar x) e_subst st val Hval).
    destruct (eval e (update_state st (Scalar x) (val, []))) as [i |];
      simpl; try reflexivity.
Qed.

Lemma subst_assertion_sound_scalar :
  forall P x e_subst st val,
    eval e_subst st = Some val ->
    model (subst_assertion P (Scalar x) e_subst) st ->
    model P (update_state st (Scalar x) (val, [])).
Proof.
  unfold model, subst_assertion.
  intros P x e_subst st val Hval HP b Hb.
  specialize (HP (subst_cbexp b (Scalar x) e_subst)).
   assert (Hin :
    In (subst_cbexp b (Scalar x) e_subst)
       (map (fun b0 : cbexpr => subst_cbexp b0 (Scalar x) e_subst) P)).
  {
    change (In ((fun b0 : cbexpr =>
      subst_cbexp b0 (Scalar x) e_subst) b)
      (map (fun b0 : cbexpr =>
        subst_cbexp b0 (Scalar x) e_subst) P)).
    apply in_map.
    exact Hb.
  }
  specialize (HP Hin).
  rewrite subst_cbexp_sound_scalar with (val := val) in HP; auto.
Qed.



Lemma update_state_array_scalar :
  forall st x v name i,
    scalar_var x ->
    update_state st x v (Array name i) = st (Array name i).
Proof.
  intros st x v name i Hscalar.
  unfold update_state.
  destruct x as [xname | aname ai].
  - simpl. reflexivity.
  - contradiction.
Qed.

Lemma subst_cbexp_sound :
  forall b x sub st val,
    scalar_var x ->
    eval sub st = Some val ->
    eval_cbexp st (subst_cbexp b x sub) = true ->
    eval_cbexp (update_state st x (val, [])) b = true.
Proof.
  induction b; intros x sub st val Hscalar Hsub Hcb; simpl in *.

  - (* CBTrue *)
    reflexivity.

  - (* CBVar *)
    unfold update_state.
    destruct (eqb_var v x) eqn:Heq.
    + simpl in Hcb.
      rewrite Hsub in Hcb.
      exact Hcb.
    + simpl in Hcb.
      destruct (st v) as [p |] eqn:Hsv.
      * destruct p as [n amps].
        simpl in Hcb.
        exact Hcb.
      * simpl in Hcb.
        exact Hcb.

  - (* CBEq *)
    replace (eval e (update_state st x (val, [])))
      with (eval (subst_expr e x sub) st).
    2:{ symmetry. eapply subst_eval_sound. exact Hsub. }

    replace (eval e0 (update_state st x (val, [])))
      with (eval (subst_expr e0 x sub) st).
    2:{ symmetry. eapply subst_eval_sound. exact Hsub. }

    exact Hcb.

  - (* CBArrayWrite *)
    discriminate Hcb.

  - (* CBAnd *)
    apply andb_true_iff in Hcb.
    destruct Hcb as [H1 H2].
    apply andb_true_iff.
    split.
    + eapply IHb1; eauto.
    + eapply IHb2; eauto.

  - (* CBArrayEq *)
    replace (eval e (update_state st x (val, [])))
      with (eval (subst_expr e x sub) st).
    2:{ symmetry. eapply subst_eval_sound. exact Hsub. }

    replace (eval e0 (update_state st x (val, [])))
      with (eval (subst_expr e0 x sub) st).
    2:{ symmetry. eapply subst_eval_sound. exact Hsub. }

    destruct (eval (subst_expr e x sub) st) as [i |] eqn:Hi;
      try discriminate.
    destruct (eval (subst_expr e0 x sub) st) as [v0 |] eqn:Hv;
      try discriminate.

    rewrite update_state_array_scalar.
    + exact Hcb.
    + exact Hscalar.

  - (* CBAmpsEq *)
    replace (eval e (update_state st x (val, [])))
      with (eval (subst_expr e x sub) st).
    2:{ symmetry. eapply subst_eval_sound. exact Hsub. }

    destruct (eval (subst_expr e x sub) st) as [i |] eqn:Hi;
      try discriminate.

    rewrite update_state_array_scalar.
    + exact Hcb.
    + exact Hscalar.
Qed.

Lemma subst_assertion_sound :
  forall P v e s val,
    scalar_var v ->
    eval e s = Some val ->
    model (subst_assertion P v e) s ->
    model P (update_state s v (val, [])).
Proof.
  induction P as [|a P IH]; intros v e s val Hv Heval Hmodel.

  - unfold model.
    intros b HIn.
    inversion HIn.

  - unfold model in *.
    intros b HIn.
    simpl in HIn.
    destruct HIn as [Hb | HIn].
    + subst b.
      eapply subst_cbexp_sound.
      * exact Hv.
      * exact Heval.
      * apply Hmodel.
        simpl. left. reflexivity.
    + eapply IH.
      * exact Hv.
      * exact Heval.
      * unfold model.
        intros b' Hb'.
        apply Hmodel.
        simpl. right. exact Hb'.
      * exact HIn.
Qed.

Definition array_write_state
  (st : state) (name : string) (i : nat) (x : nat) : state :=
  update_state st (Array name i) (x, []).

Fixpoint subst_cbexp_array
  (b : cbexpr) (name : string) (idx val : expr) : cbexpr :=
  match b with
  | CBTrue => CBTrue
  | CBVar v => CBVar v
  | CBEq e1 e2 => CBEq e1 e2
  | CBArrayWrite n i v => CBArrayWrite n i v
  | CBAnd b1 b2 =>
      CBAnd
        (subst_cbexp_array b1 name idx val)
        (subst_cbexp_array b2 name idx val)
  | CBArrayEq n i v =>
      CBArrayEq n i v
  | CBAmpsEq n i amps =>
      CBAmpsEq n i amps
  end.


(* ====================================================== *)
(* Section 6.1 / 6.2 alignment layer                      *)
(* Qafny operation -> HLIR shape used in the paper         *)
(* ====================================================== *)

(* 6.1 Oracle pipeline:
   locateN ; applyN ; gAssign
*)
Definition oracle_ir
  (name : string)
  (target : expr)
  (locus : list expr)
  (f : expr -> expr)
  : list ir_op :=
  IRLocate name (target :: locus) ::
  IRMap name f ::
  IRJoin name target locus ::
  nil.

Lemma oracle_ir_scalar_safe :
  forall name target locus f,
    Forall ir_op_scalar_safe (oracle_ir name target locus f).
Proof.
  intros.
  unfold oracle_ir.
  repeat constructor.
Qed.

Lemma oracle_translation_sound_1 :
  forall n P name target locus f,
    hoare_ir_list n
      (ir_pre n P (oracle_ir name target locus f))
      (oracle_ir name target locus f)
      P.
Proof.
  intros n P name target locus f.
  apply hoare_ir_list_ir_pre.
  apply oracle_ir_scalar_safe.
Qed.


(* 6.2 Hadamard pipeline:
   locate target ; cast to Had ; update symbolic amplitudes
*)
Definition hadamard_ir (idx : expr) : list ir_op :=
  match hadamard_amps_single 1 with
  | (c, _) :: _ =>
      IRLocate "q" [idx] ::
      IRCast "q" idx Had ::
      IRAmpModify "amps" idx c ::
      nil
  | [] =>
      IRLocate "q" [idx] ::
      IRCast "q" idx Had ::
      nil
  end.

Lemma hadamard_translation_sound :
  forall n P idx,
    hoare_ir_list n
      (ir_pre n P (hadamard_ir idx))
      (hadamard_ir idx)
      P.
Proof.
  intros n P idx.
  apply hoare_ir_list_ir_pre.
  unfold hadamard_ir.
  destruct (hadamard_amps_single 1) as [|[c k] tl]; simpl;
    repeat constructor.
Qed.


Definition hoare_valid (P : cpredr) (c : cmd) (Q : cpredr) : Prop :=
  forall fuel s s',
    model P s ->
    exec fuel c s = Some s' ->
    model Q s'.

Lemma hoare_valid_skip :
  forall P, hoare_valid P Skip P.
Proof.
  unfold hoare_valid.
  intros P fuel s s' HP Hexec.
  destruct fuel; simpl in Hexec; try discriminate.
  inversion Hexec; subst.
  exact HP.
Qed.

Lemma hoare_valid_seq :
  forall P Q R c1 c2,
    hoare_valid P c1 Q ->
    hoare_valid Q c2 R ->
    hoare_valid P (Seq c1 c2) R.
Proof.
  unfold hoare_valid.
  intros P Q R c1 c2 H1 H2 fuel s s' HP Hexec.
  destruct fuel as [|fuel']; simpl in Hexec; try discriminate.
  destruct (exec fuel' c1 s) as [smid|] eqn:Hc1; try discriminate.
  eapply H2.
  - eapply H1; eauto.
  - exact Hexec.
Qed.

Lemma hoare_valid_consequence :
  forall P P' Q Q' c,
    entails P P' ->
    hoare_valid P' c Q' ->
    entails Q' Q ->
    hoare_valid P c Q.
Proof.
  unfold hoare_valid, entails.
  intros P P' Q Q' c Hpre Hc Hpost fuel s s' HP Hexec.
  unfold model.
  intros b Hb.
  eapply Hpost.
  - eapply Hc.
    + unfold model.
      intros b0 Hb0.
      eapply Hpre.
      * exact HP.
      * exact Hb0.
    + exact Hexec.
  - exact Hb.
Qed.

Definition assn := state -> Prop.

Definition valid (P : assn) (c : cmd) (Q : assn) : Prop :=
  forall fuel s s',
    P s ->
    exec fuel c s = Some s' ->
    Q s'.

Definition wp_cmd (c : cmd) (Q : assn) : assn :=
  fun s => forall fuel s', exec fuel c s = Some s' -> Q s'.

Lemma valid_wp :
  forall c Q,
    valid (wp_cmd c Q) c Q.
Proof.
  unfold valid, wp_cmd.
  intros c Q fuel s s' Hwp Hexec.
  eapply Hwp; eauto.
Qed.


Theorem quantum_to_classical_soundness_final :
  forall P Q c,
    valid P c Q ->
    forall fuel s s',
      P s ->
      exec fuel c s = Some s' ->
      Q s'.
Proof.
  intros P Q c Hvalid fuel s s' HP Hexec.
  eapply Hvalid; eauto.
Qed.



Lemma assign_subst_sound :
  forall P v e s v0,
    scalar_var v ->
    eval e s = Some v0 ->
    model (subst_assertion P v e) s ->
    model P (fun x => if eqb_var x v then Some (v0, []) else s x).
Proof.
  intros P v e s v0 Hv Heval HP.
  unfold model in *.
  intros b Hb.
  specialize (HP (subst_cbexp b v e)).
  assert (HinSub : In (subst_cbexp b v e) (subst_assertion P v e)).
  {
    unfold subst_assertion.
    change (In ((fun x => subst_cbexp x v e) b)
               (map (fun x => subst_cbexp x v e) P)).
    apply in_map.
    exact Hb.
  }
  specialize (HP HinSub).
  eapply subst_cbexp_sound.
  - exact Hv.
  - exact Heval.
  - exact HP.
Qed.



(* TIGHTNESS *)


Lemma qpred_check_shrink_l :
  forall T T' P P',
    qpred_check (T ++ T') (P ++ P') ->
    length T = length P ->
    qpred_check T P.
Proof.
  intros T T' P P' H Hlen.
  remember (T ++ T') as Tall.
  remember (P ++ P') as Pall.
  revert T T' P P' HeqTall HeqPall Hlen.
  induction H; intros T0 T'0 P0 P'0 HT HP Hlen.
  - symmetry in HT.
    apply app_eq_nil in HT as [HT HT'].
    symmetry in HP.
    apply app_eq_nil in HP as [HP HP'].
    subst. constructor.
  - destruct T0 as [| [sa0 t0] T0].
    + simpl in Hlen.
      destruct P0 as [| p0 P0]; simpl in Hlen; try discriminate.
      constructor.
    + destruct P0 as [| [s0 v0] P0]; simpl in Hlen; try discriminate.
      simpl in HT, HP.
      inversion HT; subst.
      inversion HP; subst.
      constructor; auto.
      eapply IHqpred_check.
      * reflexivity.
      * reflexivity.
      * inversion Hlen; reflexivity.
Qed.

Lemma pred_check_app_l :
  forall env T T' W P R,
    pred_check env (T ++ T') (W, P ++ R) ->
    length T = length P ->
    pred_check env T (W, P).
Proof.
  intros env T T' W P R H Hlen.
  unfold pred_check in *.
  destruct H as [Hc Hq].
  split.
  - exact Hc.
  - eapply qpred_check_shrink_l.
    + exact Hq.
    + exact Hlen.
Qed.

Lemma type_check_proof_to_locus :
  forall rmax t env T W P W' Q e,
    type_check_proof rmax t env T T (W, P) (W', Q) e ->
    @locus_system rmax t env T e T /\
    pred_check env T (W, P) /\
    pred_check env T (W', Q).
Proof.
  intros rmax t env T W P W' Q e Htc.
  inversion Htc; subst.
  destruct H0 as [Hloc Hpost].
  split.
  - exact Hloc.
  - split.
    + exact H.
    + exact Hpost.
Qed.

Lemma locus_systuem_subst_type_map_back_framed :
  forall (rmax : nat) q env T T' Tframe x v e,
    subst_type_map T x v = T ->
    @locus_system rmax q env (subst_type_map T x v) e T' ->
    @locus_system rmax q env (T ++ Tframe) e (T' ++ Tframe).
Proof.
  intros rmax q env T T' Tframe x v e Hsubst Hloc.
  rewrite <- Hsubst.
  eapply sub_ses.
  exact Hloc.
Qed.
Lemma locus_system_subst_type_map_framed :
  forall (rmax : nat) q env T T' Tframe x v e,
    @locus_system rmax q env (subst_type_map T x v) e T' ->
    @locus_system rmax q env
      (subst_type_map T x v ++ Tframe)
      e
      (T' ++ Tframe).
Proof.
  intros rmax q env T T' Tframe x v e Hloc.
  eapply sub_ses.
  exact Hloc.
Qed.


Lemma subst_type_map_app :
  forall T Tframe x v,
    subst_type_map (T ++ Tframe) x v =
    subst_type_map T x v ++ subst_type_map Tframe x v.
Proof.
  induction T as [| [l ty] T IHT]; intros Tframe x v; simpl.
  - reflexivity.
  - rewrite IHT.
    reflexivity.
Qed.
Lemma subst_type_map_app_frame :
  forall T Tframe x v,
    subst_type_map Tframe x v = Tframe ->
    subst_type_map (T ++ Tframe) x v =
    subst_type_map T x v ++ Tframe.
Proof.
  intros T Tframe x v Hframe.
  rewrite subst_type_map_app.
  rewrite Hframe.
  reflexivity.
Qed.

Lemma let_c_pf_framed :
  forall rmax q env T T' Tframe W Q x a v e,
    ~ AEnv.In (elt:=ktype) x env ->
    simp_aexp a = Some v ->
    type_check_proof rmax q env
      (T ++ Tframe)
      T'
      W Q
      (subst_pexp e x v) ->
    @triple rmax q env
      (T ++ Tframe)
      W
      (subst_pexp e x v)
      Q ->
    @triple rmax q env
      (T ++ Tframe)
      W
      (Let x a e)
      Q.
Proof.
  intros.
  eapply let_c_pf; eauto.
Qed.

Lemma maps_to_env_add_old :
  forall env x y k ky,
    ~ AEnv.In (elt:=ktype) x env ->
    AEnv.MapsTo (elt:=ktype) y ky env ->
    AEnv.MapsTo (elt:=ktype) y ky (AEnv.add x k env).
Proof.
  intros env x y k ky Hfresh Hmap.
  apply AEnv.add_2.
  - intro Heq.
    subst y.
    apply Hfresh.
    exists ky.
    exact Hmap.
  - exact Hmap.
Qed.

Lemma type_aexp_env_add :
  forall env x k a ty,
    ~ AEnv.In (elt:=ktype) x env ->
    type_aexp env a ty ->
    type_aexp (AEnv.add x k env) a ty.
Proof.
  intros env x k a ty Hfresh Hty.
  induction Hty.

  - (* ba_type *)
    eapply ba_type.
    + exact H.
    + eapply maps_to_env_add_old; eauto.

  - (* ba_type_q *)
    eapply ba_type_q.
    eapply maps_to_env_add_old; eauto.

  - (* num_type *)
    apply num_type.

  - (* num_type_q *)
    apply num_type_q.

  - (* plus_type *)
    eapply plus_type; eauto.

  - (* mult_type *)
    eapply mult_type; eauto.

  - (* mnum_type *)
    apply mnum_type.
Qed.

Lemma type_cbexp_env_add :
  forall env x k b t,
    ~ AEnv.In (elt:=ktype) x env ->
    type_cbexp env b t ->
    type_cbexp (AEnv.add x k env) b t.
Proof.
  intros env x k b t Hfresh H.
  induction H.

  - eapply ceq_type.
    + eapply type_aexp_env_add; eauto.
    + eapply type_aexp_env_add; eauto.
    + exact H1.
    + exact H2.

  - eapply clt_type.
    + eapply type_aexp_env_add; eauto.
    + eapply type_aexp_env_add; eauto.
    + exact H1.
    + exact H2.
Qed.
Lemma type_bexp_env_add :
  forall env x k b ty,
    ~ AEnv.In (elt:=ktype) x env ->
    type_bexp env b ty ->
    type_bexp (AEnv.add x k env) b ty.
Proof.
  intros env x k b ty Hfresh H.
  induction H.

  - apply cb_type.
    eapply type_cbexp_env_add; eauto.

  - eapply beq_type_1.
    + eapply maps_to_env_add_old; eauto.
    + eapply maps_to_env_add_old; eauto.
    + exact H1.

  - eapply beq_type_2.
    + eapply maps_to_env_add_old; eauto.
    + eapply maps_to_env_add_old; eauto.
    + exact H1.

  - eapply blt_type_1.
    + eapply maps_to_env_add_old; eauto.
    + eapply maps_to_env_add_old; eauto.
    + exact H1.

  - eapply blt_type_2.
    + eapply maps_to_env_add_old; eauto.
    + eapply maps_to_env_add_old; eauto.
    + exact H1.

  - eapply btest_type.
    + eapply maps_to_env_add_old; eauto.
    + exact H0.

  - (* bneg_type *)
    apply bneg_type.
    apply IHtype_bexp.
    exact Hfresh.
Qed.

Lemma in_env_add :
  forall env x k y,
    AEnv.In (elt:=ktype) y env ->
    AEnv.In (elt:=ktype) y (AEnv.add x k env).
Proof.
  intros env x k y Hin.
  destruct Hin as [ky Hmap].
  destruct (AEnv.E.eq_dec x y) as [Heq | Hneq].
  - subst.
    exists k.
    apply AEnv.add_1.
    reflexivity.
  - exists ky.
    apply AEnv.add_2.
    + intro Hxy.
      apply Hneq.
      exact Hxy.
    + exact Hmap.
Qed.

Lemma sublist_env_add :
  forall xs env x k,
    sublist xs env ->
    sublist xs (AEnv.add x k env).
Proof.
  intros xs env x k H.
  unfold sublist in *.
  induction H.
  - constructor.
  - constructor.
    + apply in_env_add. exact H.
    + exact IHForall.
Qed.

Lemma cpred_check_env_add :
  forall env x k W,
    cpred_check W env ->
    cpred_check W (AEnv.add x k env).
Proof.
  intros env x k W H.
  unfold cpred_check in *.
  induction H.
  - constructor.
  - constructor.
    + apply sublist_env_add. exact H.
    + exact IHForall.
Qed.


Lemma type_aexp_freevars_sublist :
  forall env a ty,
    type_aexp env a ty ->
    sublist (freeVarsAExp a) env.
Proof.
  intros env a ty H.
  induction H.
  - simpl.
    unfold sublist.
    simpl.
    constructor.
    + exists t. exact H0.
    + constructor.

  - simpl.
    unfold sublist.
    simpl.
    constructor.
    + exists (QT n). exact H.
    + constructor.

  - simpl. constructor.

  - simpl. constructor.

  - simpl.
    unfold sublist in *.
    rewrite Forall_app.
    split.
    + exact IHtype_aexp1.
    + exact IHtype_aexp2.

  - simpl.
    unfold sublist in *.
    rewrite Forall_app.
    split.
    + exact IHtype_aexp1.
    + exact IHtype_aexp2.

  - simpl. constructor.
Qed.

Lemma pred_check_add_ceq :
  forall env x a T W P,
    type_aexp env a (Mo QafnySyntax.MT, []) ->
    pred_check env T (W, P) ->
    pred_check (AEnv.add x (Mo QafnySyntax.MT) env) T
      (CEq x a :: W, P).
Proof.
  intros env x a T W P Ha Hpred.
  unfold pred_check in *.
  destruct Hpred as [HW HP].
  simpl in HW, HP.
  split.
  - simpl.
    constructor.
    + simpl.
      apply sublist_env_add.
      eapply type_aexp_freevars_sublist.
      exact Ha.
    + apply cpred_check_env_add.
      exact HW.
  - exact HP.
Qed.

Lemma qpred_check_prefix :
  forall T T' P R,
    qpred_check (T ++ T') (P ++ R) ->
    length T = length P ->
    qpred_check T P.
Proof.
  intros T T' P R H Hlen.
  remember (T ++ T') as Tall.
  remember (P ++ R) as Pall.
  revert T T' P R HeqTall HeqPall Hlen.
  induction H; intros T0 T'0 P0 R0 HT HP Hlen.
  - symmetry in HT.
    apply app_eq_nil in HT as [HT HT'].
    symmetry in HP.
    apply app_eq_nil in HP as [HP HR].
    subst.
    constructor.

  - destruct T0 as [| [sa0 t0] T0].
    + destruct P0 as [| [s0 v0] P0].
      * constructor.
      * simpl in Hlen. discriminate.
    + destruct P0 as [| [s0 v0] P0].
      * simpl in Hlen. discriminate.
      * simpl in HT, HP.
        inversion HT; subst.
        inversion HP; subst.
        constructor; eauto.

Qed.

Lemma pred_check_app_le :
  forall env T T' W P R,
    pred_check env (T ++ T') (W, P ++ R) ->
    length T = length P ->
    pred_check env T (W, P).
Proof.
  intros env T T' W P R H Hlen.
  unfold pred_check in *.
  destruct H as [Hc Hq].
  split.
  - exact Hc.
  - eapply qpred_check_shrink_l.
    + exact Hq.
    + exact Hlen.
Qed.
Lemma qpred_check_length :
  forall T P,
    qpred_check T P ->
    length T = length P.
Proof.
  intros T P H.
  induction H.
  - reflexivity.
  - simpl.
    rewrite IHqpred_check.
    reflexivity.
Qed.

Lemma pred_check_q_length :
  forall env T W P,
    pred_check env T (W, P) ->
    length T = length P.
Proof.
  intros env T W P H.
  unfold pred_check in H.
  destruct H as [_ Hq].
  apply qpred_check_length.
  exact Hq.
Qed.

Definition pred_check
  (env : aenv)
  (T : type_map)
  (WP : cpred * qpred) : Prop :=
  match WP with
  | (W, P) =>
      cpred_check W env /\ qpred_check T P
  end.

Lemma pred_check_length :
  forall env T W P,
    pred_check env T (W, P) ->
    length T = length P.
Proof.
  intros env T W P H.
  unfold pred_check in H.
  simpl in H.
  destruct H as [_ Hq].
  apply qpred_check_length.
  exact Hq.
Qed.

Lemma pred_check_app_length_left :
  forall env T T1 W P,
    pred_check env (T ++ T1) (W, P) ->
    T1 = [] ->
    length T = length P.
Proof.
  intros env T T1 W P H HT1.
  subst T1.
  rewrite app_nil_r in H.
  eapply pred_check_length.
  exact H.
Qed.


Lemma compile_pexp_to_ir_skip :
  compile_pexp_to_ir PSKIP = [].
Proof.
  reflexivity.
Qed.

Lemma compile_pexp_to_ir_seq :
  forall s1 s2,
    compile_pexp_to_ir (PSeq s1 s2) =
    compile_pexp_to_ir s1 ++ compile_pexp_to_ir s2.
Proof.
  reflexivity.
Qed.

Lemma locus_system_frame :
  forall rmax q env Tin Tout e Tframe,
    @locus_system rmax q env Tin e Tout ->
    @locus_system rmax q env (Tin ++ Tframe) e (Tout ++ Tframe).
Proof.
  intros rmax q env Tin Tout e Tframe H.
  eapply sub_ses.
  exact H.
Qed.





Lemma relative_tightness_skip_only :
  forall rmax q env T W P,
    @locus_system rmax q env T PSKIP T ->
    pred_check env T (W, P) ->
    @triple rmax q env T (W, P) PSKIP (W, P).
Proof.
  intros.
  apply skip_pf.
Qed.

Lemma relative_tightness_aux_fixed_skip :
  forall rmax q env T W P W' Q,
    @locus_system rmax q env T PSKIP T ->
    pred_check env T (W, P) ->
    pred_check env T (W', Q) ->
    imply rmax (W, P) (W', Q) ->
    @triple rmax q env T (W, P) PSKIP (W', Q).
Proof.
  intros rmax q env T W P W' Q Hloc Hpre Hpost Himp.
  destruct Hpre as [Hcp Hqp].

  eapply triple_con_2 with (Q' := (W, P)) (T1 := T).

  - unfold type_check_proof.
    repeat split; simpl; auto.

  - exact Himp.

  - exact Hpost.

  - apply skip_pf.
Qed.

Lemma triple_post_consequence :
  forall rmax t env T T1 e W P W0 Q0 W' Q,
    type_check_proof rmax t env T T1 (W, P) (W0, Q0) e ->
    imply rmax (W0, Q0) (W', Q) ->
    pred_check env T1 (W', Q) ->
    @triple rmax t env T (W, P) e (W0, Q0) ->
    @triple rmax t env T (W, P) e (W', Q).
Proof.
  intros.
  eapply triple_con_2 with (Q' := (W0, Q0)) (T1 := T1); eauto.
Qed.

Lemma relative_completeness :
  forall rmax t env T e W P W0 Q0 W' Q n,
    type_check_proof rmax t env T T (W, P) (W0, Q0) e ->
    @triple rmax t env T (W, P) e (W0, Q0) ->
    imply rmax (W0, Q0) (W', Q) ->
    pred_check env T (W', Q) ->
    hoare_triple
      (trans env W P)
      (lower_ir_to_cmd n (compile_pexp_to_ir e))
      (trans env W' Q) ->
    @triple rmax t env T (W, P) e (W', Q).
Proof.
  intros.
  eapply triple_post_consequence; eauto.
Qed.

Lemma app_eq_same_length_nil :
  forall {A} (xs ys : list A),
    length (xs ++ ys) = length xs ->
    ys = [].
Proof.
  intros A xs ys H.
  rewrite app_length in H.
  assert (length ys = 0) by lia.
  apply length_zero_iff_nil.
  exact H0.
Qed.
Lemma relative_tightness_aux :
  forall rmax t env T e W P W' Q n,
    @locus_system rmax t env T e T ->
    pred_check env T (W, P) ->
    pred_check env T (W', Q) ->
    hoare_triple
      (trans env W P)
      (lower_ir_to_cmd n (compile_pexp_to_ir e))
      (trans env W' Q) ->
    @triple rmax t env T (W, P) e (W', Q).
Proof.
  intros rmax t env T e W P W' Q n Hloc Hpre Hpost Hhoare.
  induction Hloc.
- replace P with (P ++ []) at 1 by now rewrite app_nil_r.
replace Q with (Q ++ []) at 1 by now rewrite app_nil_r.
eapply triple_frame with
  (T := T')
  (T1 := T')
  (T' := T1)
  (R := []).
* unfold type_check_proof.
repeat split.
+ (* pre *)
  eapply pred_check_app_l.
**replace P with (P ++ []) by now rewrite app_nil_r.
replace (T' ++ T1) with ((T' ++ T1) ++ []) by now rewrite app_nil_r.

instantiate (1 := []).
repeat rewrite app_nil_r.
exact Hpre.
** eapply pred_check_length.
eapply pred_check_app_le with (T' := T1) (R := []).
*** rewrite app_nil_r.
  exact Hpre.
***(* length T' = length P *)
  eapply pred_check_length.
eapply pred_check_app_le with (T' := T1) (R := []).
 rewrite app_nil_r.
  exact Hpre.
eapply pred_check_length.
eapply pred_check_app_le with (T' := T1) (R := []).
rewrite app_nil_r.
  exact Hpre.
eapply pred_check_app_length_left.
exact Hpre.
eapply app_eq_same_length_nil.
 


Admitted.


Theorem qafny_compiler_relative_tightness :
  forall rmax t env T W P e W' Q n,
    type_check_proof rmax t env T T (W, P) (W', Q) e ->
    hoare_triple
      (trans env W P)
      (lower_ir_to_cmd n (compile_pexp_to_ir e))
      (trans env W' Q) ->
    @triple rmax t env T (W, P) e (W', Q).
Proof.
  intros rmax t env T W P e W' Q n Htc Hhoare.
  destruct (type_check_proof_to_locus _ _ _ _ _ _ _ _ _ Htc)
    as [Hloc [Hpre Hpost]].

  eapply relative_tightness_aux; eauto.
Qed.


Lemma triple_skip_consequence :
  forall rmax q env T W P W' Q,
    pred_check env T (W, P) ->
    pred_check env T (W', Q) ->
    imply rmax (W, P) (W', Q) ->
    @triple rmax q env T (W, P) PSKIP (W', Q).
Proof.
  intros rmax q env T W P W' Q Hpre Hpost Himp.

  eapply triple_con_2 with (Q' := (W, P)) (T1 := T).
  - unfold type_check_proof.
    split.
    + exact Hpre.
    + split.
      * change T with ([] ++ T).
        eapply sub_ses.
        apply skip_ses.
      * exact Hpre.
  - exact Himp.
  - exact Hpost.
  - apply skip_pf.
Qed.

Lemma pred_check_subst_type_map_back :
  forall env T Tframe x v W P,
    subst_type_map T x v = T ->
    pred_check env (T ++ Tframe) (W, P) ->
    pred_check env (subst_type_map T x v ++ Tframe) (W, P).
Proof.
  intros env T Tframe x v W P Hsubst Hpred.
  rewrite Hsubst.
  exact Hpred.
Qed.


Lemma hoare_triple_let_c_intro :
  forall fuel x a e P Q,
    entails P
      (subst_assertion_array P "q" (Const 0)
        (VarExpr (Array "temp"
          (safe_eval (translate_aexp a) (fun _ => None))))) ->
    hoare_triple
      P
      (lower_ir_to_cmd fuel (compile_pexp_to_ir e))
      Q ->
    hoare_triple
      P
      (lower_ir_to_cmd fuel (compile_pexp_to_ir (Let x (AE a) e)))
      Q.
Proof.
  intros fuel x a e P Q Hent Hbody.
  simpl.
  eapply seq_rule.
  - eapply consequence_rule.
    + exact Hent.
    + apply array_write_rule.
    + apply entails_refl.
  - exact Hbody.
Qed.


Lemma imply_refl :
  forall rmax P,
    imply rmax P P.
Proof.
  intros rmax [W Q].
  apply imply_cpred.
  intros s H.
  exact H.
Qed.

Lemma pred_check_app_left :
  forall env T Tframe W P,
    pred_check env (T ++ Tframe) (W, P) ->
    length T = length P ->
    pred_check env T (W, P).
Proof.
  intros env T Tframe W P Hpred Hlen.
  destruct Hpred as [Hc Hq].
  split.
  - exact Hc.
  - eapply qpred_check_shrink_l with (T' := Tframe) (P' := []).
    + rewrite app_nil_r.
      exact Hq.
    + exact Hlen.
Qed.
Lemma relative_tightness_aux_framed_exists :
  forall rmax q env Tin Tout e,
    @locus_system rmax q env Tin e Tout ->
    forall W P W' Q R Tframe fuel,
      pred_check env (Tin ++ Tframe) (W, P ++ R) ->
      pred_check env (Tout ++ Tframe) (W', Q ++ R) ->
      imply rmax (W, P ++ R) (W', Q ++ R) ->
      hoare_triple
        (trans env W (P ++ R))
        (lower_ir_to_cmd fuel (compile_pexp_to_ir e))
        (trans env W' (Q ++ R)) ->
      exists A B,
        imply rmax (W, P ++ R) A /\
        imply rmax B (W', Q ++ R).
Proof.
  intros rmax q env Tin Tout e Hloc.
  intros W P W' Q R Tframe fuel Hpre Hpost Himp Hhoare.

  exists (W, P ++ R).
  exists (W', Q ++ R).

  split.
  - apply imply_refl.
  - apply imply_refl.
Qed.

Lemma lowered_hoare_reflects_triple_exists_skip :
  forall rmax q env T W P n,
    type_check_proof rmax q env T T (W, P) (W, P) PSKIP ->
    hoare_triple
      (trans env W P)
      (lower_ir_to_cmd n (compile_pexp_to_ir PSKIP))
      (trans env W P) ->
    exists W0 Q0,
      @triple rmax q env T (W, P) PSKIP (W0, Q0).
Proof.
  intros rmax q env T W P n Htc Hhoare.
  exists W, P.
  apply skip_pf.
Qed.



Lemma type_check_proof_to_triple :
  forall rmax t env T W P e W' Q,
    type_check_proof rmax t env T T (W, P) (W', Q) e ->
    @triple rmax t env T (W, P) e (W', Q).
Proof.
Admitted.

Lemma relative_tightness:
  forall rmax t env T W P e W' Q n,
    type_check_proof rmax t env T T (W, P) (W', Q) e ->
    hoare_triple
      (trans env W P)
      (lower_ir_to_cmd n (compile_pexp_to_ir e))
      (trans env W' Q) ->
    exists W0 Q0,
      @triple rmax t env T (W, P) e (W0, Q0).
Proof.
  intros rmax t env T W P e W' Q n Htc Hhoare.
  exists W', Q.
  eapply type_check_proof_to_triple.
  exact Htc.
Qed.


(* Translation Quantum State to Array *)
Definition trans_qstate (q : qstate) : cpredr :=
  flat_map
    (fun '(l, se) =>
       match trans_locus l with
       | Some (name, idx) =>
           [CBArrayEq name (Const idx) (Const (trans_state_elem se))]
       | None => []
       end)
    q.
Definition trans_stack (W : stack) : cpredr :=
  flat_map
    (fun '(x, (r, v)) =>
       let name := var_to_string x in
       [CBArrayEq name (Const 0) (Const v)]) (AEnv.elements W).
Definition trans_state (phi : LocusDef.aenv * (stack * qstate)) : cpredr :=
  match phi with
  | (aenv, s) =>
      let (W, q) := s in
      trans_stack W ++ trans_qstate q
  end.

Lemma trans_state_surj :
  forall (s : stack * qstate),
    exists P : cpredr,
      P = trans_state (empty_aenv, s).
Proof.
  intros s.
  exists (trans_state (empty_aenv, s)).
  reflexivity.
Qed.












































 
    
