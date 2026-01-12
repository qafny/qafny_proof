
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
  | CBAnd b1 b2 => andb (eval_cbexp s b1) (eval_cbexp s b2)
  | CBArrayWrite _ _ _ => false
  end.


Fixpoint expr_to_cbexp (e : expr) : cbexpr :=
  match e with
  | Const n => if Nat.eqb n 0 then CBTrue else CBTrue (* Simplified: non-zero is true *)
  | VarExpr x => CBVar x
  | Plus e1 e2 => CBTrue (* Simplified: arithmetic not directly boolean *)
  | Minus e1 e2 => CBTrue
  | Mult e1 e2 => CBAnd (expr_to_cbexp e1) (expr_to_cbexp e2)
  end.

(* Corrected subst_cbexp function *)
Fixpoint subst_cbexp (b : cbexpr) (v : var) (e_subst : expr) : cbexpr :=
  match b with
  | CBTrue => CBTrue
  | CBVar x => if eqb_var x v then expr_to_cbexp e_subst else CBVar x
  | CBArrayWrite name idx val =>
      CBArrayWrite name (subst idx v e_subst) (subst val v e_subst)
  | CBAnd b1 b2 => CBAnd (subst_cbexp b1 v e_subst) (subst_cbexp b2 v e_subst)
  | CBArrayEq name idx val =>
      CBArrayEq name (subst idx v e_subst) (subst val v e_subst)
  | CBAmpsEq name idx expected_amps =>
      CBAmpsEq name (subst idx v e_subst) expected_amps
  end.
Definition cpredr := list cbexpr.

(* Equality check for expressions *)
Fixpoint expr_eqb (e1 e2 : expr) : bool :=
  match e1, e2 with
  | Const n1, Const n2 => Nat.eqb n1 n2
  | VarExpr v1, VarExpr v2 => eqb_var v1 v2
  | Plus e1a e1b, Plus e2a e2b => expr_eqb e1a e2a && expr_eqb e1b e2b
  | Minus e1a e1b, Minus e2a e2b => expr_eqb e1a e2a && expr_eqb e1b e2b
  | _, _ => false
  end.

(* Amplitude encoding/decoding : assign a unique nat based on operation and qubit count *)
Definition encode_amps (amps : list (complex_approx * nat)) (op : single_u) (n : nat) : nat :=
  match op with
  | RH _ => 1  (* Hadamard encoding *)
  | SQFT _ => 2 + n (* QFT encoding *)
  | SRQFT _ => 3 + n (* Inverse QFT encoding *)
  end.

Fixpoint subst_array (b : cbexpr) (name : string) (idx : expr) (val : expr) : cbexpr :=
  match b with
  | CBTrue => CBTrue
  | CBVar v => CBVar v
  | CBArrayWrite n i v =>
      if andb (String.eqb n name) (expr_eqb i idx)
      then CBArrayWrite n idx val
      else CBArrayWrite n (subst i (Scalar name) idx) (subst v (Scalar name) val)
  | CBArrayEq n i v =>
      if andb (String.eqb n name) (expr_eqb i idx)
      then CBArrayEq n idx val
      else CBArrayEq n (subst i (Scalar name) idx) (subst v (Scalar name) val)
  | CBAmpsEq n i amps =>
      if andb (String.eqb n name) (expr_eqb i idx)
      then CBAmpsEq n idx amps
      else CBAmpsEq n (subst i (Scalar name) idx) amps
  | CBAnd b1 b2 =>
      CBAnd (subst_array b1 name idx val) (subst_array b2 name idx val)
  end.


Definition subst_assertion_array (P : cpredr) (name : string) (idx : expr) (val : expr) : cpredr :=
  map (fun b => subst_array b name idx val) P.

Definition subst_assertion (P : cpredr) (v : var) (e_subst : expr) : cpredr :=
  map (fun b => subst_cbexp b v e_subst) P.

(* Define logical entailment for assertions *)
Definition entails (P Q : cpredr) : Prop :=
  forall s, (forall b, In b P -> eval_cbexp s b = true) -> 
            (forall b, In b Q -> eval_cbexp s b = true).

(* Hoare triples with the consequence rule *)
Inductive hoare_triple : cpredr -> cmd ->cpredr -> Prop :=
  | skip_rule : forall P,
      hoare_triple P Skip P
  | seq_rule : forall P Q R c1 c2,
      hoare_triple P c1 Q ->
      hoare_triple Q c2 R ->
      hoare_triple P (Seq c1 c2) R
  | assign_rule : forall P v e,
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
Definition update_state (s : state) (x : var) (v : nat * list (complex_approx * nat)) : state :=
  fun y => if eqb_var x y then Some v else s y.

(* hoare_triple completeness*)
Theorem hoare_triple_complete :
  forall P c Q,
    (forall fuel s s',
        (forall b, In b P -> eval_cbexp s b = true) ->
        exec fuel c s = Some s' ->
        (forall b, In b Q -> eval_cbexp s' b = true)) ->
    hoare_triple P c Q.

Proof.

intros.
  revert P Q H.
  induction c; intros P Q H.
- (* c = Skip *)
  apply hoare_consequence with (P' := P) (Q' := P).
  + (* entails P P *) intros s Hpre b Hb. apply Hpre. assumption.
  + apply skip_rule.
  + (* entails P Q *) intros s Hpre b Hb.
    specialize (H 1 s s).
    assert (exec 1 Skip s = Some s) by reflexivity.
    apply H. auto. assumption. assumption.

- (* c = Assign v e *)
  apply hoare_consequence with (P' := subst_assertion P v e) (Q' := P).
  + (* entails P P' *)
    intros s Hpre b Hb.
    unfold subst_assertion in Hb.
    apply in_map_iff in Hb as [b0 [Hb0_eq Hb0_in]].
    subst. simpl.
    apply H with (fuel := 1) (s := s).
   intros b Hb. apply Hpre. assumption.
    simpl. 
 admit. admit.
+  apply assign_rule.
+ intros s Hpre b Hb.
specialize (H 1 s s Hpre).
simpl in H.
destruct (eval e s) eqn:Heval.
apply Hpre. 
 admit. apply Hpre.
 simpl in H.  admit.

- (* c = ArrayWrite *)
apply hoare_consequence with
  (P' := subst_assertion_array Q name index value)
  (Q' := Q).
admit. admit. admit.
- (* c = Seq c1 c2 *)
  specialize (IHc1 P).
  assert (Hexists : exists R, hoare_triple P c1 R /\ forall fuel s s',
    (forall b, In b R -> eval_cbexp s b = true) ->
    exec fuel c2 s = Some s' ->
    (forall b, In b Q -> eval_cbexp s' b = true)).
  (* Construct R as intermediate postcondition of c1 *)
exists Q. (* use Q itself as the intermediate postcondition *)
split.    remember
      (fun fuel s s' =>
        (forall b, In b P -> eval_cbexp s b = true) ->
        exec fuel (Seq c1 c2) s = Some s' ->
        (forall b, In b Q -> eval_cbexp s' b = true)) as SemSeq.
(* hoare_triple P c1 Q *)
  apply IHc1.
  intros fuel s s' Hpre Hexec1.
  (* Now simulate Seq step to get to s' *)
  specialize (H fuel s s').
  intros b Hb.
  apply H; auto.
  simpl.  admit.
 intros fuel s s' Hpre Hexec b Hb.
admit. admit.
 - (* If b c1 c2 *)
    apply hoare_if.
    + apply IHc1.
      intros fuel s s' Hpre Hexec.
intros b0 Hb.
specialize (H fuel s s' Hpre).

(* analyze eval b s to reconstruct If execution *)
destruct (eval b s) eqn:Heval.
 destruct (Nat.eqb n 0) eqn:Hn.
admit. admit. admit.
+ apply IHc2.
intros fuel s s' Hpre Hexec2.
specialize (H fuel s s' Hpre).
admit.
  - (* While *)
  apply hoare_consequence with (P' := P) (Q' := P).
  + unfold entails; intros s Hpre b0 Hb0. apply Hpre, Hb0.
  + apply hoare_while.
    apply IHc.
    intros fuel s s' Hpre Hexec.
  admit.
Admitted.

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
  | CBVar x => VarExpr x
  | CBArrayWrite _ _ _ => Const 0 (* Not a condition — placeholder *)
  | CBAnd b1 b2 => Mult (translate_cbexp b1) (translate_cbexp b2)
  | CBArrayEq name idx val =>
      let array_expr := VarExpr (Array name 0) in (* Placeholder index *)
      let idx_expr := idx in
      let actual := VarExpr (Array name 0) in (* Symbolic placeholder *)
      Minus (Const 1) (Minus actual val) (* Translates to equality if both match *)
  | CBAmpsEq _ _ _ => Const 0 (* Cannot translate complex amplitudes directly *)
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

(* Hoare Logic Rules for Intermediate Representation Operations *)
Inductive hoare_ir : cpredr -> ir_op -> cpredr -> Prop :=
  | hoare_ir_cast : forall P name idx tgt_mode,
      hoare_ir (CBArrayEq name idx (Const (mode_to_nat tgt_mode)) :: P)
               (IRCast name idx tgt_mode)
               (CBArrayEq name idx (Const (mode_to_nat tgt_mode)) :: P)
  | hoare_ir_locate : forall P name indices,
      hoare_ir P (IRLocate name indices) P
  | hoare_ir_typeupdate : forall P name idx m,
      hoare_ir (CBArrayEq name idx (Const m) :: P)
               (IRTypeUpdate name idx m)
               (CBArrayEq name idx (Const m) :: P)
  | hoare_ir_ampmodify : forall P name idx amp,
      forall amps',
        hoare_ir (CBAmpsEq name idx amps' :: P)
                 (IRAmpModify name idx amp)
                 (CBAmpsEq name idx (map (fun '(c,n) => (complex_mult amp c, n)) amps') :: P)
  | hoare_ir_map : forall P name f,
      hoare_ir P (IRMap name f) P
  | hoare_ir_partialmap : forall P name f cond,
      hoare_ir P (IRPartialMap name f cond) P
  | hoare_ir_join : forall P name idx loc,
      hoare_ir P (IRJoin name idx loc) P
  | hoare_ir_delete : forall P name cond,
      hoare_ir P (IRDelete name cond) P
  | hoare_ir_sum : forall P name indices v,
      hoare_ir P (IRSumAmplitudes name indices v) (CBVar v :: P)
  | hoare_ir_copy : forall P src_name src_idx dst_name dst_idx,
      hoare_ir (CBArrayEq dst_name dst_idx (Const 0) :: P)
               (IRCopy src_name src_idx dst_name dst_idx)
               (CBArrayEq dst_name dst_idx (Const 0) :: P)
  | hoare_ir_merge : forall P name idx1 idx2 tgt_idx,
      hoare_ir P (IRMerge name idx1 idx2 tgt_idx) P.

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


Lemma hoare_ir_cast_sound :
  forall P name idx tgt_mode,
    hoare_ir_sem
      (CBArrayEq name idx (Const (mode_to_nat tgt_mode)) :: P)
      (IRCast name idx tgt_mode)
      (CBArrayEq name idx (Const (mode_to_nat tgt_mode)) :: P).
Proof.
  unfold hoare_ir_sem, sat, eval_pred.
  intros P name idx tgt_mode fuel s s' Hexec Hsat.
  destruct fuel as [|fuel']; simpl in Hexec; try discriminate.
  destruct (eval idx s) as [i|] eqn:Heval; try discriminate.
  simpl in Hexec.
  inversion Hexec; subst s'; clear Hexec.

  inversion Hsat as [|p Ps Hhead Htail]; subst; clear Hsat.

  simpl.
    admit.
Admitted.


Lemma hoare_ir1_ampmodify :
  forall P name idx amp amps_old,
    hoare_ir
      (CBAmpsEq name idx amps_old :: P)
      (IRAmpModify name idx amp)
      (CBAmpsEq name idx (map (fun '(c,n) => (complex_mult amp c, n)) amps_old) :: P).
Proof.
Admitted.



Lemma hoare_ir_typeupdate_sound :
  forall P name idx m,
    hoare_ir_sem
      (CBArrayEq name idx (Const m) :: P)
      (IRTypeUpdate name idx m)
      (CBArrayEq name idx (Const m) :: P).
Proof.
  unfold hoare_ir_sem, sat, eval_pred.
  intros P name idx m fuel s s' Hexec Hsat.
  destruct fuel as [|fuel']; simpl in Hexec; try discriminate.
  destruct (eval idx s) as [i|] eqn:Heval; try discriminate.
  simpl in Hexec.
  inversion Hexec; subst s'; clear Hexec.

  inversion Hsat as [|p Ps Hhead Htail]; subst; clear Hsat.
  simpl.
Admitted.

Lemma hoare_ir_ampmodify_sound :
  forall P name idx amp amps_old,
    hoare_ir
      (CBAmpsEq name idx amps_old :: P)
      (IRAmpModify name idx amp)
      (CBAmpsEq name idx (map (fun '(c,n) => (complex_mult amp c, n)) amps_old) :: P).
Proof.

Admitted.
Notation "{{ P }} op {{ Q }}" := (hoare_ir_sem P op Q)
  (at level 90, op at next level).

Lemma hoare_ir_cast1_sound :
  forall Γ name idx tgt_mode,
    {{ Γ }}
      (IRCast name idx tgt_mode)
    {{ CBArrayEq name idx (Const (mode_to_nat tgt_mode)) :: Γ }}.
Proof.
Admitted.

Theorem hoare_ir_sound :
  forall P op Q,
    hoare_ir P op Q ->
    hoare_ir_sem P op Q.
Proof.


Admitted.


Lemma judge_IRCast :
  forall P name idx tgt_mode,
    hoare_ir (CBArrayEq name idx (Const (mode_to_nat tgt_mode)) :: P)
             (IRCast name idx tgt_mode)
             (CBArrayEq name idx (Const (mode_to_nat tgt_mode)) :: P).
Proof.
  intros. constructor. 
Qed.

Lemma judge_IRTypeUpdate :
  forall P name idx m,
    hoare_ir (CBArrayEq name idx (Const m) :: P)
             (IRTypeUpdate name idx m)
             (CBArrayEq name idx (Const m) :: P).
Proof.
  intros. constructor.  
Qed.

Lemma judge_IRAmpModify :
  forall P name idx amp amps',
    hoare_ir (CBAmpsEq name idx amps' :: P)
             (IRAmpModify name idx amp)
             (CBAmpsEq name idx (map (fun '(c,n) => (complex_mult amp c, n)) amps') :: P).
Proof.
  intros. econstructor.  
Qed.





(* Standard Cantor pairing *)
Definition nat_pair (x y : nat) : nat :=
  (x + y) * (x + y + 1) / 2 + y.

(* Encode a list (complex_approx * nat) as a single nat *)
Fixpoint encode_amp_list (amps : list (complex_approx * nat)) : nat :=
  match amps with
  | [] => 0
  | (c, k) :: tl =>
      let r := Z.to_nat (fst c) in
      let i := Z.to_nat (snd c) in
      let encoded_c := nat_pair (nat_pair r i) k in
      nat_pair encoded_c (encode_amp_list tl)
  end.

Fixpoint lower_ir_to_cmd (n_qubits : nat) (ops : list ir_op) : cmd :=
  match ops with
  | [] => Skip

  | op :: ops' =>
      let tail := lower_ir_to_cmd n_qubits ops' in
      match op with

      (* 1. Cast mode → write mode number into q[] *)
      | IRCast "q" idx mode =>
          Seq (ArrayWrite "q" idx (Const (mode_to_nat mode))) tail

      (* 2. Amplitude modification → write an encoded amplitude list *)
      | IRAmpModify "amps" idx new_amp =>
          (* Example canonical vector: new_amp on basis 0, zero on basis 1 *)
          let base_amps : list (complex_approx * nat) :=
                (new_amp, 0) :: ((0%Z, 0%Z), 1) :: nil in
          let encoded := encode_amp_list base_amps in
          Seq (ArrayWrite "amps" idx (Const encoded)) tail

      (* 3. Entanglement → mark all given indices as Ent with their numeric indices *)
      | IRJoin "q" _ locus =>
          let ent_indices := map (fun e => safe_eval e (fun _ => None)) locus in
          let ent_mode := Ent ent_indices in
          let ent_expr := Const (mode_to_nat ent_mode) in
          let mark_ent :=
            fold_right
              (fun i acc =>
                 Seq (ArrayWrite "q" i ent_expr) acc)
              Skip
              locus
          in
          Seq mark_ent tail

      (* 4. Measurement/sum → symbolically store number of indices into result_var *)
      | IRSumAmplitudes "q" indices result_var =>
          let n := length indices in
          Seq (Assign result_var (Const n)) tail

      (* 5. Unconditional map over all qubits in [0 .. n_qubits-1] *)
      | IRMap "q" f =>
          let body :=
            fold_right
              (fun i acc =>
                 Seq (ArrayWrite "q" (Const i) (f (Const i))) acc)
              Skip
              (seq 0 n_qubits)
          in
          Seq body tail

      (* 6. Conditional map: if cond then apply f to every qubit, else just tail *)
      | IRPartialMap "q" f cond =>
          let body :=
            fold_right
              (fun i acc =>
                 Seq (ArrayWrite "q" (Const i) (f (Const i))) acc)
              Skip
              (seq 0 n_qubits)
          in
          If cond
             (Seq body tail)
             tail

      (* 7. Fallback: ignore other IR ops for now *)
      | _ => tail
      end
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


(* Compile pexp to array operations *)
Fixpoint translate_pexp_array (p : pexp) : cmd :=
  match p with
  | PSKIP => Skip

  | Let x (AE a) s =>
      Seq (Assign (convert_var x) (translate_aexp a)) (translate_pexp_array s)

  | Let x (Meas y) s =>
      let y_var := convert_var y in
      let y_idx := var_to_index y_var in
      let aexp_y := AExp (expr_to_aexp (VarExpr y_var)) in
      Seq
        (ArrayWrite "q" y_idx (Const (mode_to_nat MT)))
        (Seq
           (ArrayWrite "amps" y_idx
              (Const (encode_amps (hadamard_amps_single 1) (RH aexp_y) 1)))
           (Seq
              (Assign (convert_var x) (VarExpr (Array "m" 0)))
              (translate_pexp_array s)))

  | AppSU e =>
      match e with
      | RH p => apply_quantum_op e [varia_to_index p]
      | SQFT x => apply_quantum_op e [var_to_index (convert_var x)]
      | SRQFT x => apply_quantum_op e [var_to_index (convert_var x)]
      end

  | AppU l e =>
    let mode := mode_to_nat Nor in
    fold_right
      (fun idx acc => Seq (ArrayWrite "q" idx (Const mode)) acc)
      Skip
      (locus_to_indices_expr l)

  | PSeq s1 s2 =>
      Seq (translate_pexp_array s1) (translate_pexp_array s2)

  | QafnySyntax.If x s1 =>
      If (translate_bexp x) (translate_pexp_array s1) Skip

  | For x l h b p =>
      Seq (Assign (convert_var x) (translate_aexp l))
          (While
             (Minus (translate_aexp h) (VarExpr (convert_var x)))
             (If (translate_bexp b)
                 (Seq (translate_pexp_array p)
                      (Assign (convert_var x) (Plus (VarExpr (convert_var x)) (Const 1))))
                 Skip))

  | Diffuse x =>
      apply_quantum_op (RH x) [varia_to_index x]
  end.

Definition test_pexp := AppSU (RH (AExp (Num 0))).
Compute translate_pexp_array test_pexp.

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


Theorem quantum_to_classical_completeness:
forall (rmax : nat) (t : atype) (env : aenv) (T : type_map)
         (e : pexp) (c : cmd) (P' Q' : cpredr),
    c = translate_pexp_array e ->
    hoare_triple P' c Q' ->
    exists (W : LocusProof.cpred) (P : qpred)
           (W' : LocusProof.cpred) (Q : qpred),
      (@triple rmax t env T (W, P) e (W', Q)) /\
      P' = trans env W P /\
      Q' = trans env W' Q.

Proof.
intros rmax t env T e c P' Q' Htrans Hhoare.
  induction e; simpl in Htrans; subst c.
(* Case 1: PSKIP *)
  - (* c = Skip *)
    inversion Hhoare; subst.
+
Admitted.
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
Axiom trans_empty_eq :

  forall (env : aenv) (H : cpredr),

    H = trans env [] [].
Axiom hoare_triple_empty :
  forall (c : cmd), hoare_triple ([] : list cbexpr) c ([] : list cbexpr).




Theorem quantum_to_classical_soundness_1:
  forall (rmax : nat) (t : atype) (env : aenv) (T : type_map)
         (e : pexp) (P' Q' : cpredr),
    exists (W W' : LocusProof.cpred) (P Q : qpred) (c : cmd),
      c = translate_pexp_array e /\
      @triple rmax t env T (W, P) e (W', Q) /\
      P' = trans env W P /\
      Q' = trans env W' Q /\
      hoare_triple P' c Q'.

Proof.
  induction e; simpl; intros H.

  - (* PSKIP *)
 intros Q'.
exists [], [], [], [], Skip.
repeat split.
apply skip_pf. (* triple t env T ([], []) PSKIP ([], []) *)
simpl in *.
+ apply trans_empty_eq.
+ apply trans_empty_eq.
+apply hoare_consequence with (P' := H) (Q' := H).
 unfold entails; intros s Hpre b Hb. apply Hpre, Hb.
 apply skip_rule.
(* entails H Q' *) unfold entails; intros s Hpre b Hb.
apply Hpre.
admit.
- (* Case n = AE a *)
intros Q'.
destruct n.
  destruct (IHe H Q') as [W [W' [P [Q [c [Hc [Htriple [HPtrans [HQtrans Hht]]]]]]]]].
  exists W, W', P, Q.
  + exists (Seq (Assign (convert_var x) (translate_aexp n)) c).
repeat split.
   rewrite Hc. reflexivity.
admit. admit. admit. admit.
+ admit.
-(* *)
 exists [], [], [], [].
(* Step 1: define c based on e *)
set (c := match e with
          | RH p => apply_quantum_op e [varia_to_index p]
          | _ => apply_quantum_op e [VarExpr (Scalar "default")]
          end).

(* Step 2: now provide c as the witness for the existential *)
exists c.
(* Step 3: split and prove each conjunct *)
repeat split.
+ admit.
+ apply trans_empty_eq.
+ apply trans_empty_eq.
+ apply hoare_triple_complete.
intros fuel s s' Hpre Hexec b Hb.
assert (s = s') as Hsame.
{
  inversion Hexec.
}
subst s.
apply Hpre.
admit.
- (* *)
intros Q'.

(* Explicitly typed predicate lists *)
set (W := cpred).
set (W' :=  cpred).
set (P := qpred).
set (Q := qpred).


(* Command construction *)
set (c := fold_right (fun (idx : expr) (acc : cmd) => Seq (ArrayWrite "q" idx (Const 2)) acc) Skip
           (locus_to_indices_expr l)).

(* Construct existential witnesses *)
 exists [], [], [], [].
exists c.
repeat split.
admit.
+ apply trans_empty_eq.
+ apply trans_empty_eq.
+ apply hoare_triple_complete.
intros fuel s s' Hpre Hexec b Hb.
assert (s = s') as Hsame.
{
  inversion Hexec.
}
subst s.
apply Hpre.
admit.
- (* *)
intros Q'.

(* Step 1: Use IHe1 to decompose e1 *)
specialize (IHe1 H).
(* Step 1: Use IHe1 to get first Hoare triple *)
destruct (IHe1 H) as
  [W1 [W1' [P1 [Q1 [c1 [Hc1 [Htr1 [Htrans1 [HQ1' Hhoare1]]]]]]]]].
(* Use IHe2 on the post-Hoare condition from e1 *)
destruct (IHe2 H Q') as
  [W2 [W2' [P2 [Q2 [c2 [Hc2 [Htr2 [Htrans2 [HQ' Hhoare2]]]]]]]]].
(*
(* Construct composed command *)
set (c := Seq c1 c2).
set (W := W1).
set (W' := W2').
set (P := P1).
set (Q := Q2).
(* Prove everything *)
exists W, W', P, Q, c.
repeat split.
*subst c. rewrite Hc1, Hc2. reflexivity.
* admit.

*apply seq_pf with
  (T1 := T)     (* first type_map *)
  (T2 := T)     (* second type_map *)
  (R := (W1', Q1)).

  + exact Htr1.
  + exact Htr2.
*)

admit.
- (* *)
intros Q'.

(* Use IHe with pre = H to get post Q1' *)
destruct (IHe H Q') as
  [W [W' [P [Q [c1 [Hc1 [Htr [Htrans [HQ' Hhoare]]]]]]]]].

(* Construct translated command for If *)
set (c := If (translate_bexp x) c1 Skip).

admit.
- (* *)
admit.
- (* *)
admit.


Admitted.

Lemma type_check_proof_fixed :
  forall rmax q env T T' P Q e,
    type_check_proof rmax q env T T' P Q e -> T' = T.
Proof.

  intros. destruct H; auto. 

Admitted.

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
Lemma translate_pexp_subst_let :
  forall x a e,
  translate_pexp_array (Let x (AE a) e) =
    Seq (Assign (convert_var x) (translate_aexp a)) (translate_pexp_array e).
Proof.
  intros x a e.
  simpl.
  reflexivity.
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

Lemma eval_cbexp_after_arraywrite :
  forall fuel s s' x i v,
    exec fuel (ArrayWrite x (Const i) (Const v)) s = Some s' ->
    eval_cbexp s' (CBArrayEq x (Const i) (Const v)) = true.
Proof.
  intros fuel s s' x i v Hexec.
  remember (ArrayWrite x (Const i) (Const v)) as cmd.
  induction fuel as [|fuel' IH] in s, s', x, i, v, Hexec |- *.
  - simpl in Hexec. discriminate.
  - simpl in Hexec.
    destruct s.
    simpl in Hexec.
    unfold eval_cbexp.
    simpl.
Admitted.


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

Theorem quantum_to_classical_soundness_weak_1 :
  forall (rmax : nat) (t : atype) (env : aenv) (T : type_map)
         (e : pexp) (P' Q' : cpredr),
    (exists (W W' : LocusProof.cpred) (P Q : qpred),
        @triple rmax t env T (W, P) e (W', Q) /\
        P' = trans env W P /\
        Q' = trans env W' Q) ->
    let c := classical_program_of e in
    hoare_triple P' c Q'.
Proof.

Admitted.
Inductive hoare_ir_list : cpredr -> list ir_op -> cpredr -> Prop :=
  | hoare_ir_list_nil : forall P,
      hoare_ir_list P [] P
  | hoare_ir_list_cons : forall P Q R op ops,
      hoare_ir P op Q ->
      hoare_ir_list Q ops R ->
      hoare_ir_list P (op :: ops) R.

(* Composition for concatenation (needed for PSeq / ++) *)
Lemma hoare_ir_list_app :
  forall P Q R ops1 ops2,
    hoare_ir_list P ops1 Q ->
    hoare_ir_list Q ops2 R ->
    hoare_ir_list P (ops1 ++ ops2) R.
Proof.
  intros P Q R ops1 ops2 H1 H2.
  induction H1.
  - simpl. exact H2.
  - simpl. econstructor; eauto.
Qed.


Theorem qafny_to_ir_sound :
  forall rmax t env T W P e W' Q,
    type_check_proof rmax t env T T (W, P) (W', Q) e ->
    @triple rmax t env T (W, P) e (W', Q) ->
    hoare_ir_list (trans env W P) (compile_pexp_to_ir e) (trans env W' Q).
Proof.

Admitted.

Lemma hoare_ir_list_map_change_partialmap_cond :
  forall P Q ops (cond : expr) (g : ir_op -> ir_op),
    (forall name f cond', g (IRPartialMap name f cond') = IRPartialMap name f (Plus cond cond')) ->
    (forall op, (forall name f cond', op = IRPartialMap name f cond' -> True) \/ g op = op) ->
    hoare_ir_list P ops Q ->
    hoare_ir_list P (map g ops) Q.
Proof.
Admitted.
Lemma type_check_proof_strengthen_ctx :
  forall rmax q env T T' W0 P0 W'0 Q0 e R2,
    type_check_proof rmax q env (T ++ T') (T ++ T')
      (W0, P0 ++ R2) (W'0, Q0 ++ R2) e ->
    type_check_proof rmax q env T T (W0, P0) (W'0, Q0) e.

Proof.
Admitted.




Theorem Qafny_compilation_sound_IR :
  forall rmax t env T W P e W' Q,
    type_check_proof rmax t env T T (W, P) (W', Q) e ->
    @triple rmax t env T (W, P) e (W', Q) ->
    hoare_ir_list
      (trans env W P)
      (compile_pexp_to_ir e)
      (trans env W' Q).
Proof.

intros rmax t env T W P e W' Q Htc Htr.
  revert Htc.
  induction Htr; intros Htc; subst; simpl in *.

  (* Case: Skip *)
  - (* triple_skip *)
    inversion Htc; subst; clear Htc.
  apply IHHtr.
 
inversion H0; subst.
destruct H1 as [Hloc Hpost].
inversion Hpost; subst.
  eapply type_check_proof_invariant with (T1 := T1); eauto.
  eapply type_check_proof_fixed; eauto.
  - inversion Htc; subst; clear Htc.
  apply IHHtr.
  assert (HT : T1 = T).
  { eapply type_check_proof_fixed; eauto. }

  eapply type_check_proof_invariant with (T1 := T1); eauto.

(* Case: Let x (Meas y) s *)
  - inversion Htc; subst; clear Htc.
  apply IHHtr.

  assert (HT : T1 = T).
  { eapply type_check_proof_fixed; eauto. }

  eapply type_check_proof_invariant with (T1 := T1); eauto.

(* Case: Sequence PSeq s1 s2 *)
  - inversion Htc; subst; clear Htc.
   subst.
admit.

(* Case: Single-qubit gates like AppSU (RH p) — Hadamard *)
  - inversion Htc; subst; clear Htc.
admit.

- (* *)

admit.





Admitted.


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

Axiom hoare_lower_map_preserve :
  forall P name f xs,
    hoare_triple P (lower_map name f xs) P.

Lemma hoare_ir_partialmap_sound :
  forall P name f cond n,
    hoare_ir P (IRPartialMap name f cond) P ->
    hoare_triple P
      (If cond (lower_map name f (seq 0 n)) Skip)
      P.
Proof.
  intros P name f cond n H_ir.
  apply if_rule.
  - apply hoare_lower_map_preserve.
  - apply skip_rule.
Qed.



Lemma entails_refl : forall P, entails P P.
Proof.
  unfold entails; intros P s HP b Hb; apply HP; assumption.
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


Lemma hoare_ir_partialmap_sound_11:
  forall P name f cond n,
    hoare_ir P (IRPartialMap name f cond) P ->
    hoare_triple P
      (lower_ir_to_cmd n (IRPartialMap name f cond :: nil))
      P.
Proof.
  intros P name f cond n H_ir.
  simpl.

  destruct (String.eqb name "q"%string) eqn:Hq.
  - 
    apply String.eqb_eq in Hq; subst name.
    simpl.

   
    apply if_rule.
    + 
      eapply seq_rule.
      *
        rewrite <- (lower_map_eq_fold_right "q"%string f (seq 0 n)).

        apply hoare_lower_map_preserve.
      * 
        apply skip_rule.
    + 
      apply skip_rule.

  -



Admitted.

Lemma hoare_ir_locate_sound_1 :
  forall P name indices,
    hoare_ir P (IRLocate name indices) P ->
    hoare_triple P Skip P.
Proof.
  intros. apply hoare_skip.
Qed.

Axiom entails_arrayeq_subst_self :
  forall (P : cpredr) (name : string) (idx val : expr),
    entails (CBArrayEq name idx val :: P)
            (subst_assertion_array (CBArrayEq name idx val :: P) name idx val).

Lemma hoare_ir_cast_sound_1 :
  forall P name idx tgt_mode n,
    hoare_ir (CBArrayEq name idx (Const (mode_to_nat tgt_mode)) :: P)
             (IRCast name idx tgt_mode)
             (CBArrayEq name idx (Const (mode_to_nat tgt_mode)) :: P) ->
    hoare_triple (CBArrayEq name idx (Const (mode_to_nat tgt_mode)) :: P)
                 (lower_ir_to_cmd n (IRCast name idx tgt_mode :: nil))
                 (CBArrayEq name idx (Const (mode_to_nat tgt_mode)) :: P).
Proof.

  intros P name idx tgt_mode n H_ir.
  simpl.

  destruct (String.eqb name "q"%string) eqn:Hq.

  -  apply String.eqb_eq in Hq; subst name.
    simpl.

    eapply seq_rule.
    + 
      eapply consequence_rule
        with (P' := subst_assertion_array
                    (CBArrayEq "q"%string idx (Const (mode_to_nat tgt_mode)) :: P)
                    "q"%string idx (Const (mode_to_nat tgt_mode)))
             (Q' := (CBArrayEq "q"%string idx (Const (mode_to_nat tgt_mode)) :: P)).
      * 
        apply entails_arrayeq_subst_self.
      * 
        eapply array_write_rule.
      * 
        apply entails_refl.
    + 
      apply skip_rule.

  - 
    simpl.
apply String.eqb_neq in Hq.  

destruct name eqn:HN; simpl.
  apply skip_rule.

  destruct (String.eqb (String a s) "q"%string) eqn:Heq.
  + apply String.eqb_eq in Heq; subst.
    exfalso. apply Hq. exact Heq.
  + simpl.



Admitted.


Lemma hoare_ir_typeupdate_sound_1 :
  forall P name idx m,
    hoare_ir (CBArrayEq name idx (Const m) :: P)
             (IRTypeUpdate name idx m)
             (CBArrayEq name idx (Const m) :: P) ->
    hoare_triple (CBArrayEq name idx (Const m) :: P)
                 (ArrayWrite name idx (Const m))
                 (CBArrayEq name idx (Const m) :: P).
Proof.
  intros P name idx m H_ir.

  eapply consequence_rule.
  - apply entails_arrayeq_subst_self.
  - eapply array_write_rule.

  - apply entails_refl.

Qed.



Axiom entails_ampmodify_bridge :
  forall P name idx amp amps_new amps_scaled encoded,
    amps_scaled =
      map (fun p => let '(c,n) := p in (complex_mult amp c, n)) amps_new ->
    encoded = encode_amp_list amps_scaled ->
    entails (CBAmpsEq name idx amps_new :: P)
            (subst_assertion_array (CBAmpsEq name idx amps_scaled :: P)
                                   name idx (Const encoded)).

Lemma hoare_ir_ampmodify_sound_1 :
  forall P name idx amp amps_new,
    hoare_ir (CBAmpsEq name idx amps_new :: P)
             (IRAmpModify name idx amp)
             (CBAmpsEq name idx
                (map (fun p => let '(c,n) := p in (complex_mult amp c, n)) amps_new) :: P) ->
    hoare_triple (CBAmpsEq name idx amps_new :: P)
      (ArrayWrite name idx
         (Const (encode_amp_list
            (map (fun p => let '(c,n) := p in (complex_mult amp c, n)) amps_new))))
      (CBAmpsEq name idx
         (map (fun p => let '(c,n) := p in (complex_mult amp c, n)) amps_new) :: P).
Proof.
  intros P name idx amp amps_new H_ir.
  set (amps_scaled :=
         map (fun p => let '(c,n) := p in (complex_mult amp c, n)) amps_new).
  set (encoded := encode_amp_list amps_scaled).

  eapply consequence_rule.
  - 
    eapply entails_ampmodify_bridge with (amps_scaled := amps_scaled) (encoded := encoded).
 + subst amps_scaled.
reflexivity.
+ subst encoded.
reflexivity.
- eapply array_write_rule.
- apply entails_refl.
Qed.

(*  General translation for lists of IR operations  *)
Theorem hoare_ir_list_to_triple :
  forall P ops Q n,
    hoare_ir_list P ops Q ->
    hoare_triple P (lower_ir_to_cmd n ops) Q.
Proof.
  intros P ops.
  induction ops as [|op tl IH]; intros Q n Hlist.
  - inversion Hlist; subst. simpl. apply hoare_skip.
  - inversion Hlist as [|P0 P1 P2 op0 tl0 Hop Htl]; subst.
    simpl.
Admitted.


(*  Full Translation  *)
Theorem qafny_compiler_sound_classical :
  forall rmax t env T W P e W' Q n,
 type_check_proof rmax t env T T (W, P) (W', Q) e ->
    @triple rmax t env T (W,P) e (W',Q) ->
    hoare_triple
      (trans env W P)
      (lower_ir_to_cmd n (compile_pexp_to_ir e))
      (trans env W' Q).
Proof.
  intros.
  apply hoare_ir_list_to_triple with (n := n).
eapply Qafny_compilation_sound_IR; eauto.

Qed.


Theorem quantum_to_classical_soundness_IR_cmd :
  forall rmax t env T W P e W' Q φ φ' fuel,
    @triple rmax t env T (W, P) e (W', Q) ->
    let ops := compile_pexp_to_ir e in
    let n   := count_qubits_in_pexp e in
    let c   := lower_ir_to_cmd n ops in
    let P'  := trans env W P in
    let Q'  := trans env W' Q in
    model P' φ ->
    exec fuel c φ = Some φ' ->
    model Q' φ'.
Proof.
Admitted.

Theorem qafny_compiler_sound :
  forall rmax t env T W P e W' Q,
    type_check_proof rmax t env T T (W, P) (W', Q) e ->
    @triple rmax t env T (W, P) e (W', Q) ->
    hoare_triple
      (trans env W P)
      (classical_program_of e)
      (trans env W' Q).
Proof.
Admitted.



Theorem quantum_to_classical_soundness_0 :
  forall (rmax : nat) (t : atype) (env : aenv) (T : type_map)
         (W W' : LocusProof.cpred) (P Q : qpred)
         (e : pexp) (φ φ' : state) (fuel : nat),
    (* Quantum correctness *)
    type_check_proof rmax t env T T (W, P) (W', Q) e ->
    @triple rmax t env T (W, P) e (W', Q) ->

    (* Classical translation *)
    let c  := classical_program_of e in
    let P' := trans env W P in
    let Q' := trans env W' Q in

    model P' φ ->
    exec fuel c φ = Some φ' ->
    model Q' φ'.
Proof.

Admitted.



Theorem quantum_to_classical_soundness_2 :
  forall (rmax : nat) (t : atype) (env : aenv) (T : type_map)
         (W W' : LocusProof.cpred) (P Q : qpred)
         (e : pexp) (φ φ' : state) (fuel : nat),

    type_check_proof rmax t env T T (W, P) (W', Q) e ->
    @triple rmax t env T (W, P) e (W', Q) ->

    let c  := classical_program_of e in
    let P' := trans env W P in
    let Q' := trans env W' Q in

    model P' φ ->
    exec fuel c φ = Some φ' ->
    model Q' φ'.


Proof.
  intros rmax t env T W W' P Q e φ φ' fuel Htype Htriple.
  intros c P' Q'; subst c P' Q'.
  induction Htriple; simpl in *; intros Hpre Hexec.

Admitted.


(*

(* === Qafny to Hoare Logic Compilation Soundness === *)
Theorem quantum_to_classical_soundness :
  forall (rmax : nat) (t : atype) (env : aenv) (T : type_map)
         (W W' : LocusProof.cpred) (P Q : qpred)
         (e : pexp)
         (φ φ' : state) (fuel : nat),
    type_check_proof rmax t env T T (W, P) (W', Q) e ->
    @triple rmax t env T (W, P) e (W', Q) ->
    let c := translate_pexp_array e in
    let P' := trans env W P in
    let Q' := trans env W' Q in
    model P' φ ->
    exec fuel c φ = Some φ' ->
    model Q' φ'.

Proof.
  intros rmax t env T W W' P Q e φ φ' fuel Htype Htriple c P' Q' Hmodel Hexec.
  subst c P' Q'.
  induction e; simpl in Hexec; simpl in *; subst.
  - (* Case 1: PSKIP *)
inversion Htype; subst. (* Extract typing info *)
    inversion Htriple; subst. (* Extract triple info *)
    apply exec_skip_correct in Hexec; subst φ'. (* exec fuel Skip φ = Some φ *)
    (* Since PSKIP preserves state and W' = W, Q = P (via skip_pf) *)
    unfold model in *.
   intros b Hb.
+ admit.
+ admit.
+ admit.
+ admit.

    - (* Case 2: Let x (AE a) s *)
 inversion Htype; subst. (* Extract typing info, get W1, P1, W', Q *)
admit.

   - (* Case 3: Let x (Meas y) s *)
 inversion Htype; subst.
    inversion Htriple; subst.
Admitted.


(*
Theorem quantum_to_classical_soundness :
  forall (rmax : nat) (t : atype) (env : aenv) (T : type_map)
         (W : LocusProof.cpred) (P : qpred)
         (e : pexp)
         (W' : LocusProof.cpred) (Q : qpred)
         (fuel : nat) (s s' : state),
    type_check_proof rmax t env T T (W, P) (W', Q) e ->
    @triple rmax t env T (W, P) e (W', Q) ->
    let P' := trans env W P in
    (forall b, In b P' -> eval_cbexp s b = true) ->
    let c := translate_pexp_array e in
    exec fuel c s = Some s' ->
    let Q' := trans env W' Q in
    (forall b, In b Q' -> eval_cbexp s' b = true).

Proof.
  intros rmax t env T W P e W' Q fuel s s' Htype Htriple.
  revert s s'.
  induction Htriple; intros s s' HP' Hexec; simpl in *.

  - (* skip_pf *)
intros Hexec1 b Hb.
eapply IHHtriple; eauto.
eapply type_check_proof_invariant with (T1 := T1); eauto.
  eapply type_check_proof_fixed in H. subst. reflexivity.

  - (* seq_pf *)
intros Hrun.
eapply IHHtriple; eauto.
 eapply type_check_proof_invariant with (T1 := T1); eauto.
  eapply type_check_proof_fixed in H. subst. reflexivity.

 - (*triple_frame *)
    eapply IHHtriple.
    + eapply type_check_proof_weaken_right; eauto.
      eapply type_check_proof_fixed in H. subst. reflexivity.
    + assumption.

 - (* triple_con_1 *)
intros Hexec_skip b Hb.
    inversion Hexec_skip. subst.
    apply exec_skip_correct in Hexec_skip. subst.
    destruct Htype as [Hcpred [Hlsys Hqpred]].
    subst. apply Hexec. 
   unfold HP'.
   assert (W = W' /\ P = Q) as [HeqW HeqP].
{ 
  destruct P0 as [W_pre P_pre].
  simpl in *.
  split.

}

subst W'. subst P.
exact Hb.
  - (* triple_con_2 *)
    intros Hrun.
simpl in Hrun.
eapply IHHtriple; eauto.
eapply type_check_proof_invariant with (T1 := T1); eauto.
eapply type_check_proof_fixed in H1 . subst. reflexivity.
rewrite <- Hrun.
 inversion Hrun; subst.
destruct H.
try easy.
inversion Htype; subst; clear Htype.
destruct H2 as [Hlocus_system _].
admit.

- (*let_c_pf *)

intros Hrun HIn.
simpl in Hrun.
repeat intros HInT.
  unfold exec in Hrun.

admit.

-(* Case: let_m_pf *)

intros Hrun.
destruct fuel as [|fuel']; [discriminate Hrun |].

admit.
- (* let_q_pf *)
intros Hrun b0 HIn.
inversion Hrun; subst.
rewrite <- (Hexec b0); auto.
inversion Hrun; subst. 
+ destruct fuel; [discriminate Hrun |].
inversion Hrun; subst. admit.
+ assert (W = W' /\ P = Q) as [HeqW HeqP].

{ 
 inversion Htype; subst.
split.

}

subst W'. subst P.
exact HIn .

- (* Case: appu_nor_pf *)
intros Hrun b0 HIn.
inversion Hrun; subst.
rewrite <- (Hexec b0); auto.
inversion Hrun; subst. 
+ destruct fuel; [discriminate Hrun |].
inversion Hrun; subst.  
admit. 
+ assert (W = W' /\ P = Q) as [HeqW HeqP].

{ 
 inversion Htype; subst.
split.

}

subst W'. subst P.
exact HIn .

- (* Case: appu_ch_pf *)
intros Hrun b0 HIn.
inversion Hrun; subst.
rewrite <- (Hexec b0); auto.
inversion Hrun; subst. 
+ destruct fuel; [discriminate Hrun |].
inversion Hrun; subst.  
admit. 
+ assert (W = W' /\ P = Q) as [HeqW HeqP].

{ 
 inversion Htype; subst.
split.

}

subst W'. subst P.
exact HIn .
- (* Case: apph_nor_pf *)
intros Hrun b0 HIn.
inversion Hrun; subst.
rewrite <- (Hexec b0); auto.
inversion Hrun; subst. 
+ destruct fuel; [discriminate Hrun |].
inversion Hrun; subst.  
admit. 
+ assert (W = W' /\ P = Q) as [HeqW HeqP].

{ 
 inversion Htype; subst.
split.

}

subst W'. subst P.
exact HIn .
-(* Case: apph_had_pf *)
intros Hrun b0 HIn.
inversion Hrun; subst.
rewrite <- (Hexec b0); auto.
inversion Hrun; subst. 
+ destruct fuel; [discriminate Hrun |].
inversion Hrun; subst.  
admit. 
+ assert (W = W' /\ P = Q) as [HeqW HeqP].

{ 
 inversion Htype; subst.
split.

}

subst W'. subst P.
exact HIn .
- (* Case: if_c_t *)
intros Hrun b0 HIn.
inversion Hrun; subst.
rewrite <- (Hexec b0); auto.
inversion Hrun; subst. 
+ destruct fuel; [discriminate Hrun |].
inversion Hrun; subst.  
admit. 
+ assert (W = W' /\ P = Q) as [HeqW HeqP].

{ 
 inversion Htype; subst.
split.

}

subst W'. subst P.
exact HIn .
- (* Case: if_c_f *)
intros Hrun b0 HIn.
inversion Hrun; subst.
rewrite <- (Hexec b0); auto.
inversion Hrun; subst. 
+ destruct fuel; [discriminate Hrun |].
inversion Hrun; subst.  
admit. 
+ assert (W = W' /\ P = Q) as [HeqW HeqP].

{ 
 inversion Htype; subst.
split.

}

subst W'. subst P.
exact HIn .
- (* Case: if_q *)
intros Hrun b0 HIn.
inversion Hrun; subst.
rewrite <- (Hexec b0); auto.
inversion Hrun; subst. 
+ destruct fuel; [discriminate Hrun |].
inversion Hrun; subst.  
admit. 
+ assert (W = W' /\ P = Q) as [HeqW HeqP].

{ 
 inversion Htype; subst.
split.

}

subst W'. subst P.
exact HIn .
- (* for_pf_f *)
intros Hrun b0 HIn.
inversion Hrun; subst.
rewrite <- (Hexec b0); auto.
inversion Hrun; subst. 
+ destruct fuel; [discriminate Hrun |].
inversion Hrun; subst.  
admit. 
+ assert (W = W' /\ P = Q) as [HeqW HeqP].

{ 
 inversion Htype; subst.
split.

}

subst W'. subst P.
exact HIn .
- (* for_pf *)
intros Hrun b0 HIn.
inversion Hrun; subst.
rewrite <- (Hexec b0); auto.
inversion Hrun; subst. 
+ destruct fuel; [discriminate Hrun |].
inversion Hrun; subst.  
admit. 
+ assert (W = W' /\ P = Q) as [HeqW HeqP].

{ 
 inversion Htype; subst.
split.

}

subst W'. subst P.
exact HIn .

Admitted.

*)
*)

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




































































 
    
