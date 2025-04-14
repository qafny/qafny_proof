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
  | VarExpr (v : var) (* Variable *)
  | Const (n : nat) (* Natural number constant *)
  | Plus (e1 e2 : expr) (* Addition *)
  | Minus (e1 e2 : expr) (* Subtraction *)
  | Mult (e1 e2 : expr). (* Multiplication *)


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
  | Mult e1 e2 => (* Corrected: Handling Multiplication *)
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
  | Mult e1 e2 => Mult (subst e1 v e_subst) (subst e2 v e_subst) (* Corrected: Handle multiplication *)
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

(* Define logical entailment for assertions *)
Definition entails (P Q : assertion) : Prop :=
  forall s, (forall b, In b P -> eval_cbexp s b = true) -> 
            (forall b, In b Q -> eval_cbexp s b = true).

(* Hoare triples with the consequence rule *)
Inductive hoare_triple : assertion -> cmd -> assertion -> Prop :=
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

(*
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
*)

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
Definition convert_vart (v : BasicUtility.var) : var := Scalar "default".

(* Conversion function from BasicUtility.var to var *)
Definition convert_var (v : BasicUtility.var) : var :=
  match v with
  | _ => Scalar "default"
  end.
Fixpoint translate_aexp (e: aexp) : expr :=
  match e with
  | BA x => VarExpr (convert_vart x)  (* Convert BasicUtility.var to var *)
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
Fixpoint translate_cbexp (c : cbexp) : expr :=
  match c with
  | CBTrue => Const 1 
  | CBVar x => VarExpr x
  | CBArrayWrite name idx val => Const 0 
  | CBAnd b1 b2 => Mult (translate_cbexp b1) (translate_cbexp b2) 
  end.
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

Fixpoint translate_pexp (p : pexp) : cmd :=
  match p with
  | PSKIP => Skip
  | Let x (AE a) s =>
      Seq (Assign (convert_var x) (translate_aexp a)) (translate_pexp s)
  | Let x (Meas y) s =>
      Seq (Assign (convert_var x) (VarExpr (convert_var y))) (translate_pexp s)
  | AppSU e => Skip 
  | AppU l e => Skip 
  | PSeq s1 s2 =>
      Seq (translate_pexp s1) (translate_pexp s2)
  | QafnySyntax.If x s1 =>  
      If (translate_bexp x) (translate_pexp s1) Skip
  | For x l h b p =>
      Seq (Assign (convert_var x) (translate_aexp l)) 
          (While 
             (Minus (translate_aexp h) (VarExpr (convert_var x))) 
             (If (translate_bexp b)  
                 (Seq (translate_pexp p)
                      (Assign (convert_var x) (Plus (VarExpr (convert_var x)) (Const 1))))
                 Skip))  
  | Diffuse x => Skip 
  end.

(* Translate a classical+quantum state into a logical assertion *)

Definition trans_state_elem (se : state_elem) : nat :=
  match se with
  | Nval r b => 1 (* Simplified: non-zero for normal mode *)
  | Hval b => 2   (* Simplified: distinct value for Hadamard mode *)
  | Cval m f => m (* Simplified: use the number of states *)
  end.

Definition var_to_string (v : BasicUtility.var) : string :=
  match v with
  | _ => "default"  
  end.
Definition trans_locus (l : locus) : string :=
  match l with
  | (x, BNum a, BNum b) :: _ => var_to_string(x) 
  | _ => "default" 
  end.
Definition qpred : Type := list qpred_elem.
Definition trans_qstate (q : qstate) : assertion :=
  flat_map (fun '(l, se) => [CBVar (Array (trans_locus l) (trans_state_elem se))]) q.

Definition trans_stack (W : stack) : assertion :=
  map (fun '(x, (r, v)) => CBVar (Scalar (var_to_string x))) (AEnv.elements W).
Definition trans_state (phi : LocusDef.aenv * (stack * qstate)) : assertion :=
  match phi with
  | (aenv, s) =>
      let (W, q) := s in
      trans_stack W ++ trans_qstate q
  end.

Lemma exists_state_from_assertion :
  forall P : assertion,
    exists (s : stack * qstate),
      trans_state (empty_aenv, s) = P.
Proof.

Admitted.

Lemma trans_state_surj :
  forall (s : stack * qstate),
    exists P : assertion,
      P = trans_state (empty_aenv, s).
Proof.
  intros s.
  exists (trans_state (empty_aenv, s)).
  reflexivity.
Qed.
Theorem quantum_to_classical_completeness :
  forall Pre Post c,
    hoare_triple Pre c Post ->
    exists (rmax : nat) (aenv : LocusDef.aenv) (s s' : stack * qstate) (e : pexp),
      c = translate_pexp e /\
      Pre = trans_state (aenv, s) /\
      Post = trans_state (aenv, s') /\
      @qfor_sem rmax aenv s e s'.
Proof.
 intros Pre Post c H.
  induction H; simpl in *.
(* Case: skip_rule *)
  assert (Hstate: exists s : stack * qstate, trans_state (empty_aenv, s) = P).
  { apply exists_state_from_assertion. }
  destruct Hstate as [[W q] Htrans].
  exists 0%nat, empty_aenv, (W, q), (W, q), PSKIP.
  split.
  + reflexivity.
  + split.
    * symmetry. assumption.
    * split.
      - symmetry. assumption.
      - apply skip_sem.
(* Case: sequence *)
+    destruct IHhoare_triple1 as [rmax1 [aenv1 [s1 [s1' [e1 [Hc1 [HP1 [HQ1 Hsem1]]]]]]]].
    destruct IHhoare_triple2 as [rmax2 [aenv2 [s2 [s2' [e2 [Hc2 [HP2 [HQ2 Hsem2]]]]]]]].
    exists (rmax1 + rmax2), aenv1, s1, s2', (PSeq e1 e2).
    repeat split; auto.
    rewrite Hc1, Hc2.
    reflexivity.
admit.
(* Case: assign_rule *)
 +   destruct (exists_state_from_assertion P) as [[W q] Htrans].

Admitted.



(* Classical Semantics *)
Definition hoare_triple_sem (P : assertion) (c : cmd) (Q : assertion) : Prop :=
  forall (s s' : state) (fuel : nat),
    (forall b, In b P -> eval_cbexp s b = true) ->
    exec fuel c s = Some s' ->
    (forall b, In b Q -> eval_cbexp s' b = true).
(* Define mode for classical/quantum distinction *)
Inductive mode : Type := 
  | CT  (* Classical *)
  | MT. (* Measurement/Quantum *)

Fixpoint trans_qpred (env : aenv) (qp : qpred) : cpred :=
  match qp with
  | (SV l, se) :: rest =>
      (* You can use env here if needed to resolve variables *)
      CBVar (Array (trans_locus l) (trans_state_elem se)) :: trans_qpred env rest
  | _ :: rest => trans_qpred env rest
  | [] => []
  end.

Definition trans (env : aenv) (W : cpred) (P : qpred) : assertion :=
  W ++ trans_qpred env P.


Theorem quantum_to_classical_soundness:
  forall (t : atype) (env : aenv) (T : type_map)
         (W : cpred) (P : qpred)
         (e : pexp)
         (W' : cpred) (Q : qpred)
         (fuel : nat) (s s' : state),
    triple t env T (W, P) e (W', Q) ->
    let P' := trans env W P in
    let Q' := trans env W' Q in
    let c := translate_pexp e in
    (forall b, In b P' -> eval_cbexp s b = true) ->
    exec fuel c s = Some s' ->
    (forall b, In b Q' -> eval_cbexp s' b = true).

Proof. 

Admitted.




