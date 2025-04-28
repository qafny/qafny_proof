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
Inductive cbexpr : Type :=
  | CBTrue : cbexpr                (* Represents a constant true condition *)
  | CBVar : var -> cbexpr          (* Represents a Boolean variable *)
  | CBArrayWrite : string -> expr -> expr -> cbexpr (* Represents an array write operation *)
  | CBAnd : cbexpr -> cbexpr -> cbexpr. (* Represents a conjunction (AND) of two `cbexp` expressions *)
(* Define evaluation of cbexp *)
Fixpoint eval_cbexp (s : state) (b : cbexpr) : bool :=
  match b with
  | CBTrue => true
  | CBVar v => match s v with Some n => Nat.ltb 0 n | None => false end
  | CBArrayWrite name idx val => false (* Array writes are not directly evaluable conditions *)
  | CBAnd b1 b2 => andb (eval_cbexp s b1) (eval_cbexp s b2)
  end.
Fixpoint expr_to_cbexp (e : expr) : cbexpr :=
  match e with
  | Const n => if Nat.eqb n 0 then CBTrue else CBTrue (* Simplified: non-zero is true *)
  | VarExpr x => CBVar x
  | Plus e1 e2 => CBTrue (* Simplified: arithmetic not directly boolean *)
  | Minus e1 e2 => CBTrue
  | Mult e1 e2 => CBAnd (expr_to_cbexp e1) (expr_to_cbexp e2)
  end.

Fixpoint subst_cbexp (b : cbexpr) (v : var) (e_subst : expr) : cbexpr :=
  match b with
  | CBTrue => CBTrue
  | CBVar x => if eqb_var x v then expr_to_cbexp e_subst else CBVar x
  | CBArrayWrite name idx val =>
      CBArrayWrite name (subst idx v e_subst) (subst val v e_subst)
  | CBAnd b1 b2 => CBAnd (subst_cbexp b1 v e_subst) (subst_cbexp b2 v e_subst)
  end.

Definition cpredr := list cbexpr.
(*
(* Define assertions as cpred *)
Definition cpred := list cbexp.
Definition assertion := cpred.
*)
(* Equality check for expressions *)
Fixpoint expr_eqb (e1 e2 : expr) : bool :=
  match e1, e2 with
  | Const n1, Const n2 => Nat.eqb n1 n2
  | VarExpr v1, VarExpr v2 => eqb_var v1 v2
  | Plus e1a e1b, Plus e2a e2b => expr_eqb e1a e2a && expr_eqb e1b e2b
  | Minus e1a e1b, Minus e2a e2b => expr_eqb e1a e2a && expr_eqb e1b e2b
  | _, _ => false
  end.

Fixpoint subst_array (b : cbexpr) (name : string) (idx : expr) (val : expr) : cbexpr :=
  match b with
  | CBTrue => CBTrue
  | CBVar v => CBVar v
  | CBArrayWrite n i v =>
      if String.eqb n name && expr_eqb i idx then CBArrayWrite name idx val
      else CBArrayWrite n i v
  | CBAnd b1 b2 => CBAnd (subst_array b1 name idx val) (subst_array b2 name idx val)
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
  | CBArrayWrite name idx val => Const 0 
  | CBAnd b1 b2 => Mult (translate_cbexp b1) (translate_cbexp b2) 
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
(*
(* Extend translate_pexp for ArrayWrite *)
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
  (* Add ArrayWrite case *)
  | ArrayAssign name idx val =>
      ArrayWrite name (translate_aexp idx) (translate_aexp val)
  end.
*)
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
Definition trans_qstate (q : qstate) : cpredr :=
  flat_map (fun '(l, se) => [CBVar (Array (trans_locus l) (trans_state_elem se))]) q.

Definition trans_stack (W : stack) :cpredr :=
  map (fun '(x, (r, v)) => CBVar (Scalar (var_to_string x))) (AEnv.elements W).
Definition trans_state (phi : LocusDef.aenv * (stack * qstate)) : cpredr:=
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

Theorem quantum_to_classical_completeness:
  forall (rmax : nat) (aenv : aenv) (s s' : stack * qstate) (e : pexp),
    @qfor_sem rmax aenv s e s' ->
    exists (pre post : cpredr) (c : cmd),
      hoare_triple pre c post /\
      c = translate_pexp e /\
      pre = trans_state (aenv, s) /\
      post = trans_state (aenv, s').
Proof.
 intros Pre Post c H.
  induction H; simpl in *.

Admitted.

(* Classical Semantics *)
Definition hoare_triple_sem (P : cpredr) (c : cmd) (Q : cpredr) : Prop :=
  forall (s s' : state) (fuel : nat),
    (forall b, In b P -> eval_cbexp s b = true) ->
    exec fuel c s = Some s' ->
    (forall b, In b Q -> eval_cbexp s' b = true).

Inductive mode : Type := 
  | CT  (* Classical *)
  | MT. (* Measurement/Quantum *)

Fixpoint trans_qpred (env : aenv) (qp : qpred) : cpredr :=
  match qp with
  | (SV l, se) :: rest =>
      CBVar (Array (trans_locus l) (trans_state_elem se)) :: trans_qpred env rest
  | _ :: rest => trans_qpred env rest
  | [] => []
  end.


Definition convert_locus_cpred (W : LocusProof.cpred) : cpredr :=
  (* Map LocusProof.cpred elements to cbexpr *)
  [].

Definition trans (env : aenv) (W : LocusProof.cpred) (P : qpred) : cpredr :=
  convert_locus_cpred W ++ trans_qpred env P.

Check trans.
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
    translate_pexp (Let x (AE a) e) =
    Seq (Assign (convert_var x) (translate_aexp a)) (translate_pexp e).
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
    let c := translate_pexp e in
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
eapply IHHtriple.
 eapply type_check_proof_invariant with (T1 := T1); eauto.
  eapply type_check_proof_fixed in H. subst. reflexivity.
intros b Hb. apply Hexec. exact Hb.
exact Hrun.

 - (*triple_frame *)
    eapply IHHtriple.
    + eapply type_check_proof_weaken_right; eauto.
      eapply type_check_proof_fixed in H. subst. reflexivity.
    + assumption.

 - (* triple_con_1 *)
intros Hexec_skip b Hb.
    inversion Hexec_skip; subst.
    apply exec_skip_correct in Hexec_skip; subst.
    destruct Htype as [Hcpred [Hlsys Hqpred]].
    subst. apply Hexec. eauto.
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
    inversion Hrun; subst.
      eapply IHHtriple; eauto.
    + eapply type_check_proof_invariant; eauto.
      eapply type_check_proof_fixed in H1 as ->.
       reflexivity.
     +  inversion H3; subst.
      eapply type_check_proof_fixed in H1 as ->.
unfold subst_pexp at 1.
simpl.

admit.

- (*let_c_pf *)

intros Hrun HIn.
simpl in Hrun.

repeat intros HInT.
remember (Assign (convert_var x) (translate_aexp a)) as c1.
remember (translate_pexp e) as c2.
simpl in Hrun.
destruct fuel as [| fuel']; simpl in Hrun; try discriminate.
destruct (exec fuel' c1 s) eqn:Hex1; try discriminate.

admit.

-(* Case: let_m_pf *)

intros Hrun.
destruct fuel as [|fuel']; [discriminate Hrun |].

inversion Hrun as [Hseq].
admit.

- (* let_q_pf *)
intros Hrun b0 HIn.
inversion Hrun; subst.
rewrite <- (Hexec b0); auto.
inversion Hrun; subst. 
+ destruct fuel; [discriminate Hrun |].
inversion Hrun; subst.  (* Derives s' = s *)
reflexivity. 
+ assert (W = W' /\ P = Q) as [HeqW HeqP].

{ 
 inversion Htype; subst.
split.

}

subst W'. subst P.
exact HIn .
Admitted.


(*
- (* Case: appu_nor_pf *)
intros Hrun. 
intros b0 Hb0.
inversion Hrun; subst.


admit.

-(* Case: appu_ch_pf *)
 intros Hrun.
 inversion Hrun. subst.
 intros b0 Hb0.
admit. 
- (* Case: apph_nor_pf *)
 intros Hrun.
 inversion Hrun. subst.
 intros b0 Hb0.
admit. 
-(* Case: apph_had_pf *)
  intros Hrun.
  simpl in Hrun.
  unfold translate_bexp in Hrun.
  destruct (simp_bexp b) eqn:Hsimp; try discriminate.
  rewrite H0 in Hsimp. simpl in Hrun.
   intros b1 Hb1.
  eapply IHHtriple; eauto.
(*
assert (T1 = T) by (eapply type_check_proof_fixed; eauto); subst.
exact H.

*)
apply type_check_proof_weaken_right with (T1 := T1).
 exact H.
apply type_check_proof_fixed in H.
assumption.
admit.
-(* Case: if_c_t *)
intros Hrun b0 HIn.
simpl in Hrun.

 inversion Hrun; subst. 
admit.

- (* Case: if_c_f *)
intros Hrun.
simpl in Hrun.
intros b0 HIn.
admit.
-(* Case: if_q *)
intros Hrun b0 HIn.
simpl in Hrun.
admit.

  - (* for_pf_f *)
    intros Hrun b0 Hb0.
    simpl in Hrun.
    inversion Hrun; subst.
 
admit.

 - (* for_pf *)
    intros Hrun.
    simpl in Hrun.
    inversion Hrun; subst.
    eapply IHHtriple2; eauto.
    + eapply type_check_proof_invariant; eauto.
      eapply type_check_proof_fixed in H0; subst; reflexivity.
   +
remember (Seq (translate_pexp e1) (translate_pexp e2)) as c_seq.
revert dependent s.
revert dependent s'.
induction fuel as [| fuel' IH]; intros s s' Hrun; simpl in Hrun; try discriminate.



Admitted.

*)






 
    



