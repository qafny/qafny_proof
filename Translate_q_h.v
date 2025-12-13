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
(*
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
*)
(* Define equality comparison for variables *)
Definition eqb_var (v1 v2 : var) : bool :=
  match v1, v2 with
  | Scalar n1, Scalar n2 => String.eqb n1 n2
  | Array n1 i1, Array n2 i2 => String.eqb n1 n2 && Nat.eqb i1 i2
  | _, _ => false
  end.
(*
(* Define commands *)
Inductive cmd :=
  | Skip (* No operation *)
  | Assign (v : var) (e : expr) (* Variable assignment *)
  | ArrayWrite (name : string) (index : expr) (value : expr) (* Array write operation *)
  | Seq (c1 c2 : cmd) (* Sequential composition *)
  | If (b : expr) (c1 c2 : cmd) (* Conditional *)
  | While (b : expr) (c : cmd). (* While loop *)
*)
Inductive cmd :=
  | Skip
  | Assign (v : var) (e : expr)
  | ArrayWrite (name : string) (index : expr) (value : expr)
  | Seq (c1 c2 : cmd)
  | If (b : expr) (c : cmd) (* Modified: Only two arguments *)
  | While (b : expr) (c : cmd).

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
      | If b c =>
          match eval b s with
          | Some n => if Nat.eqb n 0 then Some s (* No explicit else branch, so do nothing *)
                      else exec fuel' c s
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
(* Define substitution function *)
Fixpoint subst (e : expr) (v : var) (e_subst : expr) : expr :=
  match e with
  | Const n => Const n
  | VarExpr x => if eqb_var x v then e_subst else VarExpr x
  | Plus e1 e2 => Plus (subst e1 v e_subst) (subst e2 v e_subst)
  | Minus e1 e2 => Minus (subst e1 v e_subst) (subst e2 v e_subst)
  end.
*)
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
  | if_rule : forall P Q b c1,
      hoare_triple P c1 Q ->
      hoare_triple P (If b c1 ) Q
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
Theorem hoare_if : forall P Q b c1,
  hoare_triple P c1 Q ->
  hoare_triple P (If b c1 ) Q.
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
  | AppSU e => Skip  (* Placeholder for single unitary operation *)
  | AppU l e => Skip  (* Placeholder for unitary application *)
  | PSeq s1 s2 =>
      Seq (translate_pexp s1) (translate_pexp s2)
  | If x s1 =>  (* Ensure If is applied correctly with 3 arguments *)
      If (translate_bexp x) (translate_pexp s1) Skip
  | For x l h b p =>
      Seq (Assign (convert_var x) (translate_aexp l))  (* Initialize loop variable *)
          (While 
             (Minus (translate_aexp h) (VarExpr (convert_var x))) (* Loop until x < h *)
             (If (translate_bexp b)  (* Run body only if `b` holds *)
                 (Seq (translate_pexp p)
                      (Assign (convert_var x) (Plus (VarExpr (convert_var x)) (Const 1))))
                 Skip))  (* Ensures correctness when `b` is false *)
  | Diffuse x => Skip (* Placeholder for diffusion operator *)
  end.
Theorem soundness_of_translation :
  forall (p : pexp) (s_p s_p' : state) (fuel : nat),
    eval_pexp p s_p = Some s_p' ->
    exec fuel (translate_pexp p) s_p = Some s_p'.
Proof.
  intros p s_p s_p' fuel Heval.
  induction p; simpl in *.
  
  - (* Case: PSKIP *)
    simpl. inversion Heval. reflexivity.

  - (* Case: Let x (AE a) s *)
    destruct (eval_aexp a s_p) eqn:Ha; try discriminate.
    simpl.
    assert (Htrans: translate_pexp (Let x (AE a) s) = Seq (Assign (convert_var x) (translate_aexp a)) (translate_pexp s)) by reflexivity.
    rewrite Htrans.
    simpl. rewrite Ha.
    specialize (IHp (update_state s_p (convert_var x) n) s_p' fuel).
    apply IHp. assumption.

  - (* Case: If *)
    destruct (eval_bexp b s_p) eqn:Hb; simpl; rewrite Hb.
    + apply IHp1. assumption.
    + apply IHp2. assumption.

  - (* Case: While *)
    remember (eval_bexp b s_p) as cond.
    destruct cond; simpl.
    + reflexivity.
    + apply IHp in Heval.
      simpl. rewrite Heval.
      apply IHp0. reflexivity.

  - (* Case: Seq *)
    specialize (IHp1 s_p s' fuel). rewrite IHp1; auto.
    specialize (IHp2 s' s_p' fuel). apply IHp2; auto.
Qed.
Theorem completeness_of_translation :
  forall (p : pexp) (s_c s_c' : state) (fuel : nat),
    exec fuel (translate_pexp p) s_c = Some s_c' ->
    eval_pexp p s_c = Some s_c'.
Proof.
  intros p s_c s_c' fuel Hexec.
  induction p; simpl in *.

  - (* Case: PSKIP *)
    inversion Hexec. reflexivity.

  - (* Case: Let x (AE a) s *)
    destruct (eval_aexp a s_c) eqn:Ha; try discriminate.
    simpl in Hexec.
    remember (exec fuel (translate_pexp s) (update_state s_c (convert_var x) n)) as exec_s.
    destruct exec_s eqn:Hexec_s; try discriminate.
    apply IHp in Hexec_s.
    simpl. rewrite Ha. assumption.

  - (* Case: If *)
    destruct (eval_bexp b s_c) eqn:Hb; simpl in Hexec; rewrite Hb in Hexec.
    + apply IHp1 in Hexec. assumption.
    + apply IHp2 in Hexec. assumption.

  - (* Case: While *)
    remember (eval_bexp b s_c) as cond.
    destruct cond; simpl in Hexec.
    + inversion Hexec. reflexivity.
    + apply IHp in Hexec.
      simpl. rewrite Hexec.
      apply IHp0. reflexivity.

  - (* Case: Seq *)
    remember (exec fuel (translate_pexp p1) s_c) as s_mid.
    destruct s_mid eqn:Hmid; try discriminate.
    apply IHp1 in Hmid.
    apply IHp2 in Hexec. rewrite Hmid. assumption.
Qed.
Theorem correctness_of_translation :
  forall (p : pexp) (s s' : state) (fuel : nat),
    eval_pexp p s = Some s' <-> exec fuel (translate_pexp p) s = Some s'.
Proof.
  intros.
  split.
  - (* Forward direction: Soundness *)
    apply soundness_of_translation.
  - (* Backward direction: Completeness *)
    apply completeness_of_translation.
Qed.
Theorem hoare_soundness_of_translation :
  forall (P Q : assertion) (p : pexp),
    hoare_triple P p Q ->
    hoare_triple P (translate_pexp p) Q.
Proof.
  intros P Q p Hhoare.
  induction Hhoare.

  - (* Case: Skip *)
    apply hoare_skip.

  - (* Case: Seq *)
    apply hoare_seq with Q; assumption.

  - (* Case: Assign *)
    apply hoare_assign.

  - (* Case: If *)
    apply hoare_if; assumption.

  - (* Case: While *)
    apply hoare_while; assumption.

  - (* Case: Consequence Rule *)
    apply hoare_consequence with P' Q'; assumption.
Qed.


(* Theorem: Soundness of Hoare logic *)
Theorem hoare_sound : forall P c Q,
  hoare_triple P c Q -> correct P c Q.
Proof.
  intros P c Q H.
  induction H.
  - (* Skip case *)
    unfold correct; intros; exists s; split; auto.
  - (* Sequential composition *)
    unfold correct in *.
    intros.
    specialize (IHhoare_triple1 s H1).
    destruct IHhoare_triple1 as [s' [Hexec1 Hvalid1]].
    specialize (IHhoare_triple2 s' Hvalid1).
    destruct IHhoare_triple2 as [s'' [Hexec2 Hvalid2]].
    exists s''; split; auto.
      simpl.
 exact Hexec1 .

  - (* Assignment case *)
    unfold correct; intros.
    destruct (eval e s) eqn:Heval; try contradiction.
    exists (fun x => if eqb_var x v then Some n else s x).
    split; auto.
  - (* If case *)
    unfold correct; intros.
    destruct (eval b s) eqn:Heval.
    + apply IHhoare_triple1; auto.
    + apply IHhoare_triple2; auto.
  - (* While case *)
    unfold correct; intros.
    induction (exec 100 (While b c) s) eqn:Hexec.
    + exists s0; split; auto.
    + contradiction.
  - (* Array write case *)
    unfold correct; intros.
    exists (fun x => if eqb_var x (Array name idx) then Some val else s x).
    split; auto.
  - (* Consequence case *)
    unfold correct in *; intros.
    apply H in H0.
    destruct (IHhoare_triple s H0) as [s' [Hexec Hvalid]].
    exists s'; split; auto.
    apply H1; auto.
Qed.


(*Soundness theorem*)
Theorem hoare_soundness : forall P c Q,
  hoare_triple P c Q ->
  forall s s', (forall b, In b P -> eval_cbexp s b = true) ->
               exec (1000) c s = Some s' -> (* Arbitrary large fuel *)
               (forall b, In b Q -> eval_cbexp s' b = true).
Proof.
  intros P c Q Hhoare.
  induction Hhoare; intros s s' HP Exec; simpl in Exec.
  - (* Skip case *)
    inversion Exec; subst; assumption.
  - (* Sequence case *)
    destruct (exec 1000 c1 s) eqn:H1; try congruence.
    apply IHHhoare2.
    + apply IHHhoare1; assumption.
    + assumption.
  - (* Assignment case *)
    destruct (eval e s) eqn:Heval; try congruence.
    intros b Hb.
    unfold subst_assertion.
    specialize (HP b Hb).
    simpl in HP.
    rewrite Heval in HP.
    assumption.
  - (* If case *)
    destruct (eval b s) eqn:Heval; try congruence.
    apply Nat.eqb_eq in Heval.
    destruct (Heval); [apply IHHhoare1 | apply IHHhoare2]; assumption.
  - (* While case *)
    remember (While b c) as w eqn:Heqw.
    revert dependent s.
    induction 1000 as [| fuel' IHfuel]; intros; simpl in Exec; try congruence.
    destruct (eval b s) eqn:Hb.
    + destruct (exec fuel' c s) eqn:ExecC; try congruence.
      apply IHfuel with (s := s0).
      * assumption.
      * assumption.
    + inversion Exec; subst; assumption.
  - (* Array write case *)
    intros b Hb.
    specialize (HP b Hb).
    unfold subst_assertion_array in HP.
    assumption.
  - (* Consequence case *)
    apply H2.
    apply IHHhoare.
    + intros b Hb. apply H0, HP, Hb.
    + assumption.
Qed.


(* Soundness Theorem: If Hoare triple holds for translated pexp, then it holds for original pexp. *)
Theorem hoare_soundness : forall P Q p,
  hoare_triple P (translate_pexp p) Q ->
  hoare_triple P p Q.
Proof.
  intros P Q p H.
  induction p; simpl in *.
  - (* Case: PSKIP *)
    apply hoare_skip.
  - (* Case: Let x (AE a) s *)
    apply hoare_seq with (subst_assertion P (convert_var v) (translate_aexp a)).
    + apply hoare_assign.
    + apply IHp.
  - (* Case: Let x (Meas y) s *)
    apply hoare_seq with (subst_assertion P (convert_var v) (VarExpr (convert_var y))).
    + apply hoare_assign.
    + apply IHp.
  - (* Case: PSeq s1 s2 *)
    apply hoare_seq; assumption.
  - (* Case: If x s1 *)
    apply hoare_if; assumption.
  - (* Case: For loop *)
    apply hoare_seq with (P := P).
    + apply hoare_assign.
    + apply hoare_while; apply hoare_if.
      * apply hoare_seq with (P := P).
        ** apply IHp.
        ** apply hoare_assign.
      * apply hoare_skip.
  - (* Case: Diffuse *)
    apply hoare_skip.
Qed.

(* Completeness Theorem: If Hoare triple holds for pexp, then it holds for its translated form in cmd. *)
Theorem hoare_translate_pexp_complete :
  forall P Q p,
    hoare_triple_pexp P p Q ->
    hoare_triple P (translate_pexp p) Q.
Proof.
  intros P Q p H.
  induction p; simpl.
  - (* Case: PSKIP *)
    apply hoare_skip.
  - (* Case: Let x (AE a) s *)
    apply hoare_seq with (subst_assertion P (convert_var v) (translate_aexp a)).
    + apply hoare_assign.
    + apply IHp; assumption.
  - (* Case: Let x (Meas y) s *)
    apply hoare_seq with (subst_assertion P (convert_var v) (VarExpr (convert_var y))).
    + apply hoare_assign.
    + apply IHp; assumption.
  - (* Case: PSeq s1 s2 *)
    apply hoare_seq; assumption.
  - (* Case: If x s1 *)
    apply hoare_if; assumption.
  - (* Case: For loop *)
    apply hoare_seq with (P := P).
    + apply hoare_assign.
    + apply hoare_while; apply hoare_if.
      * apply hoare_seq with (P := P).
        ** apply IHp.
        ** apply hoare_assign.
      * apply hoare_skip.
  - (* Case: Diffuse *)
    apply hoare_skip.
Qed.




(* Execution correctness definition *)
Definition correct (P: assertion) (c: cmd) (Q: assertion) : Prop :=
  forall s, (forall b, In b P -> eval_cbexp s b = true) ->
            exists s', exec 100 c s = Some s' /\ (forall b, In b Q -> eval_cbexp s' b = true).


Theorem hoare_complete : forall P c Q,
  (forall s, (forall b, In b P -> eval_cbexp s b = true) ->
             exists fuel, match exec fuel c s with
                          | Some s' => (forall b, In b Q -> eval_cbexp s' b = true)
                          | None => True
                          end) ->
  hoare_triple P c Q.

Theorem hoare_sound : forall P c Q,
  hoare_triple P c Q ->
  forall s, (forall b, In b P -> eval_cbexp s b = true) ->
            forall fuel, match exec fuel c s with
                         | Some s' => (forall b, In b Q -> eval_cbexp s' b = true)
                         | None => True
                         end.
Proof.
  intros P c Q H. induction H as [
    (* Case: skip_rule *)
    | P Q R c1 c2 H1 IH1 H2 IH2
    (* Case: seq_rule *)
    | Q v e
    (* Case: assign_rule *)
    | P Q b c1 c2 H1 IH1 H2 IH2
    (* Case: if_rule *)
    | P b c H1 IH1
    (* Case: while_rule *)
    | P name idx val
    (* Case: array_write_rule *)
    | P P' Q Q' c Hpre Hcmd IH Hpost
    (* Case: consequence_rule *)
  ]; intros s Hs fuel; simpl.
  
  - (* skip_rule: {P} Skip {P} *)
    destruct fuel; [trivial | simpl].
    exact Hs.

  - (* seq_rule: {P} c1; c2 {R} with {P} c1 {Q} and {Q} c2 {R} *)
    destruct fuel as [|fuel']; [trivial | simpl].
    destruct (exec fuel' c1 s) as [s' | ]; [| trivial].
    apply IH2. apply IH1. exact Hs.

  - (* assign_rule: {Q} v := e {Q} *)
    destruct fuel as [|fuel']; [trivial | simpl].
    destruct (eval e s) as [val | ]; [| trivial].
    intros b Hb. apply Hs. exact Hb.

  - (* if_rule: {P} if b then c1 else c2 {Q} *)
    destruct fuel as [|fuel']; [trivial | simpl].
    destruct (eval b s) as [n | ]; [| trivial].
    destruct (Nat.eqb n 0); [apply IH2 | apply IH1]; exact Hs.

  - (* while_rule: {P} while b do c {P} *)
    revert s Hs. induction fuel as [|fuel' IHfuel]; intros s Hs; [trivial | simpl].
    destruct (eval b s) as [n | ]; [| trivial].
    destruct (Nat.eqb n 0); [exact Hs |].
    destruct (exec fuel' c s) as [s' | ]; [| trivial].
    apply IHfuel. apply IH1. exact Hs.

  - (* array_write_rule: {P[idx/val]} ArrayWrite name idx val {P} *)
    destruct fuel as [|fuel']; [trivial | simpl].
    destruct (eval idx s) as [i | ]; [| trivial].
    destruct (eval val s) as [v | ]; [| trivial].
    intros b Hb. (* Need to show P holds after substitution *)
    admit. (* Placeholder: Requires reasoning about subst_assertion_array *)

  - (* consequence_rule: {P} c {Q} with P => P', {P'} c {Q'}, Q' => Q *)
    destruct (exec fuel c s) as [s' | ]; [| trivial].
    apply Hpost. apply IH. apply Hpre. exact Hs.

Admitted. (* Proof incomplete; some cases need refinement *)


