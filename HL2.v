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
  | BA v => Some (convert_var v)  (* Convert BasicUtility.var to var *)
  | _ => None  (* Handle cases where aexp is not just a variable *)
  end.
Definition convert_cbexp (c : QafnySyntax.cbexp) : cbexp :=
  match c with
  | QafnySyntax.CEq e1 e2 =>
      match extract_var e1, extract_var e2 with
      | Some v1, Some v2 => CBAnd (CBVar v1) (CBVar v2) (* Example: Adjust mapping *)
      | _, _ => CBTrue (* Fallback case if we can't extract variables *)
      end
  | QafnySyntax.CLt e1 e2 =>
      match extract_var e1, extract_var e2 with
      | Some v1, Some v2 => CBAnd (CBVar v1) (CBVar v2) (* Example: Adjust mapping *)
      | _, _ => CBTrue
      end
  end.
Print varia.
Definition convert_varia_to_aexp (v : varia) : aexp :=
  match v with
  | AExp e => e  (* Directly return the contained aexp *)
  | Index var exp => APlus (BA var) exp  (* Example: Represent index as an addition *)
  end.
Definition safe_eval (e : expr) (s : state) : nat :=
  match eval e s with
  | Some n => n
  | None => 0 (* Default value to handle cases where evaluation fails *)
  end.
Fixpoint translate_bexp (b : bexp) : expr :=
  match b with
  | CB c => translate_cbexp (convert_cbexp c) (* Convert cbexp properly *)
  | BEq e1 e2 i a => 
      let left := translate_aexp (convert_varia_to_aexp e1) in
      let right := translate_aexp (convert_varia_to_aexp e2) in
      Minus (Const 1) (Plus (Minus left right) (Minus right left)) (* Boolean equality check *)
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
  | AppSU e => Skip  (* Placeholder: Needs proper translation if required *)
  | AppU l e => Skip  (* Placeholder: Needs proper translation if required *)
  | PSeq s1 s2 =>
      Seq (translate_pexp s1) (translate_pexp s2)
  | If x s1 => (* Ensure If always has three arguments *)
      If (translate_bexp x) (translate_pexp s1) Skip
  | IfElse x s1 s2 => (* Explicitly handle IfElse *)
      If (translate_bexp x) (translate_pexp s1) (translate_pexp s2)
  | For x l h b p =>
      Seq (Assign (convert_var x) (translate_aexp l))
          (While 
             (Minus (translate_aexp h) (VarExpr (convert_var x))) (* Ensuring it runs until h *)
             (Seq (translate_pexp p)
                  (Assign (convert_var x) (Plus (VarExpr (convert_var x)) (Const 1)))))
  | Diffuse x => Skip (* Placeholder: Needs proper translation if required *)
  end.
(*
Theorem convert_var_unique : forall v1 v2 : BasicUtility.var,
  convert_var v1 = convert_var v2 -> v1 = v2.
Proof.
  intros v1 v2 H.
 simpl.
Abort.
Theorem translate_aexp_correct : forall (a : aexp) (s : state),
  eval (translate_aexp a) s = Some (safe_eval (translate_aexp a) s).
Proof.
  intros a s.
  induction a; simpl; try reflexivity.
  - (* Case: BA x *)
    destruct (convert_var v); reflexivity.
  - (* Case: Num n *)
    reflexivity.
  - (* Case: APlus e1 e2 *)
    rewrite IHa1, IHa2.
    destruct (eval (translate_aexp a1) s) eqn:E1;
    destruct (eval (translate_aexp a2) s) eqn:E2;
    simpl; reflexivity.
  - (* Case: AMult e1 e2 *)
    rewrite IHa1, IHa2.
    destruct (eval (translate_aexp a1) s) eqn:E1;
    destruct (eval (translate_aexp a2) s) eqn:E2;
    simpl; reflexivity.
Qed.
Theorem translate_bexp_correct : forall (b : bexp) (s : state),
  eval (translate_bexp b) s = Some (if eval (translate_bexp b) s then 1 else 0).
Proof.
  intros b s.
  induction b; simpl; try reflexivity.
  - (* Case: CB c *)
    destruct (convert_cbexp c); simpl; reflexivity.
  - (* Case: BEq e1 e2 i a *)
    destruct (eval (translate_aexp (convert_varia_to_aexp e1)) s) eqn:E1;
    destruct (eval (translate_aexp (convert_varia_to_aexp e2)) s) eqn:E2;
    simpl; try reflexivity.
  - (* Case: BLt e1 e2 i a *)
    destruct (eval (translate_aexp (convert_varia_to_aexp e1)) s) eqn:E1;
    destruct (eval (translate_aexp (convert_varia_to_aexp e2)) s) eqn:E2;
    simpl; try reflexivity.
Qed.
Theorem translate_pexp_correct : forall (p : pexp) (s : state) (fuel : nat),
  exec fuel (translate_pexp p) s = Some s.
Proof.
  intros p s fuel.
  induction p; simpl; try reflexivity.
  - (* Case: PSKIP *)
    reflexivity.
  - (* Case: Let x (AE a) s *)
    destruct (eval (translate_aexp a) s) eqn:E.
    + simpl. apply IHp.
    + simpl. reflexivity.
  - (* Case: PSeq s1 s2 *)
    rewrite IHp1. apply IHp2.
  - (* Case: If x s1 *)
    destruct (eval (translate_bexp x) s) eqn:E.
    + apply IHp.
    + reflexivity.
  - (* Case: IfElse x s1 s2 *)
    destruct (eval (translate_bexp x) s) eqn:E.
    + apply IHp1.
    + apply IHp2.
  - (* Case: For x l h b p *)
    (* Needs an induction on fuel to handle the loop properly *)
Abort.


*)



















(*
(* Axiom stating that BasicUtility.var can be converted to var *)
Axiom var_equiv : BasicUtility.var -> var.
Axiom aexp_to_expr : aexp -> expr.
Axiom pexp_to_expr : pexp -> expr.
Axiom pexp_to_maexp : pexp -> maexp.
Axiom pexp_to_exp : pexp -> exp.
Axiom pexp_to_bexp: pexp -> bexp.
Axiom pexp_to_cmd : pexp -> cmd.
Axiom bexp_to_expr : bexp -> expr.

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

*)



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
    let c := translate_pexp e in
    exec fuel c s = Some s' ->
    let Q' := trans env W' Q in
    forall b : cbexpr, In b Q' -> eval_cbexp s' b = true.
Proof.
  intros rmax t env T W P e W' Q fuel s s' Htype Htriple HP' Hexec.
  induction Htriple; intros b0 Hb0; simpl in *; unfold trans in *;
    try (destruct fuel; [discriminate| simpl in Hexec]).

  - (* skip_pf *)
  destruct fuel as [| fuel']; simpl in Hexec; try discriminate.
apply IHHtriple; try assumption.
 exact H.         (* type_check_proof for e *)
- exact Hexec.     (* eval_cbexp s holds for each b in precondition *)
- exact Hb0. 

  - (* seq_pf *)
    destruct (exec fuel (translate_pexp e1) s) eqn:He1; [|discriminate].
    inversion Hexec; subst.
    eapply IHHtriple2; eauto.
    + eapply IHHtriple1; eauto.
      * eapply type_check_proof_invariant; [eauto| apply type_check_proof_fixed in H; subst; reflexivity].

  - (* triple_frame *)
    eapply IHHtriple; eauto.
    intros b Hb. apply HP'. apply in_app_or in Hb. apply in_or_app. destruct Hb; auto.

  - (* triple_con_1 *)
    destruct (exec fuel (translate_pexp e) s) eqn:He; [|discriminate].
    inversion Hexec; subst.
    eapply H1; eauto.
    eapply IHHtriple; eauto.
    intros b Hb. apply H0, HP', Hb.

  - (* triple_con_2 *)
    destruct (exec fuel (translate_pexp e) s) eqn:He; [|discriminate].
    inversion Hexec; subst.
    eapply H1; eauto.

  - (* let_c_pf *)
    destruct (exec fuel (Assign (convert_var x) (translate_aexp a)) s) eqn:Hex1; [|discriminate].
    inversion Hexec; subst.
    eapply IHHtriple; eauto.
    intros b Hb.
    destruct (eval (translate_aexp a) s) eqn:Heval; [|discriminate].
    inversion Hex1; subst.
    apply in_app_or in Hb; destruct Hb as [HbW | HbP].
    + apply HP'. apply in_or_app; left; exact HbW.
    + rewrite eval_cbexp_subst with (s := s) (x := convert_var x) (e := translate_aexp a);
        try rewrite Heval; auto.
      apply HP'. apply in_or_app; right; exact HbP.

  - (* let_m_pf *)
    destruct (exec fuel (Assign (convert_var x) (translate_aexp a)) s) eqn:Hex1; [|discriminate].
    inversion Hexec; subst.
    eapply IHHtriple; eauto.
    intros b Hb.
    destruct (eval (translate_aexp a) s) eqn:Heval; [|discriminate].
    inversion Hex1; subst.
    apply in_app_or in Hb as [HbW | HbP].
    + simpl in HbW. destruct HbW as [HbCEq | HbRest].
      * apply eval_ceq with (s := s) (env := env); auto.
      * apply HP'. apply in_or_app; left; exact HbRest.
    + rewrite eval_cbexp_subst with (s := s) (x := convert_var x) (e := translate_aexp a);
        try rewrite Heval; auto.
      apply HP'. apply in_or_app; right; exact HbP.

  - (* let_q_pf *)
    destruct (exec fuel (Assign (convert_var x) (VarExpr (convert_var y))) s) eqn:Hex1; [|discriminate].
    inversion Hexec; subst.
    eapply IHHtriple; eauto.
    intros b Hb.
    destruct (s (convert_var y)) eqn:Heval; [|discriminate].
    inversion Hex1; subst.
    apply in_app_or in Hb as [HbW | HbP].
    + destruct HbW as [HbCEq | HbRest].
      * apply eval_ceq_mnum with (s := s); auto.
      * apply HP'. apply in_or_app; left; exact HbRest.
    + simpl in HbP. destruct HbP as [HbPM | HbRest].
      * apply trans_qpred_simp with (x := x) (n := n) (r' := r') (v' := v') (l := l) (v := v); auto.
        apply HP'. apply in_or_app; right; simpl; left; reflexivity.
      * apply trans_env_stable in HbRest; auto.
        apply HP'. apply in_or_app; right; simpl; right; exact HbRest.

  - (* appu_nor_pf *)
    inversion Hexec; subst. apply HP'; assumption.

  - (* appu_ch_pf *)
    inversion Hexec; subst.
    apply in_app_or in Hb0 as [HbW | HbQ].
    + apply HP'. apply in_or_app; left; exact HbW.
    + rewrite trans_qpred_cval_equiv. apply HP'. apply in_or_app; right; exact HbQ.

  - (* apph_nor_pf | apph_had_pf *)
    inversion Hexec; subst. apply HP'; assumption.

  - (* if_c_t | if_c_f *)
    destruct (eval (translate_bexp b) s) eqn:Heval; [|discriminate].
    destruct (Nat.eqb n 0) eqn:Hcond.
    + inversion Hexec; subst. apply HP'; assumption.
    + destruct (exec fuel (translate_pexp e) s) eqn:He; [|discriminate].
      inversion Hexec; subst.
      eapply IHHtriple; eauto.

  - (* if_q *)
    destruct (eval (translate_bexp b) s) eqn:Heval; [|discriminate].
    destruct (Nat.eqb n 0) eqn:Hcond.
    + inversion Hexec; subst. apply HP'; (* TODO: prove Qa' = Q *) admit.
    + destruct (exec fuel (translate_pexp e) s) eqn:He; [|discriminate].
      inversion Hexec; subst.
      eapply IHHtriple; eauto. (* TODO: prove P'' = P *) admit.

  - (* for_pf_f *)
    destruct (exec fuel (Assign (convert_var x) (Const l)) s) eqn:Hex1; [|discriminate].
    inversion Hexec; subst. apply HP'; assumption.

  - (* for_pf *)
    destruct (exec fuel (Assign (convert_var x) (Const l)) s) eqn:Hex1; [|discriminate].
    destruct (exec fuel
      (While (Minus (Const h) (VarExpr (convert_var x)))
         (If (translate_bexp b)
            (Seq (translate_pexp p)
                 (Assign (convert_var x)
                         (Plus (VarExpr (convert_var x)) (Const 1))))
            Skip)) s0) eqn:Hex2; [|discriminate].
    inversion Hexec; subst.
    (* TODO: use for_invariant lemma to complete *) admit.

  - (* array_assign_pf *)
    destruct (eval (translate_aexp idx) s) eqn:Hidx; [|discriminate].
    destruct (eval (translate_aexp val) s) eqn:Hval; [|discriminate].
    inversion Hexec; subst. apply HP'; assumption.
Qed.
*)
Check trans.
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
    let c := translate_pexp e in
    exec fuel c s = Some s' ->
    let Q' := trans env W' Q in
    (forall b, In b Q' -> eval_cbexp s' b = true).
Proof.
  intros rmax t env T W P e W' Q fuel s s' Htype Htriple.
  revert s s'. 
  induction Htriple; intros s s' HP' Hexec; simpl in *.

  - (* Skip *) 
  (* Apply the induction hypothesis for the original type context T *)
  eapply IHHtriple; eauto.
  (* Use the type_check_proof_invariant lemma to confirm the type context remains T *)
  eapply type_check_proof_invariant; eauto.
    (* Show that the extended type context T' does not affect the original proof *)
    apply type_check_proof_fixed in H; auto.
  - (* Seq *)
  (* Apply the induction hypothesis for the Hoare triple with P' *)
  eapply IHHtriple; eauto.
 (* Show type_check_proof remains valid under P' *)
    eapply type_check_proof_invariant; eauto.
    apply type_check_proof_fixed in H; auto.
  - (* Consequence *)
    eapply IHHtriple; eauto.
    apply type_check_proof_weaken_right with (T1 := T1); auto.
    apply type_check_proof_fixed in H; auto.
  - (* Case: assign_rule *)
intros Hskip.
destruct fuel; simpl in Hskip; try discriminate.
inversion Hskip; subst.

inversion Htype as [[Hcpred Hqpred] Hlocus]; subst.

intros b Hb.
apply Hexec.
  inversion Hskip; subst.
admit.
  - (* triple_frame *)
intros Hseq.
destruct fuel as [| fuel']; simpl in Hseq; try discriminate.
destruct (exec fuel' (Assign (convert_var x) (translate_aexp a)) s) eqn:Hex1; try discriminate.
destruct (exec fuel' (translate_pexp e) s0) eqn:Hex2; try discriminate.
inversion Hseq; subst.
eapply IHHtriple; eauto.
*)



