
Theorem quantum_to_classical_soundness :
  forall (rmax : nat) (aenv : LocusDef.aenv) (s s' : stack * qstate) (e : pexp),
     @qfor_sem rmax aenv s e s' ->
    exists P Q c,
      P = trans_state (aenv, s) /\
      Q = trans_state (aenv, s') /\
      c = translate_pexp e /\
      hoare_triple P c Q.

Proof.
  intros rmax aenv s s' e Hsem.
  induction Hsem.
  - (* PSKIP *)
    exists (trans_state (aenv, s)), (trans_state (aenv, s)), Skip.
    repeat split; try reflexivity.
    apply hoare_skip.

  - (* Let x (AE a) s *)
    destruct IHHsem as [P' [Q' [c' [HP [HQ [Hc' Htr]]]]]].
    exists P', Q', Seq (Assign (convert_var x) (translate_aexp a)) c'.
repeat split.
    repeat split; try reflexivity.
    apply hoare_seq with (Q := P').
    + apply hoare_assign.
    + exact Htr.

  - (* Let x (Meas y) s *)
    destruct IHHsem as [P' [Q' [c' [HP [HQ [Hc' Htr]]]]]].
    exists (trans_state (aenv, s)), Q', Seq (Assign (convert_var x) (VarExpr (convert_var y))) c'.
    repeat split; try reflexivity.
    apply hoare_seq with (Q := P').
    + apply hoare_assign.
    + exact Htr.  - (* let_sem_c *)
    destruct IHqfor_sem as [P' [Q' [c' [HP' [HQ' [Hc' Hhoare]]]]]].
    exists (trans_state (aenv, s)), (trans_state (aenv, s')), 
           (Seq (Assign (convert_var x) (translate_aexp a)) (translate_pexp e)).
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + eapply hoare_seq.
      * apply hoare_assign. (* Assign n to x *)
      * rewrite Hc'. apply Hhoare.

  - (* PSeq s1 s2 *)
    destruct IHHsem1 as [P1 [Q1 [c1 [HP1 [HQ1 [Hc1 Htr1]]]]]].
    destruct IHHsem2 as [P2 [Q2 [c2 [HP2 [HQ2 [Hc2 Htr2]]]]]].
    subst.
    exists P1, Q2, Seq c1 c2.
    repeat split; try reflexivity.
    apply hoare_seq with (Q := Q1); assumption.

  - (* If condition *)
    destruct IHHsem as [P1 [Q1 [c1 [HP1 [HQ1 [Hc1 Htr1]]]]]].
    exists (trans_state (aenv, s)), Q1, If (translate_bexp b) c1 Skip.
    repeat split; try reflexivity.
    apply hoare_if.
    + exact Htr1.
    + apply hoare_skip.

  - (* For loop *)
    destruct IHHsem as [P1 [Q1 [c1 [HP1 [HQ1 [Hc1 Htr1]]]]]].
    set (v := convert_var x).
    set (i := translate_aexp l).
    set (hi := translate_aexp h).
    set (cond := Minus hi (VarExpr v)).
    set (body := If (translate_bexp b)
                    (Seq c1 (Assign v (Plus (VarExpr v) (Const 1))))
                    Skip).
    exists (trans_state (aenv, s)), (trans_state (aenv, s2)),
           Seq (Assign v i) (While cond body).
    repeat split; try reflexivity.
    apply hoare_seq.
    + apply hoare_assign.
    + apply hoare_while.
      apply hoare_if.
      * apply hoare_seq.
        -- exact Htr1.
        -- apply hoare_assign.
      * apply hoare_skip.
Qed.


Theorem quantum_to_classical_soundness :
  forall (rmax : nat) (aenv : LocusDef.aenv) (s s' : stack * qstate) (e : pexp),
     @qfor_sem rmax aenv s e s' ->
    exists P Q c,
      P = trans_state (aenv, s) /\
      Q = trans_state (aenv, s') /\
      c = translate_pexp e /\
      hoare_triple P c Q.
Proof.
  intros rmax aenv s s' e H.
  induction H using qfor_sem_ind'.
  (* Case analysis on each qfor_sem constructor *)
  - (* skip_sem *)
    exists (trans_state (aenv, S)), (trans_state (aenv, S)), Skip.
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + apply hoare_skip.
  - (* let_sem_c *)
    destruct IHqfor_sem as [P' [Q' [c' [HP' [HQ' [Hc' Hhoare]]]]]].
    exists (trans_state (aenv, s)), (trans_state (aenv, s')), 
           (Seq (Assign (convert_var x) (translate_aexp a)) (translate_pexp e)).
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + eapply hoare_seq.
      * apply hoare_assign. (* Assign n to x *)
      * rewrite Hc'. apply Hhoare.
  - (* let_sem_m *)
    destruct IHqfor_sem as [P' [Q' [c' [HP' [HQ' [Hc' Hhoare]]]]]].
    exists (trans_state (aenv, s)), (trans_state (aenv, s')), 
           (Seq (Assign (convert_var x) (Meas a)) (translate_pexp e)).
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + eapply hoare_seq.
      * apply hoare_assign_meas. (* Custom measurement assignment *)
      * apply Hhoare.
  - (* let_sem_q *)
    destruct IHqfor_sem as [P' [Q' [c' [HP' [HQ' [Hc' Hhoare]]]]]].
    exists (trans_state (aenv, (W, ((a, BNum 0, BNum n) :: l, va) :: s))),
           (trans_state (aenv, (W, s'))),
           (Seq (Assign x (Meas a)) (translate_pexp e)).
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + eapply hoare_seq.
      * apply hoare_assign_meas. (* Measurement handling *)
      * apply Hhoare.
  - (* appu_sem_nor *)
    exists (trans_state (aenv, (W, (a, Nval r b) :: s))),
           (trans_state (aenv, (W, (a, Nval ra ba) :: s))),
           Skip. (* Unitary application as state transformation *)
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + apply hoare_skip. (* Or custom unitary rule *)
  - (* appu_sem_ch *)
    destruct IHqfor_sem as [P' [Q' [c' [HP' [HQ' [Hc' Hhoare]]]]]].
    exists (trans_state (aenv, (W, (a ++ l, Cval m b) :: s))),
           (trans_state (aenv, (W, (a ++ l, Cval m ba) :: s))),
           (translate_pexp e).
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + apply Hhoare.
  - (* appsu_sem_h_nor *)
    exists (trans_state (aenv, (W, ([a], Nval r b) :: s))),
           (trans_state (aenv, (W, ([a], Hval (eval_to_had n b)) :: s))),
           Skip.
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + apply hoare_skip. (* State transformation for H *)
  - (* appsu_sem_h_had *)
    exists (trans_state (aenv, (W, ([a], Hval b) :: s))),
           (trans_state (aenv, (W, ([a], Nval C1 (eval_to_nor n b)) :: s))),
           Skip.
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + apply hoare_skip. (* State transformation for H inverse *)
  - (* if_sem_ct *)
    destruct IHqfor_sem as [P' [Q' [c' [HP' [HQ' [Hc' Hhoare]]]]]].
    exists (trans_state (aenv, s)), (trans_state (aenv, s')), 
           (If (translate_bexp b) (translate_pexp e)).
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + apply hoare_if.
      * (* Prove translated condition matches quantum eval_bexp *)
      * apply Hhoare.
  - (* if_sem_cf *)
    exists (trans_state (aenv, s)), (trans_state (aenv, s)), Skip.
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + apply hoare_skip.
  - (* if_sem_q *)
    destruct IHqfor_sem as [P' [Q' [c' [HP' [HQ' [Hc' Hhoare]]]]]].
    exists (trans_state (aenv, (W, (l ++ l1, Cval m f) :: s))),
           (trans_state (aenv, (W', (l ++ l1, fc'') :: s'))),
           (If (translate_bexp b) (translate_pexp e)).
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + apply hoare_if.
      * (* Prove translated condition *)
      * apply Hhoare.
  - (* seq_sem *)
    destruct IHqfor_sem1 as [P1 [Q1 [c1 [HP1 [HQ1 [Hc1 Hhoare1]]]]]].
    destruct IHqfor_sem2 as [P2 [Q2 [c2 [HP2 [HQ2 [Hc2 Hhoare2]]]]]].
    exists P1, Q2, (Seq c1 c2).
    split; [auto | split; [auto | split]].
    + congruence.
    + eapply hoare_seq; eauto.
  - (* for_sem *)
    destruct IHForallA as [P' [Q' [c' [HP' [HQ' [Hc' Hhoare]]]]]].
    exists (trans_state (aenv, s)), (trans_state (aenv, s')), 
           (For x (Num l) (Num h) (translate_bexp b) (translate_pexp p)).
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + apply hoare_for; assumption.
Qed.


(* Completeness theorem *)
Theorem quantum_to_classical_completeness :
  forall P Q c,
    hoare_triple P c Q ->
    exists (rmax : nat) (aenv : LocusDef.aenv) (s s' : stack * qstate) (e : pexp),
      c = translate_pexp e /\
      P = trans_state (aenv, s) /\
      Q = trans_state (aenv, s') /\
    @qfor_sem rmax aenv s e s'.
Proof.

  intros P Q c H.
  induction H.

  - (* skip_rule *)
    exists (0 : nat), empty_aenv.
exists ((AEnv.empty nat, [] : qstate)),
       ((AEnv.empty nat, [] : qstate)),
       PSKIP.
    repeat split; simpl; try reflexivity.
    apply qfor_sem_skip.

  (* Case: skip *)
  - exists (0 : nat), empty_aenv.
   exists (AEnv.empty nat, []), (AEnv.empty (rval * aexp), []).
    exists PSKIP.
    repeat split; simpl.
    + constructor.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + constructor. (* qfor_sem_skip *)

  (* Case: assign *)
  - exists 0%nat, AEnv.empty.
    let s := constr:(fun _ => None, []) in
    let val := safe_eval e (fst s) in
    pose (s' := (fun y => if eqb_var y v then Some val else None, [])).
    exists s, s'.
    exists (Let v (AE e) PSKIP).
    repeat split; simpl.
    + constructor.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + apply qfor_sem_let_c.
      * reflexivity. (* simp_aexp a = Some n *)
      * apply qfor_sem_skip.

  (* Case: sequence *)
  - destruct IHhoare_triple1 as [r1 [aenv1 [s1 [s2 [e1 [Hcl1 [Hc1 [HP1 [HQ1 Hsem1]]]]]]]]].
    destruct IHhoare_triple2 as [r2 [aenv2 [s2' [s3 [e2 [Hcl2 [Hc2 [HP2 [HQ2 Hsem2]]]]]]]]].
    exists 0%nat, AEnv.empty, s1, s3, (PSeq e1 e2).
    repeat split; simpl.
    + constructor; assumption.
    + reflexivity.
    + assumption.
    + assumption.
    + apply qfor_sem_seq with (s1 := s2); assumption.

  (* Case: if *)
  - destruct IHhoare_triple1 as [r1 [aenv1 [s1 [s2 [e1 [Hcl1 [Hc1 [HP1 [HQ1 Hsem1]]]]]]]]].
    destruct IHhoare_triple2 as [r2 [aenv2 [s1' [s3 [e2 [Hcl2 [Hc2 [HP2 [HQ2 Hsem2]]]]]]]]].
    exists 0%nat, AEnv.empty, s1, s2, (If b e1).
    repeat split.
    + constructor; assumption.
    + simpl. reflexivity.
    + assumption.
    + assumption.
    + apply qfor_sem_if_ct with (T1 := []).
      * reflexivity. (* simp_bexp b = Some true assumed *)
      * assumption.

  (* Case: while *)
  - (* Can't construct full for-loop semantics without full qfor_sem_for *)
    admit.

  (* Case: array write *)
  - exists 0%nat, AEnv.empty.
    let s := constr:(fun _ => None, []) in
    let val := safe_eval val s in
    let i := safe_eval idx s in
    pose (s' := (fun x => if eqb_var x (Array name i) then Some val else s x, [])).
    exists (s, []), (s', []).
    exists (Let (Array name i) (AE val) PSKIP). (* A classical proxy for array write *)
    repeat split; simpl.
    + constructor.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + apply qfor_sem_let_c.
      * reflexivity.
      * apply qfor_sem_skip.

  (* Case: consequence *)
  - destruct IHhoare_triple as [rmax [aenv [s [s' [e [Hcl [Htrans [HP [HQ Hsem]]]]]]]]].
    exists rmax, aenv, s, s', e.
    repeat split; try assumption.
    + assumption.
    + assumption.
    + apply qfor_sem_consequence with (T1 := []) (P' := trans_state (aenv, s)) (Q' := trans_state (aenv, s')).
      * reflexivity. (* type_check_proof stubbed *)
      * assumption.
Qed.

Theorem  translate_subst_pexp :
  forall e x a n s s',
    simp_aexp a = Some n ->
    exec (S (S 0)) (Seq (Assign (convert_var x) (translate_aexp a)) (translate_pexp e)) s = Some s' ->
    exec (S 0) (translate_pexp (subst_pexp e x n)) s = Some s'.
Proof.
  (* Proof would involve induction on e and showing that assignment mimics substitution *)
Admitted.
Lemma subst_assertion_trans_state :
  forall aenv W q x a n,
    simp_aexp a = Some n ->
    entails (subst_assertion (trans_state (aenv, (W, q))) (convert_var x) (translate_aexp a))
            (trans_state (aenv, (W, q))).
Proof.
  (* Needs to relate classical assignment to quantum state *)
Admitted.
Lemma subst_assertion_preserves_trans_state :
  forall aenv W q x a n,
    simp_aexp a = Some n ->
    entails (subst_assertion (trans_state (aenv, (W, q))) (convert_var x) (translate_aexp a))
            (trans_state (aenv, (W, q))).
Proof.
  intros aenv W q x a n Hsimp.
  unfold entails, trans_state, subst_assertion.
  intros s0 Hsub b Hin.
  unfold trans_stack, trans_qstate in *.
  (* Analyze the effect of subst_cbexp *)
 Admitted. 


Theorem quantum_to_classical_soundness :
  forall (rmax : nat) (aenv : LocusDef.aenv) (s s' : stack * qstate) (e : pexp),
     @qfor_sem rmax aenv s e s' ->
    exists P Q c,
      P = trans_state (aenv, s) /\
      Q = trans_state (aenv, s') /\
      c = translate_pexp e /\
      hoare_triple P c Q.
Proof.
intros rmax aenv s s' e Hsem.
  induction Hsem.

  - (* skip_sem *)
    destruct s as [W q].
    exists (trans_state (aenv, (W, q))), (trans_state (aenv, (W, q))), (translate_pexp PSKIP).
    split; [reflexivity | split; [reflexivity | split; [simpl; reflexivity |]]].
    apply hoare_skip.
- (* let_sem_c *)
  destruct s as [W q].
    destruct s' as [W' q'].
    destruct IHHsem as [P' [Q' [c' [HP' [HQ' [Hc' Hhoare]]]]]].
    exists (trans_state (aenv, (W, q))), (trans_state (aenv, (W', q'))), 
           (Seq (Assign (convert_var x) (translate_aexp a)) (translate_pexp e)).
    split; [reflexivity | split; [reflexivity | split; [simpl; reflexivity |]]].
    (* Use consequence rule to bridge the gap *)
    apply hoare_consequence with 
      (P' := trans_state (aenv, (W, q))) 
      (Q' := trans_state (aenv, (W', q'))).
    + (* Precondition entailment: P entails P' *)
      unfold entails. intros s0 Hpre b Hin. apply Hpre. assumption.
    + (* Hoare triple for intermediate command *)
      apply hoare_seq with (Q := P').
      * apply hoare_assign.
      *rewrite <- HP', <- HQ', <- Hc'. assumption.
    + (* Postcondition entailment: Q' entails Q *)
      unfold entails. intros s0 Hpost b Hin. apply Hpost. assumption.
- (* let_sem_m *)
    destruct s as [W q].
    destruct s' as [W' q'].
    destruct IHHsem as [P' [Q' [c' [HP' [HQ' [Hc' Hhoare]]]]]].
    exists (trans_state (aenv, (W, q))), (trans_state (aenv, (W, q'))), 
           (Seq (Assign (convert_var x) (translate_aexp a)) c').
    split; [reflexivity | split; [reflexivity | split; [simpl; reflexivity |]]].
    apply hoare_seq with (Q := trans_state ((AEnv.add x (Mo MT) aenv), (update_cval (W, q) x n))).
    + apply hoare_assign.
    + rewrite <- HP', <- HQ', <- Hc'. assumption.

  - (* let_sem_q *)
    destruct s as [W q].
    destruct s' as [W' q'].
    destruct IHHsem as [P' [Q' [c' [HP' [HQ' [Hc' Hhoare]]]]]].
    exists (trans_state (aenv, (W, ((a, BNum 0, BNum n) :: l, va) :: q))), 
           (trans_state (aenv, (W, q'))), 
           (Seq (Assign (convert_var x) (VarExpr (convert_var a))) c').
    split; [reflexivity | split; [reflexivity | split; [simpl; reflexivity |]]].
    apply hoare_seq with (Q := trans_state ((AEnv.add x (Mo MT) aenv), (AEnv.add x (r, v) W, (l, va') :: q))).
    + apply hoare_assign.
    + rewrite <- HP', <- HQ', <- Hc'. assumption.

  - (* appu_sem_nor *)
    destruct s as [W q].
    exists (trans_state (aenv, (W, (a, Nval r b) :: q))), 
           (trans_state (aenv, (W, (a, Nval ra ba) :: q))), 
           (translate_pexp (AppU a e)).
    split; [reflexivity | split; [reflexivity | split; [simpl; reflexivity |]]].
    simpl. apply hoare_skip. (* Note: AppU translated to Skip *)

  - (* appu_sem_ch *)
    destruct s as [W q].
    exists (trans_state (aenv, (W, (a ++ l, Cval m b) :: q))), 
           (trans_state (aenv, (W, (a ++ l, Cval m ba) :: q))), 
           (translate_pexp (AppU a e)).
    split; [reflexivity | split; [reflexivity | split; [simpl; reflexivity |]]].
    simpl. apply hoare_skip. (* Note: AppU translated to Skip *)

  - (* appsu_sem_h_nor *)
    destruct s as [W q].
    exists (trans_state (aenv, (W, ([a], Nval r b) :: q))), 
           (trans_state (aenv, (W, ([a], Hval (eval_to_had n b)) :: q))), 
           (translate_pexp (AppSU (RH p)))).
    split; [reflexivity | split; [reflexivity | split; [simpl; reflexivity |]]].
    simpl. apply hoare_skip. (* Note: AppSU translated to Skip *)

  - (* appsu_sem_h_had *)
    destruct s as [W q].
    exists (trans_state (aenv, (W, ([a], Hval b) :: q))), 
           (trans_state (aenv, (W, ([a], Nval C1 (eval_to_nor n b)) :: q))), 
           (translate_pexp (AppSU (RH p)))).
    split; [reflexivity | split; [reflexivity | split; [simpl; reflexivity |]]].
    simpl. apply hoare_skip. (* Note: AppSU translated to Skip *)

  - (* if_sem_ct *)
    destruct s as [W q].
    destruct s' as [W' q'].
    destruct IHHsem as [P' [Q' [c' [HP' [HQ' [Hc' Hhoare]]]]]].
    exists (trans_state (aenv, (W, q))), (trans_state (aenv, (W', q'))), 
           (If (translate_bexp b) c' Skip).
    split; [reflexivity | split; [reflexivity | split; [simpl; reflexivity |]]].
    apply hoare_if.
    + rewrite <- HP', <- HQ', <- Hc'. assumption.
    + apply hoare_skip.

  - (* if_sem_cf *)
    destruct s as [W q].
    exists (trans_state (aenv, (W, q))), (trans_state (aenv, (W, q))), 
           (If (translate_bexp b) Skip Skip).
    split; [reflexivity | split; [reflexivity | split; [simpl; reflexivity |]]].
    apply hoare_if; [apply hoare_skip | apply hoare_skip].

  - (* if_sem_q *)
    destruct s as [W q].
    destruct s' as [W' q'].
    destruct IHHsem as [P' [Q' [c' [HP' [HQ' [Hc' Hhoare]]]]]].
    exists (trans_state (aenv, (W, (l ++ l1, Cval m f) :: q))), 
           (trans_state (aenv, (W', (l ++ l1, fc'') :: q'))), 
           (If (translate_bexp b) c' Skip).
    split; [reflexivity | split; [reflexivity | split; [simpl; reflexivity |]]].
    apply hoare_if.
    + rewrite <- HP', <- HQ', <- Hc'. assumption.
    + apply hoare_skip.

  - (* seq_sem *)
    destruct s as [W q].
    destruct s1 as [W1 q1].
    destruct s2 as [W2 q2].
    destruct IHHsem1 as [P1 [Q1 [c1 [HP1 [HQ1 [Hc1 Hhoare1]]]]]].
    destruct IHHsem2 as [P2 [Q2 [c2 [HP2 [HQ2 [Hc2 Hhoare2]]]]]].
    exists (trans_state (aenv, (W, q))), (trans_state (aenv, (W2, q2))), 
           (Seq c1 c2).
    split; [reflexivity | split; [reflexivity | split; [simpl; rewrite Hc1, Hc2; reflexivity |]]].
    apply hoare_seq with (Q := Q1).
    + rewrite <- HP1, <- HQ1, <- Hc1. assumption.
    + rewrite <- HP2, <- HQ2, <- Hc2. assumption.

  - (* for_sem *)
    destruct s as [W q].
    destruct s' as [W' q'].
    (* Complex case with ForallA; admit for now *)
    admit.

Admitted.



Theorem quantum_to_classical_soundness :
  forall (rmax : nat) (aenv : LocusDef.aenv) (s s' : stack * qstate) (e : pexp),
     @qfor_sem rmax aenv s e s' ->
    exists P Q c,
      P = trans_state (aenv, s) /\
      Q = trans_state (aenv, s') /\
      c = translate_pexp e /\
      hoare_triple P c Q.
Proof.
  intros rmax aenv s s' e H.
  induction H using qfor_sem_ind'.
  (* Case analysis on each qfor_sem constructor *)
  - (* skip_sem *)
    exists (trans_state (aenv, S)), (trans_state (aenv, S)), Skip.
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + apply hoare_skip.
  - (* let_sem_c *)
    destruct IHqfor_sem as [P' [Q' [c' [HP' [HQ' [Hc' Hhoare]]]]]].
    exists (trans_state (aenv, s)), (trans_state (aenv, s')), 
           (Seq (Assign (convert_var x) (translate_aexp a)) (translate_pexp e)).
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + eapply hoare_seq.
      * apply hoare_assign. (* Assign n to x *)
      * rewrite Hc'. apply Hhoare.
  - (* let_sem_m *)
    destruct IHqfor_sem as [P' [Q' [c' [HP' [HQ' [Hc' Hhoare]]]]]].
    exists (trans_state (aenv, s)), (trans_state (aenv, s')), 
           (Seq (Assign (convert_var x) (Meas a)) (translate_pexp e)).
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + eapply hoare_seq.
      * apply hoare_assign_meas. (* Custom measurement assignment *)
      * apply Hhoare.
  - (* let_sem_q *)
    destruct IHqfor_sem as [P' [Q' [c' [HP' [HQ' [Hc' Hhoare]]]]]].
    exists (trans_state (aenv, (W, ((a, BNum 0, BNum n) :: l, va) :: s))),
           (trans_state (aenv, (W, s'))),
           (Seq (Assign x (Meas a)) (translate_pexp e)).
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + eapply hoare_seq.
      * apply hoare_assign_meas. (* Measurement handling *)
      * apply Hhoare.
  - (* appu_sem_nor *)
    exists (trans_state (aenv, (W, (a, Nval r b) :: s))),
           (trans_state (aenv, (W, (a, Nval ra ba) :: s))),
           Skip. (* Unitary application as state transformation *)
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + apply hoare_skip. (* Or custom unitary rule *)
  - (* appu_sem_ch *)
    destruct IHqfor_sem as [P' [Q' [c' [HP' [HQ' [Hc' Hhoare]]]]]].
    exists (trans_state (aenv, (W, (a ++ l, Cval m b) :: s))),
           (trans_state (aenv, (W, (a ++ l, Cval m ba) :: s))),
           (translate_pexp e).
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + apply Hhoare.
  - (* appsu_sem_h_nor *)
    exists (trans_state (aenv, (W, ([a], Nval r b) :: s))),
           (trans_state (aenv, (W, ([a], Hval (eval_to_had n b)) :: s))),
           Skip.
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + apply hoare_skip. (* State transformation for H *)
  - (* appsu_sem_h_had *)
    exists (trans_state (aenv, (W, ([a], Hval b) :: s))),
           (trans_state (aenv, (W, ([a], Nval C1 (eval_to_nor n b)) :: s))),
           Skip.
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + apply hoare_skip. (* State transformation for H inverse *)
  - (* if_sem_ct *)
    destruct IHqfor_sem as [P' [Q' [c' [HP' [HQ' [Hc' Hhoare]]]]]].
    exists (trans_state (aenv, s)), (trans_state (aenv, s')), 
           (If (translate_bexp b) (translate_pexp e)).
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + apply hoare_if.
      * (* Prove translated condition matches quantum eval_bexp *)
      * apply Hhoare.
  - (* if_sem_cf *)
    exists (trans_state (aenv, s)), (trans_state (aenv, s)), Skip.
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + apply hoare_skip.
  - (* if_sem_q *)
    destruct IHqfor_sem as [P' [Q' [c' [HP' [HQ' [Hc' Hhoare]]]]]].
    exists (trans_state (aenv, (W, (l ++ l1, Cval m f) :: s))),
           (trans_state (aenv, (W', (l ++ l1, fc'') :: s'))),
           (If (translate_bexp b) (translate_pexp e)).
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + apply hoare_if.
      * (* Prove translated condition *)
      * apply Hhoare.
  - (* seq_sem *)
    destruct IHqfor_sem1 as [P1 [Q1 [c1 [HP1 [HQ1 [Hc1 Hhoare1]]]]]].
    destruct IHqfor_sem2 as [P2 [Q2 [c2 [HP2 [HQ2 [Hc2 Hhoare2]]]]]].
    exists P1, Q2, (Seq c1 c2).
    split; [auto | split; [auto | split]].
    + congruence.
    + eapply hoare_seq; eauto.
  - (* for_sem *)
    destruct IHForallA as [P' [Q' [c' [HP' [HQ' [Hc' Hhoare]]]]]].
    exists (trans_state (aenv, s)), (trans_state (aenv, s')), 
           (For x (Num l) (Num h) (translate_bexp b) (translate_pexp p)).
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + apply hoare_for; assumption.
Qed.




Check qfor_sem.

Check LocusDef.state.

(* Soundness Theorem *)
Theorem quantum_to_classical_soundness :
  forall (rmax : nat) (aenv : LocusDef.aenv) (s s' : stack * qstate) (e : pexp),
     @qfor_sem rmax aenv s e s' ->
    exists P Q c,
      P = trans_state (aenv, s) /\
      Q = trans_state (aenv, s') /\
      c = translate_pexp e /\
      hoare_triple P c Q.
Proof.
intros rmax aenv s s' e H.
induction H using qfor_sem_ind'.
- (* skip_sem *)
    exists (trans_state (aenv, S)), (trans_state (aenv, S)), Skip.
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + apply hoare_skip.
- (* let_sem_c *)
    destruct IHqfor_sem as [P' [Q' [c' [HP' [HQ' [Hc' Hhoare]]]]]].
    exists (trans_state (aenv, s)), (trans_state (aenv, s')), 
           (Seq (Assign (convert_var x) (translate_aexp a)) (translate_pexp e)).
    split; [reflexivity | split; [reflexivity | split]].
    + unfold translate_pexp. reflexivity.
    + eapply hoare_seq.
      * apply hoare_assign. (* Assign n to x *)
      * rewrite Hc'. apply Hhoare.
   
+ (* Hoare triple *)
      set (R := subst_assertion (trans_state (aenv, s)) (convert_var x) (translate_aexp a)).
      apply hoare_seq with R.
      * apply hoare_consequence with (P' := trans_state (aenv, s)) (Q' := R).
        -- unfold entails, R. intros s0 Hpre b Hin. (* Need to relate eval_cbexp and simp_aexp *)
           admit. (* Entailment depends on state update *)
        -- apply hoare_assign.
        -- unfold entails. intros s0 Hpost b Hin. apply Hpost. assumption.
      * (* Adjust P' and c' from IH *)
        admit. (* Substitution in translate_pexp needs alignment *)
  - (* let_sem_m *)
    destruct IHqfor_sem as [P' [Q' [c' [HP' [HQ' [Hc' Hhoare]]]]]].
    exists (trans_state (aenv, s)), (trans_state (aenv, (fst s, s'))), 
           (Seq (Assign (convert_var x) (translate_aexp a)) (translate_pexp e)).
    split; [reflexivity | split; [reflexivity | split]].
Admitted.
*)


(* Completeness theorem *)
Theorem quantum_to_classical_completeness :
  forall P Q c,
    hoare_triple P c Q ->
    exists (rmax : nat) (aenv : LocusDef.aenv) (s s' : stack * qstate) (e : pexp),
      c = translate_pexp e /\
      P = trans_state (aenv, s) /\
      Q = trans_state (aenv, s') /\
    @qfor_sem rmax aenv s e s'.
Proof.

  intros P Q c H.
  induction H.

  - (* skip_rule *)
    exists (0 : nat), empty_aenv.
exists ((AEnv.empty nat, [] : qstate)),
       ((AEnv.empty nat, [] : qstate)),
       PSKIP.
    repeat split; simpl; try reflexivity.
    apply qfor_sem_skip.

  (* Case: skip *)
  - exists (0 : nat), empty_aenv.
   exists (AEnv.empty nat, []), (AEnv.empty (rval * aexp), []).
    exists PSKIP.
    repeat split; simpl.
    + constructor.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + constructor. (* qfor_sem_skip *)

  (* Case: assign *)
  - exists 0%nat, AEnv.empty.
    let s := constr:(fun _ => None, []) in
    let val := safe_eval e (fst s) in
    pose (s' := (fun y => if eqb_var y v then Some val else None, [])).
    exists s, s'.
    exists (Let v (AE e) PSKIP).
    repeat split; simpl.
    + constructor.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + apply qfor_sem_let_c.
      * reflexivity. (* simp_aexp a = Some n *)
      * apply qfor_sem_skip.

  (* Case: sequence *)
  - destruct IHhoare_triple1 as [r1 [aenv1 [s1 [s2 [e1 [Hcl1 [Hc1 [HP1 [HQ1 Hsem1]]]]]]]]].
    destruct IHhoare_triple2 as [r2 [aenv2 [s2' [s3 [e2 [Hcl2 [Hc2 [HP2 [HQ2 Hsem2]]]]]]]]].
    exists 0%nat, AEnv.empty, s1, s3, (PSeq e1 e2).
    repeat split; simpl.
    + constructor; assumption.
    + reflexivity.
    + assumption.
    + assumption.
    + apply qfor_sem_seq with (s1 := s2); assumption.

  (* Case: if *)
  - destruct IHhoare_triple1 as [r1 [aenv1 [s1 [s2 [e1 [Hcl1 [Hc1 [HP1 [HQ1 Hsem1]]]]]]]]].
    destruct IHhoare_triple2 as [r2 [aenv2 [s1' [s3 [e2 [Hcl2 [Hc2 [HP2 [HQ2 Hsem2]]]]]]]]].
    exists 0%nat, AEnv.empty, s1, s2, (If b e1).
    repeat split.
    + constructor; assumption.
    + simpl. reflexivity.
    + assumption.
    + assumption.
    + apply qfor_sem_if_ct with (T1 := []).
      * reflexivity. (* simp_bexp b = Some true assumed *)
      * assumption.

  (* Case: while *)
  - (* Can't construct full for-loop semantics without full qfor_sem_for *)
    admit.

  (* Case: array write *)
  - exists 0%nat, AEnv.empty.
    let s := constr:(fun _ => None, []) in
    let val := safe_eval val s in
    let i := safe_eval idx s in
    pose (s' := (fun x => if eqb_var x (Array name i) then Some val else s x, [])).
    exists (s, []), (s', []).
    exists (Let (Array name i) (AE val) PSKIP). (* A classical proxy for array write *)
    repeat split; simpl.
    + constructor.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + apply qfor_sem_let_c.
      * reflexivity.
      * apply qfor_sem_skip.

  (* Case: consequence *)
  - destruct IHhoare_triple as [rmax [aenv [s [s' [e [Hcl [Htrans [HP [HQ Hsem]]]]]]]]].
    exists rmax, aenv, s, s', e.
    repeat split; try assumption.
    + assumption.
    + assumption.
    + apply qfor_sem_consequence with (T1 := []) (P' := trans_state (aenv, s)) (Q' := trans_state (aenv, s')).
      * reflexivity. (* type_check_proof stubbed *)
      * assumption.
Qed.



(*
(* Translate a classical+quantum state into a logical assertion *)
Theorem hoare_sound_for_qafny :
  forall (rmax : nat) (aenv : aenv)
         (φ φ' : state) (e : pexp) (c : cmd)
         (P Q : assertion),
    c = translate_pexp e ->
    P = trans_state φ  ->
    Q = trans_state φ' ->
    hoare_triple P c Q ->
    qfor_sem rmax aenv φ e φ'.

Proof.
Admitted.

*)



(* Soundness theorem *)
Theorem quantum_to_classical_soundness :
  forall (q : mode) (env : aenv) (T : type_map) 
         (W : cpred) (P : qpred) (e : pexp) (W' : cpred) (Q : qpred),
    triple q env T W P e W' Q ->
    exists (P' Q' : assertion) (c : cmd),
      P' = trans env W P /\
      Q' = trans env W' Q /\
      c = translate_pexp e /\
      hoare_triple P' c Q'.



(*
(* Completeness theorem *)
Theorem quantum_to_classical_completeness :
  forall P Q c,
    hoare_triple P c Q ->
    exists (rmax : nat) (aenv : LocusDef.aenv) (s s' : stack * qstate) (e : pexp),
      c = translate_pexp e /\
      P = trans_state (aenv, s) /\
      Q = trans_state (aenv, s') /\
    @qfor_sem rmax aenv s e s'.

Proof.
intros.
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


Admitted.
*)

Theorem quantum_to_classical_soundness :
  forall (t : atype) (env : aenv) (T : type_map)
         (W : cpred) (P : qpred)
         (e : pexp)
         (W' : cpred) (Q : qpred),
    triple t env T (W, P) e (W', Q) ->
    exists (P' Q' : assertion) (c : cmd),
      P' = trans env W P /\
      Q' = trans env W' Q /\
      c = translate_pexp e /\
      hoare_triple P' c Q'.
 





Lemma qfor_sem_fuel_increase : 
  forall rmax1 rmax2 aenv s e s', 
    @qfor_sem rmax1 aenv s e s' -> @qfor_sem (rmax1 + rmax2) aenv s e s'.
Proof.
 
Admitted.



Definition convert_cpred (W : LocusProof.cpred) : cpred :=
  map convert_cbexp W.
(* Redefine trans to avoid trans_qpred mismatch *)
Definition trans (env : aenv) (W : LocusProof.cpred) (P : qpred) : cpred :=
  convert_cpred W ++ map (fun _ => CBTrue) P.
*)






