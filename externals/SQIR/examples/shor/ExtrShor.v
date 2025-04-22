Require Import Shor NumTheory.
Require Import AltGateSet.

(* Redefining Shor's alg. using the new gate set *)

Fixpoint controlled_rotations n : ucom U :=
  match n with
  | 0 | 1 => SKIP
  | 2     => CU1 (R2 * PI / R2 ^ n) 1 0
  | S n'  => controlled_rotations n' >> CU1 (R2 * PI / R2 ^ n) n' 0
  end.

Fixpoint QFT n : ucom U :=
  match n with
  | 0    => SKIP
  | 1    => H 0
  | S n' => H 0 >> controlled_rotations n >> map_qubits S (QFT n')
  end.

Fixpoint reverse_qubits' dim n : ucom U :=
  match n with
  | 0    => SKIP
  | 1    => SWAP 0 (dim - 1)
  | S n' => reverse_qubits' dim n' >> SWAP n' (dim - n' - 1)
  end.
Definition reverse_qubits n := reverse_qubits' n (n/2)%nat.
Definition QFT_w_reverse n := QFT n >> reverse_qubits n.

Fixpoint bc2ucom (bc : bccom) : ucom U :=
  match bc with
  | bcskip => SKIP
  | bcx a => X a
  | bcswap a b => SWAP a b
  | bccont a bc1 => control a (bc2ucom bc1)
  | bcseq bc1 bc2 => (bc2ucom bc1) >> (bc2ucom bc2)
  end.

Fixpoint controlled_powers' (f : nat -> bccom) k kmax : bccom :=
  match k with
  | O    => bcskip
  | S O  => bygatectrl (kmax - 1) (f O)
  | S k' => bcseq (controlled_powers' f k' kmax)
                 (bygatectrl (kmax - k' - 1) (f k'))
  end.
Definition controlled_powers (f : nat -> bccom) k : ucom U := 
  bc2ucom (controlled_powers' f k k).

Definition QPE k (f : nat -> bccom) : ucom U :=
  npar k U_H >>
  controlled_powers (fun x => map_bccom (fun q => k + q)%nat (f x)) k >>
  invert (QFT_w_reverse k).

Definition modexp a x N := a ^ x mod N.
Definition modmult_circuit a ainv N n i := 
  RCIR.bcelim (ModMult.modmult_rev N (modexp a (2 ^ i) N) (modexp ainv (2 ^ i) N) n).

(* requires 0 < a < N, gcd a N = 1 *)
Definition shor_circuit a N := 
  let m := Nat.log2 (2 * N^2)%nat in
  let n := Nat.log2 (2 * N) in
  let ainv := modinv a N in
  let f i := modmult_circuit a ainv N n i in
  X (m + n - 1) >> QPE m f.

(* shor_circuit uses:
   - Nat.log2 (2 * N^2) qubits as input to QFT
   - Nat.log2 (2 * N) qubits as data in modular exponentiation
   - modmult_rev_anc (Nat.log2 (2 * N)) qubits as ancilla in modular exponentiation 

   The values of the first Nat.log2 (2 * N^2) qubits are inspected at the end
   of the circuit. *)
Definition shor_output_nqs (N : nat) : nat := Nat.log2 (2 * N^2).
Definition modmult_data_nqs (N : nat) : nat := Nat.log2 (2 * N).
Definition modmult_anc_nqs (N : nat) : nat := modmult_rev_anc (Nat.log2 (2 * N)).
Definition modmult_nqs (N : nat) : nat := modmult_data_nqs N + modmult_anc_nqs N.
Definition shor_nqs (N : nat) : nat := shor_output_nqs N + modmult_nqs N.


(** Proofs **)

Lemma controlled_rotations_WF : forall n, well_formed (controlled_rotations n).
Proof.
  destruct n.
  constructor; auto.
  destruct n.
  constructor; auto.
  induction n. 
  constructor; auto.
  constructor. apply IHn.
  constructor; auto. 
Qed.

Local Transparent SQIR.Rz SQIR.CNOT.
Lemma controlled_rotations_WT : forall n, (n > 0)%nat ->
  uc_well_typed (to_base_ucom n (controlled_rotations n)).
Proof.
  intros n Hn.
  destruct n; try lia.
  clear Hn.
  destruct n. constructor. lia.
  induction n. repeat constructor; lia.
  replace (controlled_rotations (S (S (S n)))) 
    with (controlled_rotations (S (S n)) >> 
          CU1 (2 * PI / 2 ^ (S (S (S n)))) (S (S n)) 0) 
    by reflexivity.
  remember (S (S n)) as n'.
  replace (to_base_ucom (S n') (controlled_rotations n' >> 
           CU1 (2 * PI / 2 ^ S n') n' 0))
    with (to_base_ucom (S n') (controlled_rotations n') ;
          to_base_ucom (S n') (CU1 (2 * PI / 2 ^ S n') n' 0))%ucom
    by reflexivity.
  constructor.
  eapply change_dim_WT; try apply IHn.
  lia.
  apply controlled_rotations_WF.
  repeat constructor; lia. 
Qed.
Local Opaque SQIR.Rz SQIR.CNOT.

Lemma controlled_rotations_same : forall n,
  uc_eval n (controlled_rotations n) = 
    UnitarySem.uc_eval (QPE.controlled_rotations n).
Proof.
  destruct n; try reflexivity.
  destruct n; try reflexivity.
  induction n; try reflexivity.
  replace (controlled_rotations (S (S (S n)))) 
    with (controlled_rotations (S (S n)) >> 
          CU1 (2 * PI / 2 ^ (S (S (S n)))) (S (S n)) 0) 
    by reflexivity.
  replace (QPE.controlled_rotations (S (S (S n))))
    with (cast (QPE.controlled_rotations (S (S n))) (S (S (S n))); 
            UnitaryOps.control (S (S n)) (Rz (2 * PI / 2 ^ (S (S (S n)))) 0))%ucom
    by reflexivity.
  remember (S (S n)) as n'.
  replace (S n') with (n' + 1)%nat by lia.
  erewrite change_dim.
  unfold uc_eval in *.
  simpl.
  rewrite <- (pad_dims_r (to_base_ucom _ _)).
  rewrite <- (pad_dims_r (QPE.controlled_rotations _)).
  rewrite IHn.
  reflexivity.
  apply QPE.controlled_rotations_WT.
  lia.
  apply controlled_rotations_WT.
  lia.
Qed.

Local Opaque controlled_rotations.
Lemma QFT_WF : forall n, well_formed (QFT n).
Proof.
  destruct n.
  constructor; auto.
  induction n.
  constructor; auto.
  simpl.
  constructor.
  constructor.
  constructor; auto.
  apply controlled_rotations_WF.
  apply map_qubits_WF.
  apply IHn.
Qed.

Lemma QFT_same : forall n,
  uc_eval n (QFT n) = UnitarySem.uc_eval (QPE.QFT n).
Proof.
  destruct n; try reflexivity.
  induction n; try reflexivity.
  replace (QFT (S (S n))) 
    with (H 0 >> controlled_rotations (S (S n)) >> map_qubits S (QFT (S n))) 
    by reflexivity.
  replace (QPE.QFT (S (S n))) 
    with (SQIR.H 0 ; QPE.controlled_rotations (S (S n)) ; 
          cast (UnitaryOps.map_qubits S (QPE.QFT (S n))) (S (S n)))%ucom 
    by reflexivity. 
  Local Opaque H controlled_rotations QFT QPE.controlled_rotations QPE.QFT.
  erewrite change_dim.
  simpl.
  apply f_equal2; [ | apply f_equal2]; try reflexivity.
  rewrite map_qubits_same.
  specialize (pad_dims_l (to_base_ucom (S n) (QFT (S n))) (S O)) as aux.
  simpl in aux. 
  replace (fun q : nat => S q) with S in aux by reflexivity.
  rewrite <- aux; clear aux. 
  specialize (pad_dims_l (QPE.QFT (S n)) (S O)) as aux.
  simpl in aux. 
  replace (fun q : nat => S q) with S in aux by reflexivity.
  rewrite <- aux; clear aux. 
  rewrite <- IHn. 
  reflexivity.
  apply QFT_WF.
  rewrite <- change_dim.
  apply controlled_rotations_same.
Qed.

Lemma reverse_qubits_same : forall n,
  uc_eval n (reverse_qubits n) = UnitarySem.uc_eval (QPE.reverse_qubits n).
Proof.
  assert (H : forall n dim, uc_eval dim (reverse_qubits' dim n) = 
                         UnitarySem.uc_eval (QPE.reverse_qubits' dim n)).
  { intros n dim.
    destruct n; try reflexivity.
    induction n; try reflexivity.
    unfold uc_eval in *.
    simpl in *.
    rewrite IHn.
    reflexivity. }
  intro n.
  unfold reverse_qubits.
  apply H.
Qed.

Lemma reverse_qubits_WF : forall n, well_formed (reverse_qubits n).
Proof.
  assert (H : forall n dim, well_formed (reverse_qubits' dim n)).
  { intros n dim.
    destruct n.
    constructor; auto.
    induction n.
    constructor; auto.
    simpl. constructor. 
    apply IHn.
    constructor; auto. }
  intro. apply H.
Qed.

Lemma QFT_w_reverse_same : forall n,
  uc_eval n (QFT_w_reverse n) = UnitarySem.uc_eval (QPE.QFT_w_reverse n).
Proof.
  intro n.
  unfold uc_eval; simpl.
  rewrite <- QFT_same, <- reverse_qubits_same.
  reflexivity.
Qed.

Lemma QFT_w_reverse_WF : forall n, well_formed (QFT_w_reverse n).
Proof. constructor. apply QFT_WF. apply reverse_qubits_WF. Qed.

Lemma bc2ucom_WF : forall bc, well_formed (bc2ucom bc).
Proof.
  induction bc; repeat constructor; auto.
  simpl. unfold control. apply control'_WF.
  assumption.
Qed.

Lemma bc2ucom_fresh : forall dim q bc,
  is_fresh q (to_base_ucom dim (bc2ucom bc)) <->
  @is_fresh _ dim q (RCIR.bc2ucom bc).
Proof.
  intros dim q bc.
  induction bc; try reflexivity.
  simpl.
  destruct bc; try reflexivity.
  rewrite <- UnitaryOps.fresh_control.
  unfold control.
  rewrite <- fresh_control'.
  rewrite IHbc.
  reflexivity.
  lia.
  apply bc2ucom_WF.
  rewrite <- UnitaryOps.fresh_control.
  unfold control.
  rewrite <- fresh_control'.
  rewrite IHbc.
  reflexivity.
  lia.
  apply bc2ucom_WF.
  split; intro H; inversion H; subst; simpl.
  constructor.
  apply IHbc1; auto.
  apply IHbc2; auto.
  constructor.
  apply IHbc1; auto.
  apply IHbc2; auto.
Qed.

Lemma bc2ucom_correct : forall dim (bc : bccom),
  uc_eval dim (bc2ucom bc) = UnitarySem.uc_eval (RCIR.bc2ucom bc).
Proof.
  intros dim bc.
  induction bc; try reflexivity.
  simpl.
  rewrite control_correct.
  destruct bc; try reflexivity.
  apply control_ucom_X.
  apply UnitaryOps.control_cong.
  apply IHbc.
  apply bc2ucom_fresh. 
  apply UnitaryOps.control_cong.
  apply IHbc.
  apply bc2ucom_fresh. 
  apply bc2ucom_WF. 
  unfold uc_eval in *. simpl.
  rewrite IHbc1, IHbc2.
  reflexivity.  
Qed.

Local Transparent SQIR.X SQIR.CNOT SQIR.SWAP SQIR.U1.
Lemma bcfresh_is_fresh : forall {dim} q bc,
    bcfresh q bc -> @is_fresh _ dim q (to_base_ucom dim (bc2ucom bc)).
Proof.
  intros dim q bc Hfr. 
  induction bc; simpl; inversion Hfr; repeat constructor; auto.
  unfold control.
  apply fresh_control'. lia.
  apply bc2ucom_WF.
  split; auto.
Qed.
Local Opaque SQIR.X SQIR.CNOT SQIR.SWAP SQIR.U1.

Lemma uc_eval_bygatectrl_correct :
  forall c n dim, @uc_eval dim (bc2ucom (bygatectrl n c)) = @uc_eval dim (control n (bc2ucom c)).
Proof.
  induction c; intros;
    try (simpl; easy).
  rewrite bc2ucom_correct.
  simpl. do 2 rewrite <- bc2ucom_correct. rewrite IHc1, IHc2.
  repeat (rewrite control_correct by apply bc2ucom_WF; simpl).
  rewrite control_correct. simpl. easy.
  constructor; apply bc2ucom_WF.
Qed.

Lemma controlled_powers_same : forall n (f : nat -> bccom) k (f' : nat -> base_ucom n),
  (k > 0)%nat ->
  (forall i, uc_eval (k + n) (bc2ucom (f i)) = UnitarySem.uc_eval (cast (f' i) (k + n))) ->
  (forall i j, (j < k)%nat -> is_fresh j (cast (f' i) (k + n))) ->
  (forall i j, (j < k)%nat -> bcfresh j (f i)) ->
  uc_eval (k + n) (controlled_powers f k) = 
    UnitarySem.uc_eval (QPE.controlled_powers_var f' k).
Proof.
  assert (H : forall n (f : nat -> bccom) (f' : nat -> base_ucom n) k kmax,
    (kmax > 0)%nat ->
    (forall i, uc_eval (kmax + n) (bc2ucom (f i)) = 
          UnitarySem.uc_eval (cast (f' i) (kmax + n))) ->
    (forall i j, (j < kmax)%nat -> is_fresh j (cast (f' i) (kmax + n))) ->
    (forall i j, (j < kmax)%nat -> bcfresh j (f i)) ->
    uc_eval (kmax + n) (bc2ucom (controlled_powers' f k kmax)) = 
      UnitarySem.uc_eval (@QPE.controlled_powers_var' n f' k kmax)).
  { intros n f f' k kmax Hkmax Hfeq Hfr' Hfr.
    destruct k; try reflexivity.
    induction k. 
    simpl.
    rewrite uc_eval_bygatectrl_correct.
    rewrite control_correct.  
    rewrite cast_control_commute.
    apply control_cong.
    apply Hfeq.
    split; intro H.
    apply Hfr'. lia.
    apply bcfresh_is_fresh.
    apply Hfr. lia.
    apply bc2ucom_WF.
    replace (controlled_powers' f (S (S k)) kmax)
      with (bcseq (controlled_powers' f (S k) kmax)
                  (bygatectrl (kmax - (S k) - 1) (f (S k)))) 
      by reflexivity.
    replace (controlled_powers_var' f' (S (S k)) kmax)
      with (controlled_powers_var' f' (S k) kmax ;
            cast (UnitaryOps.control (kmax - (S k) - 1) (f' (S k))) (kmax + n))%ucom 
      by reflexivity.
    remember (S k) as k'.
    specialize (uc_eval_bygatectrl_correct (f k')) as G.
    unfold uc_eval in *.
    simpl in *.
    rewrite IHk.
    apply f_equal2; try reflexivity.
    specialize control_correct as aux.
    unfold uc_eval in aux.
    rewrite G.
    rewrite aux. clear aux.
    rewrite cast_control_commute.
    apply control_cong.
    apply Hfeq.
    split; intro H.
    apply Hfr'. lia.
    apply bcfresh_is_fresh.
    apply Hfr. lia.
    apply bc2ucom_WF. }
  intros. apply H; auto.
Qed.

Lemma map_bccom_eq_map_qubits : forall f bc,
  bcelim bc <> bcskip ->
  bc2ucom (map_bccom f (bcelim bc)) = map_qubits f (bc2ucom (bcelim bc)).
Proof.
  intros f bc H.
  induction bc; simpl in *; try reflexivity.
  contradict H; reflexivity.
  destruct (bcelim bc). contradiction.
  1-2: try rewrite IHbc by easy; reflexivity.
  simpl bc2ucom.
  rewrite map_qubits_control.
  simpl in IHbc.
  rewrite IHbc by easy.
  reflexivity.
  apply control'_WF.
  apply bc2ucom_WF.
  simpl bc2ucom.
  rewrite map_qubits_control.
  simpl in IHbc.
  rewrite IHbc by easy.
  reflexivity.
  constructor; apply bc2ucom_WF.
  destruct (bcelim bc1); destruct (bcelim bc2); try easy;
    simpl in *; try rewrite IHbc2; try rewrite IHbc1; easy.
Qed.

Local Opaque npar controlled_powers QFT_w_reverse QPE.QFT_w_reverse.
Lemma QPE_same : forall k n (f : nat -> bccom) (f' : nat -> base_ucom n),
  (k > 0)%nat -> (n > 0)%nat ->
  (forall i, bcelim (f i) <> bcskip) ->
  (forall i, uc_eval n (bc2ucom (bcelim (f i))) = UnitarySem.uc_eval (f' i)) ->
  uc_eval (k + n) (QPE k (fun i => bcelim (f i))) = 
    UnitarySem.uc_eval (QPE.QPE_var k n f').
Proof.
  intros k n f f' Hk Hn Hf1 Hf2.
  unfold uc_eval. simpl.
  repeat apply f_equal2.
  - specialize change_dim as H.
    unfold uc_eval in H.
    rewrite H with (n:=k). 
    symmetry. apply cast_cong_r.
    rewrite <- uc_well_typed_invert. 
    apply QFT_w_reverse_WT.
    assumption.
    symmetry. 
    specialize invert_same as aux.
    unfold uc_eval in aux.
    unfold uc_equiv.
    rewrite aux. 
    rewrite <- 2 invert_correct.
    apply f_equal.
    apply QFT_w_reverse_same.
    apply QFT_w_reverse_WF.
  - apply controlled_powers_same; auto.
    intro i.
    rewrite map_bccom_eq_map_qubits.
    rewrite change_dim with (n:=n).
    unfold uc_eval in *.
    rewrite map_qubits_same.
    apply cast_cong_l.
    apply Hf2.
    apply bc2ucom_WF.
    apply Hf1.
    intros i j Hj.
    apply map_qubits_fresh; auto.
    intros i j Hj.
    apply map_qubits_bcfresh; auto.
  - specialize change_dim as H.
    unfold uc_eval in H.
    rewrite H with (n:=k). 
    symmetry. apply cast_cong_r. 
    apply npar_WT.
    assumption.
    symmetry. apply npar_H_same.
Qed.

(* Compute the effect of running (shor_circuit a N) on the all-zero input state. *)
Definition run_shor_circuit a N := 
  @Mmult _ _ 1 (uc_eval (shor_nqs N) (shor_circuit a N))
               (basis_vector (2^(shor_nqs N)) 0).

(* Returns the probability that (shor_circuit a N) outputs x. *)
Definition prob_shor_outputs a N x := 
  @prob_partial_meas _ (modmult_nqs N) 
    (basis_vector (2^(shor_output_nqs N)) x) (run_shor_circuit a N).

Local Opaque genM0 modmult_full reverser bcinv.
Lemma bcelim_modmult_rev_neq_bcskip : forall n M C Cinv,
  bcelim (modmult_rev M C Cinv n) <> bcskip.
Proof. 
  intros.
  unfold modmult_rev.
  assert (bcelim (modmult M C Cinv (S (S n))) <> bcskip).
  { unfold modmult.
    assert (bcelim (swapperh1 (S (S n))) <> bcskip).
    { unfold swapperh1.
      simpl. 
      destruct (bcelim (swapperh1' n (S (S n)))); easy. }
    Local Opaque swapperh1.
    simpl.
    destruct (bcelim (swapperh1 (S (S n)))); 
    destruct (bcelim (genM0 M (S (S n)))); 
    destruct (bcelim (modmult_full C Cinv (S (S n))));
    destruct (bcelim (bcinv (swapperh1 (S (S n)); genM0 M (S (S n)))%bccom));
    easy. }
  Local Opaque modmult.
  simpl.
  destruct (bcelim (bcinv (reverser n))); 
  destruct (bcelim (modmult M C Cinv (S (S n))));
  destruct (bcelim (reverser n));
  easy.
Qed.

Lemma shor_circuit_same : forall a N, 
  (0 < N)%nat ->
  let m := shor_output_nqs N in
  let n := modmult_data_nqs N in
  let f := Shor.f_modmult_circuit a (modinv a N) N n in
  uc_eval (shor_nqs N) (shor_circuit a N) = 
    UnitarySem.uc_eval (SQIR.useq (SQIR.X (m + n - 1)) (QPE_var m (modmult_nqs N) f)).
Proof.
  intros a N H m n f.
  subst m n.
  unfold uc_eval, shor_circuit, shor_nqs, modmult_nqs.
  unfold shor_output_nqs, modmult_data_nqs, modmult_anc_nqs in *.
  Local Opaque Nat.mul Nat.pow QPE QPE.QPE_var.
  simpl.
  remember (Nat.log2 (2 * N ^ 2)) as m.
  remember (Nat.log2 (2 * N)) as n.
  assert (0 < n)%nat.
  { subst. apply Nat.log2_pos. lia. }
  assert (0 < m)%nat.
  { subst. 
    assert (1 <= N ^ 2)%nat.
    rewrite <- (Nat.pow_1_l 2) at 1.
    apply Nat.pow_le_mono_l. lia.
    apply Nat.log2_pos. lia. }
  clear Heqn Heqm.
  apply f_equal2.
  apply QPE_same; auto.
  lia.
  intro i.
  apply bcelim_modmult_rev_neq_bcskip.
  intro i.
  subst f.
  unfold f_modmult_circuit, modexp.
  rewrite bc2ucom_correct.
  reflexivity.
  reflexivity.
Qed.

Lemma uc_well_typed_shor_circuit : forall a N,
  (a < N)%nat ->
  uc_well_typed (to_base_ucom (shor_nqs N) (shor_circuit a N)).
Proof.
  intros.
  apply uc_eval_nonzero_iff.
  specialize (shor_circuit_same a N) as Hsame. 
  unfold uc_eval in Hsame.
  rewrite Hsame by lia.
  clear Hsame.
  apply uc_eval_nonzero_iff.
  unfold shor_output_nqs, modmult_nqs, modmult_data_nqs, modmult_anc_nqs.
  constructor.
  apply uc_well_typed_X. 
  unfold modmult_rev_anc.
  lia.
  apply QPE_var_WT.
  assert (1 <= N ^ 2)%nat.
  rewrite <- (Nat.pow_1_l 2) at 1.
  apply Nat.pow_le_mono_l. lia.
  apply Nat.log2_pos. lia. 
  intro i.
  assert (Nat.log2 (2 * N) > 0)%nat.
  apply Nat.log2_pos. lia.
  apply eWT_uc_well_typed_bcelim. lia.
  apply modmult_rev_eWT. lia.
Qed.

Lemma shor_circuit_same' : forall a N x, 
  (0 < N)%nat ->
  let m := shor_output_nqs N in
  let n := modmult_data_nqs N in
  let anc := modmult_anc_nqs N in
  let f := Shor.f_modmult_circuit a (modinv a N) N n in
  prob_shor_outputs a N x = 
    prob_partial_meas (basis_vector (2^m) x) (Shor.Shor_final_state m n anc f).
Proof.
  intros a N x H m n anc f.
  unfold prob_shor_outputs, run_shor_circuit.
  rewrite shor_circuit_same by assumption.
  subst m n anc.
  unfold shor_nqs, modmult_nqs.
  unfold shor_output_nqs, modmult_data_nqs, modmult_anc_nqs in *.
  remember (Nat.log2 (2 * N ^ 2)) as m.
  remember (Nat.log2 (2 * N)) as n.
  assert (0 < n)%nat.
  { subst. apply Nat.log2_pos. lia. }
  assert (0 < m)%nat.
  { subst. 
    assert (1 <= N ^ 2)%nat.
    rewrite <- (Nat.pow_1_l 2) at 1.
    apply Nat.pow_le_mono_l. lia.
    apply Nat.log2_pos. lia. }
  clear Heqm Heqn.
  apply f_equal.
  unfold Shor_final_state.
  simpl.
  rewrite Mmult_assoc.
  rewrite 4 basis_f_to_vec_alt.
  rewrite f_to_vec_X by lia.
  rewrite f_to_vec_merge.
  restore_dims.
  rewrite f_to_vec_merge.
  apply f_equal2.
  reflexivity.
  rewrite Nat.add_assoc.
  apply f_to_vec_eq; intros i Hi.
  bdestruct (i <? m + n).
  bdestruct (i <? m).
  rewrite update_index_neq by lia.
  rewrite 2 nat_to_funbool_0.
  reflexivity.
  bdestruct (i =? m + n - 1).
  subst i.
  rewrite update_index_eq.
  rewrite nat_to_funbool_0, nat_to_funbool_1. 
  bdestructΩ (m + n - 1 - m =? n - 1).
  try reflexivity.
  rewrite update_index_neq by lia.
  rewrite nat_to_funbool_0, nat_to_funbool_1. 
  bdestructΩ (i - m =? n - 1).
  try reflexivity.
  rewrite update_index_neq by lia.
  rewrite 2 nat_to_funbool_0.
  reflexivity.
  apply pow_positive; lia.
  apply Nat.pow_gt_1; lia.
  apply pow_positive; lia.
  apply pow_positive; lia.
Qed.


