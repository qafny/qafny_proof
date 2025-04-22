Require Export VectorStates.
Require Import DiscreteProb.

Local Coercion Nat.b2n : bool >-> nat.

(* General definitions useful for specifying & verifying quantum algorithms. *)


(* ======================================== *)
(**    Boolean oracle (f : nat -> bool)    **)
(* ======================================== *)

(* Definition of boolean oracle U : ∣ x ⟩∣ y ⟩ ↦ ∣ x ⟩∣ y ⊕ f(x) ⟩ *)
Definition boolean_oracle {n} (U : base_ucom (S n)) (f : nat -> bool) :=
  forall x (y : bool), (x < 2 ^ n)%nat -> 
    @Mmult _ _ 1 (uc_eval U) (basis_vector (2 ^ n) x ⊗ ∣ y ⟩) = 
      basis_vector (2 ^ n) x ⊗ ∣ xorb y (f x) ⟩.

Definition pad_vector {n} dim (v : Vector (2 ^ n)) : Vector (2 ^ dim) :=
  v ⊗ kron_n (dim - n) ∣0⟩.

Lemma wf_pad_vector :
  forall n dim (v : Vector (2 ^ n)),
  (n <= dim)%nat -> WF_Matrix v -> WF_Matrix (pad_vector dim v).
Proof.
  intros n dim v Hn Hw. unfold pad_vector.
  apply WF_kron; auto with wf_db.
  rewrite Nat.pow_1_l. reflexivity.
Qed.

(* Alternate form of boolean_oracle that uses ancilla qubits.
   The qubits are ordered as follows: 
     input x (n qubits) ; output y (1 qubit) ; ancillae (dim-n-1 qubits) *)
Definition padded_boolean_oracle {dim} n
  (U : base_ucom dim) (f : nat -> bool) :=
  forall x (y : bool),
  (x < 2 ^ n)%nat ->
  @Mmult
      _ _ 1
      (uc_eval U)
      (@pad_vector (S n) dim (basis_vector (2 ^ n) x ⊗ ∣ y ⟩ )) =
    @pad_vector (S n) dim (basis_vector (2 ^ n) x ⊗ ∣ xorb y (f x) ⟩ ).


(* ======================================= *)
(**    Integer oracle (f : nat -> nat)    **)
(* ======================================= *)

(* Special case U : ∣ x ⟩∣ 0 ⟩ ↦ ∣ x ⟩∣ f(x) ⟩ *)
Definition integer_oracle {n} (U : base_ucom (2 * n)) (f : nat -> nat) :=
  forall (x :nat), (x < 2 ^ n)%nat -> 
    @Mmult _ _ 1 (uc_eval U) (basis_vector (2 ^ n) x ⊗ basis_vector (2 ^ n) 0) = 
      basis_vector (2 ^ n) x ⊗ ((basis_vector (2 ^ n) (f x))).


(* ========================================== *)
(**    Count the solutions to a predicate    **)
(* ========================================== *)

(* Count the number of inputs in [a,a+b) where f returns true; note that
   we never "run" this function, it's just used in specifications. *)
Fixpoint count (f : nat -> bool) a b : nat :=
  match b with
  | O => O
  | S b' => (f (a + b') + count f a b')%nat
  end.

Definition count0 f := count f 0.
Definition count1 f := count f 1.

Lemma count_extend : forall f a b, 
  count f a (S b)  = if (f (a + b)%nat) then S (count f a b) else count f a b.
Proof. intros. simpl. destruct (f (a + b)%nat); reflexivity. Qed.

Lemma count_upper_bound : forall a b (f : nat -> bool), (count f a b <= b)%nat.
Proof.
  intros.
  induction b; simpl.
  lia.
  destruct (f (a + b)%nat); simpl; lia.
Qed.

Lemma count_all_false : forall a b, count (fun _ => false) a b = O.
Proof. induction b; intros; simpl; try apply IHn; easy. Qed.

Lemma count_all_true : forall a b, count (fun _ => true) a b = b.
Proof. induction b; intros; simpl; lia. Qed.

Lemma count_zero: forall  a b (f : nat -> bool), 
  count f a b = O -> forall i, (a <= i < a + b)%nat -> f i = false.
Proof.
  intros a b f H i Hi.
  induction b as [|b].
  lia.
  simpl in H.
  apply Nat.eq_add_0 in H as [? ?].
  bdestruct (i =? a + b)%nat; subst.
  destruct (f (a + b)%nat); simpl in *; easy.
  apply IHb; lia.
Qed.
 
Lemma count_nonzero: forall  a b (f : nat -> bool), 
  count f a b <> O <-> exists i, (a <= i < a + b)%nat /\ f i = true.
Proof.
  intros a b f.
  split; intro H.
  - induction b as [|b].
    simpl in H.
    lia.
    simpl in H.
    bdestruct (count f a b =? 0).
    rewrite H0 in H.
    exists (a + b)%nat.
    split; try lia.
    destruct (f (a + b)%nat); simpl in *; auto.
    apply IHb in H0. 
    destruct H0 as [x [? ?]].
    exists x.
    split. lia. auto.
  - destruct H as [x [Hx1 Hx2]]. 
    induction b. lia.
    bdestruct (x =? a + b)%nat. subst. simpl. rewrite Hx2. simpl. lia.
    simpl. destruct (f (a + b))%nat; lia.
Qed.

Lemma count_eq : forall a b f g,
    (forall x, (a <= x < a + b)%nat -> f x = g x) ->
    count f a b = count g a b.
Proof.
  induction b; intros. reflexivity.
  assert (f (a + b) = g (a + b))%nat by (apply H; lia).
  simpl. rewrite H0. rewrite IHb with (g := g). reflexivity.
  intros. apply H. lia.
Qed.

Lemma count_update_oob : forall f x v a b, 
  (x < a)%nat \/ (a + b <= x)%nat -> 
  count f a b = count (update f x v) a b.
Proof.
  intros. apply count_eq. intros.
  rewrite update_index_neq. easy. lia.
Qed.

Lemma count_update : forall f x v a b, 
  (a <= x < a + b)%nat -> 
  f x = true -> 
  count (update f x v) a b = if v then count f a b else ((count f a b) - 1)%nat.
Proof.
  induction b; intros. lia.
  destruct v. rewrite update_same; easy.
  bdestruct (x =? a + b)%nat. subst. simpl. rewrite update_index_eq. rewrite H0.
  rewrite <- count_update_oob; simpl; lia.
  simpl. rewrite update_index_neq by easy. 
  destruct (f (a + b))%nat. rewrite IHb by (try easy; try lia).
  assert (count f a b <> 0)%nat. 
  apply count_nonzero. exists x. split. lia. assumption.
  lia.
  rewrite IHb. easy. lia. easy.
Qed.

Lemma count_update_false : forall a b x f, 
  (a <= x < a + b)%nat -> 
  f x = true -> 
  S (count (update f x false) a b) = count f a b.
Proof.
  intros. 
  assert (count f a b <> 0)%nat. 
  apply count_nonzero. exists x. split. lia. assumption.
  rewrite count_update by assumption.
  lia.
Qed.

Lemma count0_Nsum : forall n f, count0 f n = Nsum n (fun i => if f i then S O else O).
Proof.
  unfold count0.
  intros. induction n. reflexivity. 
  simpl. rewrite IHn. destruct (f n); simpl; lia.
Qed.

Lemma count1_Nsum : forall n f,
  f O = false -> 
  f n = false ->
  count1 f n = Nsum n (fun i => if f i then S O else O).
Proof.
  unfold count1.
  intros n f HO Hn. 
  assert (H : count f 1 n = Nsum (S n) (fun i => if f i then S O else O)).
  { clear Hn.
    induction n. simpl. rewrite HO. reflexivity.
    simpl. rewrite IHn. destruct (f (S n)); simpl; lia. }
  destruct n. reflexivity.
  rewrite H. simpl. rewrite Hn. simpl. lia.
Qed.

Lemma count_complement : forall a b f g, 
  (count (fun i => f i && g i) a b + count (fun i => f i && ¬ (g i)) a b = count f a b)%nat.
Proof.
  intros. induction b. easy.
  simpl. destruct (f (a + b))%nat; destruct (g (a + b))%nat; simpl; lia.
Qed.

Lemma count_implies : forall a b f g,
  (forall x, a <= x < a + b -> f x = true -> g x = true)%nat ->
  (count f a b <= count g a b)%nat.
Proof.
  intros. induction b. easy.
  assert (count f a b <= count g a b)%nat.
  { apply IHb. intros. apply H. lia. easy. }
  simpl. destruct (f (a + b))%nat eqn:Hf. apply H in Hf. 
  2: lia.
  rewrite Hf. lia.
  destruct (g (a + b))%nat; simpl; lia.
Qed.

Lemma count_orb : forall a b f g,
  count (fun i => f i || g i) a b = 
    (count f a b + count (fun i => ¬ (f i) && g i)  a b)%nat.
Proof.
  intros.
  rewrite <- count_complement with (g:=f).
  assert (forall n1 n2 n3 n4, n1 = n3 -> n2 = n4 -> n1 + n2 = n3 + n4)%nat by lia.
  apply H; apply count_eq; intros; destruct (f x); destruct (g x); reflexivity.
Qed.

Definition negf (f : nat -> bool) i := negb (f i).

Lemma negf_involutive : forall f, negf (negf f) = f.
Proof.
  intros.
  unfold negf.
  apply functional_extensionality.
  intro.
  apply negb_involutive.
Qed.

Local Opaque Nat.sub.
Lemma count_negf : forall a b (f : nat -> bool),
  count (negf f) a b = (b - count f a b)%nat.
Proof.
  intros.
  induction b; simpl.
  reflexivity.
  rewrite IHb.
  unfold negf.
  specialize (count_upper_bound a b f) as H.
  destruct (f (a + b))%nat; simpl; lia.
Qed.

Lemma vsum_count0 : forall n (f : nat -> bool),
  vsum n (fun i : nat => if f i then I 1 else Zero) = 
    INR (count0 f n) .* I 1.
Proof.
  unfold count0.
  intros.
  induction n. 
  lma.
  rewrite vsum_extend_r, IHn.
  simpl count.
  rewrite plus_INR.
  destruct (f n); simpl; lma.
Qed.

Lemma nth_repeat : forall n r i,
  (i < n)%nat -> nth i (repeat r n) 0 = r.
Proof.
  intros n r i Hi.
  rewrite nth_indep with (d':=r).
  clear Hi.
  gen i.
  induction n; intro i; simpl; destruct i; try reflexivity.
  apply IHn.
  rewrite repeat_length.
  assumption.
Qed.

Lemma pr_outcome_sum_count : forall l u f,
  (l < u)%nat ->
  pr_outcome_sum (uniform l u) f 
  = (INR (count1 (fun x => f (l + x - 1)%nat) (u - l)) / INR (u - l))%R.
Proof.
  intros l u f H.
  unfold uniform.
  rewrite pr_outcome_sum_append.
  rewrite pr_outcome_sum_repeat_false.
  rewrite Rplus_0_l.
  remember (u - l)%nat as n.
  assert (Hn:(n > 0)%nat) by lia.
  clear - Hn.
  unfold pr_outcome_sum.
  rewrite 2 repeat_length.
  erewrite Rsum_eq_bounded.
  2: { intros i Hi.
       replace  (if f (l + i)%nat then nth i (repeat (1 / INR n)%R n) 0 else 0) with
           ((1 / INR n)%R * (if f (l + i)%nat then 1 else 0))%R.
       reflexivity.
       destruct (f (l + i)%nat).
       rewrite nth_repeat by assumption.
       lra.
       lra. }
  rewrite <- Rsum_scale.
  replace (INR (count1 (fun x : nat => f (l + x - 1)%nat) n) / INR n)%R with (1 / INR n * INR (count1 (fun x : nat => f (l + x - 1)%nat) n))%R by lra.
  apply f_equal2; try reflexivity.
  clear Hn.
  induction n.
  reflexivity.
  rewrite Rsum_extend.
  simpl.
  rewrite IHn.
  unfold count1. simpl.
  replace (l + S n - 1)%nat with (l + n)%nat by lia.
  destruct (f (l + n)%nat). 
  rewrite S_O_plus_INR.
  simpl.
  reflexivity.
  simpl. lra.
Qed.

(* Copied from euler/Asympt.v *)
Lemma seq_extend :
  forall n x, List.seq x (S n) = List.seq x n ++ [(x + n)%nat].
Proof.
  induction n; intros. simpl. rewrite Nat.add_0_r. easy.
  replace (List.seq x (S (S n))) with (x :: List.seq (S x) (S n)) by easy.
  rewrite IHn. simpl. replace (x + S n)%nat with (S (x + n))%nat by lia.
  easy.
Qed.

Lemma count_filter_seq : forall a b f, 
  count f a b = length (filter f (List.seq a b)).
Proof.
  induction b; intros.
  reflexivity.
  rewrite seq_extend. rewrite filter_app. rewrite app_length.
  rewrite <- IHb. simpl.
  destruct (f (a + b))%nat. simpl. lia.
  simpl. lia.
Qed.


(* ============================== *)
(**    Measurement predicates    **)
(* ============================== *)

(* What is the probability of outcome ϕ given input ψ? *)
Definition probability_of_outcome {n} (ϕ ψ : Vector n) : R :=
  let c := (ϕ† × ψ) O O in
  (Cmod c) ^ 2.

(* What is the probability of measuring ϕ on the first m qubits given
  (m + n) qubit input ψ? *)
Definition prob_partial_meas {m n} (ϕ : Vector (2^m)) (ψ : Vector (2^(m + n))) :=
  Rsum (2^n) (fun y => probability_of_outcome (ϕ ⊗ basis_vector (2^n) y) ψ).

Lemma probability_of_outcome_comm : forall {d} (ϕ ψ : Vector d),
  probability_of_outcome ϕ ψ = probability_of_outcome ψ ϕ.
Proof.
  intros d ψ ϕ. unfold probability_of_outcome.
  replace (ϕ † × ψ) with (ϕ † × ψ ††) by (rewrite adjoint_involutive; easy).
  rewrite <- Mmult_adjoint.
  unfold adjoint.
  rewrite Cmod_Cconj.
  reflexivity.
Qed.

Lemma probability_of_outcome_is_norm : forall {d} (ϕ ψ : Vector d),
  probability_of_outcome ϕ ψ = ((norm (ϕ† × ψ)) ^ 2)%R.
Proof.
  intros d ψ ϕ.
  unfold probability_of_outcome, Cmod, norm.
  apply f_equal2; try reflexivity.
  apply f_equal.
  unfold Mmult, adjoint.
  simpl.
  autorewrite with R_db.
  reflexivity.
Qed.

Lemma Rsum_Msum : forall n (f : nat -> Square 1),
  Rsum n (fun i : nat => Datatypes.fst (f i O O)) = Datatypes.fst (Msum n f O O).
Proof.
  intros.
  rewrite Msum_Csum.
  rewrite <- Rsum_Csum.
  induction n; simpl.
  reflexivity.
  rewrite IHn.
  reflexivity.
Qed.

Lemma prob_partial_meas_alt : 
  forall {m n} (ϕ : Vector (2^m)) (ψ : Vector (2^(m + n))),
  @prob_partial_meas m n ϕ ψ = ((norm ((ϕ ⊗ I (2 ^ n))† × ψ)) ^ 2)%R.
Proof.
  intros.
  unfold prob_partial_meas.
  erewrite Rsum_eq.
  2: { intros.
       rewrite probability_of_outcome_is_norm.
       unfold norm.
       rewrite pow2_sqrt.
       restore_dims.
       distribute_adjoint.
       Msimpl.
       repeat rewrite Mmult_assoc.
       restore_dims.
       rewrite <- (Mmult_assoc (ϕ ⊗ _)).
       rewrite kron_mixed_product.
       unify_pows_two.
       rewrite <- Mmult_assoc.
       reflexivity. 
       apply inner_product_ge_0. }  
  rewrite rewrite_I_as_sum by lia.
  rewrite kron_Msum_distr_l.
  rewrite Msum_adjoint.
  erewrite Msum_eq_bounded.
  2: { intros. distribute_adjoint. reflexivity. }
  rewrite Mmult_Msum_distr_r.
  unfold norm.
  rewrite pow2_sqrt.
  2: apply inner_product_ge_0.
  rewrite Msum_adjoint, Mmult_Msum_distr_l.
  erewrite Msum_eq_bounded.
  2: { intros.
      rewrite Mmult_Msum_distr_r. 
      erewrite Msum_eq_bounded.
      2: { intros.
           distribute_adjoint.
           Msimpl.
           repeat rewrite Mmult_assoc.
           restore_dims.
           rewrite <- (Mmult_assoc (ϕ ⊗ _)).
           rewrite kron_mixed_product.
           repeat rewrite Mmult_assoc.
           rewrite <- (Mmult_assoc (_†)).
           reflexivity. } 
     reflexivity. }
  rewrite Msum_diagonal.
  2: { intros. rewrite basis_vector_product_neq by auto.
       do 2 Msimpl. reflexivity. }
  erewrite Msum_eq_bounded.
  2: { intros. rewrite basis_vector_product_eq by assumption.
       Msimpl. unify_pows_two.
       repeat rewrite <- Mmult_assoc.
       reflexivity. }
  remember (fun i : nat => ψ† × (ϕ × ϕ† ⊗ (basis_vector (2 ^ n) i × (basis_vector (2 ^ n) i) †)) × ψ) as f.
  erewrite Rsum_eq.
  2: { intros.
       replace (ψ† × (ϕ × ϕ† ⊗ (basis_vector (2 ^ n) i × (basis_vector (2 ^ n) i) †)) × ψ) with (f i) by (subst; reflexivity).
       reflexivity. }
  apply Rsum_Msum.
Qed.

Lemma partial_meas_tensor : 
  forall {m n} (ϕ : Vector (2^m)) (ψ1 : Vector (2^m)) (ψ2 : Vector (2^n)),
  Pure_State_Vector ψ2 ->
  @prob_partial_meas m n ϕ (ψ1 ⊗ ψ2) = probability_of_outcome ϕ ψ1.
Proof.
  intros ? ? ? ? ? [H H0].
  rewrite prob_partial_meas_alt.
  rewrite probability_of_outcome_is_norm.
  unfold norm.
  apply f_equal2; try reflexivity.
  do 2 apply f_equal.
  distribute_adjoint.
  Msimpl.
  rewrite H0.
  Msimpl.
  reflexivity.
Qed.

Lemma nth_apply_u_probability_of_outcome : forall n (u : Square (2 ^ n)) x,
  (x < 2 ^ n)%nat ->
  WF_Matrix u ->
  nth x (apply_u u) 0 
    = probability_of_outcome 
        (basis_vector (2^n) x) 
        (u × basis_vector (2^n) 0).
Proof.
  intros n u x Hx WFu.
  unfold apply_u, probability_of_outcome.
  rewrite nth_indep with (d':=Cmod2 0).
  rewrite map_nth.
  remember (u × basis_vector (2 ^ n) 0) as ψ.
  rewrite nth_vec_to_list by assumption.
  rewrite (basis_vector_decomp ψ) at 2.
  rewrite Mmult_vsum_distr_l.
  symmetry.
  erewrite vsum_unique.
  2 : { exists x. split. assumption. 
        split.
        rewrite Mscale_mult_dist_r.
        rewrite basis_vector_product_eq.
        reflexivity. assumption.
        intros y Hy Hxy.
        rewrite Mscale_mult_dist_r.
        rewrite basis_vector_product_neq by auto.
        lma. }
  unfold Cmod, Cmod2.
  rewrite pow2_sqrt.
  unfold I, scale.
  simpl.
  lra.
  apply Rplus_le_le_0_compat; apply pow2_ge_0.
  subst. 
  apply WF_mult.
  assumption.
  apply basis_vector_WF.
  apply pow_positive. lia.
  rewrite map_length.  
  rewrite vec_to_list_length.
  assumption.
Qed.

Lemma rewrite_pr_outcome_sum : forall n k (u : Square (2 ^ (n + k))) f,
  WF_Matrix u ->
  pr_outcome_sum (apply_u u) (fun x => f (fst k x)) 
  = Rsum (2 ^ n) (fun x => ((if f x then 1 else 0) *
                         prob_partial_meas (basis_vector (2 ^ n) x) 
                           (u × basis_vector (2 ^ (n + k)) 0))%R).
Proof.
  intros n k u f WFu.
  unfold pr_outcome_sum.
  unfold apply_u at 1.
  rewrite map_length.
  rewrite vec_to_list_length.
  rewrite nested_Rsum.
  apply Rsum_eq_bounded.
  intros x Hx.
  destruct (f x) eqn:fx.
  rewrite Rmult_1_l.
  erewrite Rsum_eq_bounded.
  2: { intros y Hy. 
       rewrite simplify_fst by assumption.
       rewrite fx.
       rewrite nth_apply_u_probability_of_outcome.
       reflexivity.
       replace (2 ^ (n + k))%nat with (2 ^ n * 2 ^ k)%nat by unify_pows_two.
       nia. assumption.
  }
  unfold prob_partial_meas.
  erewrite Rsum_eq_bounded.
  reflexivity.
  intros y Hy. 
  rewrite split_basis_vector by assumption.
  replace (2 ^ (n + k))%nat with (2 ^ n * 2 ^ k)%nat by unify_pows_two.
  reflexivity.
  rewrite Rmult_0_l.
  erewrite Rsum_eq_bounded.
  2: { intros y Hy. rewrite simplify_fst by assumption.
       rewrite fx. reflexivity. }
  apply Rsum_0.
  reflexivity.
Qed.
