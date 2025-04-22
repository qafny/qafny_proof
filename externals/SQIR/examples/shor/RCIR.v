Require Import VectorStates UnitaryOps Coq.btauto.Btauto.

(* The following belows to the RCIR file, which contains only the boolean circuit. *)
(* Implementation Language *)
Inductive bccom :=
| bcskip
| bcx (n : nat)
| bcswap (m n : nat)
| bccont (n : nat) (p : bccom)
| bcseq (p1 p2 : bccom)
.

Declare Scope bccom_scope.
Delimit Scope bccom_scope with bccom.
Local Open Scope bccom.
Notation "p1 ; p2" := (bcseq p1 p2) (at level 50) : bccom_scope.
Notation "f '[' i '|->' x ']'" := (update f i x) (at level 10).
Local Open Scope nat_scope.

Definition bccnot (x y : nat) := bccont x (bcx y).
Definition bcccnot (x y z : nat) := bccont x (bccnot y z).

Fixpoint bcexec (p : bccom) (f : nat -> bool) :=
  match p with
  | bcskip => f
  | bcx n => f [n |-> ¬ (f n)]
  | bcswap m n => (f [n |-> f m]) [m |-> f n]
  | bccont n p => if f n then bcexec p f else f
  | bcseq p1 p2 => bcexec p2 (bcexec p1 f)
  end.

Ltac BreakIf :=
  match goal with
  | [ |- context[if ?X then _ else _] ] => destruct X eqn:?
  | [ H : context[if ?X then _ else _] |- _ ] => destruct X eqn:?
  end.

Ltac gen_if_no T P :=
  match goal with
  | [ H : T |- _ ] => idtac
  | _ => assert (T) by P
  end.

Lemma neq_sym :
  forall {T} (x y : T),
    x <> y -> y <> x.
Proof.
  intros. intro. rewrite H0 in H. easy.
Qed.

Ltac GenNeq :=
  match goal with
  | [ H : ?x <> ?y |- _ ] => gen_if_no (y <> x) (apply (neq_sym x y H))
  end.

Ltac EqbEq :=
  match goal with
  | [ H : (?x =? ?y) = true |- _ ] => repeat rewrite H; rewrite Nat.eqb_eq in H; subst
  end.

Ltac EqbRefl :=
  match goal with
  | [ |- context[?x =? ?x] ] => repeat rewrite Nat.eqb_refl; simpl
  end.

Ltac EqbNeq :=
  match goal with
  | [ H : ?x =? ?y = false |- _ ] => repeat rewrite H; rewrite Nat.eqb_neq in H; GenNeq
  end.

Ltac EqEqb :=
  match goal with
  | [ H : ?x = ?y |- context[?x =? ?y] ] => rewrite <- (Nat.eqb_eq x y H); simpl
  | [ H : ?x <> ?y |- context[?x =? ?y] ] => rewrite <- (Nat.eqb_neq x y H); simpl
  end.

Ltac Negb :=
  match goal with
  | [ H : ¬ ?b = false |- _ ] => rewrite negb_false_iff in H
  | [ H : ¬ ?b = true |- _ ] => rewrite negb_true_iff in H
  end.

Ltac boolsub :=
  match goal with
  | [ H : ?b = true |- context[?b] ] => rewrite H
  | [ H : ?b = false |- context[?b] ] => rewrite H
  | [ H1 : ?b = true, H2 : ?b = false |- _ ] => rewrite H1 in H2; discriminate H2
  | [ H1 : ?b = true, H2 : context[?b] |- _ ] => rewrite H1 in H2; simpl in H2
  | [ H1 : ?b = false, H2 : context[?b] |- _ ] => rewrite H1 in H2; simpl in H2
  end.

Ltac bdes exp :=
  match exp with
  | ?a ⊕ ?b => bdes a; bdes b
  | ?a && ?b => bdes a; bdes b
  | ?a || ?b => bdes a; bdes b
  | ¬ ?a => bdes a
  | true => idtac
  | false => idtac
  | ?a => destruct a eqn:?; repeat boolsub; try easy
  end.

Ltac bsimpl :=
  simpl in *;
  match goal with
  | [ |- true = false ] => match goal with
                         | [ H : context[?a ⊕ ?b] |- _ ] => bdes a; bdes b
                         | [ H : context[?a && ?b] |- _ ] => bdes a; bdes b
                         | [ H : context[?a || ?b] |- _ ] => bdes a; bdes b
                         | [ H : context[¬ ?a] |- _ ] => bdes a
                         end
  | [ |- false = true ] => match goal with
                         | [ H : context[?a ⊕ ?b] |- _ ] => bdes a; bdes b
                         | [ H : context[?a && ?b] |- _ ] => bdes a; bdes b
                         | [ H : context[?a || ?b] |- _ ] => bdes a; bdes b
                         | [ H : context[¬ ?a] |- _ ] => bdes a
                         end
  | [ |- ?a = ?b ] => bdes a; bdes b
  end.

Ltac Expand fl :=
  match fl with
  | [] => idtac
  | ?x :: ?fl' => match goal with
                | [ H : x = ?b |- _ ] => repeat (rewrite H; simpl)
                | _ => idtac
                end;
                Expand fl'
  end.

Ltac bnauto_expand fl :=
  try btauto;
  repeat (BreakIf; repeat EqbEq; repeat EqbRefl; 
     repeat EqbNeq; repeat Negb; repeat boolsub; try (Expand fl); try easy; try btauto);
  repeat bsimpl.  

Ltac bnauto := bnauto_expand (@List.nil bool).

Lemma bcseq_correct :
  forall p1 p2 f, bcexec (p1 ; p2) f = bcexec p2 (bcexec p1 f).
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma bccnot_correct :
  forall x y f,
    x <> y ->
    bcexec (bccnot x y) f = f[y |-> (f y ⊕ f x)].
Proof.
  intros. apply functional_extensionality; intro i. simpl. unfold update.
  bnauto.
Qed.

Lemma bcswap_correct :
  forall x y f,
    bcexec (bcswap x y) f = fun i => if i =? x then f y else if i =? y then f x else f i.
Proof. intros. reflexivity. Qed.

Lemma bcccnot_correct :
  forall x y z f,
    x <> y ->
    y <> z ->
    x <> z ->
    bcexec (bcccnot x y z) f = f[z |-> (f z ⊕ (f y && f x))].
Proof.
  intros. apply functional_extensionality; intro i. simpl. unfold update. bnauto.
Qed.

(*Here we define the wellformedness of bc circuit. *)
Inductive bcfresh : nat -> bccom -> Prop :=
| bcfresh_skip : forall q, q <> 0 -> bcfresh q bcskip 
     (* q <> 0 fits the requirement in SQIR, which is unnecessary in principle *)
| bcfresh_x : forall q n, q <> n -> bcfresh q (bcx n)
| bcfresh_swap : forall q m n, q <> m -> q <> n -> bcfresh q (bcswap m n)
| bcfresh_cont : forall q n p, q <> n -> bcfresh q p -> bcfresh q (bccont n p)
| bcfresh_seq  : forall q p1 p2, bcfresh q p1 -> bcfresh q p2 -> bcfresh q (p1; p2)
.

Inductive bc_well_formed : bccom -> Prop :=
| bcWF_skip : bc_well_formed bcskip
| bcWF_x : forall n, bc_well_formed (bcx n)
| bcWF_swap : forall m n, bc_well_formed (bcswap m n)
| bcWF_cont : forall n p,  bcfresh n p -> bc_well_formed p -> bc_well_formed (bccont n p)
| bcWF_seq : forall p1 p2, bc_well_formed p1 -> bc_well_formed p2 -> bc_well_formed (p1; p2)
.

Inductive bcWT (dim : nat) : bccom -> Prop :=
| bcWT_skip : dim > 0 -> bcWT dim bcskip
| bcWT_x : forall n, n < dim -> bcWT dim (bcx n)
| bcWT_swap : forall m n, m < dim -> n < dim -> m <> n -> bcWT dim (bcswap m n)
| bcWT_cont : forall n p, n < dim -> bcfresh n p -> bcWT dim p -> bcWT dim (bccont n p)
| bcWT_seq : forall p1 p2, bcWT dim p1 -> bcWT dim p2 -> bcWT dim (p1; p2)
.

Lemma bcWT_bc_well_formed :
  forall dim p,
    bcWT dim p -> bc_well_formed p.
Proof.
  intros. induction p; inversion H; subst; constructor.
  - easy.
  - apply IHp. easy.
  - apply IHp1. easy.
  - apply IHp2. easy.
Qed.

Lemma bcWT_enlarge :
  forall p dim dim',
    dim < dim' ->
    bcWT dim p ->
    bcWT dim' p.
Proof.
  induction p; intros; inversion H0; subst; constructor; try easy; try lia.
  - apply IHp with (dim := dim); easy.
  - apply IHp1 with (dim := dim); easy.
  - apply IHp2 with (dim := dim); easy.
Qed.

(* Implementation language to compile bc circuit to SQIR. *)
Fixpoint bc2ucom {dim} (p : bccom) : base_ucom dim :=
  match p with
  | bcskip => SKIP
  | bcx n => X n
  | bcswap m n => SWAP m n
  | bccont n (bcx m) => CNOT n m
  | bccont n p => control n (bc2ucom p)
  | bcseq p1 p2 => useq (bc2ucom p1) (bc2ucom p2)
  end.

Local Transparent ID CNOT X SWAP. 
Lemma bcfresh_is_fresh :
  forall q p {dim},
    bcfresh q p -> @is_fresh _ dim q (bc2ucom p).
Proof.
  intros. induction p; simpl; inversion H.
  - apply fresh_app1. easy.
  - apply fresh_X. easy.
  - unfold SWAP. repeat constructor; easy.
  - apply IHp in H4.
    destruct p; try (apply fresh_control; easy).
    inversion H4; subst.
    constructor; easy.
  - apply IHp1 in H3. apply IHp2 in H4. apply fresh_seq; easy.
Qed.

Lemma bcWT_uc_well_typed :
  forall p {dim},
    bcWT dim p -> @uc_well_typed _ dim (bc2ucom p).
Proof.
  intros. induction p; simpl; inversion H.
  - constructor. easy.
  - apply uc_well_typed_X. easy.
  - apply uc_well_typed_SWAP. easy.
  - apply IHp in H4.
    destruct p; try (apply bcfresh_is_fresh with (dim := dim) in H3; apply uc_well_typed_control; easy).
    inversion H3; inversion H4; subst.
    constructor; easy.
  - apply IHp1 in H2. apply IHp2 in H3. apply WT_seq; easy.
Qed.
Local Opaque ID CNOT X SWAP.

Lemma bcfresh_bcexec_irrelevant :
  forall p q f,
    bcfresh q p ->
    bcexec p f q = f q.
Proof.
  induction p; intros.
  - easy.
  - inversion H; subst. simpl. apply update_index_neq. lia.
  - inversion H; subst. simpl. rewrite 2 update_index_neq by lia. reflexivity.
  - inversion H; subst. apply IHp with (f := f) in H4. simpl. destruct (f n); easy.
  - inversion H; subst. apply IHp1 with (f := f) in H3. apply IHp2 with (f := bcexec p1 f) in H4. simpl.
    rewrite H4. rewrite H3. easy.
Qed.

Lemma bc2ucom_correct :
  forall dim p f,
    dim > 0 ->
    bcWT dim p ->
    (uc_eval (bc2ucom p)) × (f_to_vec dim f) = f_to_vec dim (bcexec p f).
Proof.
  intros dim p. induction p; intros; simpl.
  - rewrite denote_SKIP. Msimpl. easy. easy.
  - apply f_to_vec_X. inversion H0. easy.
  - inversion H0. apply f_to_vec_SWAP; easy.
  - inversion H0. assert (WT := H5). assert (FS := H4).
    apply bcfresh_is_fresh with (dim := dim) in H4. apply bcWT_uc_well_typed in H5.
    assert (G: (uc_eval (control n (bc2ucom p))) × f_to_vec dim f
               = f_to_vec dim (if f n then bcexec p f else f)). {
      rewrite control_correct; try easy.
      destruct (f n) eqn:Efn.
      + rewrite Mmult_plus_distr_r.
        rewrite Mmult_assoc. rewrite IHp by easy.
        rewrite f_to_vec_proj_neq, f_to_vec_proj_eq; try easy.
        Msimpl. easy.
        rewrite bcfresh_bcexec_irrelevant; easy.
        rewrite Efn. easy.
      + rewrite Mmult_plus_distr_r.
        rewrite Mmult_assoc. rewrite IHp by easy.
        rewrite f_to_vec_proj_eq, f_to_vec_proj_neq; try easy.
        Msimpl. easy.
        rewrite bcfresh_bcexec_irrelevant by easy.
        rewrite Efn. easy.
    }
    destruct p; try apply G.
    inversion WT; inversion FS; subst.
    rewrite f_to_vec_CNOT by easy.
    destruct (f n) eqn:Efn.
    simpl. rewrite xorb_true_r. easy.
    rewrite xorb_false_r. rewrite update_same; easy.
  - inversion H0. specialize (IHp1 f H H3).
    rewrite Mmult_assoc. rewrite IHp1.
    specialize (IHp2 (bcexec p1 f) H H4).
    easy.
Qed.

Fixpoint bcelim p :=
  match p with
  | bccont q p => match bcelim p with
                 | bcskip => bcskip
                 | p' => bccont q p'
                 end
  | bcseq p1 p2 => match bcelim p1, bcelim p2 with
                  | bcskip, p2' => p2'
                  | p1', bcskip => p1'
                  | p1', p2' => bcseq p1' p2'
                  end
  | _ => p
  end.

Inductive efresh : nat -> bccom -> Prop :=
| efresh_skip : forall q, efresh q bcskip 
| efresh_x : forall q n, q <> n -> efresh q (bcx n)
| efresh_swap : forall q m n, q <> m -> q <> n -> efresh q (bcswap m n)
| efresh_cont : forall q n p, q <> n -> efresh q p -> efresh q (bccont n p)
| efresh_seq  : forall q p1 p2, efresh q p1 -> efresh q p2 -> efresh q (p1; p2)
.

Inductive eWF : bccom -> Prop :=
| eWF_skip : eWF bcskip
| eWF_x : forall n, eWF (bcx n)
| eWF_swap : forall m n, eWF (bcswap m n)
| eWF_cont : forall n p,  efresh n p -> eWF p -> eWF (bccont n p)
| eWF_seq : forall p1 p2, eWF p1 -> eWF p2 -> eWF (p1; p2)
.

Inductive eWT (dim : nat) : bccom -> Prop :=
| eWT_skip : dim > 0 -> eWT dim bcskip
| eWT_x : forall n, n < dim -> eWT dim (bcx n)
| eWT_swap : forall m n, m < dim -> n < dim -> m <> n -> eWT dim (bcswap m n)
| eWT_cont : forall n p, n < dim -> efresh n p -> eWT dim p -> eWT dim (bccont n p)
| eWT_seq : forall p1 p2, eWT dim p1 -> eWT dim p2 -> eWT dim (p1; p2)
.

Lemma efresh_bcexec_irrelevant :
  forall p q f,
    efresh q p ->
    bcexec p f q = f q.
Proof.
  induction p; intros.
  - easy.
  - inversion H; subst. simpl. apply update_index_neq. lia.
  - inversion H; subst. simpl. rewrite 2 update_index_neq; try lia. easy.
  - inversion H; subst. apply IHp with (f := f) in H4. simpl. destruct (f n); easy.
  - inversion H; subst. apply IHp1 with (f := f) in H3. apply IHp2 with (f := bcexec p1 f) in H4. simpl.
    rewrite H4. rewrite H3. easy.
Qed.

Lemma bcfresh_efresh :
  forall p q,
    bcfresh q p -> efresh q p.
Proof.
  induction p; intros; inversion H; subst; constructor; try easy; [apply IHp | apply IHp1 | apply IHp2]; easy.
Qed.

Lemma bc_well_formed_eWF :
  forall p,
    bc_well_formed p -> eWF p.
Proof.
  induction p; intros; inversion H; subst; constructor; try easy; [apply bcfresh_efresh | apply IHp | apply IHp1 | apply IHp2]; easy.
Qed.

Lemma efresh_bcfresh :
  forall p q,
    bcelim p <> bcskip -> efresh q p -> bcfresh q (bcelim p).
Proof.
  induction p; intros; simpl.
  simpl in H. contradiction.
  inversion H0; subst. constructor; easy.
  inversion H0; subst. constructor; easy.
  simpl in *.
  destruct (bcelim p) eqn:Ep; try easy;
    try (inversion H0; subst; constructor; try easy; try (apply IHp; easy)).
  simpl in H. inversion H0; subst.
  destruct (bcelim p1) eqn:Ep1; destruct (bcelim p2) eqn:Ep2; try easy; 
    try (apply IHp2; easy);
    try (apply IHp1; easy);
    try (constructor; [apply IHp1 | apply IHp2]; easy).
Qed.

Lemma eWT_bcWT :
  forall p dim,
    bcelim p <> bcskip -> eWT dim p -> bcWT dim (bcelim p).
Proof.
  induction p; intros;
    try (inversion H0; subst; constructor; easy).
  assert (bcelim p <> bcskip).
  { intro. simpl in H. rewrite H1 in H. easy.
  }
  inversion H0; subst. apply efresh_bcfresh in H5; try easy. simpl in *.
  destruct (bcelim p) eqn:Ep; try easy;
    try (constructor; try easy; try (apply IHp; easy)).
  simpl in *. inversion H0; subst. 
  destruct (bcelim p1) eqn:Ep1; destruct (bcelim p2) eqn:Ep2; try easy; 
    try (apply IHp2; easy);
    try (apply IHp1; easy);
    try (constructor; [apply IHp1 | apply IHp2]; easy).
Qed.

Lemma eWT_eWF :
  forall p dim,
    eWT dim p -> eWF p.
Proof.
  induction p; intros; inversion H; subst; constructor; try easy;
    try (apply IHp with (dim := dim); easy).
  apply IHp1 with (dim := dim); easy.
  apply IHp2 with (dim := dim); easy.
Qed.

Lemma bcelim_invariant :
  forall p f,
    bcexec p f = bcexec (bcelim p) f.
Proof.
  induction p; intros; try (simpl; easy).
  simpl.
  destruct (bcelim p) eqn:Ep; try (simpl in *; rewrite IHp; bnauto).
  simpl in *.
  destruct (bcelim p1) eqn:Ep1; destruct (bcelim p2) eqn:Ep2; rewrite IHp1; rewrite IHp2; easy.
Qed.

Lemma bc2ucom_eWT_variant :
  forall p dim f,
    dim > 0 ->
    eWT dim p ->
    uc_eval (bc2ucom (bcelim p)) × f_to_vec dim f = f_to_vec dim (bcexec p f).
Proof.
  intros. rewrite bcelim_invariant.
  destruct (bcelim p) eqn:Ep;
   try (apply bc2ucom_correct; try easy; rewrite <- Ep; apply eWT_bcWT; try easy; rewrite Ep; easy). 
  simpl. rewrite denote_SKIP by easy. Msimpl. easy.
Qed.

(* Define bcinv op. For any bc_seq op, inv means to reverse the order. *)
Fixpoint bcinv p :=
  match p with
  | bccont n p => bccont n (bcinv p)
  | bcseq p1 p2 => bcinv p2; bcinv p1
  | _ => p
  end.

Lemma bcinv_involutive :
  forall p,
    bcinv (bcinv p) = p.
Proof.
  induction p; simpl; try easy.
  - rewrite IHp. easy.
  - rewrite IHp1, IHp2. easy.
Qed.

Lemma efresh_bcinv :
  forall p q,
    efresh q p ->
    efresh q (bcinv p).
Proof.
  induction p; intros; inversion H; simpl; subst; try easy.
  - apply IHp in H4. constructor; easy.
  - apply IHp1 in H3. apply IHp2 in H4. constructor; easy.
Qed.

Lemma bcfresh_bcinv :
  forall p q,
    bcfresh q p ->
    bcfresh q (bcinv p).
Proof.
  induction p; intros; inversion H; simpl; subst; try easy.
  - apply IHp in H4. constructor; easy.
  - apply IHp1 in H3. apply IHp2 in H4. constructor; easy.
Qed.

Lemma eWF_bcinv :
  forall p,
    eWF p ->
    eWF (bcinv p).
Proof.
  induction p; intros; inversion H; subst; simpl; constructor.
  - apply efresh_bcinv. easy.
  - apply IHp. easy.
  - apply IHp2. easy.
  - apply IHp1. easy.
Qed.

Lemma eWT_two_bcinv :
  forall p dim,
    eWT dim p ->
    eWT dim (bcinv (bcinv p)).
Proof.
  induction p; intros; inversion H; subst; simpl; constructor.
  all: try lia.
  - apply efresh_bcinv. apply efresh_bcinv. assumption.
  - apply IHp. easy.
  - apply IHp1. easy.
  - apply IHp2. easy.
Qed.

Lemma bc_well_formed_bcinv :
  forall p,
    bc_well_formed p ->
    bc_well_formed (bcinv p).
Proof.
  induction p; intros; inversion H; subst; simpl; constructor.
  - apply bcfresh_bcinv. easy.
  - apply IHp. easy.
  - apply IHp2. easy.
  - apply IHp1. easy.
Qed.

Lemma bcinv_correct :
  forall p f,
    eWF p ->
    bcexec (bcinv p; p) f = f.
Proof.
  induction p; intros; simpl.
  - easy.
  - apply functional_extensionality; intros. unfold update.
    bdestruct (x =? n). rewrite Nat.eqb_refl. subst. destruct (f n); easy.
    easy.
  - apply functional_extensionality; intros. unfold update.
    bdestruct (x =? m); subst. 
    bdestruct (n =? m); subst.
    reflexivity.
    rewrite Nat.eqb_refl. 
    reflexivity.
    bdestruct (x =? n); subst.
    rewrite Nat.eqb_refl. 
    reflexivity.
    reflexivity.
  - inversion H; subst. destruct (f n) eqn:Efn.
    assert (efresh n (bcinv p)) by (apply efresh_bcinv; easy).
    rewrite efresh_bcexec_irrelevant by easy. rewrite Efn.
    specialize (IHp f H3). simpl in IHp. easy.
    rewrite Efn. easy.
  - inversion H; subst. simpl in IHp1, IHp2.
    specialize (IHp1 (bcexec (bcinv p2) f) H2). rewrite IHp1.
    apply IHp2. easy.
Qed.

Lemma bcinv_correct_bc_well_formed :
  forall p f,
    bc_well_formed p ->
    bcexec (bcinv p; p) f = f.
Proof.
  intros. apply bcinv_correct. apply bc_well_formed_eWF. easy.
Qed.

Lemma bcinv_correct_rev :
  forall p f,
    eWF p ->
    bcexec (p; bcinv p) f = f.
Proof.
  intros. apply eWF_bcinv in H.
  apply bcinv_correct with (f := f) in H.
  rewrite bcinv_involutive in H. easy.
Qed.

Lemma bcinv_reverse :
  forall p f g,
    eWF p ->
    bcexec p f = g ->
    bcexec (bcinv p) g = f.
Proof.
  intros. specialize (bcinv_correct_rev p f H) as G. simpl in G. rewrite H0 in G. easy.
Qed.

Lemma bcinv_correct_bc_well_formed_rev :
  forall p f,
    bc_well_formed p ->
    bcexec (p; bcinv p) f = f.
Proof.
  intros. apply bcinv_correct_rev. apply bc_well_formed_eWF. easy.
Qed.

Lemma bcinv_eWT :
  forall p dim,
    eWT dim p ->
    eWT dim (bcinv p).
Proof.
  induction p; intros; inversion H; subst; simpl.
  all: constructor; try easy.
  apply efresh_bcinv. easy. apply IHp. easy.
  apply IHp2. easy. apply IHp1. easy.
Qed.

Lemma bccnot_eWT :
  forall x y dim,
    x <> y ->
    x < dim -> y < dim ->
    eWT dim (bccnot x y).
Proof.
  intros. unfold bccnot. constructor. easy. constructor. easy. constructor. easy.
Qed.

Lemma bccnot_eWF :
  forall x y,
    x <> y ->
    eWF (bccnot x y).
Proof.
  intros. unfold bccnot. constructor. constructor. easy. constructor.
Qed.

Lemma bcccnot_eWT :
  forall a b c dim,
    a <> b -> b <> c -> a <> c ->
    a < dim -> b < dim -> c < dim ->
    eWT dim (bcccnot a b c).
Proof.
  intros. repeat (try constructor; try lia).
Qed.

Lemma bcccnot_eWF :
  forall a b c,
    a <> b -> b <> c -> a <> c ->
    eWF (bcccnot a b c).
Proof.
  intros. repeat (try constructor; try lia).
Qed.

Lemma bcswap_eWT :
  forall x y dim,
    x < dim -> y < dim -> x <> y ->
    eWT dim (bcswap x y).
Proof.
  intros. constructor; assumption.
Qed.

Lemma bcswap_eWF :
  forall x y,
    eWF (bcswap x y).
Proof.
  intros. constructor.
Qed.

Lemma uc_eval_CNOT_control :
  forall n m dim,
    @uc_eval dim (CNOT n m) = @uc_eval dim (control n (bc2ucom (bcx m))).
Proof.
  intros. rewrite denote_cnot. simpl. rewrite control_ucom_X. easy.
Qed.

Lemma bc2ucom_bcelim :
  forall p dim f,
    dim > 0 ->
    eWT dim p ->
    uc_eval (bc2ucom (bcelim p)) × f_to_vec dim f = f_to_vec dim (bcexec p f).
Proof.
  intros. apply bc2ucom_eWT_variant; easy.
Qed.

Lemma eWT_uc_well_typed_bcelim :
  forall p dim,
    dim > 0 ->
    eWT dim p ->
    @uc_well_typed _ dim (bc2ucom (bcelim p)).
Proof.
  intros.
  destruct (bcelim p) eqn:Ep; rewrite <- Ep;
    try (apply bcWT_uc_well_typed; apply eWT_bcWT; try easy; rewrite Ep; easy; easy).
  rewrite Ep. simpl. apply uc_well_typed_ID. easy.
Qed.

(*
Definition csplit (p : bccom) :=
  match p with
  | bccont n (p1; p2) => bccont n p1; bccont n p2
  | _ => p
  end.

Lemma bc2ucom_csplit :
  forall p dim,
    bcWT dim p ->
    uc_eval (@bc2ucom dim (csplit p)) = uc_eval (@bc2ucom dim p).
Proof.
  intros. destruct p; try easy.
  destruct p; try easy.
  simpl. inversion H; subst.
  inversion H3; inversion H4; subst.
  destruct p1 eqn:Ep1; destruct p2 eqn:Ep2; try easy;
    try inversion H6; try inversion H7; try inversion H10; try inversion H11; subst;
      repeat rewrite uc_eval_CNOT_control; easy.
Qed.

Lemma uc_well_typed_csplit :
  forall p dim,
    bcWT dim p ->
    uc_well_typed (@bc2ucom dim (csplit p)).
Proof.
  intros. assert (H1 := H).
  apply bcWT_uc_well_typed in H1.
  destruct p; try easy.
  destruct p; try easy.
  simpl. inversion H; subst.
  inversion H4; inversion H5; subst.
  destruct p1 eqn:Ep1; destruct p2 eqn:Ep2; try easy;
    try inversion H7; try inversion H8; try inversion H11; try inversion H12; subst;
      constructor;
      try (apply uc_well_typed_CNOT; easy);
      apply bcfresh_is_fresh with (dim := dim) in H7; apply bcfresh_is_fresh with (dim := dim) in H8;
        apply bcWT_uc_well_typed with (dim := dim) in H11; apply bcWT_uc_well_typed with (dim := dim) in H12;
          apply uc_well_typed_control; easy.
Qed.
*)

Fixpoint bygatectrl n c :=
  match c with
  | c1; c2 => bygatectrl n c1; bygatectrl n c2
  | c => bccont n c
  end.

Lemma bcexec_bccont :
  forall c n f,
    efresh n c -> bcexec (bccont n c) f n = f n.
Proof.
  induction c; intros; simpl; bnauto.
  inversion H; subst. rewrite update_index_neq in Heqb0 by (apply neq_sym; easy). rewrite Heqb in Heqb0. easy. 
  inversion H; subst. rewrite update_index_neq in Heqb0 by (apply neq_sym; easy). rewrite Heqb in Heqb0. easy.
  inversion H; subst. do 2 rewrite update_index_neq in Heqb0 by (apply neq_sym; easy). rewrite Heqb in Heqb0. easy.
  inversion H; subst. rewrite efresh_bcexec_irrelevant in Heqb1 by easy. rewrite Heqb in Heqb1. easy.
  inversion H; subst. do 2 rewrite efresh_bcexec_irrelevant in Heqb0 by easy. rewrite Heqb in Heqb0. easy.
Qed.

Lemma bcexec_bccont_bcfresh :
  forall c n f,
    bcfresh n c -> bcexec (bccont n c) f n = f n.
Proof.
  intros. apply bcexec_bccont. apply bcfresh_efresh. easy.
Qed.

Lemma bygatectrl_correct :
  forall c n f,
    efresh n c -> bcexec (bygatectrl n c) f = bcexec (bccont n c) f.
Proof.
  induction c; intros;
    try (simpl; easy).
  inversion H; subst.
  simpl. rewrite IHc2 by easy.
  simpl. rewrite IHc1 by easy.
  rewrite bcexec_bccont by easy.
  simpl. destruct (f n) eqn:Ef; try easy.
Qed.

Lemma bygatectrl_correct_bcfresh :
  forall c n f,
    bcfresh n c -> bcexec (bygatectrl n c) f = bcexec (bccont n c) f.
Proof.
  intros. apply bygatectrl_correct. apply bcfresh_efresh. easy.
Qed.

Lemma eWF_bygatectrl :
  forall c n,
    eWF (bccont n c) -> eWF (bygatectrl n c).
Proof.
  induction c; intros;
    try (simpl; easy).
  inversion H; subst. inversion H2; subst. inversion H3; subst.
  simpl. constructor.
  apply IHc1. constructor; easy.
  apply IHc2. constructor; easy.
Qed.

Lemma eWT_bygatectrl :
  forall c n dim,
    eWT dim (bccont n c) -> eWT dim (bygatectrl n c).
Proof.
  induction c; intros;
    try (simpl; easy).
  inversion H; subst. inversion H3; subst. inversion H4; subst.
  simpl. constructor.
  apply IHc1. constructor; easy.
  apply IHc2. constructor; easy.
Qed.

Lemma bygatectrl_bcinv :
  forall c n, bygatectrl n (bcinv c) = bcinv (bygatectrl n c).
Proof.
  intros. induction c; simpl; try easy.
  rewrite IHc1, IHc2. easy.
Qed.

Fixpoint map_bccom (f : nat -> nat) (bc : bccom) : bccom :=
  match bc with
  | bcskip => bcskip
  | bcx a => bcx (f a)
  | bcswap a b => bcswap (f a) (f b)
  | bccont a bc1 => bccont (f a) (map_bccom f bc1)
  | bcseq bc1 bc2 => bcseq (map_bccom f bc1) (map_bccom f bc2)
  end.

Lemma map_qubits_bcfresh : forall k q (bc : bccom),
  (q < k)%nat ->
  bcelim bc <> bcskip ->
  bcfresh q (map_bccom (fun i : nat => (k + i)%nat) (bcelim bc)).
Proof.
  intros k q bc Hq H.
  induction bc. simpl. 
  contradict H; reflexivity.
  1-2: simpl; constructor; lia.
  simpl. 
  destruct (bcelim bc) eqn:bce.
  contradict H.
  simpl. rewrite bce. reflexivity.
  1-4: simpl in *; constructor; try lia; apply IHbc; easy.
  simpl.
  destruct (bcelim bc1) eqn:bce1; destruct (bcelim bc2) eqn:bce2.
  contradict H.
  simpl. rewrite bce1, bce2. reflexivity.
  all: try (apply IHbc1; easy).
  all: try (apply IHbc2; easy).
  all: simpl; constructor.
  all: try (apply IHbc1; easy).
  all: try (apply IHbc2; easy).
Qed.

