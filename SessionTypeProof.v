Require Import Reals.
Require Import Psatz.
Require Import Complex.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat Permutation. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import OQASM.
Require Import Classical_Prop.
Require Import MathSpec.
Require Import QWhileSyntax.
Require Import SessionDef.
Require Import SessionKind.
Require Import SessionSem.
Require Import SessionType.
(**********************)
(** Unitary Programs **)
(**********************)

Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Declare Scope pexp_scope.
Delimit Scope pexp_scope with pexp.
Local Open Scope pexp_scope.
Local Open Scope nat_scope.

Inductive env_state_eq : type_map -> qstate ->  Prop :=
    env_state_eq_empty : env_state_eq nil nil
  | env_state_eq_many : forall s t a l1 l2, env_state_eq l1 l2 -> type_state_elem_same t a -> env_state_eq ((s,t)::l1) ((s,a)::l2).

Definition qstate_wt {rmax} S := forall s s' m bl, @find_state rmax S s (Some (s',Cval m bl)) -> m > 0.

Lemma find_env_state : forall s s' t T S, env_state_eq T S -> @find_env se_type T s (Some (s++s',t))
       -> (exists a, @find_env state_elem S s (Some (s++s',a)) /\ type_state_elem_same t a).
Proof.
  intros.
  remember (Some (s ++ s', t)) as q.
  generalize dependent S.
  induction H0.
  easy. intros. inv Heqq. inv H0. exists a.
  split. apply find_env_many_1. easy. easy.
  intros. inv H1.
  assert (Some (y ++ s', t) = Some (y ++ s', t)) by auto.
  apply IHfind_env with (S0 := l2) in H1. destruct H1 as [a' [X1 X2]].
  exists a'. split. apply find_env_many_2. auto. auto. auto. auto.
Qed.

(*TODO: Le Chang, additional theorem. *)
Lemma env_state_eq_app: forall S a1 a2, env_state_eq (a1++a2) S
      -> exists b1 b2, env_state_eq (a1++a2) (b1++b2) /\ S = b1 ++ b2 /\ length b1 = length a1.
Proof.
  intros. remember (a1++a2) as S1.
  generalize dependent a1.
  generalize dependent a2.
  induction H. intros. symmetry in HeqS1. apply app_eq_nil in HeqS1. inv HeqS1.
  exists nil,nil. split. simpl. constructor. simpl. easy.
  intros. destruct a1. simpl in *. destruct a2. inv HeqS1.
  inv HeqS1.
  specialize (IHenv_state_eq a2 nil).
  simpl in *. assert (a2 = a2) by easy. apply IHenv_state_eq in H1.
  destruct H1 as [b1 [b2 [X1 [X2 X3]]]].
  exists b1. exists ((s,a)::b2).
  rewrite length_zero_iff_nil in X3 ; subst. simpl in *.
  split. constructor. easy. easy. easy.
  inv HeqS1.
  specialize (IHenv_state_eq a2 a1).
  assert (a1 ++ a2 = a1 ++ a2) by easy. apply IHenv_state_eq in H1.
  destruct H1 as [b1 [b2 [X1 [X2 X3]]]].
  exists ((s, a)::b1). exists b2.
  split. simpl. constructor. easy. easy.
  split. simpl. rewrite X2. easy. simpl. rewrite X3. easy.
Qed.

Lemma env_state_eq_same_length: forall a1 a2 b1 b2, length a1 = length b1
        -> env_state_eq (a1++a2) (b1++b2) -> env_state_eq a1 b1 /\ env_state_eq a2 b2.
Proof.
  induction a1;intros;simpl in *.
  symmetry in H. apply length_zero_iff_nil in H as X1; subst. simpl in *.
  split. constructor. easy. destruct b1. simpl in *. easy.
  simpl in *. inv H.
  inv H0.
  destruct (IHa1 a2 b1 b2 H2 H4) as [X1 X2].
  split. constructor; easy. easy.
Qed.

Lemma env_state_eq_app_join: forall a1 a2 b1 b2, env_state_eq a1 b1 -> env_state_eq a2 b2 -> env_state_eq (a1++a2) (b1 ++ b2).
Proof.
  induction a1; intros; simpl in *.
  inv H. simpl. easy.
  inv H. simpl in *. constructor. apply IHa1; easy. easy.
Qed.

Lemma env_state_eq_app_comm: forall a1 a2 b1 b2, length a1 = length b1 -> env_state_eq (a1 ++ a2) (b1++b2) -> env_state_eq (a2 ++ a1) (b2++b1).
Proof.
  intros. remember (a1 ++ a2) as l1. remember (b1 ++ b2) as l2.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent b1.
  generalize dependent b2.
  induction H0. intros.
  symmetry in Heql1. symmetry in Heql2.
  apply app_eq_nil in Heql1. apply app_eq_nil in Heql2. inv Heql1. inv Heql2.
  simpl. constructor.
  intros.
  destruct a1. simpl in *. symmetry in H1. rewrite length_zero_iff_nil in H1; subst. simpl in *.
  destruct b2. inv Heql2. inv Heql2. repeat rewrite app_nil_r. constructor; easy.
  simpl in *. inv Heql1.
  destruct b1. simpl in *. lia. simpl in *. inv Heql2.
  assert (env_state_eq (((s, t) :: a1) ++ a2) (((s, a) :: b1) ++ b2)). simpl.
  apply env_state_eq_many; try easy.
  apply env_state_eq_same_length in H2 as X1; try easy.
  apply env_state_eq_app_join; try easy.
Qed.
  
Lemma env_state_eq_trans: forall r T T' S, env_state_eq T S -> env_equiv T T' -> (exists S', @state_equiv r S S' /\ env_state_eq T' S').
Proof.
   intros. generalize dependent S. induction H0...
  - intros. exists S0. split. constructor. easy.
  - intros... 
    inv H. exists l2. split. constructor. easy.
  - intros. apply env_state_eq_app in H as X1.
    destruct X1 as [b1 [b2 [X1 [X2 X3]]]]; subst.
    exists (b2 ++ b1). split. apply state_comm. apply env_state_eq_app_comm; try easy.
  - intros.
Admitted.

(*TODO: Le Chang, us eht result in find_env_state. *)
Lemma find_type_state : forall s s' t r T S, env_state_eq T S -> find_type T s (Some (s++s',t))
       -> (exists S' a, @state_equiv r S S' /\ find_env S' s (Some (s++s',a)) /\ type_state_elem_same t a).
Proof.
  intros.  inv H0. 
  (* use the env_state_eq_trans.  *)
  specialize (find_env_state s s' t T S H) as X1.
Admitted.

Lemma find_type_state_1 : forall s s' t r T M S, env_state_eq T S -> find_type T s (Some (s++s',t))
       -> (exists a, @find_state r (M,S) s (Some (s++s',a)) /\ type_state_elem_same t a).
Proof.
  intros. apply find_type_state with (r := r) (S := S) in H0.
  destruct H0 as [S' [a [X1 [X2 X3]]]].
  exists a. split. apply find_qstate_rule with (S'0 := S'); try easy. apply X3. easy.
Qed.

(*TODO: Le Chang, please finish the proof.
  Should be easy, just have sub-lemma to induct on find_env. see what is its relation with up_state. *)
Lemma find_state_up_good {rmax}: forall S s s' v v', @find_state rmax S s (Some (s',v)) -> exists S', @up_state rmax S s v' S'.
Proof.
  intros. inv H.
Admitted.

Lemma find_state_up_good_1 {rmax}: forall S s s' v v', @find_state rmax S s (Some (s',v)) -> exists S', @up_state rmax S s' v' S'.
Proof.
  intros. inv H.
Admitted.

Lemma find_env_ch: forall T s s' t, find_env T s (Some (s',t)) -> (exists T', env_equiv T T' /\ find_env T' s (Some (s',CH))).
Proof.
 intros. remember (Some (s',t)) as a. induction H; subst. inv Heqa.
 inv Heqa.
 exists ((s',CH)::S).
 split. apply env_subtype.
 destruct t; constructor.
 constructor. easy.
 assert (Some (s', t) = Some (s', t)) by easy. apply IHfind_env in H1.
 destruct H1 as [T' [X1 X2]].
 exists ((x,v)::T').
 split.
 constructor. easy.
 apply find_env_many_2. easy. easy.
Qed.

Lemma find_type_ch : forall T1 s s' t, find_type T1 s (Some (s',t)) -> find_type T1 s (Some (s',CH)).
Proof.
  intros. inv H.
  specialize (find_env_ch S' s s' t H1) as X1. destruct X1 as [T' [X1 X2]].
  apply find_type_rule with (S := T1) in X2; try easy.
  apply env_equiv_trans with (T2 := S'); easy.
Qed.

Lemma pick_mea_exists {rmax}: forall T S t s' x n, @qstate_wt rmax S -> env_state_eq T (snd S) 
             -> find_type T ([(x,BNum 0,BNum n)]) (Some (([(x,BNum 0,BNum n)])++s',t)) -> 
          exists r v, @pick_mea rmax S x n (r,v).
Proof.
  intros.
  apply find_type_ch in H1.
  apply find_type_state with (r := rmax) (S := snd S) in H1 as X1.
  destruct X1 as [S' [a [X1 [X2 X3]]]].
  inv X3.
  assert (@find_state rmax S [(x, BNum 0, BNum n)] (Some ([(x, BNum 0, BNum n)] ++ s', Cval m bl))).
  destruct S. apply find_qstate_rule with (S'0 := S'); try easy.
  apply H in H2 as X3.
  assert (exists i, 0 <= i < m). exists 0. lia. destruct H3.
  remember (bl x0) as ra. destruct ra.
  exists (Cmod c). exists (a_nat2fb r n).
  apply pick_meas with (l := s') (m0 := m) (b := bl) (i := x0); try easy.
  easy.
Qed. 

Lemma mask_state_exists {rmax}: forall S x n r v,
             @pick_mea rmax S x n (r,v) ->
          exists S', @mask_state rmax ([(x,BNum 0,BNum n)]) v S S'.
Proof.
  intros. inv H.
  assert (ses_len ([(x, BNum 0, BNum n)])= Some n).
  unfold ses_len. destruct (get_core_ses ([(x, BNum 0, BNum n)])) eqn:eq1; simpl in *; try easy.
  inv eq1. simpl. assert (n - 0 + 0 = n) by lia. rewrite H. easy.
  remember (build_state_pars m n (a_nat2fb bl n) (to_sum_c m n (a_nat2fb bl n) b) b).
  destruct p.
  assert (build_state_ch n (a_nat2fb bl n) (Cval m b) = Some (Cval n0 p)).
  unfold build_state_ch. rewrite <- Heqp. easy.
  apply find_state_up_good with (v' := (Cval n0 p)) in H2 as X1.
  destruct X1 as [Sa X1].
  exists Sa.
  eapply mask_state_rule; auto. apply H2. apply H. apply H0. easy. 
Qed.

Definition kind_env_stack (env:aenv) (s:stack) : Prop :=
  forall x t, AEnv.MapsTo x (Mo t) env -> AEnv.In x s.

Definition kind_env_wf (env:aenv) : Prop :=
  forall x n, AEnv.MapsTo x (QT n) env -> n > 0.

Definition env_wf (env:type_map) : Prop :=
   forall x t, In (x,t) env -> simple_ses x.

Inductive env_state_eqv {r:nat} : type_map -> qstate ->  Prop :=
    env_state_eqv_rule : forall l1 l2 l1' l2', 
      env_equiv l1 l1' -> @state_equiv r l2 l2' -> env_state_eq l1' l2' -> env_state_eqv l1 l2.

Lemma env_state_equiv :
  forall rmax s t1 t2, @env_state_eqv rmax t1 s -> env_equiv t1 t2 -> (exists s1, @state_equiv rmax s s1 /\ @env_state_eqv rmax t2 s1).
  Proof. Admitted.

Lemma env_equiv_simple_type : forall T T', env_equiv T T' -> simple_tenv T -> simple_tenv T'.
Proof.
  intros. induction H; simpl in *. easy.
  unfold simple_tenv in *. intros. apply (H0 a b). simpl. right. easy.
  unfold simple_tenv in *. intros.
  apply (H0 a b). apply in_or_app. apply in_app_iff in H. destruct H. right. easy. left. easy.
  unfold simple_tenv in *. intros.
  simpl in H1. destruct H1. inv H1. apply (H0 a v). simpl. left. easy.
  apply (H0 a b). simpl. right. easy.
  unfold simple_tenv in *. intros.
  simpl in *. destruct H1. inv H1. apply (H0 a b). left. easy.
  assert (forall (a : session) (b : se_type),
               In (a, b) S -> simple_ses a).
  intros. apply (H0 a0 b0). right. easy.
  specialize (IHenv_equiv H2). apply (IHenv_equiv a b). easy.
Admitted.

Lemma find_env_simple: forall T l l' t, @find_env se_type T l (Some (l',t)) -> simple_tenv T -> simple_ses l'.
Proof.
  intros. remember (Some (l', t)) as a. induction H; subst; try easy.
  inv Heqa. unfold simple_tenv in *.
  apply (H0 l' t). simpl. left. easy.
  apply IHfind_env; try easy.
  unfold simple_tenv in *. intros. apply (H0 a b). simpl in *. right. easy.
Qed.

Lemma find_type_simple: forall T l l' t, find_type T l (Some (l',t)) -> simple_tenv T -> simple_ses l'.
Proof.
  intros. inv H. apply env_equiv_simple_type in H1; try easy. eapply (find_env_simple S' l l' t); try easy.
Qed.

Lemma simple_ses_app_l: forall l l', simple_ses (l++l') -> simple_ses l.
Proof.
  intros. induction l; try easy. constructor.
  inv H. constructor; try easy. apply IHl. easy.
Qed.

Lemma qstate_wt_eq : forall r W S S', @qstate_wt r (W,S) -> @state_equiv r S S' -> @qstate_wt r (W, S').
Proof.
  intros.
Admitted.


Lemma type_soundness : 
    forall e rmax t aenv s tenv tenv', @env_state_eq tenv (snd s) -> kind_env_stack aenv (fst s) ->
      @session_system rmax t aenv tenv e tenv' -> freeVarsNotCPExp aenv e -> @qstate_wt rmax s -> simple_tenv tenv ->
           e = PSKIP \/ (exists aenv' e' s', @qfor_sem rmax aenv' s e s' e' 
              /\ @qstate_wt rmax s' /\ (exists tenv'', @session_system rmax t aenv' tenv'' e' tenv')).
Proof.
  intros.
  generalize dependent s.
  induction H1; simpl in *; intros.
  specialize (env_equiv_simple_type T1 T2 H H4) as X1.
  specialize (IHsession_system H2 X1).
  specialize (env_state_eq_trans rmax T1 T2 (snd s0) H0 H) as X2.
  destruct X2 as [Sa [X2 X3]].
  specialize (IHsession_system (fst s0,Sa) X3 H3).
  destruct s0; simpl in *. eapply qstate_wt_eq with (S' := Sa) in H5; try easy.
  apply IHsession_system in H5. destruct H5. left. easy.
  right. destruct H5 as [aenv [ea [s' [X4 X5]]]].
  exists aenv, ea, s'. split. apply state_eq_sem with (f' := Sa); try easy. easy.
  left. easy.
  right. exists env. exists ((subst_pexp e x v)).
  exists s. apply let_sem_c; simpl in *; easy.
  right.
  exists env.
  exists e.
  unfold freeVarsNotCPExp in H2. simpl in H2.
  assert (freeVarsNotCAExp env a).
  unfold freeVarsNotCAExp. intros. apply (H2 x0); try easy.
  apply in_app_iff. left. easy.
  apply kind_aexp_class_empty in H1 as X2; subst.
  specialize (kind_env_stack_exist env (fst s) a H0 H6 H1) as X1.
  destruct X1.
  exists (update_cval s x x0). constructor. easy. right. easy.
 (* Let rule with measure. *)
  right. 
  apply (@pick_mea_exists rmax T s) in H5 as X1; try easy.
  destruct X1 as [r [cv X1]].
  apply mask_state_exists in X1 as X2. destruct X2 as [Sa X2].
  exists (AEnv.add x (Mo MT) env).
  exists e.
  exists (update_cval Sa x (r,cv)).
  eapply let_sem_q; eauto.
  right.
  apply find_type_ch in H6.
  exists env. exists PSKIP.
  apply find_type_state_1  with (r:= rmax) (M := fst s) (S := (snd s)) in H6 as X1; try easy.
  destruct X1 as [a [X1 X2]].
  inv X2. apply find_type_simple in H6 as X2; try easy.
  apply simple_ses_app_l in X2.
  apply (@eval_ch_exists rmax m env l n bl e) in H1 as X3; try easy.
  destruct X3 as [ba X3].
  apply find_state_up_good_1 with (v' := (Cval m ba)) in X1 as X4; try easy.
  destruct X4 as [S' X4].
  exists S'.
  assert ((fst s, snd s) = s). destruct s. simpl; easy.
  rewrite H7 in *.
  eapply appu_sem_ch. apply X1. apply X3. apply X4.
  right.
  specialize (find_type_state_1 ([a]) nil TNor rmax T (fst s) (snd s) H) as X1.
  rewrite app_nil_r in X1.
  destruct (X1 H6) as [a0 [X2 X3]].
  inv X3.
  apply find_state_up_good with (v' := (Hval (fun i => (update allfalse 0 (r i))))) in X2 as X4; try easy.
  destruct X4 as [S' X4].
  exists env,PSKIP,S'.
  rewrite <- surjective_pairing in *.
  eapply appsu_sem_h_nor. apply H5. apply X2. easy.
  right.
  specialize (find_type_state_1 ([a]) nil THad rmax T (fst s) (snd s) H) as X1.
  rewrite app_nil_r in X1.
  destruct (X1 H6) as [a0 [X2 X3]].
  inv X3.
  apply find_state_up_good with (v' := (Nval C1 (fun j => bl j 0))) in X2 as X4; try easy.
  destruct X4 as [S' X4].
  exists env,PSKIP,S'.
  rewrite <- surjective_pairing in *.
  eapply appsu_sem_h_had. apply H5. apply X2. easy.
  right.
  exists env,e,s. apply if_sem_ct; try easy.
  right.
  exists env,PSKIP,s. apply if_sem_cf; try easy.
  right.
  apply kind_env_stack_exist_bexp with (s := (fst s)) in H1 as X1; try easy.
  destruct X1 as [bv X1]. destruct bv.
  exists env,e,s. destruct s. apply if_sem_mt; try easy.
  exists env,PSKIP,s. destruct s. apply if_sem_mf; try easy.
  unfold freeVarsNotCBExp,freeVarsNotCPExp in *; simpl in *.
  intros. apply (H2 x); try easy.
  apply in_app_iff. left. easy.
  right.  
  assert (freeVarsNotCPExp env e).
  unfold freeVarsNotCPExp in *. intros.
  apply (H2 x); try easy. simpl in *.
  apply in_app_iff. right. easy.
  specialize (IHsession_system H H0 H7 H4).
  assert (e = PSKIP \/ e <> PSKIP).
  destruct e; try (right; easy).
  destruct H8;subst.
  exists env, PSKIP. exists s. apply if_sem_q_2.
  destruct IHsession_system; subst. easy.
  destruct H9 as [env' [e' [s' X1]]].
  
Admitted.

(*
  | if_sem_q_1 : forall aenv l l1 n n' s s' sa sa' sac b e e' m m' f f' fc fc' fa,
               type_bexp aenv b (QT n,l) -> @eval_bexp rmax aenv s b s' ->
                @find_state rmax s' l (Some (l++l1, Cval m f)) -> ses_len l1 = Some n' ->
                 mut_state 0 n n' (Cval (fst (grab_bool f m n)) (snd (grab_bool f m n))) fc ->
                @up_state rmax s' (l++l1) fc sa -> qfor_sem aenv sa e sa' e' -> e <> PSKIP ->
                 @find_state rmax sa' l1 (Some (l1, fc')) -> mut_state 0 n' n fc' (Cval m' f') ->
                assem_bool m m' n f f' fa -> @up_state rmax s (l++l1) (Cval (fst fa) (snd fa)) sac ->
                    qfor_sem aenv s (If b e) sac (If b e')



Lemma session_progress : 
    forall e rmax t aenv s tenv tenv1 tenv', @env_state_eq tenv (snd s) ->
      @env_equiv tenv tenv1 ->
      @session_system rmax t aenv tenv1 e tenv' ->
           e = PSKIP \/ (exists e' s1 s', @state_equiv rmax (snd s) s1 -> @qfor_sem rmax aenv (fst s,s1) e s' e').
Proof. Admitted.

*)



