From Coq Require Import Strings.String Logic.FunctionalExtensionality.
Require Import PeanoNat.
Require Import Lia.

Inductive ty : Type :=
  | Ty_Num  : ty
  | Ty_Arrow : ty -> ty -> ty.

Inductive bin_op : Type :=
  | bop_add
  | bop_minus
  | bop_mul
  | bop_div.

Definition eval_bin_op (op : bin_op) (l : nat) (r : nat) :=
  match op with
  | bop_add => l + r
  | bop_minus => l - r
  | bop_mul => l * r
  | bop_div => Nat.div l r
  end.

Inductive tm : Type :=
  | tm_var   : nat -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : ty -> tm -> tm
  | tm_num   : nat -> tm
  | tm_binop : bin_op -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_abs : forall T2 t1,
      value (tm_abs T2 t1)
  | v_num : forall n,
      value (tm_num n).

Fixpoint shift_f (c : nat) (f : nat -> nat) (t : tm) :=
  match t with
  | tm_var n => tm_var (if Nat.leb c n then f n else n)
  | tm_app t1 t2 => tm_app (shift_f c f t1) (shift_f c f t2)
  | tm_abs T t1 => tm_abs T (shift_f (S c) f t1)
  | tm_num n => tm_num n
  | tm_binop op t1 t2 => tm_binop op (shift_f c f t1) (shift_f c f t2)
  end.

Definition shift_up (s : nat) (t : tm) := shift_f 0 (plus s) t.

Definition shift_down (t : tm) := shift_f 0 pred t.

Fixpoint subst (n : nat) (s : tm) (t : tm) :=
  match t with
  | tm_var v => if Nat.eqb v n then s else tm_var v
  | tm_app t1 t2 => tm_app (subst n s t1) (subst n s t2)
  | tm_abs T t1 => tm_abs T (subst (S n) (shift_up 1 s) t1)
  | tm_num nu => tm_num nu
  | tm_binop op t1 t2 => tm_binop op (subst n s t1) (subst n s t2)
  end.

Definition bind_top (s : tm) (t : tm) :=
  shift_down (subst 0 (shift_up 1 s) t).

Inductive step : tm -> tm -> Prop :=
  | ST_AppStep : forall t1 t1' t2,
      step t1 t1' ->
      step (tm_app t1 t2) (tm_app t1' t2)
  | ST_AppSub : forall T t1 t2,
      step (tm_app (tm_abs T t1) t2) (bind_top t2 t1)
  | ST_BinopL : forall op t1 t1' t2,
      step t1 t1' ->
      step (tm_binop op t1 t2) (tm_binop op t1' t2)
  | ST_BinopR : forall op v1 t2 t2',
      value v1 ->
      step t2 t2' ->
      step (tm_binop op v1 t2) (tm_binop op v1 t2')
  | ST_BinopOp : forall op n1 n2,
      step (tm_binop op (tm_num n1) (tm_num n2)) (tm_num (eval_bin_op op n1 n2)).

Definition context := list ty.

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Num : forall ctx n,
      has_type ctx (tm_num n) Ty_Num
  | T_BinOp : forall ctx op el er,
      has_type ctx el Ty_Num ->
      has_type ctx er Ty_Num ->
      has_type ctx (tm_binop op el er) Ty_Num
  | T_Var : forall ctx x T,
      List.nth_error ctx x = Some T ->
      has_type ctx (tm_var x) T
  | T_Abs : forall ctx T1 e T2,
      has_type (cons T1 ctx) e T2 ->
      has_type ctx (tm_abs T1 e) (Ty_Arrow T1 T2)
  | T_App : forall ctx e1 e2 T1 T2,
      has_type ctx e1 (Ty_Arrow T1 T2) ->
      has_type ctx e2 T1 ->
      has_type ctx (tm_app e1 e2) T2.

Lemma shiftf_plus_add : forall t c p0 p1,
  shift_f c (plus p0) (shift_f c (plus p1) t) = shift_f c (plus (p0+p1)) t.
Proof.
  induction t; intros c p0 p1; simpl.
  - destruct (Nat.leb_spec c n).
    + assert (Hl: c <= p1 + n). { lia. } rewrite <- Nat.leb_le in Hl. rewrite Hl.
      f_equal. lia.
    + rewrite <- Nat.leb_gt in H. rewrite H. reflexivity.
  - f_equal.
    + apply IHt1.
    + apply IHt2.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - f_equal.
    + apply IHt1.
    + apply IHt2.
Qed.

Lemma shift_f_pred_up : forall t cp c n,
  cp <= c + n ->
  c <= cp ->
  shift_f cp pred (shift_f c (plus (S n)) t) = shift_f c (plus n) t.
Proof.
  induction t; intros cp c pn Hlcp Hlc; simpl.
  - destruct (Nat.leb_spec c n).
    + assert (Hln: cp <= S (pn + n)). { lia. }
      rewrite <- Nat.leb_le in Hln. rewrite Hln. reflexivity.
    + assert (Hgcp: n < cp). { lia. } rewrite <- Nat.leb_gt in Hgcp. rewrite Hgcp.
      reflexivity.
  - f_equal.
    + apply IHt1; auto.
    + apply IHt2; auto.
  - f_equal. apply IHt; lia.
  - reflexivity.
  - f_equal.
    + apply IHt1; auto.
    + apply IHt2; auto.
Qed.

Lemma weakening_pref : forall pctx wctx ctx t T,
  has_type (List.app pctx ctx) t T ->
  has_type (List.app pctx (List.app wctx ctx))
    (shift_f (List.length pctx) (plus (List.length wctx)) t) T.
Proof.
  intros pctx wctx ctx t T Ht.
  generalize dependent wctx.
  remember (List.app pctx ctx) as ctxT.
  generalize dependent ctx. generalize dependent pctx.
  induction Ht; intros pctx tctx Ectx wctx; subst; simpl.
  - apply T_Num.
  - apply T_BinOp.
    + apply IHHt1. reflexivity.
    + apply IHHt2. reflexivity.
  - apply T_Var. rewrite <- H.
    destruct (Nat.leb_spec (List.length pctx) x).
    + rewrite List.nth_error_app2; [| lia].
      rewrite List.nth_error_app2; [| lia].
      rewrite List.nth_error_app2; [| lia].
      f_equal. lia.
    + rewrite List.nth_error_app1; [| assumption].
      rewrite List.nth_error_app1; [| assumption].
      reflexivity.
  - apply T_Abs.
    specialize (IHHt (cons T1 pctx) tctx eq_refl wctx).
    simpl in IHHt. exact IHHt.
  - apply T_App with T1.
    + apply IHHt1. reflexivity.
    + apply IHHt2. reflexivity.
Qed.

Lemma weakening : forall pctx ctx t T,
  has_type ctx t T ->
  has_type (List.app pctx ctx) (shift_up (List.length pctx) t) T.
Proof.
  intros.
  apply (weakening_pref nil). simpl. assumption.
Qed.

Lemma subst_preserve_typing : forall pctx ctx t1 T1 t2 T2,
  has_type ctx t1 T1 ->
  has_type (List.app pctx (cons T1 ctx)) t2 T2 ->
  has_type (List.app pctx ctx)
    (shift_f (List.length pctx) pred 
      (subst (List.length pctx) (shift_up (S (List.length pctx)) t1) t2))
    T2.
Proof.
  intros pctx ctx t1 T1 t2 T2 Htt1 Htt2.
  remember (List.app pctx (cons T1 ctx)) as ctx2.
  generalize dependent Htt1. generalize dependent T1. generalize dependent t1.
  generalize dependent pctx. generalize dependent ctx.
  induction Htt2; intros ctx1 pctx t1 Tt1 Ectx Htt1; subst; simpl.
  - apply T_Num.
  - apply T_BinOp; eauto.
  - destruct (Nat.eqb_spec x (List.length pctx)).
    + subst x.
      rewrite List.nth_error_app in H. rewrite Nat.ltb_irrefl in H.
      rewrite Nat.sub_diag in H. simpl in H. injection H as Et. subst T.
      
      unfold shift_up. rewrite shift_f_pred_up.
      * apply weakening. assumption.
      * apply le_n.
      * apply le_0_n.
    + simpl. apply T_Var. rewrite <- H.
      destruct (Nat.leb_spec x (List.length pctx)).
      * assert (Hlt : x < List.length pctx). { lia.  }
        rewrite <- Nat.leb_gt in Hlt. rewrite Hlt.

        rewrite List.nth_error_app1; [| lia].
        rewrite List.nth_error_app1; [| lia].
        reflexivity.
      * assert (Eb : Nat.leb (List.length pctx) x = true). 
          { apply Nat.leb_le. apply Nat.lt_le_incl. assumption. }
        rewrite Eb.

        rewrite List.nth_error_app2; [| lia].
        rewrite List.nth_error_app2; [| lia].
        destruct x. { lia. }
        simpl. destruct (List.length pctx).
          { rewrite Nat.sub_0_r. reflexivity. }
          { assert (E: S (x - S n0) = x - n0). { lia. }
            rewrite <- E. simpl. reflexivity. }
  - apply T_Abs. 
    specialize (IHHtt2 ctx1 (cons T1 pctx) t1 Tt1). simpl in IHHtt2.
    specialize (IHHtt2 eq_refl Htt1).
    unfold shift_up in *. rewrite shiftf_plus_add. simpl. assumption.
  - eapply T_App.
    + eapply IHHtt2_1; eauto.
    + eapply IHHtt2_2; eauto.
Qed.

Lemma bind_top_preserve_typing : forall ctx t1 T1 t2 T2,
  has_type ctx t1 T1 ->
  has_type (cons T1 ctx) t2 T2 ->
  has_type ctx (bind_top t1 t2) T2.
Proof.
  intros ctx t1 T1 t2 T2 Htt1 Htt2. unfold bind_top.
  specialize (subst_preserve_typing nil _ _ _ _ _ Htt1 Htt2) as Hst.
  simpl in Hst. apply Hst.
Qed.

Theorem preservation : forall t1 t2 T,
  has_type nil t1 T ->
  step t1 t2 ->
  has_type nil t2 T.
Proof.
  remember nil as Gamma.
  intros t1 t2 T Ht. generalize dependent t2.
  induction Ht; subst; intros t' Hs.
  - inversion Hs.
  - inversion Hs; subst.
    + apply T_BinOp.
      * apply (IHHt1 eq_refl). assumption.
      * assumption.
    + apply T_BinOp.
      * assumption.
      * apply (IHHt2 eq_refl). assumption.
    + apply T_Num.
  - rewrite List.nth_error_nil in H. discriminate H.
  - inversion Hs.
  - inversion Hs; subst.
    + eapply T_App.
      * apply (IHHt1 eq_refl). assumption.
      * assumption.
    + inversion Ht1. subst.
      eapply bind_top_preserve_typing; eauto.
Qed.

Lemma canonical_value_num : forall t,
  has_type nil t Ty_Num ->
  value t ->
  exists n, t = tm_num n.
Proof.
  intros t Ht Hv.
  destruct Hv.
  - inversion Ht.
  - exists n. reflexivity.
Qed.

Lemma canonical_value_abs : forall t T1 T2,
  has_type nil t (Ty_Arrow T1 T2) ->
  value t ->
  exists t1, t = tm_abs T1 t1.
Proof.
  intros t T1 T2 Ht Hv.
  destruct Hv.
  - inversion Ht; subst. exists t1. reflexivity.
  - inversion Ht.
Qed.
      
Theorem progress : forall t T,
  has_type nil t T ->
  value t \/ exists t', step t t'.
Proof.
  intros t T Ht. remember nil as ctx.
  induction Ht; subst ctx.
  - left. apply v_num.
  - right. specialize (IHHt2 eq_refl). specialize (IHHt1 eq_refl).
    destruct IHHt1 as [Hvt1 | [t1' Hst1]].
    + destruct IHHt2 as [Hvt2 | [t2' Hst2]].
      * destruct (canonical_value_num _ Ht1 Hvt1) as [v1 Ev1].
        destruct (canonical_value_num _ Ht2 Hvt2) as [v2 Ev2].
        subst el er. exists (tm_num (eval_bin_op op v1 v2)).
        apply ST_BinopOp.
      * exists (tm_binop op el t2'). apply ST_BinopR; assumption.
    + exists (tm_binop op t1' er). apply ST_BinopL; assumption.
  - rewrite List.nth_error_nil in H. discriminate H.
  - left. apply v_abs.
  - right. specialize (IHHt2 eq_refl). specialize (IHHt1 eq_refl).
    destruct IHHt1 as [Hvt1 | [t1' Hst1]].
    + destruct (canonical_value_abs _ _ _ Ht1 Hvt1) as [t11 Et11]. subst e1.
      eexists. apply ST_AppSub.
    + exists (tm_app t1' e2). apply ST_AppStep. assumption.
Qed.
