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
  | tm_let   : tm -> ty -> tm -> tm
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
  | tm_let t1 T t2 => tm_let (shift_f c f t1) T (shift_f (S c) f t2)
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
  | tm_let t1 T t2 => tm_let (subst n s t1) T (subst (S n) (shift_up 1 s) t2)
  | tm_num nu => tm_num nu
  | tm_binop op t1 t2 => tm_binop op (subst n s t1) (subst n s t2)
  end.

Inductive step : tm -> tm -> Prop :=
  | ST_AppStep : forall t1 t1' t2,
      step t1 t1' ->
      step (tm_app t1 t2) (tm_app t1' t2)
  | ST_AppSub : forall T t1 t2,
      step (tm_app (tm_abs T t1) t2) (shift_down (subst 0 (shift_up 1 t2) t1))
  | ST_Let : forall t1 T1 t2,
      step (tm_let t1 T1 t2) (shift_down (subst 0 (shift_up 1 t1) t2))
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
      has_type ctx (tm_app e1 e2) T2
  | T_Let : forall ctx t1 T1 t2 T2,
      (* has_type ctx t1 T1 -> *)
      has_type (cons T1 ctx) t2 T2 ->
      has_type ctx (tm_let t1 T2 t2) T2.

Theorem preservation : ~ forall t1 t2 T,
  has_type nil t1 T ->
  step t1 t2 ->
  has_type nil t2 T.
Proof.
  intros H.
  remember (Ty_Arrow (Ty_Arrow Ty_Num Ty_Num) Ty_Num) as T.
  remember (tm_let (tm_abs Ty_Num (tm_var 0)) T (tm_var 0)) as t1.
  remember (tm_abs Ty_Num (tm_var 0)) as t2.

  assert (Ht1 : has_type nil t1 T).
    { subst. eapply T_Let.
      - apply T_Var. simpl. reflexivity. }
  assert (Hs : step t1 t2).
    { subst. apply ST_Let. }

  specialize (H t1 t2 T Ht1 Hs). subst.
  inversion H.
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
  - right. eexists. apply ST_Let.
Qed.
