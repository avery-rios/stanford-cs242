Require Import Strings.String.

Inductive value :=
    | v_true
    | v_false
    | v_number : nat -> value
    | v_string : string -> value
    | v_list : list value -> value
    | v_dict : list (string * value) -> value.

Inductive property : Type -> Type :=
    | p_empty : forall t, property t
    | p_lt : nat ->  property nat
    | p_gt : nat -> property nat
    | p_eq : forall t, t -> property t
    | p_and : forall t, property t -> property t -> property t
    | p_or : forall t, property t -> property t -> property t.

Inductive schema :=
    | s_number : property nat -> schema
    | s_string : property string -> schema
    | s_bool
    | s_list : nat -> schema -> schema
    | s_dict : list (string * schema) -> schema.

Inductive match_prop : forall (t : Type), t -> property t -> Prop :=
    | P_Empty : forall t n, match_prop t n (p_empty t)
    | P_Lt : forall n pn, n < pn -> match_prop nat n (p_lt pn)
    | P_Gt : forall n pn, n > pn -> match_prop nat n (p_gt pn)
    | P_Eq : forall t n, match_prop t n (p_eq t n)
    | P_And : forall t n p0 p1,
        match_prop t n p0 ->
        match_prop t n p1 ->
        match_prop t n (p_and t p0 p1)
    | P_Or0 : forall t n p0 p1,
        match_prop t n p0 ->
        match_prop t n (p_or t p0 p1)
    | P_Or1 : forall t n p0 p1,
        match_prop t n p1 ->
        match_prop t n (p_or t p0 p1).

Inductive val_matches : value -> schema -> Prop :=
    | VS_True : val_matches v_true s_bool 
    | VS_False : val_matches v_false s_bool
    | VS_Number : forall n p,
        match_prop nat n p ->
        val_matches (v_number n) (s_number p)
    | VS_String : forall s p,
        match_prop string s p ->
        val_matches (v_string s) (s_string p)
    | VS_List_Nil : forall s,
        val_matches (v_list nil) (s_list 0 s)
    | VS_List_Cons : forall h t s,
        val_matches h s ->
        val_matches (v_list t) (s_list 0 s) ->
        val_matches (v_list (h :: t)) (s_list 0 s)
    | VS_List_Cons_S : forall h t l s,
        val_matches h s ->
        val_matches (v_list t) (s_list l s) ->
        val_matches (v_list (h :: t)) (s_list (S l) s)
    | VS_Dict_Empty : forall vs,
        val_matches (v_dict vs) (s_dict nil)
    | VS_Dict_Cons : forall hk hv tv hs ts,
        val_matches hv hs ->
        val_matches (v_dict tv) (s_dict ts) ->
        val_matches (v_dict ((hk, hv) :: tv)) (s_dict ((hk, hs) :: ts)).

Inductive accessor :=
    | a_empty 
    | a_key : string -> accessor -> accessor 
    | a_index : nat -> accessor -> accessor 
    | a_pipe : accessor -> accessor.

Fixpoint next_accessor (a : accessor) : accessor :=
  match a with
  | a_empty => a_empty
  | a_key _ a => a
  | a_index _ a => a
  | a_pipe a_empty => a_empty
  | a_pipe a => a_pipe (next_accessor a)
  end.

Inductive accessor_step : accessor -> value -> accessor -> value -> Prop :=
    | E_Key_Eq : forall k a hv t,
        accessor_step 
            (a_key k a) (v_dict ((k, hv) :: t))
            a hv
    | E_Key_Next : forall k a a' hk hv t v',
        k <> hk ->
        accessor_step (a_key k a) (v_dict t) a' v' ->
        accessor_step (a_key k a) (v_dict ((hk, hv) :: t)) a' v'
    | E_Index_0 : forall a hv tv,
        accessor_step (a_index O a) (v_list (hv :: tv)) a hv
    | E_Index_S : forall i a hv tv a' v',
        accessor_step (a_index i a) (v_list tv) a' v' ->
        accessor_step (a_index (S i) a) (v_list (hv :: tv)) a' v'
    | E_Pipe_Nil : forall a,
        a <> a_empty ->
        accessor_step (a_pipe a) (v_list nil) (a_pipe (next_accessor a)) (v_list nil)
    | E_Pipe_Cons : forall a hv tv a' hv' tv',
        accessor_step a hv a' hv' ->
        accessor_step (a_pipe a) (v_list tv) (a_pipe a') (v_list tv') ->
        accessor_step
            (a_pipe a) (v_list (hv :: tv))
            (a_pipe a') (v_list (hv' :: tv'))
    | E_Pipe_Empty : forall l,
        accessor_step (a_pipe a_empty) (v_list l) a_empty (v_list l).

Inductive accessor_matches : accessor -> schema -> Prop :=
    | AS_Empty : forall s, accessor_matches a_empty s
    | AS_Key_Eq : forall hk a hs t,
        accessor_matches a hs ->
        accessor_matches (a_key hk a) (s_dict ((hk, hs) :: t))
    | AS_Key_Next : forall a k hk hs t,
        k <> hk ->
        accessor_matches (a_key k a) (s_dict t) ->
        accessor_matches (a_key k a) (s_dict ((hk, hs) :: t))
    | AS_Index_0 : forall a l s,
        accessor_matches a s ->
        accessor_matches (a_index 0 a) (s_list (S l) s)
    | AS_Index_S : forall i a l s,
        accessor_matches (a_index i a) (s_list l s) ->
        accessor_matches (a_index (S i) a) (s_list (S l) s)
    | AS_Pipe : forall a l s,
        accessor_matches a s ->
        accessor_matches (a_pipe a) (s_list l s).

Lemma accessor_empty_dec : forall a, a = a_empty \/ a <> a_empty.
Proof.
  destruct a; try solve [right; discriminate].
  left. reflexivity.
Qed.

Lemma step_matches : forall s a, 
    accessor_matches a s ->
    exists s',
      accessor_matches (next_accessor a) s' /\
      forall v v',
        val_matches v s ->
        accessor_step a v (next_accessor a) v' ->
        val_matches v' s'.
Proof.
  intros s a Ham. induction Ham.
  - simpl. exists s_bool. split.
    + apply AS_Empty.
    + intros v v' _ Hs. inversion Hs.
  - simpl. exists hs. split. { assumption. } 
    intros v v' Hvm Hs.
    inversion Hvm. subst. inversion Hs; subst.
    + assumption.
    + congruence.
  - simpl in *. destruct IHHam as [s' [Ham' IHHam]]. exists s'.
    split. { assumption. }
    intros v v' Hvm Hs. inversion Hvm; subst.
    apply (IHHam (v_dict tv)).
    + assumption.
    + inversion Hs; subst.
      * congruence.
      * assumption.
  - simpl. exists s.
    split. { assumption. }
    intros v v' Hvm Hs. inversion Hvm; subst. inversion Hs; subst.
    assumption.
  - simpl in *. destruct IHHam as [s' [Ham' IHHam]]. exists s'.
    split. { assumption. }
    intros v v' Hvm Hs.
    inversion Hvm; subst. inversion Hs; subst.
    apply (IHHam (v_list t)); assumption.
  - destruct (accessor_empty_dec a).
      { subst a. exists (s_list l s). simpl. split.
        - apply AS_Empty.
        - intros v v' Hvm Hs. inversion Hs; subst. assumption. }
      { destruct IHHam as [s' [Ham' IHHam]]. exists (s_list l s').
        split.
        - destruct a; try solve [congruence]; simpl in *;
            apply AS_Pipe; assumption.
        - intros v v' Hvm Hs.
          remember (a_pipe a) as acc.
          remember (next_accessor acc) as acc'.

          generalize dependent l.
          induction Hs; intros len Hvm; subst; try discriminate.
          + inversion Hvm; subst. apply VS_List_Nil.
          + injection Heqacc as Ea. subst a0.
            assert (Ea : a' = next_accessor a).
              { destruct a; try congruence; simpl in *; injection Heqacc' as E;
                assumption. } subst.
            inversion Hvm; subst.
            * apply VS_List_Cons.
                { apply (IHHam hv); assumption. }
                { apply IHHs2; auto. }
            * apply VS_List_Cons_S.
                { apply (IHHam hv); assumption. }
                { apply IHHs2; auto. }
          + congruence.
         }
Qed.

Lemma match_steps : forall a v s,
  accessor_matches a s ->
  val_matches v s ->
  a = a_empty \/ exists v', accessor_step a v (next_accessor a) v'.
Proof.
  intros a v s Ham.
  generalize dependent v.
  induction Ham; intros v Hvm; simpl in *.
  - left. reflexivity.
  - right. inversion Hvm; subst. exists hv.
    apply E_Key_Eq.
  - right. inversion Hvm; subst.
    specialize (IHHam (v_dict tv) H5). destruct IHHam as [contra | [v' Hs']].
      { discriminate. }
    exists v'. apply E_Key_Next; assumption.
  - right. inversion Hvm; subst. exists h.
    apply E_Index_0.
  - right. inversion Hvm; subst.
    specialize (IHHam (v_list t) H3). destruct IHHam as [contra | [v' Hs']].
      { discriminate. }
    exists v'. apply E_Index_S. assumption.
  - right.
    destruct (accessor_empty_dec a).
      { subst a. exists v. inversion Hvm; subst; apply E_Pipe_Empty. }
    remember (s_list l s) as val.
    generalize dependent l.
    induction Hvm; intros len Ev; subst; try discriminate.
    + exists (v_list nil). destruct a; constructor; discriminate.
    + injection Ev as E0 Es. subst.
      specialize (IHHam h Hvm1). destruct IHHam as [contra | [h' Hsh]].
        { contradiction. }
      specialize (IHHvm2 0 eq_refl). destruct IHHvm2 as [vt' Hst].
      assert (Et : exists t', vt' = v_list t').
        { inversion Hst; subst.
          - exists nil. reflexivity.
          - exists (cons hv' tv'). reflexivity.
          - exists t. reflexivity. }
      destruct Et as [t' Et']. subst vt'.
      exists (v_list (h' :: t')). destruct a; try contradiction; 
        apply E_Pipe_Cons; auto.
    + injection Ev as El Es. subst.
      specialize (IHHam h Hvm1). destruct IHHam as [contra | [h' Hsh]].
        { contradiction. }
      specialize (IHHvm2 l eq_refl). destruct IHHvm2 as [vt' Hst].
      assert (Et : exists t', vt' = v_list t').
        { inversion Hst; subst; eexists; reflexivity. }
      destruct Et as [t' Et']. subst vt'.
      exists (v_list (h' :: t')). destruct a; try contradiction;
        apply E_Pipe_Cons; auto.
Qed.

Fixpoint accessor_weight (a : accessor) : nat :=
  match a with
  | a_empty => 0
  | a_key _ a => S (accessor_weight a)
  | a_index _ a => S (accessor_weight a)
  | a_pipe a => S (accessor_weight a)
  end.

Lemma weight_decrease : forall a, a <> a_empty ->
  S (accessor_weight (next_accessor a)) = accessor_weight a.
Proof.
  intros a Hne.
  induction a.
  - contradiction.
  - reflexivity.
  - reflexivity.
  - destruct a; try reflexivity.
    + change (accessor_weight (a_pipe (a_pipe a))) with 
        (S (accessor_weight (a_pipe a))).
      rewrite <- IHa.
      * simpl. reflexivity.
      * discriminate.
Qed.

Inductive multi_step_to : accessor -> value -> accessor -> value -> Prop :=
  | ms_refl : forall a v, multi_step_to a v a v
  | ms_step : forall a v a' v' a'' v'',
      accessor_step a v a' v' ->
      multi_step_to a' v' a'' v'' ->
      multi_step_to a v a'' v''.

Theorem accessor_safety : forall a s v,
  accessor_matches a s ->
  val_matches v s ->
  exists v', multi_step_to a v a_empty v'.
Proof.
  intros a. remember (accessor_weight a) as w.
  generalize dependent a.
  induction w; intros a Ew.
  - destruct a; simpl in *; try discriminate.
    intros s v _ _. exists v. apply ms_refl.
  - intros s v Ham Hvm.
    destruct (accessor_empty_dec a).
    + subst a. discriminate.
    + destruct (match_steps _ _ _ Ham Hvm) as [contra | [v' Hs]].
        { subst a. contradiction. }
      destruct (step_matches _ _ Ham) as [s' [Ham' Hvm']].
      specialize (Hvm' v v' Hvm Hs).
      rewrite <- (weight_decrease _ H) in Ew. injection Ew as Ew. subst w.
      specialize (IHw (next_accessor a) eq_refl _ _ Ham' Hvm').
      destruct IHw as [v'' Hms].
      exists v''. eapply ms_step.
      * apply Hs.
      * apply Hms.
Qed.

