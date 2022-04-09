Require Export Common.
Require Export LambdaDollar.
Require Export LambdaLetDollar.

Inductive sim_J_F {A} (R : tm' A → tm A → Prop) : J' A → J A → Prop :=
| sim_J_fun : ∀ (e' : tm'  A) (e : tm  A), R e' e → sim_J_F R (J_fun' e') (J_fun e)
| sim_J_arg : ∀ (v' : val' A) (v : val A), R v' v → sim_J_F R (J_arg' v') (J_arg v)
| sim_J_dol : ∀ (e' : tm'  A) (e : tm  A), R e' e → sim_J_F R (J_dol' e') (J_dol e)
.
Reserved Notation "e' ~ₑ e" (at level 40).
Reserved Notation "v' ~ᵥ v" (at level 40).
Reserved Notation "p' ~ₚ p" (at level 40).
Reserved Notation "j' ~ⱼ j" (at level 40).
Reserved Notation "k' ~ₖ k" (at level 40).
Reserved Notation "t' ~ₜ t" (at level 40).
Inductive sim_tm {A} : tm' A → tm A → Prop :=
| sim_var  : ∀ a,
    <| var a |> ~ₑ <{ var a }>
| sim_abs  : ∀ e' e, e' ~ₑ e →
    <| λ  e' |> ~ₑ <{ λ   e }>
(* | sim_s_0  : ∀ e e', e ~ₑ e' → <{ S₀ e }> ~ₑ <| S₀, e' |> *)
| sim_s_0  :
    <| S₀ |> ~ₑ <{ λ S₀ 1 0 }>
| sim_app  : ∀ e1' e2' e1 e2, e1' ~ₑ e1 → e2' ~ₑ e2 →
    <| e1'   e2' |> ~ₑ <{ e1   e2 }>
| sim_dol  : ∀ e1' e2' e1 e2, e1' ~ₑ e1 → e2' ~ₑ e2 →
    <| e1' $ e2' |> ~ₑ <{ e1 $ e2 }>
| sim_let  : ∀ e1' e2' e1 e2, e1' ~ₑ e1 → e2' ~ₑ e2 →
    <| let e1' in e2' |> ~ₑ <{ (λ e2) e1 }>
| sim_eta  : ∀ (v' : val' A) (v : val A), v' ~ₑ v →
    v' ~ₑ <{ λ {liftV v} $ 0 }>
(* | sim_eta_dol : ∀ (v1 v2 : val A) (v1' v2' : val' A),
    v1 ~ₑ v1' → v2 ~ₑ v2' → <{ v1 $ v2 }> ~ₑ <| v1' v2' |> *)
| sim_let_fun : ∀ e1' e2' e1 e2, e1' ~ₑ e1 → e2' ~ₑ e2 →
    <| let e1' in (        0   ↑e2') |> ~ₑ <{ e1   e2 }>
| sim_let_arg : ∀ (v1' : val' A) e2' (v1 : val A) e2, v1' ~ₑ v1 → e2' ~ₑ e2 →
    <| let e2' in ({liftV' v1'}  0 ) |> ~ₑ <{ v1   e2 }>
| sim_let_dol : ∀ e1' e2' e1 e2, e1' ~ₑ e1 → e2' ~ₑ e2 →
    <| let e1' in (        0 $ ↑e2') |> ~ₑ <{ e1 $ e2 }>
where "e' ~ₑ e" := (sim_tm  e' e)
and   "j' ~ⱼ j" := (sim_J_F sim_tm j' j).
Inductive sim_val {A} : val' A → val A → Prop :=
| sim_val_abs : ∀ v' v, val_to_tm' v' ~ₑ val_to_tm v → v' ~ᵥ v
where "v' ~ᵥ v" := (sim_val v' v).
Inductive sim_non {A} : non' A → non A → Prop :=
| sim_non_ : ∀ p p', non_to_tm' p' ~ₑ non_to_tm p → p' ~ₚ p
where "p' ~ₚ p" := (sim_non p' p).
Inductive sim_K {A} : K' A → K A → Prop :=
| sim_K_nil  :
    K_nil' ~ₖ K_nil
| sim_K_cons : ∀ j' j k' k,
    j' ~ⱼ j →
    k' ~ₖ k →
    K_let' k' <| ↑j'[0] |> ~ₖ K_cons j k
| sim_K_let : ∀ e' e k' k,
    e' ~ₑ e →
    k' ~ₖ k →
    K_let' k' e' ~ₖ K_cons (J_arg <{ λv e }>) k
where "k' ~ₖ k" := (sim_K k' k).
Inductive sim_T {A} : T' A → T A → Prop :=
| sim_T_nil  :
    T_nil' ~ₜ T_nil
| sim_T_cons : ∀ v' v k' k t' t,
    v' ~ᵥ v →
    k' ~ₖ k →
    t' ~ₜ t →
    T_cons' v' k' t' ~ₜ T_cons v k t
where "t' ~ₜ t" := (sim_T t' t).
Global Hint Constructors sim_J_F : core.
Global Hint Constructors sim_K : core.
Global Hint Constructors sim_T : core.
Global Hint Constructors sim_val : core.
Global Hint Constructors sim_non : core.
Global Hint Constructors sim_tm : core.

Fixpoint let_to_dollar {A} (e : tm' A) : tm A :=
  match e with
  | <| var a |> => <{ var a }>
  | <| S₀ |> => <{ λ (S₀ 1 0) }>
  | <| λ  e' |> => <{ λ {let_to_dollar e'} }>
  | <| e1   e2 |> => <{ {let_to_dollar e1}   {let_to_dollar e2} }>
  | <| e1 $ e2 |> => <{ {let_to_dollar e1} $ {let_to_dollar e2} }>
  | <| let e1 in e2 |> => <{ (λ {let_to_dollar e2}) {let_to_dollar e1} }>
  end.

Lemma sim_let_to_dollar : ∀ {A} (e' : tm' A),
  e' ~ₑ let_to_dollar e'.
Proof.
  induction e'; cbn; auto.
Qed.

Lemma sim_tm_from_sim_val : ∀ {A v'} {v : val A},
  v' ~ᵥ v →
  v' ~ₑ v.
Admitted.
(* Proof.
  intros. destruct v, v'; inversion H; clear H; subst; assumption.
Qed. *)
Global Hint Resolve sim_tm_from_sim_val : core.

Lemma sim_val_inv : ∀ {A} (v' : val' A) (e : tm A),
  v' ~ₑ e → ∃ (v : val A), e = v /\ v' ~ᵥ v.
Admitted.
(* Proof.
  intros. destruct v. inversion H; clear H; subst.
  exists (val_abs' e'0); split; auto. repeat constructor; auto.
  repeat eexists. repeat constructor; auto.
Qed. *)

Lemma sim_non_inv : ∀ {A} (p' : non' A) (e : tm A),
  p' ~ₑ e → ∃ (p : non A), e = p /\ p' ~ₚ p.
Admitted.
(* Proof with split; cbn; auto; repeat constructor; assumption.
  intros. destruct p; inversion H; clear H; subst.
  exists (non_app' <| S₀ |> <| λ e'0 |>)...
  exists (non_app' e1' e2')...
  exists (non_let' e1' <| 0 ↑e2' |>)...
  exists (non_let' e2' <| {liftV' v1'} 0|>)...
  exists (non_dol' e1' e2')...
  exists (non_app' v1' v2')...
  exists (non_let' e1' <| 0 $ ↑e2' |>)...
Qed. *)

Lemma sim_app_inv : ∀ {A} e1' e2' (term : tm A),
  <| e1' e2' |> ~ₑ term → ∃ e1 e2, e1' ~ₑ e1 /\ e2' ~ₑ e2 /\ term = <{ e1 e2 }>.
Proof.
  intros. inversion H; clear H; subst; eauto.
  destruct v'; inversion H0.
Qed.

Lemma sim_dol_inv : ∀ {A} e1' e2' (term : tm A),
  <| e1' $ e2' |> ~ₑ term → ∃ e1 e2, e1' ~ₑ e1 /\ e2' ~ₑ e2 /\ term = <{ e1 $ e2 }>.
Proof.
  intros. inversion H; clear H; subst; eauto.
  destruct v'; inversion H0.
Qed.

Ltac reason := repeat(
  match goal with
  | H : val_to_tm' _ ~ₑ _ |- _ =>
      let v := fresh "v" in
      let Hev := fresh "Hev" in
      let Hv := fresh "Hv" in
      apply sim_val_inv in H as [v [Hev Hv]]; subst
  | H : val_to_tm' ?v1 = val_to_tm' ?v2 |- _ => apply inj_val' in H
  | H : val_to_tm  ?v1 = val_to_tm  ?v2 |- _ => apply inj_val  in H
  end).

Lemma sim_plug_j : ∀ {A} (j' : J' A) j e' e,
  j' ~ⱼ j →
  e' ~ₑ e →
  <| j'[e'] |> ~ₑ <{ j[e] }>.
Proof with auto.
  intros; inversion H; clear H; subst; cbn...
Qed.

Lemma sim_plug_k : ∀ {A} (k' : K' A) k e' e,
  k' ~ₖ k →
  e' ~ₑ e →
  <| k'[e'] |> ~ₑ <{ k[e] }>.
Proof.
  intros. generalize dependent e. generalize dependent e'.
  induction H; intros; cbn; auto.
  inversion H; clear H; subst; cbn; constructor; auto.
Qed.

Lemma sim_plug_t : ∀ {A} (t' : T' A) t e' e,
  t' ~ₜ t →
  e' ~ₑ e →
  <| t'[e'] |> ~ₑ <{ t[e] }>.
Proof.
  induction t'; intros; inversion H; clear H; subst; cbn; auto.
  constructor; auto.
  apply sim_plug_k; auto.
Qed.

Lemma sim_plug_k_inv : ∀ {A} (k' : K' A) e' term,
  <| k' [e'] |> ~ₑ term →
  ∃ k e,
    k' ~ₖ k /\
    e' ~ₑ e /\
    term = <{ k [e] }>.
Proof.
  intros A. induction k'; intros; cbn in *; eauto.
  inversion H; clear H; subst;
  try solve [destruct v'; inversion H0; auto].

  (* sim_let *)
  apply IHk' in H2 as [k [e [Hk [He Hsub]]]]; subst.
  repeat eexists; eauto.

  apply IHk' in H2 as [k [e [Hk [He Hsub]]]]; subst.
  eexists _, _; split; try apply (sim_K_cons (J_fun' e2')); eauto.

  apply IHk' in H4 as [k [e [Hk [He Hsub]]]]; subst.
  eexists _, _; split; try apply (sim_K_cons (J_arg' v1')); eauto.

  apply IHk' in H2 as [k [e [Hk [He Hsub]]]]; subst.
  eexists _, _; split; try apply (sim_K_cons (J_dol' e2')); eauto.
Qed.

Lemma sim_plug_inv : ∀ {A} (k' : K' A) (t' : T' A) e' term,
  <| k' [t' [e']] |> ~ₑ term →
  ∃ k t e,
    k' ~ₖ k /\
    t' ~ₜ t /\
    e' ~ₑ e /\
    term = <{ k [t [e]] }>.
Admitted.

Lemma sim_subst_lemma : ∀ e' e v' (v : val ␀),
  e' ~ₑ e →
  v' ~ᵥ v →
  <| e' [0 := v'] |> ~ₑ <{ e [0 := v] }>.
Admitted.
(* Proof.
  intros. unfold tm_subst0. unfold tm_subst0'.
  apply sim_bind; auto.
  intros [n|]; try destruct n; cbn. auto.
Qed. *)

Ltac laws := repeat(
  match goal with
  | |- context C [bind (var_subst _) (val_to_tm (liftV ?v))] =>
      rewrite <- (lift_val_to_tm v);
      rewrite bind_var_subst_lift
  | |- context C [bind (var_subst _) (↑ _)] =>
      rewrite bind_var_subst_lift
  end).

Lemma sim_redex_beta : ∀ e' (v' : val' ␀) ev v,
  <| λ e' |> ~ₑ ev →
  v' ~ᵥ v → ∃ term,
    <{ ev v }> -->* term /\ 
    <| e' [0 := v'] |> ~ₑ term.
Proof.
  intros. generalize dependent v. generalize dependent v'.
  dependent induction H; intros.
  - repeat eexists.
    + apply multi_contr. apply contr_beta.
    + apply (sim_subst_lemma e' e v' v); auto.
  - rewrite x in *. clear x v'.
    destruct (IHsim_tm e' v eq_refl JMeq_refl JMeq_refl _ _ H0) as [term [H1 H2]].
    repeat eexists; try apply H2.
    apply (multi_contr_multi (contr_beta _ _)). cbn. laws.
    apply (multi_contr_multi (contr_dollar _ _)).
    apply H1.
Qed.

Lemma sim_s_0_app : ∀ (es : tm ␀) (v : val ␀),
  <| S₀ |> ~ₑ es → <{ es v }> -->* <{ S₀ {↑(val_to_tm v)} 0 }>.
Proof.
  intros. generalize dependent v.
  dependent induction H; intros.
  - eapply multi_contr_multi. eapply (contr_beta _ _). cbn. auto.
  - rewrite x in *. clear x v'.
    eapply multi_contr_multi. eapply (contr_beta _ _). cbn. laws.
    eapply multi_contr_multi. eapply (contr_dollar _ _).
    apply IHsim_tm; auto.
Qed.


Theorem let_step_to_dollar_multi : ∀ e1' e2' e1,
  e1' -->' e2' →
  e1' ~ₑ e1 →
  ∃  e2, e1 -->* e2 /\ e2' ~ₑ e2.
Proof with auto.
  intros term1' term2' term1 Hstep Hsim.
  inversion Hstep as [k' t' e1']; clear Hstep; subst. 
  apply sim_plug_inv in Hsim as [k [t [e1 [Hk [Ht [He Hsub]]]]]]; subst.
  inversion H; clear H; subst.
  destruct r; cbn in *.

  (* redex_beta' *)
  { apply sim_app_inv in He as [e1_1 [e1_2 [He1 [He2 Hsub]]]]; reason; subst.
    destruct (sim_redex_beta _ _ _ _ He1 Hv) as [e2 [Hmulti Hsim]].
    repeat eexists.
    + eapply multi_k. eapply multi_t. apply Hmulti.
    + apply sim_plug_k... apply sim_plug_t...
  }

  (* redex_dollar' *)
  { apply sim_dol_inv in He as [e1_1 [e1_2 [He1 [He2 Hsub]]]]; reason; subst.
    repeat eexists.
    + eapply multi_k. eapply multi_t. apply (multi_contr (contr_dollar _ _)).
    + apply sim_plug_k... apply sim_plug_t...
  }

  (* redex_shift' *)
  { apply sim_dol_inv in He as [e1_1 [e1_2 [He1 [Hs Hsub]]]]; reason; subst.
    apply sim_app_inv in Hs as [e1_3 [e1_4 [Hes [He2 Hsub]]]]; reason; subst.
    eapply (sim_s_0_app _ v2) in Hes.
    repeat eexists.
    + eapply multi_k. eapply multi_t.
      eapply multi_trans.
      eapply multi_delim. apply Hes.
      apply (multi_contr_multi (contr_shift v1 K_nil _)). cbn.
      rewrite lambda_to_val.
      laws.
      apply multi_refl.
    + apply sim_plug_k... apply sim_plug_t...
      apply sim_app...
      constructor...
  }

  (* redex_dol_let' *)
  {
  }

  (* redex_let' *)
  {
  }

  (* redex_let_beta' *)
  {
  }

  (* redex_let_assoc' *)
  {
  }

Qed.