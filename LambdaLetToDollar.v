Require Export Common.
Require Export LambdaDollar.
Require Export LambdaLetDollar.

(* ANCHOR Similarity Relation
 *)
Reserved Notation "e' ~ₑ e" (at level 40).
Reserved Notation "v' ~ᵥ v" (at level 40).
Reserved Notation "p' ~ₚ p" (at level 40).
Reserved Notation "j' ~ⱼ j" (at level 40).
Reserved Notation "k' ~ₖ k" (at level 40).
Reserved Notation "t' ~ₜ t" (at level 40).
Notation "↑ e" := (↑ e) (in custom λ_dollar_scope at level 0).
Notation "↑ e" := (↑ e) (in custom λ_let_dollar_scope at level 0).

Inductive sim_tm {A} : tm' A → tm A → Prop :=
| sim_var  : ∀ a,
    <| var a |> ~ₑ <{ var a }>
| sim_abs  : ∀ e' e, e' ~ₑ e →
    <| λ  e' |> ~ₑ <{ λ   e }>
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
| sim_beta : ∀ (v' : val' A) (v : val A) k' k e' e, v' ~ₑ v → k' ~ₖ k → e' ~ₑ e →
    <| λ {liftV' v'} $ ↑k'[e'] |> ~ₑ <{ λ {liftV v} $ ↑k [↑(λ e) 0] }>
| sim_let_new : ∀ j' j e' e, j' ~ⱼ j → e' ~ₑ e →
    <| let e' in ↑j'[0] |> ~ₑ <{ j[e] }>
with sim_J {A} : J' A → J A → Prop :=
| sim_J_fun : ∀ (e' : tm'  A) (e : tm  A), e' ~ₑ e → J_fun' e' ~ⱼ J_fun e
| sim_J_arg : ∀ (v' : val' A) (v : val A), v' ~ₑ v → J_arg' v' ~ⱼ J_arg v
| sim_J_dol : ∀ (e' : tm'  A) (e : tm  A), e' ~ₑ e → J_dol' e' ~ⱼ J_dol e
with sim_K {A} : K' A → K A → Prop :=
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
where "e' ~ₑ e" := (sim_tm  e' e)
and   "j' ~ⱼ j" := (sim_J j' j)
and   "k' ~ₖ k" := (sim_K k' k).
Scheme sim_tm_mut := Minimality for sim_tm Sort Prop
with   sim_J_mut  := Minimality for sim_J Sort Prop
with   sim_K_mut  := Minimality for sim_K Sort Prop.
(* Minimality vs Induction : the former does not include a proof of ~ in the predicate P *)

Inductive sim_val {A} : val' A → val A → Prop :=
| sim_val_abs : ∀ v' v, val_to_tm' v' ~ₑ val_to_tm v → v' ~ᵥ v
where "v' ~ᵥ v" := (sim_val v' v).
Inductive sim_non {A} : non' A → non A → Prop :=
| sim_non_ : ∀ p p', non_to_tm' p' ~ₑ non_to_tm p → p' ~ₚ p
where "p' ~ₚ p" := (sim_non p' p).
Inductive sim_T {A} : T' A → T A → Prop :=
| sim_T_nil  :
    T_nil' ~ₜ T_nil
| sim_T_cons : ∀ v' v k' k t' t,
    v' ~ᵥ v →
    k' ~ₖ k →
    t' ~ₜ t →
    T_cons' v' k' t' ~ₜ T_cons v k t
where "t' ~ₜ t" := (sim_T t' t).
Global Hint Constructors sim_J : core.
Global Hint Constructors sim_K : core.
Global Hint Constructors sim_T : core.
Global Hint Constructors sim_val : core.
Global Hint Constructors sim_non : core.
Global Hint Constructors sim_tm : core.

(* ANCHOR Small-Steps Grouping: Context Build-Up
 *)
Reserved Notation "e' ~ₐ e" (at level 40).
Inductive sim' : tm' ␀ → tm ␀ → Prop :=
| sim_assoc'  : ∀ k0' k0 t0' t0 v' v k' k j' j,
    k0' ~ₖ k0 →
    t0' ~ₜ t0 →
    v' ~ᵥ v →
    k' ~ₖ k →
    j' ~ⱼ j →
    <| k0'[t0'[let S₀ v' in ↑k'[↑j'[0]]]] |> ~ₐ <{ k0[t0[k[j[S₀ {liftV v} 0]]]] }>
| sim_assoc_let'  : ∀ k0' k0 t0' t0 v' v k' k e' e,
    k0' ~ₖ k0 →
    t0' ~ₜ t0 →
    v' ~ᵥ v →
    k' ~ₖ k →
    e' ~ₑ e →
    <| k0'[t0'[let S₀ v' in ↑k'[e']]] |> ~ₐ <{ k0[t0[k[(λ e) (S₀ {liftV v} 0)]]] }>
where "e' ~ₐ e" := (sim' e' e).
Global Hint Constructors sim' : core.

(* ANCHOR Similarity Relation + Small-Steps Grouping
 *)
Reserved Notation "e' ~ e" (at level 40).
Inductive sim (e' : tm' ␀) (e : tm ␀) : Prop :=
| sim_sim_tm :       e'              ~ₑ e → e' ~ e
| sim_assoc  :       e'              ~ₐ e → e' ~ e
| sim_extra  : ∀ s', e' -->' s' → s' ~ₑ e → e' ~ e
where "e' ~ e" := (sim e' e).
Global Hint Constructors sim : core.

Lemma sim_let_fun : ∀ {A} (e1' : tm' A) e2' e1 e2, e1' ~ₑ e1 → e2' ~ₑ e2 →
  <| let e1' in (0 ↑e2') |> ~ₑ <{ e1 e2 }>.
Proof.
  intros. apply (sim_let_new (J_fun' _) (J_fun _)); auto.
  Qed.
Lemma sim_let_arg : ∀ {A} (v1' : val' A) e2' (v1 : val A) e2, v1' ~ₑ v1 → e2' ~ₑ e2 →
  <| let e2' in ({liftV' v1'} 0 ) |> ~ₑ <{ v1 e2 }>.
Proof.
  intros. apply (sim_let_new (J_arg' _) (J_arg _)); auto.
  Qed.
Lemma sim_let_dol : ∀ {A} (e1' : tm' A) e2' e1 e2, e1' ~ₑ e1 → e2' ~ₑ e2 →
  <| let e1' in (0 $ ↑e2') |> ~ₑ <{ e1 $ e2 }>.
Proof.
  intros. apply (sim_let_new (J_dol' _) (J_dol _)); auto.
  Qed.
Global Hint Resolve sim_let_fun sim_let_arg sim_let_dol : core.

Fixpoint let_to_dollar {A} (e : tm' A) : tm A :=
  match e with
  | <| var a |> => <{ var a }>
  | <| S₀ |> => <{ λ (S₀ 1 0) }>
  | <| λ  e' |> => <{ λ {let_to_dollar e'} }>
  | <| e1   e2 |> => <{ {let_to_dollar e1}   {let_to_dollar e2} }>
  | <| e1 $ e2 |> => <{ {let_to_dollar e1} $ {let_to_dollar e2} }>
  | <| let e1 in e2 |> => <{ (λ {let_to_dollar e2}) {let_to_dollar e1} }>
  end.

Lemma sim_refl_let_to_dollar : ∀ {A} (e' : tm' A),
  e' ~ₑ let_to_dollar e'.
Proof.
  induction e'; cbn; auto.
Qed.

Lemma sim_tm_from_sim_val : ∀ {A v'} {v : val A},
  v' ~ᵥ v →
  v' ~ₑ v.
Proof.
  intros. destruct v, v'; inversion H; clear H; subst; assumption.
Qed.
Global Hint Resolve sim_tm_from_sim_val : core.

Lemma sim_val_inv : ∀ {A} (v' : val' A) (e : tm A),
  v' ~ₑ e → ∃ (v : val A), e = v /\ v' ~ᵥ v.
Proof with auto.
  intros. destruct v'. inversion H; clear H; subst.
  - exists <{ λv e0 }>; repeat split. constructor...
  - repeat eexists.
    rewrite lambda_to_val; f_equal.
    apply sim_eta. rewrite H0 in *. assumption.
  - repeat eexists.
    rewrite lambda_to_val; f_equal.
    apply sim_beta...
  - inversion H; clear H; subst.
    + exists <{ λv S₀ 1 0 }>; split.
      reflexivity.
      repeat constructor.
    + rewrite H0 in *.
      repeat eexists.
      rewrite lambda_to_val; f_equal.
      constructor. cbn. assumption.
Qed.

Lemma sim_val_inv' : ∀ (v' : val' ␀) (e : tm ␀),
  ~ v' ~ₐ e.
Proof.
  intros. intro. inversion H; clear H; subst;
  destruct k0'; cbn in *;
  try (destruct t0'; cbn in *);
  destruct v'; inversion H0.
Qed.

Lemma sim_val_inv'' : ∀ (v' : val' ␀) (e : tm ␀),
  v' ~ e → ∃ (v : val ␀), e = v /\ v' ~ᵥ v.
Proof.
  intros. inversion H; clear H; subst.
  - apply sim_val_inv in H0 as [v [Hsub Hsim]]; subst; eauto.
  - apply sim_val_inv' in H0. contradiction.
  - apply val_does_not_step' in H0; destruct H0.
Qed.

Ltac reason := repeat(
  match goal with
  | H : val_to_tm' _ ~ₑ _ |- _ =>
      let v := fresh "v" in
      let Hev := fresh "Hev" in
      let Hv := fresh "Hv" in
      apply sim_val_inv in H as [v [Hev Hv]]; subst
  | H : val_to_tm' _ ~ _ |- _ =>
      let v := fresh "v" in
      let Hev := fresh "Hev" in
      let Hv := fresh "Hv" in
      apply sim_val_inv'' in H as [v [Hev Hv]]; subst
  | H : val_to_tm' ?v1 = val_to_tm' ?v2 |- _ => apply inj_val' in H
  | H : val_to_tm  ?v1 = val_to_tm  ?v2 |- _ => apply inj_val  in H
  end).

Lemma sim_non_inv : ∀ {A} (p' : non' A) (e : tm A),
  p' ~ₑ e → ∃ (p : non A), e = p /\ p' ~ₚ p.
Proof with try split; cbn; auto; repeat constructor; try assumption.
  intros. destruct p'; inversion H; clear H; subst;
  try solve [destruct v'; inversion H0].
  eexists (non_app _ _)...
  eexists (non_dol _ _)...
  eexists (non_app _ _)...
  inversion H2; clear H2; subst; cbn.
  eexists (non_app _ _)... apply (sim_let_new (J_fun' _) (J_fun _))...
  eexists (non_app _ _)... apply (sim_let_new (J_arg' _) (J_arg _))...
  eexists (non_dol _ _)... apply (sim_let_new (J_dol' _) (J_dol _))...
Qed.

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

Lemma sim_let_inv : ∀ (e1' : tm' ␀) e2' term,
  <| let e1' in e2' |> ~ₑ term →
    (∃ e1 e2, e1' ~ₑ e1 /\ e2' ~ₑ e2 /\ term = <{ (λ e2) e1 }>) \/
    (∃ (j' : J' ␀) (j : J ␀) e1, e1' ~ₑ e1 /\ j' ~ⱼ j /\ e2' = <| ↑j'[0] |> /\ term = <{ j[e1] }>).
Proof.
  intros. inversion H; clear H; subst.
  - left; eauto.
  - destruct v'; inversion H0.
  - right. repeat eexists; eauto.
Qed.

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

Lemma plug_k_compose : ∀ {A} {k1' : K' A} {k1 k2' k2},
  k1' ~ₖ k1 →
  k2' ~ₖ k2 →
  ∃ k' k,
    k' ~ₖ k /\
    (∀ e', <| k1' [k2' [e']] |> = <| k' [e'] |>) /\
    (∀ e , <{ k1  [k2  [e ]] }> = <{ k  [e ] }>).
Proof with auto.
  induction k1'; intros k1 k2' k2 Hk1 Hk2; inversion Hk1; clear Hk1; subst; cbn.
  - repeat eexists...
  - destruct (IHk1' _ _ _ H3 Hk2) as [k0' [k0 [Hk0 [Hsub1 Hsub2]]]].
    exists (K_let' k0' <| ↑j'[0] |>), (K_cons j k0); repeat split; auto; intros;
    try rewrite Hsub1;
    try rewrite Hsub2...
  - destruct (IHk1' _ _ _ H3 Hk2) as [k0' [k0 [Hk0 [Hsub1 Hsub2]]]].
    exists (K_let' k0' t), (K_arg <{ λv e }> k0); repeat split; auto; intros;
    try rewrite Hsub1;
    try rewrite Hsub2...
    constructor...
Qed.

Lemma plug_k_compose_ex : ∀ {A} {k1' : K' A} {k1 k2' k2},
  k1' ~ₖ k1 →
  k2' ~ₖ k2 →
  ∃ k' k,
    k' ~ₖ k /\
    (∀ e', <|  k1' [ k2' [e']] |> = <|  k' [e'] |>) /\
    (∀ e , <{  k1  [ k2  [e ]] }> = <{  k  [e ] }>) /\
    (∀ e', <| ↑k1' [↑k2' [e']] |> = <| ↑k' [e'] |>) /\
    (∀ e , <{ ↑k1  [↑k2  [e ]] }> = <{ ↑k  [e ] }>).
Proof with auto.
  induction k1'; intros k1 k2' k2 Hk1 Hk2; inversion Hk1; clear Hk1; subst; cbn.
  - repeat eexists...
  - destruct (IHk1' _ _ _ H3 Hk2) as [k0' [k0 [Hk0 [Hsub1 [Hsub2 [Hsubl1 Hsubl2]]]]]].
    exists (K_let' k0' <| ↑j'[0] |>), (K_cons j k0); repeat split; auto; intros;
    try rewrite Hsub1;
    try rewrite Hsub2;
    try rewrite Hsubl1;
    try rewrite Hsubl2...
  - destruct (IHk1' _ _ _ H3 Hk2) as [k0' [k0 [Hk0 [Hsub1 [Hsub2 [Hsubl1 Hsubl2]]]]]].
    exists (K_let' k0' t), (K_arg <{ λv e }> k0); repeat split; auto; intros;
    try rewrite Hsub1;
    try rewrite Hsub2;
    try rewrite Hsubl1;
    try rewrite Hsubl2...
    constructor...
Qed.

Lemma plug_t_compose : ∀ {A} {t1' : T' A} {t1 t2' t2},
  t1' ~ₜ t1 →
  t2' ~ₜ t2 →
  ∃ t' t,
    t' ~ₜ t /\
    (∀ e', <| t1' [t2' [e']] |> = <| t' [e'] |>) /\
    (∀ e , <{ t1  [t2  [e ]] }> = <{ t  [e ] }>).
Proof with auto.
  induction t1'; intros t1 t2' t2 Ht1 Ht2; inversion Ht1; clear Ht1; subst; cbn.
  - repeat eexists...
  - destruct (IHt1' _ _ _ H5 Ht2) as [t0' [t0 [Ht0 [Hsub1 Hsub2]]]].
    exists (T_cons' v k t0'), (T_cons v0 k0 t0); repeat split; auto; intros; cbn;
    try rewrite Hsub1;
    try rewrite Hsub2... 
Qed.

Lemma sim_plug_j_inv : ∀ {A} (j' : J' A) e' term,
  <| j' [e'] |> ~ₑ term →
  ∃ j e,
    j' ~ⱼ j /\
    e' ~ₑ e /\
    term = <{ j [e] }>.
Proof.
  intros. destruct j'; cbn in *; inversion H; clear H; subst; reason;
  try solve [eexists (J_fun _) + eexists (J_arg _) + eexists (J_dol _); repeat eexists; eauto];
  destruct v'; inversion H0.
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
  - apply IHk' in H2 as [k [e [Hk [He Hsub]]]]; subst.
    repeat eexists; eauto.

  (* sim_let_new *)
  - apply IHk' in H4 as [k [e0 [Hk [He0 Hsub]]]]; subst.
    repeat eexists; eauto.
Qed.

Lemma sim_plug_t_inv : ∀ {A} (t' : T' A) e' term,
  <| t' [e'] |> ~ₑ term →
  ∃ t e,
    t' ~ₜ t /\
    e' ~ₑ e /\
    term = <{ t [e] }>.
Proof.
  intros A. induction t'; intros; cbn in *; eauto.
  inversion H; clear H; subst. 
  - reason.
    rename k into k', v into v', v0 into v.
    apply sim_plug_k_inv in H4 as [k [e [Hk [Hsim Hsub]]]]; subst.
    apply IHt' in Hsim as [t [e0 [Ht [He Hsub]]]]; subst.
    repeat eexists; eauto.
  - destruct v'; inversion H0.
Qed.

Lemma sim_plug_inv : ∀ {A} (k' : K' A) (t' : T' A) e' term,
  <| k' [t' [e']] |> ~ₑ term →
  ∃ k t e,
    k' ~ₖ k /\
    t' ~ₜ t /\
    e' ~ₑ e /\
    term = <{ k [t [e]] }>.
Proof.
  intros.
  apply sim_plug_k_inv in H as [k [e [Hk [H Hsub]]]]; subst.
  apply sim_plug_t_inv in H as [t [s [Ht [H Hsub]]]]; subst.
  repeat eexists; auto.
Qed.


Lemma sim_map : ∀ {A} {e' e B} {f : A → B},
  e' ~ₑ e →
  map' f e' ~ₑ map f e.
Proof with auto.
  intros. generalize dependent B.
  induction H using sim_tm_mut with
    (P0 := λ A j' j, ∀ B (f : A → B), mapJ' f j' ~ⱼ mapJ f j)
    (P1 := λ A k' k, ∀ B (f : A → B), mapK' f k' ~ₖ mapK f k);
  intros; cbn; auto; reason; subst;
  try rewrite <- lift_val_to_tm;
  try rewrite <- lift_val_to_tm';
  try rewrite <- lift_map;
  try rewrite <- lift_map'...
  
  (* sim_eta *)
  rename v0 into v.
  destruct (map_val_is_val  v  f) as [v2  Hrv ]. 
  destruct (map_val_is_val' v' f) as [v2' Hrv']. 
  rewrite Hrv; rewrite Hrv'.
  rewrite lift_val_to_tm.
  apply sim_eta.
  rewrite <- Hrv; rewrite <- Hrv'.
  apply IHsim_tm.

  (* sim_beta *)
  rename v0 into v1, v' into v1'.
  destruct (map_val_is_val  v1  f) as [w1  Hrv1 ]. 
  destruct (map_val_is_val' v1' f) as [w1' Hrv1'].
  rewrite Hrv1; rewrite Hrv1'.
  rewrite lift_val_to_tm; rewrite lift_val_to_tm'.
  rewrite map_plug_k_is_plug_of_maps.
  rewrite map_plug_k_is_plug_of_maps'.
  rewrite <- lift_mapK.
  rewrite <- lift_mapK'.
  change (map (option_map f) <{ (λ {map (option_map Some) e}) 0 }>) with <{ {map (option_map f) <{ ↑(λ e) }> } 0 }>.
  rewrite <- lift_map.
  apply sim_beta...
  rewrite <- Hrv1; rewrite <- Hrv1'...

  (* sim_let_new *)
  rewrite map_plug_j_is_plug_of_maps'. cbn.
  rewrite map_plug_j_is_plug_of_maps.
  rewrite <- lift_mapJ'.
  apply sim_let_new...

  (* J *)
  constructor.
  rewrite mapV_is_map.
  rewrite mapV_is_map'...

  (* K *)
  rewrite map_plug_j_is_plug_of_maps'. cbn.
  rewrite <- lift_mapJ'.
  constructor...
Qed.
Global Hint Resolve sim_map : core.

Lemma sim_bind : ∀ {A} {e' e B} {f' : A → tm' B} {f : A → tm B},
  e' ~ₑ e →
  (∀ a, f' a ~ₑ f a) →
  bind' f' e' ~ₑ bind f e.
Proof with auto.
  intros. generalize dependent B.
  induction H using sim_tm_mut with
    (P0 := λ A j' j, ∀ B (f' : A → tm' B) (f : A → tm B), (∀ a, f' a ~ₑ f a) → bindJ' f' j' ~ⱼ bindJ f j)
    (P1 := λ A k' k, ∀ B (f' : A → tm' B) (f : A → tm B), (∀ a, f' a ~ₑ f a) → bindK' f' k' ~ₖ bindK f k);
  intros; cbn; auto;
  try solve [constructor; apply IHsim_tm; auto; intros [a|]; auto];
  try rewrite <- lift_val_to_tm;
  try rewrite <- lift_val_to_tm';
  try rewrite bind_plug_k_is_plug_of_binds';
  try rewrite bind_plug_k_is_plug_of_binds;
  try rewrite bind_plug_j_is_plug_of_binds';
  try rewrite bind_plug_j_is_plug_of_binds;
  repeat (rewrite bind_lift + rewrite bind_lift' + rewrite bindK_lift + rewrite bindK_lift' + rewrite bindJ_lift');
  repeat rewrite lambda_match_just_some;
  try (
    change (λ a : A, map Some (f a)) with (lift ∘ f) +
    change (λ a : A, map' Some (f' a)) with (lift ∘ f');
    rewrite <- lift_bind' +
    rewrite <- lift_bind  + 
    rewrite <- lift_bindJ');
  reason; subst; auto.
  - apply sim_let...
    apply IHsim_tm2; intros [a|]...
  - rewrite <- bindV_is_bind; rewrite <- bindV_is_bind'.
    rewrite lift_val_to_tm.
    apply sim_eta.
    rewrite bindV_is_bind; rewrite bindV_is_bind'...
  - change (λ a, map' Some (f' a)) with (lift ∘ f'). rewrite <- lift_bind'.
    rewrite <- bindV_is_bind; rewrite <- bindV_is_bind'.
    rewrite lift_val_to_tm; rewrite lift_val_to_tm'.
    rewrite <- lift_bindK. rewrite <- lift_bindK'.
    change <{ λ {map (option_map Some) e} }> with <{ ↑(λ e) }>.
    remember <{ λ e }>. cbn. rewrite bind_lift. rewrite lambda_match_just_some. rewrite <- lift_bind.
    subst.
    apply sim_beta; try rewrite bindV_is_bind; try rewrite bindV_is_bind'...
    cbn.
    apply IHsim_tm3. intros [a|]; cbn... apply sim_map...
  - cbn. apply sim_let_new...
  - constructor... rewrite bindV_is_bind; rewrite bindV_is_bind'...
  - apply sim_K_cons...
  - apply sim_K_let... apply IHsim_tm; intros [a|]; cbn; auto.
Qed.
Global Hint Resolve sim_bind : core.

Lemma sim_subst_lemma : ∀ e' e v' (v : val ␀),
  e' ~ₑ e →
  v' ~ᵥ v →
  <| e' [0 := v'] |> ~ₑ <{ e [0 := v] }>.
Proof.
  intros. unfold tm_subst0. unfold tm_subst0'.
  apply sim_bind; auto.
  intros [n|]; try destruct n; cbn. auto.
Qed.

Ltac laws := repeat(
  try match goal with
  | |- context C [bind (var_subst (tm_abs ?e)) _] =>
      change (tm_abs e) with (val_to_tm (val_abs e))
  end;
  try match goal with
  | |- context C [bind  (var_subst  _) (val_to_tm  (liftV  ?v))] =>
      rewrite <- (lift_val_to_tm  v)
  | |- context C [bind' (var_subst' _) (val_to_tm' (liftV' ?v))] =>
      rewrite <- (lift_val_to_tm' v)
  end;
  match goal with
  | |- context C [bind  (var_subst  _) (↑ _)] =>
      rewrite bind_var_subst_lift
  | |- context C [bind  (var_subst  _) <{ ↑?k[?e] }>] =>
      rewrite bind_var_subst_lift_k
  | |- context C [bind' (var_subst' _) (↑ _)] =>
      rewrite bind_var_subst_lift'
  | |- context C [bind' (var_subst' _) <| ↑?k[?e] |>] =>
      rewrite bind_var_subst_lift_k'
  end).

Example example_beta_exp_subst : ∀ (e : tm ^␀) (v : val ␀),
  <{ (↑(λ e) 0)[0 := v] }> --> <{ e [0 := v] }>.
Proof.
  intros.
  change <{ λ {map (option_map Some) e} }> with (↑ <{ λ e }>). remember <{ λ e }>.
  cbn. laws. subst. auto.
Qed.


Lemma sim_redex_beta : ∀ e' (v' : val' ␀) ev v,
  <| λ e' |> ~ₑ ev →
  v' ~ᵥ v → ∃ term,
    <{ ev v }> -->* term /\ 
    <| e' [0 := v'] |> ~ₑ term.
Proof with auto.
  intros. generalize dependent v. generalize dependent v'.
  dependent induction H; intros.
  - repeat eexists.
    + apply multi_contr. apply contr_beta.
    + apply (sim_subst_lemma e' e v' v)...
  - rewrite x in *. clear x v'.
    destruct (IHsim_tm e' v eq_refl JMeq_refl JMeq_refl _ _ H0) as [term [H1 H2]].
    repeat eexists; try apply H2.
    apply (multi_contr_multi (contr_beta _ _)). cbn. laws.
    apply (multi_contr_multi (contr_dollar _ _)).
    apply H1.
  - rename e'0 into e', v'0 into v0'.
    repeat eexists.
    + eapply multi_contr_multi. apply contr_beta.
      remember <{ λ e }> as t eqn:Heqt. repeat (cbn; laws). subst.
      eapply multi_delim. eapply multi_k. apply multi_contr. auto.
    + repeat (cbn; laws). change (bind' (var_subst' v0') e') with (tm_subst0' e' v0').
      constructor...
      apply sim_plug_k...
      apply (sim_subst_lemma e' e v0' v0)...
Qed.

Lemma sim_redex_let_beta : ∀ (v' : val' ␀) e' elet v,
  <| let v' in e' |> ~ₑ elet →
  v' ~ᵥ v → ∃ term,
    elet -->* term /\
    <| e' [0 := v'] |> ~ₑ term.
Proof with auto.
  intros. inversion H; clear H; subst; reason.
  - repeat eexists.
    + eapply multi_contr. apply contr_beta.
    + apply sim_subst_lemma...
  - destruct v'0; inversion H1.
  - repeat eexists.
    + apply multi_refl.
    + rewrite subst_plug_of_lift_j. apply sim_plug_j...
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

Lemma sim_lift : ∀ {A} {e' : tm' A} {e},
   e' ~ₑ  e →
  ↑e' ~ₑ ↑e.
Proof.
  intros. unfold lift. unfold LiftTm'. unfold LiftTm. apply (sim_map H).
Qed.
Global Hint Resolve sim_lift : core.

Lemma sim_lift_val : ∀ {A} {v' : val' A} {v},
  v' ~ᵥ v →
  liftV' v' ~ᵥ liftV v.
Proof.
  intros. constructor. rewrite <- lift_val_to_tm'. rewrite <- lift_val_to_tm. inversion H; clear H; subst.
  apply sim_lift; auto. 
Qed.
Global Hint Resolve sim_lift_val : core.

Lemma sim_lift_j : ∀ {A} {j' : J' A} {j},
   j' ~ⱼ  j →
  ↑j' ~ⱼ ↑j.
Proof.
  intros. inversion H; clear H; subst; cbn; auto.
  constructor. rewrite mapV_is_map; rewrite mapV_is_map'. auto.
Qed.
Global Hint Resolve sim_lift_j : core.

Lemma sim_lift_k : ∀ {A} {k' : K' A} {k},
   k' ~ₖ  k →
  ↑k' ~ₖ ↑k.
Proof with auto.
  intros. induction H; cbn...
  rewrite map_plug_j_is_plug_of_maps'. cbn. rewrite <- lift_mapJ'. apply sim_K_cons...
  apply sim_lift_j...
Qed.
Global Hint Resolve sim_lift_k : core.

Lemma t_inv_inner : ∀ (t' : T' ␀) (t : T ␀),
  t' ~ₜ t →
  (t' = T_nil' /\ t = T_nil) \/
  (∃ (t2' : T' ␀) (t2 : T ␀) (v' : val' ␀) (v : val ␀) (k' : K' ␀) (k : K ␀),
    t2' ~ₜ t2 /\
    v' ~ᵥ v /\
    k' ~ₖ k /\
    (∀ (e' : tm' ␀), <| t'[e'] |> = <| t2'[v' $ k'[e']] |>) /\
    (∀ (e  : tm  ␀), <{ t [e ] }> = <{ t2 [v  $ k [e ]] }>)).
Proof.
  induction t'; intros. inversion H; clear H; subst; auto.
  right.
  inversion H; clear H; subst.
  destruct (IHt' t0 H6) as [[Ht' Ht] | [t2' [t2 [v' [v_ [k' [k_ [Ht [Hv [Hk [Hplug' Hplug]]]]]]]]]]];
  try solve [subst; repeat eexists; eauto].
  inversion Hv; clear Hv; subst. rename H into Hv.
  cbn.
  exists (T_cons' v k t2'), (T_cons v0 k0 t2).
  repeat eexists. auto. apply Hv. apply Hk.
  intros. cbn. rewrite Hplug'; auto.
  intros. cbn. rewrite Hplug; auto.
Qed.

Lemma k_inv_inner : ∀ (k' : K' ␀) (k : K ␀),
  k' ~ₖ k →
  (k' = K_nil' /\ k = K_nil) \/
  (∃ (k2' : K' ␀) (k2 : K ␀) (j2' : J' ␀) (j2 : J ␀),
    k2' ~ₖ k2 /\
    j2' ~ⱼ j2 /\
    (∀ (e' : tm' ␀), <| k'[e'] |> = <| k2'[let e' in ↑j2'[0]] |>) /\
    (∀ (e  : tm  ␀), <{ k [e ] }> = <{ k2 [ j2[e]] }>)) \/
  (∃ (k2' : K' ␀) (k2 : K ␀) (e2' : tm' ^␀) (e2 : tm ^␀),
    k2' ~ₖ k2 /\
    e2' ~ₑ e2 /\
    (∀ (e' : tm' ␀), <| k'[e'] |> = <| k2'[let e' in e2'] |>) /\
    (∀ (e  : tm  ␀), <{ k [e ] }> = <{ k2 [(λ e2) e] }>)).
Proof with auto.
  induction k'; intros; inversion H; clear H; subst; cbn; auto;
  destruct (IHk' _ H4) as
    [[Hk' Hk]
    |[[k2' [k2 [j2' [j2 [Hk2 [Hj2 [Hke' Hke]]]]]]]
     |[k2' [k2 [e2' [e2 [Hk2 [Hj2 [Hke' Hke]]]]]]]]]; subst; right.
  - left. exists K_nil', K_nil. repeat eexists...
  - left. exists (K_let' k2' <| ↑j'[0] |>), (K_cons j k2), j2', j2; repeat split; auto; intros.
    + rewrite Hke' in *. reflexivity.
    + rewrite Hke in *. reflexivity.
  - right. exists (K_let' k2' <| ↑j'[0] |>), (K_cons j k2), e2', e2. repeat split; auto; intros; cbn.
    + rewrite Hke' in *. reflexivity.
    + rewrite Hke in *. reflexivity.
  - right. exists K_nil', K_nil. repeat eexists...
  - left. exists (K_let' k2' t), (K_arg <{ λv e }> k2), j2', j2. repeat split; auto; intros; cbn.
    + constructor...
    + rewrite Hke' in *. reflexivity.
    + rewrite Hke in *. reflexivity.
  - right. exists (K_let' k2' t), (K_arg <{ λv e }> k2), e2', e2. repeat split; auto; intros; cbn.
    + constructor...
    + rewrite Hke' in *. reflexivity.
    + rewrite Hke in *. reflexivity.
Qed.


Lemma sim_plug_k' : ∀ k' k e' e,
  k' ~ₖ k →
  e' ~ₐ e →
  <| k'[e'] |> ~ₐ <{ k[e] }>.
Proof with auto.
  intros. inversion H0; clear H0; subst.
  - destruct (plug_k_compose H H1) as [k3' [k3 [Hk [Hsub1 Hsub2]]]]. rewrite Hsub1. rewrite Hsub2.
    apply sim_assoc'...
  - destruct (plug_k_compose H H1) as [k3' [k3 [Hk [Hsub1 Hsub2]]]]. rewrite Hsub1. rewrite Hsub2.
    apply sim_assoc_let'...
Qed.

Lemma sim_plug_t' : ∀ t' t e' e,
  t' ~ₜ t →
  e' ~ₐ e →
  <| t'[e'] |> ~ₐ <{ t[e] }>.
Proof with auto.
  intros. inversion H0; clear H0; subst;
  destruct (t_inv_inner t' t H) as [[Hsub1 Hsub2]|[t2' [t2 [w' [w [k2' [k2 [Ht [Hw [Hk [Hsub1 Hsub2]]]]]]]]]]]; subst; cbn in *; auto;
  rewrite Hsub1 in *;
  rewrite Hsub2 in *;
  clear Hsub1 Hsub2;
  destruct (plug_k_compose Hk H1) as [k3' [k3 [Hk3 [Hsub1 Hsub2]]]]; rewrite Hsub1; rewrite Hsub2; clear Hsub1 Hsub2;
  destruct (plug_t_compose Ht (sim_T_cons _ _ _ _ _ _ Hw Hk3 sim_T_nil)) as [t3' [t3 [Ht3 [Hsub1 Hsub2]]]]; cbn in *; rewrite Hsub1; rewrite Hsub2; clear Hsub1 Hsub2;
  destruct (plug_t_compose Ht3 H2) as [t4' [t4 [Ht4 [Hsub1 Hsub2]]]]; cbn in *; rewrite Hsub1; rewrite Hsub2; clear Hsub1 Hsub2.
  - apply (sim_assoc' K_nil' K_nil)...
  - apply (sim_assoc_let' K_nil' K_nil)...
Qed.

Lemma sim_pre_shift : ∀ k0' k0 t0' t0 v' v k' k j' j w' w esw,
  k0' ~ₖ k0 →
  t0' ~ₜ t0 →
  v' ~ᵥ v →
  k' ~ₖ k →
  j' ~ⱼ j →
  w' ~ᵥ w →
  <{ esw }> -->* <{ S₀ {liftV w} 0 }> →
  ∃ term,
    <{ k0 [t0 [v $ k [j [esw]]]] }> -->* term /\
    <| k0' [t0' [(λ {liftV' v'} $ ↑k'[↑j'[0]]) $ S₀ w']] |> ~ term.
Proof with auto.
  intros k0' k0 t0' t0 v' v k' k j' j w' w esw.
  intros Hk0 Ht0 Hv Hk Hj Hw Hesw.
  destruct (plug_k_compose_ex Hk (sim_K_cons _ _ _ _ Hj sim_K_nil)) as [kj' [kj [Hkj [_ [Hsub [_ Hsubl]]]]]].
  cbn in *. rewrite Hsub.
  repeat eexists.
  - eapply multi_k. eapply multi_t.
    eapply multi_trans. eapply multi_delim. eapply multi_k. apply Hesw.
    eapply multi_contr. eapply contr_shift.
  - cbn; laws.
    eapply sim_extra.
    rewrite lambda_to_val'.
    + eapply step_k'. eapply step_t'. eapply step_contr'. eapply contr_shift'.
    + rewrite <- Hsubl.
      eapply sim_plug_k... eapply sim_plug_t... repeat constructor...
      apply sim_plug_k... apply sim_plug_j... apply sim_lift_j...
Qed.

Lemma sim_pre_shift_let : ∀ k0' k0 t0' t0 v' v k' k e' e w' w esw,
  k0' ~ₖ k0 →
  t0' ~ₜ t0 →
  v' ~ᵥ v →
  k' ~ₖ k →
  e' ~ₑ e →
  w' ~ᵥ w →
  <{ esw }> -->* <{ S₀ {liftV w} 0 }> →
  ∃ term,
    <{ k0 [t0 [v $ k [(λ e) (esw)]]] }> -->* term /\
    <| k0' [t0' [(λ {liftV' v'} $ ↑k'[  e'  ]) $ S₀ w']] |> ~ term.
Proof with auto.
  intros k0' k0 t0' t0 v' v k' k e' e w' w esw.
  intros Hk0 Ht0 Hv Hk He Hw Hesw.
  destruct (plug_k_compose_ex Hk (sim_K_let _ _ _ _ He sim_K_nil)) as [ke' [ke [Hke [_ [Hsub [_ Hsubl]]]]]].
  cbn in *. rewrite Hsub.
  repeat eexists.
  - eapply multi_k. eapply multi_t.
    eapply multi_trans. eapply multi_delim. eapply multi_k. apply Hesw.
    eapply multi_contr. eapply contr_shift.
  - cbn; laws.
    eapply sim_extra.
    rewrite lambda_to_val'.
    + eapply step_k'. eapply step_t'. eapply step_contr'. eapply contr_shift'.
    + rewrite <- Hsubl.
      eapply sim_plug_k... eapply sim_plug_t... constructor...
      apply sim_beta...
Qed.

(* ANCHOR Simulation Step: ~ₑ to ~
 *)
Lemma let_step_to_dollar_multi_aux : ∀ e1' e2' e1,
  e1' -->' e2' →
  e1' ~ₑ e1 →
  ∃ e2, e1 -->* e2 /\ e2' ~ e2.
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
    + apply sim_sim_tm. apply sim_plug_k... apply sim_plug_t...
  }

  (* redex_dollar' *)
  { apply sim_dol_inv in He as [e1_1 [e1_2 [He1 [He2 Hsub]]]]; reason; subst.
    repeat eexists.
    + eapply multi_k. eapply multi_t. apply (multi_contr (contr_dollar _ _)).
    + apply sim_sim_tm. apply sim_plug_k... apply sim_plug_t...
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
    + apply sim_sim_tm. apply sim_plug_k... apply sim_plug_t...
      apply sim_app...
      apply sim_eta...
  }

  (* redex_dol_let' *)
  { apply sim_dol_inv in He as [e1_1 [e1_2 [He1 [Hs Hsub]]]]; reason; subst.
    inversion Hs; clear Hs; subst;
    try solve [destruct v'; inversion H; auto].
    * apply sim_app_inv in H1 as [es [e1_4 [Hes [He2 Hsub]]]]; reason; subst.
      eapply (sim_pre_shift_let _ _ _ _ _ _ K_nil' K_nil); eauto.
      rewrite <- lift_val_to_tm. apply sim_s_0_app...
    * apply sim_app_inv in H3 as [es [e1_4 [Hes [He2 Hsub]]]]; reason; subst.
      eapply (sim_pre_shift _ _ _ _ _ _ K_nil' K_nil); eauto.
      rewrite <- lift_val_to_tm. apply sim_s_0_app...
  }

  (* redex_let' *)
  { repeat eexists; auto.
    apply sim_sim_tm. apply sim_plug_k... apply sim_plug_t...
    apply sim_plug_j_inv in He. destruct He as [j_ [e [Hj [He Hsub]]]]; subst.
    apply sim_let_new...
  }

  (* redex_let_beta' *)
  { apply sim_let_inv in He as [[v_ [t0_ [H1 [H2 Hsub]]]]|[j' [j [v_ [Hv [Hj [Hsub1 Hsub2]]]]]]]; reason; subst.
    - repeat eexists.
      + eapply multi_k. eapply multi_t. apply multi_contr. apply contr_beta.
      + apply sim_sim_tm. apply sim_plug_k... apply sim_plug_t... apply sim_subst_lemma...
    - rewrite subst_plug_of_lift_j.
      repeat eexists; auto.
      apply sim_sim_tm. apply sim_plug_k... apply sim_plug_t... apply sim_plug_j...
  }

  (* redex_let_assoc' *)
  { destruct (sim_let_inv _ _ _ He ) as [[x1 [x2 [Hx1 [Hx2 Hsub]]]]|[j' [j [x1 [Hx1 [Hj [Hsub1 Hsub2]]]]]]]; subst.
    * destruct (sim_let_inv _ _ _ Hx1) as [[y1 [y2 [Hy1 [Hy2 Hsub]]]]|[j0' [j0 [y1 [Hy1 [Hj0 [Hsub1 Hsub2]]]]]]]; subst.
      + apply sim_app_inv in Hy1 as [es [v_ [Hes [Hv_ Hsub]]]]; reason; subst.
        eapply (sim_s_0_app _ v0) in Hes.
        repeat eexists.
        - eapply multi_k. eapply multi_t.
          eapply (multi_j (J_arg <{ λv _ }>)). eapply (multi_j (J_arg <{ λv _ }>)). apply Hes.
        - cbn.
          rewrite lift_val_to_tm.
          apply sim_assoc.
          apply (sim_assoc_let' _ _ _ _ _ _ (K_let' K_nil' t1) (K_cons (J_arg <{ λv x2 }>) K_nil) t0 y2); auto.
      + apply sim_app_inv in Hy1 as [es [v_ [Hes [Hv_ Hsub]]]]; reason; subst.
        eapply (sim_s_0_app _ v0) in Hes.
        repeat eexists.
        - eapply multi_k. eapply multi_t.
          eapply (multi_j (J_arg <{ λv _ }>)). eapply multi_j. apply Hes.
        - cbn.
          rewrite lift_val_to_tm.
          apply sim_assoc.
          apply (sim_assoc' _ _ _ _ _ _ (K_let' K_nil' t1) (K_cons (J_arg <{ λv x2 }>) K_nil) j0' j0); auto.
    * destruct (sim_let_inv _ _ _ Hx1) as [[y1 [y2 [Hy1 [Hy2 Hsub]]]]|[j0' [j0 [y1 [Hy1 [Hj0 [Hsub1 Hsub2]]]]]]]; subst.
      + apply sim_app_inv in Hy1 as [es [v_ [Hes [Hv_ Hsub]]]]; reason; subst.
        eapply (sim_s_0_app _ v0) in Hes.
        repeat eexists.
        - eapply multi_k. eapply multi_t.
          eapply multi_j. eapply (multi_j (J_arg <{ λv y2 }>)). apply Hes.
        - cbn.
          rewrite lift_val_to_tm.
          apply sim_assoc.
          apply (sim_assoc_let' _ _ _ _ _ _ (K_let' K_nil' <| ↑j'[0] |>) (K_cons j K_nil) t0 y2); auto.
      + apply sim_app_inv in Hy1 as [es [v_ [Hes [Hv_ Hsub]]]]; reason; subst.
        eapply (sim_s_0_app _ v0) in Hes.
        repeat eexists.
        - eapply multi_k. eapply multi_t.
          eapply multi_j. eapply multi_j. apply Hes.
        - cbn.
          rewrite lift_val_to_tm.
          apply sim_assoc.
          apply (sim_assoc' _ _ _ _ _ _ (K_let' K_nil' <| ↑j'[0] |>) (K_cons j K_nil) j0' j0); auto.
  }
Qed.

Lemma aux_K1 : ∀ k0' k0 v' v k' k j' j term',
  k0' ~ₖ k0 →
  v' ~ᵥ v →
  k' ~ₖ k →
  j' ~ⱼ j →
  <| k0' [let S₀ v' in ↑k'[↑j'[0]]] |> -->' term' →
  term' ~ₐ <{ k0 [k [j [S₀ {liftV v} 0]]] }>.
Proof with auto.
  intros k0' k0 v' v k' k j' j term' Hk0 Hv Hk Hj Hstep.
  destruct (k_inv_inner _ _ Hk0) as
    [[Hke' Hke]
    |[[k2' [k2 [j2' [j2 [Hk2 [Hj2 [Hke' Hke]]]]]]]
      |[k2' [k2 [e2' [e2 [Hk2 [Hj2 [Hke' Hke]]]]]]]]].
  * subst. cbn in *. apply let_S0_does_not_step in Hstep. destruct Hstep.
  * rewrite Hke' in *.
    rewrite Hke in *.
    apply plug_k_let_let_S0_step_inv in Hstep. subst.
    apply (sim_assoc' k2' k2 T_nil' T_nil v' v (K_let' k' <| ↑j2'[0] |>) (K_cons j2 k))...
  * rewrite Hke' in *.
    rewrite Hke in *.
    apply plug_k_let_let_S0_step_inv in Hstep. subst.
    apply (sim_assoc' k2' k2 T_nil' T_nil v' v (K_let' k' e2') (K_arg <{ λv e2 }> k))... constructor...
Qed.

Lemma aux_K2 : ∀ k0' k0 v' v k' k e' e term',
  k0' ~ₖ k0 →
  v' ~ᵥ v →
  k' ~ₖ k →
  e' ~ₑ e →
  <| k0' [let S₀ v' in ↑k'[e']] |> -->' term' →
  term' ~ₐ <{ k0 [k [(λ e) (S₀ {liftV v} 0)]] }>.
Proof with auto.
  intros k0' k0 v' v k' k j' j term' Hk0 Hv Hk Hj Hstep.
  destruct (k_inv_inner _ _ Hk0) as
    [[Hke' Hke]
    |[[k2' [k2 [j2' [j2 [Hk2 [Hj2 [Hke' Hke]]]]]]]
      |[k2' [k2 [e2' [e2 [Hk2 [Hj2 [Hke' Hke]]]]]]]]].
  * subst. cbn in *. apply let_S0_does_not_step in Hstep. destruct Hstep.
  * rewrite Hke' in *.
    rewrite Hke in *.
    apply plug_k_let_let_S0_step_inv in Hstep. subst.
    apply (sim_assoc_let' k2' k2 T_nil' T_nil v' v (K_let' k' <| ↑j2'[0] |>) (K_cons j2 k))...
  * rewrite Hke' in *.
    rewrite Hke in *.
    apply plug_k_let_let_S0_step_inv in Hstep. subst.
    apply (sim_assoc_let' k2' k2 T_nil' T_nil v' v (K_let' k' e2') (K_arg <{ λv e2 }> k))... constructor...
Qed.

(* ANCHOR Simulation Step
 *)
Theorem let_step_to_dollar_multi : ∀ e1' e2' e1,
  e1' -->' e2' →
  e1' ~ e1 →
  ∃ e2, e1 -->* e2 /\ e2' ~ e2.
Proof with auto.
  intros term1' term2' term1 Hstep Hsim.
  inversion Hsim; clear Hsim; subst.
  - apply (let_step_to_dollar_multi_aux _ _ _ Hstep H).
  - inversion H; clear H; subst. 
    { destruct (t_inv_inner _ _ H1) as [[Ht' Ht]|[t' [t [w' [w [kt' [kt [Ht [Hv [Hk [Hsub1 Hsub2]]]]]]]]]]]; subst; cbn in *.
      + repeat eexists; auto.
        eapply aux_K1 in Hstep as Hsim; eauto.
      + rewrite Hsub1 in *.
        rewrite Hsub2 in *.
        apply plug_shift_step_inv' in Hstep as [inner [Hsub Hstep]]; subst.
        apply shift_step_inv' in Hstep as [[Hkt Hsub]|[inner2 [Hstep Hsub]]]; subst; cbn in *.
        * inversion Hk; clear Hk; subst; cbn in *.
          eapply sim_pre_shift... assumption.
        * eapply aux_K1 in Hstep as Hsim; eauto.
          repeat eexists; auto.
          apply sim_assoc. eapply sim_plug_k'... eapply sim_plug_t'... eapply (sim_plug_t' (T_cons' w' K_nil' T_nil') (T_cons w K_nil T_nil))...
    }
    { destruct (t_inv_inner _ _ H1) as [[Ht' Ht]|[t' [t [w' [w [kt' [kt [Ht [Hv [Hk [Hsub1 Hsub2]]]]]]]]]]]; subst; cbn in *.
      + repeat eexists; auto.
        eapply aux_K2 in Hstep as Hsim; eauto.
      + rewrite Hsub1 in *.
        rewrite Hsub2 in *.
        apply plug_shift_step_inv' in Hstep as [inner [Hsub Hstep]]; subst.
        apply shift_step_inv' in Hstep as [[Hkt Hsub]|[inner2 [Hstep Hsub]]]; subst; cbn in *.
        * inversion Hk; clear Hk; subst; cbn in *.
          eapply sim_pre_shift_let... assumption.
        * eapply aux_K2 in Hstep as Hsim; eauto.
          repeat eexists; auto.
          apply sim_assoc. eapply sim_plug_k'... eapply sim_plug_t'... eapply (sim_plug_t' (T_cons' w' K_nil' T_nil') (T_cons w K_nil T_nil))...
    }
  - repeat eexists; auto.
    apply (deterministic_step' _ _ _ Hstep) in H; subst.
    constructor...
Qed.

(* ANCHOR Simulation
 *)
Theorem let_multi_to_dollar_multi : ∀ e1' e2' e1,
  e1' -->'* e2' →
  e1' ~ e1 →
  ∃ e2, e1 -->* e2 /\ e2' ~ e2.
Proof.
  intros. generalize dependent e1.
  induction H; intros;
  try solve [repeat eexists; auto].
  
  eapply (let_step_to_dollar_multi _ _ _ H) in H1 as Hstep. destruct Hstep as [e2 [Hmulti1 Hsim1]].
  apply IHmulti in Hsim1 as Hstep. destruct Hstep as [e3 [Hmulti2 Hsim2]].
  repeat eexists.
  - apply (multi_trans Hmulti1 Hmulti2).
  - assumption.
Qed.
(* Print Assumptions let_multi_to_dollar_multi. *)

Theorem let_multi_to_dollar_multi_val : ∀ e' (v' : val' ␀) e,
  e' -->'* v' →
  e' ~ e →
  ∃ (v : val ␀), e -->* v /\ v' ~ᵥ v.
Proof.
  intros e' v' e Hmulti Hsim.
  destruct (let_multi_to_dollar_multi e' v' e Hmulti Hsim) as [v [Hmulti' Hsim']].
  reason; eauto.
Qed.

Theorem let_to_dollar_equivalent_steps : ∀ e' (v' : val' ␀),
  e' -->'* v' →
  ∃ (v : val ␀), let_to_dollar e' -->* v /\ v' ~ᵥ v.
Proof.
  intros.
  apply (let_multi_to_dollar_multi_val e' v' (let_to_dollar e') H).
  constructor; apply sim_refl_let_to_dollar.
Qed.
