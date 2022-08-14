Require Export Common.
Require Export LambdaDollar.
Require Export LambdaLetDollar.

(* ANCHOR Similarity Relation
 *)
Reserved Notation "e ~ₑ e'" (at level 40).
Reserved Notation "v ~ᵥ v'" (at level 40).
Reserved Notation "p ~ₚ p'" (at level 40).
Reserved Notation "j ~ⱼ j'" (at level 40).
Reserved Notation "k ~ₖ k'" (at level 40).
Reserved Notation "t ~ₜ t'" (at level 40).
Inductive sim_tm {A} : tm A → tm' A → Prop :=
| sim_var  : ∀ a, <{ var a }> ~ₑ <| var a |>
| sim_abs  : ∀ e e', e ~ₑ e' → <{ λ  e }> ~ₑ <| λ   e' |>
| sim_s_0  : ∀ e e', e ~ₑ e' → <{ S₀ e }> ~ₑ <| S₀, e' |>
| sim_app  : ∀ e1 e2 e1' e2', e1 ~ₑ e1' → e2 ~ₑ e2' → <{ e1   e2 }> ~ₑ <| e1'   e2' |>
| sim_dol  : ∀ e1 e2 e1' e2', e1 ~ₑ e1' → e2 ~ₑ e2' → <{ e1 $ e2 }> ~ₑ <| e1' $ e2' |>
| sim_eta  : ∀ (v : val A) (v' : val' A), v ~ₑ v' →
    <{ λ {liftV v} $ 0 }> ~ₑ v'
| sim_eta_dol : ∀ (v1 v2 : val A) (v1' v2' : val' A), v1 ~ₑ v1' → v2 ~ₑ v2' →
    <{ v1 $ v2 }> ~ₑ <| v1' v2' |>
| sim_let : ∀ j e j' e', j ~ⱼ j' → e ~ₑ e' →
    <{ j[e] }> ~ₑ <| let e' in ↑j'[0] |>
with sim_J {A} : J A → J' A → Prop :=
| sim_J_fun : ∀ (e : tm  A) (e' : tm'  A), e ~ₑ e' → J_fun e ~ⱼ J_fun' e'
| sim_J_arg : ∀ (v : val A) (v' : val' A), v ~ₑ v' → J_arg v ~ⱼ J_arg' v'
| sim_J_dol : ∀ (e : tm  A) (e' : tm'  A), e ~ₑ e' → J_dol e ~ⱼ J_dol' e'
where "e ~ₑ e'" := (sim_tm e e')
and   "j ~ⱼ j'" := (sim_J  j j').
Scheme sim_tm_mut := Minimality for sim_tm Sort Prop
with   sim_J_mut  := Minimality for sim_J Sort Prop.
Inductive sim_val {A} : val A → val' A → Prop :=
| sim_val_abs : ∀ v v', val_to_tm v ~ₑ val_to_tm' v' → v ~ᵥ v'
where "v ~ᵥ v'" := (sim_val v v').
Inductive sim_non {A} : non A → non' A → Prop :=
| sim_non_ : ∀ p p', non_to_tm p ~ₑ non_to_tm' p' → p ~ₚ p'
where "p ~ₚ p'" := (sim_non p p').
Inductive sim_K {A} : K A → K' A → Prop :=
| sim_K_nil  :
    K_nil ~ₖ K_nil'
| sim_K_cons : ∀ j j' k k',
    j ~ⱼ j' →
    k ~ₖ k' →
    K_cons j k ~ₖ K_let' k' <| ↑j'[0] |> (* J[K] ~ let x = K' in J'[0] *)
where "k ~ₖ k'" := (sim_K k k').
Inductive sim_T {A} : T A → T' A → Prop :=
| sim_T_nil  :
    T_nil ~ₜ T_nil'
| sim_T_cons : ∀ v v' k k' t t',
    v ~ᵥ v' →
    k ~ₖ k' →
    t ~ₜ t' →
    T_cons v k t ~ₜ T_cons' v' k' t'
where "t ~ₜ t'" := (sim_T t t').
Global Hint Constructors sim_J : core.
Global Hint Constructors sim_K : core.
Global Hint Constructors sim_T : core.
Global Hint Constructors sim_val : core.
Global Hint Constructors sim_non : core.
Global Hint Constructors sim_tm : core.

Lemma sim_let_fun {A} : ∀ (e1 : tm A) e2 e1' e2',
  e1 ~ₑ e1' → e2 ~ₑ e2' → <{ e1   e2 }> ~ₑ <| let e1' in (0   ↑e2') |>.
Proof.
  intros. apply (sim_let (J_fun _) _ (J_fun' _)); auto.
Qed.
Lemma sim_let_arg {A} : ∀ (v1 : val A) e2 (v1' : val' A) e2',
  v1 ~ₑ v1' → e2 ~ₑ e2' → <{ v1   e2 }> ~ₑ <| let e2' in ({liftV' v1'}  0 ) |>.
Proof.
  intros. apply (sim_let (J_arg _) _ (J_arg' _)); auto.
Qed.
Lemma sim_let_dol {A} : ∀ (e1 : tm A) e2 e1' e2',
  e1 ~ₑ e1' → e2 ~ₑ e2' → <{ e1 $ e2 }> ~ₑ <| let e1' in (0 $ ↑e2') |>.
Proof.
  intros. apply (sim_let (J_dol _) _ (J_dol' _)); auto.
Qed.
Global Hint Resolve sim_let_fun sim_let_arg sim_let_dol : core.

Fixpoint dollar_to_let {A} (e : tm A) : tm' A :=
  match e with
  | <{ var a }> => <| var a |>
  | <{ λ  e' }> => <| λ   {dollar_to_let e'} |>
  | <{ S₀ e' }> => <| S₀, {dollar_to_let e'} |>
  | <{ e1   e2 }> => <| {dollar_to_let e1}   {dollar_to_let e2} |>
  | <{ e1 $ e2 }> => <| {dollar_to_let e1} $ {dollar_to_let e2} |>
  end.

(* ANCHOR Reflexivity of the Similarity Relation *)

Lemma sim_refl_dollar_to_let : ∀ {A} (e : tm A),
  e ~ₑ dollar_to_let e.
Proof.
  induction e; cbn; auto.
Qed.

Lemma sim_tm_from_sim_val : ∀ {A v} {v' : val' A},
  v ~ᵥ v' →
  v ~ₑ v'.
Proof.
  intros. destruct v, v'; inversion H; clear H; subst; assumption.
Qed.
Global Hint Resolve sim_tm_from_sim_val : core.

Lemma sim_val_inv : ∀ {A} (v : val A) (e' : tm' A),
  v ~ₑ e' → ∃ (v' : val' A), e' = v' /\ v ~ᵥ v'.
Proof.
  intros. destruct v. inversion H; clear H; subst.
  exists (val_abs' e'0); split; auto. repeat constructor; auto.
  repeat eexists. repeat constructor; auto.
  destruct j; inversion H0.
Qed.

Lemma sim_non_inv : ∀ {A} (p : non A) (e' : tm' A),
  p ~ₑ e' → ∃ (p' : non' A), e' = p' /\ p ~ₚ p'.
Proof with split; cbn; auto; cbn; repeat (constructor; cbn); try assumption.
  intros. destruct p; inversion H; clear H; subst;
  try (destruct j; inversion H0; clear H0; subst; inversion H1; clear H1; subst).
  - exists (non_app' <| S₀ |> <| λ e'0 |>)...
  - exists (non_app' e1' e2')...
  - exists (non_let' e'0 <| 0 ↑e' |>)... apply sim_let_fun; auto.
  - exists (non_let' e'0 <| {liftV' v'} 0 |>)... apply sim_let_arg; auto.
  - exists (non_dol' e1' e2')...
  - exists (non_app' v1' v2')...
  - exists (non_let' e'0 <| 0 $ ↑e' |>)... apply sim_let_dol; auto.
Qed.

Ltac reason := repeat(
  match goal with
  | H : val_to_tm ?v ~ₑ ?e' |- _ =>
      let v' := fresh "v'" in
      let Hev := fresh "Hev" in
      let Hv := fresh "Hv" in
      apply sim_val_inv in H as [v' [Hev Hv]]; subst
  | H : non_to_tm ?p ~ₑ ?e' |- _ =>
      let p' := fresh "p'" in
      let Hep := fresh "Hep" in
      let Hp := fresh "Hp" in
      apply sim_non_inv in H as [p' [Hep Hp]]; rewrite Hep in *; clear e' Hep
  | H : val_to_tm' ?v1 = val_to_tm' ?v2 |- _ => apply inj_val' in H
  | H : val_to_tm  ?v1 = val_to_tm  ?v2 |- _ => apply inj_val  in H
  | H : non_to_tm  ?p1 = non_to_tm  ?p2 |- _ => rewrite H in *

  | H : non_to_tm  ?p = val_to_tm  ?v |- _ => destruct v, p; inversion H
  | H : val_to_tm  ?v = non_to_tm  ?p |- _ => destruct v, p; inversion H
  end).

Lemma broken_sim_plug_j_inv_as_term_not_nonvalue : ∀ {A} (j : J A) e term',
  <{ j[e] }> ~ₑ term' →
  (∃ j' e', j ~ⱼ j' /\ e ~ₑ e' /\ ( term' = <| j'[e'] |> \/ term' = <| let e' in ↑j'[0] |>)) \/
  (∃ v v' e', j = J_arg v /\ e ~ₑ e' /\ v ~ᵥ v' /\ term' = <| let v' in 0 ↑e' |>).
Proof.
  intros; destruct j; inversion H; clear H; subst; reason; cbn in *; subst;
  try solve [left; repeat eexists; eauto].
  admit. admit. left; repeat eexists; eauto.
  cbn.
  (* Imposible: v1' v2' = v1' $ v2' *)
Abort.

Lemma sim_plug_j_inv : ∀ {A} (j : J A) (p : non A) term',
  <{ j[p] }> ~ₑ term' →
  (∃ j' p', j ~ⱼ j' /\ p ~ₚ p' /\ ( term' = <| j'[p'] |> \/ term' = <| let p' in ↑j'[0] |>)) \/
  (∃ v v' p', j = J_arg v /\ p ~ₚ p' /\ v ~ᵥ v' /\ term' = <| let v' in 0 {↑(non_to_tm' p')} |>).
Proof.
  intros; destruct j; inversion H; clear H; subst; reason; cbn in *;
  try (inversion Hp; clear Hp; subst);
  try solve [left; repeat eexists; eauto];
  destruct j; inversion H0; clear H0; subst; reason; inversion H1; clear H1; subst; reason; subst; try (inversion Hp; clear Hp; subst);
  try solve [left; repeat eexists; eauto].
  right. repeat eexists; auto.
Qed.

(* k[p] ~ e' -->'* k'[p'] *)
Lemma plug_k_steps_to_similar_k' : ∀ (k : K ␀) (p : non ␀) term',
  <{ k [p] }> ~ₑ term' →
  ∃ (k' : K' ␀) (p' : non' ␀),
    term' -->'* <| k'[ p'] |> /\
    k ~ₖ k' /\
    p ~ₚ p'.
Proof with auto.
  induction k; intros; cbn in *.
  - apply sim_non_inv in H as [p' [H Hp]]; subst.
    exists K_nil'; exists p'; auto.
  - destruct (plug_non_is_non k T_nil p) as [kp Hkp]. cbn in Hkp. rewrite Hkp in H.
    apply sim_plug_j_inv in H as
      [[j' [p' [Hj [Hp [Hsub | Hsub]]]]]
      |[v [v' [p' [Hj [Hp [Hv Hsub]]]]]]
      ]; subst;
    inversion Hp; clear Hp; subst; rewrite <- Hkp in *; clear kp Hkp;
      apply IHk in H as [k' [p'' [Hstep [Hk He]]]].
    * exists (K_let' k' <| ↑j'[0] |>), p''; repeat split; cbn.
      + eapply multi_contr_multi'. apply contr_let'.
        apply multi_let'. apply Hstep.
      + constructor...
      + inversion He...
    * exists (K_let' k' <| ↑j'[0] |>), p''; repeat split; cbn.
      + apply multi_let'. apply Hstep.
      + constructor...
      + inversion He...
    * eexists (K_let' k' _), p''; repeat split; cbn. 
      + eapply multi_contr_multi'. apply contr_let_beta'.
        cbn. rewrite bind_var_subst_lift'.
        eapply multi_contr_multi'. apply (contr_let' (J_arg' _)).
        apply multi_let'. apply Hstep.
      + constructor...
      + inversion He...
Qed.

Lemma plug_t_steps_to_similar_t' : ∀ (t : T ␀) (p : non ␀) term',
  <{ t [p] }> ~ₑ term' →
  ∃ (t' : T' ␀) (p' : non' ␀),
    term' -->'* <| t'[ p'] |> /\
    t ~ₜ t' /\
    p ~ₚ p'.
Proof.
  induction t; intros; cbn in *.
  - apply sim_non_inv in H as [p' [H Hp]]; subst.
    exists T_nil'; exists p'; auto.
  - inversion H; clear H; reason; subst.
    + destruct (plug_non_is_non K_nil t p) as [tp Htp]; cbn in Htp. rewrite Htp in H4.
      apply plug_k_steps_to_similar_k' in H4 as [k' [p' [Hmulti1 [Hk Hp]]]].
      inversion Hp; clear Hp; subst.
      rewrite <- Htp in H.
      apply IHt in H as [t' [p'' [Hmulti2 [Ht Hp2]]]].
      repeat eexists; eauto; cbn.
      apply multi_delim'.
      apply (multi_trans Hmulti1).
      apply (multi_k' Hmulti2).
      inversion Hp2; clear Hp2; subst. auto.
    + destruct (plug_non_is_non k t p) as [tp Htp]; cbn in Htp. rewrite Htp in *.
      destruct v2, tp; inversion H1.
    + destruct j; inversion H0; clear H0; subst.
      inversion H1; clear H1; subst; reason.
      destruct (plug_non_is_non K_nil t p) as [tp Htp]; cbn in Htp. rewrite Htp in H0.
      apply plug_k_steps_to_similar_k' in H0 as [k' [p' [Hmulti1 [Hk Hp]]]].
      inversion Hp; clear Hp; subst.
      rewrite <- Htp in H.
      apply IHt in H as [t' [p'' [Hmulti2 [Ht Hp2]]]].
      repeat eexists; eauto; cbn.
      apply (multi_contr_multi' (contr_let_beta' _ _)).
      cbn. change (map' Some e'0) with (↑e'0). rewrite bind_var_subst_lift'.
      apply multi_delim'.
      apply (multi_trans Hmulti1).
      apply (multi_k' Hmulti2).
      inversion Hp2; clear Hp2; subst. auto.
Qed.

Lemma plug_kt_steps_to_similar_kt' : ∀ (k : K ␀) (t : T ␀) (p : non ␀) term',
  <{ k [t [p]] }> ~ₑ term' →
  ∃ (k' : K' ␀) (t' : T' ␀) (p' : non' ␀),
    term' -->'* <| k'[ t' [p']] |> /\
    k ~ₖ k' /\
    t ~ₜ t' /\
    p ~ₚ p'.
Proof.
  intros.
  destruct (plug_non_is_non K_nil t p) as [tp Htp]; cbn in Htp. rewrite Htp in H.
  apply plug_k_steps_to_similar_k' in H as [k' [p1 [Hmulti1 [Hk Hp1]]]].
  inversion Hp1; clear Hp1; reason; subst.
  rewrite <- Htp in *.
  apply plug_t_steps_to_similar_t' in H as [t' [p2 [Hmulti2 [Ht Hp2]]]].
  inversion Hp2; clear Hp2; reason; subst;
  repeat eexists; eauto;
  apply (multi_trans Hmulti1);
  apply (multi_k' Hmulti2).
Qed.


Lemma sim_map : ∀ {A} {e e' B} {f : A → B},
  e ~ₑ e' →
  map f e ~ₑ map' f e'.
Proof with auto.
  intros. generalize dependent B.
  induction H using sim_tm_mut with
    (P0 := λ A j j', ∀ B (f : A → B), mapJ f j ~ⱼ mapJ' f j');
  intros; cbn; auto; reason; subst;
  try rewrite <- lift_val_to_tm;
  try rewrite <- lift_val_to_tm';
  try rewrite <- lift_map;
  try rewrite <- lift_map'...
  
  (* sim_eta *)
  rename v'0 into v'.
  destruct (map_val_is_val  v  f) as [v2  Hrv ]. 
  destruct (map_val_is_val' v' f) as [v2' Hrv']. 
  rewrite Hrv; rewrite Hrv'.
  rewrite lift_val_to_tm.
  apply sim_eta.
  rewrite <- Hrv; rewrite <- Hrv'.
  apply IHsim_tm.

  (* sim_eta_dol *)
  rename v'0 into v1'.
  rename v' into v2'.
  destruct (map_val_is_val  v1  f) as [w1  Hrv1 ]. 
  destruct (map_val_is_val' v1' f) as [w1' Hrv1'].
  destruct (map_val_is_val  v2  f) as [w2  Hrv2 ]. 
  destruct (map_val_is_val' v2' f) as [w2' Hrv2']. 
  rewrite Hrv1; rewrite Hrv1'; rewrite Hrv2; rewrite Hrv2'.
  apply sim_eta_dol.
  rewrite <- Hrv1; rewrite <- Hrv1'...
  rewrite <- Hrv2; rewrite <- Hrv2'...

  (* sim_let *)
  rewrite map_plug_j_is_plug_of_maps.
  rewrite map_plug_j_is_plug_of_maps'; cbn.
  rewrite <- lift_mapJ'.
  apply sim_let...

  (* J *)
  constructor.
  rewrite mapV_is_map; rewrite mapV_is_map'...
Qed.
Global Hint Resolve sim_map : core.

Lemma sim_bind : ∀ {A} {e e' B} {f : A → tm B} {f' : A → tm' B},
  e ~ₑ e' →
  (∀ a, f a ~ₑ f' a) →
  bind f e ~ₑ bind' f' e'.
Proof with auto.
  intros. generalize dependent B.
  induction H using sim_tm_mut with
    (P0 := λ A j j', ∀ B (f : A → tm B) (f' : A → tm' B), (∀ a, f a ~ₑ f' a) → bindJ f j ~ⱼ bindJ' f' j');
  intros; cbn; auto;
  try solve [constructor; apply IHsim_tm; auto; intros [a|]; auto];
  try rewrite <- lift_val_to_tm;
  try rewrite <- lift_val_to_tm';
  try (rewrite bind_lift + rewrite bind_lift'); try rewrite lambda_match_just_some;
  try change (λ a : A, map Some (f a)) with (lift ∘ f);
  try change (λ a : A, map' Some (f' a)) with (lift ∘ f');
  try rewrite <- lift_bind';
  try rewrite <- lift_bind;
  reason; subst; auto.

  (* sim_eta *)
  rename v'0 into v'.
  destruct (bind_val_is_val  v  f ) as [v2  Hrv ].
  destruct (bind_val_is_val' v' f') as [v2' Hrv'].
  rewrite Hrv; rewrite Hrv'.
  rewrite lift_val_to_tm.
  apply sim_eta.
  rewrite <- Hrv; rewrite <- Hrv'...

  (* ṣim_eta_dol *)
  rename v'0 into v1'.
  rename v' into v2'.
  destruct (bind_val_is_val  v1  f ) as [w1  Hrv1 ].
  destruct (bind_val_is_val' v1' f') as [w1' Hrv1'].
  destruct (bind_val_is_val  v2  f ) as [w2  Hrv2 ].
  destruct (bind_val_is_val' v2' f') as [w2' Hrv2']. 
  rewrite Hrv1; rewrite Hrv1'; rewrite Hrv2; rewrite Hrv2'.
  apply sim_eta_dol.
  rewrite <- Hrv1; rewrite <- Hrv1'...
  rewrite <- Hrv2; rewrite <- Hrv2'...

  (* sim_let *)
  rewrite bind_plug_j_is_plug_of_binds;
  rewrite bind_plug_j_is_plug_of_binds'.
  rewrite bindJ_lift'. rewrite lambda_match_just_some. cbn. rewrite <- lift_bindJ'.
  apply sim_let...

  (* J *)
  constructor.
  rewrite bindV_is_bind; rewrite bindV_is_bind'...
Qed.
Global Hint Resolve sim_bind : core.

Lemma sim_plug_j : ∀ {A} (j : J A) j' e e',
  j ~ⱼ j' →
  e ~ₑ e' →
  <{ j[e] }> ~ₑ <| j'[e'] |>.
Proof with auto.
  intros; inversion H; clear H; subst; cbn...
Qed.

Lemma sim_plug_k : ∀ {A} (k : K A) k' e e',
  k ~ₖ k' →
  e ~ₑ e' →
  <{ k[e] }> ~ₑ <| k'[e'] |>.
Proof.
  intros. generalize dependent e. generalize dependent e'.
  induction H; intros; cbn; auto.
Qed.

Lemma sim_plug_t : ∀ {A} (t : T A) t' e e',
  t ~ₜ t' →
  e ~ₑ e' →
  <{ t[e] }> ~ₑ <| t'[e'] |>.
Proof.
  induction t; intros; inversion H; clear H; subst; cbn; auto.
  constructor; auto.
  apply sim_plug_k; auto.
Qed.

Lemma sim_lift : ∀ {A} {e : tm A} {e'},
   e ~ₑ  e' →
  ↑e ~ₑ ↑e'.
Proof.
  intros. unfold lift. unfold LiftTm'. unfold LiftTm. apply (sim_map H).
Qed.
Global Hint Resolve sim_lift : core.

Lemma sim_lift_val : ∀ {A} {v : val A} {v'},
  v ~ᵥ v' →
  liftV v ~ᵥ liftV' v'.
Proof.
  intros.
  inversion H; clear H; subst.
  constructor.
  rewrite <- lift_val_to_tm.
  rewrite <- lift_val_to_tm'.
  apply sim_lift; assumption.
Qed.
Global Hint Resolve sim_lift_val : core.

Lemma sim_lift_j : ∀ {A} {j : J A} {j'},
   j ~ⱼ  j' →
  ↑j ~ⱼ ↑j'.
Proof.
  intros. inversion H; clear H; subst; cbn; auto.
  reason; subst.
  apply sim_lift_val in Hv. auto.
Qed.
Global Hint Resolve sim_lift_j : core.

Lemma sim_lift_k : ∀ {A} {k : K A} {k'},
   k ~ₖ  k' →
  ↑k ~ₖ ↑k'.
Proof with auto.
  intros; induction H; cbn...

  assert (map' (option_map Some) <| ↑j'[0] |> = <| ↑↑j'[0] |>) as HH.
    inversion H; clear H; subst; cbn;
    try change (map' Some e') with (↑e');
    try change (mapV' Some v') with (liftV' v');
    repeat rewrite mapV_is_map';
    repeat rewrite <- lift_val_to_tm';
    unfold lift; unfold LiftTm';
    repeat rewrite map_map_law'...
  rewrite HH.
  constructor...
  apply sim_lift_j...
Qed.
Global Hint Resolve sim_lift_k : core.

Lemma sim_subst_lemma : ∀ e e' v (v' : val' ␀),
  e ~ₑ e' →
  v ~ᵥ v' →
  <{ e [0 := v] }> ~ₑ <| e' [0 := v'] |>.
Proof.
  intros. unfold tm_subst0. unfold tm_subst0'.
  apply sim_bind; auto.
  intros [n|]; try destruct n; cbn. auto.
Qed.

Ltac laws := repeat(
  try match goal with
  | |- context C [bind' (var_subst' _) (mapV' Some _)] =>
      rewrite mapV_is_map'
  end;
  try match goal with
  | |- context C [bind  (var_subst  _) (val_to_tm  (liftV  ?v))] =>
      rewrite <- (lift_val_to_tm  v)
  | |- context C [bind' (var_subst' _) (val_to_tm' (liftV' ?v))] =>
      rewrite <- (lift_val_to_tm' v)
  | |- context C [bind  (var_subst  _) (map  Some ?e)] =>
      change (map Some e) with (↑e)
  | |- context C [bind' (var_subst' _) (map' Some ?e)] =>
      change (map' Some e) with (↑e)
  end;
  match goal with
  | |- context C [bind  (var_subst  _) (↑ _)] =>
      rewrite bind_var_subst_lift
  | |- context C [bind' (var_subst' _) (↑ _)] =>
      rewrite bind_var_subst_lift'
  end).

Lemma k_inv_inner' : ∀ (k : K ␀) (k' : K' ␀),
  k ~ₖ k' →
  (k = K_nil /\ k' = K_nil') \/
  (∃ (k2 : K ␀) (k2' : K' ␀) (j2 : J ␀) (j2' : J' ␀),
    k2 ~ₖ k2' /\
    j2 ~ⱼ j2' /\
    (∀ (e  : tm ^␀), <{ ↑k[e ] }> = <{ ↑k2[↑j2[e ]] }>) /\
    (∀ (e' : tm' ␀), <| k'[e'] |> = <| k2'[let e' in ↑j2'[0]] |>)).
Proof with auto.
  induction k; intros; inversion H; clear H; subst; cbn; auto.
  destruct (IHk _ H4) as [[Hk Hk'] | [k2 [k2' [j2 [j2' [Hk2 [Hj2 [Hke Hke']]]]]]]]; subst; right.
  - exists K_nil, K_nil'. repeat eexists...
  - exists (K_cons j k2), (K_let' k2' <| ↑j'[0] |>), j2, j2'; repeat split; auto; intros.
    + rewrite Hke in *. reflexivity.
    + rewrite Hke' in *. reflexivity.
Qed.

Lemma sim_redex_beta : ∀ e (v : val ␀) ev' v',
  <{ λ e }> ~ₑ ev' →
  v ~ᵥ v' → ∃ term',
    <| ev' v' |> -->'* term' /\ 
    <{ e [0 := v] }> ~ₑ term'.
Proof with auto.
  intros. inversion H; clear H; subst.
  - repeat eexists.
    + apply multi_contr'. apply contr_beta'.
    + apply sim_subst_lemma...

  (* <{ (λ e) v }> = <{ (λ ↑v0 $ 0) v }> ~> <{ v0 $ v }> ~ₑ <{ v0' v' }>, a case where λ$ is behind one step *)
  - repeat eexists.
    + auto.
    + cbn. laws. apply sim_eta_dol...
  - destruct j; inversion H1.
Qed.

(* ANCHOR Simulation Step
 *)
Theorem dollar_step_to_let_multi : ∀ e1 e2 e1',
  e1 --> e2 →
  e1 ~ₑ e1' →
  ∃ e2', e1' -->'* e2' /\ e2 ~ₑ e2'.
Proof with auto.
  intros term1 term2 term1' Hstep Hsim.
  inversion Hstep; clear Hstep; subst.
  inversion H; clear H; subst.
  destruct (redex_is_non r) as [p Hrp]. rewrite Hrp in Hsim.
  apply plug_kt_steps_to_similar_kt' in Hsim as [k' [t' [p' [Hmulti [Hk [Ht Hp]]]]]].
  inversion Hp; clear Hp; subst.
  rewrite <- Hrp in *. clear Hrp p.
  destruct r; cbn in *.

  (* redex_beta *)
  { destruct v.
    inversion H; clear H; subst; reason;
    try (rewrite <- H2 in *; clear p' H2);
    try (rewrite <- H1 in *; clear p' H1);
    try (destruct j; inversion H0; clear H0; subst; inversion H2; clear H2; subst; reason).
    * destruct (sim_redex_beta _ _ _ _ H3 Hv) as [term' [Hmulti2 Hsim]].
      repeat eexists.
      + apply (multi_trans Hmulti). eapply multi_k'. eapply multi_t'. apply Hmulti2.
      + apply sim_plug_k... apply sim_plug_t...
    * destruct (sim_redex_beta _ _ _ _ H3 Hv) as [term' [Hmulti2 Hsim]].
      rewrite lambda_to_val in H3; reason.
      repeat eexists.
      + apply (multi_trans Hmulti). eapply multi_k'. eapply multi_t'.
        eapply multi_contr_multi'. apply contr_let_beta'.
        cbn. laws. apply Hmulti2.
      + apply sim_plug_k... apply sim_plug_t...
    * rewrite lambda_to_val in H1. apply inj_val in H1. subst.
      inversion Hv; clear Hv; subst. cbn in H.
      destruct (sim_redex_beta _ _ _ _ H Hv0) as [term' [Hmulti2 Hsim]].
      repeat eexists.
      + apply (multi_trans Hmulti). eapply multi_k'. eapply multi_t'.
        eapply multi_contr_multi'. apply contr_let_beta'.
        cbn. rewrite mapV_is_map'. laws. apply Hmulti2.
      + apply sim_plug_k... apply sim_plug_t...
  }

  (* redex_dollar *)
  { destruct p'; inversion H; clear H; reason; subst.
    + repeat eexists.
      * apply Hmulti.
      * apply sim_plug_k... apply sim_plug_t... constructor...
    + repeat eexists.
      - apply (multi_trans Hmulti).
        eapply multi_k'. eapply multi_t'.
        cbn. apply (multi_contr' (contr_dollar' _ _)).
      - apply sim_plug_k... apply sim_plug_t...
    + destruct j; inversion H0; clear H0; subst; inversion H3; clear H3; subst; reason.
      cbn in *. 
      repeat eexists.
      - apply (multi_trans Hmulti).
        eapply multi_k'. eapply multi_t'.
        apply (multi_contr_multi' (contr_let_beta' _ _)).
        cbn. laws.
        apply (multi_contr' (contr_dollar' _ _)).
      - apply sim_plug_k... apply sim_plug_t...
  }

  (* redex_shift *)
  { change <{ S₀ t0 }> with (non_to_tm (non_s_0 t0)) in H.
    apply (plug_t_steps_to_similar_t' (T_cons v k0 T_nil) _ _) in H as [t'' [p'' [Hmulti' [Ht' Hp']]]].
    inversion Ht'; clear Ht'; subst. inversion H5; clear H5; subst. inversion Hp'; clear Hp'; subst. cbn in *.
    inversion H; clear H; subst; try solve [destruct j; inversion H0].
    rewrite <- H1 in *. clear H1 p''.
    destruct (k_inv_inner' _ _ H4) as [[Hk0 Hk'0] | [k2 [k2' [j2 [j2' [Hk2 [Hj2 [Hke Hke']]]]]]]]; subst.
    + repeat eexists.
      - apply (multi_trans Hmulti).
        eapply multi_k'. eapply multi_t'.
        apply (multi_trans Hmulti').
        apply (multi_contr_multi' (contr_shift' v' <| λv' e' |>)).
        apply (multi_contr' (contr_beta' _ _)).
      - apply sim_plug_k... apply sim_plug_t... apply sim_subst_lemma... cbn. constructor. apply sim_eta...
    + repeat eexists.
      - apply (multi_trans Hmulti).
        eapply multi_k'. eapply multi_t'.
        rewrite Hke' in *.
        apply (multi_trans Hmulti').
        eapply multi_trans.
        eapply multi_delim'.
        apply (plug_k_let_reassoc_s_0 _ _ _).
        eapply multi_contr_multi'. rewrite lambda_to_val'. apply contr_dol_let'.
        eapply multi_contr_multi'. rewrite lambda_to_val'. apply contr_shift'.
        apply multi_contr'. apply contr_beta'. 
      - apply sim_plug_k... apply sim_plug_t... apply sim_subst_lemma...
        rewrite Hke.
        constructor. constructor. constructor... apply sim_plug_k... apply sim_plug_j...
  }
Qed.

(* ANCHOR Simulation
 *)
Theorem dollar_multi_to_let_multi : ∀ e1 e2 e1',
  e1 -->* e2 →
  e1 ~ₑ e1' →
  ∃ e2', e1' -->'* e2' /\ e2 ~ₑ e2'.
Proof.
  intros. generalize dependent e1'.
  induction H; intros;
  try solve [repeat eexists; auto].
  
  eapply (dollar_step_to_let_multi _ _ _ H) in H1 as Hstep. destruct Hstep as [e2' [Hmulti1 Hsim1]].
  apply IHmulti in Hsim1 as Hstep. destruct Hstep as [e3' [Hmulti2 Hsim2]].
  repeat eexists.
  - apply (multi_trans Hmulti1 Hmulti2).
  - assumption.
Qed.
(* Print Assumptions dollar_multi_to_let_multi. *)

Theorem dollar_multi_to_let_multi_val : ∀ e (v : val ␀) e',
  e -->* v →
  e ~ₑ e' →
  ∃ (v' : val' ␀), e' -->'* v' /\ v ~ᵥ v'.
Proof.
  intros e v e' Hmulti Hsim.
  destruct (dollar_multi_to_let_multi e v e' Hmulti Hsim) as [v' [Hmulti' Hsim']].
  reason; eauto.
Qed.

Theorem dollar_to_let_equivalent_steps : ∀ e (v : val ␀),
  e -->* v →
  ∃ (v' : val' ␀), dollar_to_let e -->'* v' /\ v ~ᵥ v'.
Proof.
  intros.
  apply (dollar_multi_to_let_multi_val e v (dollar_to_let e) H).
  apply sim_refl_dollar_to_let.
Qed.
