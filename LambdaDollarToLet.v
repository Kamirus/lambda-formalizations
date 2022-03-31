Require Export Common.
Require Export LambdaDollar.
Require Export LambdaLetDollar.

Inductive sim_J_F {A} (R : tm A → tm' A → Prop) : J A → J' A → Prop :=
| sim_J_fun : ∀ (e : tm  A) (e' : tm'  A), R e e' → sim_J_F R (J_fun e) (J_fun' e')
| sim_J_arg : ∀ (v : val A) (v' : val' A), R v v' → sim_J_F R (J_arg v) (J_arg' v')
| sim_J_dol : ∀ (e : tm  A) (e' : tm'  A), R e e' → sim_J_F R (J_dol e) (J_dol' e')
.
Reserved Notation "e ~ₑ e'" (at level 40).
Reserved Notation "v ~ᵥ v'" (at level 40).
Reserved Notation "p ~ₚ p'" (at level 40).
Reserved Notation "j ~ⱼ j'" (at level 40).
Reserved Notation "k ~ₖ k'" (at level 40).
Reserved Notation "t ~ₜ t'" (at level 40).
Inductive sim_tm {A} : tm A → tm' A → Prop :=
| sim_var  : ∀ a, <{ var a }> ~ₑ <| var a |>
| sim_abs  : ∀ e e', e ~ₑ e' → <{ λ  e }> ~ₑ <| λ  e' |>
| sim_s_0  : ∀ e e', e ~ₑ e' → <{ S₀ e }> ~ₑ <| S₀ e' |>
| sim_app  : ∀ e1 e2 e1' e2', e1 ~ₑ e1' → e2 ~ₑ e2' → <{ e1   e2 }> ~ₑ <| e1'   e2' |>
| sim_dol  : ∀ e1 e2 e1' e2', e1 ~ₑ e1' → e2 ~ₑ e2' → <{ e1 $ e2 }> ~ₑ <| e1' $ e2' |>
| sim_let  : ∀ j j' e e', j ~ⱼ j' → e ~ₑ e' → <{ j [e] }> ~ₑ <| let e' in ↑j'[0] |>
where "e ~ₑ e'" := (sim_tm  e e')
and   "j ~ⱼ j'" := (sim_J_F sim_tm j j').
Inductive sim_val {A} : val A → val' A → Prop :=
| sim_val_abs : ∀ e e', tm_abs e ~ₑ tm_abs' e' → val_abs e ~ᵥ val_abs' e'
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
Global Hint Constructors sim_J_F : core.
Global Hint Constructors sim_K : core.
Global Hint Constructors sim_T : core.
Global Hint Constructors sim_val : core.
Global Hint Constructors sim_non : core.
Global Hint Constructors sim_tm : core.

Axiom sim_val_eta : ∀ {A} (v : val A) v',
  v ~ᵥ v' →
  <{ λv {liftV v} $ 0 }> ~ᵥ v'.

Lemma sim_tm_from_sim_val : ∀ {A v} {v' : val' A},
  v ~ᵥ v' →
  v ~ₑ v'.
Proof.
  intros. destruct v, v'. inversion H; clear H; subst. assumption.
Qed.
Global Hint Resolve sim_tm_from_sim_val : core.

Lemma sim_val_inv : ∀ {A} (v : val A) (e' : tm' A),
  v ~ₑ e' → ∃ (v' : val' A), e' = v' /\ v ~ᵥ v'.
Proof.
  intros. destruct v. inversion H; clear H; subst.
  exists (val_abs' e'0); auto.
  destruct j; inversion H0.
Qed.

Lemma sim_non_inv : ∀ {A} (p : non A) (e' : tm' A),
  p ~ₑ e' → ∃ (p' : non' A), e' = p' /\ p ~ₚ p'.
Proof.
  intros. destruct p; inversion H; clear H; subst.
  exists (non_s_0' e'0); split; auto; repeat constructor; assumption.
  destruct j; inversion H0.
  exists (non_app' e1' e2'); split; auto; repeat constructor; assumption.
  exists (non_let' e'0 <| ↑j'[0] |>); split; auto; constructor; cbn; rewrite <- H0; auto.
  exists (non_dol' e1' e2'); split; auto; repeat constructor; assumption.
  exists (non_let' e'0 <| ↑j'[0] |>); split; auto; constructor; cbn; rewrite <- H0; auto.
Qed.

Ltac reason := repeat(
  match goal with
  | H : val_to_tm ?v ~ₑ ?e' |- _ =>
      let v' := fresh "v'" in
      let Hev := fresh "Hev" in
      let Hv := fresh "Hv" in
      apply sim_val_inv in H as [v' [Hev Hv]]; subst
  | H : val_to_tm' ?v1 = val_to_tm' ?v2 |- _ => apply val_to_tm_injection' in H
  | H : val_to_tm  ?v1 = val_to_tm  ?v2 |- _ => apply val_to_tm_injection  in H
  end).


(* k[p] ~ e' -->'* k'[p'] *)
Lemma plug_k_steps_to_similar_k' : ∀ (k : K ␀) (p : non ␀) term',
  <{ k [p] }> ~ₑ term' →
  ∃ (k' : K' ␀) (p' : non' ␀),
    term' -->'* <| k'[ p'] |> /\
    k ~ₖ k' /\
    p ~ₚ p'.
Proof.
  induction k; intros; cbn in *.
  - apply sim_non_inv in H as [p' [H Hp]]; subst.
    exists K_nil'; exists p'; auto.
  - inversion H; clear H; subst;
    try solve [destruct j; inversion H1 + inversion H0].

    destruct j; inversion H0; clear H0; subst. 
    apply IHk in H1 as [k' [p'' [Hstep [Hk He]]]].
    inversion He; clear He; subst. 
    repeat eexists; eauto. cbn.
    apply (non_when_steps_to_plug_non' _ _ T_nil') in Hstep as Haux. destruct Haux as [p' HH]. subst.
    apply (multi_contr_multi' (contr_let' (J_fun' e2') p')); cbn.
    apply (multi_let' Hstep).

    apply sim_val_inv in H1 as [v' [Hev Hv]]; subst.
    apply IHk in H2 as [k' [p'' [Hstep [Hk He]]]].
    inversion He; clear He; subst. 
    repeat eexists; eauto; cbn.
    apply (non_when_steps_to_plug_non' _ _ T_nil') in Hstep as Haux. destruct Haux as [p' HH]. subst.
    apply (multi_contr_multi' (contr_let' (J_arg' v') p')); cbn.
    apply (multi_let' Hstep).

    destruct j; inversion H0; clear H0; subst. 
    apply IHk in H1 as [k' [p'' [Hstep [Hk He]]]].
    inversion He; clear He; subst. 
    repeat eexists; eauto. cbn.
    apply (non_when_steps_to_plug_non' _ _ T_nil') in Hstep as Haux. destruct Haux as [p' HH]. subst.
    apply (multi_contr_multi' (contr_let' (J_dol' e2') p')); cbn.
    apply (multi_let' Hstep).

    destruct j0, j; inversion H0; clear H0; subst; inversion H1; clear H1; subst; reason.

    apply IHk in H2 as [k' [p'' [Hstep [Hk He]]]];
    inversion He; clear He; subst;
    apply (non_when_steps_to_plug_non' _ _ T_nil') in Hstep as Haux; destruct Haux as [p' HH]; subst;
    exists (K_let' k' <| 0 ↑e'0 |>); exists p''; cbn; repeat split; auto;
    [ apply (multi_let' Hstep) | apply (sim_K_cons _ (J_fun' e'0)); auto ].

    apply IHk in H0 as [k' [p'' [Hstep [Hk He]]]];
    inversion He; clear He; subst;
    apply (non_when_steps_to_plug_non' _ _ T_nil') in Hstep as Haux; destruct Haux as [p' HH]; subst; cbn.
    eexists (K_let' k' _); repeat eexists; cbn.
    apply (multi_contr_multi' (contr_let_beta' _ _)).
    change (tm_subst0' <| 0 {↑ (non_to_tm' p')} |> v') with <| v' {tm_subst0' (↑(non_to_tm' p')) v'} |>.
    rewrite subst_lift'.
    apply (multi_contr_multi' (contr_let' (J_arg' v') _)); cbn.
    apply (multi_let' Hstep). apply (sim_K_cons _ (J_arg' v')); auto. auto.

    destruct k; cbn in *; inversion H3; destruct v; [destruct p | destruct j]; inversion H0.

    apply IHk in H2 as [k' [p'' [Hstep [Hk He]]]];
    inversion He; clear He; subst;
    apply (non_when_steps_to_plug_non' _ _ T_nil') in Hstep as Haux; destruct Haux as [p' HH]; subst;
    exists (K_let' k' <| {liftV' v'0} 0 |>); exists p''; cbn; repeat split; auto;
    [ apply (multi_let' Hstep) | apply (sim_K_cons _ (J_arg' v'0)); auto ].

    apply IHk in H2 as [k' [p'' [Hstep [Hk He]]]];
    inversion He; clear He; subst;
    apply (non_when_steps_to_plug_non' _ _ T_nil') in Hstep as Haux; destruct Haux as [p' HH]; subst.
    exists (K_let' k' <| 0 $ ↑e'0 |>); exists p''; cbn; repeat split; auto;
    [ apply (multi_let' Hstep) | apply (sim_K_cons _ (J_dol' e'0)); auto ].
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
  - inversion H; clear H; subst.
    apply sim_val_inv in H2 as [v' [HH Hv]]; subst.
    destruct (plug_non_is_non K_nil t p) as [tp Htp]; cbn in Htp. rewrite Htp in H4.
    apply plug_k_steps_to_similar_k' in H4 as [k' [p' [Hmulti1 [Hk Hp]]]].
    inversion Hp; clear Hp; subst. rewrite <- Htp in *.
    apply IHt in H as [t' [p'' [Hmulti2 [Ht Hp2]]]].
    inversion Hp2; clear Hp2; subst. 
    exists (T_cons' v' k' t'). exists p''; repeat split; auto.
    cbn.
    apply multi_delim'.
    apply (multi_trans Hmulti1).
    apply multi_k'. apply Hmulti2.

    destruct j; cbn in H0; inversion H0; clear H0; subst.
    reason.
    inversion H1; clear H1; subst.
    destruct (plug_non_is_non K_nil t p) as [tp Htp]; cbn in Htp. rewrite Htp in H0.
    apply plug_k_steps_to_similar_k' in H0 as [k' [p' [Hmulti1 [Hk Hp]]]].
    inversion Hp; clear Hp; subst. rewrite <- Htp in *.
    apply IHt in H as [t' [p'' [Hmulti2 [Ht Hp2]]]].
    inversion Hp2; clear Hp2; subst. 
    exists (T_cons' v' k' t'). repeat eexists; eauto. cbn.
    apply (multi_contr_multi' (contr_let_beta' v' _)).
    change (tm_subst0' <| 0 $ ↑ (e') |> v') with <| v' $ (↑e')[0 := v'] |>.
    apply multi_delim'.
    rewrite subst_lift'.
    apply (multi_trans Hmulti1).
    apply (multi_k' Hmulti2).
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
  inversion Hp1; clear Hp1; subst. rewrite <- Htp in *.
  apply plug_t_steps_to_similar_t' in H as [t' [p2 [Hmulti2 [Ht Hp2]]]].
  inversion Hp2; clear Hp2; subst.
  exists k'. exists t'. exists p2. repeat split; auto.
  apply (multi_trans Hmulti1).
  apply (multi_k' Hmulti2).
Qed.


Lemma sim_map : ∀ {A} {e e' B} {f : A → B},
  e ~ₑ e' →
  map f e ~ₑ map' f e'.
Proof.
  induction e; intros; inversion H; clear H; subst; cbn; auto;
  try solve [destruct j; inversion H0].
  
  destruct j; inversion H0; clear H0; subst.

  inversion H1; clear H1; subst;
  rename e'0 into e1'; rename e' into e2';
  cbn; rewrite <- lift_map';
  apply (sim_let (J_fun (map f e2)) (J_fun' (map' f e2')) (map f e1) (map' f e1')); auto.

  inversion H1; clear H1; subst.
  rename e'0 into e2';
  cbn; reason; subst.
  inversion Hv; clear Hv; subst. cbn in *.
  remember (sim_let (J_arg <{ λv {map (option_map f) e} }>) (J_arg' <| λv' {map' (option_map f) e'} |>) (map f e2) (map' f e2')) as Hg eqn: HHg; clear HHg.
  cbn in *.
  rewrite map_map_law' in *.
  rewrite option_map_comp_law in *.
  rewrite option_map_some_law in *.
  apply Hg; auto. constructor; cbn. constructor. eapply IHe1 in H. cbn in *. inversion H; clear H; subst. apply H3.

  inversion H1; clear H1; subst; cbn in *; inversion H0; clear H0; subst. 
  rename e'0 into e1'.
  rename e' into e2'.
  cbn; rewrite <- lift_map';
  apply (sim_let (J_dol (map f e2)) (J_dol' (map' f e2')) (map f e1) (map' f e1')); auto.
Qed.
Global Hint Resolve sim_map : core.

Lemma sim_let_arg : ∀ {A} (v : val A) v' e e' ev ev',
  ev  = val_to_tm  v  →
  ev' = val_to_tm' v' →
  e ~ₑ e' →
  v ~ᵥ v' →
  <{ ev e }> ~ₑ <| let e' in ↑ev' 0 |>.
Proof.
  intros. remember (sim_let (J_arg v) (J_arg' v') e e') as Hs eqn: HHs; clear HHs.
  cbn in *. subst. rewrite lift_val_to_tm'. apply Hs; auto.
Qed.

Lemma sim_bind : ∀ {A} {e e' B} {f : A → tm B} {f' : A → tm' B},
  e ~ₑ e' →
  (∀ a, f a ~ₑ f' a) →
  bind f e ~ₑ bind' f' e'.
Proof.
  induction e; intros; inversion H; clear H; subst; cbn; auto;
  try solve [destruct j; inversion H1];
  try solve [constructor; apply IHe; auto; intros [a|]; auto].

  inversion H2; clear H2; subst; cbn in *; inversion H1; clear H1; reason; subst.
  rename e'0 into e1'; rename e' into e2'.
  remember (sim_let (J_fun (bind f e2)) (J_fun' (bind' f' e2')) (bind f e1) (bind' f' e1')) as Hg eqn: HHg; clear HHg.
  cbn in *.
  rewrite bind_lift'. rewrite lambda_match_just_some. 
  change (λ a : A, map' Some (f' a)) with (lift ∘ f').
  rewrite <- lift_bind'. apply Hg; auto.

  rename e'0 into e2'; rename v'0 into v'.
  rewrite <- lift_val_to_tm'.
  rewrite bind_lift'. rewrite lambda_match_just_some.
  change (λ a : A, map' Some (f' a)) with (map' Some ∘ f').
  specialize IHe1 with (e' := v').
  assert (bind f v ~ₑ bind' f' v'). apply IHe1; auto.
  rewrite map_bind_law'. change (map' Some (bind' f' v')) with (↑(bind' f' v')).
  inversion Hv; clear Hv; subst. 
  cbn in *.
  rewrite lift_tm_abs'.
  eapply sim_let_arg; auto; reflexivity.

  inversion H2; clear H2; subst; cbn in *; inversion H1; clear H1; reason; subst.
  rename e'0 into e1'; rename e' into e2'.
  remember (sim_let (J_dol (bind f e2)) (J_dol' (bind' f' e2')) (bind f e1) (bind' f' e1')) as Hg eqn: HHg; clear HHg.
  cbn in *.
  rewrite bind_lift'. rewrite lambda_match_just_some. 
  change (λ a : A, map' Some (f' a)) with (lift ∘ f').
  rewrite <- lift_bind'. apply Hg; auto.
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
  induction k; intros; inversion H; clear H; subst; cbn; auto.
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
  intros. inversion H; clear H; subst. cbn. constructor.
  inversion H0; clear H0; subst. constructor. apply (sim_map H2).
Qed.
Global Hint Resolve sim_lift_val : core.

Lemma sim_lift_j : ∀ {A} {j : J A} {j'},
   j ~ⱼ  j' →
  ↑j ~ⱼ ↑j'.
Proof.
  intros. inversion H; clear H; subst; cbn; auto. constructor. destruct v, v'; auto.
Qed.
Global Hint Resolve sim_lift_j : core.

Lemma sim_lift_k : ∀ {A} {k : K A} {k'},
   k ~ₖ  k' →
  ↑k ~ₖ ↑k'.
Proof with auto.
  intros; induction H; cbn...

  assert (map' (option_map Some) <| ↑j'[0] |> = <| ↑↑j'[0] |>) as HH.
    inversion H; clear H; subst; cbn;
    repeat rewrite <- lift_val_to_tm';
    unfold lift; unfold LiftTm';
    repeat rewrite map_map_law'...
  rewrite HH.
  constructor...
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

Theorem dollar_to_let_simulation_step : ∀ e1 e2 e1',
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
  - destruct v.
    inversion H; clear H; subst. rewrite <- H2 in *. clear H2 p'. 
    apply sim_val_inv in H4 as [v0' [Hev Hv]]; subst.
    inversion H3; clear H3; subst.
    + exists <| k' [t' [e' [0 := v0']]] |>. split.
      * apply (multi_trans Hmulti).
        apply (multi_k' (multi_t' (multi_contr' (contr_beta' _ _)))).
      * apply sim_plug_k...
        apply sim_plug_t...
        apply sim_subst_lemma...
    + destruct j; inversion H.
    + destruct p'; inversion H1; clear H1; subst; cbn in *.
      destruct j; inversion H0; clear H0; subst; inversion H2; clear H2; subst; cbn in *.
      * inversion H3; clear H3; subst; try solve [destruct j; inversion H].
        reason.
        exists <| k' [t' [{tm_subst0' e'0 v'}]] |>; split.
        apply (multi_trans Hmulti).
        apply multi_k'. apply multi_t'.
        change <| λ e'0 |> with (val_to_tm' <| λv' e'0 |>).
        eapply (multi_contr_multi' (contr_let_beta' _ _)).
        change (tm_subst0' <| 0 {↑(val_to_tm' v')} |> <| λv' e'0 |>) with <| (λ e'0) {↑(val_to_tm' v')}[0 := λv' e'0] |>.
        rewrite subst_lift'.
        apply (multi_contr' (contr_beta' _ _)).
        apply sim_plug_k... apply sim_plug_t... apply sim_subst_lemma...
      * destruct v; inversion H1; clear H1; subst. reason; subst.
        inversion Hv; clear Hv; subst.
        repeat eexists.
        apply (multi_trans Hmulti).
        eapply multi_k'. eapply multi_t'.
        eapply (multi_contr_multi' (contr_let_beta' _ _)).
        rewrite <- lift_val_to_tm'.
        change (tm_subst0' <| {↑(val_to_tm' <| λv' e' |>)} 0 |> v'1) with <| {↑(val_to_tm' <| λv' e' |>)} [0 := v'1] v'1 |>.
        rewrite subst_lift'.
        apply (multi_contr' (contr_beta' _ _)).
        apply sim_plug_k... apply sim_plug_t... apply sim_subst_lemma...
        inversion H0; clear H0; subst...
  - destruct p'; inversion H; clear H; subst; reason; cbn in *.
    + repeat eexists.
      apply (multi_trans Hmulti). eapply multi_k'. eapply multi_t'. eapply multi_contr'...
      apply sim_plug_k... apply sim_plug_t... 
    + destruct j; inversion H0; clear H0; subst; inversion H3; clear H3; reason; subst. cbn in *.
      repeat eexists.
      apply (multi_trans Hmulti). eapply multi_k'. eapply multi_t'.
      eapply multi_contr_multi'.
      eapply contr_let_beta'. 
      change (tm_subst0' <| 0 $ ↑ (val_to_tm' v') |> v'0) with <| v'0 $ {↑(val_to_tm' v')}[ 0 := v'0] |>.
      rewrite subst_lift'.
      eapply multi_contr'...
      apply sim_plug_k... apply sim_plug_t...
  - change <{ S₀ t0 }> with (non_to_tm (non_s_0 t0)) in H.
    apply (plug_t_steps_to_similar_t' (T_cons v k0 T_nil) _ _) in H as [t'' [p'' [Hmulti' [Ht' Hp']]]].
    inversion Ht'; clear Ht'; subst. inversion H5; clear H5; subst. inversion Hp'; clear Hp'; subst. cbn in *.
    inversion H; clear H; subst; try solve [destruct j; inversion H0].
    rewrite <- H1 in *. clear H1 p''.
    destruct (k_inv_inner' _ _ H4) as [[Hk0 Hk'0] | [k2 [k2' [j2 [j2' [Hk2 [Hj2 [Hke Hke']]]]]]]]; subst.
    + repeat eexists.
      apply (multi_trans Hmulti).
      eapply multi_k'. eapply multi_t'.
      apply (multi_trans Hmulti').
      apply multi_contr'. apply contr_shift'.
      apply sim_plug_k... apply sim_plug_t... apply sim_subst_lemma... cbn. apply sim_val_eta...
    + repeat eexists.
      apply (multi_trans Hmulti).
      eapply multi_k'. eapply multi_t'.
      rewrite Hke' in *.
      apply (multi_trans Hmulti').
      eapply multi_trans.
      eapply multi_delim'.
      apply (plug_k_let_bubbles_up_s_0 _ _ _).
      eapply multi_contr_multi'. apply contr_dol_let'.
      apply multi_contr'. rewrite lambda_to_val'. apply contr_shift'. 
      apply sim_plug_k... apply sim_plug_t... apply sim_subst_lemma...
      rewrite Hke.
      constructor. constructor. constructor... apply sim_plug_k... apply sim_plug_j...
Qed.
