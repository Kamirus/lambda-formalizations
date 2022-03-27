Require Export Common.
Require Export LambdaDollar.
Require Export LambdaLetDollar.

Reserved Notation "e ~ₑ e'" (at level 40).
Reserved Notation "v ~ᵥ v'" (at level 40).
Reserved Notation "p ~ₚ p'" (at level 40).
Reserved Notation "j ~ⱼ j'" (at level 40).
Reserved Notation "k ~ₖ k'" (at level 40).
Reserved Notation "t ~ₜ t'" (at level 40).
Inductive sim_J {A} : J A → J' A → Prop :=
| sim_J_fun : ∀ e e', e ~ₑ e' → J_fun e ~ⱼ J_fun' e'
| sim_J_arg : ∀ v v', v ~ᵥ v' → J_arg v ~ⱼ J_arg' v'
| sim_J_dol : ∀ e e', e ~ₑ e' → J_dol e ~ⱼ J_dol' e'
with sim_T {A} : T A → T' A → Prop :=
| sim_T_nil  : T_nil ~ₜ T_nil'
| sim_T_cons : ∀ v v' k k' t t', T_cons v k t ~ₜ T_cons' v' k' t'
with sim_K {A} : K A → K' A → Prop :=
| sim_K_nil  : K_nil ~ₖ K_nil'
| sim_K_cons : ∀ j j' k k',
    j ~ⱼ j' → k ~ₖ k' →
    K_cons j k ~ₖ K_let' k' <| ↑j'[0] |> (* J[K] ~ let x = K' in J'[0] *)
with sim_val {A} : val A → val' A → Prop :=
| sim_val_abs : ∀ e e', tm_abs e ~ₑ tm_abs' e' → val_abs e ~ᵥ val_abs' e'
with sim_non {A} : non A → non' A → Prop :=
| sim_non_ : ∀ p p', non_to_tm p ~ₑ non_to_tm' p' → p ~ₚ p'
with sim_tm {A} : tm A → tm' A → Prop :=
| sim_var  : ∀ a, <{ var a }> ~ₑ <| var a |>
| sim_abs  : ∀ e e', e ~ₑ e' → <{ λ  e }> ~ₑ <| λ  e' |>
| sim_s_0  : ∀ e e', e ~ₑ e' → <{ S₀ e }> ~ₑ <| S₀ e' |>
| sim_app  : ∀ e1 e2 e1' e2', e1 ~ₑ e1' → e2 ~ₑ e2' → <{ e1   e2 }> ~ₑ <| e1'   e2' |>
| sim_dol  : ∀ e1 e2 e1' e2', e1 ~ₑ e1' → e2 ~ₑ e2' → <{ e1 $ e2 }> ~ₑ <| e1' $ e2' |>
(* | sim_plug : ∀ k k' e e', k ~ₖ k' → e ~ₑ e' → plugK k e ~ₑ plugK' k' e' *)
| sim_plug : ∀ v v' k k' e e',
    k ~ₖ k' → e ~ₑ e' →
    <{ λ {liftV  v } $ ↑k [0] }> ~ₑ <| λ {liftV' v'} $ ↑k'[0] |>
where "e ~ₑ e'" := (sim_tm  e e')
and   "v ~ᵥ v'" := (sim_val v v')
and   "p ~ₚ p'" := (sim_non p p')
and   "j ~ⱼ j'" := (sim_J   j j')
and   "k ~ₖ k'" := (sim_K   k k')
and   "t ~ₜ t'" := (sim_T   t t').
Global Hint Constructors sim_J : core.
Global Hint Constructors sim_K : core.
Global Hint Constructors sim_T : core.
Global Hint Constructors sim_val : core.
Global Hint Constructors sim_non : core.
Global Hint Constructors sim_tm : core.

Reserved Notation "e ~ e'" (at level 40).
Inductive sim_toplevel {A} : tm A → tm' A → Prop :=
| sim_top_base : ∀ e e', e ~ₑ e' → e ~ e'
| sim_top_cons : ∀ k k' t t' e e',
    k ~ₖ k' → t ~ₜ t' → e ~ₑ e' → 
    <{ k[t[e]] }> ~ <| k'[t'[e']] |>
where "e ~ e'" := (sim_toplevel e e').
Global Hint Constructors sim_toplevel : core.

Lemma sim_val_inv : ∀ {A} (v : val A) (e' : tm' A),
  v ~ₑ e' → ∃ (v' : val' A), e' = v' /\ v ~ᵥ v'.
Proof.
  intros. destruct v. inversion H; clear H; subst.
  exists (val_abs' e'0); auto.
  exists (val_abs' <| {liftV' v'} $ ↑k'[0] |>); split; auto.
  constructor.
  eapply (sim_plug v v' k k'); eassumption.
Qed.

Lemma sim_non_inv : ∀ {A} (p : non A) (e' : tm' A),
  p ~ₑ e' → ∃ (p' : non' A), e' = p' /\ p ~ₚ p'.
Proof.
  intros. destruct p; inversion H; clear H; subst.
  exists (non_s_0' e'0); split; auto; repeat constructor; assumption.
  exists (non_app' e1' e2'); split; auto; repeat constructor; assumption.
  exists (non_dol' e1' e2'); split; auto; repeat constructor; assumption.
Qed.

Lemma sim_j_inv : ∀ (j : J ␀) e term',
  <{ j[e] }> ~ₑ term' → ∃ j' e', j ~ⱼ j' /\ e ~ₑ e' /\ term' = <| j'[e'] |>.
Proof.
  intros. inversion H; clear H; subst;
    try destruct a; 
    destruct j; inversion H0; clear H0; subst; cbn in *;
    try solve [repeat eexists; eauto].
  apply sim_val_inv in H1 as [v' [Hvv Hv]]; subst.
  repeat eexists; eauto.
Qed.

(* k[p] *)
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
  - apply sim_j_inv in H as [j' [e' [Hj [Hke Hje]]]]; subst.
    apply IHk in Hke as [k' [p'' [Hstep [Hk He]]]].
    inversion He; clear He; subst. 
    apply (non_when_steps_to_plug_non' _ _ T_nil') in Hstep as Haux. destruct Haux as [p' HH]. subst.
    exists (K_let' k' <| ↑j'[0] |>). exists p''. cbn.
    repeat split; auto.
    apply (multi_contr' _ _ _ (contr_let' j' p')).
    apply (multi_let'). apply Hstep.
  Qed.
(* v $ K[S₀ f. e] -->'* e [f := λ x. v $ K'[x]] *)
(* Lemma aux :
  <{ {val_abs v} $ {plugK k <{ S₀ e }>} }> *)
