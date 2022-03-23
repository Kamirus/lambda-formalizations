Require Export Common.
Require Export LambdaDollar.
Require Export LambdaLetDollar.

Reserved Notation "e ~ₑ e'" (at level 90).
Reserved Notation "v ~ᵥ v'" (at level 90).
Reserved Notation "j ~ⱼ j'" (at level 90).
Reserved Notation "k ~ₖ k'" (at level 90).
Inductive sim_J {A} : J A → J' A → Prop :=
| sim_J_fun : ∀ e e', e ~ₑ e' → J_fun e ~ⱼ J_fun' e'
| sim_J_arg : ∀ v v', v ~ᵥ v' → J_arg v ~ⱼ J_arg' v'
| sim_J_dol : ∀ e e', e ~ₑ e' → J_dol e ~ⱼ J_dol' e'
with sim_K {A} : K A → K' A → Prop :=
| sim_K_nil  : K_nil ~ₖ K_nil'
| sim_K_cons : ∀ j j' k k',
    j ~ⱼ j' → k ~ₖ k' →
    K_cons j k ~ₖ K_let' k' (plugJ' (liftJ' j') (tm_var' None)) (* J[K] ~ let x = K' in J'[0] *)
with sim_val {A} : val A → val' A → Prop :=
| sim_val_abs : ∀ e e', e ~ₑ e' → val_abs e ~ᵥ val_abs' e'
with sim_tm {A} : tm A → tm' A → Prop :=
| sim_var  : ∀ a,    tm_var a ~ₑ tm_var' a
| sim_abs  : ∀ e e', e ~ₑ e' → tm_abs e ~ₑ tm_abs' e'
| sim_s_0  : ∀ e e', e ~ₑ e' → tm_s_0 e ~ₑ tm_s_0' e'
| sim_app  : ∀ e1 e2 e1' e2', e1 ~ₑ e1' → e2 ~ₑ e2' → tm_app e1 e2 ~ₑ tm_app' e1' e2'
| sim_dol  : ∀ e1 e2 e1' e2', e1 ~ₑ e1' → e2 ~ₑ e2' → tm_dol e1 e2 ~ₑ tm_dol' e1' e2'
| sim_plug : ∀ k k' e e', k ~ₖ k' → e ~ₑ e' → plugK k e ~ₑ plugK' k' e'
where "e ~ₑ e'" := (sim_tm  e e')
and   "v ~ᵥ v'" := (sim_val v v')
and   "j ~ⱼ j'" := (sim_J   j j')
and   "k ~ₖ k'" := (sim_K   k k').