Require Export Common.
Require Export LambdaDollar.

Inductive non {A} :=
| non_s_0 : tm ^A → non (* S₀ f. e *)
| non_app : tm A → tm A → non (* e   e *)
| non_dol : tm A → tm A → non (* e $ e *)
.

Arguments non A : clear implicits.
Global Hint Constructors non : core.

Definition non_to_tm {A} (p : non A) := 
  match p with
  | non_s_0 e => tm_s_0 e
  | non_app e1 e2 => tm_app e1 e2
  | non_dol e1 e2 => tm_dol e1 e2
  end.

Definition tm_dec (e : tm ␀) : (val ␀ + non ␀) :=
  match e with
  | <{ var a }> => from_void a
  | <{ λ  e' }> => inl (val_abs e')
  | <{ S₀ e' }> => inr (non_s_0 e')
  | <{ e1   e2 }> => inr (non_app e1 e2)
  | <{ e1 $ e2 }> => inr (non_dol e1 e2)
  end.

Lemma tm_decide : ∀ e, (∃ v, tm_dec e = inl v) \/ (∃ p, tm_dec e = inr p).
Proof.
  intro e; remember (tm_dec e) as d eqn: H; destruct d; solve [left + right; eexists; auto].
  Qed.

Lemma tm_dec_val : ∀ e v, tm_dec e = inl v → e = val_to_tm v.
Proof.
  intros; inv e; cbn in *; try destruct a; inv H; auto.
  Qed.
Lemma tm_dec_non : ∀ e p, tm_dec e = inr p → e = non_to_tm p.
Proof.
  intros; inv e; cbn in *; try destruct a; inv H; auto.
  Qed.

Ltac inv_tm_dec :=
  match goal with
  | H : ␀ |- _ => destruct H
  | H : (_, _) = (_, _) |- _ => inj H
  | H : inl ?v = tm_dec ?e |- _ => rewrite (tm_dec_val e v (eq_sym H)) in *; auto
  | H : inr ?p = tm_dec ?e |- _ => rewrite (tm_dec_non e p (eq_sym H)) in *; auto
  | H : context C [match tm_dec ?e with inl _ => _ | inr _ => _ end] |- _ =>
    let td := fresh "td" in
    let Hd := fresh "Hd" in
    remember (tm_dec e) as td eqn: Hd; inv td; try rewrite Hd in *
  end.


Section Contexts.
  Context {A : Type}.
  Inductive T' :=
  | T_nil'  : T'
  | T_cons' : val A → T' → T'  (* (v$) · T *)
  .

  Inductive redex' :=
  | redex_beta'   : val A → val A → redex'
  | redex_dollar' : val A → val A → redex'
  | redex_shift'  : val A → tm ^A → redex'  (* v $ S₀ f. e *)
  | redex_let'    : val A → J A → non A → redex'  (* v $ J[p] *)
  .

  Inductive dec' :=
  | dec_value' : val A → dec'
  | dec_stuck' : K A → tm ^A → dec' (* K[S₀ f. e] *)
  | dec_redex' : K A → T' → redex' → dec' (* K[T[Redex]] *)
  .

  Fixpoint plugT' trail e :=
    match trail with
    | T_nil' => e
    | T_cons' v t => plugT' t <{ {val_to_tm v} $ e }>
    (* | T_cons' v t => <{ {val_to_tm v} $ {plugT' t e} }> *)
    end.

  Definition redex_to_term' r := 
    match r with
    | redex_beta'   v1 v2 => tm_app (val_to_tm v1) (val_to_tm v2)
    | redex_dollar' v1 v2 => tm_dol (val_to_tm v1) (val_to_tm v2)
    | redex_shift'  v  e  => tm_dol (val_to_tm v)  <{ S₀ e }>
    | redex_let'   v j p  => tm_dol (val_to_tm v)  (plugJ j (non_to_tm p))
    end.

End Contexts.
Arguments T' A : clear implicits.
Arguments redex' A : clear implicits.
Arguments dec' A : clear implicits.

(* decompose:  T[w $ e]  into  T'[r]*)
Fixpoint decompose'T (t : T' ␀) (w : val ␀) (e : tm ␀) : T' ␀ * redex' ␀ :=
  match e with
  | <{ var a }> => from_void a
  | <{ λ  e' }> => pair t (redex_dollar' w (val_abs e'))
  | <{ S₀ e' }> => pair t (redex_shift'  w          e' )
  | <{ e1 e2 }> =>
    match tm_dec e1 with
    | inr p1 => pair t (redex_let' w (J_fun e2) p1)
    | inl v1 => 
      match tm_dec e2 with
      | inl v2 => pair (T_cons' w t) (redex_beta' v1 v2)
      | inr p2 => pair t (redex_let' w (J_arg v1) p2)
      end
    end
  | <{ e1 $ e2 }> => 
    match tm_dec e1 with
    | inr p1 => pair t (redex_let' w (J_dol e2) p1)
    | inl v1 => decompose'T (T_cons' w t) v1 e2
    end
  end.

Fixpoint decompose' (e : tm ␀) : dec' ␀ :=
  match e with
  | <{ var a }> => from_void a
  | <{ λ  e' }> => dec_value' (val_abs e')
  | <{ S₀ e' }> => dec_stuck' K_nil e'
  | <{ e1 e2 }> =>
    match decompose' e1 with
    | dec_stuck' k e'  => dec_stuck' (K_fun k e2) e'
    | dec_redex' k t r => dec_redex' (K_fun k e2) t r
    | dec_value' v1    => 
      match decompose' e2 with
      | dec_stuck' k e'  => dec_stuck' (K_arg v1 k) e'
      | dec_redex' k t r => dec_redex' (K_arg v1 k) t r
      | dec_value' v2    => dec_redex' (K_nil) T_nil' (redex_beta' v1 v2)
      end
    end
  | <{ e1 $ e2 }> =>
    match decompose' e1 with
    | dec_stuck' k e'  => dec_stuck' (K_dol k e2) e'
    | dec_redex' k t r => dec_redex' (K_dol k e2) t r
    | dec_value' v1    => 
      let (t, r) := decompose'T T_nil' v1 e2 in
      dec_redex' K_nil t r
    end
  end.

Ltac inv_decompose_match' H :=
  match goal with
  | H : (match decompose' ?e with | dec_stuck' _ _ | dec_redex' _ _ _ | dec_value' _ => _ end = _) |- _ =>
    let d := fresh "d" in remember (decompose' e) as d; inv d; inv_decompose_match' H
  | H : (let (_,_) := decompose'T ?t ?w ?e in _) = _ |- _ =>
    let d := fresh "d" in remember (decompose'T t w e) as d; inv d; inv_decompose_match' H
  | _ => try solve [inversion H; auto]; try inj H
  end.

(* plug ∘ decompose' = id *)
Lemma decompose_value_inversion' : ∀ e v,
  decompose' e = dec_value' v → e = val_to_tm v.
Proof.
  intros. inv e; cbn in *.
  - destruct a.
  - inj H; auto.
  - inversion H.
  - inv_decompose_match' H.
  - inv_decompose_match' H.
  Qed.

Lemma decompose_stuck_inversion' : ∀ e k e',
  decompose' e = dec_stuck' k e' → e = plugK k <{ S₀ e' }>.
Proof.
  intros e k; generalize dependent e;
  induction k; intros; inv e; cbn in *;
  try solve [inversion a | inv H];
  inv_decompose_match' H; cbn;
  try rewrite (decompose_value_inversion' e1 v); cbn; auto;
  f_equal; apply IHk; auto.
  Qed.

Ltac inv_dec' :=
  match goal with
  | H : dec_value' ?v = decompose' ?e |- _ => rewrite (decompose_value_inversion' e v); cbn; auto
  | H : dec_stuck' ?k ?e' = decompose' ?e |- _ => rewrite (decompose_stuck_inversion' e k e'); cbn; auto
  end.

Lemma decomposeT_inversion' : ∀ t v e t' r,
  decompose'T t v e = (t', r) → 
  plugT' t <{ {val_to_tm v} $ e }> = plugT' t' (redex_to_term' r).
Proof.
  intros t v e; generalize dependent v; generalize dependent t;
  dependent induction e; intros; cbn in *;
  repeat inv_tm_dec; cbn;
  try solve [f_equal; auto].
  apply IHe2 in H; auto.
  Qed.

Lemma decompose_redex_inversion' : ∀ e t k r,
  decompose' e = dec_redex' k t r → e = plugK k (plugT' t (redex_to_term' r)).
Proof.
  dependent induction e; intros; cbn in *;
  try solve [destruct a | inv H];
  inv_decompose_match' H;
  repeat inv_dec'; cbn; f_equal;
  try solve [apply IHk + apply IHe1 + apply IHe2; auto].
  erewrite <- (decomposeT_inversion' _ _ _ t r); eauto.
  auto.
  Qed.


(* v $ K[p] ~> v' $ p *)
(* Fixpoint decompose'K (v : val ␀) (k : K ␀) : val ␀.
refine (
  match k with
  | K_nil => v
  (* v $ J[K[p]] ~> (λ x. v $ J[x]) $ K[p] *)
  | K_cons j k => decompose'K (val_abs (tm_dol (↑(val_to_tm v)) (plugJ (liftJ j) <{ 0 }>))) k
  end). *)