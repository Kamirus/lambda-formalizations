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
Lemma tm_dec_of_val : ∀ v, tm_dec (val_to_tm v) = inl v.
Proof.
  intros; destruct v; auto.
Qed.
Lemma tm_dec_of_non : ∀ p, tm_dec (non_to_tm p) = inr p.
Proof.
  intros; destruct p; auto.
Qed.

Ltac reason := repeat(
  rewrite tm_dec_of_val in * +
  rewrite tm_dec_of_non in * +
  match goal with
  | H : ␀ |- _ => destruct H
  | H : (_, _) = (_, _) |- _ => inj H
  | H : inl ?v = tm_dec ?e |- _ => rewrite (tm_dec_val e v (eq_sym H)) in *; auto
  | H : inr ?p = tm_dec ?e |- _ => rewrite (tm_dec_non e p (eq_sym H)) in *; auto
  | H : context C [let (_, _) := ?e in _] |- _ =>
    let p := fresh "p" in remember e as p; inv p
  | |- context C [let (_, _) := ?e in _] => 
    let p := fresh "p" in remember e as p; inv p
  | H : context C [match tm_dec ?e with inl _ => _ | inr _ => _ end] |- _ =>
    let td := fresh "td" in
    let Hd := fresh "Hd" in
    remember (tm_dec e) as td eqn: Hd; inv td; try rewrite Hd in *
  end).


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
    (* | T_cons' v t => plugT' t <{ {val_to_tm v} $ e }> *)
    | T_cons' v t => <{ {val_to_tm v} $ {plugT' t e} }>
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
(* Fixpoint decompose'T (t : T' ␀) (w : val ␀) (e : tm ␀) : T' ␀ * redex' ␀ :=
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
  end. *)

(* decompose:  w $ e  into  T'[r]*)
Fixpoint decompose'W (w : val ␀) (e : tm ␀) : T' ␀ * redex' ␀ :=
  match e with
  | <{ var a }> => from_void a
  | <{ λ  e' }> => (T_nil', redex_dollar' w (val_abs e'))
  | <{ S₀ e' }> => (T_nil', redex_shift'  w          e' )
  | <{ e1 e2 }> =>
    match tm_dec e1 with
    | inr p1 => (T_nil', redex_let' w (J_fun e2) p1)
    | inl v1 => 
      match tm_dec e2 with
      | inr p2 => (T_nil', redex_let' w (J_arg v1) p2)
      | inl v2 => (T_cons' w T_nil', redex_beta' v1 v2)
      end
    end
  | <{ e1 $ e2 }> => 
    match tm_dec e1 with
    | inr p1 => (T_nil', redex_let' w (J_dol e2) p1)
    | inl v1 => 
      let (t, r) := decompose'W v1 e2
      in (T_cons' w t, r)
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
      let (t, r) := decompose'W v1 e2 in
      (* let (t, r) := decompose'T T_nil' v1 e2 in *)
      dec_redex' K_nil t r
    end
  end.

Ltac inv_decompose_match' H :=
  match goal with
  | H : (match decompose' ?e with | dec_stuck' _ _ | dec_redex' _ _ _ | dec_value' _ => _ end = _) |- _ =>
    let d := fresh "d" in remember (decompose' e) as d; inv d; inv_decompose_match' H
  | H : (let (_,_) := ?e in _) = _ |- _ =>
    let d := fresh "d" in remember e as d; inv d; inv_decompose_match' H
  | _ => try solve [inversion H; auto]; try inj H
  end.


Lemma inj_non : ∀ {A} (p p' : non A),
  non_to_tm p = non_to_tm p' → p = p'.
Proof.
  intros; destruct p, p'; cbn in *; inv H; auto.
  Qed.

Lemma inj_redex : ∀ {A} (r r' : redex' A),
  redex_to_term' r = redex_to_term' r' -> r = r'.
Proof.
  intros; destruct r, r';
  repeat match goal with
  | v : val ?A |- _ => destruct v; cbn in *
  | j : J ?A |- _ => destruct j; cbn in *
  | H: non_to_tm _ = non_to_tm _ |- _ => apply inj_non in H; subst
  | H: _ = _ |- _ => inv H
  end; auto.

  destruct n0; cbn in *; inv x.
  destruct n; cbn in *; inv x.
Qed.

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

(* Lemma decomposeT_inversion' : ∀ t v e t' r,
  decompose'T t v e = (t', r) → 
  plugT' t <{ {val_to_tm v} $ e }> = plugT' t' (redex_to_term' r).
Proof.
  intros t v e; generalize dependent v; generalize dependent t;
  dependent induction e; intros; cbn in *;
  reason; cbn;
  try solve [f_equal; auto].
  apply IHe2 in H; auto.
  Qed. *)

Lemma decomposeW_j_p : ∀ w j p,
  decompose'W w (plugJ j (non_to_tm p)) = (T_nil', redex_let' w j p).
Proof.
  intros; inv j; cbn; reason; reflexivity.
Qed.
Lemma decomposeW_inversion' : ∀ w e t r,
  decompose'W w e = (t, r) →
  <{ {val_to_tm w} $ e }> = plugT' t (redex_to_term' r).
Proof.
  intros w e; generalize dependent w;
  dependent induction e; intros; cbn in *;
  reason; cbn; f_equal.
  apply IHe2; auto.
Qed.
Lemma decompose_redex_inversion' : ∀ e t k r,
  decompose' e = dec_redex' k t r → e = plugK k (plugT' t (redex_to_term' r)).
Proof.
  dependent induction e; intros; cbn in *;
  try solve [destruct a | inv H];
  inv_decompose_match' H;
  repeat inv_dec'; cbn; f_equal;
  try solve [apply IHk + apply IHe1 + apply IHe2; auto].
  (* erewrite <- (decomposeT_inversion' _ _ _ t r); eauto. *)
  erewrite <- (decomposeW_inversion' _ _ t r); eauto.
Qed.

(* decompose' ∘ plug = id *)
Lemma decompose_plug_value' : ∀ v,
  decompose' (val_to_tm v) = dec_value' v.
Proof.
  intros; destruct v; auto.
Qed.
Lemma decompose_plug_stuck' : ∀ k e, 
  decompose' (plugK k <{ S₀ e }>) = dec_stuck' k e.
Proof.
  induction k; intros; cbn; auto.
  inv j; cbn.
  - rewrite IHk; auto.
  - rewrite decompose_plug_value'. rewrite IHk; auto.
  - rewrite IHk; auto.
Qed.
Lemma decomposeW_plug_redex : ∀ w t r,
  decompose'W w (plugT' t (redex_to_term' r)) = ((T_cons' w t), r).
Proof with cbn in *; auto.
  intros w t; generalize dependent w; induction t; intros...
  - inv r; cbn; reason; cbn in *;
    try reflexivity.
    + destruct v0... reason. reflexivity.
    + rewrite decomposeW_j_p in Heqp. reason. reflexivity.
  - reason. rewrite IHt in Heqp. reason. reflexivity.
Qed.
Lemma decompose_plug_redex' : ∀ k t r,
  decompose' (plugK k (plugT' t (redex_to_term' r))) = dec_redex' k t r.
Proof with cbn; auto.
  intros k t; generalize dependent k; induction t; intros...
  - induction k...
    + inv r; cbn; inv v; cbn; try solve [inv v0; auto]; auto.
      reason. rewrite decomposeW_j_p in Heqp. reason. reflexivity.
    + inv j; try inv v; cbn; try solve [rewrite IHk; auto].
  - induction k...
    + inv v... reason...
      rewrite decomposeW_plug_redex in Heqp. reason. reflexivity.
    + inv j; try inv v0; cbn; try solve [rewrite IHk; auto].
Qed.


Definition contract' (r : redex' ␀) : tm ␀ :=
  match r with
  (* (λ x. e) v  ~>  e [x := v] *)
  | redex_beta' (val_abs e) v => <{ e [0 := v] }>

  (* v1 $ v2  ~>  v1 v2 *)
  | redex_dollar' v1 v2 => <{ {val_to_tm v1} {val_to_tm v2} }>

  (* v $ S₀ f. e  ~>  e [f := λ x. v $ x] *)
  | redex_shift' v e => <{ e [0 := λv {↑ val_to_tm v} $ 0] }>

  (* v $ J[p]  ~> (λ x. v $ J[x]) $ p *)
  | redex_let' v j p => <{ (λ {↑ val_to_tm v} $ {plugJ (liftJ j) <{ 0 }>}) $ {non_to_tm p} }>
  end.

Definition step' e :=
  match decompose' e with
  | dec_redex' k t r => Some (plugK k (plugT' t (contract' r)))
  | _ => None
  end.

Fixpoint eval' i e :=
  match i with
  | 0 => e
  | S j =>
    match step' e with
    | Some e' => eval' j e'
    | None => e
    end
  end.

Section Examples.
  Definition _id : tm ␀ := <{ λ 0 }>.
  Definition _const : tm ␀ := <{ λ λ 1 }>.

  Compute (eval' 10 <{ _id $ _const $ S₀ 0 }>).
  Compute (eval' 10 <{ _const $ _id $ S₀ 0 }>).
End Examples.


(* v $ K[p] ~> v' $ p *)
(* Fixpoint decompose'K (v : val ␀) (k : K ␀) : val ␀.
refine (
  match k with
  | K_nil => v
  (* v $ J[K[p]] ~> (λ x. v $ J[x]) $ K[p] *)
  | K_cons j k => decompose'K (val_abs (tm_dol (↑(val_to_tm v)) (plugJ (liftJ j) <{ 0 }>))) k
  end). *)