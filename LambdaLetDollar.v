Require Export Common.
Require Export Coq.Logic.FunctionalExtensionality.

(* ANCHOR Terms
 *)
Inductive tm' {A} :=
| tm_var' : A → tm'
| tm_s_0' : tm' (* S₀ *)
| tm_abs' : @tm' ^A → tm' (* λ  x. e *)
| tm_app' : tm' → tm' → tm' (* e   e *)
| tm_dol' : tm' → tm' → tm' (* e $ e *)
| tm_let' : tm' → @tm' ^A → tm' (* let x = e1 in e2 *)
.
Arguments tm' A : clear implicits.
Global Hint Constructors tm' : core.

Inductive val' {A} :=
| val_abs' : @tm' ^A → val'
| val_s_0' : val'
.
Arguments val' A : clear implicits.
Global Hint Constructors val' : core.

Definition val_to_tm' {A} (v : val' A) := 
  match v with
  | val_abs' e => tm_abs' e
  | val_s_0' => tm_s_0'
  end.
Coercion val_to_tm' : val' >-> tm'.

Lemma inj_val' : ∀ {A} (v1 v2 : val' A),
  val_to_tm' v1 = val_to_tm' v2 → 
  v1 = v2.
Proof.
  intros. destruct v1, v2; cbn in H; auto;
  try solve [inversion H; auto].
Qed.

Inductive non' {A} :=
| non_app' : tm' A → tm'  A → non' (* e   e *)
| non_dol' : tm' A → tm'  A → non' (* e $ e *)
| non_let' : tm' A → tm' ^A → non' (* let x = e1 in e2 *)
.
Arguments non' A : clear implicits.
Global Hint Constructors non' : core.

Definition non_to_tm' {A} (p : non' A) := 
  match p with
  | non_app' e1 e2 => tm_app' e1 e2
  | non_dol' e1 e2 => tm_dol' e1 e2
  | non_let' e1 e2 => tm_let' e1 e2
  end.
Coercion non_to_tm' : non' >-> tm'.

Lemma inj_non' : ∀ {A} (p p' : non' A),
  non_to_tm' p = non_to_tm' p' → p = p'.
Proof.
  intros; destruct p, p'; cbn in *; inv H; auto.
Qed.

Declare Custom Entry λ_let_dollar_scope.
Notation "<| e |>" := e (at level 1, e custom λ_let_dollar_scope at level 99).
Notation "( x )" := x (in custom λ_let_dollar_scope, x at level 99).
Notation "{ x }" := x (in custom λ_let_dollar_scope at level 0, x constr).
Notation "x" := x (in custom λ_let_dollar_scope at level 0, x constr at level 0).
Notation "'var' v" := (tm_var' v) (in custom λ_let_dollar_scope at level 1, left associativity).
Notation "0" := <| var None |> (in custom λ_let_dollar_scope at level 0).
Notation "1" := <| var {Some None} |> (in custom λ_let_dollar_scope at level 0).
Notation "2" := <| var {Some (Some None)} |> (in custom λ_let_dollar_scope at level 0).
Notation "'λ' e" := (tm_abs' e)
    (in custom λ_let_dollar_scope at level 90,
      e custom λ_let_dollar_scope at level 99,
      right associativity).
Notation "'λv'' e" := (val_abs' e)
    (in custom λ_let_dollar_scope at level 90,
      e custom λ_let_dollar_scope at level 99,
      right associativity).
Notation "'S₀,' e" := (tm_app' tm_s_0' (tm_abs' e))
    (in custom λ_let_dollar_scope at level 90,
      e custom λ_let_dollar_scope at level 99,
      right associativity).
Notation "'S₀'" := (tm_s_0').
Notation "e1 e2" := (tm_app' e1 e2) (in custom λ_let_dollar_scope at level 10, left associativity).
Notation "e1 '$' e2" := (tm_dol' e1 e2) (in custom λ_let_dollar_scope at level 80, right associativity).
Notation "'let' e1 'in' e2" := (tm_let' e1 e2) (in custom λ_let_dollar_scope at level 70, right associativity).

Lemma lambda_to_val' : ∀ {A} (e : tm' ^A),
  <| λ e |> = <| λv' e |>.
Proof.
  reflexivity.
Qed.


Fixpoint map' {A B : Type} (f : A -> B) (e : tm' A) : tm' B :=
  match e with
  | <| var a |> => <| var {f a} |>
  | <| S₀ |> => <| S₀ |>
  | <| λ  e' |> => <| λ  {map' (option_map f) e'} |>
  | <| e1   e2 |> => <| {map' f e1}   {map' f e2} |>
  | <| e1 $ e2 |> => <| {map' f e1} $ {map' f e2} |>
  | <| let e1 in e2 |> => tm_let' (map' f e1) (map' (option_map f) e2)
  end.

Definition mapV' {A B} (f : A → B) (v : val' A) : val' B :=
  match v with
  | val_abs' e => val_abs' (map' (option_map f) e)
  | val_s_0' => val_s_0'
  end.

Lemma map_val_is_val' : ∀ {A B} (v : val' A) (f : A → B),
  ∃ w, map' f (val_to_tm' v) = val_to_tm' w.
Proof.
  intros. destruct v; cbn.
  - eexists <| λv' _ |>. reflexivity.
  - exists val_s_0'; reflexivity.
Qed.

Lemma mapV_is_map' : ∀ {A B} v (f : A → B),
  val_to_tm' (mapV' f v) = map' f (val_to_tm' v).
Proof.
  intros. destruct v; auto.
Qed.

Lemma map_map_law' : forall A e B C (f:A->B) (g:B->C),
  map' g (map' f e) = map' (g ∘ f) e.
Proof.
  intros. generalize dependent B. generalize dependent C.
  induction e; intros; cbn; auto;
  try solve [f_equal; rewrite IHe; rewrite option_map_comp_law; auto];
  try solve [rewrite IHe1; rewrite IHe2; reflexivity].
  rewrite IHe1; f_equal. rewrite IHe2.
  rewrite option_map_comp_law; auto.
Qed.

Lemma mapV_mapV_law' : forall A v B C (f : A → B) (g : B → C),
  mapV' g (mapV' f v) = mapV' (g ∘ f) v.
Proof.
  destruct v; intros; cbn; auto.
  rewrite map_map_law'.
  rewrite option_map_comp_law. reflexivity.
Qed.

Fixpoint bind' {A B : Type} (f : A -> tm' B) (e : tm' A) : tm' B :=
  match e with
  | <| var a |> => f a
  | <| S₀ |> => <| S₀ |>
  | <| e1   e2 |> => <| {bind' f e1}   {bind' f e2} |>
  | <| e1 $ e2 |> => <| {bind' f e1} $ {bind' f e2} |>
  | <| λ  e' |> => tm_abs' (bind' (fun a' => 
      match a' with
      | None   => tm_var' None
      | Some a => map' Some (f a)
      end) e')
  | <| let e1 in e2 |> => tm_let' (bind' f e1) (bind' (fun a' => 
      match a' with
      | None   => tm_var' None
      | Some a => map' Some (f a)
      end) e2)
  end.

Definition bindV' {A B} (f : A → tm' B) (v : val' A) : val' B :=
  match v with
  | val_s_0' => val_s_0'
  | val_abs' e => val_abs' (bind' (fun a' => 
      match a' with
      | None   => tm_var' None
      | Some a => map' Some (f a)
      end) e)
  end.

Lemma bind_val_is_val' : ∀ {A B} (v : val' A) (f : A → tm' B),
  ∃ w, bind' f (val_to_tm' v) = val_to_tm' w.
Proof.
  intros. destruct v; cbn.
  - eexists <| λv' _ |>. reflexivity.
  - eexists val_s_0'. reflexivity.
Qed.

Lemma bindV_is_bind' : ∀ {A B} v (f : A → tm' B),
  val_to_tm' (bindV' f v) = bind' f (val_to_tm' v).
Proof.
  intros. destruct v; auto.
Qed.

Lemma bind_map_law' : ∀ {A B C} (f : B → tm' C) (g : A → B) e,
  bind' f (map' g e) = bind' (λ a, f (g a)) e.
Proof.
  intros. generalize dependent B. generalize dependent C.
  induction e; intros; cbn; auto;
  try solve [f_equal; rewrite IHe; f_equal; apply functional_extensionality; intros [a|]; cbn; auto];
  try solve [f_equal; apply IHe1 + apply IHe2].
  rewrite IHe1; f_equal. rewrite IHe2.
  f_equal; apply functional_extensionality; intros [a|]; cbn; auto.
Qed.

Lemma bind_pure' : ∀ {A} (e : tm' A),
  bind' (λ a, <| var a |>) e = e.
Proof.
  induction e; cbn; auto;
  try solve [f_equal; rewrite <- IHe at 2; f_equal; apply functional_extensionality; intros [a|]; cbn; auto];
  try solve [f_equal; apply IHe1 + apply IHe2].
  rewrite IHe1; f_equal. rewrite <- IHe2 at 2.
  f_equal; apply functional_extensionality; intros [a|]; cbn; auto.
Qed.

Lemma map_bind_law' : ∀ {A B C} (f : A → tm' B) (g : B → C) e,
  bind' (map' g ∘ f) e = map' g (bind' f e).
Proof.
  intros; generalize dependent B; generalize dependent C; induction e; intros; cbn; auto;
  try solve [
    rewrite <- IHe; repeat f_equal; apply functional_extensionality; intros [a|]; auto; cbn;
    change ((map' g ∘ f) a) with (map' g (f a));
    repeat rewrite map_map_law'; f_equal];
  try solve [f_equal; apply IHe1 + apply IHe2].
  rewrite IHe1; f_equal. rewrite <- IHe2.
  f_equal; apply functional_extensionality; intros [a|]; cbn; auto.
  change ((map' g ∘ f) a) with (map' g (f a)); repeat rewrite map_map_law'; f_equal.
Qed.

Lemma map_as_bind' : ∀ {A B} e (f : A → B),
  map' f e = bind' (tm_var' ∘ f) e.
Proof.
  intros; generalize dependent B; induction e; intros; cbn; auto;
  try solve [rewrite IHe; repeat f_equal; apply functional_extensionality; intros [a|]; auto];
  try solve [rewrite IHe1; rewrite IHe2; reflexivity].
  rewrite IHe1; f_equal. rewrite IHe2; f_equal.
  apply functional_extensionality; intros [a|]; auto.
Qed.


Definition var_subst' {V} e' (v:^V) :=
  match v with
  | None => e'
  | Some v => <| var v |>
  end.

Definition tm_subst0' {V} (e:tm' ^V) (v:val' V) :=
  bind' (var_subst' (val_to_tm' v)) e.

Notation "e [ 0 := v ]" := (tm_subst0' e v)
  (in custom λ_let_dollar_scope at level 0,
    e custom λ_let_dollar_scope,
    v custom λ_let_dollar_scope at level 99).


Class Plug' (E : Type → Type) := plug' : ∀ {A}, E A → tm' A → tm' A.

Notation "E [ e ]" := (plug' E e)
  (in custom λ_let_dollar_scope at level 70,
    e custom λ_let_dollar_scope at level 99).


Definition tm_dec' (e : tm' ␀) : (val' ␀ + non' ␀) :=
  match e with
  | <| var a |> => from_void a
  | <| S₀ |> => inl val_s_0'
  | <| λ  e' |> => inl (val_abs' e')
  | <| e1   e2 |> => inr (non_app' e1 e2)
  | <| e1 $ e2 |> => inr (non_dol' e1 e2)
  | <| let e1 in e2 |> => inr (non_let' e1 e2)
  end.
Lemma tm_dec_val' : ∀ e v, tm_dec' e = inl v → e = val_to_tm' v.
Proof.
  intros; inv e; cbn in *; try destruct a; inv H; auto.
Qed.
Lemma tm_dec_non' : ∀ e p, tm_dec' e = inr p → e = non_to_tm' p.
Proof.
  intros; inv e; cbn in *; try destruct a; inv H; auto.
Qed.
Lemma tm_dec_of_val' : ∀ v, tm_dec' (val_to_tm' v) = inl v.
Proof.
  intros; destruct v; auto.
Qed.
Lemma tm_dec_of_non' : ∀ p, tm_dec' (non_to_tm' p) = inr p.
Proof.
  intros; destruct p; auto.
Qed.

Ltac reason := repeat(
  rewrite tm_dec_of_val' in * +
  rewrite tm_dec_of_non' in * +
  match goal with
  | H : ␀ |- _ => destruct H
  | H : (_, _) = (_, _) |- _ => inj H
  | H : val_to_tm' _ = val_to_tm' _ |- _ => apply inj_val' in H; rewrite H in *
  | H : non_to_tm' _ = non_to_tm' _ |- _ => apply inj_non' in H; rewrite H in *
  | H : inl ?v = tm_dec' ?e |- _ => rewrite (tm_dec_val' e v (eq_sym H)) in *; auto
  | H : inr ?p = tm_dec' ?e |- _ => rewrite (tm_dec_non' e p (eq_sym H)) in *; auto
  | H : context C [let (_, _) := ?e in _] |- _ =>
    let p := fresh "p" in remember e as p; inv p
  | |- context C [let (_, _) := ?e in _] => 
    let p := fresh "p" in remember e as p; inv p
  | H : context C [match tm_dec' ?e with inl _ => _ | inr _ => _ end] |- _ =>
    let td := fresh "td" in
    let Hd := fresh "Hd" in
    remember (tm_dec' e) as td eqn: Hd; inv td; try rewrite Hd in *
  | H : context C [match ?v with val_abs' _ => _ | val_s_0' => _ end] |- _ =>
    destruct v; inversion H; clear H; subst
  end).


(* ANCHOR Contexts
 *)
Section Contexts.
  Context {A : Type}.
  Inductive J' :=
  | J_fun' : tm'  A → J'  (* [] M *)
  | J_arg' : val' A → J'  (* V [] *)
  | J_dol' : tm'  A → J'  (* []$M *)
  .
  Inductive K' :=
  | K_nil'  : K'
  | K_let'  : K' → tm' ^A → K' (* let x = K in e *)
  .

  Inductive T' :=
  | T_nil'  : T'
  | T_cons' : val' A → K' → T' → T'  (* (v$K) · T *)
  .

  Inductive redex' :=
  | redex_beta'      : tm' ^A → val' A → redex'  (* (λ e) v *)
  | redex_dollar'    : val' A → val' A → redex'  (* v $ v' *)
  | redex_shift'     : val' A → val' A → redex'  (* v $ S₀ v' *)
  | redex_dol_let'   : val' A → val' A → tm' ^A → redex' (* v $ let x = S₀ v1 in e2 *)
  | redex_let'       : J'     → non' A → redex'  (* J[p] *)
  | redex_let_beta'  : val' A → tm' ^A → redex'  (* let x = v in e *)
  | redex_let_assoc' : val' A → tm' ^A → tm' ^A → redex' (* let x = (let y = S₀ v1 in e2) in e3 *)
  .

  Inductive dec' :=
  | dec_value' : val' A → dec'
  | dec_stuck_s_0' : val' A → dec' (* S₀ v *)
  | dec_stuck_let' : val' A → tm' ^A → dec' (* let x = S₀ v in e *)
  | dec_redex' : K' → T' → redex' → dec' (* K[T[Redex]] *)
  .
End Contexts.
Arguments J' A : clear implicits.
Arguments K' A : clear implicits.
Arguments T' A : clear implicits.
Arguments redex' A : clear implicits.
Arguments dec' A : clear implicits.

Definition plugJ' {A} (j : J' A) e' :=
  match j with
  | J_fun' e => <| e' e |>
  | J_arg' v => <| v  e' |>
  | J_dol' e => <| e' $ e |>
  end.
Instance PlugJ' : Plug' J' := @plugJ'.

Fixpoint plugK' {A} (k : K' A) e :=
  match k with
  | K_nil' => e
  | K_let' k1 e2 => <| let {plugK' k1 e} in e2 |>
  end.
Instance PlugK' : Plug' K' := @plugK'.

Fixpoint plugT' {A} (trail : T' A) e :=
  match trail with
  | T_nil' => e
  | T_cons' v k t => <| v $ k [{plugT' t e}] |>
  end.
Instance PlugT' : Plug' T' := @plugT'.

Definition redex_to_term' {A} (r : redex' A) := 
  match r with
  | redex_beta'   e v => <| (λ e) v |>
  | redex_dollar' v1 v2 => <| v1 $ v2 |>
  | redex_shift'  v  v' => <| v  $ S₀ v' |>
  | redex_dol_let' v v1 e2 => <| v $ let S₀ v1 in e2 |>
  | redex_let' j p  => <| j[p] |>
  | redex_let_beta' v e => <| let v in e |>
  | redex_let_assoc' v1 e2 e3 => <| let (let S₀ v1 in e2) in e3 |>
  end.
Coercion redex_to_term' : redex' >-> tm'.

(* ANCHOR Decompose
 *)
Fixpoint decompose' (e : tm' ␀) : dec' ␀ :=
  match e with
  | <| var a |> => from_void a
  | <| S₀    |> => dec_value' val_s_0'
  | <| λ  e' |> => dec_value' (val_abs' e')
  | <| e1 e2 |> =>
    match tm_dec' e1 with
    | inr p1 => dec_redex' K_nil' T_nil' (redex_let' (J_fun' e2) p1)   (* p1 e2 *)
    | inl v1 =>
      match tm_dec' e2 with
      | inr p2 => dec_redex' K_nil' T_nil' (redex_let' (J_arg' v1) p2) (* v1 p2 *)
      | inl v2 =>
        match v1 with
        | val_abs' t => dec_redex' K_nil' T_nil' (redex_beta' t v2)    (* (λ t) v2 *)
        | val_s_0' => dec_stuck_s_0' v2                                (* S₀ v2 *)
        end
      end
    end
  | <| e1 $ e2 |> =>
    match tm_dec' e1 with
    | inr p1 => dec_redex' K_nil' T_nil' (redex_let' (J_dol' e2) p1) (* p1 $ e2 *)
    | inl v1 => (* v1 $ e *)
      match decompose' e2 with
      | dec_stuck_s_0' v2'       => dec_redex' K_nil' (T_nil')         (redex_shift' v1 v2')         (* v1 $ S₀ v2' *)
      | dec_stuck_let' v2_1 e2_2 => dec_redex' K_nil' (T_nil')         (redex_dol_let' v1 v2_1 e2_2) (* v1 $ let x = S₀ v2_1 in e2_2 *)
      | dec_redex' k t r         => dec_redex' K_nil' (T_cons' v1 k t) (r)                           (* v1 $ K[T[r]] *)
      | dec_value' v2            => dec_redex' K_nil' (T_nil')         (redex_dollar' v1 v2)         (* v1 $ v2 *)
      end
    end
  | <| let e1 in e2 |> =>
    match decompose' e1 with
    | dec_stuck_s_0' v1'       => dec_stuck_let' v1' e2                                           (* let x = S₀ v1' in e2 *)
    | dec_stuck_let' v1_1 e1_2 => dec_redex' (K_nil')      T_nil' (redex_let_assoc' v1_1 e1_2 e2) (* let x = (let y = S₀ v1_1 in e1_2) in e2 *)
    | dec_redex' k t r         => dec_redex' (K_let' k e2) t      (r)                             (* let x = K[T[r]] in e2 *)
    | dec_value' v1            => dec_redex' (K_nil')      T_nil' (redex_let_beta' v1 e2)         (* let x = v1 in e2 *)
    end
  end.


Ltac inv_decompose_match' H :=
  match goal with
  | H : (match decompose' ?e with | dec_stuck_s_0' _ | dec_stuck_let' _ _ | dec_redex' _ _ _ | dec_value' _ => _ end = _) |- _ =>
    let d := fresh "d" in remember (decompose' e) as d; inv d; inv_decompose_match' H
  | H : (let (_,_) := ?e in _) = _ |- _ =>
    let d := fresh "d" in remember e as d; inv d; inv_decompose_match' H
  | _ => try solve [inversion H; auto]; try inj H
  end.


Lemma inj_plug_j' : ∀ {A} (j1 j2 : J' A) (p1 p2 : non' A),
  <| j1[p1] |> = <| j2[p2] |> →
  j1 = j2 /\ p1 = p2.
Proof.
  intros;
  destruct j1, j2; cbn in *; inversion H; clear H; reason; subst; auto;
  solve [destruct p1 + destruct p2; destruct v; inversion H1; auto].
Qed.

Lemma inj_redex' : ∀ {A} (r r' : redex' A),
  redex_to_term' r = redex_to_term' r' → r = r'.
Proof.
  intros; destruct r, r'; cbn in *; inversion H; clear H; reason; subst; auto;
  try apply inj_val' in H1; try apply inj_val' in H2; subst; auto;
  try solve [destruct j; cbn in *; inversion H1; auto];
  try solve [destruct j; destruct v; destruct n; cbn in *; inversion H1; auto];
  try solve [destruct v0 + destruct v2; inversion H2].
  apply inj_plug_j' in H1 as [H1 H2]; subst; auto.
  destruct v; inversion H1.
  destruct v0; inversion H1.
Qed.


(* ANCHOR Unique Decomposition
 *)
(* plug' ∘ decompose' = id *)
Lemma decompose_value_inversion' : ∀ e v,
  decompose' e = dec_value' v → e = val_to_tm' v.
Proof.
  intros. inv e; cbn in *.
  - destruct a.
  - destruct v; inversion H; clear H; subst. auto.
  - inj H; auto.
  - reason; inversion H.
  - reason; inv_decompose_match' H.
  - inv_decompose_match' H.
Qed.
Lemma decompose_stuck_s_0_inversion' : ∀ e v,
  decompose' e = dec_stuck_s_0' v → e = <| S₀ v |>.
Proof.
  intros. inv e; cbn in *; reason; auto;
  try solve [inversion a | inv H];
  inv_decompose_match' H.
Qed.
Lemma decompose_stuck_let_inversion' : ∀ e v1 e2,
  decompose' e = dec_stuck_let' v1 e2 → e = <| let S₀ v1 in e2 |>.
Proof.
  intros. inv e; cbn in *; reason; auto;
  try solve [inversion a | inv H];
  inv_decompose_match' H.
  rewrite (decompose_stuck_s_0_inversion' e1 v1); auto.
Qed.
Ltac inv_dec' :=
  match goal with
  | H : dec_value' ?v = decompose' ?e |- _ => rewrite (decompose_value_inversion' e v); cbn; auto
  | H : dec_stuck_s_0' ?e' = decompose' ?e |- _ => rewrite (decompose_stuck_s_0_inversion' e e'); cbn; auto
  | H : dec_stuck_let' ?e1 ?e2 = decompose' ?e |- _ => rewrite (decompose_stuck_let_inversion' e e1 e2); cbn; auto
  end.
Lemma decompose_redex_inversion' : ∀ e t k r,
  decompose' e = dec_redex' k t r → e = <| k[t[r]] |>.
Proof.
  dependent induction e; intros; cbn in *; reason; auto;
  try solve [destruct a | inv H];
  inv_decompose_match' H;
  repeat inv_dec'; cbn; f_equal;
  try solve [apply IHk + apply IHe1 + apply IHe2; auto].
Qed.

(* decompose' ∘ plug' = id *)
Lemma decompose_plug_value' : ∀ v,
  decompose' (val_to_tm' v) = dec_value' v.
Proof.
  intros; destruct v; auto.
Qed.
Lemma decompose_plug_stuck_s_0' : ∀ (v : val' ␀), 
  decompose' <| S₀ v |> = dec_stuck_s_0' v.
Proof.
  intros; destruct v; cbn; auto.
Qed.
Lemma decompose_plug_stuck_let' : ∀ (v : val' ␀) e,
  decompose' <| let S₀ v in e |> = dec_stuck_let' v e.
Proof.
  intros; destruct v; cbn; auto.
Qed.
Lemma decompose_plug_redex' : ∀ k t (r : redex' ␀),
  decompose' <| k[t[r]] |> = dec_redex' k t r.
Proof with cbn; auto.
  intros k t; generalize dependent k; induction t; intros...
  - induction k...
    + inv r; cbn; try inv v; cbn; try solve [inv v0; auto]; auto.
      inv j; cbn; reason; reflexivity.
    + rewrite IHk; reflexivity.
  - induction k0...
    + inv v; rewrite IHt...
    + rewrite IHk0. reflexivity.
Qed.


Instance LiftTm' : Lift tm' := λ {A}, map' Some.

Definition liftV' {A : Type} (v : val' A) : val' ^A := mapV' Some v.

Lemma lift_val_to_tm' : ∀ {A} (v : val' A),
  ↑ (val_to_tm' v) = val_to_tm' (liftV' v).
Proof.
  intros. destruct v; cbn; reflexivity.
Qed.

Definition mapJ' {A B} (f : A → B) (j : J' A) : J' B := 
  match j with
  | J_fun' e => J_fun' (map' f e)
  | J_arg' v => J_arg' (mapV' f v)
  | J_dol' e => J_dol' (map' f e)
  end.

Lemma mapJ_mapJ_law' : forall A j B C (f : A → B) (g : B → C),
  mapJ' g (mapJ' f j) = mapJ' (g ∘ f) j.
Proof.
  destruct j; intros; cbn;
  try rewrite map_map_law';
  try rewrite mapV_mapV_law';
  auto.
Qed.

Fixpoint mapK' {A B} (f : A → B) (k : K' A) : K' B := 
  match k with
  | K_nil' => K_nil'
  | K_let' k1 e2 => K_let' (mapK' f k1) (map' (option_map f) e2)
  end.

Lemma mapK_mapK_law' : forall A k B C (f : A → B) (g : B → C),
  mapK' g (mapK' f k) = mapK' (g ∘ f) k.
Proof.
  induction k; intros; cbn; auto.
  rewrite IHk.
  rewrite map_map_law'.
  rewrite option_map_comp_law.
  reflexivity.
Qed.

Instance LiftJ' : Lift J' := λ {A}, mapJ' Some.

Instance LiftK' : Lift K' := λ {A}, mapK' Some.

Definition bindJ' {A B} (f : A → tm' B) (j : J' A) : J' B := 
  match j with
  | J_fun' e => J_fun' (bind' f e)
  | J_arg' v => J_arg' (bindV' f v)
  | J_dol' e => J_dol' (bind' f e)
  end.

Fixpoint bindK' {A B} (f : A → tm' B) (k : K' A) : K' B := 
  match k with
  | K_nil' => K_nil'
  | K_let' k1 e2 => K_let' (bindK' f k1) (bind' (fun a' => 
      match a' with
      | None   => tm_var' None
      | Some a => map' Some (f a)
      end) e2)
  end.

Lemma bindV_mapV_law' : ∀ {A B C} (f : B → tm' C) (g : A → B) v,
  bindV' f (mapV' g v) = bindV' (λ a, f (g a)) v.
Proof.
  intros.
  apply inj_val'. repeat rewrite bindV_is_bind'. rewrite mapV_is_map'.
  apply bind_map_law'.
Qed.

Lemma bindJ_mapJ_law' : ∀ {A B C} (f : B → tm' C) (g : A → B) j,
  bindJ' f (mapJ' g j) = bindJ' (λ a, f (g a)) j.
Proof.
  intros; destruct j; cbn; auto;
  rewrite bind_map_law' + rewrite bindV_mapV_law'; auto.
Qed.

Lemma bindK_mapK_law' : ∀ {A B C} (f : B → tm' C) (g : A → B) k,
  bindK' f (mapK' g k) = bindK' (λ a, f (g a)) k.
Proof.
  intros. generalize dependent B. generalize dependent C.
  induction k; intros; cbn; auto.
  rewrite IHk; f_equal.
  rewrite bind_map_law'; f_equal.
  apply functional_extensionality; intros [a|]; cbn; auto.
Qed.

Lemma mapV_bindV_law' : ∀ {A B C} (f : A → tm' B) (g : B → C) v,
  bindV' (map' g ∘ f) v = mapV' g (bindV' f v).
Proof.
  intros. apply inj_val'. rewrite mapV_is_map'. repeat rewrite bindV_is_bind'. apply map_bind_law'.
Qed.

Lemma mapJ_bindJ_law' : ∀ {A B C} (f : A → tm' B) (g : B → C) j,
  bindJ' (map' g ∘ f) j = mapJ' g (bindJ' f j).
Proof.
  intros; destruct j; intros; cbn; auto;
  rewrite map_bind_law' + rewrite mapV_bindV_law'; auto.
Qed.

Lemma mapK_bindK_law' : ∀ {A B C} (f : A → tm' B) (g : B → C) k,
  bindK' (map' g ∘ f) k = mapK' g (bindK' f k).
Proof.
  intros; generalize dependent B; generalize dependent C; induction k; intros; cbn; auto.
  rewrite IHk; f_equal.
  rewrite <- map_bind_law'; f_equal.
  apply functional_extensionality; intros [a|]; cbn; auto.
  change ((map' g ∘ f) a) with (map' g (f a)); repeat rewrite map_map_law'; f_equal.
Qed.


(* ANCHOR Evaluation
 *)
Definition contract' (r : redex' ␀) : tm' ␀ :=
  match r with
  (* (λ x. e) v  ~>  e [x := v] *)
  | redex_beta' e v => <| e [0 := v] |>

  (* v1 $ v2  ~>  v1 v2 *)
  | redex_dollar' v1 v2 => <| v1 v2 |>

  (* v $ S₀ w  ~>  w v *)
  | redex_shift' v w  => <| w v |>

  (* v $ let x = S₀ w in e  ~>  (λ x. v $ e) $ S₀ w *)
  | redex_dol_let' v w e => <| (λ {liftV' v} $ e) $ S₀ w |>

  (* J[p]  ~>  let x = p in J[x] *)
  | redex_let' j p => <| let p in ↑j[0] |>

  (* let x = v in e  ~>  e [x := v] *)
  | redex_let_beta' v e => <| e [0 := v] |>

  (* let x = (let y = S₀ v1 in e2) in e3  ~>  let y = S₀ v1 in let x = e2 in e3 *)
  | redex_let_assoc' v1 e2 e3 => <| let S₀ v1 in let e2 in {map' (option_map Some) e3} |>
  end.

Definition optional_step' e :=
  match decompose' e with
  | dec_redex' k t r => Some <| k[t[{contract' r}]] |>
  | _ => None
  end.

Reserved Notation "e1 ~>' e2" (at level 40).
Inductive contr' : tm' ␀ → tm' ␀ → Prop :=
| contr_tm' : ∀ r, redex_to_term' r ~>' contract' r
where "e1 ~>' e2" := (contr' e1 e2).
Global Hint Constructors contr' : core.

Reserved Notation "e1 -->' e2" (at level 40).
Inductive step' : tm' ␀ → tm' ␀ → Prop :=
| step_tm' : ∀ (k : K' ␀) (t : T' ␀) (e1 e2 : tm' ␀), e1 ~>' e2 → <| k[t[e1]] |> -->' <| k[t[e2]] |>
where "e1 -->' e2" := (step' e1 e2).
Global Hint Constructors step' : core.

Notation "e1 -->'* e2" := (multi step' e1 e2) (at level 40).

Lemma step_contr' : ∀ {e1 e2},
  e1 ~>' e2 →
  e1 -->' e2.
Proof.
  intros.
  apply (step_tm' K_nil' T_nil' e1 e2).
  assumption.
Qed.
Lemma multi_contr' : ∀ {e1 e2},
  e1 ~>' e2 →
  e1 -->'* e2.
Proof.
  intros. apply (multi_step _ _ _ _ (step_contr' H)); auto.
Qed.
Lemma multi_contr_multi' : ∀ {e1 e2 e3},
  e1 ~>' e2 →
  e2 -->'* e3 →
  e1 -->'* e3.
Proof.
  intros. eapply multi_step; try eapply (step_tm' K_nil' T_nil'); cbn; eassumption.
Qed.
Definition contr_beta' : ∀ e (v : val' ␀), <| (λ e) v |> ~>' <| e [ 0 := v ] |> := λ e v, contr_tm' (redex_beta' e v).
Definition contr_dollar' : ∀ (v1 v2 : val' ␀), <| v1 $ v2 |> ~>' <| v1 v2 |> := λ v1 v2, contr_tm' (redex_dollar' v1 v2).
Definition contr_shift' : ∀ (v w : val' ␀), <| v $ S₀ w |> ~>' <| w v |> := λ v w, contr_tm' (redex_shift' v w).
Definition contr_dol_let' : ∀ (v v1 : val' ␀) e2, <| v $ let S₀ v1 in e2 |> ~>' <| (λ {liftV' v} $ e2) $ S₀ v1 |> := λ v v1 e2, contr_tm' (redex_dol_let' v v1 e2).
Definition contr_let' : ∀ (j : J' ␀) (p : non' ␀), <| j[p] |> ~>' <| let p in ↑j[0] |> := λ j p, contr_tm' (redex_let' j p).
Definition contr_let_beta' : ∀ (v : val' ␀) e, <| let v in e |> ~>' <| e [ 0 := v ] |> := λ v e, contr_tm' (redex_let_beta' v e).
Definition contr_let_assoc' : ∀ (v1 : val' ␀) e2 e3, <| let (let S₀ v1 in e2) in e3 |> ~>' <| let S₀ v1 in let e2 in {map' (option_map Some) e3} |> := λ v1 e2 e3, contr_tm' (redex_let_assoc' v1 e2 e3).
Global Hint Resolve step_contr' contr_beta' contr_dollar' contr_shift' contr_dol_let' contr_let' contr_let_beta' contr_let_assoc' : core.

Lemma deterministic_contr' : ∀ e e1 e2,
  e ~>' e1 →
  e ~>' e2 →
  e1 = e2.
Proof.
  intros e e1 e2 H1 H2.
  inversion H1; clear H1; subst. 
  inversion H2; clear H2; subst.
  apply inj_redex' in H0; subst; reflexivity.
Qed.

Lemma redex_when_contr' : ∀ e1 e2,
  e1 ~>' e2 →
  ∃ r1, e1 = redex_to_term' r1.
Proof.
  intros. inversion H; clear H; subst.
  exists r; auto.
Qed.

Lemma deterministic_step' : ∀ e e1 e2,
  e -->' e1 →
  e -->' e2 →
  e1 = e2.
Proof.
  intros e e1 e2 H1 H2.
  inversion H1; clear H1; subst. 
  inversion H2; clear H2; subst.
  apply redex_when_contr' in H as HH; destruct HH as [r0 HH]; subst.
  apply redex_when_contr' in H1 as HH; destruct HH as [r1 HH]; subst.
  assert (dec_redex' k0 t0 r1 = dec_redex' k t r0) as Hktr.
  { repeat rewrite <- decompose_plug_redex'. f_equal; assumption. }
  inversion Hktr; clear Hktr; subst.
  repeat f_equal.
  apply (deterministic_contr' r0); assumption.
Qed.

Fixpoint eval' i e :=
  match i with
  | 0 => e
  | S j =>
    match optional_step' e with
    | Some e' => eval' j e'
    | None => e
    end
  end.

Section Examples.
  Definition _id : tm' ␀ := <| λ 0 |>.
  Definition _const : tm' ␀ := <| λ λ 1 |>.

  Compute (eval' 10 <| _id $ _const $ S₀, 0 |>).
  Compute (eval' 10 <| _const $ _id $ S₀, 0 |>).

  Definition j1 : J' ␀ := J_fun' <| λ 0 0 |>.
  Definition j2 : J' ␀ := J_arg' <| λv' 0 |>.
  Definition j3 : J' ␀ := J_dol' <| λ 0 |>.
  Definition ej123 := <| j1[j2[j3[S₀, 0]]] |>.

  Example from_K_to_K' : eval' 3 ej123 = <| 
    let
      let
        let S₀, 0
        in ↑j3[0]
      in ↑j2[0]
    in ↑j1[0]
  |>. Proof. auto. Qed.

  Example from_K_to_stuck' : eval' 5 ej123 = <| 
    let S₀, 0 in
    let
        let ↑j3[0]
        in ↑↑j2[0]
    in ↑↑j1[0]
  |>. Proof. cbn. auto. Qed.

  Example ex_dol_let : eval' 6 <| _id $ ej123 |> = <| 
    (λ ↑_id $ 
      let
        let ↑j3[0]
        in ↑↑j2[0]
      in ↑↑j1[0]
    ) $ S₀, 0
  |>. Proof. cbn. auto. Qed.

  Example ex_shift : eval' 8 <| _id $ ej123 |> = <|
    λ ↑_id $ let (let ↑j3[0] in ↑↑j2[0]) in ↑↑j1[0]
  |>. Proof. cbn. auto. Qed.

  Compute (decompose' (eval' 8 <| _id $ ej123 |>)).
  
End Examples.


Lemma plug_non_is_non' : ∀ (k' : K' ␀) (t' : T' ␀) (p' : non' ␀),
  ∃ p'', <| k' [t' [p']] |> = non_to_tm' p''.
Proof.
  intros; destruct k'; cbn in *.
  destruct t'; cbn in *.
  eexists; reflexivity.
  eexists (non_dol' _ _); reflexivity.
  eexists (non_let' _ _); reflexivity.
Qed.

Lemma redex_is_non' : ∀ {A} r', ∃ p', @redex_to_term' A r' = non_to_tm' p'.
Proof.
  intros. destruct r'; cbn;
  try solve [try destruct j; eexists (non_app' _ _) + eexists (non_dol' _ _) + eexists (non_let' _ _); reflexivity].
Qed.

Lemma non_when_contr' : ∀ e' e'',
  e' ~>' e'' →
  ∃ p', e' = non_to_tm' p'.
Proof.
  intros. inversion H; clear H; subst.
  apply redex_is_non'.
Qed.

Lemma non_when_step' : ∀ e' e'',
  e' -->' e'' →
  ∃ p', e' = non_to_tm' p'.
Proof.
  intros. inversion H; clear H; subst.
  apply non_when_contr' in H0 as [p' Hp]; subst.
  apply plug_non_is_non'.
Qed.

Lemma non_when_steps_to_non' : ∀ e' (p'' : non' ␀),
  e' -->'* p'' →
  ∃ p', e' = non_to_tm' p'.
Proof.
  intros. dependent induction H. exists p''. reflexivity.
  destruct (IHmulti p'') as [p' IH]; auto; subst.
  apply (non_when_step' x p'); auto.
Qed.

Lemma non_when_steps_to_plug_non' : ∀ e (k' : K' ␀) (t' : T' ␀) (p' : non' ␀),
  e -->'* <| k' [t' [p']] |> →
  ∃ p, e = non_to_tm' p.
Proof.
  intros. destruct (plug_non_is_non' k' t' p') as [p'' Hp''].
  apply (non_when_steps_to_non' _ p''). rewrite Hp'' in *. assumption.
Qed.


Lemma step_let' : ∀ {e1 e2 e},
  e1 -->' e2 →
  <| let e1 in e |> -->' <| let e2 in e |>.
Proof.
  intros. generalize dependent e.
  induction H; auto; intros.
  apply (step_tm' (K_let' k e) t e1 e2).
  apply H.
Qed.

Lemma multi_let' : ∀ {e1 e2 e},
  e1 -->'* e2 →
  <| let e1 in e |> -->'* <| let e2 in e |>.
Proof.
  intros. generalize dependent e.
  induction H; auto; intros.
  eapply (multi_step); [idtac | apply IHmulti].
  apply step_let'.
  apply H.
Qed.

Lemma step_delim' : ∀ {v : val' ␀} {e1 e2},
  e1 -->' e2 →
  <| v $ e1 |> -->' <| v $ e2 |>.
Proof.
  intros. generalize dependent v.
  induction H; auto; intros.
  apply (step_tm' K_nil' (T_cons' v k t) e1 e2).
  apply H.
Qed.

Lemma multi_delim' : ∀ {v : val' ␀} {e1 e2},
  e1 -->'* e2 →
  <| v $ e1 |> -->'* <| v $ e2 |>.
Proof.
  intros. generalize dependent v.
  induction H; auto; intros.
  eapply (multi_step); [idtac | apply IHmulti].
  apply step_delim'.
  apply H.
Qed.

Lemma step_k' : ∀ {e1 e2} {k : K' ␀},
  e1 -->' e2 →
  <| k[e1] |> -->' <| k[e2] |>.
Proof.
  intros e1 e2 k; generalize dependent e1; generalize dependent e2.
  induction k; auto; intros.
  cbn. apply step_let'. apply IHk. apply H.
Qed.

Lemma multi_k' : ∀ {e1 e2} {k : K' ␀},
  e1 -->'* e2 →
  <| k[e1] |> -->'* <| k[e2] |>.
Proof.
  intros. generalize dependent k.
  induction H; auto; intros.
  eapply (multi_step); [idtac | apply IHmulti].
  apply step_k'.
  apply H.
Qed.

Lemma step_t' : ∀ {e1 e2} {t : T' ␀},
  e1 -->' e2 →
  <| t[e1] |> -->' <| t[e2] |>.
Proof.
  intros e1 e2 t; generalize dependent e1; generalize dependent e2.
  induction t; auto; intros.
  cbn. apply step_delim'. apply step_k'. apply IHt. apply H.
Qed.

Lemma multi_t' : ∀ {e1 e2} {t : T' ␀},
  e1 -->'* e2 →
  <| t[e1] |> -->'* <| t[e2] |>.
Proof.
  intros. generalize dependent t.
  induction H; auto; intros.
  eapply (multi_step); [idtac | apply IHmulti].
  apply step_t'.
  apply H.
Qed.


Lemma lift_map' : ∀ {A B} (e : tm' A) (f : A → B),
  ↑(map' f e) = map' (option_map f) (↑e).
Proof.
  intros.
  unfold lift. unfold LiftTm'.
  repeat rewrite map_map_law'.
  f_equal.
Qed.

Lemma bind_lift' : ∀ {A B} e (f : ^A → tm' B),
  bind' f (↑e) = bind' (f ∘ Some) e.
Proof.
  intros.
  unfold lift. unfold LiftTm'.
  rewrite bind_map_law'. f_equal.
Qed.

Lemma bindJ_lift' : ∀ {A B} j (f : ^A → tm' B),
  bindJ' f (↑j) = bindJ' (f ∘ Some) j.
Proof.
  intros.
  unfold lift. unfold LiftJ'.
  rewrite bindJ_mapJ_law'. f_equal.
Qed.

Lemma bindK_lift' : ∀ {A B} k (f : ^A → tm' B),
  bindK' f (↑k) = bindK' (f ∘ Some) k.
Proof.
  intros.
  unfold lift. unfold LiftK'.
  rewrite bindK_mapK_law'. f_equal.
Qed.

Lemma lift_bind' : ∀ {A B} e (f : A → tm' B),
  ↑(bind' f e) = bind' (lift ∘ f) e.
Proof.
  intros.
  unfold lift. unfold LiftTm'.
  rewrite map_bind_law'. reflexivity.
Qed.

Lemma lift_bindJ' : ∀ {A B} j (f : A → tm' B),
  ↑(bindJ' f j) = bindJ' (lift ∘ f) j.
Proof.
  intros.
  unfold lift. unfold LiftJ'. unfold LiftTm'.
  rewrite mapJ_bindJ_law'. reflexivity.
Qed.

Lemma lift_bindK' : ∀ {A B} k (f : A → tm' B),
  ↑(bindK' f k) = bindK' (lift ∘ f) k.
Proof.
  intros.
  unfold lift. unfold LiftK'. unfold LiftTm'.
  rewrite mapK_bindK_law'. reflexivity.
Qed.

Lemma map_plug_j_is_plug_of_maps' : ∀ {A B} j e (f : A → B),
  map' f <| j[e] |> = <| {mapJ' f j} [{map' f e}] |>.
Proof.
  intros. destruct j; cbn; try destruct v; auto.
Qed.

Lemma map_plug_k_is_plug_of_maps' : ∀ {A B} (k : K' A) e (f : A → B),
  map' f <| k[e] |> = <| {mapK' f k} [{map' f e}] |>.
Proof.
  intros A B. generalize dependent B.
  induction k; intros; cbn; auto.
  rewrite IHk. reflexivity.
Qed.

Lemma bind_plug_j_is_plug_of_binds' : ∀ {A B} j e (f : A → tm' B),
  bind' f <| j[e] |> = <| {bindJ' f j} [{bind' f e}] |>.
Proof.
  intros. destruct j; cbn; try destruct v; auto.
Qed.

Lemma bind_plug_k_is_plug_of_binds' : ∀ {A B} (k : K' A) e (f : A → tm' B),
  bind' f <| k[e] |> = <| {bindK' f k} [{bind' f e}] |>.
Proof.
  intros A B. generalize dependent B.
  induction k; intros; cbn; auto.
  rewrite IHk. reflexivity.
Qed.

Lemma lift_tm_abs' : ∀ {A} (e : tm' ^A),
  <| λ {map' (option_map Some) e} |> = ↑<| λ e |>.
Proof.
  reflexivity.
Qed.

Lemma lift_mapJ' : ∀ {A B} j (f : A → B),
  ↑(mapJ' f j) = mapJ' (option_map f) (↑j).
Proof.
  intros. destruct j; cbn;
  repeat rewrite map_map_law';
  repeat rewrite mapV_mapV_law';
  f_equal.
Qed.

Lemma lift_mapK' : ∀ {A B} k (f : A → B),
  ↑(mapK' f k) = mapK' (option_map f) (↑k).
Proof.
  intros. unfold lift. unfold LiftK'.
  repeat rewrite mapK_mapK_law'.
  f_equal.
Qed.

Lemma subst_lift' : ∀ {A} (e : tm' A) v,
  <| (↑e) [0 := v] |> = e.
Proof.
  intro A.
  unfold tm_subst0' .
  unfold lift. unfold LiftTm'.
  intros. rewrite bind_map_law'. apply bind_pure'.
Qed.

Lemma bind_var_subst_lift' : ∀ {A} (e : tm' A) v,
  bind' (var_subst' (val_to_tm' v)) (↑e) = e.
Proof.
  intros. change (bind' (var_subst' v) (↑e)) with <| (↑e) [0 := v] |>.
  apply subst_lift'.
Qed.

Lemma bind_var_subst_lift_j' : ∀ {A} (j : J' A) e v,
  bind' (var_subst' (val_to_tm' v)) <| ↑j[e] |> = <| j [{bind' (var_subst' (val_to_tm' v)) e}] |>.
Proof.
  intros; destruct j; cbn; auto;
  try change (map' Some t) with (↑t);
  try change (mapV' Some v0) with (liftV' v0);
  try rewrite <- lift_val_to_tm';
  try rewrite bind_var_subst_lift'; reflexivity.
Qed.

Lemma bind_var_subst_lift_k' : ∀ {A} (k : K' A) e v,
  bind' (var_subst' (val_to_tm' v)) <| ↑k[e] |> = <| k [{bind' (var_subst' (val_to_tm' v)) e}] |>.
Proof.
  induction k; intros; cbn; auto.
  rewrite IHk.
  f_equal.
  rewrite bind_map_law'.
  assert ((λ a, match option_map Some a with Some a0 => map' Some (var_subst' v a0) | None => <| 0 |> end) = (λ a, <| var a |>)).
  apply functional_extensionality; intros [a|]; cbn; auto.
  rewrite H.
  apply bind_pure'.
Qed.

Lemma subst_plug_of_lift_j : ∀ {A} (j : J' A) (v : val' A),
  <| (↑j[0])[0 := v] |> = <| j[v] |>.
Proof.
  intros. destruct j; cbn; auto;
  try change (mapV' Some v0) with (liftV' v0);
  try change (map' Some t) with (↑t);
  try rewrite <- lift_val_to_tm';
  rewrite bind_var_subst_lift'; reflexivity.
Qed.


(* ANCHOR Context Capture
 *)
Theorem plug_k_let_bubbles_up_s_0 : ∀ (k : K' ␀) e1 e2,
  <| k [let S₀, e1 in e2] |> -->'* <| let S₀, e1 in ↑k[e2] |>.
Proof.
  induction k; intros; cbn; auto.
  eapply multi_trans. eapply multi_let'. apply IHk.
  rewrite lambda_to_val'. apply multi_contr'. apply contr_let_assoc'.
Qed.

Theorem plug_k_let_bubbles_up_s_0' : ∀ (k : K' ␀) (v : val' ␀) e,
  <| k [let S₀ v in e] |> -->'* <| let S₀ v in ↑k[e] |>.
Proof.
  induction k; intros; cbn; auto.
  eapply multi_trans. eapply multi_let'. apply IHk.
  apply multi_contr'. apply contr_let_assoc'.
Qed.


Lemma plug_k_let_let_S0_step_inv : ∀ (k : K' ␀) (v : val' ␀) e1 e2 term,
  <| k [let let S₀ v in e1 in e2] |> -->' term →
  term = <| k [let S₀ v in let e1 in {map' (option_map Some) e2}] |>.
Proof.
  intros.
  eapply deterministic_step' in H.
  2: { eapply step_k'. apply step_contr'. apply contr_let_assoc'. }
  subst. reflexivity.
Qed.

Lemma S0_val_does_not_step : ∀ (v : val' ␀) term,
  <| S₀ v |> -->' term → False.
Proof.
  intros.
  inversion H; clear H; subst. 
  destruct k; cbn in *.
  - destruct t; cbn in *. subst.
    + inversion H1; clear H1; subst. 
      destruct r; inversion H0; clear H0; subst. 
      destruct j; inversion H1; clear H1; subst.
      * destruct n; inversion H0.
      * destruct n; destruct v; inversion H2.
    + inversion H0.
  - inversion H0. 
Qed.

Lemma let_S0_does_not_step : ∀ (v : val' ␀) e term,
  <| let S₀ v in e |> -->' term → False.
Proof.
  intros. inversion H; clear H; subst.
  destruct k; cbn in *.
  - destruct t; cbn in *; subst.
    + inversion H1; clear H1; subst. 
      destruct r; inversion H0; clear H0; subst. 
      * destruct j; inversion H1.
      * destruct v0; inversion H1.
    + inversion H0.
  - inversion H0; clear H0; subst.
    eapply S0_val_does_not_step. rewrite <- H2. constructor; eassumption.
Qed.

Lemma plug_step_inv : ∀ (k : K' ␀) (t : T' ␀) (r : redex' ␀) term,
  <| k [t [r]] |> -->' term →
  term = <| k [t [{contract' r}]] |>.
Proof.
  intros. inversion H; clear H; subst.
  inversion H1; clear H1; subst. 
  assert (decompose' <| k0 [t0 [r0]] |> = decompose' <| k [t [r]] |>) by (rewrite H0; auto).
  repeat rewrite decompose_plug_redex' in *. inversion H; clear H; subst. reflexivity.
Qed.

Lemma inner_step_inv' : ∀ (k : K' ␀) (t : T' ␀) e term inner,
  <| k [t [e]] |> -->' term →
  e -->' inner →
  term = <| k [t [inner]] |>.
Proof.
  intros. eapply step_t' in H0. eapply step_k' in H0.
  eapply deterministic_step'; eauto.
Qed.

Lemma fold_redex_dol_let' : ∀ (w v : val' ␀) e,
  <| w $ let S₀ v in e |> = redex_dol_let' w v e.
Proof.
  reflexivity.
Qed.

Lemma fold_redex_shift' : ∀ (w v : val' ␀),
  <| w $ S₀ v |> = redex_shift' w v.
Proof.
  intros. auto.
Qed.

Lemma plug_shift_step_inv' : ∀ (k0 : K' ␀) (t0 : T' ␀) (w : val' ␀) (k : K' ␀) (v : val' ␀) e term,
  <| k0 [t0 [w $ k [let S₀ v in e]]] |> -->' term → ∃ inner,
  term = <| k0 [t0 [inner]] |> /\
  <| w $ k [let S₀ v in e] |> -->' inner.
Proof.
  intros.
  remember (plug_k_let_bubbles_up_s_0' k v e) as Hinner eqn:HH. clear HH.
  apply (@multi_delim' w) in Hinner.
  inversion Hinner; clear Hinner; subst. 
  - rewrite H2 in *.
    rewrite fold_redex_dol_let' in *.
    eapply (plug_step_inv k0 t0 _ term) in H. subst. eauto.
  - eapply step_t' in H0 as HH. eapply step_k' in HH.
    repeat eexists.
    + apply (deterministic_step' _ _ _ H HH).
    + assumption. 
Qed.

Lemma shift_step_inv' : ∀ (w : val' ␀) (k : K' ␀) (v : val' ␀) e term,
  <| w $ k [let S₀ v in e] |> -->' term → 
  (k = K_nil' /\ term = contract' (redex_dol_let' w v e)) \/
  (∃ inner, <| k [let S₀ v in e] |> -->' inner /\ term = <| w $ inner |>).
Proof.
  intros.
  remember (plug_k_let_bubbles_up_s_0' k v e) as Hinner eqn:HH. clear HH.
  inversion Hinner; clear Hinner; subst.
  - left. rewrite H2 in *.
    destruct k.
    split; auto. cbn in *.
    eapply (deterministic_step' _ _ _ H). auto.
    cbn in H2. inversion H2. destruct k; inversion H1.
  - right.
    apply (inner_step_inv' K_nil' (T_cons' w K_nil' T_nil') _ _ _ H) in H0 as HH.
    repeat eexists; eauto.
Qed.
