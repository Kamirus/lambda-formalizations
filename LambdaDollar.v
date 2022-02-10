Require Export Common.

Inductive tm {A} :=
| tm_var : A → tm
| tm_abs : @tm ^A → tm (* λ  x. e *)
| tm_s_0 : @tm ^A → tm (* S₀ f. e *)
| tm_app : tm → tm → tm (* e   e *)
| tm_dol : tm → tm → tm (* e $ e *)
.
Arguments tm A : clear implicits.
Global Hint Constructors tm : core.

Declare Custom Entry λ_dollar_scope.
Notation "<{ e }>" := e (at level 1, e custom λ_dollar_scope at level 99).
Notation "( x )" := x (in custom λ_dollar_scope, x at level 99).
Notation "{ x }" := x (in custom λ_dollar_scope at level 0, x constr).
Notation "x" := x (in custom λ_dollar_scope at level 0, x constr at level 0).
Notation "'var' v" := (tm_var v) (in custom λ_dollar_scope at level 1, left associativity).
Notation "0" := <{ var None }> (in custom λ_dollar_scope at level 0).
Notation "1" := <{ var {Some None} }> (in custom λ_dollar_scope at level 0).
Notation "2" := <{ var {Some (Some None)} }> (in custom λ_dollar_scope at level 0).
Notation "'λ' e" := (tm_abs e)
    (in custom λ_dollar_scope at level 90,
      e custom λ_dollar_scope at level 99,
      right associativity).
Notation "'S₀' e" := (tm_s_0 e)
    (in custom λ_dollar_scope at level 90,
      e custom λ_dollar_scope at level 99,
      right associativity).
Notation "e1 e2" := (tm_app e1 e2) (in custom λ_dollar_scope at level 10, left associativity).
Notation "e1 '$' e2" := (tm_dol e1 e2) (in custom λ_dollar_scope at level 80, right associativity).


Fixpoint map {A B : Type} (f : A -> B) (e : tm A) : tm B :=
  match e with
  | <{ var a }> => <{ var {f a} }>
  | <{ λ  e' }> => <{ λ  {map (option_map f) e'} }>
  | <{ S₀ e' }> => <{ S₀ {map (option_map f) e'} }>
  | <{ e1   e2 }> => <{ {map f e1}   {map f e2} }>
  | <{ e1 $ e2 }> => <{ {map f e1} $ {map f e2} }>
  end.

Notation "f <$> a" := (map f a) (at level 40, left associativity).

Lemma map_id_law : forall {V} (f : V -> V) e,
  (forall x, f x = x) ->
  f <$> e = e.
Admitted.
Lemma map_comp_law : forall A e B C (f:A->B) (g:B->C),
  g <$> (f <$> e) = g ∘ f <$> e.
Admitted.


Fixpoint bind {A B : Type} (f : A -> tm B) (e : tm A) : tm B :=
  match e with
  | <{ var a }> => f a
  | <{ e1   e2 }> => <{ {bind f e1}   {bind f e2} }>
  | <{ e1 $ e2 }> => <{ {bind f e1} $ {bind f e2} }>
  | <{ λ  e' }> => tm_abs (bind (fun a' => 
      match a' with
      | None   => tm_var None
      | Some a => map Some (f a)
      end) e')
  | <{ S₀ e' }> => tm_s_0 (bind (fun a' => 
      match a' with
      | None   => tm_var None
      | Some a => map Some (f a)
      end) e')
  end.

Notation "e >>= f" := (bind f e) (at level 20, left associativity).

Lemma bind_is_map : forall A e B (f:A->B),
  f <$> e = e >>= (fun v => tm_var (f v)).
Admitted.

Lemma bind_law : forall A e B C (f:A->tm B) (g:B->tm C),
  e >>= f >>= g = e >>= (fun a => f a >>= g).
Admitted.


Inductive val {A} :=
| val_abs : @tm ^A → val
.
Arguments val A : clear implicits.
Global Hint Constructors val : core.

Definition val_to_tm {A} (v : val A) := 
  match v with
  | val_abs e => tm_abs e
  end.

Inductive Void : Type := .
Notation "␀" := (Void).
Definition term := tm ␀.
Definition value := val ␀.
Definition from_void {A} (v : ␀) : A := match v with end.


Definition var_subst {V} e' (v:^V) :=
  match v with
  | None => e'
  | Some v => <{ var v }>
  end.

Definition tm_subst0 {V} (e:tm ^V) (e':tm V) :=
  e >>= var_subst e'.

Notation "e [ 0 := e' ]" := (tm_subst0 e e')
  (in custom λ_dollar_scope at level 0,
    e custom λ_dollar_scope,
    e' custom λ_dollar_scope at level 99).


Section Contexts.
  Context {A : Type}.
  Inductive J :=
  | J_fun : tm  A → J  (* [] M *)
  | J_arg : val A → J  (* V [] *)
  | J_dol : tm  A → J  (* []$M *)
  .
  Inductive K :=
  | K_nil  : K
  | K_cons : J → K → K
  .
  Inductive T :=
  | T_nil  : T
  | T_cons : val A → K → T → T  (* (v$K) · T *)
  .

  Inductive redex :=
  | redex_beta   : val A → val A → redex
  | redex_dollar : val A → val A → redex
  | redex_shift  : val A → K → tm ^A → redex  (* v $ K[S₀ f. e] *)
  .

  Inductive dec :=
  | dec_value : val A → dec
  | dec_stuck : K → tm ^A → dec (* K[S₀ f. e] *)
  | dec_redex : K → T → redex → dec (* K[T[Redex]] *)
  .

  Definition plugJ j e' :=
    match j with
    | J_fun e => <{ e' e }>
    | J_arg v => <{ {val_to_tm v} e' }>
    | J_dol e => <{ e' $ e }>
    end.
  
  Fixpoint plugK k e :=
    match k with
    | K_nil => e
    (* | K_cons j k' => plugK k' (plugJ j e) *)
    | K_cons j k' => plugJ j (plugK k' e)
    end.
  
  Fixpoint plugT trail e :=
    match trail with
    | T_nil => e
    (* | T_cons v k t => plugT t <{ {val_to_tm v} $ {plugK k e} }> *)
    | T_cons v k t => <{ {val_to_tm v} $ {plugK k (plugT t e)} }>
    end.

  Definition redex_to_term r := 
    match r with
    | redex_beta   v1 v2 => tm_app (val_to_tm v1) (val_to_tm v2)
    | redex_dollar v1 v2 => tm_dol (val_to_tm v1) (val_to_tm v2)
    | redex_shift v k e  => tm_dol (val_to_tm v) (plugK k <{ S₀ e }>)
    end.

End Contexts.
Arguments J A : clear implicits.
Arguments K A : clear implicits.
Arguments T A : clear implicits.
Arguments redex A : clear implicits.
Arguments dec A : clear implicits.

Definition K_fun {A} k e := @K_cons A (J_fun e) k.
Definition K_arg {A} v k := @K_cons A (J_arg v) k.
Definition K_dol {A} k e := @K_cons A (J_dol e) k.
(* Notation "'K_fun' k e" := (K_cons (J_fun e) k) (at level 10, left associativity). *)
(* Notation "'K_arg' v k" := (K_cons (J_arg v) k) (at level 10, left associativity). *)
(* Notation "'K_dol' k e" := (K_cons (J_dol e) k) (at level 10, left associativity). *)

Fixpoint decompose (e : tm ␀) : dec ␀ :=
  match e with
  | <{ var a }> => from_void a
  | <{ λ  e' }> => dec_value (val_abs e')
  | <{ S₀ e' }> => dec_stuck K_nil e'
  | <{ e1   e2 }> =>
    match decompose e1 with
    | dec_stuck k e'  => dec_stuck (K_fun k e2) e'
    | dec_redex k t r => dec_redex (K_fun k e2) t r
    | dec_value v1    => 
      match decompose e2 with
      | dec_stuck k e'  => dec_stuck (K_arg v1 k) e'
      | dec_redex k t r => dec_redex (K_arg v1 k) t r
      | dec_value v2    => dec_redex (K_nil) T_nil (redex_beta v1 v2)
      end
    end
  | <{ e1 $ e2 }> =>
    match decompose e1 with
    | dec_stuck k e'  => dec_stuck (K_dol k e2) e'
    | dec_redex k t r => dec_redex (K_dol k e2) t r
    | dec_value v1    => 
      match decompose e2 with
      | dec_stuck k e'  => dec_redex K_nil (T_nil) (redex_shift v1 k e')
      | dec_redex k t r => dec_redex K_nil (T_cons v1 k t) r
      | dec_value v2    => dec_redex K_nil (T_nil) (redex_dollar v1 v2)
      end
    end
  end.

Ltac inv_decompose_match H :=
  match goal with
  | H : (match decompose ?e with | dec_stuck _ _ | dec_redex _ _ _ | dec_value _ => _ end = _) |- _
    => let d := fresh "d" in remember (decompose e) as d; inv d; inv_decompose_match H
  | _ => try solve [inversion H; auto]; inj H
  end.

Lemma decompose_value_law : ∀ e v,
  decompose e = dec_value v → e = val_to_tm v.
Proof.
  dependent inversion e; intros; cbn in *.
  inversion v.
  injection H; intros; subst; reflexivity.
  inversion H.
  remember (decompose t) as d; dependent induction d; try inversion H;
  remember (decompose t0) as d0; dependent induction d0; try inversion H.
  remember (decompose t) as d; dependent induction d; try inversion H;
  remember (decompose t0) as d0; dependent induction d0; try inversion H.
  Qed.

Lemma decompose_stuck_law : ∀ k e e',
  decompose e = dec_stuck k e' → e = plugK k <{ S₀ e' }>.
Proof.
  induction k; intros.

  (* ḅase *)
  inv e; cbn in *; 
    try solve [inversion a | inversion H | injection H; intros; subst; reflexivity];
    remember (decompose e1) as d1; inv d1; try solve [inversion H; auto];
    remember (decompose e2) as d2; inv d2; try solve [inversion H; auto].

  (* step *)
  inv e; cbn in *; try solve [inversion a | inversion H; auto];
  remember (decompose e1) as d1; inv d1.

  - rewrite (decompose_value_law e1 v); auto.
    remember (decompose e2) as d2; inv d2; inversion H; clear H; subst.
    rewrite <- (IHk e2 e'); auto.
  - inversion H; clear H; subst.
    rewrite <- (IHk e1 e'); auto.
  - inversion H.

  - rewrite (decompose_value_law e1 v); auto.
    remember (decompose e2) as d2; inv d2; inversion H.
  - inversion H; clear H; subst.
    rewrite <- (IHk e1 e'); auto.
  - inversion H.
  Qed.

Ltac inv_dec :=
  match goal with
  | H : dec_value ?v = decompose ?e |- _ => rewrite (decompose_value_law e v); cbn; auto
  | H : dec_stuck ?k ?e' = decompose ?e |- _ => rewrite (decompose_stuck_law k e e'); cbn; auto
  end.

Lemma decompose_redex_law : ∀ e t k r,
  decompose e = dec_redex k t r → e = plugK k (plugT t (redex_to_term r)).
Proof.
  dependent induction e; intros; cbn in *;
  try solve [inversion a | inversion H | inv H];
  inv_decompose_match H;
  repeat inv_dec; cbn; f_equal; try solve [apply IHk; auto].
  apply IHe2; auto.
  apply IHe1; auto.
  apply IHe2; auto.
  apply IHe1; auto.
  Qed.

(* Fixpoint decompose_e (k : K ␀) (e : tm ␀) : dec ␀ :=
  match e with
  | <{ var a }> => from_void a
  | <{ λ  e' }> => decompose_K (val_abs e') k
  | <{ S₀ e' }> => dec_stuck k e'
  | <{ e1   e2 }> => decompose_e (K_fun k e2) e1
  | <{ e1 $ e2 }> => decompose_e (K_dol k e2) e1
  end
with decompose_K (v : val ␀) (k : K ␀) : dec ␀ :=
  match k with
  | K_nil => dec_value v
  | K_cons (J_fun e2) k1 => decompose_e (K_arg v k1) e2
  | K_cons (J_arg v1) k2 => dec_redex k2 T_nil (redex_beta v1 v)
  | K_cons (J_dol e2) k1 => todo
  end
. *)

