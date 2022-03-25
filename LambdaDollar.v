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

Inductive val {A} :=
| val_abs : @tm ^A → val
.
Arguments val A : clear implicits.
Global Hint Constructors val : core.

Definition val_to_tm {A} (v : val A) := 
  match v with
  | val_abs e => tm_abs e
  end.
Coercion val_to_tm : val >-> tm.

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
Notation "'λv' e" := (val_abs e)
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

(* Lemma bind_is_map : forall A e B (f:A->B),
  f <$> e = e >>= (fun v => tm_var (f v)).
Admitted. *)

(* Lemma bind_law : forall A e B C (f:A->tm B) (g:B->tm C),
  e >>= f >>= g = e >>= (fun a => f a >>= g).
Admitted. *)


Definition var_subst {V} e' (v:^V) :=
  match v with
  | None => e'
  | Some v => <{ var v }>
  end.

Definition tm_subst0 {V} (e:tm ^V) (v:val V) :=
  e >>= var_subst (val_to_tm v).

Notation "e [ 0 := v ]" := (tm_subst0 e v)
  (in custom λ_dollar_scope at level 0,
    e custom λ_dollar_scope,
    v custom λ_dollar_scope at level 99).


Class Plug (E : Type → Type) := plug : ∀ {A}, E A → tm A → tm A.

Notation "E [ e ]" := (plug E e)
  (in custom λ_dollar_scope at level 70,
    e custom λ_dollar_scope at level 99).


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
End Contexts.
Arguments J A : clear implicits.
Arguments K A : clear implicits.
Arguments T A : clear implicits.
Arguments redex A : clear implicits.
Arguments dec A : clear implicits.

Definition plugJ {A} (j : J A) e' :=
  match j with
  | J_fun e => <{ e' e }>
  | J_arg v => <{ v  e' }>
  | J_dol e => <{ e' $ e }>
  end.
Instance PlugJ : Plug J := @plugJ.

Fixpoint plugK {A} (k : K A) e :=
  match k with
  | K_nil => e
  (* | K_cons j k' => plugK k' (plugJ j e) *)
  | K_cons j k' => plugJ j (plugK k' e)
  end.
Instance PlugK : Plug K := @plugK.

Fixpoint plugT {A} (trail : T A) e :=
  match trail with
  | T_nil => e
  (* | T_cons v k t => plugT t <{ {val_to_tm v} $ {plugK k e} }> *)
  | T_cons v k t => <{ v $ k [{plugT t e}] }>
  end.
Instance PlugT : Plug T := @plugT.

Definition redex_to_term {A} (r : redex A) : tm A := 
  match r with
  | redex_beta   v1 v2 => <{ v1 v2 }>
  | redex_dollar v1 v2 => <{ v1 $ v2 }>
  | redex_shift v k e  => <{ v $ k [S₀ e] }>
  end.
Coercion redex_to_term : redex >-> tm.

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

(* plug ∘ decompose = id *)
Lemma decompose_value_inversion : ∀ e v,
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

Lemma decompose_stuck_inversion : ∀ e k e',
  decompose e = dec_stuck k e' → e = <{ k[S₀ e'] }>.
Proof.
  intros e k; generalize dependent e;
  induction k; intros; inv e; cbn in *;
  try solve [inversion a | inversion H | inj H; reflexivity];
  inv_decompose_match H; cbn;
  try rewrite (decompose_value_inversion e1 v); cbn; auto;
  f_equal; apply IHk; auto.
  Qed.

Ltac inv_dec :=
  match goal with
  | H : dec_value ?v = decompose ?e |- _ => rewrite (decompose_value_inversion e v); cbn; auto
  | H : dec_stuck ?k ?e' = decompose ?e |- _ => rewrite (decompose_stuck_inversion e k e'); cbn; auto
  end.

Lemma decompose_redex_inversion : ∀ e t k r,
  decompose e = dec_redex k t r → e = <{ k[t[r]] }>.
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

(* decompose ∘ plug = id *)
Lemma decompose_plug_value : ∀ v,
  decompose (val_to_tm v) = dec_value v.
Proof.
  intros; destruct v; auto.
  Qed.

Lemma decompose_plug_stuck : ∀ k e, 
  decompose <{ k[S₀ e] }> = dec_stuck k e.
Proof.
  induction k; intros; cbn; auto.
  inv j; cbn.
  - rewrite IHk; auto.
  - rewrite decompose_plug_value. rewrite IHk; auto.
  - rewrite IHk; auto.
  Qed.

Lemma decompose_plug_redex : ∀ k t (r : redex ␀),
  decompose <{ k[t[r]] }> = dec_redex k t r.
Proof with cbn; auto.
  intros k t; generalize dependent k; induction t; intros...
  - induction k...
    + inv r; cbn; inv v; cbn; try solve [inv v0; auto].
      rewrite decompose_plug_stuck; auto.
    + inv j; try inv v; cbn; try solve [rewrite IHk; auto].
  - induction k0...
    + inv v... rewrite IHt...
    + inv j; try inv v0; cbn; try solve [rewrite IHk0; auto].
Qed.


Instance LiftTm : Lift tm := λ {A}, map Some.

Definition liftV {A : Type} (v : val A) : val ^A :=
  match v with
  | val_abs e => val_abs (map (option_map Some) e)
  end.

Definition liftJ {A : Type} (j : J A) : J ^A := 
  match j with
  | J_fun e => J_fun (↑e)
  | J_arg v => J_arg (liftV v)
  | J_dol e => J_dol (↑e)
  end.
Instance LiftJ : Lift J := @liftJ.

Fixpoint liftK {A : Type} (k : K A) : K ^A :=
  match k with
  | K_nil => K_nil
  | K_cons j k => K_cons (↑j) (liftK k)
  end.
Instance LiftK : Lift K := @liftK.


Definition contract (r : redex ␀) : tm ␀ :=
  match r with
  (* (λ x. e) v  ~>  e [x := v] *)
  | redex_beta (val_abs e) v => <{ e [0 := v] }>

  (* v1 $ v2  ~>  v1 v2 *)
  | redex_dollar v1 v2 => <{ v1 v2 }>

  (* v $ K[S₀ f. e]  ~>  e [f := λ x. v $ K[x]] *)
  | redex_shift v k e  => <{ e [0 := λv {liftV v} $ ↑k[0] ] }>
  end.

Definition optional_step e :=
  match decompose e with
  | dec_redex k t r => Some <{ k[t[{contract r}]] }>
  | _ => None
  end.

Reserved Notation "e1 ~> e2" (at level 40).
Inductive contr : tm ␀ → tm ␀ → Prop :=
| contr_tm : ∀ r, redex_to_term r ~> contract r
where "e1 ~> e2" := (contr e1 e2).
Global Hint Constructors contr : core.

Reserved Notation "e1 --> e2" (at level 40).
Inductive step : tm ␀ → tm ␀ → Prop :=
| step_tm : ∀ k t e1 e2, e1 ~> e2 → <{ k[t[e1]] }> --> <{ k[t[e2]] }>
where "e1 --> e2" := (step e1 e2).
Global Hint Constructors step : core.

Notation "e1 -->* e2" := (multi step e1 e2) (at level 40).

Lemma contr_beta : ∀ e (v : val ␀),
  <{ (λ e) v }> ~> <{ e [0 := v] }>.
Proof.
  intros. change <{ (λ e) v }> with (redex_to_term (redex_beta <{ λv e }> v)).
  constructor.
Qed.

Lemma contr_dollar : ∀ (v1 v2 : val ␀),
  <{ v1 $ v2 }> ~> <{ v1 v2 }>.
Proof.
  intros. change <{ v1 $ v2 }> with (redex_to_term (redex_dollar v1 v2)).
  constructor.
Qed.

Lemma contr_shift : ∀ (v : val ␀) k e,
  <{ v $ k[S₀ e] }> ~> <{ e [0 := λv {liftV v} $ ↑k[0] ] }>.
Proof.
  intros. change <{ v $ k[S₀ e] }> with (redex_to_term (redex_shift v k e)). constructor.
Qed.

Fixpoint eval i e :=
  match i with
  | 0 => e
  | S j =>
    match optional_step e with
    | Some e' => eval j e'
    | None => e
    end
  end.

Section Examples.
  Definition _id : tm ␀ := <{ λ 0 }>.
  Definition _const : tm ␀ := <{ λ λ 1 }>.

  Compute (eval 10 <{ _id $ _const $ S₀ 0 }>).
  Compute (eval 10 <{ _const $ _id $ S₀ 0 }>).

  Definition j1 : J ␀ := J_fun <{ λ 0 0 }>.
  Definition j2 : J ␀ := J_arg <{ λv 0 }>.
  Definition j3 : J ␀ := J_dol <{ λ 0 }>.
  Definition ej123 := <{ j1[j2[j3[S₀ 0]]] }>.

  Example ex_shift : eval 1 <{ _id $ ej123 }> = <{
    λ ↑_id $ ↑j1[↑j2[↑j3[0]]]
  }>. Proof. cbn. auto. Qed.

  Compute (decompose (eval 1 <{ _id $ ej123 }>)).
End Examples.
