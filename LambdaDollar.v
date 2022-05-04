Require Export Common.

(* ANCHOR Terms
 *)
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

Lemma inj_val : ∀ {A} (v1 v2 : val A),
  val_to_tm v1 = val_to_tm v2 → 
  v1 = v2.
Proof.
  intros. destruct v1, v2. cbn in H. injection H; intro H1; rewrite H1; reflexivity.
Qed.

Inductive non {A} :=
| non_s_0 : tm ^A → non (* S₀ f. e *)
| non_app : tm A → tm  A → non (* e   e *)
| non_dol : tm A → tm  A → non (* e $ e *)
.

Arguments non A : clear implicits.
Global Hint Constructors non : core.

Definition non_to_tm {A} (p : non A) := 
  match p with
  | non_s_0 e => tm_s_0 e
  | non_app e1 e2 => tm_app e1 e2
  | non_dol e1 e2 => tm_dol e1 e2
  end.
Coercion non_to_tm : non >-> tm.

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

Lemma lambda_to_val : ∀ {A} (e : tm ^A),
  <{ λ e }> = <{ λv e }>.
Proof.
  reflexivity.
Qed.


Fixpoint map {A B : Type} (f : A -> B) (e : tm A) : tm B :=
  match e with
  | <{ var a }> => <{ var {f a} }>
  | <{ λ  e' }> => <{ λ  {map (option_map f) e'} }>
  | <{ S₀ e' }> => <{ S₀ {map (option_map f) e'} }>
  | <{ e1   e2 }> => <{ {map f e1}   {map f e2} }>
  | <{ e1 $ e2 }> => <{ {map f e1} $ {map f e2} }>
  end.

Definition mapV {A B} (f : A → B) (v : val A) : val B :=
  match v with
  | val_abs e => val_abs (map (option_map f) e)
  end.

Definition mapP {A B : Type} (f : A -> B) (p : non A) : non B :=
  match p with
  | non_app e1 e2 => non_app (map f e1) (map f e2)
  | non_dol e1 e2 => non_dol (map f e1) (map f e2)
  | non_s_0 e' => non_s_0 (map (option_map f) e')
  end.

Lemma map_val_is_val : ∀ {A B} (v : val A) (f : A → B),
  ∃ w, map f (val_to_tm v) = val_to_tm w.
Proof.
  intros. destruct v; cbn. eexists <{ λv _ }>. reflexivity.
Qed.

Lemma mapV_is_map : ∀ {A B} v (f : A → B),
  val_to_tm (mapV f v) = map f (val_to_tm v).
Proof.
  intros. destruct v; auto.
Qed.

Lemma mapP_is_map : ∀ {A B} p (f : A → B),
  non_to_tm (mapP f p) = map f (non_to_tm p).
Proof.
  intros. destruct p; auto.
Qed.

Lemma map_map_law : forall A e B C (f:A->B) (g:B->C),
  map g (map f e) = map (g ∘ f) e.
Proof.
  intros. generalize dependent B. generalize dependent C.
  induction e; intros; cbn; auto;
  try solve [f_equal; rewrite IHe; rewrite option_map_comp_law; auto];
  try solve [rewrite IHe1; rewrite IHe2; reflexivity].
Qed.

Lemma mapV_mapV_law : forall A v B C (f : A → B) (g : B → C),
  mapV g (mapV f v) = mapV (g ∘ f) v.
Proof.
  destruct v; intros; cbn; auto.
  rewrite map_map_law.
  rewrite option_map_comp_law. reflexivity.
Qed.


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

Definition bindV {A B} (f : A → tm B) (v : val A) : val B :=
  match v with
  | val_abs e => val_abs (bind (fun a' => 
      match a' with
      | None   => tm_var None
      | Some a => map Some (f a)
      end) e)
  end.

Definition bindP {A B : Type} (f : A -> tm B) (p : non A) : non B :=
  match p with
  | non_app e1 e2 => non_app (bind f e1) (bind f e2)
  | non_dol e1 e2 => non_dol (bind f e1) (bind f e2)
  | non_s_0 e' => non_s_0 (bind (fun a' => 
  match a' with
  | None   => tm_var None
  | Some a => map Some (f a)
  end) e')
  end.

Lemma bind_val_is_val : ∀ {A B} (v : val A) (f : A → tm B),
  ∃ w, bind f (val_to_tm v) = val_to_tm w.
Proof.
  intros. destruct v; cbn. eexists <{ λv _ }>. reflexivity.
Qed.

Lemma bindV_is_bind : ∀ {A B} v (f : A → tm B),
  val_to_tm (bindV f v) = bind f (val_to_tm v).
Proof.
  intros. destruct v; auto.
Qed.

Lemma bindP_is_bind : ∀ {A B} p (f : A → tm B),
  non_to_tm (bindP f p) = bind f (non_to_tm p).
Proof.
  intros. destruct p; auto.
Qed.

Lemma bind_map_law : ∀ {A B C} (f : B → tm C) (g : A → B) e,
  bind f (map g e) = bind (λ a, f (g a)) e.
Proof.
  intros. generalize dependent B. generalize dependent C.
  induction e; intros; cbn; auto;
  try solve [f_equal; rewrite IHe; f_equal; apply functional_extensionality; intros [a|]; cbn; auto];
  try solve [f_equal; apply IHe1 + apply IHe2].
Qed.

Lemma bind_pure : ∀ {A} (e : tm A),
  bind (λ a, <{ var a }>) e = e.
Proof.
  induction e; cbn; auto;
  try solve [f_equal; rewrite <- IHe at 2; f_equal; apply functional_extensionality; intros [a|]; cbn; auto];
  try solve [f_equal; apply IHe1 + apply IHe2].
Qed.

Lemma map_bind_law : ∀ {A B C} (f : A → tm B) (g : B → C) e,
  bind (map g ∘ f) e = map g (bind f e).
Proof.
  intros; generalize dependent B; generalize dependent C; induction e; intros; cbn; auto;
  try solve [
    rewrite <- IHe; repeat f_equal; apply functional_extensionality; intros [a|]; auto; cbn;
    change ((map g ∘ f) a) with (map g (f a));
    repeat rewrite map_map_law; f_equal];
  try solve [f_equal; apply IHe1 + apply IHe2].
Qed.


Definition var_subst {V} e' (v:^V) :=
  match v with
  | None => e'
  | Some v => <{ var v }>
  end.

Definition tm_subst0 {V} (e:tm ^V) (v:val V) :=
  bind (var_subst (val_to_tm v)) e.

Notation "e [ 0 := v ]" := (tm_subst0 e v)
  (in custom λ_dollar_scope at level 0,
    e custom λ_dollar_scope,
    v custom λ_dollar_scope at level 99).


Class Plug (E : Type → Type) := plug : ∀ {A}, E A → tm A → tm A.

Notation "E [ e ]" := (plug E e)
  (in custom λ_dollar_scope at level 70,
    e custom λ_dollar_scope at level 99).


(* ANCHOR Contexts
 *)
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
  | K_cons j k' => plugJ j (plugK k' e)
  end.
Instance PlugK : Plug K := @plugK.

Fixpoint plugT {A} (trail : T A) e :=
  match trail with
  | T_nil => e
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

(* ANCHOR Decompose
 *)
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
  end
.

(* ANCHOR Unique Decomposition
 *)
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

Definition liftV {A : Type} (v : val A) : val ^A := mapV Some v.

Lemma lift_val_to_tm : ∀ {A} (v : val A),
  ↑ (val_to_tm v) = val_to_tm (liftV v).
Proof.
  intros. destruct v; cbn. reflexivity.
Qed.

Definition mapJ {A B} (f : A → B) (j : J A) : J B := 
  match j with
  | J_fun e => J_fun (map f e)
  | J_arg v => J_arg (mapV f v)
  | J_dol e => J_dol (map f e)
  end.

Lemma mapJ_mapJ_law : forall A j B C (f : A → B) (g : B → C),
  mapJ g (mapJ f j) = mapJ (g ∘ f) j.
Proof.
  destruct j; intros; cbn;
  try rewrite map_map_law;
  try rewrite mapV_mapV_law;
  auto.
Qed.

Fixpoint mapK {A B} (f : A → B) (k : K A) : K B := 
  match k with
  | K_nil => K_nil
  | K_cons j1 k2 => K_cons (mapJ f j1) (mapK f k2)
  end.

Lemma mapK_mapK_law : forall A k B C (f : A → B) (g : B → C),
  mapK g (mapK f k) = mapK (g ∘ f) k.
Proof.
  induction k; intros; cbn; auto.
  rewrite mapJ_mapJ_law.
  rewrite IHk.
  reflexivity.
Qed.

Instance LiftJ : Lift J := λ {A}, mapJ Some.

Instance LiftK : Lift K := λ {A}, mapK Some.

Definition bindJ {A B} (f : A → tm B) (j : J A) : J B := 
  match j with
  | J_fun e => J_fun (bind f e)
  | J_arg v => J_arg (bindV f v)
  | J_dol e => J_dol (bind f e)
  end.

Fixpoint bindK {A B} (f : A → tm B) (k : K A) : K B := 
  match k with
  | K_nil => K_nil
  | K_cons j1 k2 => K_cons (bindJ f j1) (bindK f k2)
  end.

Lemma bindV_mapV_law : ∀ {A B C} (f : B → tm C) (g : A → B) v,
  bindV f (mapV g v) = bindV (λ a, f (g a)) v.
Proof.
  intros. destruct v; cbn.
  rewrite bind_map_law. repeat f_equal.
  apply functional_extensionality; intros [a|]; cbn; auto.
Qed.

Lemma bindJ_mapJ_law : ∀ {A B C} (f : B → tm C) (g : A → B) j,
  bindJ f (mapJ g j) = bindJ (λ a, f (g a)) j.
Proof.
  intros. destruct j; cbn;
  rewrite bind_map_law + rewrite bindV_mapV_law; auto.
Qed.

Lemma bindK_mapK_law : ∀ {A B C} (f : B → tm C) (g : A → B) k,
  bindK f (mapK g k) = bindK (λ a, f (g a)) k.
Proof.
  intros. generalize dependent B. generalize dependent C.
  induction k; intros; cbn; auto.
  rewrite IHk; f_equal.
  apply bindJ_mapJ_law.
Qed.

Lemma mapV_bindV_law : ∀ {A B C} (f : A → tm B) (g : B → C) v,
  bindV (map g ∘ f) v = mapV g (bindV f v).
Proof.
  intros.
  apply inj_val.
  rewrite mapV_is_map.
  repeat rewrite bindV_is_bind. apply map_bind_law.
Qed.

Lemma mapJ_bindJ_law : ∀ {A B C} (f : A → tm B) (g : B → C) j,
  bindJ (map g ∘ f) j = mapJ g (bindJ f j).
Proof.
  intros. destruct j; cbn; rewrite map_bind_law + rewrite mapV_bindV_law; auto.
Qed.

Lemma mapK_bindK_law : ∀ {A B C} (f : A → tm B) (g : B → C) k,
  bindK (map g ∘ f) k = mapK g (bindK f k).
Proof.
  intros; generalize dependent B; generalize dependent C; induction k; intros; cbn; auto.
  rewrite IHk; f_equal.
  apply mapJ_bindJ_law.
Qed.


(* ANCHOR Evaluation
 *)
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
| step_tm : ∀ (k : K ␀) (t : T ␀) (e1 e2 : tm ␀), e1 ~> e2 → <{ k[t[e1]] }> --> <{ k[t[e2]] }>
where "e1 --> e2" := (step e1 e2).
Global Hint Constructors step : core.

Notation "e1 -->* e2" := (multi step e1 e2) (at level 40).

Lemma step_contr : ∀ {e1 e2},
  e1 ~> e2 →
  e1 --> e2.
Proof.
  intros.
  apply (step_tm K_nil T_nil e1 e2).
  assumption.
Qed.
Lemma multi_contr : ∀ {e1 e2},
  e1 ~> e2 →
  e1 -->* e2.
Proof.
  intros. apply (multi_step _ _ _ _ (step_contr H)); auto.
Qed.
Lemma multi_contr_multi : ∀ {e1 e2 e3},
  e1 ~> e2 →
  e2 -->* e3 →
  e1 -->* e3.
Proof.
  intros. eapply multi_step; try eapply (step_tm K_nil T_nil); cbn; eassumption.
Qed.

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
Global Hint Resolve step_contr contr_beta contr_dollar contr_shift : core.

Lemma no_contr_lambda : ∀ e e2, ~ <{ λ e }> ~> e2.
Proof.
  intros e e2 H. inversion H; clear H; subst. destruct r; inversion H1.
Qed.
Lemma no_contr_shift : ∀ e e2, ~ <{ S₀ e }> ~> e2.
Proof.
  intros e e2 H. inversion H; clear H; subst. destruct r; inversion H1.
Qed.

Global Hint Resolve contr_beta contr_dollar contr_shift no_contr_lambda no_contr_shift : core.

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


Lemma plug_non_is_non : ∀ (k : K ␀) (t : T ␀) (p : non ␀),
  ∃ ktp, <{ k [t [p]] }> = non_to_tm ktp.
Proof.
  intros; destruct k; cbn in *.
  destruct t; cbn in *.
  eexists; reflexivity.
  eexists (non_dol _ _); reflexivity.
  destruct j; cbn;
  eexists (non_app _ _) + eexists (non_dol _ _) + eexists (non_fun _ _); reflexivity.
Qed.

Lemma redex_is_non : ∀ {A} r, ∃ p, @redex_to_term A r = non_to_tm p.
Proof.
  intros. destruct r; cbn;
  try solve [try destruct j; eexists (non_app _ _) + eexists (non_dol _ _); reflexivity].
Qed.


Lemma step_j : ∀ {j : J ␀} {e1 e2},
  e1 --> e2 →
  <{ j[e1] }> --> <{ j[e2] }>.
Proof.
  intros. generalize dependent j.
  induction H; auto; intros.
  apply (step_tm (K_cons j k) t e1 e2).
  apply H.
Qed.

Lemma multi_j : ∀ {e1 e2} (j : J ␀),
  e1 -->* e2 →
  <{ j[e1] }> -->* <{ j[e2] }>.
Proof.
  intros. generalize dependent j.
  induction H; auto; intros.
  eapply (multi_step); [idtac | apply IHmulti].
  apply step_j.
  apply H.
Qed.

Lemma step_delim : ∀ {v : val ␀} {e1 e2},
  e1 --> e2 →
  <{ v $ e1 }> --> <{ v $ e2 }>.
Proof.
  intros. generalize dependent v.
  induction H; auto; intros.
  apply (step_tm K_nil (T_cons v k t) e1 e2).
  apply H.
Qed.

Lemma multi_delim : ∀ {v : val ␀} {e1 e2},
  e1 -->* e2 →
  <{ v $ e1 }> -->* <{ v $ e2 }>.
Proof.
  intros. generalize dependent v.
  induction H; auto; intros.
  eapply (multi_step); [idtac | apply IHmulti].
  apply step_delim.
  apply H.
Qed.

Lemma step_k : ∀ {e1 e2} {k : K ␀},
  e1 --> e2 →
  <{ k[e1] }> --> <{ k[e2] }>.
Proof.
  intros e1 e2 k; generalize dependent e1; generalize dependent e2.
  induction k; auto; intros.
  cbn. apply step_j. apply IHk. apply H.
Qed.

Lemma multi_k : ∀ {e1 e2} {k : K ␀},
  e1 -->* e2 →
  <{ k[e1] }> -->* <{ k[e2] }>.
Proof.
  intros. generalize dependent k.
  induction H; auto; intros.
  eapply (multi_step); [idtac | apply IHmulti].
  apply step_k.
  apply H.
Qed.

Lemma step_t : ∀ {e1 e2} {t : T ␀},
  e1 --> e2 →
  <{ t[e1] }> --> <{ t[e2] }>.
Proof.
  intros e1 e2 t; generalize dependent e1; generalize dependent e2.
  induction t; auto; intros.
  cbn. apply step_delim. apply step_k. apply IHt. apply H.
Qed.

Lemma multi_t : ∀ {e1 e2} {t : T ␀},
  e1 -->* e2 →
  <{ t[e1] }> -->* <{ t[e2] }>.
Proof.
  intros. generalize dependent t.
  induction H; auto; intros.
  eapply (multi_step); [idtac | apply IHmulti].
  apply step_t.
  apply H.
Qed.


Lemma lift_map : ∀ {A B} (e : tm A) (f : A → B),
  ↑(map f e) = map (option_map f) (↑e).
Proof.
  intros.
  unfold lift. unfold LiftTm.
  repeat rewrite map_map_law.
  f_equal.
Qed.

Lemma bind_lift : ∀ {A B} e (f : ^A → tm B),
  bind f (↑e) = bind (f ∘ Some) e.
Proof.
  intros.
  unfold lift. unfold LiftTm.
  rewrite bind_map_law. f_equal.
Qed.

Lemma lift_bind : ∀ {A B} e (f : A → tm B),
  ↑(bind f e) = bind (lift ∘ f) e.
Proof.
  intros.
  unfold lift. unfold LiftTm.
  rewrite map_bind_law. reflexivity.
Qed.

Lemma bindK_lift : ∀ {A B} k (f : ^A → tm B),
  bindK f (↑k) = bindK (f ∘ Some) k.
Proof.
  intros.
  unfold lift. unfold LiftK.
  rewrite bindK_mapK_law. f_equal.
Qed.

Lemma lift_bindK : ∀ {A B} e (f : A → tm B),
  ↑(bindK f e) = bindK (lift ∘ f) e.
Proof.
  intros.
  unfold lift. unfold LiftK. unfold LiftTm.
  rewrite mapK_bindK_law. reflexivity.
Qed.

Lemma map_plug_j_is_plug_of_maps : ∀ {A B} j e (f : A → B),
  map f <{ j[e] }> = <{ {mapJ f j} [{map f e}] }>.
Proof.
  intros. destruct j; cbn; try destruct v; auto.
Qed.

Lemma map_plug_k_is_plug_of_maps : ∀ {A B} (k : K A) e (f : A → B),
  map f <{ k[e] }> = <{ {mapK f k} [{map f e}] }>.
Proof.
  intros A B. generalize dependent B.
  induction k; intros; cbn; auto.
  rewrite map_plug_j_is_plug_of_maps.
  rewrite IHk. reflexivity.
Qed.

Lemma bind_plug_j_is_plug_of_binds : ∀ {A B} j e (f : A → tm B),
  bind f <{ j[e] }> = <{ {bindJ f j} [{bind f e}] }>.
Proof.
  intros. destruct j; cbn; try destruct v; auto.
Qed.

Lemma bind_plug_k_is_plug_of_binds : ∀ {A B} (k : K A) e (f : A → tm B),
  bind f <{ k[e] }> = <{ {bindK f k} [{bind f e}] }>.
Proof.
  intros A B. generalize dependent B.
  induction k; intros; cbn; auto.
  rewrite bind_plug_j_is_plug_of_binds.
  rewrite IHk. reflexivity.
Qed.

Lemma lift_mapK : ∀ {A B} k (f : A → B),
  ↑(mapK f k) = mapK (option_map f) (↑k).
Proof.
  intros. unfold lift. unfold LiftK.
  repeat rewrite mapK_mapK_law.
  f_equal.
Qed.

Lemma subst_lift : ∀ {A} (e : tm A) v,
  <{ (↑e) [0 := v] }> = e.
Proof.
  intro A.
  unfold tm_subst0 .
  unfold lift. unfold LiftTm.
  intros. rewrite bind_map_law. apply bind_pure.
Qed.

Lemma bind_var_subst_lift : ∀ {A} (e : tm A) v,
  bind (var_subst (val_to_tm v)) (↑e) = e.
Proof.
  intros. change (bind (var_subst v) (↑e)) with <{ (↑e) [0 := v] }>.
  apply subst_lift.
Qed.

Lemma bind_var_subst_lift_j : ∀ {A} (j : J A) e v,
  bind (var_subst (val_to_tm v)) <{ ↑j[e] }> = <{ j [{bind (var_subst (val_to_tm v)) e}] }>.
Proof.
  intros; destruct j; cbn; auto;
  try change (mapV Some v0) with (liftV v0);
  try rewrite <- lift_val_to_tm;
  try change (map Some t) with <{ ↑t }>;
  try rewrite bind_var_subst_lift; reflexivity.
Qed.

Lemma bind_var_subst_lift_k : ∀ {A} (k : K A) e v,
  bind (var_subst (val_to_tm v)) <{ ↑k[e] }> = <{ k [{bind (var_subst (val_to_tm v)) e}] }>.
Proof.
  induction k; intros; cbn; auto.
  change (mapJ Some j) with (↑j).
  rewrite bind_var_subst_lift_j. unfold tm_subst0. rewrite IHk. reflexivity.
Qed.
