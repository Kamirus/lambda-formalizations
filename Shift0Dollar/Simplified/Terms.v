Require Export Common.
Require Export Coq.Logic.FunctionalExtensionality.

(* ANCHOR

  terms                 e ::= v | p
  values                v ::= x | λ x. e | S₀
  nonvalues             p ::= v v | let x = e in e | v $ e
  evaluation contexts   K ::= [] | let x = K in e
  trails                T ::= [] | v $ K[T]

 *)

Inductive tm {A} :=
| tm_val : val → tm (* v *)
| tm_non : non → tm (* p *)
with val {A} :=
| val_var : A      → val (* x *)
| val_abs : @tm ^A → val (* λ x. e *)
| val_s_0 :          val (* S₀ *)
with non {A} :=
| non_app : val → val    → non (* v   v *)
| non_dol : val → tm     → non (* v $ e *)
| non_let : tm  → @tm ^A → non (* let x = e in e *)
.
Arguments tm A : clear implicits.
Arguments val A : clear implicits.
Arguments non A : clear implicits.
Global Hint Constructors tm val non : core.
Scheme tm_mut  := Minimality for tm Sort Prop
with   val_mut := Minimality for val Sort Prop
with   non_mut := Minimality for non Sort Prop.

Coercion tm_val : val >-> tm.
Coercion tm_non : non >-> tm.

Lemma inj_val : ∀ {A} (v1 v2 : val A),
  tm_val v1 = tm_val v2 → 
  v1 = v2.
Proof.
  intros. destruct v1, v2; cbn in H; auto;
  try solve [inversion H; auto].
Qed.

Lemma inj_non : ∀ {A} (p p' : non A),
  tm_non p = tm_non p' → p = p'.
Proof.
  intros; destruct p, p'; cbn in *; inv H; auto.
Qed.

Declare Custom Entry λ_dollar_scope.
Notation "<{ e }>" := e (at level 1, e custom λ_dollar_scope at level 99).
Notation "( x )" := x (in custom λ_dollar_scope, x at level 99).
Notation "{ x }" := x (in custom λ_dollar_scope at level 0, x constr).
Notation "x" := x (in custom λ_dollar_scope at level 0, x constr at level 0).
Notation "'var' v" := (val_var v) (in custom λ_dollar_scope at level 1, left associativity).
Notation "0" := <{ var None }> (in custom λ_dollar_scope at level 0).
Notation "1" := <{ var {Some None} }> (in custom λ_dollar_scope at level 0).
Notation "2" := <{ var {Some (Some None)} }> (in custom λ_dollar_scope at level 0).
Notation "'λ' e" := (val_abs e)
    (in custom λ_dollar_scope at level 90,
      e custom λ_dollar_scope at level 99,
      right associativity).
(* Notation "'λv'' e" := (val_abs' e)
    (in custom λ_dollar_scope at level 90,
      e custom λ_dollar_scope at level 99,
      right associativity). *)
(* Notation "'S₀,' e" := (tm_app' tm_s_0' (tm_abs' e))
    (in custom λ_dollar_scope at level 90,
      e custom λ_dollar_scope at level 99,
      right associativity). *)
Notation "'S₀'" := (val_s_0).
Notation "v1 v2" := (non_app v1 v2) (in custom λ_dollar_scope at level 10, left associativity).
Notation "v '$' e" := (non_dol v e) (in custom λ_dollar_scope at level 80, right associativity).
Notation "'let' e1 'in' e2" := (non_let e1 e2) (in custom λ_dollar_scope at level 70, right associativity).


Fixpoint map {A B : Type} (f : A → B) (e : tm A) : tm B :=
  match e with
  | tm_val v => tm_val (mapV f v)
  | tm_non p => tm_non (mapP f p)
  end
with mapV {A B : Type} (f : A → B) (v : val A) : val B :=
  match v with
  | <{ var a }> => <{ var {f a} }>
  | <{ λ e }> => <{ λ {map (option_map f) e} }>
  | <{ S₀ }> => <{ S₀ }>
  end
with mapP {A B : Type} (f : A → B) (p : non A) : non B :=
  match p with
  | <{ v   v' }> => <{ {mapV f v}   {mapV f v'} }>
  | <{ v $ e  }> => <{ {mapV f v} $ {map f e} }>
  | <{ let e1 in e2 }> => <{ let {map f e1} in {map (option_map f) e2} }>
  end.

(* Lemma map_val_is_val : ∀ {A B} (v : val A) (f : A → B),
  ∃ w, map f (tm_val v) = tm_val w.
Proof.
  intros. destruct v; cbn.
  - eexists <{ λv _ }>. reflexivity.
  - exists val_s_0; reflexivity.
Qed.

Lemma map_non_is_non : ∀ {A B} (p1 : non A) (f : A → B),
  ∃ p2, map f (non_to_tm p1) = non_to_tm p2.
Proof.
  intros. destruct p1; cbn.
  - eexists (non_app _ _). reflexivity.
  - eexists (non_dol _ _). reflexivity.
  - eexists (non_let _ _). reflexivity.
Qed.

Lemma mapV_is_map : ∀ {A B} v (f : A → B),
  tm_val (mapV f v) = map f (tm_val v).
Proof.
  intros. destruct v; auto.
Qed.

Lemma mapP_is_map : ∀ {A B} p (f : A → B),
  non_to_tm (mapP f p) = map f (non_to_tm p).
Proof.
  intros. destruct p; auto.
Qed. *)

(* Lemma map_map_law : forall A e B C (f:A→B) (g:B→C),
  map g (map f e) = map (g ∘ f) e.
Proof.
  intros. generalize dependent B. generalize dependent C.
  induction e; intros; cbn; auto;
  try solve [f_equal; rewrite IHe; rewrite option_map_comp_law; auto];
  try solve [rewrite IHe1; rewrite IHe2; reflexivity].
  rewrite IHe1; f_equal. rewrite IHe2.
  rewrite option_map_comp_law; auto.
Qed.

Lemma mapV_mapV_law : forall A v B C (f : A → B) (g : B → C),
  mapV g (mapV f v) = mapV (g ∘ f) v.
Proof.
  destruct v; intros; cbn; auto.
  rewrite map_map_law.
  rewrite option_map_comp_law. reflexivity.
Qed. *)


Instance LiftTm  : Lift tm  := λ {A}, map  Some.
Instance LiftVal : Lift val := λ {A}, mapV Some.
(* Definition liftV {A : Type} (v : val A) : val ^A := mapV Some v. *)

(* Lemma lift_tm_val : ∀ {A} (v : val A),
  ↑ (tm_val v) = tm_val (liftV v).
Proof.
  intros. destruct v; cbn; reflexivity.
Qed. *)


Definition option_bind {A B : Type} (f : A → val B) (o : ^A) : val ^B :=
  match o with
  | None   => <{ 0 }>
  | Some a => ↑ (f a)
  end.


Fixpoint bind {A B : Type} (f : A → val B) (e : tm A) : tm B :=
  match e with
  | tm_val v => tm_val (bindV f v)
  | tm_non p => tm_non (bindP f p)
  end
with bindV {A B : Type} (f : A → val B) (v : val A) : val B :=
  match v with
  | <{ var a }> => f a
  | <{ λ e }> => <{ λ {bind (option_bind f) e} }>
  | <{ S₀ }> => <{ S₀ }>
  end
with bindP {A B : Type} (f : A → val B) (p : non A) : non B :=
  match p with
  | <{ v   v' }> => <{ {bindV f v}   {bindV f v'} }>
  | <{ v $ e  }> => <{ {bindV f v} $ {bind f e} }>
  | <{ let e1 in e2 }> => <{ let {bind f e1} in {bind (option_bind f) e2} }>
  end.

(* Lemma bind_val_is_val : ∀ {A B} (v : val A) (f : A → tm B),
  ∃ w, bind f (tm_val v) = tm_val w.
Proof.
  intros. destruct v; cbn.
  - eexists <{ λv _ }>. reflexivity.
  - eexists val_s_0. reflexivity.
Qed.

Lemma bindV_is_bind : ∀ {A B} v (f : A → tm B),
  tm_val (bindV f v) = bind f (tm_val v).
Proof.
  intros. destruct v; auto.
Qed.

Lemma bindP_is_bind : ∀ {A B} p (f : A → tm B),
  non_to_tm (bindP f p) = bind f (non_to_tm p).
Proof.
  intros. destruct p; auto.
Qed. *)

(* Lemma bind_map_law : ∀ {A B C} (f : B → tm C) (g : A → B) e,
  bind f (map g e) = bind (λ a, f (g a)) e.
Proof.
  intros. generalize dependent B. generalize dependent C.
  induction e; intros; cbn; auto;
  try solve [f_equal; rewrite IHe; f_equal; apply functional_extensionality; intros [a|]; cbn; auto];
  try solve [f_equal; apply IHe1 + apply IHe2].
  rewrite IHe1; f_equal. rewrite IHe2.
  f_equal; apply functional_extensionality; intros [a|]; cbn; auto.
Qed.

Lemma bind_pure : ∀ {A} (e : tm A),
  bind (λ a, <{ var a }>) e = e.
Proof.
  induction e; cbn; auto;
  try solve [f_equal; rewrite <- IHe at 2; f_equal; apply functional_extensionality; intros [a|]; cbn; auto];
  try solve [f_equal; apply IHe1 + apply IHe2].
  rewrite IHe1; f_equal. rewrite <- IHe2 at 2.
  f_equal; apply functional_extensionality; intros [a|]; cbn; auto.
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
  rewrite IHe1; f_equal. rewrite <- IHe2.
  f_equal; apply functional_extensionality; intros [a|]; cbn; auto.
  change ((map g ∘ f) a) with (map g (f a)); repeat rewrite map_map_law; f_equal.
Qed.

Lemma map_as_bind : ∀ {A B} e (f : A → B),
  map f e = bind (tm_var ∘ f) e.
Proof.
  intros; generalize dependent B; induction e; intros; cbn; auto;
  try solve [rewrite IHe; repeat f_equal; apply functional_extensionality; intros [a|]; auto];
  try solve [rewrite IHe1; rewrite IHe2; reflexivity].
  rewrite IHe1; f_equal. rewrite IHe2; f_equal.
  apply functional_extensionality; intros [a|]; auto.
Qed. *)


Definition var_subst {V} e (v:^V) :=
  match v with
  | None => e
  | Some v => <{ var v }>
  end.

Definition tm_subst0 {V} (e:tm ^V) (v:val V) :=
  bind (var_subst v) e.

Notation "e [ 0 := v ]" := (tm_subst0 e v)
  (in custom λ_dollar_scope at level 0,
    e custom λ_dollar_scope,
    v custom λ_dollar_scope at level 99).


Class Plug (E : Type → Type) := plug : ∀ {A}, E A → tm A → tm A.

Notation "E [ e ]" := (plug E e)
  (in custom λ_dollar_scope at level 70,
    e custom λ_dollar_scope at level 99).


(* Ltac reason := repeat(
  rewrite tm_dec_of_val in * +
  rewrite tm_dec_of_non in * +
  match goal with
  | H : ∅ |- _ => destruct H
  | H : (_, _) = (_, _) |- _ => inj H
  | H : tm_val _ = tm_val _ |- _ => apply inj_val in H; rewrite H in *
  | H : non_to_tm _ = non_to_tm _ |- _ => apply inj_non in H; rewrite H in *
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
  | H : context C [match ?v with val_abs _ => _ | val_s_0 => _ end] |- _ =>
    destruct v; inversion H; clear H; subst
  end). *)


(* ANCHOR Contexts
 *)
Inductive K {A} :=
| K_nil  : K
| K_let  : K → tm ^A → K (* let x = K in e *)
.
Arguments K A : clear implicits.

Fixpoint plugK {A} (k : K A) e :=
  match k with
  | K_nil => e
  | K_let k1 e2 => <{ let {plugK k1 e} in e2 }>
  end.
Instance PlugK : Plug K := @plugK.


Inductive dec {T R A} :=
| dec_value : val A → dec
| dec_stuck : K A → val A → dec (* K [S₀ v] *)
| dec_redex : K A → T A → R A → dec (* K [T [Redex]] *)
.
Arguments dec T R A : clear implicits.


(* Ltac inv_decompose_match H :=
  match goal with
  | H : (match decompose ?e with | dec_stuck_s_0 _ | dec_stuck_let _ _ | dec_redex _ _ _ | dec_value _ => _ end = _) |- _ =>
    let d := fresh "d" in remember (decompose e) as d; inv d; inv_decompose_match H
  | H : (let (_,_) := ?e in _) = _ |- _ =>
    let d := fresh "d" in remember e as d; inv d; inv_decompose_match H
  | _ => try solve [inversion H; auto]; try inj H
  end. *)


(* ANCHOR Unique Decomposition
 *)
(* plug ∘ decompose = id *)
(* Lemma decompose_value_inversion : ∀ e v,
  decompose e = dec_value v → e = tm_val v.
Proof.
  intros. inv e; cbn in *.
  - destruct a.
  - destruct v; inversion H; clear H; subst. auto.
  - inj H; auto.
  - reason; inversion H.
  - reason; inv_decompose_match H.
  - inv_decompose_match H.
Qed.
Lemma decompose_stuck_s_0_inversion : ∀ e v,
  decompose e = dec_stuck_s_0 v → e = <{ S₀ v }>.
Proof.
  intros. inv e; cbn in *; reason; auto;
  try solve [inversion a | inv H];
  inv_decompose_match H.
Qed.
Lemma decompose_stuck_let_inversion : ∀ e v1 e2,
  decompose e = dec_stuck_let v1 e2 → e = <{ let S₀ v1 in e2 }>.
Proof.
  intros. inv e; cbn in *; reason; auto;
  try solve [inversion a | inv H];
  inv_decompose_match H.
  rewrite (decompose_stuck_s_0_inversion e1 v1); auto.
Qed.
Ltac inv_dec :=
  match goal with
  | H : dec_value ?v = decompose ?e |- _ => rewrite (decompose_value_inversion e v); cbn; auto
  | H : dec_stuck_s_0 ?e = decompose ?e |- _ => rewrite (decompose_stuck_s_0_inversion e e); cbn; auto
  | H : dec_stuck_let ?e1 ?e2 = decompose ?e |- _ => rewrite (decompose_stuck_let_inversion e e1 e2); cbn; auto
  end.
Lemma decompose_redex_inversion : ∀ e t k r,
  decompose e = dec_redex k t r → e = <{ k[t[r]] }>.
Proof.
  dependent induction e; intros; cbn in *; reason; auto;
  try solve [destruct a | inv H];
  inv_decompose_match H;
  repeat inv_dec; cbn; f_equal;
  try solve [apply IHk + apply IHe1 + apply IHe2; auto].
Qed. *)

(* decompose ∘ plug = id *)
(* Lemma decompose_plug_value : ∀ v,
  decompose (tm_val v) = dec_value v.
Proof.
  intros; destruct v; auto.
Qed.
Lemma decompose_plug_stuck_s_0 : ∀ (v : val ∅), 
  decompose <{ S₀ v }> = dec_stuck_s_0 v.
Proof.
  intros; destruct v; cbn; auto.
Qed.
Lemma decompose_plug_stuck_let : ∀ (v : val ∅) e,
  decompose <{ let S₀ v in e }> = dec_stuck_let v e.
Proof.
  intros; destruct v; cbn; auto.
Qed.
Lemma decompose_plug_redex : ∀ k t (r : redex ∅),
  decompose <{ k[t[r]] }> = dec_redex k t r.
Proof with cbn; auto.
  intros k t; generalize dependent k; induction t; intros...
  - induction k...
    + inv r; cbn; try inv v; cbn; try solve [inv v0; auto]; auto.
      inv j; cbn; reason; reflexivity.
    + rewrite IHk; reflexivity.
  - induction k0...
    + inv v; rewrite IHt...
    + rewrite IHk0. reflexivity.
Qed. *)


Fixpoint mapK {A B} (f : A → B) (k : K A) : K B := 
  match k with
  | K_nil => K_nil
  | K_let k1 e2 => K_let (mapK f k1) (map (option_map f) e2)
  end.

(* Lemma mapK_mapK_law : forall A k B C (f : A → B) (g : B → C),
  mapK g (mapK f k) = mapK (g ∘ f) k.
Proof.
  induction k; intros; cbn; auto.
  rewrite IHk.
  rewrite map_map_law.
  rewrite option_map_comp_law.
  reflexivity.
Qed. *)

Instance LiftK : Lift K := λ {A}, mapK Some.


(* Fixpoint bindK {A B} (f : A → tm B) (k : K A) : K B := 
  match k with
  | K_nil => K_nil
  | K_let k1 e2 => K_let (bindK f k1) (bind (fun a => 
      match a with
      | None   => tm_var None
      | Some a => map Some (f a)
      end) e2)
  end.

Lemma bindV_mapV_law : ∀ {A B C} (f : B → tm C) (g : A → B) v,
  bindV f (mapV g v) = bindV (λ a, f (g a)) v.
Proof.
  intros.
  apply inj_val. repeat rewrite bindV_is_bind. rewrite mapV_is_map.
  apply bind_map_law.
Qed.

Lemma bindK_mapK_law : ∀ {A B C} (f : B → tm C) (g : A → B) k,
  bindK f (mapK g k) = bindK (λ a, f (g a)) k.
Proof.
  intros. generalize dependent B. generalize dependent C.
  induction k; intros; cbn; auto.
  rewrite IHk; f_equal.
  rewrite bind_map_law; f_equal.
  apply functional_extensionality; intros [a|]; cbn; auto.
Qed.

Lemma mapV_bindV_law : ∀ {A B C} (f : A → tm B) (g : B → C) v,
  bindV (map g ∘ f) v = mapV g (bindV f v).
Proof.
  intros. apply inj_val. rewrite mapV_is_map. repeat rewrite bindV_is_bind. apply map_bind_law.
Qed.

Lemma mapK_bindK_law : ∀ {A B C} (f : A → tm B) (g : B → C) k,
  bindK (map g ∘ f) k = mapK g (bindK f k).
Proof.
  intros; generalize dependent B; generalize dependent C; induction k; intros; cbn; auto.
  rewrite IHk; f_equal.
  rewrite <- map_bind_law; f_equal.
  apply functional_extensionality; intros [a|]; cbn; auto.
  change ((map g ∘ f) a) with (map g (f a)); repeat rewrite map_map_law; f_equal.
Qed. *)


(* ANCHOR Evaluation
 *)
(* Definition contract (r : redex ∅) : tm ∅ :=
  match r with
  (* (λ x. e) v  ~>  e [x := v] *)
  | redex_beta e v => <{ e [0 := v] }>

  (* v1 $ v2  ~>  v1 v2 *)
  | redex_dollar v1 v2 => <{ v1 v2 }>

  (* v $ S₀ w  ~>  w v *)
  | redex_shift v w  => <{ w v }>

  (* v $ let x = S₀ w in e  ~>  (λ x. v $ e) $ S₀ w *)
  | redex_dol_let v w e => <{ (λ {liftV v} $ e) $ S₀ w }>

  (* J[p]  ~>  let x = p in J[x] *)
  | redex_let j p => <{ let p in ↑j[0] }>

  (* let x = v in e  ~>  e [x := v] *)
  | redex_let_beta v e => <{ e [0 := v] }>

  (* let x = (let y = S₀ v1 in e2) in e3  ~>  let y = S₀ v1 in let x = e2 in e3 *)
  | redex_let_assoc v1 e2 e3 => <{ let S₀ v1 in let e2 in {map (option_map Some) e3} }>
  end. *)


(* Lemma plug_non_is_non : ∀ (k : K ∅) (t : T ∅) (p : non ∅),
  ∃ p, <{ k [t [p]] }> = non_to_tm p.
Proof.
  intros; destruct k; cbn in *.
  destruct t; cbn in *.
  eexists; reflexivity.
  eexists (non_dol _ _); reflexivity.
  eexists (non_let _ _); reflexivity.
Qed.

Lemma redex_is_non : ∀ {A} r, ∃ p, @redex_to_term A r = non_to_tm p.
Proof.
  intros. destruct r; cbn;
  try solve [try destruct j; eexists (non_app _ _) + eexists (non_dol _ _) + eexists (non_let _ _); reflexivity].
Qed.

Lemma non_when_contr : ∀ e e,
  e ~> e →
  ∃ p, e = non_to_tm p.
Proof.
  intros. inversion H; clear H; subst.
  apply redex_is_non.
Qed.

Lemma non_when_step : ∀ e e,
  e --> e →
  ∃ p, e = non_to_tm p.
Proof.
  intros. inversion H; clear H; subst.
  apply non_when_contr in H0 as [p Hp]; subst.
  apply plug_non_is_non.
Qed.

Lemma non_when_steps_to_non : ∀ e (p : non ∅),
  e -->* p →
  ∃ p, e = non_to_tm p.
Proof.
  intros. dependent induction H. exists p. reflexivity.
  destruct (IHmulti p) as [p IH]; auto; subst.
  apply (non_when_step x p); auto.
Qed.

Lemma non_when_steps_to_plug_non : ∀ e (k : K ∅) (t : T ∅) (p : non ∅),
  e -->* <{ k [t [p]] }> →
  ∃ p, e = non_to_tm p.
Proof.
  intros. destruct (plug_non_is_non k t p) as [p Hp].
  apply (non_when_steps_to_non _ p). rewrite Hp in *. assumption.
Qed. *)


(* Lemma step_let : ∀ {e1 e2 e},
  e1 --> e2 →
  <{ let e1 in e }> --> <{ let e2 in e }>.
Proof.
  intros. generalize dependent e.
  induction H; auto; intros.
  apply (step_tm (K_let k e) t e1 e2).
  apply H.
Qed.

Lemma multi_let : ∀ {e1 e2 e},
  e1 -->* e2 →
  <{ let e1 in e }> -->* <{ let e2 in e }>.
Proof.
  intros. generalize dependent e.
  induction H; auto; intros.
  eapply (multi_step); [idtac | apply IHmulti].
  apply step_let.
  apply H.
Qed. *)

(* Lemma step_delim : ∀ {v : val ∅} {e1 e2},
  e1 --> e2 →
  <{ v $ e1 }> --> <{ v $ e2 }>.
Proof.
  intros. generalize dependent v.
  induction H; auto; intros.
  apply (step_tm K_nil (T_cons v k t) e1 e2).
  apply H.
Qed.

Lemma multi_delim : ∀ {v : val ∅} {e1 e2},
  e1 -->* e2 →
  <{ v $ e1 }> -->* <{ v $ e2 }>.
Proof.
  intros. generalize dependent v.
  induction H; auto; intros.
  eapply (multi_step); [idtac | apply IHmulti].
  apply step_delim.
  apply H.
Qed. *)

(* Lemma step_k : ∀ {e1 e2} {k : K ∅},
  e1 --> e2 →
  <{ k[e1] }> --> <{ k[e2] }>.
Proof.
  intros e1 e2 k; generalize dependent e1; generalize dependent e2.
  induction k; auto; intros.
  cbn. apply step_let. apply IHk. apply H.
Qed.

Lemma multi_k : ∀ {e1 e2} {k : K ∅},
  e1 -->* e2 →
  <{ k[e1] }> -->* <{ k[e2] }>.
Proof.
  intros. generalize dependent k.
  induction H; auto; intros.
  eapply (multi_step); [idtac | apply IHmulti].
  apply step_k.
  apply H.
Qed. *)

(* Lemma step_t : ∀ {e1 e2} {t : T ∅},
  e1 --> e2 →
  <{ t[e1] }> --> <{ t[e2] }>.
Proof.
  intros e1 e2 t; generalize dependent e1; generalize dependent e2.
  induction t; auto; intros.
  cbn. apply step_delim. apply step_k. apply IHt. apply H.
Qed.

Lemma multi_t : ∀ {e1 e2} {t : T ∅},
  e1 -->* e2 →
  <{ t[e1] }> -->* <{ t[e2] }>.
Proof.
  intros. generalize dependent t.
  induction H; auto; intros.
  eapply (multi_step); [idtac | apply IHmulti].
  apply step_t.
  apply H.
Qed. *)


(* Lemma lift_map : ∀ {A B} (e : tm A) (f : A → B),
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

Lemma bindJ_lift : ∀ {A B} j (f : ^A → tm B),
  bindJ f (↑j) = bindJ (f ∘ Some) j.
Proof.
  intros.
  unfold lift. unfold LiftJ.
  rewrite bindJ_mapJ_law. f_equal.
Qed.

Lemma bindK_lift : ∀ {A B} k (f : ^A → tm B),
  bindK f (↑k) = bindK (f ∘ Some) k.
Proof.
  intros.
  unfold lift. unfold LiftK.
  rewrite bindK_mapK_law. f_equal.
Qed.

Lemma lift_bind : ∀ {A B} e (f : A → tm B),
  ↑(bind f e) = bind (lift ∘ f) e.
Proof.
  intros.
  unfold lift. unfold LiftTm.
  rewrite map_bind_law. reflexivity.
Qed.

Lemma lift_bindJ : ∀ {A B} j (f : A → tm B),
  ↑(bindJ f j) = bindJ (lift ∘ f) j.
Proof.
  intros.
  unfold lift. unfold LiftJ. unfold LiftTm.
  rewrite mapJ_bindJ_law. reflexivity.
Qed.

Lemma lift_bindK : ∀ {A B} k (f : A → tm B),
  ↑(bindK f k) = bindK (lift ∘ f) k.
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
  rewrite IHk. reflexivity.
Qed.

Lemma lift_tm_abs : ∀ {A} (e : tm ^A),
  <{ λ {map (option_map Some) e} }> = ↑<{ λ e }>.
Proof.
  reflexivity.
Qed.

Lemma lift_mapJ : ∀ {A B} j (f : A → B),
  ↑(mapJ f j) = mapJ (option_map f) (↑j).
Proof.
  intros. destruct j; cbn;
  repeat rewrite map_map_law;
  repeat rewrite mapV_mapV_law;
  f_equal.
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
  bind (var_subst (tm_val v)) (↑e) = e.
Proof.
  intros. change (bind (var_subst v) (↑e)) with <{ (↑e) [0 := v] }>.
  apply subst_lift.
Qed.

Lemma bind_var_subst_lift_j : ∀ {A} (j : J A) e v,
  bind (var_subst (tm_val v)) <{ ↑j[e] }> = <{ j [{bind (var_subst (tm_val v)) e}] }>.
Proof.
  intros; destruct j; cbn; auto;
  try change (map Some t) with (↑t);
  try change (mapV Some v0) with (liftV v0);
  try rewrite <- lift_tm_val;
  try rewrite bind_var_subst_lift; reflexivity.
Qed.

Lemma bind_var_subst_lift_k : ∀ {A} (k : K A) e v,
  bind (var_subst (tm_val v)) <{ ↑k[e] }> = <{ k [{bind (var_subst (tm_val v)) e}] }>.
Proof.
  induction k; intros; cbn; auto.
  rewrite IHk.
  f_equal.
  rewrite bind_map_law.
  assert ((λ a, match option_map Some a with Some a0 => map Some (var_subst v a0) | None => <{ 0 }> end) = (λ a, <{ var a }>)).
  apply functional_extensionality; intros [a|]; cbn; auto.
  rewrite H.
  apply bind_pure.
Qed.

Lemma subst_plug_of_lift_j : ∀ {A} (j : J A) (v : val A),
  <{ (↑j[0])[0 := v] }> = <{ j[v] }>.
Proof.
  intros. destruct j; cbn; auto;
  try change (mapV Some v0) with (liftV v0);
  try change (map Some t) with (↑t);
  try rewrite <- lift_tm_val;
  rewrite bind_var_subst_lift; reflexivity.
Qed. *)


(* ANCHOR Context Capture
 *)
(* Theorem plug_k_let_reassoc_s_0 : ∀ (k : K ∅) e1 e2,
  <{ k [let S₀, e1 in e2] }> -->* <{ let S₀, e1 in ↑k[e2] }>.
Proof.
  induction k; intros; cbn; auto.
  eapply multi_trans. eapply multi_let. apply IHk.
  rewrite lambda_to_val. apply multi_contr. apply contr_let_assoc.
Qed.

Theorem plug_k_let_reassoc_s_0 : ∀ (k : K ∅) (v : val ∅) e,
  <{ k [let S₀ v in e] }> -->* <{ let S₀ v in ↑k[e] }>.
Proof.
  induction k; intros; cbn; auto.
  eapply multi_trans. eapply multi_let. apply IHk.
  apply multi_contr. apply contr_let_assoc.
Qed.


Lemma plug_k_let_let_S0_step_inv : ∀ (k : K ∅) (v : val ∅) e1 e2 term,
  <{ k [let let S₀ v in e1 in e2] }> --> term →
  term = <{ k [let S₀ v in let e1 in {map (option_map Some) e2}] }>.
Proof.
  intros.
  eapply deterministic_step in H.
  2: { eapply step_k. apply step_contr. apply contr_let_assoc. }
  subst. reflexivity.
Qed.

Lemma S0_val_does_not_step : ∀ (v : val ∅) term,
  <{ S₀ v }> --> term → False.
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

Lemma let_S0_does_not_step : ∀ (v : val ∅) e term,
  <{ let S₀ v in e }> --> term → False.
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

Lemma plug_step_inv : ∀ (k : K ∅) (t : T ∅) (r : redex ∅) term,
  <{ k [t [r]] }> --> term →
  term = <{ k [t [{contract r}]] }>.
Proof.
  intros. inversion H; clear H; subst.
  inversion H1; clear H1; subst. 
  assert (decompose <{ k0 [t0 [r0]] }> = decompose <{ k [t [r]] }>) by (rewrite H0; auto).
  repeat rewrite decompose_plug_redex in *. inversion H; clear H; subst. reflexivity.
Qed.

Lemma inner_step_inv : ∀ (k : K ∅) (t : T ∅) e term inner,
  <{ k [t [e]] }> --> term →
  e --> inner →
  term = <{ k [t [inner]] }>.
Proof.
  intros. eapply step_t in H0. eapply step_k in H0.
  eapply deterministic_step; eauto.
Qed.

Lemma fold_redex_dol_let : ∀ (w v : val ∅) e,
  <{ w $ let S₀ v in e }> = redex_dol_let w v e.
Proof.
  reflexivity.
Qed.

Lemma fold_redex_shift : ∀ (w v : val ∅),
  <{ w $ S₀ v }> = redex_shift w v.
Proof.
  intros. auto.
Qed.

Lemma plug_shift_step_inv : ∀ (k0 : K ∅) (t0 : T ∅) (w : val ∅) (k : K ∅) (v : val ∅) e term,
  <{ k0 [t0 [w $ k [let S₀ v in e]]] }> --> term → ∃ inner,
  term = <{ k0 [t0 [inner]] }> /\
  <{ w $ k [let S₀ v in e] }> --> inner.
Proof.
  intros.
  remember (plug_k_let_reassoc_s_0 k v e) as Hinner eqn:HH. clear HH.
  apply (@multi_delim w) in Hinner.
  inversion Hinner; clear Hinner; subst. 
  - rewrite H2 in *.
    rewrite fold_redex_dol_let in *.
    eapply (plug_step_inv k0 t0 _ term) in H. subst. eauto.
  - eapply step_t in H0 as HH. eapply step_k in HH.
    repeat eexists.
    + apply (deterministic_step _ _ _ H HH).
    + assumption. 
Qed.

Lemma shift_step_inv : ∀ (w : val ∅) (k : K ∅) (v : val ∅) e term,
  <{ w $ k [let S₀ v in e] }> --> term → 
  (k = K_nil /\ term = contract (redex_dol_let w v e)) \/
  (∃ inner, <{ k [let S₀ v in e] }> --> inner /\ term = <{ w $ inner }>).
Proof.
  intros.
  remember (plug_k_let_reassoc_s_0 k v e) as Hinner eqn:HH. clear HH.
  inversion Hinner; clear Hinner; subst.
  - left. rewrite H2 in *.
    destruct k.
    split; auto. cbn in *.
    eapply (deterministic_step _ _ _ H). auto.
    cbn in H2. inversion H2. destruct k; inversion H1.
  - right.
    apply (inner_step_inv K_nil (T_cons w K_nil T_nil) _ _ _ H) in H0 as HH.
    repeat eexists; eauto.
Qed. *)
