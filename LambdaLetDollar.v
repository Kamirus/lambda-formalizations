Require Export Common.

Inductive tm' {A} :=
| tm_var' : A → tm'
| tm_abs' : @tm' ^A → tm' (* λ  x. e *)
| tm_s_0' : @tm' ^A → tm' (* S₀ f. e *)
| tm_app' : tm' → tm' → tm' (* e   e *)
| tm_dol' : tm' → tm' → tm' (* e $ e *)
| tm_let' : tm' → @tm' ^A → tm' (* let x = e1 in e2 *)
.
Arguments tm' A : clear implicits.
Global Hint Constructors tm' : core.

Inductive val' {A} :=
| val_abs' : @tm' ^A → val'
.
Arguments val' A : clear implicits.
Global Hint Constructors val' : core.

Definition val_to_tm' {A} (v : val' A) := 
  match v with
  | val_abs' e => tm_abs' e
  end.

Inductive non' {A} :=
| non_s_0' : tm' ^A → non' (* S₀ f. e *)
| non_app' : tm' A → tm'  A → non' (* e   e *)
| non_dol' : tm' A → tm'  A → non' (* e $ e *)
| non_let' : tm' A → tm' ^A → non' (* let x = e1 in e2 *)
.

Arguments non' A : clear implicits.
Global Hint Constructors non' : core.

Definition non_to_tm' {A} (p : non' A) := 
  match p with
  | non_s_0' e => tm_s_0' e
  | non_app' e1 e2 => tm_app' e1 e2
  | non_dol' e1 e2 => tm_dol' e1 e2
  | non_let' e1 e2 => tm_let' e1 e2
  end.

Declare Custom Entry λ_let_dollar_scope.
Notation "<{ e }>" := e (at level 1, e custom λ_let_dollar_scope at level 99).
Notation "( x )" := x (in custom λ_let_dollar_scope, x at level 99).
Notation "{ x }" := x (in custom λ_let_dollar_scope at level 0, x constr).
Notation "x" := x (in custom λ_let_dollar_scope at level 0, x constr at level 0).
Notation "'var' v" := (tm_var' v) (in custom λ_let_dollar_scope at level 1, left associativity).
Notation "0" := <{ var None }> (in custom λ_let_dollar_scope at level 0).
Notation "1" := <{ var {Some None} }> (in custom λ_let_dollar_scope at level 0).
Notation "2" := <{ var {Some (Some None)} }> (in custom λ_let_dollar_scope at level 0).
Notation "'λ' e" := (tm_abs' e)
    (in custom λ_let_dollar_scope at level 90,
      e custom λ_let_dollar_scope at level 99,
      right associativity).
Notation "'λv'' e" := (val_abs' e)
    (in custom λ_let_dollar_scope at level 90,
      e custom λ_let_dollar_scope at level 99,
      right associativity).
Notation "'S₀' e" := (tm_s_0' e)
    (in custom λ_let_dollar_scope at level 90,
      e custom λ_let_dollar_scope at level 99,
      right associativity).
Notation "e1 e2" := (tm_app' e1 e2) (in custom λ_let_dollar_scope at level 10, left associativity).
Notation "e1 '$' e2" := (tm_dol' e1 e2) (in custom λ_let_dollar_scope at level 80, right associativity).
Notation "'let' e1 'in' e2" := (tm_let' e1 e2) (in custom λ_let_dollar_scope at level 70, right associativity).


Fixpoint map' {A B : Type} (f : A -> B) (e : tm' A) : tm' B :=
  match e with
  | <{ var a }> => <{ var {f a} }>
  | <{ λ  e' }> => <{ λ  {map' (option_map f) e'} }>
  | <{ S₀ e' }> => <{ S₀ {map' (option_map f) e'} }>
  | <{ e1   e2 }> => <{ {map' f e1}   {map' f e2} }>
  | <{ e1 $ e2 }> => <{ {map' f e1} $ {map' f e2} }>
  | <{ let e1 in e2 }> => tm_let' (map' f e1) (map' (option_map f) e2)
  end.

(* Lemma map_id_law : forall {V} (f : V -> V) e,
  (forall x, f x = x) ->
  f <$> e = e.
Admitted.
Lemma map_comp_law : forall A e B C (f:A->B) (g:B->C),
  g <$> (f <$> e) = g ∘ f <$> e.
Admitted. *)


Fixpoint bind' {A B : Type} (f : A -> tm' B) (e : tm' A) : tm' B :=
  match e with
  | <{ var a }> => f a
  | <{ e1   e2 }> => <{ {bind' f e1}   {bind' f e2} }>
  | <{ e1 $ e2 }> => <{ {bind' f e1} $ {bind' f e2} }>
  | <{ λ  e' }> => tm_abs' (bind' (fun a' => 
      match a' with
      | None   => tm_var' None
      | Some a => map' Some (f a)
      end) e')
  | <{ S₀ e' }> => tm_s_0' (bind' (fun a' => 
      match a' with
      | None   => tm_var' None
      | Some a => map' Some (f a)
      end) e')
  | <{ let e1 in e2 }> => tm_let' (bind' f e1) (bind' (fun a' => 
      match a' with
      | None   => tm_var' None
      | Some a => map' Some (f a)
      end) e2)
  end.

(* Lemma bind_is_map : forall A e B (f:A->B),
  f <$> e = e >>= (fun v => tm_var (f v)).
Admitted. *)

(* Lemma bind_law : forall A e B C (f:A->tm' B) (g:B->tm' C),
  e >>= f >>= g = e >>= (fun a => f a >>= g).
Admitted. *)


Definition var_subst' {V} e' (v:^V) :=
  match v with
  | None => e'
  | Some v => <{ var v }>
  end.

Definition tm_subst0' {V} (e:tm' ^V) (v:val' V) :=
  bind' (var_subst' (val_to_tm' v)) e.

Notation "e [ 0 := v ]" := (tm_subst0' e v)
  (in custom λ_let_dollar_scope at level 0,
    e custom λ_let_dollar_scope,
    v custom λ_let_dollar_scope at level 99).


Definition tm_dec' (e : tm' ␀) : (val' ␀ + non' ␀) :=
  match e with
  | <{ var a }> => from_void a
  | <{ λ  e' }> => inl (val_abs' e')
  | <{ S₀ e' }> => inr (non_s_0' e')
  | <{ e1   e2 }> => inr (non_app' e1 e2)
  | <{ e1 $ e2 }> => inr (non_dol' e1 e2)
  | <{ let e1 in e2 }> => inr (non_let' e1 e2)
  end.


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
  | redex_beta'      : val' A → val' A → redex'
  | redex_dollar'    : val' A → val' A → redex'
  | redex_shift'     : val' A → tm' ^A → redex'  (* v $ S₀ f. e *)
  | redex_dol_let'   : val' A → tm' ^A → tm' ^A → redex' (* v $ let x = S₀ f. e1 in e2 *)
  | redex_let'       : J'     → non' A → redex'  (* J[p] *)
  | redex_let_beta'  : val' A → tm' ^A → redex'  (* let x = v in e *)
  | redex_let_assoc' : tm' ^A → tm' ^A → tm' ^A → redex' (* let x = (let y = S₀ f. e1 in e2) in e3 *)
  .

  Inductive dec' :=
  | dec_value' : val' A → dec'
  | dec_stuck_s_0' : tm' ^A → dec' (* S₀ f. e1 *)
  | dec_stuck_let' : tm' ^A → tm' ^A → dec' (* let x = S₀ f. e1 in e2 *)
  | dec_redex' : K' → T' → redex' → dec' (* K[T[Redex]] *)
  .

  Definition stuck_to_non' : tm' ^␀ * option (tm' ^␀) → non' ␀ := λ s,
    match s with
    | (e, None) => non_s_0' e
    | (e1, Some e2) => non_let' <{ S₀ e1 }> e2
    end.

  Definition plugJ' j e' :=
    match j with
    | J_fun' e => <{ e' e }>
    | J_arg' v => <{ {val_to_tm' v} e' }>
    | J_dol' e => <{ e' $ e }>
    end.
  
  Fixpoint plugK' k e :=
    match k with
    | K_nil' => e
    | K_let' k1 e2 => <{ let {plugK' k1 e} in e2 }>
    end.

  Fixpoint plugT' trail e :=
    match trail with
    | T_nil' => e
    | T_cons' v k t => <{ {val_to_tm' v} $ {plugK' k (plugT' t e)} }>
    end.

  Definition redex_to_term' r := 
    match r with
    | redex_beta'   v1 v2 => <{ {val_to_tm' v1} {val_to_tm' v2} }>
    | redex_dollar' v1 v2 => <{ {val_to_tm' v1} $ {val_to_tm' v2} }>
    | redex_shift'  v  e  => <{ {val_to_tm' v } $  S₀ e }>
    | redex_dol_let' v e1 e2 => <{ {val_to_tm' v } $ let S₀ e1 in e2 }>
    | redex_let' j p  => plugJ' j (non_to_tm' p)
    | redex_let_beta' v e => <{ let {val_to_tm' v} in e }>
    | redex_let_assoc' e1 e2 e3 => <{ let (let S₀ e1 in e2) in e3 }>
    end.

End Contexts.
Arguments J' A : clear implicits.
Arguments K' A : clear implicits.
Arguments T' A : clear implicits.
Arguments redex' A : clear implicits.
Arguments dec' A : clear implicits.


Fixpoint decompose' (e : tm' ␀) : dec' ␀ :=
  match e with
  | <{ var a }> => from_void a
  | <{ λ  e' }> => dec_value' (val_abs' e')
  | <{ S₀ e' }> => dec_stuck_s_0' e'
  | <{ e1 e2 }> =>
    match tm_dec' e1 with
    | inr p1 => dec_redex' K_nil' T_nil' (redex_let' (J_fun' e2) p1) (* p1 e2 *)
    | inl v1 =>
      match tm_dec' e2 with
      | inr p2 => dec_redex' K_nil' T_nil' (redex_let' (J_arg' v1) p2) (* v1 p2 *)
      | inl v2 => dec_redex' K_nil' T_nil' (redex_beta' v1 v2)         (* v1 v2 *)
      end
    end
  | <{ e1 $ e2 }> =>
    match tm_dec' e1 with
    | inr p1 => dec_redex' K_nil' T_nil' (redex_let' (J_dol' e2) p1) (* p1 $ e2 *)
    | inl v1 => (* v1 $ e *)
      match decompose' e2 with
      | dec_stuck_s_0' e2'       => dec_redex' K_nil' (T_nil')         (redex_shift' v1 e2')         (* v1 $ S₀ f. e2' *)
      | dec_stuck_let' e2_1 e2_2 => dec_redex' K_nil' (T_nil')         (redex_dol_let' v1 e2_1 e2_2) (* v1 $ let x = S₀ f. e2_1 in e2_2 *)
      | dec_redex' k t r         => dec_redex' K_nil' (T_cons' v1 k t) (r)                           (* v1 $ K[T[r]] *)
      | dec_value' v2            => dec_redex' K_nil' (T_nil')         (redex_dollar' v1 v2)         (* v1 $ v2 *)
      end
    end
  | <{ let e1 in e2 }> =>
    match decompose' e1 with
    | dec_stuck_s_0' e1'       => dec_stuck_let' e1' e2                                           (* let x = S₀ f. e1' in e2 *)
    | dec_stuck_let' e1_1 e1_2 => dec_redex' (K_nil')      T_nil' (redex_let_assoc' e1_1 e1_2 e2) (* let x = (let y = S₀ f. e1_1 in e1_2) in e2 *)
    | dec_redex' k t r         => dec_redex' (K_let' k e2) t      (r)                             (* let x = K[T[r]] in e2 *)
    | dec_value' v1            => dec_redex' (K_nil')      T_nil' (redex_let_beta' v1 e2)         (* let x = v1 in e2 *)
    end
  end.

(* Ltac inv_decompose_match H :=
  match goal with
  | H : (match decompose ?e with | dec_stuck _ _ | dec_redex _ _ _ | dec_value _ => _ end = _) |- _
    => let d := fresh "d" in remember (decompose e) as d; inv d; inv_decompose_match H
  | _ => try solve [inversion H; auto]; inj H
  end. *)

(* plug ∘ decompose = id *)
(* Lemma decompose_value_inversion : ∀ e v,
  decompose e = dec_value v → e = val_to_tm' v.
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
  decompose e = dec_stuck k e' → e = plugK k <{ S₀ e' }>.
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

(* decompose ∘ plug = id *)
Lemma decompose_plug_value : ∀ v,
  decompose (val_to_tm' v) = dec_value v.
Proof.
  intros; destruct v; auto.
  Qed.

Lemma decompose_plug_stuck : ∀ k e, 
  decompose (plugK k <{ S₀ e }>) = dec_stuck k e.
Proof.
  induction k; intros; cbn; auto.
  inv j; cbn.
  - rewrite IHk; auto.
  - rewrite decompose_plug_value. rewrite IHk; auto.
  - rewrite IHk; auto.
  Qed.

Lemma decompose_plug_redex : ∀ k t r,
  decompose (plugK k (plugT t (redex_to_term r))) = dec_redex k t r.
Proof with cbn; auto.
  intros k t; generalize dependent k; induction t; intros...
  - induction k...
    + inv r; cbn; inv v; cbn; try solve [inv v0; auto].
      rewrite decompose_plug_stuck; auto.
    + inv j; try inv v; cbn; try solve [rewrite IHk; auto].
  - induction k0...
    + inv v... rewrite IHt...
    + inv j; try inv v0; cbn; try solve [rewrite IHk0; auto].
  Qed. *)


Definition lift' {A : Type} (e : tm' A) : tm' ^A := map' Some e.

Definition liftV' {A : Type} (v : val' A) : val' ^A :=
  match v with
  | val_abs' e => val_abs' (lift' e)
  end.

Definition liftJ' {A : Type} (j : J' A) : J' ^A := 
  match j with
  | J_fun' e => J_fun' (lift' e)
  | J_arg' v => J_arg' (liftV' v)
  | J_dol' e => J_dol' (lift' e)
  end.

Fixpoint liftK' {A : Type} (k : K' A) : K' ^A :=
  match k with
  | K_nil' => K_nil'
  | K_let' k1 e2 => K_let' (liftK' k1) (lift' e2)
  end.

(* Notation "↑ e" := (lift' e) (at level 15). *)

Definition contract' (r : redex' ␀) : tm' ␀ :=
  match r with
  (* (λ x. e) v  ~>  e [x := v] *)
  | redex_beta' (val_abs' e) v => <{ e [0 := v] }>

  (* v1 $ v2  ~>  v1 v2 *)
  | redex_dollar' v1 v2 => <{ {val_to_tm' v1} {val_to_tm' v2} }>

  (* v $ S₀ f. e  ~>  e [f := λ x. v $ x] *)
  | redex_shift' v e  => <{ e [0 := λv' {lift' (val_to_tm' v)} $ 0] }>

  (* v $ let x = S₀ f. e1 in e2  ~>  (λ x. v $ e2) $ S₀ f. e1 *)
  | redex_dol_let' v e1 e2 => <{ (λ {lift' (val_to_tm' v)} $ e2) $ S₀ e1 }>

  (* J[p]  ~>  let x = p in J[x] *)
  | redex_let' j p => <{ let {non_to_tm' p} in {plugJ' (liftJ' j) <{ 0 }>} }>

  (* let x = v in e  ~>  e [x := v] *)
  | redex_let_beta' v e => <{ e [0 := v] }>

  (* let x = (let y = S₀ f. e1 in e2) in e3  ~>  let y = S₀ f. e1 in let x = e2 in e3*)
  | redex_let_assoc' e1 e2 e3 => <{ let S₀ e1 in let e2 in {lift' e3} }>
  end.

Definition step' e :=
  match decompose' e with
  | dec_redex' k t r => Some (plugK' k (plugT' t (contract' r)))
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
  Definition _id : tm' ␀ := <{ λ 0 }>.
  Definition _const : tm' ␀ := <{ λ λ 1 }>.

  Compute (eval' 10 <{ _id $ _const $ S₀ 0 }>).
  Compute (eval' 10 <{ _const $ _id $ S₀ 0 }>).

  Definition j1 : J' ␀ := J_fun' <{ λ 0 0 }>.
  Definition j2 : J' ␀ := J_arg' <{ λv' 0 }>.
  Definition j3 : J' ␀ := J_dol' <{ λ 0 }>.
  Definition ej123 := plugJ' j1 (plugJ' j2 (plugJ' j3 <{ S₀ 0 }>)).

  Example from_K_to_K' : eval' 3 ej123 = <{ 
    let
      let
        let S₀ 0
        in {plugJ' (liftJ' j3) <{ 0 }>}
      in {plugJ' (liftJ' j2) <{ 0 }>}
    in {plugJ' (liftJ' j1) <{ 0 }>}
  }>. Proof. auto. Qed.

  Example from_K_to_stuck' : eval' 5 ej123 = <{ 
    let S₀ 0 in
    let
      let {plugJ' (liftJ' j3) <{ 0 }>}
      in {lift' (plugJ' (liftJ' j2) <{ 0 }>)}
    in {lift' (plugJ' (liftJ' j1) <{ 0 }>)}
  }>. Proof. auto. Qed.

  Example ex_dol_let : eval' 6 <{ _id $ ej123 }> = <{ 
    (λ {lift' _id} $ 
      let
        let {plugJ' (liftJ' j3) <{ 0 }>}
        in {lift' (plugJ' (liftJ' j2) <{ 0 }>)}
      in {lift' (plugJ' (liftJ' j1) <{ 0 }>)}
    ) $ S₀ 0
  }>. Proof. cbn. auto. Qed.

  Example ex_shift : eval' 7 <{ _id $ ej123 }> = <{
    λ {lift' <{ 
        λ {lift' _id} $ 
          let
            let {plugJ' (liftJ' j3) <{ 0 }>}
            in {lift' (plugJ' (liftJ' j2) <{ 0 }>)}
          in {lift' (plugJ' (liftJ' j1) <{ 0 }>)}
      }>} $ 0
  }>. Proof. cbn. auto. Qed.

  Compute (decompose' (eval' 7 <{ _id $ ej123 }>)).
  
End Examples.