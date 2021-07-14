(* Common *)
Require Export Common.

(* Knowledge Links:
  - shift/reset tutorial http://pllab.is.ocha.ac.jp/~asai/cw2011tutorial/main-e.pdf
  - shift0/reset0 http://www.tilk.eu/shift0/materzok-csl13.pdf
  - https://bitbucket.org/pl-uwr/aleff-lex/src/master/coq/Lang/Open/Syntax.v
 *)

(* Terms *)

Inductive tm {V} := 
| tm_val    : val → tm
| tm_non    : non → tm
with val {V} := 
| val_var   : V → val
| val_lam   : @tm ^V → val
| val_S₀    : val
with non {V} :=
| non_app   : tm → tm → non
| non_let   : tm → @tm ^V → non
| non_reset : tm → tm → non
.
Arguments tm  V : clear implicits.
Arguments val V : clear implicits.
Arguments non V : clear implicits.

Scheme tm_mut := Induction for tm Sort Prop
with val_mut := Induction for val Sort Prop
with non_mut := Induction for non Sort Prop.

Module Notations.
  Declare Custom Entry λc_dollar_scope.
  Notation "<{ M }>" := M (at level 1, M custom λc_dollar_scope at level 99).
  Notation "( x )" := x (in custom λc_dollar_scope, x at level 99).
  Notation "{ x }" := x (in custom λc_dollar_scope at level 0, x constr).
  Notation "x" := x (in custom λc_dollar_scope at level 0, x constr at level 0).
  Notation "'var' v" := (tm_val (val_var v)) (in custom λc_dollar_scope at level 1, left associativity).
  Notation "0" := <{ var None }> (in custom λc_dollar_scope at level 0).
  Notation "1" := <{ var {Some None} }> (in custom λc_dollar_scope at level 0).
  Notation "2" := <{ var {Some (Some None)} }> (in custom λc_dollar_scope at level 0).
  Notation "M N" := (tm_non (non_app M N)) (in custom λc_dollar_scope at level 1, left associativity).
  Notation "'λ' M" := (tm_val (val_lam M))
    (in custom λc_dollar_scope at level 90,
    M custom λc_dollar_scope at level 99,
    right associativity).
  Notation "M '$' N" := (tm_non (non_reset M N)) (in custom λc_dollar_scope at level 80, right associativity).
  Notation "'S₀'" := (tm_val (val_S₀)) (in custom λc_dollar_scope at level 0).
  Notation "'S₀λ' M" := <{ {tm_val (val_S₀)} (λ M) }>
    (in custom λc_dollar_scope at level 90,
    M custom λc_dollar_scope at level 99,
    right associativity).
  Notation "'let' M 'in' N" := (tm_non (non_let M N))
    (in custom λc_dollar_scope at level 95,
    M custom λc_dollar_scope at level 99,
    N custom λc_dollar_scope at level 99,
    right associativity).
  Notation "< M >" := <{ (λ 0) $ M }> (in custom λc_dollar_scope at level 0).
End Notations.
Export Notations.

(* Map *)

Fixpoint map {A B : Type} (f : A → B) (e : tm A) : tm B :=
  match e with
  | tm_val t => tm_val (map_val f t)
  | tm_non t => tm_non (map_non f t)
  end
with map_val {A B : Type} (f : A → B) (e : val A) : val B :=
  match e with
  | val_var v => val_var (f v)
  | val_lam e => val_lam (map (option_map f) e)
  | val_S₀    => val_S₀
  end
with map_non {A B : Type} (f : A → B) (e : non A) : non B :=
  match e with
  | non_app e1 e2 => non_app (map f e1) (map f e2)
  | non_let e1 e2 => non_let (map f e1) (map (option_map f) e2)
  | non_reset e1 e2 => non_reset (map f e1) (map f e2)
  end.

Notation map_id_law_for F := (λ V e,
  ∀ (f : V → V),
    (∀ x, f x = x) →
    F f e = e
).

Ltac crush := 
  intros; cbn; f_equal; auto.

Ltac crush_option := 
  let x := fresh "x" in
  intros [x|]; cbn; f_equal; auto.

Lemma map_id_law : ∀ V e, map_id_law_for map V e.
Proof.
  cbn; apply (tm_mut
    (map_id_law_for map)
    (map_id_law_for map_val)
    (map_id_law_for map_non)); crush;
  (apply H + apply H0); crush_option.
Qed.

Notation map_comp_law_for F := (λ A e,
  ∀ B C (f : A → B) (g : B → C),
    F g (F f e) = F (g ∘ f) e
).

Lemma option_map_comp : ∀ A B C (f : A → B) (g : B → C),
  option_map (g ∘ f) = option_map g ∘ option_map f.
Proof.
  intros. apply functional_extensionality. crush_option.
Qed.

Lemma map_comp_law : ∀ V e, map_comp_law_for map V e.
Proof.
  cbn; apply (tm_mut
    (map_comp_law_for map)
    (map_comp_law_for map_val)
    (map_comp_law_for map_non)); crush;
  rewrite option_map_comp;
  (apply H + apply H0); crush_option.
Qed.

(* Bind *)

Definition option_bind {A B} (f: A → val B) (o: ^A) : val ^B :=
  match o with
  | None => val_var None
  | Some a => map_val Some (f a)
  end.

Fixpoint bind {A B : Type} (f : A → val B) (e : tm A) : tm B :=
  match e with
  | tm_val t => tm_val (bind_val f t)
  | tm_non t => tm_non (bind_non f t)
  end
with bind_val {A B : Type} (f : A → val B) (e : val A) : val B :=
  match e with
  | val_var v => f v
  | val_lam e => val_lam (bind (option_bind f) e)
  | val_S₀    => val_S₀
  end
with bind_non {A B : Type} (f : A → val B) (e : non A) : non B :=
  match e with
  | non_app e1 e2 => non_app (bind f e1) (bind f e2)
  | non_let e1 e2 => non_let (bind f e1) (bind (option_bind f) e2)
  | non_reset e1 e2 => non_reset (bind f e1) (bind f e2)
  end.

Notation bind_is_map_for F Bind := (λ A e,
  ∀ B (f : A → B), F f e = Bind (λ v, val_var (f v)) e
).

Lemma bind_is_map : ∀ A e, bind_is_map_for map bind A e.
Proof.
  cbn; apply (tm_mut
    (bind_is_map_for map bind)
    (bind_is_map_for map_val bind_val)
    (bind_is_map_for map_non bind_non)); crush;
    (rewrite H + rewrite H0); f_equal; apply functional_extensionality; crush_option.
Qed.

(* Notation bind_law_for Bind := (λ A e,
  ∀ B C (f:A → val B) (g:B → val C),
    Bind g (Bind f e) = Bind (λ a, Bind g (f a)) e
).
Lemma bind_law : ∀ A e, bind_law_for bind A e. *)


(* Closed terms *)

Inductive Void : Type := .
Definition term := tm Void.

(* Examples *)

Example tm_id : term := <{ λ 0 }>.
Example tm_ω  : term := <{ λ 0 0 }>.
Example tm_Ω  : term := <{ (λ 0 0) (λ 0 0) }>.

Example tm_e1 a z b : term := <{ <a <(S₀λ S₀λ 1 (0 z)) b>> }>.

Example tm_shift_id  e : term := <{ S₀λ 0 $ e }>.

(* Contexts *)

Section Contexts.
  Context {V : Type}.
  Inductive J :=
  | J_app_l : tm V → J   (* [] M *)
  | J_app_r : val V → J  (* V [] *)
  | J_S₀ : tm V → J      (* []$M *)
  .
  Inductive K :=
  | K_empty : K
  | K_JK : J → K → K
  | K_let : K → tm ^V → K
  .
  Inductive E :=
  | E_K : K → E → E
  | E_V : val V → E → E
  .
End Contexts.
Arguments J V : clear implicits.
Arguments K V : clear implicits.
Arguments E V : clear implicits.

Inductive C {V} :=
| C_E : E V → C → C
| C_app : non V → C → C
| C_reset : non V → C → C
| C_lam : @C ^V → C
| C_let : tm V → @C ^V → C
.
Arguments C V : clear implicits.



(* Reduction *)

Reserved Notation "M '-->' N" (at level 40).
Inductive step : term -> term -> Prop :=
| step_beta_v : forall M V,
  <{ (λ M) V }> --> <{ M [0 := V] }>
.