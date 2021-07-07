(* Common *)
Require Export Common.

(* Knowledge Links:
  - shift/reset tutorial http://pllab.is.ocha.ac.jp/~asai/cw2011tutorial/main-e.pdf
  - shift0/reset0 http://www.tilk.eu/shift0/materzok-csl13.pdf
  - https://bitbucket.org/pl-uwr/aleff-lex/src/master/coq/Lang/Open/Syntax.v
 *)

(* Terms *)

Inductive tm : Type → Type := 
| tm_val    : ∀ {V}, val V → tm V
| tm_nonval : ∀ {V}, non V → tm V
with val : Type → Type := 
| val_var   : ∀ {V}, V → val V
| val_lam   : ∀ {V}, tm ^V → val V
| val_S₀    : ∀ {V}, val V
with non : Type → Type :=
| non_app   : ∀ {V}, tm V → tm V → non V
| non_let   : ∀ {V}, tm V → tm ^V → non V
| non_reset : ∀ {V}, tm V → tm V → non V
.

Declare Custom Entry λc_dollar_scope.
Notation "<{ M }>" := M (at level 1, M custom λc_dollar_scope at level 99).
Notation "( x )" := x (in custom λc_dollar_scope, x at level 99).
Notation "{ x }" := x (in custom λc_dollar_scope at level 0, x constr).
Notation "x" := x (in custom λc_dollar_scope at level 0, x constr at level 0).
(* Notation tm_var_n n := (tm_var (var_n n)). *)
(* Notation "0" := (tm_var_n 0) (in custom λc_dollar_scope at level 0). *)
(* Notation "1" := (tm_var_n 1) (in custom λc_dollar_scope at level 0). *)
(* Notation "2" := (tm_var_n 2) (in custom λc_dollar_scope at level 0). *)
(* Notation "3" := (tm_var_n 3) (in custom λc_dollar_scope at level 0). *)
(* Notation "4" := (tm_var_n 4) (in custom λc_dollar_scope at level 0). *)
Notation "'var' v" := (tm_val (val_var v)) (in custom λc_dollar_scope at level 1, left associativity).
Notation "0" := <{ var None }> (in custom λc_dollar_scope at level 0).
Notation "1" := <{ var {Some None} }> (in custom λc_dollar_scope at level 0).
Notation "2" := <{ var {Some (Some None)} }> (in custom λc_dollar_scope at level 0).
Notation "M N" := (tm_nonval (non_app M N)) (in custom λc_dollar_scope at level 1, left associativity).
Notation "'λ' M" := (tm_val (val_lam M))
  (in custom λc_dollar_scope at level 90,
   M custom λc_dollar_scope at level 99,
   right associativity).
Notation "M '$' N" := (tm_nonval (non_reset M N)) (in custom λc_dollar_scope at level 80, right associativity).
(* Notation "'S₀'" := (tm_val (val_S₀)) (in custom λc_dollar_scope at level 0). *)
Notation "'S₀' M" := <{ {tm_val (val_S₀)} (λ M) }>
  (in custom λc_dollar_scope at level 90,
   M custom λc_dollar_scope at level 99,
   right associativity).
Notation "'let' M 'in' N" := (tm_nonval (non_let M N))
  (in custom λc_dollar_scope at level 95,
   M custom λc_dollar_scope at level 99,
   N custom λc_dollar_scope at level 99,
   right associativity).

Notation "< M >" := <{ (λ 0) $ M }> (in custom λc_dollar_scope at level 0).

(* Closed terms *)

Inductive Void : Type := .
Definition term := tm Void.

(* Examples *)

Example tm_id : term := <{ λ 0 }>.
Example tm_ω  : term := <{ λ 0 0 }>.
Example tm_Ω  : term := <{ (λ 0 0) (λ 0 0) }>.

Example tm_e1 a z b : term := <{ <a <(S₀ S₀ 1 (0 z)) b>> }>.
Example tm_shift_id e : term := <{ S₀ 0 $ e }>.

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