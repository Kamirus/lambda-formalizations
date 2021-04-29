
Notation "^ f" := (option_map f) (at level 5, right associativity).
Notation "^ X" := (option X) : type_scope.

Inductive ty :=
| ty_unit : ty
| ty_arr : ty -> ty -> ty
.
Hint Constructors ty : core.

Inductive tm (V : Type) :=
| tm_var : V -> tm V
| tm_app : tm V -> tm V -> tm V
| tm_abs : ty -> tm ^V -> tm V
.
Hint Constructors tm : core.
Arguments tm_var {V}.
Arguments tm_app {V}.
Arguments tm_abs {V}.

Declare Custom Entry stlc.
Notation "'do' e" := e (at level 100, e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "{ x }" := x (in custom stlc at level 0, x constr).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "0" := (tm_var None) (in custom stlc at level 0).
Notation "1" := (tm_var (Some None)) (in custom stlc at level 0).
Notation "2" := (tm_var (Some (Some None))) (in custom stlc at level 0).
(* Notation "'S' .. 'S' x" := (tm_var (inc_S .. (inc_S x) ..)) (in custom stlc at level 0). *)
Notation "'var' V" := (tm_var V) (in custom stlc at level 1, left associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ t , e" :=
  (tm_abs t e) (in custom stlc at level 90,
                 t custom stlc at level 99,
                 e custom stlc at level 99,
                 left associativity).
(* Coercion tm_var : V >-> tm V. *)
Notation "S -> T" := (ty_arr S T) (in custom stlc at level 50, right associativity).


(* closed terms *)
Inductive Void : Type := .
Definition term := tm Void.

(* Several examples, the type `U` is irrelevant here *)
Example tm_id U : term := do
  \U, 0.
Example tm_ω  U : term := do
  \U, 0 0.
Print tm_ω.
Example tm_Ω  U : term := do
  (\U, 0 0) (\U, 0 0).
Print tm_Ω.

(* attempt to create open terms *)
Fail Example ex_tm_var : term := do
  0.
Fail Example ex_tm_abs : term := do
  \ty_unit, 1.

(* Lemma tm_var_is_not_closed : forall (t : term) V,
  t = tm_var V ->
  False.
Proof. intros. assumption. Qed. *)


(* Substitution *)
Fixpoint lift {V} (e : tm V) : tm ^V :=
  match e with
  | tm_var v => tm_var (Some v)
  | tm_app e1 e2 => tm_app (lift e1) (lift e2)
  | tm_abs A e => tm_abs A (lift e)
  end.

Fixpoint tm_subst {V} (e : tm ^V) (e' : tm V) : tm V :=
  match e with
  | tm_var v' =>
      match v' with
      | None => e'
      | Some v => tm_var v
      end
  | tm_app e1 e2 => tm_app (tm_subst e1 e') (tm_subst e2 e')
  | tm_abs A e => tm_abs A (tm_subst e (lift e'))
  end.


(* Evaluation *)
Reserved Notation "t1 '-->' t2" (at level 40).
Inductive step {V} : tm V -> tm V -> Prop :=
| ST_Redex : forall A e e',
    do (\A, e) e' --> tm_subst e e'
| ST_App1 : forall e1 e2 e,
    e1 --> e2 ->
    do e1 e --> do e2 e
| ST_App2 : forall e1 e2 e,
    e1 --> e2 ->
    do e e1 --> do e e2
where "t1 '-->' t2" := (step t1 t2).
Hint Constructors step : core.
(* Notation multistep := (multi step). *)
(* Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40). *)

Lemma redex : forall V (E : tm V) e e' A,
  E = tm_subst e e' ->
  do (\A, e) e' --> E.
Proof.
  intros. subst. apply ST_Redex.
  Qed.

Lemma tm_ω_value : forall t, ~ exists e, tm_ω t --> e.
Proof. unfold tm_ω. intros t [e H]. inversion H. Qed.

Lemma tm_Ω_reduces_to_itself : forall t, tm_Ω t --> tm_Ω t.
Proof. intros. unfold tm_Ω. apply redex. reflexivity. Qed.


(* Typing relation *)

Definition ctx V := V -> ty.
Definition emp : ctx Void := fun no => match no with end.

Definition ctx_cons {V : Type} (Gamma : ctx V) (t : ty) : ctx ^V :=
  fun V' =>
    match V' with
    | None => t
    | Some V => Gamma V
    end.
Notation "Gamma , t" := (ctx_cons Gamma t) (at level 100, t custom stlc at level 0).

Reserved Notation "Gamma '|-' t ':' T"
  (at level 101, t custom stlc, T custom stlc at level 0).
Inductive has_type : forall {V}, ctx V -> tm V -> ty -> Prop :=
| T_Var : forall {V} Gamma (x : V) t,
    Gamma x = t ->
    Gamma |- var x : t
| T_Abs : forall {V} Gamma A B (e : tm ^V),
    Gamma, A |- e : B ->
    Gamma |- \A, e : (A -> B)
| T_App : forall {V} (Gamma : ctx V) B A e1 e2,
    Gamma |- e1 : (A -> B) ->
    Gamma |- e2 : A ->
    Gamma |- e1 e2 : B
where "Gamma '|-' t ':' T" := (has_type Gamma t T).
Hint Constructors has_type : core.

Lemma tm_id_typeable : forall (t:ty),
  emp |- {tm_id t} : (t -> t).
Proof. unfold tm_id; auto. Qed.

Require Import Coq.Program.Equality.

Ltac inv H := dependent destruction H.

Lemma typing_deterministic : forall V (Gamma : ctx V) e t1 t2,
  Gamma |- e : t1 ->
  Gamma |- e : t2 ->
  t1 = t2.
Proof.
  intros V Gamma e.
  dependent induction e; intros.
  - inv H. inv H0. reflexivity.
  - inv H. inv H1.
    assert (do (A -> B) = do (A0 -> B0)). eapply IHe1; eassumption.
    injection H1; auto.
  - inv H. inv H0.
    f_equal. eapply IHe; eassumption.
Qed.

Lemma ty_not_equi_recursive : forall A B, A = ty_arr A B -> False.
Proof.
  induction A; intros.
  - discriminate H.
  - injection H; intros; subst.
    eapply IHA1. eassumption.
  Qed.

Lemma tm_ω_not_typeable : forall (t:ty),
  ~ exists T, emp |- {tm_ω t} : T.
Proof.
  unfold tm_ω.
  intros t [T H].
  dependent destruction H.
  dependent destruction H.
  assert (A = ty_arr A B) by (eapply typing_deterministic; eassumption).
  apply ty_not_equi_recursive in H1. contradiction.
  Qed.

