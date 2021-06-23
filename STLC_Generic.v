(* Formalization of the Simply Typed Lambda Calculus using nested datatypes *)

(* Goal: Progress and Preservation *)

Require Export Terms.
Require Export Coq.Program.Equality.

Ltac inv H := dependent destruction H.

(* Evaluation *)

Reserved Notation "e1 '-->' e2" (at level 40).
Inductive step : term -> term -> Prop :=
| step_redex : forall e e',
    <{ (λ e) e' }> --> <{ e [0 := e'] }>
| step_app1 : forall e1 e2 e,
    e1 --> e2 ->
    <{ e1 e }> --> <{ e2 e }>
| step_app2 : forall e1 e2 v,
    whnf v ->
    e1 --> e2 ->
    <{ v e1 }> --> <{ v e2 }>
where "e1 '-->' e2" := (step e1 e2).
Hint Constructors step : core.

Remark tm_ω_value : ~ exists e, tm_ω --> e.
Proof. unfold tm_ω. intros [e H]. inv H. Qed.

Remark tm_Ω_reduces_to_itself : tm_Ω --> tm_Ω.
Proof. intros. unfold tm_Ω. constructor. Qed.


(* Types *)

Inductive ty :=
| ty_unit : ty            (* unit is a type *)
| ty_arr : ty -> ty -> ty (* A -> B is a type when A and B are types *)
.
Hint Constructors ty : core.

Notation "A -> B" := (ty_arr A B) (in custom term_scope at level 50, right associativity).


(* Context *)
(*
  For the typing relation we need a context Γ that remembers a type for each
  free variable.

  For the nested-datatypes format it's convenient to represent the context as
  a function of type [V -> ty] so a mapping from free variable to its type.

  So the empty context [·] is of type [Void -> ty]
    with the only reasonable implementation
 *)

Definition ctx V := V -> ty.

Definition emp : ctx Void := fun no => match no with end.
Notation "·" := emp.

Definition ctx_cons {V : Type} (A : ty) (Γ : ctx V) : ctx ^V :=
  fun V' =>
    match V' with
    | None => A
    | Some V => Γ V
    end.
Notation "Γ , A" := (ctx_cons A Γ) (at level 100, A custom term_scope at level 0).


(* Typing relation *)

Reserved Notation "Γ '|-' A ':' T"
  (at level 101, A custom term_scope, T custom term_scope at level 0).
Inductive has_type : forall {V}, ctx V -> tm V -> ty -> Prop :=
| var_has_type : forall {V} Γ (x : V) A,
    Γ x = A ->
    Γ |- var x : A
| abs_has_type : forall {V} Γ A B (e : tm ^V),
    Γ, A |- e : B ->
    Γ |- λ e : (A -> B)
| app_has_type : forall {V} (Γ : ctx V) B A e1 e2,
    Γ |- e1 : (A -> B) ->
    Γ |- e2 : A ->
    Γ |- e1 e2 : B
where "Γ '|-' A ':' T" := (has_type Γ A T).
Hint Constructors has_type : core.

Remark tm_id_typeable : forall (A:ty),
  · |- tm_id : (A -> A).
Proof. unfold tm_id; auto. Qed.

Remark ty_not_equi_recursive : forall A B,
  A = ty_arr A B ->
  False.
Proof.
  induction A; intros.
  - discriminate H.
  - injection H; intros; subst.
    eapply IHA1. eassumption.
Qed.

Remark tm_ω_not_typeable :
  ~ exists T, · |- tm_ω : T.
Proof.
  unfold tm_ω.
  intros [T H].
  dependent destruction H.
  dependent destruction H.
  fold · in *.
  assert (A = ty_arr A B) by (inv H; inv H0; assumption).
  eapply ty_not_equi_recursive. eassumption.
Qed.


(* Typing is not deterministic for Curry-style terms *)

Definition typing_deterministic := forall V (Γ : ctx V) e t1 t2,
  Γ |- e : t1 ->
  Γ |- e : t2 ->
  t1 = t2.

Lemma typing_is_not_deterministic : ~ typing_deterministic.
Proof.
  unfold typing_deterministic; intro H.
  set (T1 := <{ ty_unit -> ty_unit }>).
  set (T2 := <{ T1 -> T1 }>).
  assert (H1: · |- tm_id : T1) by apply tm_id_typeable.
  assert (H2: · |- tm_id : T2) by apply tm_id_typeable.
  cut (T1 = T2). intro H0; discriminate H0.
  eapply H; eauto.
Qed.

Lemma val_arr_inversion : forall v A B,
  whnf v ->
  · |- v : (A -> B) ->
  exists e', v = <{ λ e' }>.
Proof.
  intros.
  inv H0; try inv H.
  exists e. reflexivity.
Qed.

(* Progress *)
(* Our first main theorem: Progress - well-typed terms never get 'stuck'
  if the term [e] type-checks then it's either a value or it makes a step
 *)
Theorem progress : forall e A,
  · |- e : A ->
  whnf e \/ exists e', e --> e'.
Proof with try solve [right; eexists; constructor; eauto | left; constructor].
  intros e A H.
  dependent induction H; fold · in *... (* lambda case solved already: value *)
  - contradiction. (* variable case is impossible as the terms are closed *)
  - assert (whnf e1 \/ (exists e', e1 --> e')) by auto; clear IHhas_type1.
    assert (whnf e2 \/ (exists e', e2 --> e')) by auto; clear IHhas_type2.
    destruct H1 as [H1 | [e' H1]]...
    destruct H2 as [H2 | [e' H2]]...
    apply (val_arr_inversion _ A B) in H1 as [e' H1]; auto.
    subst... (* we have a redex *)
Qed.


(* Weakening *)
(* The second theorem we want to prove is called Preservation,
  but before we can formalize it we need:
  - Weakening lemma
  - Substitution lemma
 *)

Lemma compose_cons : forall V W Γ (f:V->W) A,
  Γ ∘ f, A = (Γ, A) ∘ option_map f.
Proof. intros; apply functional_extensionality; destruct x; auto. Qed.

Theorem weakening : forall V e W (f:V->W) Γ A,
  Γ ∘ f |- e : A ->
  Γ |- {f <$> e} : A.
Proof.
  induction e; intros; inv H; cbn; auto.
  - econstructor; eauto.
  - constructor. apply IHe.
    rewrite <- compose_cons. assumption.
Qed.

Notation "↑ e" := (Some <$> e) (at level 70).
Notation "Γ \ 0" := (fun v => Γ (Some v)) (at level 5).

Theorem Weakening : forall V e (Γ : ctx ^V) A,
  Γ \ 0 |-    e  : A ->
  Γ     |- {↑ e} : A.
Proof.
  intros. apply weakening in H. assumption.
  Qed.

Lemma substitution_lemma : forall V e W (f:ctx W->ctx V) (fsub:V->tm W) Γ A,
  (forall v, Γ |- {fsub v} : {f Γ v}) ->
  f Γ |- e : A ->
  Γ |- {e >>= fsub} : A.
Proof.
  induction e; intros W f fsub Γ A Hv He; inv He; cbn; auto; econstructor; eauto.
  apply IHe with (f := fun _ => f Γ, A); auto.
  intros [v|]; cbn; auto.
  apply weakening.
  assert (HΓ: (Γ, A) ∘ Some = Γ) by (apply functional_extensionality; auto).
  rewrite HΓ. apply Hv.
Qed.

Lemma Substitution_lemma : forall V e (e':tm V) Γ A B,
  Γ, B |- e : A ->
  Γ |- e' : B ->
  Γ |- e [0 := e'] : A.
Proof.
  intros V e e' Γ A B He He'.
  apply (substitution_lemma ^V e V (ctx_cons B) (sub e') Γ A); auto.
  intros [v|]; cbn; auto.
Qed.


(* Preservation *)

Theorem preservation : forall e e',
  e --> e' -> forall A,
  · |- e  : A ->
  · |- e' : A.
Proof.
  intros e e' Hstep.
  induction Hstep; intros A He; inv He; fold · in *.
  - inv He1. fold · in *.
    eapply Substitution_lemma; eauto.
  - apply IHHstep in He1.
    econstructor; eauto.
  - apply IHHstep in He2.
    econstructor; eauto.
  Qed.


(* Full normalization *)
(*
  Previously we discussed call-by-value evaluation relation [-->] where
  we did not evaluate terms under binders (here: just lambdas).

  It is worth seeing that the definitions we've seen so far are general enough
  to prove stronger versions of Progress and Preservation
  that are not restriced to closed terms.

  We aim to define the full normalization relation [-->n] and since the relation
  is different, so are the values.

  [nf e] says that the term [e] of type [tm V] (so it can have free variables)
  is a value. Values can take one of two forms:
    - [x e1 .. en] is a value when [x] is a variable and [e1] .. [en] are values
    - [λ e] is a value when [e] is a value
 *)
Inductive nf : forall {V}, tm V -> Prop :=
| nval_var : forall V (v : V),
    nf <{ var v }>
| nval_app_var : forall V e (v : V),
    nf e ->
    nf <{ (var v) e }>
| nval_app : forall V (e1 e2 e : tm V),
    nf <{ e1 e2 }> ->
    nf e ->
    nf <{ e1 e2 e }>
| nval_abs : forall V (e : tm ^V),
    nf e ->
    nf <{ λ e }>
.
Hint Constructors nf : core.

Reserved Notation "t1 '-->n' t2" (at level 40).
Inductive norm : forall {V}, tm V -> tm V -> Prop :=
| norm_redex : forall V e (e' : tm V),
    <{ (λ e) e' }> -->n <{ e [0 := e'] }>
| norm_app1 : forall V (e1 e2 e : tm V),
    e1 -->n e2 ->
    <{ e1 e }> -->n <{ e2 e }>
| norm_app2 : forall V (e1 e2 v : tm V),
    nf v ->
    e1 -->n e2 ->
    <{ v e1 }> -->n <{ v e2 }>
| norm_abs : forall V (e1 e2 : tm ^V),
    e1 -->n e2 ->
    <{ λ e1 }> -->n <{ λ e2 }>
where "t1 '-->n' t2" := (norm t1 t2).
Hint Constructors norm : core.


Lemma nval_no_steps : forall V (e : tm V),
  nf e ->
  ~ exists e', e -->n e'.
Proof with eauto.
  intros V e Hval [e' H].
  induction Hval; inv H...
  inv H...
  Qed.

Theorem open_preservation : forall V (e e' : tm V),
  e -->n e' -> forall Γ A,
  Γ |- e  : A ->
  Γ |- e' : A.
Proof.
  intros V e e' Hstep.
  induction Hstep; intros Γ t0 He; inv He; try (econstructor; eauto).
  - inv He1.
    eapply Substitution_lemma; eauto.
  Qed.

Theorem open_progress : forall V Γ (e : tm V) A,
  Γ |- e : A ->
  nf e \/ exists e', e -->n e'.
Proof with try solve [right; eexists; eauto | left; auto].
  intros V Γ e A H.
  dependent induction H...
  - destruct IHhas_type  as [H0 | [e' H0]]...
  - destruct IHhas_type1 as [H1 | [e' H1]]... (* e1 makes a step *)
    destruct IHhas_type2 as [H2 | [e' H2]]... (* e2 makes a step *)
    destruct H1... (* either an app value [x e1 .. en] or redex *)
Qed.
