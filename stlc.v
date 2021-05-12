(* Formalization of the Simply Typed Lambda Calculus using nested datatypes *)

(* Goal: Progress and Preservation *)

Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.

Ltac inv H := dependent destruction H.

Notation "^ f" := (option_map f) (at level 5, right associativity) : function_scope.
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
Notation "<{ e }>" := e (at level 100, e custom stlc at level 99).
Notation "'do' e" := e (at level 100, e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "{ x }" := x (in custom stlc at level 0, x constr).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "0" := (tm_var None) (in custom stlc at level 0).
Notation "1" := (tm_var (Some None)) (in custom stlc at level 0).
Notation "2" := (tm_var (Some (Some None))) (in custom stlc at level 0).
Notation "3" := (tm_var (Some (Some (Some None)))) (in custom stlc at level 0).
Notation "4" := (tm_var (Some (Some (Some (Some None))))) (in custom stlc at level 0).
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


(* Closed terms *)

Inductive Void : Type := .
Definition term := tm Void.

(* Several examples, the type `U` is irrelevant here *)
Example tm_id U : term := do
  \U, 0. (* \x: U, x *)
Example tm_ω  U : term := do
  \U, 0 0. (* \x: U, x x *)
Example tm_Ω  U : term := do
  (\U, 0 0) (\U, 0 0).

(* Attempt to create open terms *)
Fail Example ex_tm_var : term := do
  0.
Fail Example ex_tm_abs : term := do
  \ty_unit, 1.


(* Value *)

Inductive val : term -> Prop :=
| val_abs : forall e t, val (do \t, e)
.

(* source: https://github.com/pi8027/lambda-calculus/blob/master/coq/LN/Untyped.v *)
Require Import Coq.funind.Recdef.
Notation nopts n T := (iter _ n option T).

Notation tm' n V := (tm (nopts n V)).
Notation term' n := (tm' n Void).

Definition ctx V := V -> ty.
Notation ctx' n V := (ctx (nopts n V)).
Definition emp : ctx Void := fun no => match no with end.

Definition ctx_cons {V : Type} (Gamma : ctx V) (t : ty) : ctx ^V :=
  fun V' =>
    match V' with
    | None => t
    | Some V => Gamma V
    end.
Notation "Gamma , t" := (ctx_cons Gamma t) (at level 100, t custom stlc at level 0).


(* Lift *)
(* http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.447.5355&rep=rep1&type=pdf *)

(* apply [Some] [n]-times *)
Fixpoint lift_var_n {V : Type} (n : nat) : V -> nopts n V :=
  match n with
  | 0 => fun v => v
  | S n => fun v => Some (lift_var_n n v)
  end.

(* leave variables less than [k] untouched and remaining ones increase by [n] *)
Fixpoint prelift_var {V : Type} { m : nat }
  (n k : nat) (v : nopts k (nopts m V)) {struct k} : nopts k (nopts n (nopts m V)).
destruct k.
- exact (lift_var_n n v).
- destruct v.
  + exact (Some (prelift_var _ _ _ _ i)).
  + exact None.
Defined.

Fixpoint prelift {V : Type}
  (m n k : nat) (t : tm' k (nopts m V)) {struct t} : tm' k (nopts n (nopts m V)) :=
  match t with
  | do var v => do var {prelift_var n k v}
  | do e1 e2 => do {prelift m n k e1} {prelift m n k e2}
  | do \t, e => do \t, {prelift m n (S k) e}
  end.

Example prelift_ex1 : forall {V : Type},
@prelift V 2 2 1 (do 0 1 2) = (do 0 3 4).
Proof. reflexivity. Qed.

Example prelift_ex2 : forall {V : Type} t,
@prelift V 2 2 1 (do 0 (\t, 0 1 2)) = (do 0 (\t, 0 1 4)).
Proof. reflexivity. Qed.

Notation lift e := (prelift 0 1 0 e).


(* Substitution *)

Fixpoint tm_subst_var
  {V : Type} (n : nat) (e : tm V) : nopts (S n) V -> tm' n V :=
  match n with
  | 0 => fun (v : ^V) =>
      match v with
      | None => e
      | Some v => tm_var v
      end
  | S n => fun v =>
      match v with
      | None => tm_var None
      | Some v => lift (tm_subst_var n e v)
      end
  end.

Fixpoint tm_subst_n
  {V : Type} (n : nat) (e : tm' (S n) V) (e' : tm V) : tm' n V :=
  match e with
  | do var v => tm_subst_var n e' v
  | do e1 e2 => do {tm_subst_n n e1 e'} {tm_subst_n n e2 e'}
  | do \t, e => do \t, {tm_subst_n (S n) e e'}
  end.

Definition tm_subst {V} (e : tm ^V) (e' : tm V) : tm V :=
  tm_subst_n 0 e e'.

Example subst_ex_1 : forall ty,
  tm_subst (do 0 0) (tm_ω ty) = tm_Ω ty.
Proof. reflexivity. Qed.

Example subst_ex_2 : forall ty (e : term),
  tm_subst (do \ty, 1 0) e = (do \ty, {lift e} 0).
Proof. intros. cbn. reflexivity. Qed.

Example subst_ex_3 : forall ty,
  tm_subst (do 1 0) (lift (tm_id ty)) = do 0 {lift (tm_id ty)}.
Proof. intros. cbn. reflexivity. Qed.

Example subst_ex_4 : forall ty,
  tm_subst_n 1 (do 1 0) (tm_id ty) = do {lift (tm_id ty)} 0.
Proof. intros. cbn. reflexivity. Qed.


(* Evaluation *)

(* CBV, could be CBN or undeterministic *)
(* no evaluation under a lambda - significantly easier:
   we substitute closed terms only!  *)

Reserved Notation "t1 '-->' t2" (at level 40).
Inductive step : term -> term -> Prop :=
| step_redex : forall A e e',
    do (\A, e) e' --> tm_subst e e'
| step_app1 : forall e1 e2 e,
    e1 --> e2 ->
    do e1 e --> do e2 e
| step_app2 : forall e1 e2 v,
    val v ->
    e1 --> e2 ->
    do v e1 --> do v e2
where "t1 '-->' t2" := (step t1 t2).
Hint Constructors step : core.

Lemma redex : forall E e e' A,
  E = tm_subst e e' ->
  do (\A, e) e' --> E.
Proof.
  intros. subst. apply step_redex.
  Qed.

Lemma tm_ω_value : forall t, ~ exists e, tm_ω t --> e.
Proof. unfold tm_ω. intros t [e H]. inv H. Qed.

Lemma tm_Ω_reduces_to_itself : forall t, tm_Ω t --> tm_Ω t.
Proof. intros. unfold tm_Ω. apply redex. reflexivity. Qed.


(* Typing relation *)

Reserved Notation "Gamma '|-' t ':' T"
  (at level 101, t custom stlc, T custom stlc at level 0).
Inductive has_type : forall {V}, ctx V -> tm V -> ty -> Prop :=
| var_has_type : forall {V} Gamma (x : V) t,
    Gamma x = t ->
    Gamma |- var x : t
| abs_has_type : forall {V} Gamma A B (e : tm ^V),
    Gamma, A |- e : B ->
    Gamma |- \A, e : (A -> B)
| app_has_type : forall {V} (Gamma : ctx V) B A e1 e2,
    Gamma |- e1 : (A -> B) ->
    Gamma |- e2 : A ->
    Gamma |- e1 e2 : B
where "Gamma '|-' t ':' T" := (has_type Gamma t T).
Hint Constructors has_type : core.

Lemma tm_id_typeable : forall (t:ty),
  emp |- {tm_id t} : (t -> t).
Proof. unfold tm_id; auto. Qed.

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

Lemma val_no_steps : forall (e : term),
  val e ->
  ~ exists e', e --> e'.
Proof.
  intros e Hval [e' H].
  destruct Hval.
  inversion H.
  Qed.

Lemma val_arr : forall v A B,
  val v ->
  emp |- v : (A -> B) ->
  exists e', v = do \A, e'.
Proof.
  intros.
  inv H0; try inv H.
  exists e. reflexivity.
  Qed.

Theorem progress : forall e t,
  emp |- e : t ->
  val e \/ exists e', e --> e'.
Proof.
  intros e t H.
  dependent induction H.
  - contradiction.
  - left. constructor.
  - assert (val e1 \/ (exists e', e1 --> e')) by auto. clear IHhas_type1.
    assert (val e2 \/ (exists e', e2 --> e')) by auto. clear IHhas_type2.
    destruct H1.
    + destruct H2.
      * apply (val_arr _ A B) in H1 as [e' H1]; try assumption. subst.
        right. eexists. econstructor.
      * destruct H2; right; eexists; apply step_app2; eauto.
    + destruct H1; right; eexists; apply step_app1; eauto.
Qed.



(* solve app case by simple inductive reasoning *)
Ltac appauto IHe1 IHe2 :=
  econstructor;
  [ eapply IHe1; eauto
  | eapply IHe2; eauto
  ].

(* Weakening *)

Fixpoint drop {V : Type} (n : nat) : ctx' n V -> ctx V :=
  match n with
  | 0 => fun (ctx : ctx V) => ctx
  | S n => fun (ctx : ctx' (S n) V) => drop n (fun v => ctx (Some v))
  end.

Fixpoint predrop {V : Type}
  (m n k : nat) (ctx : ctx' k (nopts n (nopts m V))) {struct k} : ctx' k (nopts m V).
destruct k; cbn in *.
- exact (drop n ctx).
- intro v. destruct v.
  + set (ctx_up := fun v => ctx (Some v)). apply predrop in ctx_up.
    exact (ctx_up i).
  + exact (ctx None). 
Defined.

Lemma preweakening_var : forall V m k n Gamma t v,
  @predrop V m n k Gamma |- var v : t ->
  Gamma |- var {prelift_var n k v} : t.
Proof with cbn in *.
  intros. subst...
  induction k...
  + induction n; auto...
    constructor.
    apply IHn in H.
    inv H. reflexivity.
  + destruct v.
    - constructor.
      set (G := fun v => Gamma (Some v)).
      specialize IHk with (Gamma := G) (v := i).
      cut (G |- var {prelift_var n k i} : t).
      * intros H0. inv H0. reflexivity.
      * apply IHk. clear IHk. subst G.
        inv H. auto.
    - inv H. auto.
  Qed.

Lemma predrop_cons : forall V m n k Gamma t e B,
  @predrop V m n    k   Gamma, t  |- e : B ->
  @predrop V m n (S k) (Gamma, t) |- e : B.
Proof.
  intros.
  dependent induction H; auto.
  appauto IHhas_type1 IHhas_type2.
  Qed.

Lemma preweakening : forall V m k e n Gamma t,
  @predrop V m n k Gamma |- e : t ->
  Gamma |- {prelift m n k e} : t.
Proof with cbn in *.
  dependent induction e; intros; inv H...
  - apply preweakening_var. auto.
  - appauto IHe1 IHe2.
  - constructor.
    apply predrop_cons in H.
    apply IHe in H; auto.
  Qed.

Lemma weakening : forall V e Gamma t,
  @predrop V 0 1 0 Gamma |- e : t ->
  Gamma |- {lift e} : t.
Proof with cbn in *.
  intros.
  apply preweakening. auto.
  Qed.

(* Substitution Lemma *)

Fixpoint ctx_rm
  {V : Type} (n : nat) : ctx' (S n) V -> ctx' n V :=
  match n with
  | 0   => fun (ctx : ctx         ^V) (v :             V) => ctx (Some v)
  | S n => fun (ctx : ctx' (2 + n) V) (v : nopts (S n) V) =>
      match v with
      | None => ctx None
      | Some v => ctx_rm _ (fun v => ctx (Some v)) v
      end
  end.

Fixpoint ctx_skip
  {V : Type} (n : nat) : ctx' n V -> ctx V :=
  match n with
  | 0   => fun G => G
  | S n => fun G => ctx_skip n (fun v => G (Some v))
  end.

Fixpoint ctx_nth
  {V : Type} (n : nat) : ctx' (S n) V -> ty :=
  match n with
  | 0   => fun (ctx : ctx         ^V) => ctx None
  | S n => fun (ctx : ctx' (2 + n) V) => ctx_nth n (fun v => ctx (Some v))
  end.

Example rm_0 : forall V (Gamma : ctx V) A,
  ctx_rm 0 (Gamma, A) = Gamma.
Proof. reflexivity. Qed.

Example rm_1 : forall V (Gamma : ctx V) A B,
  ctx_rm 1 (Gamma, A, B) = (Gamma, B).
Proof. reflexivity. Qed.


Lemma substitution_lemma : forall V n e Gamma e' t,
  Gamma |- e : t ->
  ctx_skip (S n) Gamma |- e' : {ctx_nth n Gamma} ->
  ctx_rm n Gamma |- {@tm_subst_n V n e e'} : t.
Proof with cbn in *.
  intros. dependent induction e...
  - inv H.
    induction n... 
    + destruct v; auto.
    + destruct v.
      * apply weakening. cbn.
        apply IHn. assumption.
      * constructor. reflexivity.
  - inv H. appauto IHe1 IHe2.
  - inv H. constructor.
    cut (ctx_rm (S n) (Gamma, t) |- {tm_subst_n (S n) e e'} : B).
    + intro... inv H1; rewrite <- x; auto. appauto H1_ H1_0.
    + apply IHe; auto.
  Qed.


(* Preservation *)

Theorem preservation : forall e e',
  e --> e' -> forall t,
  emp |- e : t ->
  emp |- e' : t.
Proof.
  intros e e' Hstep.
  induction Hstep; intros t He; inv He; fold emp in *.
  - inv He1. fold emp in *.
    unfold tm_subst.
    set (H := substitution_lemma Void 0 e (emp, A0) e' B).
    apply H in He1; auto.
  - apply IHHstep in He1.
    econstructor; eauto.
  - apply IHHstep in He2.
    econstructor; eauto.
  Qed.


(* Full normalization *)

(* Inductive val' : forall {V}, tm V -> Prop :=
| val'_var : forall V v, @val' V (do var v)
| val'_app : forall V v e,
  foldr
| val'_abs : forall V e t,
    val' e ->
    @val' V (do \t, e)
.
Hint Constructors val' : core. *)

Reserved Notation "t1 '-->n' t2" (at level 40).
Inductive norm : forall {V}, tm V -> tm V -> Prop :=
| norm_redex : forall V A e e',
    do (\A, e) e' -->n @tm_subst V e e'
| norm_app1 : forall V (e1 e2 e : tm V),
    e1 -->n e2 ->
    do e1 e -->n do e2 e
| norm_app2 : forall V (e1 e2 e : tm V),
    e1 -->n e2 ->
    do e e1 -->n do e e2
| norm_abs : forall V t (e1 e2 : tm ^V),
    e1 -->n e2 ->
    do \t, e1 -->n do \t, e2
where "t1 '-->n' t2" := (norm t1 t2).
Hint Constructors norm : core.

(* For this we need to alter normalization relation -
   for now only closed terms can reduce *)
Theorem open_preservation : forall V (e e' : tm V),
  e -->n e' -> forall Gamma t,
  Gamma |- e : t ->
  Gamma |- e' : t.
Proof.
  intros V e e' Hstep.
  induction Hstep; intros Gamma t0 He; inv He; try (econstructor; eauto).
  - inv He1.
    unfold tm_subst.
    set (H := substitution_lemma _ 0 e (Gamma, A0) e' B).
    apply H in He1; auto.
  Qed.
