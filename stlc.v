
Require Import Coq.Program.Equality.
Require Import Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.

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


(* Value *)

Inductive val : term -> Prop :=
| val_abs : forall e t, val (do \t, e)
.

(* source: https://github.com/pi8027/lambda-calculus/blob/master/coq/LN/Untyped.v *)
Require Import Coq.funind.Recdef.
(* Set Implicit Arguments. *)
Notation nopts n T := (iter _ n option T).

Notation tm' n V := (tm (nopts n V)).
Notation term' n := (tm' n Void).

Fixpoint tmap {V1 V2 : Type} (f : V1 -> V2) (e : tm V1) : tm V2 :=
  match e with
  | tm_var x => tm_var (f x)
  | tm_app e1 e2 => tm_app (tmap f e1) (tmap f e2)
  | tm_abs ty e => tm_abs ty (tmap ^f e)
  end.

Definition lift {V} (e : tm V) : tm ^V := tmap Some e.

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

(* Substitution *)

(* Fixpoint lift {V} (e : tm V) : tm ^V :=
  match e with
  | tm_var v => tm_var (Some v)
  | tm_app e1 e2 => tm_app (lift e1) (lift e2)
  | tm_abs A e => tm_abs A (lift e)
  end. *)
Definition tm_subst {V} (e : tm ^V) (e' : tm V) : tm V :=
  tm_subst_n 0 e e'.

(* Fixpoint tm_subst {V} (e : tm ^V) (e' : tm V) : tm V :=
  match e with
  | tm_var v' =>
      match v' with
      | None => e'
      | Some v => tm_var v
      end
  | tm_app e1 e2 => tm_app (tm_subst e1 e') (tm_subst e2 e')
  | tm_abs A e => tm_abs A (tm_subst e (lift e'))
  end. *)

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
(* Notation multistep := (multi step). *)
(* Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40). *)

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


(* Preservation *)

Notation ctx' n V := (ctx (nopts n V)).

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

Fixpoint ctx_nth
  {V : Type} (n : nat) : ctx' (S n) V -> ty :=
  match n with
  | 0   => fun (ctx : ctx         ^V) => ctx None
  | S n => fun (ctx : ctx' (2 + n) V) => ctx_nth n (fun v => ctx (Some v))
  end.

Require Import Coq.Logic.FunctionalExtensionality.

Lemma ctx_decomposition : forall V (Gamma : ctx ^V),
  Gamma = (ctx_rm 0 Gamma, {ctx_nth 0 Gamma}).
Proof.
  intros. apply functional_extensionality; intros. destruct x; reflexivity.
  Qed.

Example rm_0 : forall V (Gamma : ctx V) A,
  ctx_rm 0 (Gamma, A) = Gamma.
Proof. reflexivity. Qed.

Example rm_1 : forall V (Gamma : ctx V) A B,
  ctx_rm 1 (Gamma, A, B) = (Gamma, B).
Proof. reflexivity. Qed.

Fixpoint drop {V : Type} (n : nat) : ctx' n V -> ctx V :=
  match n with
  | 0 => fun (ctx : ctx V) => ctx
  | S n => fun (ctx : ctx' (S n) V) => drop n (fun v => ctx (Some v))
  end.

Fixpoint lift_n {V : Type} (n : nat) : tm V -> tm' n V :=
  match n with
  | 0 => fun e => e
  | S n => fun e => lift (lift_n n e)
  end.

Fixpoint lift_var_n {V : Type} (n : nat) : V -> nopts n V :=
  match n with
  | 0 => fun v => v
  | S n => fun v => Some (lift_var_n n v)
  end.

(* http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.447.5355&rep=rep1&type=pdf *)
(* leave variables less than [k] untouched and remaining ones increase by [n] *)
Fixpoint prelift_var {V : Type} { m : nat }
  (n k : nat) (v : nopts k (nopts m V)) {struct k} : nopts k (nopts n (nopts m V)).
destruct k.
- exact (lift_var_n n v).
- destruct v.
  + exact (Some (prelift_var _ _ _ _ i)).
  + exact None.
Defined.

(* Fixpoint prelift_var {V : Type} { m : nat }
  (n k : nat) (v : nopts (k + m) V) {struct k} : nopts (n + (k + m)) V.
destruct k; cbn in *.
- apply (lift_var_n n) in v.
  induction n; cbn in *.
  + apply v.
  + destruct v.
    apply IHn in i. apply Some. apply i.
    apply None.
-  cut ((n + S (k + m)) = S (n + (k + m))); intros; try lia; rewrite H; clear H.
  cbn; destruct v.
  + apply prelift_var with (n := n) in i.
    apply (Some i).
  + apply None.
Defined. *)

Fixpoint prelift {V : Type}
  (m n k : nat) (t : tm' k (nopts m V)) {struct t} : tm' k (nopts n (nopts m V)) :=
  match t with
  | do var v => do var {prelift_var n k v}
  | do e1 e2 => do {prelift m n k e1} {prelift m n k e2}
  | do \t, e => do \t, {prelift m n (S k) e}
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


(* Fixpoint prelift {V : Type} {m : nat}
  (n k : nat) (t : tm' (k + m) V) {struct t} : tm' (n + (k + m)) V.
refine (
  match t with
  | do var v => do var {prelift_var n k v}
  | do e1 e2 => do {prelift _ _ n k e1} {prelift _ _ n k e2}
  | do \t, e => do \t, _ (*{prelift n (S k) e} *)
  end
).
apply (prelift _ _ n (S k)) in e.
cut ((n + (S k + m)) = S (n + (k + m))); intros; try lia; rewrite H in *; clear H.
exact e.
Defined. *)

(* Definition prelift' {V : Type} {m : nat}
  (n k : nat) (t : tm' m V) : tm' (if lt_dec m k then m else n + m) V.
destruct (lt_dec m k).
- exact t.
- assert (k <= m). lia.
  assert (m = (k + (m - k))). lia. rewrite H0 in t.
  apply (prelift n k) in t.
  cut ((n + (k + (m - k))) = n + m); intros; try lia. rewrite H1 in t.
  exact t.
Defined. *)

Example prelift_ex1 : forall {V : Type},
  @prelift V 2 2 1 (do 0 1 2) = (do 0 3 4).
Proof. reflexivity. Qed.

Example prelift_ex2 : forall {V : Type} t,
  @prelift V 2 2 1 (do 0 (\t, 0 1 2)) = (do 0 (\t, 0 1 4)).
Proof. reflexivity. Qed.


(* Example predrop_ex1 : forall {V : Type} t t' ctx,
  ctx = <{ emp, t', t }> -> 
  ctx |- 0 : t ->
  @predrop V m n k ctx |- 0 : t *)


(* Fixpoint prelift_ctx {V : Type} {m : nat}
  (n k : nat) (ctx : ctx' (k + m) V) {struct k} : ctx' (n + (k + m)) V.
destruct k; cbn in *.
- destruct n; cbn in *.
  + exact ctx.
  + intro v. *)

(* Record Tm V := buildT
  { _ctx: ctx V
  ; _term: tm V
  ; _type: ty
  ; _typing: _ctx |- _term : _type
  }.
Notation Tm' n V := (Tm (nopts n V)).

Definition Lift {V : Type} {m : nat} (n k : nat) (M : Tm' (k + m)) :
  { N : Tm' (n + (k + m))
  | _ctx N = liftedEnv n (_ctx M) k /\
    _term N = prelift_aux n (_term M) k /\
    _type N = _type M
  }.

Definition Lift_n {V : Type} (n : nat) (M: Tm V):
  { N: Tm
  | _ctx N = liftedEnv n (_ctx M) k /\
    _term N = prelift_aux n (_term M) k /\
    _type N = _type M
  }. *)

Lemma drop_S : forall V n (Gamma : ctx' n V) A,
  drop (S n) (Gamma, A) = drop n Gamma.
Proof. intros. cbn. reflexivity. Qed.

Lemma ctx_inv : forall V (GammaA : ctx ^V),
  exists Gamma A, GammaA = (Gamma, A).
Proof.
  intros.
  exists (fun v => GammaA (Some v)).
  exists (GammaA None).
  apply functional_extensionality. intros [v|]; reflexivity.
  Qed.

Ltac ctxinv H G A := 
  let e := fresh "e" in
  let Heqe := fresh "Heqe" in
  let Heq := fresh "Heq" in
  remember (ctx_inv _ H) as e eqn:Heqe; clear Heqe; destruct e as [G [A Heq]]; subst.

Ltac appauto IHe1 IHe2 :=
  econstructor;
  [ eapply IHe1; eauto
  | eapply IHe2; eauto
  ].

(* Weakening : var *)

Lemma weakening_var : forall V (e : tm V) Gamma A t v,
  e = tm_var v ->
  Gamma    |-       e  : t ->
  Gamma, A |- {lift e} : t.
Proof. intros. subst. cbn. inv H0. constructor. reflexivity. Qed.

Lemma lift_var : forall V (v : V) n,
  exists v',
  lift_n n (tm_var v) = tm_var v'.
Proof.
  induction n; intros; cbn.
  - eexists; eauto.
  - destruct IHn. eexists. rewrite H. reflexivity.
  Qed.

Lemma weakening_var_n : forall V n (e : tm V) Gamma t v,
  e = tm_var v ->
  drop n Gamma |- e : t ->
  Gamma |- {lift_n n e} : t.
Proof.
  induction n; intros; subst. auto.
  subst. cbn.
  ctxinv Gamma G A. 
  rewrite drop_S in H0. eapply IHn in H0; eauto.
  set (HH := lift_var); edestruct HH; clear HH. rewrite H in *.
  eapply weakening_var; eauto.
  Qed.


(* Weakening *)

Lemma preweakening_var : forall V m k e n Gamma t v,
  e = tm_var v ->
  @predrop V m n k Gamma |- e : t ->
  Gamma |- {prelift m n k e} : t.
Proof with cbn in *.
  intros. subst...

Lemma preweakening : forall V m k e n Gamma t,
  @predrop V m n k Gamma |- e : t ->
  Gamma |- {prelift m n k e} : t.
Proof with cbn in *.
  dependent induction e; intros; inv H...
  admit.
  appauto IHe1 IHe2.
  constructor.
  assert (predrop m n (S k) (Gamma, t) |- e : B). admit.
  apply IHe in H0; auto.
Admitted.

Definition simple_cast {T1 T2 : Type} (H : T1 = T2) (x : T1) : T2 :=
  eq_rect T1 (fun T3 : Type => T3) x T2 H.

(* Fixpoint coerce :
  JMeq *)


Lemma weakening_n : forall V n (e : tm V) Gamma t,
  drop n Gamma |- e : t ->
  Gamma |- {lift_n n e} : t.
Proof with cbn in *.
  induction e; intros; inv H.
  - eapply weakening_var_n; eauto.
  - assert (lift_n n (do e1 e2) = do {lift_n n e1} {lift_n n e2}). admit.
    rewrite H1.
    appauto IHe1 IHe2.
  - 
    (* remember (lift_n n e).
    assert ((iter Type n option (option V)) = option (iter Type n option V)). admit.
    rewrite H0 in t0. *)
    (* assert ((lift_n n (do \t, e)) = do \t, {lift_n n e}). *)
  
    induction n. cbn in *; auto.

    assert (iter Type (S n) option V = option (iter Type n option V)). admit.
    (* cbn in Gamma. *)
    replace (iter Type (S n) option V) with (option (iter Type n option V)).

    cbn in *.
    assert (tm' n ^V = tm ^ (nopts n V)). admit.
    assert (lift (lift_n n (do \ t, e)) ~= lift_n n (lift (do \ t, e))). admit.
    subst H1.
    remember (simple_cast H0 (lift_n n (lift (do \ t, e)))) as lam.
    unfold simple_cast in Heqlam.
    apply (simple_cast H0) in Heqlam.
    
    (* rewrite <- H0 in *. *)
    remember (lift_n n (lift (do \ t, e))). dependent rewrite -> H0 in t0. subst.
    dependent rewrite -> H1. JMeq
  
      induction n; cbn in *.
    + appauto H H0.
    + cbn.

  - intros. cbn in Gamma.
    remember (ctx_inv _ Gamma); clear Heqe0; destruct e0 as [G [A Heq]]; subst.
    apply IHn in H...
    rewrite drop_S in H. apply IHn in H.

  induction n, e; auto; intros.
  - inv H...
  - intros... auto.
  - intros... 
  Qed.

Lemma remove_lift : forall V (e : tm V) Gamma A t,
  Gamma, A |- {lift e} : t ->
  Gamma    |-       e  : t.
Proof with cbn in *.
  dependent induction e; intros; cbn in *; inv H.
  - auto.
  - econstructor.
    eapply IHe1; eauto.
    eapply IHe2; eauto.
  - inv H.
  
    inv e. cbn in *.
    + constructor.
      destruct v...
      * apply IHe in H. constructor. inv H... reflexivity.
      * inv H. auto.
    + constructor.
      inv H. econstructor. apply IHe.
    + constructor. inv e; 
    apply IHe in H.
  Qed.

Lemma weakening : forall V (e : tm V) Gamma A t,
  Gamma    |-       e  : t ->
  Gamma, A |- {lift e} : t.
Proof with cbn in *.
  dependent induction e; intros; cbn in *; inv H.
  - auto.
  - econstructor.
    eapply IHe1; eauto.
    eapply IHe2; eauto.
  - inv e...
    + constructor. destruct v...
      * inv H... constructor... reflexivity.
      * inv H. auto.
    + 
  
    econstructor.
    eapply IHe in H.
    eapply IHe.
  Qed.

Fixpoint optionn n (X : Type) : Type :=
  match n with
  | 0 => X
  | S n => option (optionn n X)
  end.

Fixpoint liftn n (t : term) : tm (optionn n Void) :=
  match n with
  | 0 => t
  | S n => lift (liftn n t)
  end.

(* Inductive hole : forall {V}, ctx ^V -> ctx V -> ty -> tm V -> term -> Prop :=
| hole_0 : forall A e,
    hole (emp  , A)  emp        A       e  e
| hole_S : forall {V} (Gamma' : ctx V) Gamma A t e e',
    hole  Gamma      Gamma'     A       e  e' ->
    hole (Gamma, t) (Gamma', t) A (lift e) e'
. *)

Inductive hole : forall {V}, ctx ^V -> ctx V -> ty -> nat -> Prop :=
| hole_0 : forall A,
    hole (emp  , A)  emp        A    0
| hole_S : forall {V} (Gamma' : ctx V) Gamma A t n,
    hole  Gamma      Gamma'     A    n ->
    hole (Gamma, t) (Gamma', t) A (S n)
.

Lemma hole_inv : forall V (GammaA : ctx ^V) Gamma A n,
  hole GammaA Gamma A n ->
  exists Gamma' B, GammaA = (Gamma', B).
Proof.
  intros. inv H; eexists; eexists; eauto.
  Qed.

(* Inductive hole : forall {V}, ctx V -> ty -> ctx V -> ty -> tm V -> term -> Prop :=
| hole_0 : forall A e,
    hole emp A  emp        A       e  e
| hole_S : forall {V} (Gamma' : ctx V) Gamma A t e e',
    hole  Gamma      Gamma'     A       e  e' ->
    hole Gamma t (Gamma', t) A (lift e) e'
. *)

Lemma discriminate_ctx : forall V (Gamma1 : ctx V) Gamma2 A1 A2,
  (Gamma1, A1) = (Gamma2, A2) ->
  Gamma1 = Gamma2 /\ A1 = A2.
Proof with (simpl in *; assumption).
  intros.
  split.
  - apply functional_extensionality; intro v.
    eapply equal_f with (x := Some v) in H...
  - eapply equal_f with (x := None) in H...
  Qed.

(* TODO notation for substitution `e [0 := e']` *)

Lemma subst_var_preservation :
  forall n (x : nopts n ^Void) (e' : term) Gamma B,
  Gamma |- var x : B ->
  emp |- e' : {ctx_nth n Gamma} ->
  ctx_rm n Gamma |- { tm_subst_n n (tm_var x) e' } : B.
Proof.
  induction n; intros; cbn in *; inv H; destruct x; cbn in *; auto.
  - admit.
  - eapply IHn in H0 as H1; eauto.
  Qed.

Lemma subst_preservation_clean :
  forall V n (e : tm' n V) (e' : term) E Gamma B,
  V = (^Void)%type ->
  E ~= e ->
  Gamma |- E : B ->
  emp |- e' : {ctx_nth n Gamma} ->
  ctx_rm n Gamma |- { tm_subst_n n E e' } : B.
Proof with simpl in *.
  dependent induction n; dependent induction e; intros; subst...
  - inv H1. destruct v; auto.
    admit.
  - inv H1.
    econstructor.
    eapply IHe1; eauto.
    eapply IHe2; eauto.
  - inv H1.
    econstructor.
    eapply IHe.
Qed.

Lemma subst_preservation_clean :
  forall n (e : tm' n ^Void) (e' : term) Gamma B,
  Gamma |- e : B ->
  emp |- e' : {ctx_nth n Gamma} ->
  ctx_rm n Gamma |- { tm_subst_n n e e' } : B.
Proof with simpl in *.
  induction n; dependent induction e; simpl; intros.
  - destruct v. contradiction.
    inv H...
    admit.
  - inv H.
    econstructor.
    eapply IHe1; eauto.
    eapply IHe2; eauto.
  - inv H.
    econstructor. cbn in *.
    eapply IHe in H0 as H2.
    eapply IHe.
Qed.

Lemma subst_preservation_qux : forall W (e : tm W) V E,
  W = (^V)%type ->
  E ~= e ->
  forall (Gamma1 : ctx V) t B,
  Gamma1, t |- E : B -> forall Gamma e' lifted_e' A,
  hole (Gamma1, t) Gamma A lifted_e' e' ->
  emp |- e' : A ->
  Gamma |- { tm_subst E lifted_e' } : B.
Proof.
  induction e.
  - intros. subst.
    simpl. destruct v.
    + inv H1. simpl in *.
      dependent induction H2. contradiction.
      apply discriminate_ctx in x as [Heq1 Heq2]; subst.
      apply hole_inv in H2 as H22; destruct H22 as [GammaX [C Heq]]; subst.
      destruct v; simpl.
      constructor. simpl. admit.
      admit.
    + inv H1. simpl. dependent induction H2.
      * assert (A = t). admit. subst.
        assumption.
        (* inv H1. simpl. assumption. *)
      * apply discriminate_ctx in x as [Heq1 Heq2]. subst.
        (* inv H1. simpl in *. *)
        assert (Gamma' |- e : t).
        apply hole_inv in H2 as H22; destruct H22 as [GammaX [C Heq]]; subst.
        apply IHhole with (GammaX); auto.
        admit.
        admit.
  - intros; subst; simpl.
    inv H1.
    econstructor.
    eapply IHe1; eauto.
    eapply IHe2; eauto.
  - intros; subst; simpl.
    inv H1.
    constructor.
    eapply IHe; eauto.
    constructor. auto.
Qed.

Lemma subst_preservation_aux : forall W (e : tm W) V E,
  W = (^V)%type ->
  E ~= e ->
  forall (GammaA : ctx ^V) B,
  GammaA |- E : B -> forall Gamma e' lifted_e' A,
  hole GammaA Gamma A lifted_e' e' ->
  emp |- e' : A ->
  Gamma |- { tm_subst E lifted_e' } : B.
Proof.
  induction e.
  - intros. subst. simpl.
    inv H1.
    dependent induction H2.
    + destruct v; simpl; auto.
    + destruct v; simpl.
      apply IHhole with (o) in H3 as H.
      (* apply hole_inv in H2 as H22; destruct H22 as [GammaX [C Heq]]; subst. *)
      destruct o; simpl in *.
      admit.
      inv H2. simpl in *.

    apply hole_inv in H2 as H22; destruct H22 as [GammaX [C Heq]]; subst.
    destruct v; simpl in *.
    (* apply hole_inv in H2 as H22. destruct H22 as [Gamma' [C Heq]]. subst. *)
    (* inv H1. simpl. *)
    (* generalize dependent H3. *)
    (* apply hole_inv in H2 as H22. destruct H22 as [Gamma' [C Heq]]. subst. *)
    dependent induction H2.
    (* intros; subst; simpl. *)
    + inv H1. simpl. 
      (* assert (A = C). admit. *)
      (* subst. rewrite <- x. *)
      destruct v; auto.
    + 
      (* simpl in *. *)
      destruct v; simpl; auto.
      * inv H1.
        simpl in *.
        apply (IHhole o) in H3 as H4; auto.
        destruct o.
        constructor. simpl. admit.
        constructor. simpl.
        (* apply hole_inv in H2 as H22. destruct H22 as [Gamma'' [D Heq]]. subst. *)
        (* simpl in *. apply (IHhole o Gamma'' D) in H3 as H4. destruct o; simpl in *. *)
        simpl in *. apply (IHhole o) in H3 as H4. destruct o; simpl in *.
        admit.
        apply hole_inv in H2 as H22. destruct H22 as [Gamma'' [D Heq]]. subst.
        constructor. simpl. 
    (* inv H1. induction H2.
    + destruct v; auto.
    + destruct v.
      specialize IHhole with o. apply IHhole in H3. simpl in *.
      destruct o; simpl.
      * constructor. inv H3. simpl. assumption.
      * constructor. inv H3; simpl; auto.
        inv H2. contradiction.
    destruct v. admit. *)
  - intros; subst; simpl.
    inv H1.
    econstructor.
    eapply IHe1; eauto.
    eapply IHe2; eauto.
  - intros; subst; simpl.
    inv H1.
    constructor.
    eapply IHe; eauto.
    constructor. auto.

  intros W e. GammaA e B He.
  dependent induction He; intros.
  - admit.
  - simpl. constructor.
Qed.

Lemma subst_preservation : forall V (Gamma : ctx V) GammaA lifted_e' e' A,
  hole GammaA Gamma A lifted_e' e' ->
  emp |- e' : A -> forall e B,
  GammaA |- e : B ->
  forall W (GammaE : ctx W) E,
  W = (^V)%type ->
  GammaE ~= GammaA ->
  E ~= e ->
  Gamma |- { tm_subst E lifted_e' } : B.
Proof.
  intros V Gamma GammaA lifted_e' e' A Hhole.
  induction Hhole.
  - intros He. dependent induction e0; intros; simpl; subst.
    + inv H. destruct v. contradiction. simpl. assumption.
    + inv H. simpl.
      econstructor.
      eapply IHe0_1; eauto.
      eapply IHe0_2; eauto.
    + inv H. 
      simpl. constructor.
      eapply IHe0.

  
  intros B Hhole He He'.
  induction Hhole.

  intros V Gamma GammaA e lifted_e' e' A B Hhole He He'.
  dependent induction He.
  - admit.
  - simpl. constructor.
Qed.

Lemma subst_preservation_0 : forall W (e : tm W), forall V A B (Gamma : ctx V) E,
  W = (^V)%type ->
  E ~= e ->
  Gamma, A |- E : B -> forall e',
  Gamma |- e' : A ->
  Gamma |- { tm_subst E e' } : B.
Proof.
  induction e; intros; subst.
  - admit.
  - admit.
  - simpl. inv H1.
    constructor.
    assert (Gamma, t |- {lift e'} : A). admit.
    eapply IHe; auto.
  intros V Gamma e.
  dependent induction e; intros A B He e' He'; inv He.
  - admit.
  - admit.
  - simpl.
Abort.

Lemma subst_preservation_1 : forall V (Gamma : ctx V) e A B,
  Gamma, A |- e : B -> forall e',
  Gamma |- e' : A ->
  Gamma |- { tm_subst e e' } : B.
Proof.
  intros V Gamma e.
  dependent induction e; intros A B He e' He'; inv He.
  - admit.
  - admit.
  - simpl.
Abort.

Lemma subst_preservation_2 : forall V (Gamma : ctx V) e A B,
  Gamma, A |- e : B -> forall e',
  Gamma |- e' : A ->
  Gamma |- { tm_subst e e' } : B.
Proof.
  intros V Gamma e A B He.
  dependent induction He; intros e' He'.
  - destruct x; simpl; auto.
  - simpl. constructor.
    eapply IHHe.
Abort.

Theorem preservation : forall e e' t,
  emp |- e : t ->
  e --> e' ->
  emp |- e' : t.
Proof.
  intros e e' t He Hstep.
  dependent induction Hstep.
  - inv He. inv He1.
  Qed.

