(* Formalization of the Simply Typed Lambda Calculus using nested datatypes *)

(* Goal: Progress and Preservation *)

Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.funind.Recdef.

Ltac inv H := dependent destruction H.

Notation "^ f" := (option_map f) (at level 5, right associativity) : function_scope.
Notation "^ X" := (option X) : type_scope.


(* Types *)

Inductive ty :=
| ty_unit : ty            (* unit is a type *)
| ty_arr : ty -> ty -> ty (* A -> B is a type when A and B are types *)
.
Hint Constructors ty : core.


(* Terms *)
(*
  The representation of terms in the STLC (simply typed lambda calculus)
  depends on how variables are encoded.

  The most readable format represents variables as strings, e.g. [λx: A, f x].
  The problem of this representation is that ⍺-equivalent terms are distinct,
  e.g. [λx:A, x] ≠ [λy:A, y].

  To avoid this issue we can encode variables as natural numbers, called
  de bruijn indices. Then a variable [n] refers to the n-th lambda on a path
  from the variable occurrence to the root of the term-tree
  (read more: https://en.wikipedia.org/wiki/De_Bruijn_index).
  e.g. both [λx:A, x] and [λy:A, y] are represented as [λA, 0] in this format.

  Note: we need type annotations for our lambda abstractions 
  .
  .

  
 *)

Inductive tm (V : Type) :=      (* terms depend on an abstract variable type [V] *)
| tm_var : V -> tm V            (* variable [v] is a term [tm V] when [v : V] *)
| tm_app : tm V -> tm V -> tm V (* an application of e1 to e2 is a term *)
| tm_abs : tm ^V -> tm V  (*  *)
.
Hint Constructors tm : core.
Arguments tm_var {V}.
Arguments tm_app {V}.
Arguments tm_abs {V}.

Notation "T ↑ n" := (iter _ n option T) (at level 5) : type_scope.

Fixpoint var_n {V : Type} (n : nat) : V ↑ (S n) :=
  match n with
  | 0 => None
  | S n => Some (var_n n)
  end.

Declare Custom Entry stlc.
Notation "<{ e }>" := e (at level 1, e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "{ x }" := x (in custom stlc at level 0, x constr).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "0" := (tm_var (var_n 0)) (in custom stlc at level 0).
Notation "1" := (tm_var (var_n 1)) (in custom stlc at level 0).
Notation "2" := (tm_var (var_n 2)) (in custom stlc at level 0).
Notation "3" := (tm_var (var_n 3)) (in custom stlc at level 0).
Notation "4" := (tm_var (var_n 4)) (in custom stlc at level 0).
(* Notation "'S' .. 'S' x" := (tm_var (inc_S .. (inc_S x) ..)) (in custom stlc at level 0). *)
Notation "'var' V" := (tm_var V) (in custom stlc at level 1, left associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ e" :=
  (tm_abs e) (in custom stlc at level 90,
               e custom stlc at level 99,
               left associativity).
(* Coercion tm_var : V >-> tm V. *)
Notation "S -> T" := (ty_arr S T) (in custom stlc at level 50, right associativity).


(* Closed terms *)

Inductive Void : Type := .
Definition term := tm Void.

(* Several examples, the type `U` is irrelevant here *)
Example tm_id : term :=
  <{ \ 0 }>. (* \x, x *)
Example tm_ω  : term :=
  <{ \ 0 0 }>. (* \x, x x *)
Example tm_Ω  : term :=
  <{ (\ 0 0) (\ 0 0) }>.

(* Attempt to create open terms *)
Fail Example ex_tm_var : term :=
  <{ 0 }>.
Fail Example ex_tm_abs : term :=
  <{ \ 1 }>.


(* Lift *)
(* source: http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.447.5355&rep=rep1&type=pdf *)

(* apply [Some] [n]-times *)
Fixpoint lift_var_n {V : Type} (n : nat) : V -> V ↑ n :=
  match n with
  | 0 => fun v => v
  | S n => fun v => Some (lift_var_n n v)
  end.

(* leave variables less than [k] untouched and remaining ones increase by [n] *)
Fixpoint lift_var {V : Type}
  (n k : nat) : V ↑ k -> V ↑ n ↑ k.
destruct k; intro v;
[ exact (lift_var_n n v)
| destruct v;
  [ exact (Some (lift_var V n k i))
  | exact None
  ]
].
Defined.

Fixpoint lift {V : Type}
  (n k : nat) (e : tm V ↑ k) : tm V ↑ n ↑ k :=
  match e with
  | <{ var v }> => tm_var (lift_var n k v)
  | <{ e1 e2 }> => tm_app (lift n k e1) (lift n k e2)
  | <{ \ e   }> => tm_abs (lift n (S k) e)
  end.

Example lift_ex1 : forall {V : Type},
@lift (V ↑ 2) 2 1 <{ 0 1 2 }> = <{ 0 3 4 }>.
Proof. reflexivity. Qed.

Example lift_ex2 : forall {V : Type},
@lift (V ↑ 2) 2 1 <{ 0 (\ 0 1 2) }> = <{ 0 (\ 0 1 4) }>.
Proof. reflexivity. Qed.

Notation "↑ e" := (lift 1 0 e) (at level 99).

(* Substitution *)

Fixpoint tm_subst_var
  {V : Type} (n : nat) : V ↑ (S n) -> tm V -> tm V ↑ n.
destruct n; intros [v | ] e;
[ exact (tm_var v)
| exact e
| exact (↑ tm_subst_var _ _ v e)
| exact (tm_var None)
].
Defined.

Fixpoint tm_subst
  {V : Type} (n : nat) (e : tm V ↑ (S n)) (e' : tm V) : tm V ↑ n :=
  match e with
  | <{ var v }> => tm_subst_var n v e'
  | <{ e1 e2 }> => tm_app (tm_subst n e1 e') (tm_subst n e2 e')
  | <{ \ e   }> => tm_abs (tm_subst (S n) e e')
  end.

Notation "e [ n := e' ]" := (tm_subst n e e')
  (in custom stlc at level 0,
    e custom stlc,
    e' custom stlc at level 99,
    n constr at level 0).

Example subst_ex_1 :
  <{ (0 0) [0 := tm_ω] }> = tm_Ω.
Proof. reflexivity. Qed.

Example subst_ex_2 : forall (e : term),
  <{ (\ 1 0) [0 := e] }> = <{ \ {↑ e} 0 }>.
Proof. intros; reflexivity. Qed.

Example subst_ex_3 :
  <{ (1 0) [0 := {↑ tm_id}] }> = <{ 0 {↑ tm_id} }>.
Proof. intros; reflexivity. Qed.

Example subst_ex_4 :
  <{ (1 0) [S 0 := tm_id] }> = <{ {↑ tm_id} 0 }>.
Proof. intros; reflexivity. Qed.


(* Value *)

Inductive val : term -> Prop :=
| val_abs : forall e, val <{ \ e }>
.
Hint Constructors val : core.


(* Evaluation *)

(* CBV, could be CBN or undeterministic *)

Reserved Notation "e1 '-->' e2" (at level 40).
Inductive step : term -> term -> Prop :=
| step_redex : forall e e',
    <{ (\ e) e' }> --> <{ e [0 := e'] }>
| step_app1 : forall e1 e2 e,
    e1 --> e2 ->
    <{ e1 e }> --> <{ e2 e }>
| step_app2 : forall e1 e2 v,
    val v ->
    e1 --> e2 ->
    <{ v e1 }> --> <{ v e2 }>
where "e1 '-->' e2" := (step e1 e2).
Hint Constructors step : core.

Remark tm_ω_value : ~ exists e, tm_ω --> e.
Proof. unfold tm_ω. intros [e H]. inv H. Qed.

Remark tm_Ω_reduces_to_itself : tm_Ω --> tm_Ω.
Proof. intros. unfold tm_Ω. constructor. Qed.

(* Context *)

Definition ctx V := V -> ty.
Definition emp : ctx Void := fun no => match no with end.

Definition ctx_cons {V : Type} (Γ : ctx V) (A : ty) : ctx ^V :=
  fun V' =>
    match V' with
    | None => A
    | Some V => Γ V
    end.
Notation "Γ , A" := (ctx_cons Γ A) (at level 100, A custom stlc at level 0).


(* Typing relation *)

Reserved Notation "Γ '|-' A ':' T"
  (at level 101, A custom stlc, T custom stlc at level 0).
Inductive has_type : forall {V}, ctx V -> tm V -> ty -> Prop :=
| var_has_type : forall {V} Γ (x : V) A,
    Γ x = A ->
    Γ |- var x : A
| abs_has_type : forall {V} Γ A B (e : tm ^V),
    Γ, A |- e : B ->
    Γ |- \ e : (A -> B)
| app_has_type : forall {V} (Γ : ctx V) B A e1 e2,
    Γ |- e1 : (A -> B) ->
    Γ |- e2 : A ->
    Γ |- e1 e2 : B
where "Γ '|-' A ':' T" := (has_type Γ A T).
Hint Constructors has_type : core.

Remark tm_id_typeable : forall (A:ty),
  emp |- tm_id : (A -> A).
Proof. unfold tm_id; auto. Qed.

Remark ty_not_equi_recursive : forall A B, A = ty_arr A B -> False.
Proof.
  induction A; intros.
  - discriminate H.
  - injection H; intros; subst.
    eapply IHA1. eassumption.
  Qed.

Remark tm_ω_not_typeable :
  ~ exists T, emp |- tm_ω : T.
Proof.
  unfold tm_ω.
  intros [T H].
  dependent destruction H.
  dependent destruction H.
  fold emp in *.
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
  assert (H1: emp |- tm_id : T1) by apply tm_id_typeable.
  assert (H2: emp |- tm_id : T2) by apply tm_id_typeable.
  cut (T1 = T2). intro H0; discriminate H0.
  eapply H; eauto.
  Qed.

Lemma val_arr : forall v A B,
  val v ->
  emp |- v : (A -> B) ->
  exists e', v = <{ \ e' }>.
Proof.
  intros.
  inv H0; try inv H.
  exists e. reflexivity.
  Qed.

Theorem progress : forall e A,
  emp |- e : A ->
  val e \/ exists e', e --> e'.
Proof with try solve [right; eexists; constructor; eauto | left; constructor].
  intros e A H.
  dependent induction H; fold emp in *...
  - contradiction.
  - assert (val e1 \/ (exists e', e1 --> e')) by auto; clear IHhas_type1.
    assert (val e2 \/ (exists e', e2 --> e')) by auto; clear IHhas_type2.
    destruct H1 as [H1 | [e' H1]]...
    destruct H2 as [H2 | [e' H2]]...
    apply (val_arr _ A B) in H1 as [e' H1]; auto.
    subst...
Qed.


(* Weakening *)

Fixpoint drop_n {V : Type} (n : nat) :
  ctx V ↑ n ->
  ctx V     :=
    match n with
    | 0 => fun (ctx : ctx V) => ctx
    | S n => fun (ctx : ctx V ↑ (S n)) => drop_n n (fun v => ctx (Some v))
    end.

Fixpoint drop {V : Type} (n k : nat) : 
  ctx V ↑ n ↑ k ->
  ctx V     ↑ k :=
    match k with
    | 0   => fun ctx => drop_n n ctx
    | S k => fun ctx => fun v =>
      match v with
      | None   => ctx None
      | Some i => drop _ _ (fun v => ctx (Some v)) i
      end
    end.

(* Weakening

  Goal:
    Γ'          , Ak .. A1 |-          e : A ->
    Γ', Bn .. B1, Ak .. A1 |- lift n k e : A

  Idea:
    Instead of adding Ak..A1 and Bn..B1 types to the context Γ'
    let Γ := Γ', Bn .. B1, Ak .. A1
    and reformulate theorem so that we drop Bn .. B1 from Γ.
    - drop n k Γ  leaves first k types in the context Γ untouched
                   and removes next n types
  
  Goal equivalent:
    drop n k Γ |- e : A ->
    Γ |- lift n k e : A
 *)

Lemma weakening_var : forall V k n (Γ : ctx V ↑ n ↑ k) A v,
  drop n k Γ |- var v : A ->
  Γ |- var {lift_var n k v} : A.
Proof with cbn in *.
  intros. subst...
  induction k...
  + induction n; auto...
    constructor.
    apply IHn in H.
    inv H. reflexivity.
  + destruct v.
    - constructor.
      set (G := fun v => Γ (Some v)).
      specialize IHk with (Γ := G) (v := i).
      cut (G |- var {lift_var n k i} : A).
      * intros H0. inv H0. reflexivity.
      * apply IHk. clear IHk. subst G.
        inv H. auto.
    - inv H. auto.
Qed.

Lemma drop_cons : forall V n k (Γ : ctx V ↑ n ↑ k) A e B,
  (drop n    k   Γ), A  |- e : B ->
   drop n (S k) (Γ , A) |- e : B.
Proof.
  intros. induction H; eauto.
Qed.

Theorem weakening : forall V k e n (Γ : ctx V ↑ n ↑ k) A,
  drop n k Γ |- e : A ->
  Γ |- {lift n k e} : A.
Proof with cbn in *.
  dependent induction e; intros; inv H...
  - apply weakening_var. auto.
  - eauto.
  - constructor.
    apply drop_cons in H.
    apply IHe in H; auto.
Qed.

Theorem Weakening : forall V e (Γ : ctx ^V) A,
  drop 1 0 Γ |- e : A ->
  Γ |- {↑ e} : A.
Proof.
  intros. apply weakening in H. assumption.
  Qed.

(* Substitution Lemma *)

Fixpoint ctx_rm
  {V : Type} (n : nat) : ctx V ↑ (S n) -> ctx V ↑ n :=
  match n with
  | 0   => fun ctx v => ctx (Some v)
  | S n => fun ctx v =>
      match v with
      | None   => ctx None
      | Some v => ctx_rm n (fun v => ctx (Some v)) v
      end
  end.

Notation "Γ \ n" := (ctx_rm n Γ) (at level 5).

(* TODO: substitution_lemma for subst closed terms - easier *)

(* Substitution Lemma

  Goal:
    Γ', B, Cn .. C1 |- e           : A ->
    Γ'              |- e'          : B ->
    Γ'   , Cn .. C1 |- e [n := e'] : A

  Idea:
    Again, remove instead of adding:
      - Γ \ n  removes the n-th type from the context Γ
      - Γ[n]   gets    the n-th type from the context Γ
      - drop (S n) 0 Γ removes first n+1 types from Γ
  
  Goal equivalent:
    Γ |- e : A ->
    drop (S n) 0 Γ |- e' : Γ[n] ->
    Γ \ n |- e [n := e'] : A
*)

Notation "Γ [ n ]" := (Γ (var_n n))
  (in custom stlc at level 0,
    n constr at level 0).

Lemma substitution_lemma : forall V n
  (e : tm  V ↑ (S n))
  (Γ : ctx V ↑ (S n))
  (e': tm V) A,
    Γ |- e : A ->
    drop (S n) 0 Γ |- e' : Γ[n] ->
    Γ \ n |- e [n := e'] : A.
Proof with cbn in *.
  intros. dependent induction e; inv H...
  - induction n...
    + destruct v; auto.
    + destruct v.
      * apply Weakening.
        apply IHn.
        assumption.
      * constructor. reflexivity.
  - eauto.
  - constructor.
    cut (ctx_rm (S n) (Γ, A) |- e [S n := e'] : B).
    + intro... inv H1; rewrite <- x; eauto.
    + apply IHe; auto.
Qed.


(* Preservation *)

Theorem preservation : forall e e',
  e --> e' -> forall A,
  emp |- e : A ->
  emp |- e' : A.
Proof.
  intros e e' Hstep.
  induction Hstep; intros A He; inv He; fold emp in *.
  - inv He1. fold emp in *.
    set (H := substitution_lemma Void 0 e (emp, A) e' B).
    apply H in He1; auto.
  - apply IHHstep in He1.
    econstructor; eauto.
  - apply IHHstep in He2.
    econstructor; eauto.
  Qed.


(* Full normalization *)

Inductive nval : forall {V}, tm V -> Prop :=
| nval_var : forall V (v : V),
    nval <{ var v }>
| nval_app_var : forall V e (v : V),
    nval e ->
    nval <{ (var v) e }>
| nval_app : forall V (e1 e2 e : tm V),
    nval <{ e1 e2 }> ->
    nval e ->
    nval <{ e1 e2 e }>
| nval_abs : forall V (e : tm ^V),
    nval e ->
    nval <{ \ e }>
.
Hint Constructors nval : core.

Reserved Notation "t1 '-->n' t2" (at level 40).
Inductive norm : forall {V}, tm V -> tm V -> Prop :=
| norm_redex : forall V e (e' : tm V),
    <{ (\ e) e' }> -->n <{ e [0 := e'] }>
| norm_app1 : forall V (e1 e2 e : tm V),
    e1 -->n e2 ->
    <{ e1 e }> -->n <{ e2 e }>
| norm_app2 : forall V (e1 e2 v : tm V),
    nval v ->
    e1 -->n e2 ->
    <{ v e1 }> -->n <{ v e2 }>
| norm_abs : forall V (e1 e2 : tm ^V),
    e1 -->n e2 ->
    <{ \ e1 }> -->n <{ \ e2 }>
where "t1 '-->n' t2" := (norm t1 t2).
Hint Constructors norm : core.


Lemma nval_no_steps : forall V (e : tm V),
  nval e ->
  ~ exists e', e -->n e'.
Proof with eauto.
  intros V e Hval [e' H].
  induction Hval; inv H...
  inv H...
  Qed.

(* For this we need to alter normalization relation -
   for now only closed terms can reduce *)
Theorem open_preservation : forall V (e e' : tm V),
  e -->n e' -> forall Γ A,
  Γ |- e  : A ->
  Γ |- e' : A.
Proof.
  intros V e e' Hstep.
  induction Hstep; intros Γ t0 He; inv He; try (econstructor; eauto).
  - inv He1.
    set (H := substitution_lemma _ 0 e (Γ, A) e' B).
    apply H in He1; auto.
  Qed.

Theorem open_progress : forall V Γ (e : tm V) A,
  Γ |- e : A ->
  nval e \/ exists e', e -->n e'.
Proof with try solve [right; eexists; eauto | left; auto].
  intros V Γ e A H.
  dependent induction H...
  - destruct IHhas_type  as [H0 | [e' H0]]...
  - destruct IHhas_type1 as [H1 | [e' H1]]... (* e1 makes a step *)
    destruct IHhas_type2 as [H2 | [e' H2]]... (* e2 makes a step *)
    destruct H1... (* either an app value [x e1 .. en] or redex *)
Qed.
