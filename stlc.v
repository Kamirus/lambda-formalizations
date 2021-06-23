(* Deprecated - this is an unnecessarily complex approach that
   mixes nested-datatypes with De Bruijn indices
*)

(* Formalization of the Simply Typed Lambda Calculus using nested datatypes *)
Section STLC.

(* Goal: Progress and Preservation *)

Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.funind.Recdef.

Ltac inv H := dependent destruction H.


(* Terms *)
(*
  The term representation in the STLC (Simply Typed Lambda Calculus)
  depends on how variables are encoded.

  1. variable-as-string

  The most readable format represents variables as strings, e.g. [λx, f x].
  The problem of this representation is that ⍺-equivalent terms are distinct,
  e.g. [λx, x] ≠ [λy, y].

  2. de-bruijn-indices

  To avoid this issue we can encode variables as natural numbers, called
  de bruijn indices, where a variable [n] refers to the n-th lambda on a path
  from the variable occurrence to the root of the term-tree
  (read more: https://en.wikipedia.org/wiki/De_Bruijn_index).
  e.g. both [λx, x] and [λy, y] are represented as [λ 0] in this format.

  Another caveat is that, in both representations, we cannot restrict
  variables occurring out of scope,
  e.g. [λ 0 7] has a free variable [7] that is not bound to any λ in the term.

  3. nested-datatypes

  Nested Datatypes together with de bruijn indices allow us to staticly restrict
  what range of free variables is allowed.
  
  [tm V] is our datatype for terms where free variables are of type [V].
  - [var v] is a term [tm V] when [v] is of type [V] (free variable occurrence)
  - [e1 e2] is a term [tm V] provided that both [e1] and [e2] are terms [tm V]
  - [λ e] is a term [tm V] if [e] is a term [tm (option V)]

  The trick is in the 3rd case (abstraction)
  where the [e] (body of the lambda) can only have variables that are either
  [None] or [Some v] where [v] is of type [V].

  [None] refers to the variable occurrence bound by the current lambda,
  whereas a true free variable occurrence of [v] of type [V] under a lambda
  needs to be wrapped with [Some].

  In other words:
  [None] represents the variable [0] in de bruijn's format,
  while [Some] on a variable [v] acts like a successor function.

  Notation:
    [^V]    means  [option V]
    [V ↑ 0] means  [V]  
    [V ↑ 1] means  [^V]  
    [V ↑ 2] means  [^^V]
    ...
 *)

Notation "V ↑ n" := (iter Type n option V) (at level 5, left associativity) : type_scope.
Notation "^ V" := (option V) (at level 4, right associativity) : type_scope.

(* [tm V] represents a term with free variables of type [V] *)
Inductive tm (V : Type) :=
| tm_var : V -> tm V
| tm_app : tm V -> tm V -> tm V
| tm_abs : tm ^V -> tm V
.
Hint Constructors tm : core.
Arguments tm_var {V}.
Arguments tm_app {V}.
Arguments tm_abs {V}.


(* [var_n n] creates the n-th de bruijn index -
  which is [Some] applied n-times to [None] *)
Fixpoint var_n {V : Type} (n : nat) : V ↑ 1 ↑ n :=
  match n with
  | 0 => None
  | S n => Some (var_n n)
  end.

(* Important:
  Please note that the return type of [var_n] is [V ↑ 1 ↑ n] which is
  [option V] wrapped n-times with [option], so: [option^n (option V)].

  Notice that it's like wrapping [V] with [option] (1+n)-times,
  so it should be equivalent to wrapping it (n+1)-times as 1+n = n+1, right?

  Well it's equivalent but we cannot state equality of terms of different types:
    let v1 = [Some^n None : V ↑ n ↑ 1]
    let v2 = [Some^n None : V ↑ 1 ↑ n]
    We cannot say [v1 = v2] because their types does not match!
    The type of [=] is [A -> A -> Prop]
    and coq cannot normalize both types to the same type
    
  The choice between [V ↑ 1 ↑ n] and [V ↑ n ↑ 1] seems irrelevant now as both
  types are valid return types for [var_n],
  but it is crucial to pick one that is compatible with functions in the
  following sections.
  Compatible - meaning that coq can agree that types normalize to the same type.
 *)

Declare Custom Entry stlc.
Notation "<{ e }>" := e (at level 1, e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "{ x }" := x (in custom stlc at level 0, x constr).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation tm_var_n n := (tm_var (var_n n)).
Notation "0" := (tm_var_n 0) (in custom stlc at level 0).
Notation "1" := (tm_var_n 1) (in custom stlc at level 0).
Notation "2" := (tm_var_n 2) (in custom stlc at level 0).
Notation "3" := (tm_var_n 3) (in custom stlc at level 0).
Notation "4" := (tm_var_n 4) (in custom stlc at level 0).
Notation "'var' V" := (tm_var V) (in custom stlc at level 1, left associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "'λ' e" :=
  (tm_abs e) (in custom stlc at level 90,
               e custom stlc at level 99,
               left associativity).

(* Closed terms *)
(*
  Term [tm V] can only have free variables of type [V].
  So terms [tm False] cannot have free variables.
  The [tm False] type prevents us from creating open terms
  as the type [False] is uninhabited.

  Instead of [False] we create an explicit empty type called [Void].
*)

Inductive Void : Type := .
Definition term := tm Void.


(* Closed terms - Examples *)

Example tm_id : term :=
  <{ λ 0 }>.             (* λx, x *)
Example tm_ω  : term :=
  <{ λ 0 0 }>.           (* λx, x x *)
Example tm_Ω  : term :=
  <{ (λ 0 0) (λ 0 0) }>. (* (λx, x x)(λx, x x) *)

Example tm_ω_without_notation :
  tm_abs (tm_app (tm_var None) (tm_var None)) = tm_ω.
Proof. reflexivity. Qed.

(* Failed attempt to create open terms *)
(* These definitions simply does not type check *)
Fail Example ex_tm_var : term :=
  <{ 0 }>.
Fail Example ex_tm_abs : term :=
  <{ λ 1 }>.


(* Value *)
(*
  Let us first consider call-by-value evaluation strategy that only computes
  closed terms (we'll show how to do a full normalization later)

  So any lambda abstraction is a value in our language.
 *)

Inductive val : term -> Prop :=
| val_abs : forall e, val <{ λ e }>
.
Hint Constructors val : core.

(* To define an evaluation relation we first need a substition operation
   and for that we need lifting... *)


(* Lift *)
(* 
  Consider a term [e] which can contain free variables: 0, 1, 2, ... k, ...

  1) We need a lift operation (↑) that increments each free variable in a term
    e.g. so that [ ↑ <{ 0 (λ 0 1) }> = <{ 1 (λ 0 2) }> ]
                             ^ not a free variable! so it's still 0

  2) To implement (↑) we need a more general version called [lift n k],
    which adds [n] to every free variable at or above [k] level.
    e.g.
      lift n 0 <{ 0 }> = <{ n }>
      lift n 1 <{ 0 }> = <{ 0 }>
      lift n 1 <{ 1 }> = <{ n+1 }>
      lift n 1 <{ 2 }> = <{ n+2 }>

      lift n 0 <{ λ 0 }> = <{ λ 0 }>
      lift n 1 <{ λ 0 }> = <{ λ 0 }>
      lift n 1 <{ λ 1 }> = <{ λ 1 }>
      lift n 1 <{ λ 2 }> = <{ λ n+2 }>

  Learn more in http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.447.5355&rep=rep1&type=pdf
 *)

(* apply [Some] [n]-times *)
Fixpoint lift_var_n {V : Type} (n : nat) : V -> V ↑ n :=
  match n with
  | 0 => fun v => v
  | S n => fun v => Some (lift_var_n n v)
  end.

(* [lift_var n k v]: increase variable [v] by [n] when it's at least [k]

  Idea:
    if [v = Some^k (       v')]
    then [  Some^k (Some^n v')]  : skip k-levels, the rest lift n-times
    else [v]
 *)
Fixpoint lift_var {V : Type}
  (n k : nat) : V ↑ k -> V ↑ n ↑ k.
destruct k; intro v;
[ (* k=0 *) exact (lift_var_n n v) (* lift [v] n-times *)
| (* k>0 *) destruct v;
  [ (* v=Some *) exact (Some (lift_var V n k i))
  | (* v=None *) exact None
  ]
].
Defined.

Fixpoint lift {V : Type}
  (n k : nat) (e : tm V ↑ k) : tm V ↑ n ↑ k :=
  match e with
  | <{ var v }> => tm_var (lift_var n k v)
  | <{ e1 e2 }> => tm_app (lift n k e1) (lift n k e2)
  | <{ λ e   }> => tm_abs (lift n (S k) e)
  end.

Notation "↑ e" := (lift 1 0 e) (at level 70).

Example lift_examples : forall {V : Type} lift_7,
  lift_7 = @lift (V ↑ 2) 7 ->
  lift_7 0 <{   0 }> = tm_var_n 7 /\
  lift_7 1 <{   0 }> = <{ 0 }> /\
  lift_7 1 <{   1 }> = tm_var_n (7+1) /\
  lift_7 1 <{   2 }> = tm_var_n (7+2) /\
  lift_7 0 <{ λ 0 }> = <{ λ 0 }> /\
  lift_7 1 <{ λ 0 }> = <{ λ 0 }> /\
  lift_7 1 <{ λ 1 }> = <{ λ 1 }> /\
  lift_7 1 <{ λ 2 }> = <{ λ {tm_var_n (7+2)} }>.
Proof. intros; repeat split; subst; reflexivity. Qed.

Example lift_ex0 : forall {V : Type} (t : tm V ↑ 3),
   t = <{ 0 (λ 0 1 2) }> ->
  ↑t = <{ 1 (λ 0 2 3) }>.
Proof. intros; subst; reflexivity. Qed.

Example lift_ex1 : forall {V : Type} (t : tm V ↑ 3),
  t = <{ 1 0 2 }> ->
  lift 2 1 t = <{ 3 0 4 }>.
Proof. intros; subst; reflexivity. Qed.

Example lift_ex2 : forall {V : Type} (t : tm V ↑ 3),
  t = <{ 0 (λ 0 1 2) }> ->
  lift 2 1 t = <{ 0 (λ 0 1 4) }>.
Proof. intros; subst; reflexivity. Qed.



(* Substitution *)
(*
  Goal: [tm_subst n e e'] replaces variables [n] appearing in [e] with [e']
  Notation: e [n := e'] 'substitute n for e' in e'

  First implement [tm_subst_var n v e']
  that is a substitution when [e = var v]:
    if [v = Some^n None]: return [e'] lifted n-times
    otherwise: return [e] as nothing can be substituted
 *)
Fixpoint tm_subst_var
  {V : Type} (n : nat) : V ↑ 1 ↑ n -> tm V -> tm V ↑ n.
destruct n; intros [v | ] e';
[ (* n=0 v=Some *) exact (tm_var v)                (* leave this variable alone *)
| (* n=0 v=None *) exact e'                        (* substitute here! *)
| (* n>0 v=Some *) exact (↑ tm_subst_var _ _ v e') (* subst recursively, then lift *)
| (* n>0 v=None *) exact (tm_var None)             (* leave this variable alone *)
].
Defined.

(*
  Did you notice the type [V ↑ 1 ↑ n]? We've seen it before in the [var_n].

  Try changing the type in [var_n] to [V ↑ n ↑ 1] and see where coq complains.
  Can you fix the broken lemma without reverting the change in [var_n]?
 *)

Fixpoint tm_subst
  {V : Type} (n : nat) (e : tm V ↑ 1 ↑ n) (e' : tm V) : tm V ↑ n :=
  match e with
  | <{ var v }> => tm_subst_var n v e'
  | <{ e1 e2 }> => tm_app (tm_subst n e1 e') (tm_subst n e2 e')
  | <{ λ e   }> => tm_abs (tm_subst (S n) e e')
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
  <{ (λ 1 0) [0 := e] }> = <{ λ {↑ e} 0 }>.
Proof. intros; reflexivity. Qed.

Example subst_ex_3 :
  <{ (1 0) [0 := {↑ tm_id}] }> = <{ 0 {↑ tm_id} }>.
Proof. intros; reflexivity. Qed.

Example subst_ex_4 :
  <{ (1 0) [S 0 := tm_id] }> = <{ {↑ tm_id} 0 }>.
Proof. intros; reflexivity. Qed.


(* Evaluation *)
(*
  Finally we have all pieces to define the evaluation relation.

  [step_redex] reduces a redex [<{ (λ e) e' }>]
    by substituting [0] in the body [e] for the term [e']
  
  [step_app1] reduces the function of an application [<{ e1 e }>]

  [step_app2] reduces the argument of an application [<{ v e1 }>]
    when the function is already a value
 *)

Reserved Notation "e1 '-->' e2" (at level 40).
Inductive step : term -> term -> Prop :=
| step_redex : forall e e',
    <{ (λ e) e' }> --> <{ e [0 := e'] }>
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


(* Now we want to define the typing relation *)
(* 
  We start by defining the datatype for types:
  - We need one basic type: the unit.
    Note that we could pick any atomic type, like [Int] or [Bool].
  - and we need an arrow - the function type
 *)

(* Types *)

Inductive ty :=
| ty_unit : ty            (* unit is a type *)
| ty_arr : ty -> ty -> ty (* A -> B is a type when A and B are types *)
.
Hint Constructors ty : core.

Notation "A -> B" := (ty_arr A B) (in custom stlc at level 50, right associativity).


(* Context *)
(*
  For the typing relation we need a context Γ that remembers a type for each
  free variable.

  For the nested-datatypes format it's convinient to represent the context as
  a function of type [V -> ty] so a mapping from free variable to its type.

  So the empty context [·] is of type [Void -> ty]
    with the only reasonable implementation
 *)

Definition ctx V := V -> ty.

Definition emp : ctx Void := fun no => match no with end.
Notation "·" := emp.

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
  val v ->
  · |- v : (A -> B) ->
  exists e', v = <{ λ e' }>.
Proof.
  intros.
  inv H0; try inv H.
  exists e. reflexivity.
Qed.

(* Our first main theorem: Progress - well-typed terms never get 'stuck'
  if the term [e] type-checks then it's either a value or it makes a step
 *)
Theorem progress : forall e A,
  · |- e : A ->
  val e \/ exists e', e --> e'.
Proof with try solve [right; eexists; constructor; eauto | left; constructor].
  intros e A H.
  dependent induction H; fold · in *... (* lambda case solved already: value *)
  - contradiction. (* variable case is impossible as the terms are closed *)
  - assert (val e1 \/ (exists e', e1 --> e')) by auto; clear IHhas_type1.
    assert (val e2 \/ (exists e', e2 --> e')) by auto; clear IHhas_type2.
    destruct H1 as [H1 | [e' H1]]...
    destruct H2 as [H2 | [e' H2]]...
    apply (val_arr_inversion _ A B) in H1 as [e' H1]; auto.
    subst... (* we have a redex *)
Qed.


(* The second theorem we want to prove is called Preservation,
  but before we can formalize it we need:
  - additional context operations
  - Weakening lemma
  - Substitution lemma
 *)

(* [drop n k Γ] is a counterpart for the [lift] operation,
  but it changes the context while [lift] changes the term

  Idea:
    [ drop n k (Γ, Bn .. B1, Ak .. A1) = (Γ, Ak .. A1) ]
 *)

Fixpoint drop_n {V : Type} (n : nat) :
  ctx V ↑ n ->
  ctx V     :=
    match n with
    | 0 => fun (ctx : ctx V) => ctx
    | S n => fun (ctx : ctx V ↑ n ↑ 1) => drop_n n (fun v => ctx (Some v))
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
  
  Goal equivalent:
    drop n k Γ |- e : A ->
    Γ |- lift n k e : A
 *)

Lemma weakening_var : forall V k n (Γ : ctx V ↑ n ↑ k) A v,
  drop n k Γ |- var v : A ->
  Γ |- var {lift_var n k v} : A.
Proof with cbn in *.
  intros; induction k...
  + induction n; auto...
    constructor.
    apply IHn in H; clear IHn.
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

Notation "Γ \ n" := (drop 1 n Γ) (at level 5).

Theorem Weakening : forall V e (Γ : ctx ^V) A,
  Γ \ 0 |-    e  : A ->
  Γ     |- {↑ e} : A.
Proof.
  intros. apply weakening in H. assumption.
  Qed.


(* Substitution Lemma - closed terms

  Goal:
    ·, B, Cn .. C1 |- e           : A ->
    ·              |- e'          : B ->
    ·   , Cn .. C1 |- e [n := e'] : A

  Idea:
    Again, remove instead of adding:
      - Γ \ n  removes the n-th type from the context Γ
      - Γ[n]   gets    the n-th type from the context Γ

  Goal equivalent:
    Γ     |- e           : A ->
    ·     |- e'          : Γ[n] ->
    Γ \ n |- e [n := e'] : A
*)

Notation "Γ [ n ]" := (Γ (var_n n))
  (in custom stlc at level 0,
    n constr at level 0).

Lemma substitution_lemma_for_closed : forall n
  (e : tm  Void ↑ 1 ↑ n)
  (Γ : ctx Void ↑ 1 ↑ n)
  (e': term) A,
    Γ     |- e           : A    ->
    ·     |- e'          : Γ[n] ->
    Γ \ n |- e [n := e'] : A.
Proof with cbn in *.
  intros. dependent induction e; inv H...
  - induction n...
    + destruct v; auto.
      (* additional steps for closed lemma *)
      assert (· = (fun v : Void => Γ (Some v)))
        by (apply functional_extensionality; intros; contradiction).
      rewrite <- H. assumption.
    + destruct v.
      * apply Weakening.
        apply IHn.
        assumption.
      * constructor. reflexivity.
  - eauto.
  - constructor.
    cut ((Γ, A) \ (S n) |- e [S n := e'] : B).
    + intro... inv H1; rewrite <- x; eauto.
    + apply IHe; auto.
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
    set (H := substitution_lemma_for_closed 0 e (·, A) e' B).
    apply H in He1; auto.
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

  [nval e] says that the term [e] of type [tm V] (so it can have free variables)
  is a value. Values can take one of two forms:
    - [x e1 .. en] is a value when [x] is a variable and [e1] .. [en] are values
    - [λ e] is a value when [e] is a value
 *)
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
    nval <{ λ e }>
.
Hint Constructors nval : core.

Reserved Notation "t1 '-->n' t2" (at level 40).
Inductive norm : forall {V}, tm V -> tm V -> Prop :=
| norm_redex : forall V e (e' : tm V),
    <{ (λ e) e' }> -->n <{ e [0 := e'] }>
| norm_app1 : forall V (e1 e2 e : tm V),
    e1 -->n e2 ->
    <{ e1 e }> -->n <{ e2 e }>
| norm_app2 : forall V (e1 e2 v : tm V),
    nval v ->
    e1 -->n e2 ->
    <{ v e1 }> -->n <{ v e2 }>
| norm_abs : forall V (e1 e2 : tm ^V),
    e1 -->n e2 ->
    <{ λ e1 }> -->n <{ λ e2 }>
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


(* Substitution Lemma - open terms

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
    Γ              |- e           : A ->
    drop (S n) 0 Γ |- e'          : Γ[n] ->
    Γ \ n          |- e [n := e'] : A
*)

Lemma substitution_lemma : forall V n
  (e : tm  V ↑ 1 ↑ n)
  (Γ : ctx V ↑ 1 ↑ n)
  (e': tm V) A,
    Γ                |- e           : A ->
    (drop n 0 Γ) \ 0 |- e'          : Γ[n] ->
    Γ \ n            |- e [n := e'] : A.
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
    cut ((Γ, A) \ (S n) |- e [S n := e'] : B).
    + intro... inv H1; rewrite <- x; eauto.
    + apply IHe; auto.
Qed.

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

End STLC.
