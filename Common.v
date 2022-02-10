Require Export Utf8.
Require Export Coq.funind.Recdef.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Program.Basics.
Require Export Coq.Program.Equality.

Open Scope program_scope.

Notation "V ↑ n" := (iter Type n option V) (at level 5, left associativity) : type_scope.
Notation "^ V" := (option V) (at level 4, right associativity) : type_scope.

Class Functor (F : Type → Type) :=
  { fmap : ∀ {A B}, (A → B) → F A → F B

  (** Functor laws **)
  ; fmap_identity : ∀ A (x : F A) (f : A → A),
      (∀ x, f x = x) → fmap f x = x
  ; fmap_composition : 
      ∀ A B C (f : B → C) (g : A → B) (x : F A), fmap (f ∘ g) x = fmap f (fmap g x)
  }.

Inductive step {T} {contr : T → T → Prop} : T → T → Prop :=
| step_refl  : ∀ M, step M M
| step_trans : ∀ M M' N,
    contr M M' → 
    step    M' N → 
    step  M    N
.
Global Notation "M --->* N" := (step M N) (at level 50).
Global Hint Constructors step : core.

Ltac inv H := dependent destruction H.
Ltac inj H := injection H; intros; subst; clear H.
    
