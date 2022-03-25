Require Export Utf8.
Require Export Coq.funind.Recdef.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Program.Basics.
Require Export Coq.Program.Equality.
Require Export Coq.Relations.Relation_Definitions.

Open Scope program_scope.

Notation "V ↑ n" := (iter Type n option V) (at level 5, left associativity) : type_scope.
Notation "^ V" := (option V) (at level 4, right associativity) : type_scope.

Inductive Void : Type := .
Notation "␀" := (Void).
Definition from_void {A} (v : ␀) : A := match v with end.

Class Functor (F : Type → Type) :=
  { fmap : ∀ {A B}, (A → B) → F A → F B

  (** Functor laws **)
  ; fmap_identity : ∀ A (x : F A) (f : A → A),
      (∀ x, f x = x) → fmap f x = x
  ; fmap_composition : 
      ∀ A B C (f : B → C) (g : A → B) (x : F A), fmap (f ∘ g) x = fmap f (fmap g x)
  }.

Inductive multi {X : Type} (R : relation X) : relation X :=
| multi_refl : ∀ (x : X), multi R x x
| multi_step : ∀ (x y z : X), R x y → multi R y z → multi R x z.
Global Hint Constructors multi : core.

Ltac inv H := dependent destruction H.
Ltac inj H := injection H; intros; subst; clear H.
    

Class Lift (F : Type → Type) := lift : ∀ {A}, F A → F ^A.
Notation "↑ e" := (lift e) (at level 0).
