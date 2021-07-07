Require Export Utf8.
Require Export Coq.funind.Recdef.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Program.Basics.

Open Scope program_scope.

Notation "V ↑ n" := (iter Type n option V) (at level 5, left associativity) : type_scope.
Notation "^ V" := (option V) (at level 4, right associativity) : type_scope.
