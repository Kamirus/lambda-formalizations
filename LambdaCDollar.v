(* Common *)
Require Export Common.

(* Knowledge Links:
  - shift/reset tutorial http://pllab.is.ocha.ac.jp/~asai/cw2011tutorial/main-e.pdf
  - shift0/reset0 http://www.tilk.eu/shift0/materzok-csl13.pdf
  - https://bitbucket.org/pl-uwr/aleff-lex/src/master/coq/Lang/Open/Syntax.v
 *)

(* Terms *)

Inductive tm {A} := 
| tm_val    : val → tm
| tm_non    : non → tm
with val {A} := 
| val_var   : A → val
| val_lam   : @tm ^A → val
| val_S₀    : val
with non {A} :=
| non_app   : tm → tm → non
| non_let   : tm → @tm ^A → non
| non_reset : tm → tm → non
.
Arguments tm  A : clear implicits.
Arguments val A : clear implicits.
Arguments non A : clear implicits.
Global Hint Constructors tm val non : core.

Scheme tm_mut := Induction for tm Sort Prop
with val_mut := Induction for val Sort Prop
with non_mut := Induction for non Sort Prop.

Definition tm_mut_ P := tm_mut P
  (λ A V, P A (tm_val V))
  (λ A Q, P A (tm_non Q)).

Module Export Notations_Tm.
  Declare Custom Entry λc_dollar_scope.
  Notation "<{ M }>" := M (at level 1, M custom λc_dollar_scope at level 99).
  Notation "( x )" := x (in custom λc_dollar_scope, x at level 99).
  Notation "{ x }" := x (in custom λc_dollar_scope at level 0, x constr).
  Notation "x" := x (in custom λc_dollar_scope at level 0, x constr at level 0).
  Notation "'var' v" := (tm_val (val_var v)) (in custom λc_dollar_scope at level 1, left associativity).
  Notation "0" := <{ var None }> (in custom λc_dollar_scope at level 0).
  Notation "1" := <{ var {Some None} }> (in custom λc_dollar_scope at level 0).
  Notation "2" := <{ var {Some (Some None)} }> (in custom λc_dollar_scope at level 0).
  Notation "M N" := (tm_non (non_app M N)) (in custom λc_dollar_scope at level 10, left associativity).
  Notation "'λ' M" := (tm_val (val_lam M))
    (in custom λc_dollar_scope at level 90,
    M custom λc_dollar_scope at level 99,
    right associativity).
  Notation "M '$' N" := (tm_non (non_reset M N)) (in custom λc_dollar_scope at level 80, right associativity).
  Notation "'S₀'" := (tm_val (val_S₀)) (in custom λc_dollar_scope at level 0).
  Notation "'S₀λ' M" := <{ {tm_val (val_S₀)} (λ M) }>
    (in custom λc_dollar_scope at level 90,
    M custom λc_dollar_scope at level 99,
    right associativity).
  Notation "'let' M 'in' N" := (tm_non (non_let M N))
    (in custom λc_dollar_scope at level 95,
    M custom λc_dollar_scope at level 99,
    N custom λc_dollar_scope at level 99,
    right associativity).
  Notation "< M >" := <{ (λ 0) $ M }> (in custom λc_dollar_scope at level 0).
End Notations_Tm.

(* Map *)

Fixpoint map {A B : Type} (f : A → B) (e : tm A) : tm B :=
  match e with
  | tm_val t => tm_val (map_val f t)
  | tm_non t => tm_non (map_non f t)
  end
with map_val {A B : Type} (f : A → B) (e : val A) : val B :=
  match e with
  | val_var v => val_var (f v)
  | val_lam e => val_lam (map (option_map f) e)
  | val_S₀    => val_S₀
  end
with map_non {A B : Type} (f : A → B) (e : non A) : non B :=
  match e with
  | non_app e1 e2 => non_app (map f e1) (map f e2)
  | non_let e1 e2 => non_let (map f e1) (map (option_map f) e2)
  | non_reset e1 e2 => non_reset (map f e1) (map f e2)
  end.

Notation map_id_law_for F := (λ A e,
  ∀ (f : A → A),
    (∀ x, f x = x) →
    F f e = e
).

Instance Map_tm  : Functor tm  := { fmap := @map }.
Instance Map_val : Functor val := { fmap := @map_val }.
Instance Map_non : Functor non := { fmap := @map_non }.

Ltac crush := 
  intros; cbn; f_equal; auto.

Ltac crush_option := 
  let x := fresh "x" in
  intros [x|]; cbn; f_equal; auto.

Lemma map_id_law : ∀ A e, map_id_law_for map A e.
Proof.
  cbn; apply (tm_mut
    (map_id_law_for map)
    (map_id_law_for map_val)
    (map_id_law_for map_non)); crush;
  (apply H + apply H0); crush_option.
Qed.

Notation map_comp_law_for F := (λ A e,
  ∀ B C (f : A → B) (g : B → C),
    F g (F f e) = F (g ∘ f) e
).

Lemma option_map_comp : ∀ A B C (f : A → B) (g : B → C),
  option_map (g ∘ f) = option_map g ∘ option_map f.
Proof.
  intros. apply functional_extensionality. crush_option.
Qed.

Lemma map_comp_law : ∀ A e, map_comp_law_for map A e.
Proof.
  cbn; apply (tm_mut
    (map_comp_law_for map)
    (map_comp_law_for map_val)
    (map_comp_law_for map_non)); crush;
  rewrite option_map_comp;
  (apply H + apply H0); crush_option.
Qed.

(* Bind *)

Definition option_bind {A B} (f: A → val B) (o: ^A) : val ^B :=
  match o with
  | None => val_var None
  | Some a => map_val Some (f a)
  end.

Fixpoint bind {A B : Type} (f : A → val B) (e : tm A) : tm B :=
  match e with
  | tm_val t => tm_val (bind_val f t)
  | tm_non t => tm_non (bind_non f t)
  end
with bind_val {A B : Type} (f : A → val B) (e : val A) : val B :=
  match e with
  | val_var v => f v
  | val_lam e => val_lam (bind (option_bind f) e)
  | val_S₀    => val_S₀
  end
with bind_non {A B : Type} (f : A → val B) (e : non A) : non B :=
  match e with
  | non_app e1 e2 => non_app (bind f e1) (bind f e2)
  | non_let e1 e2 => non_let (bind f e1) (bind (option_bind f) e2)
  | non_reset e1 e2 => non_reset (bind f e1) (bind f e2)
  end.

Notation bind_is_map_for F Bind := (λ A e,
  ∀ B (f : A → B), F f e = Bind (λ v, val_var (f v)) e
).

Lemma bind_is_map : ∀ A e, bind_is_map_for map bind A e.
Proof.
  cbn; apply (tm_mut
    (bind_is_map_for map bind)
    (bind_is_map_for map_val bind_val)
    (bind_is_map_for map_non bind_non)); crush;
    (rewrite H + rewrite H0); f_equal; apply functional_extensionality; crush_option.
Qed.

(* Notation bind_law_for Bind := (λ A e,
  ∀ B C (f:A → val B) (g:B → val C),
    Bind g (Bind f e) = Bind (λ a, Bind g (f a)) e
).
Lemma bind_law : ∀ A e, bind_law_for bind A e. *)

(* Closed terms *)

Inductive Void : Type := .
Definition term := tm Void.
Definition value := val Void.


(* Lift *)

Definition lift {F : Type → Type} {A : Type} `{Functor F} : F A → F ^A := fmap Some.

Notation "↑ e" := (lift e) (at level 2).
Notation "↥ V" := (tm_val (↑(V : val _))) (at level 2).


(* Substitution *)

Definition sub_var {A} (e': val A) (v:^A) : val A :=
  match v with
  | None => e'
  | Some v => val_var v
  end.

Definition sub {A} (e:tm ^A) (e':val A) : tm A :=
  bind (sub_var e') e.

Lemma sub_app : ∀ A M N (V : val A),
  sub <{ M N }> V = <{ {sub M V} {sub N V} }>.
Proof. auto. Qed.

Ltac ind M PP := (induction M using tm_mut with
  (P  := λ A M, PP A M)
  (P1 := λ A Q, PP A (tm_non Q))
  (P0 := λ A V, PP A (tm_val V))).

Ltac ind1 M PP := (induction M using tm_mut with
  (P  := λ A M, PP A M)
  (P1 := λ A Q, PP A (tm_non Q))
  (P0 := λ A V, PP A (tm_val V))).

Ltac ind2 M := (
  induction M using tm_mut with
  (P  := λ A M, ?PP A M)
  (P1 := λ A Q, ?PP A (tm_non Q))
  (P0 := λ A V, ?PP A (tm_val V))).

Lemma sub_nop : ∀ A M (V : val A),
  sub (↑M) V = M.
Proof.
  ind M (λ A (M : tm A), ∀ V, sub (↑M) V = M); intros; auto.
  admit.
  (* set (P := _).  HOW TO CREATE A FRESH UNIFICATION VARIABLE?? *)
(* Qed. *)
Admitted.

(* Examples *)

Example tm_id : term := <{ λ 0 }>.
Example tm_ω  : term := <{ λ 0 0 }>.
Example tm_Ω  : term := <{ (λ 0 0) (λ 0 0) }>.

Example tm_e1 a z b : term := <{ <a <(S₀λ S₀λ 1 (0 z)) b>> }>.

Example tm_shift_id  e : term := <{ S₀λ 0 $ e }>.


Section Contexts.

  Context {A : Type}.
  Inductive J :=
  | J_app_l : tm A → J   (* [] M *)
  | J_app_r : val A → J  (* V [] *)
  | J_S0 : tm A → J      (* []$M *)
  .
  Inductive K :=
  | K_empty : K
  | K_JK : J → K → K
  | K_let : K → tm ^A → K
  .
  Inductive E :=
  | E_K : K → E → E
  | E_V : val A → E → E
  .
End Contexts.
Arguments J A : clear implicits.
Arguments K A : clear implicits.
Arguments E A : clear implicits.

Inductive C {A} :=
| C_E : E A → C → C
| C_app : non A → C → C
| C_reset : non A → C → C
| C_lam : @C ^A → C
| C_let : tm A → @C ^A → C
.
Arguments C A : clear implicits.
Global Hint Constructors J K E C : core.

Definition map_J {A B : Type} (f : A → B) (j : J A) : J B :=
  match j with
  | J_app_l M => J_app_l (map     f M)
  | J_app_r V => J_app_r (map_val f V)
  | J_S0    M => J_S0    (map     f M)
  end.

Instance Map_J : Functor J := { fmap := @map_J }.



Section Plugs.

  Local Coercion tm_val : val >-> tm.
  Local Coercion tm_non : non >-> tm.

  Definition plug_J {A} (j : J A) (M : tm A) : tm A :=
    match j with
    | J_app_l M' => non_app   M M'
    | J_app_r V  => non_app   V M
    | J_S0    M' => non_reset M M'
    end.

  Fixpoint plug_K {A} (k : K A) (M : tm A) : tm A :=
    match k with
    | K_empty => M
    | K_JK j k' => plug_J j (plug_K k' M)
    | K_let k' M' => plug_K k' <{ let M in M' }>
    end.

End Plugs.

Class Plug (C : Type → Type) :=
  { plug : ∀ {A}, C A → tm A → tm A
  }.

Instance Plug_J : Plug J := { plug := @plug_J }.
Instance Plug_K : Plug K := { plug := @plug_K }.

Notation "C [ M ]" := (plug C M)
  (in custom λc_dollar_scope at level 5, left associativity,
   M custom λc_dollar_scope at level 99).

(* Set Typeclasses Debug. *)


Section Reduction.

  (* Definition up {A} (V : val A) := tm_val (↑V). *)

  Local Coercion tm_val : val >-> tm.
  Local Coercion tm_non : non >-> tm.

  (* Inductive contr : term → term → Prop :=
  | contr_β_val : ∀ M   (V : value), contr <{ (λ M) V }> (sub M V)
  | contr_η_val : ∀     (V : value), contr <{ λ ↑{tm_val V} 0 }> V
  | contr_β_let : ∀ M   (V : value), contr <{ let V in M }> (sub M V)
  | contr_η_let : ∀ M              , contr <{ let M in 0 }> M
  | contr_β_dol : ∀   (W V : value), contr <{ V $ S₀ W }> <{ W V }>
  | contr_η_dol : ∀     (V : value), contr <{ S₀λ 0 ↑{tm_val V} }> V
  | contr_D_val : ∀   (W V : value), contr <{ V $    W }> <{ V W }>
  | contr_D_let : ∀ M N (V : value), contr <{ V $ let M in N }> <{ (λ ↑{tm_val V} $ N) $ M }>
  | contr_assoc : ∀ M N L          , contr <{ let (let L in M) in N }> <{ let L in let M in ↑N }>
  | contr_name  : ∀ (j : J _) (P : non _), contr <{ j[P] }> <{ let P in (↑j)[0] }>
  . *)

  Inductive contr : ∀ {A}, tm A → tm A → Prop :=
  | contr_β_val : ∀ A M   (V : val A), contr <{ (λ M) V }> (sub M V)
  | contr_η_val : ∀ A     (V : val A), contr <{ λ {↥V} 0 }> V
  | contr_β_let : ∀ A M   (V : val A), contr <{ let V in M }> (sub M V)
  | contr_η_let : ∀ A (M : tm A)     , contr <{ let M in 0 }> M
  | contr_β_dol : ∀ A   (W V : val A), contr <{ V $ S₀ W }> <{ W V }>
  | contr_η_dol : ∀ A     (V : val A), contr <{ S₀λ 0 {↥V} }> V
  | contr_D_val : ∀ A   (W V : val A), contr <{ V $    W }> <{ V W }>
  | contr_D_let : ∀ A M N (V : val A), contr <{ V $ let M in N }> <{ (λ {↥V} $ N) $ M }>
  | contr_assoc : ∀ A M N (L : tm A) , contr <{ let (let L in M) in N }> <{ let L in let M in {↑N} }>
  | contr_name  : ∀ A (j : J A) (P : non _), contr <{ j[P] }> <{ let P in {↑j}[0] }>
  .

  Definition reduces {A} := @step (tm A) contr.

End Reduction.


Section Similarity. (* from the Fig. 7 *)
  Local Coercion tm_val : val >-> tm.

  Reserved Notation "M '~' N" (at level 40).
  Inductive similar : ∀ {A : Type}, tm A → tm A → Prop :=
  | similar_var : ∀ A (v : A),
      <{ var v }> ~ <{ var v }>
  | similar_lam : ∀ A (M M' : tm ^A),
      <{   M }> ~ <{   M' }> →
      <{ λ M }> ~ <{ λ M' }>
  | similar_shift0 : ∀ A,
      <{ S₀ }> ~ (<{ S₀ }> : tm A)
  | similar_app : ∀ A (M M' N N' : tm A),
         M      ~    M'    → 
           N    ~       N' → 
      <{ M N }> ~ <{ M' N' }>
  | similar_let : ∀ A (M M' : tm A) (N N' : tm ^A), (* EXTRA *)
             M         ~        M'       → 
                  N    ~              N' → 
      <{ let M in N }> ~ <{ let M' in N' }>
  | similar_dollar : ∀ A (M M' N N' : tm A),
         M        ~    M'      → 
             N    ~         N' → 
      <{ M $ N }> ~ <{ M' $ N' }>
  | similar_start : ∀ A (V : val A),
      V ~ <{ λ {↥V} $ 0 }>
  | similar_step : ∀ A (V : val A) (W : val ^A) (j : J ^A) (k : K ^A),
      V ~ <{ λ (λ {↥W} $ {↑j}[0]) $ k[0] }> →
      V ~ <{ λ W $ j[k[0]] }>
  where "M '~' N" := (similar M N).

End Similarity.


Module Export Notations.
  Include Notations_Tm.
  
  Notation "M -->  N" := (contr   M N) (at level 50).
  (* Notation "M -->* N" := (@step term contr M N) (at level 50). *)
  Notation "M -->* N" := (reduces M N) (at level 50).
  Notation "M '~'  N" := (similar M N) (at level 50).

  Global Hint Constructors contr : core.
  Global Hint Unfold reduces : core.
  Global Hint Constructors similar : core.

End Notations.


Lemma contr_name_app_l : ∀ A (M : tm A) (P : non A),
  <{ {tm_non P} M }> --> <{ let {tm_non P} in 0 {↑M} }>.
Proof.
  intros; apply (contr_name A (J_app_l M) P).
  Qed.

Lemma contr_name_app_r : ∀ A (V : val A) (P : non A),
  <{ {tm_val V} {tm_non P} }> --> <{ let {tm_non P} in {↥V} 0 }>.
Proof.
  intros; apply (contr_name A (J_app_r V) P).
  Qed.

Lemma contr_name_S0 : ∀ A (M : tm A) (P : non A),
  <{ {tm_non P} $ M }> --> <{ let {tm_non P} in 0 $ {↑M} }>.
Proof.
  intros; apply (contr_name A (J_S0 M) P).
  Qed.
(* Instantiations of contr_name for every case of J *)
Global Hint Resolve contr_name_app_l contr_name_app_r contr_name_S0 : core.

Lemma value_reduces : ∀ A (V : val A) M,
  tm_val V --> M →
  ∃ (V' : val _),
    M = tm_val V' /\
    tm_val V = <{ λ {↥V'} 0 }>.
Proof.
  intros. dependent induction H; try inversion Heqt.
  - exists V0; split; auto.
  - destruct j; cbn in *; inversion x.
Qed.

Lemma contr_app_l : ∀ A M (V : val A),
  M --> tm_val V → ∀ N,
  <{ M N }> -->* <{ {tm_val V} N }>.
Proof.
  intros.
  destruct M.
  apply value_reduces in H as [V' [HM' H]]; subst. rewrite H. inv HM'.
  destruct N. rename H into H2.
  econstructor. apply contr_β_val. simpl.
  set (H := contr_β_val A <{ {↥V'} 0 }> v0).
  admit.
  (* apply H. cbn in *.
  apply contr_name_app_r.
  eapply contr_name. *)
Admitted.

Lemma reduces_app_l : ∀ A M (V : val A),
  M -->* tm_val V → ∀ N,
  <{ M N }> -->* <{ {tm_val V} N }>.
Proof.
  intros. induction H; auto.
  econstructor.
  destruct M.
  - apply value_reduces in H as [V' [HM' H]]; subst. rewrite H.
Admitted.

Lemma similar_refl : ∀ A (M : tm A), M ~ M.
Proof.
  apply (tm_mut_ _); auto.
Qed.
Global Hint Resolve similar_refl : core.

(* Lemma aux : ∀ A (M N : tm A), M ~ N → A=Void → N -->* M.
Proof.
  intros. induction H.
Qed. *)


Lemma similarity_is_NOT_reasonable :
  ~ (∀ A (M N : tm A), M ~ N → N -->* M).
Proof.
  intro H.
  specialize (H Void <{ λ 0 }> <{ λ λ 1 $ 0 }> (similar_lam _ _ _ (similar_start _ _))).
  inv H. inv H. destruct j; discriminate x.
Qed.

Lemma similarity_is_reasonable : 
  (∀ A (M N : tm A), M = N → M ~ N) /\
  (∀ A (M N : tm A), M ~ N → N -->* M).
Proof.
  split; intros.
  - rewrite H. apply similar_refl.
  - induction H; auto.
    admit.
    Focus 4.
    (* econstructor. apply contr_η_val. constructor.  *)
Admitted.

