Require Export Shift0Dollar.Simplified.Terms.

(* ANCHOR Contexts
 *)
Inductive T' {A} :=
| T_nil'  : T'
| T_cons' : val A → T' → T'  (* v $ T' *)
.
Arguments T' A : clear implicits.
 
Fixpoint plugT' {A} (trail : T' A) e :=
  match trail with
  | T_nil' => e
  | T_cons' v t => <{ v $ {plugT' t e} }>
  end.
Instance PlugT' : Plug T' := @plugT'.


Inductive redex' {A} :=
| redex_beta'     : tm ^A → val A → redex'        (* (λ e) v *)
| redex_dollar'   : val A → val A → redex'        (* v v' *)
| redex_let_beta' : val A → tm ^A → redex'        (* let x = v in e *)

| redex_shift'    : val A → val A → redex'        (* w $ S₀ v *)
| redex_dol_let'  : val A → tm A → tm ^A → redex' (* w $ let e in e' *)
.
Arguments redex' A : clear implicits.

Definition redex_to_term' {A} (r : redex' A) : tm A := 
  match r with
  | redex_beta'   e v => <{ (λ e) v }>
  | redex_dollar' v v' => <{ v $ v' }>
  | redex_let_beta' v e => <{ let v in e }>
  | redex_shift' w v => <{ w $ S₀ v }>
  | redex_dol_let' w e e' => <{ w $ let e in e' }>
  end.
Coercion redex_to_term' : redex' >-> tm.

Lemma inj_redex' : ∀ {A} (r r' : redex' A),
  redex_to_term' r = redex_to_term' r' → r = r'.
Proof.
  intros; destruct r, r'; cbn in *; inversion H; clear H; subst; auto.
Admitted.

(* ANCHOR Decompose
 *)
(* Decompose `w $ e` term, which is never stuck and always returns `dec_redex` with an empty context `K` *)
Fixpoint decompose_delimited (w : val ␀) (e : tm ␀) : (T' ␀ * redex' ␀) :=
  match e with
  | tm_val v => (T_nil', redex_dollar' w v)  (* w $ v *)
  | tm_non p => decompose_delimitedP w p
  end
with decompose_delimitedP (w : val ␀) (p : non ␀) : (T' ␀ * redex' ␀) :=
  match p with
  | <{ v v' }> =>
    match v with
    | <{ var a }> => from_void a
    | <{ S₀ }>    => (          T_nil', redex_shift' w v')                      (* w $ S₀ v' *)
    | <{ λ e }>   => (T_cons' w T_nil', redex_beta'  e v')                      (* w $ (λ e) v' *)
    end
  | <{ w' $ e }> => let (t, r) := decompose_delimited w' e in (T_cons' w t, r)  (* w $ w' $ e *)
  | <{ let e in e' }> => (T_nil', redex_dol_let' w e e')                        (* w $ let e in e' *)
  end.

Fixpoint decompose' (e : tm ␀) : dec T' redex' ␀ :=
  match e with
  | tm_val v => dec_value v
  | tm_non p => decomposeP' p
  end
with decomposeP' (p : non ␀) : dec T' redex' ␀ :=
  match p with
  | <{ v v' }> =>
    match v with
    | <{ var a }> => from_void a
    | <{ S₀ }>    => dec_stuck K_nil v'                                         (* S₀ v' *)
    | <{ λ e }>   => dec_redex K_nil T_nil' (redex_beta' e v')                  (* (λ e) v' *)
    end
  | <{ w $ e }> => let (t, r) := decompose_delimited w e in dec_redex K_nil t r (* w $ e *)
  | <{ let e in e' }> =>
    match decompose' e with
    | dec_stuck k v   => dec_stuck (K_let k e') v                               (* let k[S₀ v] in e' *)
    | dec_redex k t r => dec_redex (K_let k e') t r                             (* let k[t[r]] in e' *)
    | dec_value v     => dec_redex K_nil T_nil' (redex_let_beta' v e')          (* let v       in e' *)
    end
  end.


(* ANCHOR Evaluation
 *)
Definition contract' (r : redex' ␀) : tm ␀ :=
    match r with
    (* (λ x. e) v  ~>  e [x := v] *)
    | redex_beta' e v => <{ e [0 := v] }>
  
    (* w $ v  ~>  w v *)
    | redex_dollar' v1 v2 => <{ v1 v2 }>
    
    (* let x = v in e  ~>  e [x := v] *)
    | redex_let_beta' v e => <{ e [0 := v] }>
  
    (* w $ S₀ v  ~>  v w *)
    (* | redex_shift' w v  => <{ v w }> *)

    (* w $ S₀ v  ~>  v (λ x. w $ x) *)
    | redex_shift' w v  => <{ v (λ ↑w $ 0) }>

    (* w $ let x = e in e'  ~>  (λ x. w $ e') $ e *)
    | redex_dol_let' w e e' => <{ (λ ↑w $ e') $ e }>
    end.

Definition optional_step' e :=
  match decompose' e with
  | dec_redex k t r => Some <{ k[t[{contract' r}]] }>
  | _ => None
  end.

Reserved Notation "e1 ~>' e2" (at level 40).
Inductive contr' : tm ␀ → tm ␀ → Prop :=
| contr_tm' : ∀ r, redex_to_term' r ~>' contract' r
where "e1 ~>' e2" := (contr' e1 e2).
Global Hint Constructors contr' : core.

Reserved Notation "e1 -->' e2" (at level 40).
Inductive step' : tm ␀ → tm ␀ → Prop :=
| step_tm' : ∀ (k : K ␀) (t : T' ␀) (e1 e2 : tm ␀), e1 ~>' e2 → <{ k[t[e1]] }> -->' <{ k[t[e2]] }>
where "e1 -->' e2" := (step' e1 e2).
Global Hint Constructors step' : core.

Notation "e1 -->'* e2" := (multi step' e1 e2) (at level 40).

Lemma step_contr' : ∀ {e1 e2},
  e1 ~>' e2 →
  e1 -->' e2.
Proof.
  intros.
  apply (step_tm' K_nil T_nil' e1 e2).
  assumption.
Qed.
Lemma multi_contr' : ∀ {e1 e2},
  e1 ~>' e2 →
  e1 -->'* e2.
Proof.
  intros. apply (multi_step _ _ _ _ (step_contr' H)); auto.
Qed.
Lemma multi_contr_multi' : ∀ {e1 e2 e3},
  e1 ~>' e2 →
  e2 -->'* e3 →
  e1 -->'* e3.
Proof.
  intros. eapply multi_step; try eapply (step_tm' K_nil T_nil'); cbn; eassumption.
Qed.
Definition contr_beta' : ∀ e (v : val ␀), <{ (λ e) v }> ~>' <{ e [ 0 := v ] }> := λ e v, contr_tm' (redex_beta' e v).
Definition contr_dollar' : ∀ (v1 v2 : val ␀), <{ v1 $ v2 }> ~>' <{ v1 v2 }> := λ v1 v2, contr_tm' (redex_dollar' v1 v2).
Definition contr_let_beta' : ∀ (v : val ␀) e, <{ let v in e }> ~>' <{ e [ 0 := v ] }> := λ v e, contr_tm' (redex_let_beta' v e).
(* Definition contr_shift' : ∀ (w : val ␀) (v : val ␀), <{ w $ S₀ v }> ~>' <{ v w }> := λ w v, contr_tm' (redex_shift' w v). *)
Definition contr_shift' : ∀ (w : val ␀) (v : val ␀), <{ w $ S₀ v }> ~>' <{ v (λ ↑w $ 0) }> := λ w v, contr_tm' (redex_shift' w v).
Definition contr_dol_let' : ∀ (w : val ␀) e e', <{ w $ let e in e' }> ~>' <{ (λ ↑w $ e') $ e }> := λ w e e', contr_tm' (redex_dol_let' w e e').
Global Hint Resolve step_contr' contr_beta' contr_dollar' contr_shift' contr_dol_let' contr_let_beta' : core.

Lemma deterministic_contr' : ∀ e e1 e2,
  e ~>' e1 →
  e ~>' e2 →
  e1 = e2.
Proof.
  intros e e1 e2 H1 H2.
  inversion H1; clear H1; subst. 
  inversion H2; clear H2; subst.
  apply inj_redex' in H0; subst; reflexivity.
Qed.

Lemma redex_when_contr' : ∀ e1 e2,
  e1 ~>' e2 →
  ∃ r1, e1 = redex_to_term' r1.
Proof.
  intros. inversion H; clear H; subst.
  exists r; auto.
Qed.

(* Lemma deterministic_step : ∀ e e1 e2,
  e --> e1 →
  e --> e2 →
  e1 = e2.
Proof.
  intros e e1 e2 H1 H2.
  inversion H1; clear H1; subst. 
  inversion H2; clear H2; subst.
  apply redex_when_contr in H as HH; destruct HH as [r0 HH]; subst.
  apply redex_when_contr in H1 as HH; destruct HH as [r1 HH]; subst.
  assert (dec_redex k0 t0 r1 = dec_redex k t r0) as Hktr.
  { repeat rewrite <- decompose_plug_redex. f_equal; assumption. }
  inversion Hktr; clear Hktr; subst.
  repeat f_equal.
  apply (deterministic_contr r0); assumption.
Qed. *)

Fixpoint eval' i e :=
  match i with
  | 0 => e
  | S j =>
    match optional_step' e with
    | Some e => eval' j e
    | None => e
    end
  end.

Section Examples.
  Definition _id : val ␀ := <{ λ 0 }>.
  Definition _const : val ␀ := <{ λ λ 1 }>.

  Compute (eval' 10 <{ _id $ _const $ S₀ (λ 0) }>).
  Compute (eval' 10 <{ _const $ _id $ S₀ (λ 0) }>).

  Definition _e1 : tm ␀ := <{
    _id $
      let λ 0 0 in
      let S₀ 0 in
      0
  }>.
  Compute (eval' 0 _e1).
  Compute (eval' 1 _e1).
  Compute (eval' 2 _e1).
  Compute (eval' 3 _e1).
  Compute (eval' 5 _e1).
  Compute (eval' 9 _e1).
  
End Examples.