Require Export Shift0Dollar.Simplified.Terms.

Inductive redex {A} :=
| redex_beta     : tm ^A → val A → redex (* (λ e) v *)
| redex_dollar   : val A → val A → redex (* v v' *)
| redex_let_beta : val A → tm ^A → redex (* let x = v in e *)

| redex_shift    : val A → K A → val A → redex (* w $ K[S₀ v] *)
.
Arguments redex A : clear implicits.

Definition redex_to_term {A} (r : redex A) : tm A := 
  match r with
  | redex_beta   e v => <{ (λ e) v }>
  | redex_dollar v v' => <{ v $ v' }>
  | redex_let_beta v e => <{ let v in e }>
  | redex_shift w k v => <{ w $ k [S₀ v] }>
  end.
Coercion redex_to_term : redex >-> tm.

Lemma inj_redex : ∀ {A} (r r' : redex A),
  redex_to_term r = redex_to_term r' → r = r'.
Proof.
  intros; destruct r, r'; cbn in *; inversion H; clear H; subst; auto.
Admitted.

(* ANCHOR Decompose
 *)
 Fixpoint decompose (e : tm ␀) : dec redex ␀ :=
    match e with
    | tm_val v => dec_value v
    | tm_non p => decomposeP p
    end
  with decomposeP (p : non ␀) : dec redex ␀ :=
    match p with
    | <{ v v' }> =>
      match v with
      | <{ var a }> => from_void a
      | <{ S₀ }>    => dec_stuck K_nil v'
      | <{ λ e }>   => dec_redex K_nil T_nil (redex_beta e v')
      end
    | <{ w $ e }> =>
      match decompose e with
      | dec_stuck k v   => dec_redex K_nil T_nil (redex_shift w k v) (* w $ k[S₀ v] *)
      | dec_redex k t r => dec_redex K_nil (T_cons w k t) r          (* w $ k[t[r]] *)
      | dec_value v     => dec_redex K_nil T_nil (redex_dollar w v)  (* w $ v *)
      end
    | <{ let e in e' }> =>
      match decompose e with
      | dec_stuck k v   => dec_stuck (K_let k e') v (* let k[S₀ v] in e' *)
      | dec_redex k t r => dec_redex (K_let k e') t r          (* let k[t[r]] in e' *)
      | dec_value v     => dec_redex K_nil T_nil (redex_let_beta v e')  (* let v       in e' *)
      end
    end.


(* ANCHOR Evaluation
 *)
Definition contract (r : redex ␀) : tm ␀ :=
    match r with
    (* (λ x. e) v  ~>  e [x := v] *)
    | redex_beta e v => <{ e [0 := v] }>
  
    (* w $ v  ~>  w v *)
    | redex_dollar v1 v2 => <{ v1 v2 }>
    
    (* let x = v in e  ~>  e [x := v] *)
    | redex_let_beta v e => <{ e [0 := v] }>
  
    (* w $ K[S₀ v]  ~>  v (λ x. w $ K[x]) *)
    | redex_shift w k v  => <{ v (λ ↑w $ ↑k[0]) }>
    end.

Definition optional_step e :=
  match decompose e with
  | dec_redex k t r => Some <{ k[t[{contract r}]] }>
  | _ => None
  end.

Reserved Notation "e1 ~> e2" (at level 40).
Inductive contr : tm ␀ → tm ␀ → Prop :=
| contr_tm : ∀ r, redex_to_term r ~> contract r
where "e1 ~> e2" := (contr e1 e2).
Global Hint Constructors contr : core.

Reserved Notation "e1 --> e2" (at level 40).
Inductive step : tm ␀ → tm ␀ → Prop :=
| step_tm : ∀ (k : K ␀) (t : T ␀) (e1 e2 : tm ␀), e1 ~> e2 → <{ k[t[e1]] }> --> <{ k[t[e2]] }>
where "e1 --> e2" := (step e1 e2).
Global Hint Constructors step : core.

Notation "e1 -->* e2" := (multi step e1 e2) (at level 40).

Lemma step_contr : ∀ {e1 e2},
  e1 ~> e2 →
  e1 --> e2.
Proof.
  intros.
  apply (step_tm K_nil T_nil e1 e2).
  assumption.
Qed.
Lemma multi_contr : ∀ {e1 e2},
  e1 ~> e2 →
  e1 -->* e2.
Proof.
  intros. apply (multi_step _ _ _ _ (step_contr H)); auto.
Qed.
Lemma multi_contr_multi : ∀ {e1 e2 e3},
  e1 ~> e2 →
  e2 -->* e3 →
  e1 -->* e3.
Proof.
  intros. eapply multi_step; try eapply (step_tm K_nil T_nil); cbn; eassumption.
Qed.
Definition contr_beta : ∀ e (v : val ␀), <{ (λ e) v }> ~> <{ e [ 0 := v ] }> := λ e v, contr_tm (redex_beta e v).
Definition contr_dollar : ∀ (v1 v2 : val ␀), <{ v1 $ v2 }> ~> <{ v1 v2 }> := λ v1 v2, contr_tm (redex_dollar v1 v2).
Definition contr_let_beta : ∀ (v : val ␀) e, <{ let v in e }> ~> <{ e [ 0 := v ] }> := λ v e, contr_tm (redex_let_beta v e).
Definition contr_shift : ∀ (w : val ␀) (k : K ␀) (v : val ␀), <{ w $ k [S₀ v] }> ~> <{ v (λ ↑w $ ↑k[0]) }> := λ w k v, contr_tm (redex_shift w k v).
Global Hint Resolve step_contr contr_beta contr_dollar contr_shift contr_let_beta : core.

Lemma deterministic_contr : ∀ e e1 e2,
  e ~> e1 →
  e ~> e2 →
  e1 = e2.
Proof.
  intros e e1 e2 H1 H2.
  inversion H1; clear H1; subst. 
  inversion H2; clear H2; subst.
  apply inj_redex in H0; subst; reflexivity.
Qed.

Lemma redex_when_contr : ∀ e1 e2,
  e1 ~> e2 →
  ∃ r1, e1 = redex_to_term r1.
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

Fixpoint eval i e :=
  match i with
  | 0 => e
  | S j =>
    match optional_step e with
    | Some e => eval j e
    | None => e
    end
  end.

Section Examples.
  Definition _id : val ␀ := <{ λ 0 }>.
  Definition _const : val ␀ := <{ λ λ 1 }>.

  Compute (eval 10 <{ _id $ _const $ S₀ (λ 0) }>).
  Compute (eval 10 <{ _const $ _id $ S₀ (λ 0) }>).

  Definition _e1 : tm ␀ := <{
    _id $
      let λ 0 0 in
      let S₀ 0 in
      0
  }>.
  Compute (eval 0 _e1).
  Compute (eval 1 _e1).
  Compute (eval 2 _e1).
  Compute (eval 3 _e1).
  Compute (eval 5 _e1).
  Compute (eval 9 _e1).
  
End Examples.