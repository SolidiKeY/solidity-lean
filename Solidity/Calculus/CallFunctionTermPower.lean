import Solidity.Calculus.CallFunctionLeaf

/-! # Evaluation transport for actual expanded summary terms
Instantiation is the existing typed symbolic-environment substitution. Failure
is retained through a checked strict-read certificate, never a new user premise.
-/
namespace Solidity.CallFunctionTermPower
open CallFunctionTable CallFunctionLeaf
variable {C : Contract} {Γ Δ : Ctx}

/-- Substitute an actual argument while preserving the original captured locals. -/
def inst? (h : Thin Γ Δ) (base : Tm C (.val .uint :: Γ) (.val .uint))
    (arg : Tm C Δ (.val .uint)) : Option (Tm C Δ (.val .uint)) :=
  base.substE (show SEnv C Δ (.val .uint :: Γ) from ((arg, false), SEnv.idAt Γ (fun i => i.wk h)))

/-- The argument is evaluated before the callee result. On failure its strict
read certificate prevents substitution from silently dropping that failure. -/
theorem eval_inst (h : Thin Γ Δ) (base : Tm C (.val .uint :: Γ) (.val .uint))
    (arg out : Tm C Δ (.val .uint)) (hs : base.strictReads 0 = true)
    (hi : inst? h base arg = some out) (σ : State C Δ) :
    out.eval σ = (arg.eval σ).bind (fun x => base.eval ((σ.thin h).push (t := .val .uint) x)) := by
  have hsub : base.substE (show SEnv C Δ (.val .uint :: Γ) from ((arg, false), SEnv.idAt Γ (fun i => i.wk h))) = some out := hi
  cases ha : arg.eval σ with
  | some a =>
    have hE : SEnv.Ev σ Γ (SEnv.idAt Γ (fun i => i.wk h)) (σ.thin h).env := by
      apply SEnv.Ev_idAt
      intro p i
      change TEnv.get (i.wk h) σ.env = TEnv.get i (TEnv.thin h σ.env)
      rw [TEnv.get_thin_wk]
    exact Tm.eval_substE_val (σ₀ := σ)
      (τ := (σ.thin h).push (t := .val .uint) a) (t := base) (t' := out)
      (E := (show SEnv C Δ (.val .uint :: Γ) from
        ((arg, false), SEnv.idAt Γ (fun i => i.wk h))))
      rfl (show SEnv.Ev σ (.val .uint :: Γ)
      (show SEnv C Δ (.val .uint :: Γ) from ((arg, false), SEnv.idAt Γ (fun i => i.wk h)))
      (((σ.thin h).push (t := .val .uint) a).env) from ⟨ha, hE⟩) hsub
  | none =>
    change out.eval σ = none
    apply Classical.byContradiction
    intro hn
    have hd : arg.eval σ ≠ none := Tm.strictReads_eval
      (E := (show SEnv C Δ (.val .uint :: Γ) from ((arg, false), SEnv.idAt Γ (fun i => i.wk h))))
      (.here : Idx (.val .uint :: Γ) (.val .uint)) base hs hsub hn
    exact hd ha

/-- Existing summary value-only/no-push certificates transport through actual
instantiation. They are established internally by a source/summary producer. -/
theorem pushFree_inst (h : Thin Γ Δ) (base : Tm C (.val .uint :: Γ) (.val .uint))
    (arg out : Tm C Δ (.val .uint)) (hv : base.valOnly = true)
    (ha : arg.pushFree = true) (hi : inst? h base arg = some out) :
    out.pushFree = true := by
  apply Tm.substE_pushFree (E := (show SEnv C Δ (.val .uint :: Γ) from ((arg, false), SEnv.idAt Γ (fun i => i.wk h)))) ?_ base hv hi
  intro p i
  cases i with
  | here => exact ha
  | there i =>
    change ((SEnv.idAt (C := C) Γ (fun i => i.wk h)).get i).1.pushFree = true
    rw [SEnv.get_idAt]
    rfl

/-- Actual repeated instantiation, kept only as a source/old-summary
certificate. The emitted shared leaf does not contain this expanded term. -/
def expanded? (base : Tm C (.val .uint :: Γ) (.val .uint))
    (x : Idx Γ (.val .uint)) : Nat → Option (Tm C Γ (.val .uint))
  | 0 => some (.pvV x)
  | n+1 => (expanded? base x n).bind (inst? .refl base)

/-- Sequential repeated evaluation, preserving the first failed application. -/
def iterate (f : Key → Option Key) : Nat → Key → Option Key
  | 0, x => some x
  | n+1, x => (iterate f n x).bind f

/-- Every successfully constructed old summary evaluates exactly as the actual
base at the unchanged caller state, with all intermediate failures preserved. -/
theorem eval_expanded (base : Tm C (.val .uint :: Γ) (.val .uint))
    (x : Idx Γ (.val .uint)) (hs : base.strictReads 0 = true)
    (n : Nat) (out : Tm C Γ (.val .uint)) (he : expanded? base x n = some out)
    (σ : State C Γ) :
    out.eval σ = iterate (fun a => base.eval (σ.push (t := .val .uint) a)) n (σ.getV x) := by
  induction n generalizing out with
  | zero =>
    cases he
    rfl
  | succ n ih =>
    have hh : (expanded? base x n).bind (inst? .refl base) = some out := he
    obtain ⟨prev, hp, hi⟩ := Option.bind_eq_some_iff.mp hh
    rw [eval_inst .refl base prev out hs hi σ, ih prev hp]
    rfl

/-- Successful actual instantiation preserves the producer no-push property. -/
theorem pushFree_expanded (base : Tm C (.val .uint :: Γ) (.val .uint))
    (x : Idx Γ (.val .uint)) (hv : base.valOnly = true)
    (n : Nat) (out : Tm C Γ (.val .uint)) (he : expanded? base x n = some out) :
    out.pushFree = true := by
  induction n generalizing out with
  | zero => cases he; rfl
  | succ n ih =>
    have hh : (expanded? base x n).bind (inst? .refl base) = some out := he
    obtain ⟨prev, hp, hi⟩ := Option.bind_eq_some_iff.mp hh
    exact pushFree_inst .refl base prev out hv (ih prev hp) hi

/-- Sequential application counts add with exactly Option's evaluation order. -/
theorem iterate_add (f : Key → Option Key) (n p : Nat) (x : Key) :
    iterate f (n+p) x = (iterate f n x).bind (iterate f p) := by
  induction p with
  | zero =>
    simp only [Nat.add_zero]
    cases iterate f n x <;> rfl
  | succ p ih =>
    change (iterate f (n+p) x).bind f = (iterate f n x).bind (iterate f (p+1))
    rw [ih, Option.bind_assoc]
    rfl

/-- The actual repeated-squaring family is exactly 2^k ordered applications. -/
theorem power_iterate (f : Key → Option Key) (k : Nat) :
    power f k = iterate f (2^k) := by
  funext x
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [power_succ]
    change (power f k x).bind (fun a => power f k a) = _
    simp only [ih]
    rw [Nat.pow_succ]
    have hn : 2^k * 2 = 2^k + 2^k := by omega
    rw [hn, iterate_add]

/-- A concrete old-summary expansion certificate connects its actual evaluation
to the shared family's operational semantics at every typed caller state. -/
theorem eval_expanded_power (base : Tm C (.val .uint :: Γ) (.val .uint))
    (x : Idx Γ (.val .uint)) (hs : base.strictReads 0 = true)
    (k : Nat) (out : Tm C Γ (.val .uint))
    (he : expanded? base x (2^k) = some out) (σ : State C Γ) :
    out.eval σ = power (fun a => base.eval (σ.push (t := .val .uint) a)) k (σ.getV x) := by
  rw [eval_expanded base x hs (2^k) out he σ, power_iterate]

/-- The complete emitted shared leaf is equivalent to its actual old expanded
assignment, for both modalities and every caller state/post. All certificates
are internal producer checks; none become new user validity premises. -/
theorem holds_assignment (m : Modality) (tableName inputName resultName : Var)
    (base : Tm C (.val .uint :: Γ) (.val .uint))
    (hp : base.pushFree = true) (hv : base.valOnly = true) (hs : base.strictReads 0 = true)
    (k : Nat) (j x : Idx Γ (.val .uint)) (out : Tm C Γ (.val .uint))
    (he : expanded? base x (2^k) = some out) (φ : Fml C Γ) (σ : State C Γ) :
    holds σ (leaf m tableName inputName resultName base k j x φ) ↔
      holds σ (.upd m (Upd.nil.snoc (.local j (.val out))) φ) := by
  have hev : out.eval σ = power (fun a => base.eval (σ.push (t := .val .uint) a)) k
      (σ.getV x) := eval_expanded_power base x hs k out he σ
  have hpf : out.pushFree = true := pushFree_expanded base x hv (2^k) out he
  have hc : holds σ (.upd m (Upd.nil.snoc (.local j (.val out))) φ) ↔
      holds σ (CallResultRestore.leaf m resultName .refl j out φ) :=
    ⟨fun hh => CallResultCapture.complete resultName j out φ σ hh,
      fun hh => CallResultCapture.sound resultName j out φ σ hh⟩
  rw [holds_leaf m tableName inputName resultName base hp k j x φ σ, hc, ← hev]
  cases ho : out.eval σ with
  | some v =>
    rw [CallResultRestore.holds_leaf_of_eval m resultName .refl j out φ σ v ho]
    rfl
  | none =>
    rw [CallResultRestore.holds_leaf_of_none m resultName .refl j out φ σ ho,
      CallFunctionOperationalBase.capture_noExh resultName out hpf σ]
    change m.onHalt ↔ (m.onHalt ∨ false = true)
    simp only [Bool.false_eq_true, or_false]

/-- A successful concrete summary certificate rules out both divergence and
exhaustion of the actual call, by the existing symbolic-run theorem. -/
theorem summary_ends {ps Γf : Ctx} {r : Var} {j : Idx Γ (.val .uint)}
    {args : Args C Γ ps} {body : Prog C ([.val .uint] ++ ps) Γf} {U : Upd C Γ Γ}
    (h : CallRet.summary? args (.val .uint r (some j)) body = some U) (σ : State C Γ) :
    (TRun.call args (.val .uint r (some j)) body.ext body.runR σ).Ends := by
  have hh : (if body.hasCall then
      (CallRet.sumOf body.ext (body.sym _ (SEnv.id _))).bind fun R =>
        if Tm.sumGate body R then
          (Args.sym (SEnv.id Γ) args).bind fun θ =>
            (Tm.substE (Γ₀ := Γ) (Δ := .val .uint :: ps)
              ((Tm.app0 (.lit (PrimTy.dflt .uint)), false), θ) R).map fun t =>
                Upd.nil.snoc (.local j (.val t))
        else Option.none
      else Option.none) = some U := h
  split at hh
  · obtain ⟨R, hR, h₁⟩ := Option.bind_eq_some_iff.mp hh
    split at h₁
    · obtain ⟨θ, hθ, h₂⟩ := Option.bind_eq_some_iff.mp h₁
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h₂
      rcases CallRet.sym_call (Prog.sym_sound body) hR hθ ht
          (τ := σ) rfl (SEnv.Ev_id σ) with
        ⟨v, o, ho, hv, hg, he⟩ | ⟨hr, hn⟩
      · rw [ho]
        constructor <;> intro hh <;> cases hh
      · rw [hr]
        constructor <;> intro hh <;> cases hh
    · cases h₁
  · cases hh

/-- A checked actual returning summary determines the whole returned caller,
including globals, heap and every old local. No full source-run reduction. -/
theorem run_of_summary_eval {ps Γf : Ctx} (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.val .uint] ++ ps) Γf) (j : Idx Γ (.val .uint))
    (out : Tm C Γ (.val .uint))
    (hc : CallRet.summary? args (.val .uint r (some j)) body =
      some (Upd.nil.snoc (.local j (.val out)))) (σ : State C Γ)
    (v : Key) (hv : out.eval σ = some v) :
    Stmt.runSt σ (.call f args (.val .uint r (some j)) body) = .ok (σ.setLocal j v) := by
  have ha : TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV))
      (TRun.call args (.val .uint r (some j)) body.ext body.runR σ)
      ((Upd.nil.snoc (.local j (.val out))).applyP σ) :=
    (CallRet.summary_agrees hc σ).1
  have he : (TRun.call args (.val .uint r (some j)) body.ext body.runR σ).Ends :=
    summary_ends hc σ
  change (TRun.call args (.val .uint r (some j)) body.ext body.runR σ).map (·.st) = _
  cases hr : TRun.call args (.val .uint r (some j)) body.ext body.runR σ with
  | error e =>
    rw [hr] at ha he
    cases e with
    | panic => exact ha.elim
    | revertWith _ => exact ha.elim
    | diverge => exact (he.1 rfl).elim
    | exhausted => exact (he.2 rfl).elim
    | revert =>
      change (Upd.nil.snoc (.local j (.val out))).applyP σ = none at ha
      rw [applyP_local1, Rhs.eval_val_sum, hv] at ha
      cases ha
  | ok o =>
    rw [hr] at ha
    change (Upd.nil.snoc (.local j (.val out))).applyP σ = some (o.st.glob, o.st.locV) at ha
    rw [applyP_local1, Rhs.eval_val_sum, hv] at ha
    have hp : (σ.glob, σ.locV.set j v) = (o.st.glob, o.st.locV) := Option.some.inj ha
    have hg : o.st.glob = (σ.setLocal j v).glob := (congrArg Prod.fst hp).symm
    have hl : o.st.locV = (σ.setLocal j v).locV := by
      rw [State.locV_setLocal]
      exact (congrArg Prod.snd hp).symm
    have hs : o.st = σ.setLocal j v := by
      apply State.eq_of_readsAs
      refine ⟨hg, ?_⟩
      intro u i
      change o.st.locV u i = (σ.setLocal j v).locV u i
      exact congrFun (congrFun hl u) i
    change (.ok o.st : TRes (State C Γ)) = .ok (σ.setLocal j v)
    exact congrArg Except.ok hs

/-- Exact source observation, including failure, follows from the actual
summary equation, not just a one-way validity implication. -/
theorem holds_call {ps Γf : Ctx} (m : Modality)
    (tableName inputName resultName : Var) (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.val .uint] ++ ps) Γf)
    (base : Tm C (.val .uint :: Γ) (.val .uint))
    (hp : base.pushFree = true) (hv : base.valOnly = true) (hs : base.strictReads 0 = true)
    (k : Nat) (j x : Idx Γ (.val .uint)) (out : Tm C Γ (.val .uint))
    (he : expanded? base x (2^k) = some out)
    (hc : CallRet.summary? args (.val .uint r (some j)) body =
      some (Upd.nil.snoc (.local j (.val out)))) (φ : Fml C Γ) (σ : State C Γ) :
    holds σ (leaf m tableName inputName resultName base k j x φ) ↔
      m.afterRunTR (holds · φ)
        (Stmt.runSt σ (.call f args (.val .uint r (some j)) body)) := by
  rw [holds_assignment m tableName inputName resultName base hp hv hs k j x out he φ σ]
  obtain ⟨ha, hd, hpf⟩ := CallRet.summary_agrees hc σ
  exact Upd.afterT_run_iff σ (.call f args (.val .uint r (some j)) body)
    (Upd.nil.snoc (.local j (.val out))) ha (summary_ends hc σ)
    (Upd.exh_of_pushFree hpf) m (holds · φ)

/-- The concrete existing source-summary equation and actual term-expansion
certificate transport a shared leaf to the real call, arbitrary rest/frames
included. Certificates are proved internally; no source theorem is assumed. -/
theorem sound_call {ps Γf Γ₁ Γ₀ : Ctx} (m : Modality)
    (tableName inputName resultName : Var) (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.val .uint] ++ ps) Γf)
    (base : Tm C (.val .uint :: Γ) (.val .uint))
    (hp : base.pushFree = true) (hv : base.valOnly = true) (hs : base.strictReads 0 = true)
    (k : Nat) (j x : Idx Γ (.val .uint)) (out : Tm C Γ (.val .uint))
    (he : expanded? base x (2^k) = some out)
    (hc : CallRet.summary? args (.val .uint r (some j)) body =
      some (Upd.nil.snoc (.local j (.val out))))
    (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) (σ : State C Γ)
    (hh : holds σ (leaf m tableName inputName resultName base k j x (.modalK m ω κ φ))) :
    holds σ (.modal m (.cons (.call f args (.val .uint r (some j)) body) ω) κ φ) := by
  have hu : holds σ (.upd m (Upd.nil.snoc (.local j (.val out))) (.modalK m ω κ φ)) :=
    (holds_assignment m tableName inputName resultName base hp hv hs k j x out he
      (.modalK m ω κ φ) σ).mp hh
  exact (Premise.sound_callSummary (m := m) f args .uint r (some j) body hc σ).sound ω κ φ hu

end Solidity.CallFunctionTermPower
