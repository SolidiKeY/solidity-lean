import Solidity.Semantics.RunWk
import Solidity.Semantics.RunFrame
import Solidity.Syntax.Join

/-!
# Deferred operand evaluation

An operand retains a scoped program prefix and a source in its final context.
Running it snapshots the source before dropping its temporary locals; caller
writes and heap growth survive. Weakening protects the captured getter alias
without restricting what the prefix may do.

The capture agreement is over actual typed statements: a getter call, a storage
alias declaration, and a scoped prefix followed by the existing push. Programs
remain interpreted. This module supplies ordinary-run laws only; callback
composition over `ExecP` is in `Semantics/DeferredCallback.lean`. Exact
direct/captured callback agreement is in `Semantics/DeferredCorrespondence.lean`.
`Semantics/NativeDeferred.lean` connects this representation to the native
receiver statement used by source elaboration and the calculus.
-/

namespace Solidity.DeferredSource

variable {C : Contract} {Γ Δ : Ctx} {T : Ty}

/-- A typed prefix and its final source. Its locals are private to evaluation. -/
structure Operand (C : Contract) (Γ : Ctx) (T : Ty) where
  tailCtx : Ctx
  code : Prog C Γ tailCtx
  value : Src C tailCtx T

namespace Operand

def ofSrc (v : Src C Γ T) : Operand C Γ T := ⟨Γ, .nil, v⟩

def wk (e : Operand C Γ T) (h : Thin Γ Δ) : Operand C Δ T :=
  let ⟨Δ', h', P'⟩ := e.code.wk h
  ⟨Δ', P', e.value.wk h'⟩

/-- Read the final source before dropping temporaries; retain writes and heap growth. -/
def run (e : Operand C Γ T) (σ : State C Γ) : TRes (Out C σ.H Γ × SVal T) := do
  let a ← e.code.run σ
  let v ← e.value.valueT a.st
  pure (⟨a.st.drop e.code.ext, a.ext⟩, v)

theorem run_wk (e : Operand C Γ T) (h : Thin Γ Δ) (σ : State C Γ) (d : TEnv C σ.H Δ) :
    (e.wk h).run (σ.lift h d) = liftedT₂ h d (e.run σ) := by
  have hr : TWkRel (e.code.wk h).2.1 (TEnv.off h d)
      (e.code.run σ) ((e.code.wk h).2.2.run (σ.lift h d)) := Prog.run_wk e.code h σ d
  dsimp only [wk, run]
  generalize Prog.run σ e.code = a at hr ⊢
  generalize Prog.run (σ.lift h d) (e.code.wk h).2.2 = b at hr ⊢
  cases a with
  | error err =>
    cases b with
    | error err' => exact congrArg Except.error hr.symm
    | ok b => cases hr
  | ok a =>
    cases b with
    | error err => cases hr
    | ok b =>
      obtain ⟨d', hd, rfl⟩ := hr
      dsimp only [bind, Except.bind]
      rw [Src.valueT_wk]
      obtain ⟨h1, h2⟩ := (Prog.wk_over e.code h).tenv a.st.env d'
      have hs : (a.st.lift (e.code.wk h).2.1 d').drop (e.code.wk h).2.2.ext =
          (a.st.drop e.code.ext).lift h (TEnv.drop (e.code.wk h).2.2.ext d') := by
        simp only [State.lift, State.drop, State.withEnv, h1]
      have hd' : TEnv.off h (TEnv.drop (e.code.wk h).2.2.ext d') =
          TEnv.off h (TEnv.wk a.ext Δ d) :=
        h2.trans (hd.trans (TEnv.off_wk a.ext h d).symm)
      have hs' : (a.st.lift (e.code.wk h).2.1 d').drop (e.code.wk h).2.2.ext =
          (a.st.drop e.code.ext).lift h (TEnv.wk a.ext Δ d) :=
        hs.trans (State.lift_congr h (a.st.drop e.code.ext) hd')
      cases e.value.valueT a.st with
      | error err => rfl
      | ok v =>
        change Except.ok ((⟨(a.st.lift (e.code.wk h).2.1 d').drop (e.code.wk h).2.2.ext,
            a.ext⟩ : Out C σ.H Δ), v) =
          Except.ok ((⟨(a.st.drop e.code.ext).lift h (TEnv.wk a.ext Δ d), a.ext⟩ : Out C σ.H Δ), v)
        congr 3

theorem run_afterAlias {R : RefTy} (e : Operand C Γ T) (σ : State C Γ)
    (p : Option (SRef C (.ref R))) :
    (e.wk (.drop .refl)).run (σ.push (t := .alias R) p) =
      (e.run σ).map (fun x => (⟨x.1.st.push (t := .alias R) p, x.1.ext⟩, x.2)) := by
  simpa only [liftedT₂, Out.lift, State.lift, State.push, TEnv.put, TEnv.wk, LTy.TDenote.wk]
    using run_wk e (.drop (t := .alias R) .refl) σ (p, σ.env)

def pushAt {E : Ty} (e : Operand C Γ E) (ref : SRef C (.ref (.array E))) : TStep C Γ Γ := fun σ => do
  let x ← e.run σ
  if x.1.st.storage.full ref then .error .exhausted else
  let st ← TRes.ofOpt (x.1.st.storage.push ref fun _ => some x.2.strip)
  pure ⟨x.1.st.withStorage st, x.1.ext⟩

theorem pushAt_afterAlias {R : RefTy} {E : Ty} (e : Operand C Γ E) (σ : State C Γ)
    (p : Option (SRef C (.ref R))) (ref : SRef C (.ref (.array E))) :
    (e.wk (.drop .refl)).pushAt ref (σ.push (t := .alias R) p) =
      (e.pushAt ref σ).map (fun x => ⟨x.st.push (t := .alias R) p, x.ext⟩) := by
  unfold pushAt
  rw [run_afterAlias]
  cases e.run σ with
  | error err => rfl
  | ok x =>
    dsimp only [bind, Except.bind, Except.map]
    dsimp only [State.push, State.withEnv]
    cases hf : x.1.st.storage.full ref with
    | true => rfl
    | false =>
      cases hp : x.1.st.storage.push ref (fun _ => some x.2.strip) with
      | none => rfl
      | some st => rfl

end Operand

theorem join_ext : {Γ Δ Ε : Ctx} → (P : Prog C Γ Δ) → (Q : Prog C Δ Ε) →
    (P.join Q).ext = P.ext.trans Q.ext
  | _, _, _, .nil, Q => (Ext.refl_trans Q.ext).symm
  | _, _, _, .cons s P, Q => by
    change s.ext.trans (P.join Q).ext = (s.ext.trans P.ext).trans Q.ext
    rw [join_ext P Q, Ext.trans_assoc]

theorem join_run : {Γ Δ Ε : Ctx} → (P : Prog C Γ Δ) → (Q : Prog C Δ Ε) → (σ : State C Γ) →
    (P.join Q).run σ = TRun.seq P.runR Q.runR σ
  | _, _, _, .nil, Q, σ => by
    change Q.run σ = (do let x ← Q.run σ; pure x)
    cases Q.run σ
    all_goals rfl
  | _, _, _, .cons s P, Q, σ => by
    change TRun.seq s.runR (P.join Q).runR σ = TRun.seq (TRun.seq s.runR P.runR) Q.runR σ
    simp only [TRun.seq, join_run P Q]
    cases s.runR σ with
    | error err => rfl
    | ok a =>
      dsimp only []
      cases P.runR a.st with
      | error err => rfl
      | ok b =>
        dsimp only [Except.map]
        cases Q.runR b.st
        all_goals rfl

def expandedPush {E : Ty} (e : Operand C Γ E) (i : Idx Γ (.alias (.array E))) : TStep C Γ Γ :=
    fun σ => do
  let a ← e.code.run σ
  let x ← TRun.push (.alias (i.ext e.code.ext)) (some e.value) a.st
  pure ⟨x.st.drop e.code.ext, a.ext.trans x.ext⟩

/-- The explicit scoped prefix followed by the existing typed push statement. -/
def pushBlock {E : Ty} (e : Operand C Γ E) (i : Idx Γ (.alias (.array E))) : Stmt C Γ Γ :=
  .block (e.code.join (.cons (.push (.alias (i.ext e.code.ext)) (some e.value) rfl) .nil))

theorem pushBlock_run {E : Ty} (e : Operand C Γ E) (i : Idx Γ (.alias (.array E))) (σ : State C Γ) :
    (pushBlock e i).run σ = expandedPush e i σ := by
  change ((e.code.join (.cons (.push (.alias (i.ext e.code.ext)) (some e.value) rfl) .nil)).run σ).map
    (Out.drop (e.code.join (.cons (.push (.alias (i.ext e.code.ext)) (some e.value) rfl) .nil)).ext) =
      expandedPush e i σ
  rw [join_ext, join_run]
  change (TRun.seq e.code.runR
      (TRun.seq (TRun.push (.alias (i.ext e.code.ext)) (some e.value)) TRun.nil) σ).map
        (Out.drop e.code.ext) = expandedPush e i σ
  simp only [TRun.seq, TRun.nil, expandedPush, Prog.run]
  cases e.code.runR σ with
  | error err => rfl
  | ok a =>
    dsimp only [bind, Except.bind, Except.map]
    cases TRun.push (.alias (i.ext e.code.ext)) (some e.value) a.st
    all_goals rfl

theorem expandedPush_atAlias {E : Ty} (e : Operand C Γ E) (σ : State C Γ)
    (ref : SRef C (.ref (.array E))) :
    expandedPush (e.wk (.drop .refl)) .here (σ.push (some ref)) =
      (e.pushAt ref σ).map (fun x => ⟨x.st.push (t := .alias (.array E)) (some ref), x.ext⟩) := by
  let h : Thin Γ (.alias (.array E) :: Γ) := .drop .refl
  have hr : TWkRel (e.code.wk h).2.1
      (TEnv.off h (some ref, σ.env)) (e.code.run σ)
      ((e.code.wk h).2.2.run (σ.push (some ref))) :=
    Prog.run_wk e.code h σ (some ref, σ.env)
  have hf : ((e.code.wk h).2.2.run (σ.push (some ref))).map (Out.drop (e.code.wk h).2.2.ext) =
      liftedT h (some ref, σ.env) ((e.code.run σ).map (Out.drop e.code.ext)) :=
    (TWkRel.drop (Prog.wk_over e.code h) hr).eq_lifted
  change expandedPush (e.wk h) .here (σ.push (some ref)) =
    (e.pushAt ref σ).map (fun x => ⟨x.st.push (t := .alias (.array E)) (some ref), x.ext⟩)
  dsimp only [expandedPush, Operand.wk, Operand.pushAt, Operand.run]
  generalize e.code.run σ = a at hr hf ⊢
  generalize (e.code.wk h).2.2.run (σ.push (some ref)) = b at hr hf ⊢
  cases a with
  | error err =>
    cases b with
    | error err' => exact congrArg Except.error hr.symm
    | ok b => cases hr
  | ok a =>
    cases b with
    | error err => cases hr
    | ok b =>
      obtain ⟨d', hd, rfl⟩ := hr
      have hout : Out.drop (e.code.wk h).2.2.ext
          (⟨a.st.lift (e.code.wk h).2.1 d', a.ext⟩ : Out C σ.H _) =
          (⟨(a.st.drop e.code.ext).push (t := .alias (.array E)) (some ref), a.ext⟩ : Out C σ.H _) :=
        Except.ok.inj hf
      have hp : TEnv.get ((.here : Idx (.alias (.array E) :: Γ) (.alias (.array E))).ext
          (e.code.wk h).2.2.ext) (a.st.lift (e.code.wk h).2.1 d').env = some ref := by
        simpa only [TEnv.get_ext_drop] using
          congrArg (fun x : Out C σ.H (.alias (.array E) :: Γ) => x.st.env.1) hout
      simp only [TRun.push, SPath.resolveT, hp, Src.valueT_wk, TRes.ofOpt,
        bind, Except.bind]
      cases e.value.valueT a.st with
      | error err => rfl
      | ok v =>
        dsimp only [State.lift, State.drop, State.withEnv]
        dsimp only [pure, Except.pure, Except.map]
        cases hc : a.st.storage.full ref with
        | true => rfl
        | false =>
          dsimp only [Option.getD]
          cases hs : a.st.storage.push ref (fun _ => some v.strip) with
          | none => rfl
          | some st =>
            exact congrArg (fun x : Out C σ.H (.alias (.array E) :: Γ) =>
              Except.ok (⟨x.st.withStorage st, x.ext⟩ : Out C σ.H (.alias (.array E) :: Γ))) hout

/-- Validate the getter result before any operand effect can run. -/
def afterReturnedAlias {E : Ty} (e : Operand C Γ E) : TStep C (.alias (.array E) :: Γ) Γ := fun σ => do
  let ref ← SPath.resolveT σ (.alias .here)
  let x ← (e.wk (.drop .refl)).pushAt ref σ
  pure ⟨x.st.drop (.push .refl), x.ext⟩

def capturedAfterReturnedAlias {E : Ty} (e : Operand C Γ E) : TStep C (.alias (.array E) :: Γ) Γ :=
    fun σ => do
  let a ← TRun.declStorage (.array E) (some (.path (.alias .here))) σ
  let ref ← SPath.resolveT a.st (.alias .here)
  let x ← ((e.wk (.drop .refl)).wk (.drop .refl)).pushAt ref a.st
  pure ⟨x.st.drop (.push (.push .refl)), a.ext.trans x.ext⟩

theorem capture_afterGetter {E : Ty} (e : Operand C Γ E) (σ : State C (.alias (.array E) :: Γ)) :
    capturedAfterReturnedAlias e σ = afterReturnedAlias e σ := by
  cases hp : σ.env.1 with
  | none =>
    simp only [capturedAfterReturnedAlias, afterReturnedAlias, TRun.declStorage,
      ARhs.evalT, SPath.resolveT, TEnv.get, hp, bind, Except.bind]
  | some ref =>
    simp only [capturedAfterReturnedAlias, afterReturnedAlias, TRun.declStorage,
      ARhs.evalT, SPath.resolveT, TEnv.get, hp, bind, Except.bind]
    change (do
      let x ← ((e.wk (.drop .refl)).wk (.drop .refl)).pushAt ref
        (σ.push (t := .alias (.array E)) (some ref))
      pure (Out.drop (.push (.push .refl)) x)) = (do
      let x ← (e.wk (.drop .refl)).pushAt ref σ
      pure (Out.drop (.push .refl) x))
    rw [Operand.pushAt_afterAlias]
    cases (e.wk (.drop .refl)).pushAt ref σ
    all_goals rfl

def captureProgram {E : Ty} (e : Operand C Γ E) :
    Prog C (.alias (.array E) :: Γ) (.alias (.array E) :: .alias (.array E) :: Γ) :=
  .cons (.declStorage (.array E) (.user "sp") (some (.path (.alias .here))))
    (.cons (pushBlock ((e.wk (.drop .refl)).wk (.drop .refl)) .here) .nil)

theorem captureProgram_run {E : Ty} (e : Operand C Γ E) (σ : State C (.alias (.array E) :: Γ)) :
    ((captureProgram e).run σ).map (Out.drop (.push (.push .refl))) =
      capturedAfterReturnedAlias e σ := by
  change (TRun.seq (TRun.declStorage (.array E) (some (.path (.alias .here))))
      (TRun.seq (pushBlock ((e.wk (.drop .refl)).wk (.drop .refl)) .here).runR TRun.nil) σ).map
        (Out.drop (.push (.push .refl))) = capturedAfterReturnedAlias e σ
  cases hp : σ.env.1 with
  | none =>
    simp only [TRun.seq, TRun.declStorage, capturedAfterReturnedAlias, ARhs.evalT,
      SPath.resolveT, TEnv.get, hp, bind, Except.bind, Except.map]
  | some ref =>
    simp only [TRun.seq, TRun.nil, TRun.declStorage, capturedAfterReturnedAlias, ARhs.evalT,
      SPath.resolveT, TEnv.get, hp, bind, Except.bind, Except.map]
    dsimp only [pure, Except.pure, State.withStorage, State.push]
    have hb : (pushBlock ((e.wk (.drop .refl)).wk (.drop .refl)) .here).run
        (σ.push (t := .alias (.array E)) (some ref)) =
      ((e.wk (.drop .refl)).wk (.drop .refl)).pushAt ref
        (σ.push (t := .alias (.array E)) (some ref)) := by
      rw [pushBlock_run, expandedPush_atAlias, Operand.pushAt_afterAlias]
    dsimp only [Stmt.run, State.push] at hb
    rw [hb]
    cases hq : ((e.wk (.drop .refl)).wk (.drop .refl)).pushAt ref
      (show State C (.alias (.array E) :: .alias (.array E) :: Γ) from
        { σ with env := (some ref, σ.env) })
    all_goals rfl

def runCall {ps Γf : Ctx} {E : Ty} (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (e : Operand C Γ E) : TStep C Γ Γ := fun σ => do
  let a ← TRun.call args (.storage (.array E) r) body.ext body.runR σ
  let x ← afterReturnedAlias e a.st
  pure ⟨x.st, a.ext.trans x.ext⟩

def runCapturedCall {ps Γf : Ctx} {E : Ty} (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (e : Operand C Γ E) : TStep C Γ Γ := fun σ => do
  let a ← TRun.call args (.storage (.array E) r) body.ext body.runR σ
  let x ← capturedAfterReturnedAlias e a.st
  pure ⟨x.st, a.ext.trans x.ext⟩

theorem call_capture_run {ps Γf : Ctx} {E : Ty} (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (e : Operand C Γ E) (σ : State C Γ) :
    runCapturedCall args r body e σ = runCall args r body e σ := by
  simp only [runCapturedCall, runCall, capture_afterGetter]

/-- The actual getter call and explicit alias capture, with both aliases still in scope. -/
def callProgram {ps Γf : Ctx} {E : Ty} (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (e : Operand C Γ E) :
    Prog C Γ (.alias (.array E) :: .alias (.array E) :: Γ) :=
  .cons (.call f args (.storage (.array E) r) body) (captureProgram e)

theorem callProgram_run {ps Γf : Ctx} {E : Ty} (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (e : Operand C Γ E) (σ : State C Γ) :
    ((callProgram f args r body e).run σ).map (Out.drop (.push (.push .refl))) =
      runCapturedCall args r body e σ := by
  change (TRun.seq (TRun.call args (.storage (.array E) r) body.ext body.runR)
      (captureProgram e).runR σ).map (Out.drop (.push (.push .refl))) =
        runCapturedCall args r body e σ
  simp only [TRun.seq, runCapturedCall]
  cases TRun.call args (.storage (.array E) r) body.ext body.runR σ with
  | error err => rfl
  | ok a =>
    dsimp only [bind, Except.bind]
    rw [← captureProgram_run e a.st]
    dsimp only [Prog.run]
    cases (captureProgram e).runR a.st
    all_goals rfl

/-- Explicit capture agrees with deferred evaluation for arbitrary typed getter bodies and prefixes. -/
theorem callProgram_sound {ps Γf : Ctx} {E : Ty} (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (e : Operand C Γ E) (σ : State C Γ) :
    ((callProgram f args r body e).run σ).map (Out.drop (.push (.push .refl))) =
      runCall args r body e σ :=
  (callProgram_run f args r body e σ).trans (call_capture_run args r body e σ)

end Solidity.DeferredSource
