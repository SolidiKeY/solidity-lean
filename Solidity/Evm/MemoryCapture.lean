import Solidity.Evm.MemoryCompound
import Solidity.Evm.MemoryGrowResult
import Solidity.Evm.MemoryLocals

/-!
# Capturing checked bump results on the stack

A captured prefix/postfix result is evaluated in the original source state.
The bump runs with that word below its own working stack, and only then stores
it into the destination local. This retains the old index when the destination
is also the index local, and handles self-assignment such as `i = i++`.
-/

namespace Solidity.Evm.Memory
variable {C : Contract} {Γ : Ctx}

/-- Prefix captures the checked new value; postfix captures the old one. -/
def bumpResultValue {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true)
    (old : Val C Γ p) : Val C Γ p :=
  if op.isPre then compoundValue op.binOp (increment_compound op) hp old (incrementOne hp)
  else old

theorem bumpResultValue_eval {p : PrimTy} (σ : State C Γ) (op : IncDec)
    (hp : p.isNumeric = true) (old : Val C Γ p) :
    (bumpResultValue op hp old).evalT σ = (do
      let v ← old.evalT σ
      if op.isPre then TRes.ofOpt (bumpT op p (PrimTy.key v)) else pure v) := by
  cases op <;>
    simp only [bumpResultValue, IncDec.isPre, Bool.false_eq_true, ↓reduceIte, compoundValue_eval,
      incrementOne, Val.evalT, Simple.evalT]
  all_goals cases p <;> simp only [PrimTy.isNumeric, Bool.false_eq_true] at hp <;>
    cases old.evalT σ <;> rfl

/-- Save a pure value, run the state-changing step, then set its destination. -/
def captureStep {p : PrimTy} (dst : Idx Γ (.val p)) (value : Val C Γ p)
    (step : TStep C Γ Γ) : TStep C Γ Γ := fun σ => do
  let v ← value.evalT σ
  let o ← step σ
  pure ⟨o.st.setLocal dst v, o.ext⟩

/-- Capturing a memory bump preserves its complete typed result. -/
theorem captureMemory_eq {p : PrimTy} {R : RefTy} (σ : State C Γ)
    (dst : Idx Γ (.val p)) (op : IncDec) (hp : p.isNumeric = true)
    (a : ArrTy R (.prim p)) (src : MPath C Γ (.ref R)) (i : Simple C Γ .uint) :
    TRun.assignIncDec dst op (.mindex a src i) σ =
      captureStep dst (bumpResultValue op hp (.readMem (.index a src (.simple i))))
        (TRun.incDec op (.mindex a src i)) σ := by
  simp only [TRun.assignIncDec, TRun.incDec, captureStep, bumpResultValue_eval,
    OpLoc.bumpT, Val.evalT]
  cases ha : MLoc.addrT σ (MLoc.index a src (.simple i)) with
  | error _ => rfl
  | ok addr =>
    simp only [bumpMemT, bind, Except.bind]
    cases σ.heap.readAddr addr with
    | none => rfl
    | some old =>
      simp only [TRes.ofOpt]
      cases hn : bumpT op p (PrimTy.key old) with
      | none => cases op <;> rfl
      | some new =>
        simp only
        cases σ.heap.writeAddr addr new <;> cases op <;> rfl

theorem captureField_eq {p : PrimTy} {s f : Name} (σ : State C Γ)
    (dst : Idx Γ (.val p)) (op : IncDec) (hp : p.isNumeric = true)
    (src : MPath C Γ (.struct s)) (hf : C.fieldType s f = some (.prim p)) :
    TRun.assignIncDec dst op (.mfield src f hf) σ =
      captureStep dst (bumpResultValue op hp (.readMem (.field src f hf)))
        (TRun.incDec op (.mfield src f hf)) σ := by
  simp only [TRun.assignIncDec, TRun.incDec, captureStep, bumpResultValue_eval,
    OpLoc.bumpT, Val.evalT]
  cases ha : MLoc.addrT σ (MLoc.field src f hf) with
  | error _ => rfl
  | ok addr =>
    simp only [bumpMemT, bind, Except.bind]
    cases σ.heap.readAddr addr with
    | none => rfl
    | some old =>
      simp only [TRes.ofOpt]
      cases hn : bumpT op p (PrimTy.key old) with
      | none => cases op <;> rfl
      | some new =>
        simp only
        cases σ.heap.writeAddr addr new <;> cases op <;> rfl

/-- Local capture also covers an identical source and destination local. -/
theorem captureLocal_eq {p : PrimTy} (σ : State C Γ) (dst : Idx Γ (.val p))
    (op : IncDec) (hp : p.isNumeric = true) (src : Idx Γ (.val p)) :
    TRun.assignIncDec dst op (.local src) σ =
      captureStep dst (bumpResultValue op hp (.simple (.local src)))
        (TRun.incDec op (.local src)) σ := by
  simp only [TRun.assignIncDec, TRun.incDec, captureStep, bumpResultValue_eval,
    OpLoc.bumpT, Val.evalT, Simple.evalT, bind, Except.bind]
  cases bumpT op p (PrimTy.key (TEnv.get src σ.env)) <;> cases op <;> rfl

/-- Stack-only changes preserve the full typed state relation. -/
theorem StateRepr.stack {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) (st : List Word) :
    StateRepr L b frame F σ base {m with stack := st} :=
  ⟨h.core.stack st, ⟨fun r => (h.heap.arrays r).stack st, h.heap.above, h.heap.separated⟩,
    h.pointers, h.locals, h.structs.stack st, h.separated, RefFieldsRepr.mem_eq h.refs rfl⟩

/-- The saved value survives the step on the stack before the final local store. -/
theorem captureStep_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {p : PrimTy}
    (dst : Idx Γ (.val p)) (value : Val C Γ p) (step : TStep C Γ Γ)
    (valueCode stepCode : List Instr)
    (hv : ValOutT p (value.evalT σ) (run valueCode m) m)
    (hs : ∀ {m' : Machine}, StateRepr L b frame F σ base m' →
      GrowingResult L b frame 0 F σ base m' (step σ) (run stepCode m')) :
    GrowingResult L b frame 0 F σ base m (captureStep dst value step σ)
      (run (valueCode ++ stepCode ++ [.mstore (cellOf b dst)]) m) := by
  rcases hv with ⟨v, w, hv, hw, hval⟩ | ⟨hv, hval⟩
  · rcases hs (h.push w) with ⟨o, m', base', ho, hc, hr, hst, hb, ha⟩ | ⟨ho, hc⟩
    · let out := writeMachine {m' with stack := m.stack} (cellOf b dst) w
      refine .inl ⟨⟨o.st.setLocal dst v, o.ext⟩, out, base', ?_, ?_,
        (hr.stack m.stack).setVal dst v w hw, rfl, hb, ?_⟩
      · simp only [captureStep, hv, ho, bind, Except.bind]
        rfl
      · rw [List.append_assoc, run_append_ok hval, run_append_ok hc]
        simp only [run, exec_cons_zero, Instr.step, hst, Machine.push,
          exec_nil, out, writeMachine, Out.ok_bind]
      · intro cursor hpos hal hspace
        have hall := ha cursor hpos (hal.mem_eq rfl) hspace
        exact (hall.mem_eq (m' := {m' with stack := m.stack}) rfl).localWrite _
          (Nat.lt_of_lt_of_le hpos (le_lvl b dst))
          (Nat.lt_of_lt_of_le (lvl_lt b dst) hr.locals) w
    · refine .inr ⟨?_, ?_⟩
      · simp only [captureStep, hv, ho, bind, Except.bind]
      · rw [List.append_assoc, run_append_ok hval]
        exact run_append_revert hc
  · refine .inr ⟨?_, ?_⟩
    · simp only [captureStep, hv, bind, Except.bind]
    · exact run_append_revert (run_append_revert hval)

end Solidity.Evm.Memory
