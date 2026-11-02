import Solidity.Backend.Passes.Sequence

/-!
# Explicit output maps at typed compilation boundaries

MappedOutput is a proof-only refinement of the existing branch-indexed Rep.
It names its existential output address map and is equivalent to Rep after
existential quantification. No value/state representation or source semantics
is changed. Links consume the *same* selected map, including its allocator
and old-reference facts.
-/
namespace Solidity.Backend.Passes
open Solidity.Evm
open Solidity.Evm.Compiler

variable {C : Contract} {b L frame : Nat} {Γ Δ Ξ : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ}

def MappedOutput (result : Compilation b F P) (L frame : Nat)
    (base : Nat → Fin W) (entry : State C Γ) (initial : Machine)
    (τ : State C Δ) (m : Machine) (outBase : Nat → Fin W) : Prop :=
  match result with
  | .core out _ => outBase = base ∧ Sim C L b out τ m
  | .memory out => Memory.StateRepr L b frame out.frag τ outBase m ∧
      Memory.BaseExtends entry.H base outBase ∧
      Memory.GrowsAllocator b frame (out.cert.cost entry) entry base initial τ outBase m
  | .referenceArrays out => outBase = base ∧
      Memory.RefArrayStateRepr L b frame out.frag τ outBase m
  | .objects out => outBase = base ∧
      Memory.Objects.StateRepr L b frame out.frag τ outBase m ∧
      Memory.Objects.KeepsAllocator b frame entry base initial τ m
  | .construction out => Memory.Objects.StateRepr L b frame out.frag τ outBase m ∧
      Memory.BaseExtends entry.H base outBase ∧
      Memory.Objects.GrowsAllocator b frame
        (Memory.Construction.allocationCostProg P entry) entry base initial τ outBase m
  | .memoryLoops out => ∃ amount, ∃ ext : entry.H <+: τ.H,
      Memory.Loops.Cost out.cert entry ⟨τ,ext⟩ amount ∧
      Memory.StateRepr L b frame out.frag τ outBase m ∧
      Memory.BaseExtends entry.H base outBase ∧
      Memory.GrowsAllocator b frame amount entry base initial τ outBase m
  | .memoryLoopScopes out => ∃ amount, ∃ ext : entry.H <+: τ.H,
      Memory.LoopScopes.Cost out.cert entry ⟨τ,ext⟩ amount ∧
      Memory.StateRepr L b frame out.frag τ outBase m ∧
      Memory.BaseExtends entry.H base outBase ∧
      Memory.GrowsAllocator b frame amount entry base initial τ outBase m
  | .memoryCalls out _ => Memory.StateRepr L b frame out.frag τ outBase m ∧
      Memory.BaseExtends entry.H base outBase ∧
      Memory.GrowsAllocator b frame (out.cost entry) entry base initial τ outBase m

/-- All eight existing output relations are retained exactly. -/
theorem mapped_output_iff (result : Compilation b F P) (L frame : Nat)
    (base : Nat → Fin W) (entry : State C Γ) (initial : Machine)
    (τ : State C Δ) (m : Machine) :
    result.Rep L frame base entry initial τ m ↔
      ∃ outBase, MappedOutput result L frame base entry initial τ m outBase := by
  cases result with
  | core out cert =>
    constructor
    · intro h
      exact ⟨base, rfl, h⟩
    · rintro ⟨_, _, h⟩
      exact h
  | memory out => rfl
  | referenceArrays out =>
    constructor
    · intro h
      exact ⟨base, rfl, h⟩
    · rintro ⟨_, rfl, h⟩
      exact h
  | objects out =>
    constructor
    · intro h
      exact ⟨base, rfl, h⟩
    · rintro ⟨_, rfl, hstate, ha⟩
      exact ⟨hstate, ha⟩
  | construction out => rfl
  | memoryLoops out => rfl
  | memoryLoopScopes out => rfl
  | memoryCalls out pushFree => rfl

def MappedBoundaryLink (left : Compilation b F P) (right : Compilation b left.frag Q)
    (L frame : Nat) (base : Nat → Fin W) (σ : State C Γ) (m : Machine) : Prop :=
  ∀ (o : Solidity.Out C σ.H Δ) (m' : Machine) (midBase : Nat → Fin W),
    P.run σ = .ok o → run left.code m = .ok m' 0 →
    MappedOutput left (L + Evm.Prog.pushes P) frame base σ m o.st m' midBase →
    right.Input (L + Evm.Prog.pushes P) frame midBase o.st m'

/-- A nonallocating suffix really consumes the allocating prefix's selected
map and full represented heap. Its frame and zero-cost facts are separate,
checkable premises, not a desired preservation result. -/
theorem memory_nonallocating_mapped_link (left : Memory.CompiledProg b F P)
    (right : Memory.CompiledProg b left.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hframe : b + Memory.frameNeedProg Q ≤ frame)
    (hn : Memory.hasAllocation Q = false) :
    MappedBoundaryLink (.memory left) (.memory right) L frame base σ m := by
  intro o m' midBase _ _ hr
  exact ⟨hr.1, hframe, .inl (Memory.allocationCostProg_zero Q hn o.st)⟩

/-- An allocating suffix consumes the prefix's actual map. A checked
entry budget for the sum of the two reached costs supplies its allocator
input; this is a capacity premise, not a preservation assumption. -/
theorem memory_budgeted_mapped_link (left : Memory.CompiledProg b F P)
    (right : Memory.CompiledProg b left.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hframe : b + Memory.frameNeedProg Q ≤ frame)
    (budget : ∀ (o : Solidity.Out C σ.H Δ), P.run σ = .ok o →
      Memory.AllocationInput b frame (left.cert.cost σ + right.cert.cost o.st) σ base m) :
    MappedBoundaryLink (.memory left) (.memory right) L frame base σ m := by
  intro o m' midBase hs _ hr
  exact ⟨hr.1, hframe, hr.2.2.nextInput (budget o hs)⟩

/-- General typed terminal sequencing, with both output maps named and the
intermediate map shared by the two complete representation witnesses. -/
theorem compilation_mapped_success
    (left : Compilation b F P) (right : Compilation b left.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : left.Input L frame base σ m)
    (link : MappedBoundaryLink left right L frame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false)
    {o : Solidity.Out C σ.H Δ} (hs : P.run σ = .ok o)
    {o' : Solidity.Out C o.st.H Ξ} (hs' : Q.run o.st = .ok o') :
    ∃ midBase outBase mid final,
      (P.join Q).run σ = .ok ⟨o'.st, o.ext.trans o'.ext⟩ ∧
      run left.code m = .ok mid 0 ∧
      run (left.code ++ right.code) m = .ok final 0 ∧
      final.stack = m.stack ∧
      MappedOutput left (L + Evm.Prog.pushes P) frame base σ m o.st mid midBase ∧
      MappedOutput right ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q)
        frame midBase o.st mid o'.st final outBase := by
  obtain ⟨mid, ht, hstack, hr⟩ := compilation_success left hi hp hs
  obtain ⟨midBase, hleft⟩ :=
    (mapped_output_iff left (L + Evm.Prog.pushes P) frame base σ m o.st mid).mp hr
  obtain ⟨final, ht', hstack', hr'⟩ :=
    compilation_success right (link o mid midBase hs ht hleft) hq hs'
  obtain ⟨outBase, hright⟩ :=
    (mapped_output_iff right ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q)
      frame midBase o.st mid o'.st final).mp hr'
  refine ⟨midBase, outBase, mid, final, ?_, ht, ?_, hstack'.trans hstack, hleft, hright⟩
  · rw [DeferredSource.join_run]
    simp only [TRun.seq, hs, hs', Except.map]
  · rw [run_append_ok ht]
    exact ht'

/-- The memory branch's published two-way result needs no payment-freedom
hypothesis. Its source success exposes an actual selected output map. -/
theorem memory_mapped_success (result : Memory.CompiledProg b F P)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : (Compilation.memory result).Input L frame base σ m)
    {o : Solidity.Out C σ.H Δ} (hs : P.run σ = .ok o) :
    ∃ outBase m', run result.code m = .ok m' 0 ∧ m'.stack = m.stack ∧
      MappedOutput (.memory result) (L + Evm.Prog.pushes P) frame base σ m o.st m' outBase := by
  rcases result.cert.correct hi.1 hi.2.1 hi.2.2 with
    ⟨actual, m', outBase, hs', ht, hstate, hstack, he, ha⟩ | ⟨hs', _⟩
  · have ho : actual = o := Except.ok.inj (hs'.symm.trans hs)
    cases ho
    have hstate' : Memory.StateRepr (L + Evm.Prog.pushes P) b frame result.frag
        o.st outBase m' := by
      simpa only [result.cert.pushes_zero, Nat.add_zero] using hstate
    exact ⟨outBase, m', ht, hstack, hstate', he, ha⟩
  · rw [hs] at hs'
    cases hs'

/-- Actual memory-stage composition retains both selected maps and composes
old-reference identity and exact reached allocation cost, without adding a
payment-freedom premise to the published memory theorem. -/
theorem memory_sequence_resources (left : Memory.CompiledProg b F P)
    (right : Memory.CompiledProg b left.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : (Compilation.memory left).Input L frame base σ m)
    (link : MappedBoundaryLink (.memory left) (.memory right) L frame base σ m)
    {o : Solidity.Out C σ.H Δ} (hs : P.run σ = .ok o)
    {o' : Solidity.Out C o.st.H Ξ} (hs' : Q.run o.st = .ok o') :
    ∃ midBase outBase mid final,
      (P.join Q).run σ = .ok ⟨o'.st, o.ext.trans o'.ext⟩ ∧
      run (left.code ++ right.code) m = .ok final 0 ∧ final.stack = m.stack ∧
      MappedOutput (.memory left) (L + Evm.Prog.pushes P) frame base σ m o.st mid midBase ∧
      MappedOutput (.memory right) ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q)
        frame midBase o.st mid o'.st final outBase ∧
      Memory.BaseExtends σ.H base outBase ∧
      Memory.GrowsAllocator b frame (left.cert.cost σ + right.cert.cost o.st)
        σ base m o'.st outBase final := by
  obtain ⟨midBase, mid, ht, hstack, hleft⟩ := memory_mapped_success left hi hs
  obtain ⟨outBase, final, ht', hstack', hright⟩ :=
    memory_mapped_success right (link o mid midBase hs ht hleft) hs'
  refine ⟨midBase, outBase, mid, final, ?_, ?_, hstack'.trans hstack, hleft, hright,
    Memory.BaseExtends.trans o.ext hleft.2.1 hright.2.1,
    Memory.GrowsAllocator.comp hleft.2.2 hright.2.2⟩
  · rw [DeferredSource.join_run]
    simp only [TRun.seq, hs, hs', Except.map]
  · rw [run_append_ok ht]
    exact ht'


/-- Two-sided coarse terminal failure for the explicit-map boundary. Successful
prefixes select their actual map before the suffix Input is transported. -/
theorem compilation_mapped_revert_iff
    (left : Compilation b F P) (right : Compilation b left.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : left.Input L frame base σ m)
    (link : MappedBoundaryLink left right L frame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false) :
    run (left.code ++ right.code) m = .revert ↔
      TerminalFailure P σ ∨ ∃ o, P.run σ = .ok o ∧ TerminalFailure Q o.st := by
  constructor
  · intro ht
    rcases compilation_exact left hi hp with
      ⟨o, mid, hs, hm, _, hr⟩ | ⟨hs, _⟩ | ⟨_, hm⟩
    · obtain ⟨mb, hr'⟩ :=
        (mapped_output_iff left (L + Evm.Prog.pushes P) frame base σ m o.st mid).mp hr
      rw [run_append_ok hm] at ht
      exact .inr ⟨o, hs, (compilation_revert_iff right (link o mid mb hs hm hr') hq).mp ht⟩
    · exact .inl hs
    · have hf := run_append_fault (c₂ := right.code) hm
      rw [ht] at hf
      cases hf
  · rintro (hs | ⟨o, hs, hfail⟩)
    · exact run_append_revert ((compilation_revert_iff left hi hp).mpr hs)
    · obtain ⟨mid, hm, _, hr⟩ := compilation_success left hi hp hs
      obtain ⟨mb, hr'⟩ :=
        (mapped_output_iff left (L + Evm.Prog.pushes P) frame base σ m o.st mid).mp hr
      rw [run_append_ok hm]
      exact (compilation_revert_iff right (link o mid mb hs hm hr') hq).mpr hfail

end Solidity.Backend.Passes
