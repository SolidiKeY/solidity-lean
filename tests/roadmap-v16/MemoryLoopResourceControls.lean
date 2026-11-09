import Solidity.Evm.MemoryLoopScopeAllocExamples
import Solidity.Evm.MemoryLoopExamples
import Solidity.Examples.Roadmap.V16.MemoryLoopConsumer
import Solidity.Evm.MemoryLoopSourceExamples
import Solidity.Evm.MemoryLoopScopeSourceExamples
import Solidity.Evm.MemoryLoopScopeExamples
import Solidity.Evm.MemoryLoopScopeDivergenceExamples
import Solidity.Semantics.RunFuel
import Lean

/-! Read-only references to exact published fixtures. Kernel-checked finite runF4
is connected to actual source run by existing runF_approx, never native execution.
No source/compiler fixture implementation is duplicated. -/
open Lean Elab Term in
elab "publishedLoop%" mode:ident n:ident : term => do
  let module := if mode.getId == `memory then `Solidity.Evm.MemoryCompileExamples
    else if mode.getId == `alloc then `Solidity.Evm.MemoryLoopAllocExamples
    else if mode.getId == `scopeAlloc then `Solidity.Evm.MemoryLoopScopeAllocExamples
    else if mode.getId == `directSpin then `Solidity.Evm.MemoryLoopExamples
    else if mode.getId == `direct then `Solidity.Evm.MemoryLoopSourceExamples
    else if mode.getId == `scope then `Solidity.Evm.MemoryLoopScopeSourceExamples
    else if mode.getId == `branch then `Solidity.Evm.MemoryLoopScopeExamples
    else `Solidity.Evm.MemoryLoopScopeDivergenceExamples
  let ns := if mode.getId == `memory then `Solidity.Evm.Memory.CompileExamples
    else if mode.getId == `alloc then `Solidity.Evm.Memory.LoopAllocExamples
    else if mode.getId == `scopeAlloc then `Solidity.Evm.Memory.LoopScopeAllocExamples
    else if mode.getId == `directSpin then `Solidity.Evm.Memory.LoopExamples
    else if mode.getId == `direct then `Solidity.Evm.Memory.LoopSourceExamples
    else if mode.getId == `scope then `Solidity.Evm.Memory.LoopScopeSourceExamples
    else if mode.getId == `branch then `Solidity.Evm.Memory.LoopScopeExamples
    else `Solidity.Evm.Memory.LoopScopeDivergenceExamples
  let name := mkPrivateNameCore module (ns ++ n.getId)
  unless (← getEnv).contains name do throwError "missing published fixture {name}"
  return mkConst name

open Lean Elab Term in
elab "publishedContext%" p:term : term => do
  let value ← elabTerm p none
  let type ← Meta.inferType value
  return type.getAppArgs[2]!



namespace Solidity.Roadmap.V16.MemoryLoopControls
open Solidity.Evm Memory.CompileExamples

namespace directFailure
abbrev P := publishedLoop% directSpin badProgram
abbrev compiled := publishedLoop% directSpin badCompiled
theorem path : compiled.isMemoryLoops = true := by decide +kernel
def out : Memory.Loops.CompiledProg 0 (Frag.init Γ) P := compiled.memoryLoopsResult path
attribute [irreducible] out

theorem identity : Compiler.Compilation.memoryLoops out = compiled := by
  unfold out
  exact loop_reconstruct compiled path

theorem input : (Compiler.Compilation.memoryLoops out).Input 1 4 base σ machine := by
  exact ⟨fixture_repr, by decide +kernel,
    Memory.Loops.room_nonallocating out.cert (by decide +kernel) σ base machine⟩

theorem source : P.run σ = .error .revert := by
  have fuel : P.runFC 4 σ = .error .revert :=
    (publishedLoop% memory sourceReverted_sound) (by decide +kernel)
  have approx := P.runF_approx 4 σ
  rw [Prog.runF_eq, fuel] at approx
  exact (approx.eq (by intro bad; cases bad)).symm

theorem false_box : Spec.sat σ (.box P (.not .tt)) := by
  rw [Spec.sat, source]
  intro h
  cases h

theorem true_box : Spec.sat σ (.box P .tt) := by
  rw [Spec.sat, source]
  intro h
  cases h

/-- The NEW three-outcome box consumer selects exact empty revert, never fault. -/
theorem exact_revert : P.run σ = .error .revert ∧ run out.code machine = .revert := by
  rcases loop_box out input false_box with
    ⟨_, _, _, _, _, _, _, _, _, _, _, bad⟩ | h | ⟨hs, _⟩
  · exact (bad trivial).elim
  · exact h
  · rw [source] at hs
    cases hs

theorem public_revert : run compiled.code machine = .revert := by
  rw [← identity]
  exact exact_revert.2

theorem no_diamond : ¬ Spec.sat σ (.diamond P .tt) := by
  rw [Spec.sat, source]
  intro h
  cases h

theorem wrong_fault : run compiled.code machine ≠ .fault := by
  rw [public_revert]
  intro h
  cases h

theorem wrong_payload : P.run σ ≠ .error (.revertWith [9]) := by
  rw [source]
  intro h
  cases h
end directFailure

namespace scopedFailure
abbrev P := publishedLoop% branch revertingTurns
abbrev compiled := publishedLoop% branch revertingPublic
theorem path : compiled.isMemoryLoopScopes = true := by decide +kernel
def out : Memory.LoopScopes.CompiledProg 0 (Frag.init Γ) P := compiled.memoryLoopScopesResult path
attribute [irreducible] out

theorem identity : Compiler.Compilation.memoryLoopScopes out = compiled := by
  unfold out
  exact scoped_loop_reconstruct compiled path

theorem input : (Compiler.Compilation.memoryLoopScopes out).Input 1 4 base σ machine := by
  exact ⟨fixture_repr, by decide +kernel,
    Memory.LoopScopes.room_nonallocating out.cert (by decide +kernel) σ base machine⟩

theorem source : P.run σ = .error .revert := by
  have fuel : P.runFC 4 σ = .error .revert :=
    (publishedLoop% memory sourceReverted_sound) (by decide +kernel)
  have approx := P.runF_approx 4 σ
  rw [Prog.runF_eq, fuel] at approx
  exact (approx.eq (by intro bad; cases bad)).symm

theorem false_box : Spec.sat σ (.box P (.not .tt)) := by
  rw [Spec.sat, source]
  intro h
  cases h

theorem true_box : Spec.sat σ (.box P .tt) := by
  rw [Spec.sat, source]
  intro h
  cases h

/-- The NEW three-outcome box consumer selects exact empty revert, never fault. -/
theorem exact_revert : P.run σ = .error .revert ∧ run out.code machine = .revert := by
  rcases scoped_loop_box out input false_box with
    ⟨_, _, _, _, _, _, _, _, _, _, _, bad⟩ | h | ⟨hs, _⟩
  · exact (bad trivial).elim
  · exact h
  · rw [source] at hs
    cases hs

theorem public_revert : run compiled.code machine = .revert := by
  rw [← identity]
  exact exact_revert.2

theorem no_diamond : ¬ Spec.sat σ (.diamond P .tt) := by
  rw [Spec.sat, source]
  intro h
  cases h

theorem wrong_fault : run compiled.code machine ≠ .fault := by
  rw [public_revert]
  intro h
  cases h

theorem wrong_payload : P.run σ ≠ .error (.revertWith [9]) := by
  rw [source]
  intro h
  cases h
end scopedFailure

namespace skippedFailure
abbrev P := publishedLoop% branch zeroTurns
abbrev compiled := publishedLoop% branch zeroPublic
theorem path : compiled.isMemoryLoopScopes = true := by decide +kernel
def out : Memory.LoopScopes.CompiledProg 0 (Frag.init Γ) P := compiled.memoryLoopScopesResult path
attribute [irreducible] out
theorem input : (Compiler.Compilation.memoryLoopScopes out).Input 1 4 base σ machine := by
  exact ⟨fixture_repr, by decide +kernel,
    Memory.LoopScopes.room_nonallocating out.cert (by decide +kernel) σ base machine⟩
theorem diamond : Spec.sat σ (.diamond P .tt) := by
  have approx := P.runF_approx 4 σ
  rw [Prog.runF_eq] at approx
  have positive : (P.runFC 4 σ).toOption.isSome = true := by decide +kernel
  cases h : P.runFC 4 σ with
  | error e => rw [h] at positive; cases positive
  | ok o =>
    rw [h] at approx
    have source : P.run σ = .ok o := (approx.eq (by intro bad; cases bad)).symm
    rw [Spec.sat, source]
    trivial
theorem success : ∃ o m', P.run σ = .ok o ∧ run out.code machine = .ok m' 0 ∧ m'.stack = machine.stack := by
  obtain ⟨o, m', _, _, hs, ht, _, _, stack, _⟩ := scoped_loop_diamond out input diamond
  exact ⟨o, m', hs, ht, stack⟩
theorem not_revert : run out.code machine ≠ .revert := by
  obtain ⟨_, _, _, ht, _⟩ := success
  rw [ht]
  intro h
  cases h
end skippedFailure
end Solidity.Roadmap.V16.MemoryLoopControls


namespace Solidity.Roadmap.V16.MemoryLoopControls
open Solidity.Evm

namespace allocSuccess
abbrev C := publishedLoop% alloc C
abbrev Γ := publishedLoop% alloc Γ
abbrev σ := publishedLoop% alloc σ
abbrev bases := publishedLoop% alloc bases
abbrev machine := publishedLoop% alloc machine
abbrev P := publishedLoop% alloc program
abbrev compiled := publishedLoop% alloc publicResult
def out : Memory.Loops.CompiledProg 1 (Frag.init Γ) P := publishedLoop% alloc compiled
attribute [irreducible] out

theorem identity : compiled = Compiler.Compilation.memoryLoops out := by
  unfold out
  exact publishedLoop% alloc public_shape

theorem input : (Compiler.Compilation.memoryLoops out).Input 1 6 bases σ machine := by
  unfold out
  refine ⟨(publishedLoop% alloc initial).1, by decide +kernel, ?_⟩
  exact Memory.Loops.room_singleton (publishedLoop% alloc conditionCompiled).cert
      (publishedLoop% alloc bodyCompiled).cert (by decide +kernel) (publishedLoop% alloc loop_room)

/-- Negative baseline ONLY: this legacy query is not the loop Cost/Room. -/
theorem legacy_zero : compiled.allocationCost σ = 0 := by decide +kernel
def output : Solidity.Out C [] Γ := (P.runFC 4 σ).toOption.get (by decide +kernel)
attribute [irreducible] output
theorem source : P.run σ = .ok output := by
  have positive : (P.runFC 4 σ).toOption.isSome = true := by decide +kernel
  have approx := P.runF_approx 4 σ
  rw [Prog.runF_eq] at approx
  cases h : P.runFC 4 σ with
  | error e => rw [h] at positive; cases positive
  | ok o =>
    rw [h] at approx
    have ho : output = o := by simp only [output, h, Except.toOption, Option.get_some]
    exact (approx.eq (by intro bad; cases bad)).symm.trans (congrArg Except.ok ho.symm)

theorem allocated : output.st.H.length = 1 := by decide +kernel

def post : Spec C Γ := .eq (.pvV .here) (.app0 (.lit ⟨0, by decide⟩))
def actualAnswer : PrimTy.uint.Denote := TEnv.get .here output.st.env
attribute [irreducible] actualAnswer
theorem answer_zero : actualAnswer = ⟨0, by decide⟩ := by decide +kernel
theorem diamond : Spec.sat σ (.diamond P post) := by
  rw [Spec.sat, source]
  refine ⟨actualAnswer, ?_, congrArg some answer_zero.symm⟩
  simp only [actualAnswer, Tm.eval]

theorem represented : ∃ o m' base' cost, P.run σ = .ok o ∧ run out.code machine = .ok m' 0 ∧
    Memory.Loops.Cost out.cert σ o cost ∧ Memory.StateRepr 1 1 6 out.frag o.st base' m' ∧
    m'.stack = machine.stack ∧ Memory.BaseExtends σ.H bases base' ∧
    Memory.GrowsAllocator 1 6 cost σ bases machine o.st base' m' ∧ Spec.sat o.st post ∧ o.st.H.length = 1 := by
  obtain ⟨o, m', base', cost, hs, ht, hc, hr, stack, he, hg, hp⟩ :=
    loop_diamond (C := C) (b := 1) (L := 1) (frame := 6) (Γ := Γ) (Δ := Γ)
      (F := Frag.init Γ) (P := P) out (σ := σ) (base := bases) (m := machine) input (φ := post) diamond
  have eq : o = output := Except.ok.inj (hs.symm.trans source)
  subst o
  exact ⟨output, m', base', cost, source, ht, hc, hr, stack, he, hg, hp, allocated⟩
/-- info: (some (0, 1), some [17, 0, 16, 99, 0]) -/
#guard_msgs in #eval ((publishedLoop% alloc sourceObserve) (P.run σ),
  (publishedLoop% alloc targetObserve) (run compiled.code machine))
/-- info: false -/
#guard_msgs in #eval ((publishedLoop% alloc targetObserve) (run compiled.code machine) == some [16, 0, 16, 99, 0])

end allocSuccess

namespace allocFailure
abbrev C := publishedLoop% alloc C
abbrev Γ := publishedLoop% alloc Γ
abbrev σ := publishedLoop% alloc σ
abbrev bases := publishedLoop% alloc bases
abbrev machine := publishedLoop% alloc machine
abbrev P := publishedLoop% alloc failingProgram
abbrev compiled := publishedLoop% alloc failingPublic
def out : Memory.Loops.CompiledProg 1 (Frag.init Γ) P := publishedLoop% alloc failingCompiled
attribute [irreducible] out

theorem identity : compiled = Compiler.Compilation.memoryLoops out := by
  unfold out
  exact publishedLoop% alloc failing_shape

theorem input : (Compiler.Compilation.memoryLoops out).Input 1 6 bases σ machine := by
  unfold out
  refine ⟨(publishedLoop% alloc initial).1, by decide +kernel, ?_⟩
  exact Memory.Loops.room_singleton (publishedLoop% alloc conditionCompiled).cert
      (publishedLoop% alloc failingBodyCompiled).cert (by decide +kernel) (publishedLoop% alloc failing_room)

/-- Negative baseline ONLY: this legacy query is not the loop Cost/Room. -/
theorem legacy_zero : compiled.allocationCost σ = 0 := by decide +kernel
theorem source : P.run σ = .error .revert := by
  have fuel : P.runFC 4 σ = .error .revert :=
    (publishedLoop% memory sourceReverted_sound) (by decide +kernel)
  have approx := P.runF_approx 4 σ
  rw [Prog.runF_eq, fuel] at approx
  exact (approx.eq (by intro h; cases h)).symm

theorem false_box : Spec.sat σ (.box P (.not .tt)) := by
  rw [Spec.sat, source]
  intro h
  cases h

theorem prefix_allocation_revert : run compiled.code machine = .revert := by
  rw [identity]
  rcases loop_box out input false_box with
    ⟨_, _, _, _, _, _, _, _, _, _, _, bad⟩ | ⟨_, ht⟩ | ⟨hs, _⟩
  · exact (bad trivial).elim
  · exact ht
  · rw [source] at hs
    cases hs

end allocFailure

namespace scopeAllocSuccess
abbrev C := publishedLoop% scopeAlloc C
abbrev Γ := publishedLoop% scopeAlloc Γ
abbrev σ := publishedLoop% scopeAlloc σ
abbrev bases := publishedLoop% scopeAlloc bases
abbrev machine := publishedLoop% scopeAlloc machine
abbrev P := publishedLoop% scopeAlloc wrappedProgram
abbrev compiled := publishedLoop% scopeAlloc publicResult
def out : Memory.LoopScopes.CompiledProg 1 (Frag.init Γ) P := publishedLoop% scopeAlloc wrappedCompiled
attribute [irreducible] out

theorem identity : compiled = Compiler.Compilation.memoryLoopScopes out := by
  unfold out
  exact publishedLoop% scopeAlloc public_shape

theorem input : (Compiler.Compilation.memoryLoopScopes out).Input 1 6 bases σ machine := by
  unfold out
  refine ⟨(publishedLoop% scopeAlloc initial).1, by decide +kernel, ?_⟩
  apply Memory.LoopScopes.room_ite_true
  · rfl
  · apply Memory.LoopScopes.room_base_singleton
    exact Memory.Loops.room_singleton (publishedLoop% scopeAlloc conditionCompiled).cert
      (publishedLoop% scopeAlloc bodyCompiled).cert (by decide +kernel) (publishedLoop% scopeAlloc loop_room)

/-- Negative baseline ONLY: this legacy query is not the loop Cost/Room. -/
theorem legacy_zero : compiled.allocationCost σ = 0 := by decide +kernel
def output : Solidity.Out C [] Γ := (P.runFC 4 σ).toOption.get (by decide +kernel)
attribute [irreducible] output
theorem source : P.run σ = .ok output := by
  have positive : (P.runFC 4 σ).toOption.isSome = true := by decide +kernel
  have approx := P.runF_approx 4 σ
  rw [Prog.runF_eq] at approx
  cases h : P.runFC 4 σ with
  | error e => rw [h] at positive; cases positive
  | ok o =>
    rw [h] at approx
    have ho : output = o := by simp only [output, h, Except.toOption, Option.get_some]
    exact (approx.eq (by intro bad; cases bad)).symm.trans (congrArg Except.ok ho.symm)

theorem allocated : output.st.H.length = 1 := by decide +kernel

def post : Spec C Γ := .eq (.pvV .here) (.app0 (.lit ⟨0, by decide⟩))
def actualAnswer : PrimTy.uint.Denote := TEnv.get .here output.st.env
attribute [irreducible] actualAnswer
theorem answer_zero : actualAnswer = ⟨0, by decide⟩ := by decide +kernel
theorem diamond : Spec.sat σ (.diamond P post) := by
  rw [Spec.sat, source]
  refine ⟨actualAnswer, ?_, congrArg some answer_zero.symm⟩
  simp only [actualAnswer, Tm.eval]

theorem represented : ∃ o m' base' cost, P.run σ = .ok o ∧ run out.code machine = .ok m' 0 ∧
    Memory.LoopScopes.Cost out.cert σ o cost ∧ Memory.StateRepr 1 1 6 out.frag o.st base' m' ∧
    m'.stack = machine.stack ∧ Memory.BaseExtends σ.H bases base' ∧
    Memory.GrowsAllocator 1 6 cost σ bases machine o.st base' m' ∧ Spec.sat o.st post ∧ o.st.H.length = 1 := by
  obtain ⟨o, m', base', cost, hs, ht, hc, hr, stack, he, hg, hp⟩ :=
    scoped_loop_diamond (C := C) (b := 1) (L := 1) (frame := 6) (Γ := Γ) (Δ := Γ)
      (F := Frag.init Γ) (P := P) out (σ := σ) (base := bases) (m := machine) input (φ := post) diamond
  have eq : o = output := Except.ok.inj (hs.symm.trans source)
  subst o
  exact ⟨output, m', base', cost, source, ht, hc, hr, stack, he, hg, hp, allocated⟩
/-- info: (some (0, 1), some [17, 0, 16, 99, 0]) -/
#guard_msgs in #eval ((publishedLoop% scopeAlloc sourceObserve) (P.run σ),
  (publishedLoop% scopeAlloc targetObserve) (run compiled.code machine))
/-- info: false -/
#guard_msgs in #eval ((publishedLoop% scopeAlloc targetObserve) (run compiled.code machine) == some [16, 0, 16, 99, 0])

end scopeAllocSuccess

namespace scopeAllocFailure
abbrev C := publishedLoop% scopeAlloc C
abbrev Γ := publishedLoop% scopeAlloc Γ
abbrev σ := publishedLoop% scopeAlloc σ
abbrev bases := publishedLoop% scopeAlloc bases
abbrev machine := publishedLoop% scopeAlloc machine
abbrev P := publishedLoop% scopeAlloc wrappedFailing
abbrev compiled := publishedLoop% scopeAlloc failingPublic
def out : Memory.LoopScopes.CompiledProg 1 (Frag.init Γ) P := publishedLoop% scopeAlloc wrappedFailingCompiled
attribute [irreducible] out

theorem identity : compiled = Compiler.Compilation.memoryLoopScopes out := by
  unfold out
  exact publishedLoop% scopeAlloc failing_shape

theorem input : (Compiler.Compilation.memoryLoopScopes out).Input 1 6 bases σ machine := by
  unfold out
  refine ⟨(publishedLoop% scopeAlloc initial).1, by decide +kernel, ?_⟩
  apply Memory.LoopScopes.room_ite_true
  · rfl
  · apply Memory.LoopScopes.room_base_singleton
    exact Memory.Loops.room_singleton (publishedLoop% scopeAlloc conditionCompiled).cert
      (publishedLoop% scopeAlloc failingBodyCompiled).cert (by decide +kernel) (publishedLoop% scopeAlloc failing_room)

/-- Negative baseline ONLY: this legacy query is not the loop Cost/Room. -/
theorem legacy_zero : compiled.allocationCost σ = 0 := by decide +kernel
theorem source : P.run σ = .error .revert := by
  have fuel : P.runFC 4 σ = .error .revert :=
    (publishedLoop% memory sourceReverted_sound) (by decide +kernel)
  have approx := P.runF_approx 4 σ
  rw [Prog.runF_eq, fuel] at approx
  exact (approx.eq (by intro h; cases h)).symm

theorem false_box : Spec.sat σ (.box P (.not .tt)) := by
  rw [Spec.sat, source]
  intro h
  cases h

theorem prefix_allocation_revert : run compiled.code machine = .revert := by
  rw [identity]
  rcases scoped_loop_box out input false_box with
    ⟨_, _, _, _, _, _, _, _, _, _, _, bad⟩ | ⟨_, ht⟩ | ⟨hs, _⟩
  · exact (bad trivial).elim
  · exact ht
  · rw [source] at hs
    cases hs

end scopeAllocFailure

end Solidity.Roadmap.V16.MemoryLoopControls

namespace Solidity.Roadmap.V16.MemoryLoopControls
open Solidity.Evm
namespace capacity
open scopeAllocFailure
abbrev fullMachine := publishedLoop% scopeAlloc fullMachine
theorem full_state_repr : Memory.StateRepr 1 1 6 (Frag.init Γ) σ bases fullMachine :=
  publishedLoop% scopeAlloc full_repr
theorem frame_ok : 1 + out.cert.need ≤ 6 := by decide +kernel
/-- The reached demand persists even though the source ultimately reverts. -/
theorem demand_one : Memory.LoopScopes.Demand out.cert σ 1 := by
  unfold out
  exact .head (.iteTrue rfl (.head (.base (.head (.inr ⟨_, 0, .start, rfl, rfl⟩)))))
theorem full_input_refused : ¬ compiled.Input 1 6 bases σ fullMachine := by
  intro h
  rw [identity] at h
  exact Memory.LoopScopeAllocExamples.full_cursor_refused (h.2.2 1 demand_one)
/-- This is a rejected obsolete-query comparison, never actual Input. -/
theorem legacy_query_would_admit :
    Memory.AllocationInput 1 6 (compiled.allocationCost σ) σ bases fullMachine := by
  rw [legacy_zero]
  exact .inl rfl
end capacity
namespace allocatingNonreturn
abbrev C := publishedLoop% scopeAlloc C
abbrev Γ := publishedLoop% scopeAlloc Γ
abbrev σ := publishedLoop% scopeAlloc σ
abbrev bases := publishedLoop% scopeAlloc bases
abbrev machine := publishedLoop% scopeAlloc machine
abbrev fullMachine := publishedLoop% scopeAlloc fullMachine
abbrev P := publishedLoop% scopeAlloc allocatingSpin
abbrev compiled := publishedLoop% scopeAlloc allocatingSpinPublic
theorem path : compiled.isMemoryLoopScopes = true := by decide +kernel
def out := publishedLoop% scopeAlloc checkedAllocatingSpin
attribute [irreducible] out

theorem input : (Compiler.Compilation.memoryLoopScopes out).Input 1 6 bases σ machine := by
  refine ⟨(publishedLoop% scopeAlloc initial).1, by decide +kernel, ?_⟩
  exact Memory.LoopScopes.room_of_prefixBudget out.cert
    (show Memory.LoopScopes.prefixBudget out.cert σ = some 1 from by decide +kernel)
    (.inr ⟨by decide, publishedLoop% scopeAlloc cursor,
      (publishedLoop% scopeAlloc initial).2, by decide +kernel⟩)

theorem source : P.run σ = .error .diverge :=
  Memory.LoopScopeAllocExamples.allocating_prefix_diverges

theorem identity : Compiler.Compilation.memoryLoopScopes out = compiled := by
  unfold out
  exact scoped_loop_reconstruct compiled path

theorem target : run compiled.code machine = .fault := by
  rw [← identity]
  exact scoped_loop_divergence out input source

theorem full_input_refused : ¬ compiled.Input 1 6 bases σ fullMachine := by
  intro h
  apply Memory.LoopScopeAllocExamples.allocating_prefix_full_refused
  exact ((compiled.memoryLoopScopes_input path 1 6 bases σ fullMachine).1 h).2.2
end allocatingNonreturn
namespace skippedFull
abbrev C := publishedLoop% scopeAlloc C
abbrev Γ := publishedLoop% scopeAlloc Γ
abbrev σ := publishedLoop% scopeAlloc σ
abbrev bases := publishedLoop% scopeAlloc bases
abbrev fullMachine := publishedLoop% scopeAlloc fullMachine
abbrev P := publishedLoop% scopeAlloc skippedProgram
abbrev compiled := publishedLoop% scopeAlloc skippedPublic
theorem path : compiled.isMemoryLoopScopes = true := by decide +kernel
def out : Memory.LoopScopes.CompiledProg 1 (Frag.init Γ) P := publishedLoop% scopeAlloc skippedCompiled
attribute [irreducible] out

theorem syntactic_allocation : out.cert.allocates = true := by decide +kernel

theorem identity : compiled = Compiler.Compilation.memoryLoopScopes out := by
  unfold out
  exact publishedLoop% scopeAlloc skipped_shape

theorem input : compiled.Input 1 6 bases σ fullMachine := by
  rw [identity]
  unfold out
  exact ⟨publishedLoop% scopeAlloc full_repr, by decide +kernel,
    Memory.LoopScopeAllocExamples.skipped_room_full⟩

theorem diamond : Spec.sat σ (.diamond P .tt) := by
  have approx := P.runF_approx 4 σ
  rw [Prog.runF_eq] at approx
  have positive : (P.runFC 4 σ).toOption.isSome = true := by decide +kernel
  cases h : P.runFC 4 σ with
  | error e => rw [h] at positive; cases positive
  | ok o =>
    rw [h] at approx
    have source : P.run σ = .ok o := (approx.eq (by intro bad; cases bad)).symm
    rw [Spec.sat, source]
    trivial

theorem represented : ∃ o m', P.run σ = .ok o ∧ run compiled.code fullMachine = .ok m' 0 ∧
    m'.stack = fullMachine.stack ∧ compiled.Rep 1 6 bases σ fullMachine o.st m' ∧ Spec.sat o.st (.tt : Spec C Γ) := by
  exact scoped_loop_public_diamond (C := C) (b := 1) (Γ := Γ) (Δ := Γ) (F := Frag.init Γ) (P := P)
    compiled path (L := 1) (frame := 6) (σ := σ) (base := bases) (m := fullMachine) (φ := .tt) input diamond
/-- info: (some (2, 0), true, true) -/
#guard_msgs in #eval ((publishedLoop% scopeAlloc sourceObserve) (P.run σ),
  match run compiled.code fullMachine with | .ok m _ => m.mem 0 == Word.val wMax | _ => false,
  match run compiled.code fullMachine with | .ok m _ => m.mem 1 == w[2] | _ => false)
end skippedFull
end Solidity.Roadmap.V16.MemoryLoopControls

namespace Solidity.Roadmap.V16.MemoryLoopControls
open Solidity.Evm
namespace blockAllocation
abbrev C := publishedLoop% scopeAlloc C
abbrev Γ := publishedLoop% scopeAlloc Γ
abbrev σ := publishedLoop% scopeAlloc σ
abbrev bases := publishedLoop% scopeAlloc bases
abbrev machine := publishedLoop% scopeAlloc machine
abbrev P := publishedLoop% scopeAlloc blockProgram
def compiled : Compiler.Compilation 1 (Frag.init Γ) P := publishedLoop% scopeAlloc blockAutomatic
attribute [irreducible] compiled
theorem path : compiled.isMemoryLoopScopes = true := by decide +kernel

theorem input : compiled.Input 1 6 bases σ machine := by
  unfold compiled
  rw [publishedLoop% scopeAlloc automatic_block_result, publishedLoop% scopeAlloc block_shape]
  refine ⟨(publishedLoop% scopeAlloc initial).1, by decide +kernel, ?_⟩
  apply Memory.LoopScopes.room_block
  apply Memory.LoopScopes.room_cons_base_nonallocating
  · decide +kernel
  · exact Memory.Loops.room_singleton (publishedLoop% scopeAlloc conditionCompiled).cert
      (publishedLoop% scopeAlloc bodyCompiled).cert (by decide +kernel) (publishedLoop% scopeAlloc loop_room)

/-- Final Γ fits two words, but the actual block certificate needs temporaries. -/
theorem final_context_frame_refused : ¬ compiled.Input 1 2 bases σ machine := by
  intro h
  unfold compiled at h
  rw [publishedLoop% scopeAlloc automatic_block_result, publishedLoop% scopeAlloc block_shape] at h
  have cap := h.2.1
  have need : (publishedLoop% scopeAlloc blockCompiled).cert.need = 2 := by decide +kernel
  rw [need] at cap
  omega

def output : Solidity.Out C [] Γ := (P.runFC 4 σ).toOption.get (by decide +kernel)
attribute [irreducible] output

theorem source : P.run σ = .ok output := by
  have positive : (P.runFC 4 σ).toOption.isSome = true := by decide +kernel
  have approx := P.runF_approx 4 σ
  rw [Prog.runF_eq] at approx
  cases h : P.runFC 4 σ with
  | error e => rw [h] at positive; cases positive
  | ok o =>
    rw [h] at approx
    have ho : output = o := by simp only [output, h, Except.toOption, Option.get_some]
    exact (approx.eq (by intro bad; cases bad)).symm.trans (congrArg Except.ok ho.symm)

def post : Spec C Γ := .eq (.pvV .here) (.app0 (.lit ⟨0, by decide⟩))
def actualAnswer : PrimTy.uint.Denote := TEnv.get .here output.st.env
attribute [irreducible] actualAnswer

theorem answer_zero : actualAnswer = ⟨0, by decide⟩ := by decide +kernel

theorem diamond : Spec.sat σ (.diamond P post) := by
  rw [Spec.sat, source]
  refine ⟨actualAnswer, ?_, congrArg some answer_zero.symm⟩
  simp only [actualAnswer, Tm.eval]

theorem represented : ∃ o m', P.run σ = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = machine.stack ∧ compiled.Rep 1 6 bases σ machine o.st m' ∧ Spec.sat o.st post := by
  have hi := input
  unfold compiled at hi ⊢
  rw [publishedLoop% scopeAlloc automatic_block_result, publishedLoop% scopeAlloc block_shape] at hi ⊢
  exact scoped_loop_public_diamond (C := C) (b := 1) (Γ := Γ) (Δ := Γ) (F := Frag.init Γ) (P := P)
    (.memoryLoopScopes (publishedLoop% scopeAlloc blockCompiled)) rfl
    (L := 1) (frame := 6) (σ := σ) (base := bases) (m := machine) (φ := post) hi diamond
/-- info: (some (0, 1), some [17, 0, 7, 99, 0]) -/
#guard_msgs in #eval ((publishedLoop% scopeAlloc sourceObserve) (P.run σ),
  (publishedLoop% scopeAlloc targetObserve) (run compiled.code machine))
/-- info: false -/
#guard_msgs in #eval ((publishedLoop% scopeAlloc targetObserve) (run compiled.code machine) == some [17, 0, 16, 99, 0])
end blockAllocation
end Solidity.Roadmap.V16.MemoryLoopControls

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut inductives : Array Json := #[]
  for (n, info) in env.constants.toList do
    if (`Solidity).isPrefixOf n then
      if let .inductInfo info := info then
        inductives := inductives.push (Json.mkObj [
          ("name", toJson n.toString), ("constructors", toJson (info.ctors.map Name.toString))])
  let mut theorems : Array Json := #[]
  for (n, info) in env.constants.toList do
    if (`Solidity.Roadmap.V16).isPrefixOf ((privateToUserName? n).getD n) then
      if let .thmInfo _ := info then
        let axs ← collectAxioms n
        let ty ← liftTermElabM do return (← Meta.ppExpr info.type).pretty
        let premises ← liftTermElabM do
          Meta.forallBoundedTelescope info.type (some info.type.getNumHeadForalls) fun xs _ => do
            let mut rows : Array Json := #[]
            let mut rawType := info.type
            for x in xs do
              let decl ← x.fvarId!.getDecl
              let ty ← Meta.ppExpr decl.type
              let rawDomain := rawType.consumeMData.bindingDomain!
              rawType := rawType.consumeMData.bindingBody!
              rows := rows.push (Json.mkObj [
                ("name", toJson decl.userName.toString), ("type", toJson ty.pretty),
                ("isProp", toJson (← Meta.isProp decl.type)),
                ("closedExpr", toJson (reprStr rawDomain)),
                ("constants", toJson (decl.type.getUsedConstants.toList.map Name.toString))])
            return rows
        theorems := theorems.push (Json.mkObj [
          ("name", toJson n.toString), ("ownerName", toJson ((privateToUserName? n).getD n).toString),
          ("type", toJson ty), ("premises", .arr premises),
          ("typeConstants", toJson (info.type.getUsedConstants.toList.map Name.toString)),
          ("dependencies", toJson (info.getUsedConstantsAsSet.toList.map Name.toString)),
          ("axioms", toJson (axs.toList.map Name.toString))])
  let mut definitions : Array Json := #[]
  for (n, info) in env.constants.toList do
    if (`Solidity.Roadmap.V16).isPrefixOf ((privateToUserName? n).getD n) then
      if let .defnInfo _ := info then
        definitions := definitions.push (Json.mkObj [
          ("name", toJson n.toString), ("ownerName", toJson ((privateToUserName? n).getD n).toString),
          ("dependencies", toJson (info.getUsedConstantsAsSet.toList.map Name.toString))])
  logInfo m!"V16-INVENTORY {(Json.mkObj [("definitions", .arr definitions), ("modules", toJson (env.header.moduleNames.toList.map Name.toString)), ("inductives", .arr inductives), ("theorems", .arr theorems)]).compress}"
