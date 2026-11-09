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
  let module := if mode.getId == `directSpin then `Solidity.Evm.MemoryLoopExamples
    else if mode.getId == `direct then `Solidity.Evm.MemoryLoopSourceExamples
    else if mode.getId == `scope then `Solidity.Evm.MemoryLoopScopeSourceExamples
    else if mode.getId == `branch then `Solidity.Evm.MemoryLoopScopeExamples
    else `Solidity.Evm.MemoryLoopScopeDivergenceExamples
  let ns := if mode.getId == `directSpin then `Solidity.Evm.Memory.LoopExamples
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
open Solidity.Evm
def answerPost {K : Contract} {Δ : Ctx} (_ : Prog K [] (.val .uint :: Δ))
    (n : PrimTy.uint.Denote) : Spec K (.val .uint :: Δ) :=
  .eq (.pvV .here) (.app0 (.lit n))

namespace directArrays
abbrev K := publishedLoop% direct C
abbrev P := publishedLoop% direct arrays
abbrev compiled := publishedLoop% direct compiledArrays
def out : Memory.Loops.CompiledProg 1 (Frag.init []) P := publishedLoop% direct checkedArrays
attribute [irreducible] out
abbrev bases := publishedLoop% direct bases
abbrev machine := publishedLoop% direct machine
abbrev initial := State.init K

theorem public_path : compiled.isMemoryLoops = true := by decide +kernel

theorem input : (Compiler.Compilation.memoryLoops out).Input 1 64 bases initial machine := by
  refine ⟨((publishedLoop% direct initial_repr) K).1, by decide +kernel, ?_⟩
  exact Memory.Loops.room_of_prefixBudget out.cert
    (show Memory.Loops.prefixBudget out.cert initial = some 3 from by decide +kernel)
    (.inr ⟨by decide, wmod 128, ((publishedLoop% direct initial_repr) K).2, by decide +kernel⟩)

abbrev OutputCtx : Ctx := publishedContext% P
def output : Solidity.Out K [] OutputCtx := (P.runFC 4 initial).toOption.get (by decide +kernel)
attribute [irreducible] output

def actualAnswer : PrimTy.uint.Denote := TEnv.get .here output.st.env
attribute [irreducible] actualAnswer
theorem fuel_output : P.runFC 4 initial = .ok output := by
  have positive : (P.runFC 4 initial).toOption.isSome = true := by decide +kernel
  cases h : P.runFC 4 initial with
  | error e => rw [h] at positive; cases positive
  | ok o => simp only [output, h, Except.toOption, Option.get_some]
theorem answer_value : actualAnswer = ⟨4, by decide⟩ := by decide +kernel

def post := answerPost P ⟨4, by decide⟩

theorem source : P.run initial = .ok output := by
  have approx := P.runF_approx 4 initial
  rw [Prog.runF_eq, fuel_output] at approx
  exact (approx.eq (by intro bad; cases bad)).symm

theorem diamond : Spec.sat initial (.diamond P post) := by
  rw [Spec.sat, source]
  refine ⟨actualAnswer, ?_, congrArg some answer_value.symm⟩
  simp only [actualAnswer, Tm.eval]

theorem represented : ∃ o m' base' cost,
    P.run initial = .ok o ∧ run out.code machine = .ok m' 0 ∧
    Memory.Loops.Cost out.cert initial o cost ∧
    Memory.StateRepr 1 1 64 out.frag o.st base' m' ∧ m'.stack = [w[77]] ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.GrowsAllocator 1 64 cost initial bases machine o.st base' m' ∧ Spec.sat o.st post := by
  exact loop_diamond (C := K) (b := 1) (L := 1) (frame := 64) (Γ := []) (Δ := OutputCtx) (F := Frag.init []) (P := P) out (σ := initial) (base := bases) (m := machine) input (φ := post) diamond

theorem wrong_frame : ¬ (Compiler.Compilation.memoryLoops out).Input 1 0 bases initial machine := by
  intro h
  have bad := h.2.1
  omega

theorem false_post : ¬ Spec.sat initial (.diamond P (.not .tt)) := by
  intro h
  obtain ⟨o, _, _, _, _, _, _, _, _, _, _, bad⟩ := loop_diamond out input h
  exact bad trivial

def wrongPost : Spec K OutputCtx := answerPost P ⟨5, by decide⟩

theorem wrong_answer : ¬ Spec.sat initial (.diamond P wrongPost) := by
  rw [Spec.sat, source]
  change ¬ (∃ v, (Tm.pvV .here : Tm K OutputCtx (.val .uint)).eval output.st = some v ∧ _ = some v)
  rintro ⟨v, hv, hw⟩
  have actual : (Tm.pvV .here : Tm K OutputCtx (.val .uint)).eval output.st = some actualAnswer := by
    simp only [actualAnswer, Tm.eval]
  rw [actual] at hv
  have values : actualAnswer = (⟨5, by decide⟩ : PrimTy.uint.Denote) :=
    (Option.some.inj hv).trans (Option.some.inj hw).symm
  exact (by decide : (⟨4, by decide⟩ : PrimTy.uint.Denote) ≠ ⟨5, by decide⟩)
    (answer_value.symm.trans values)

end directArrays

namespace directArraysIR
abbrev K := publishedLoop% direct irC
abbrev P := publishedLoop% direct arraysIR
abbrev compiled := publishedLoop% direct compiledArraysIR
def out : Memory.Loops.CompiledProg 1 (Frag.init []) P := publishedLoop% direct checkedArraysIR
attribute [irreducible] out
abbrev bases := publishedLoop% direct bases
abbrev machine := publishedLoop% direct machine
abbrev initial := State.init K

theorem public_path : compiled.isMemoryLoops = true := by decide +kernel

theorem input : (Compiler.Compilation.memoryLoops out).Input 1 64 bases initial machine := by
  refine ⟨((publishedLoop% direct initial_repr) K).1, by decide +kernel, ?_⟩
  exact Memory.Loops.room_of_prefixBudget out.cert
    (show Memory.Loops.prefixBudget out.cert initial = some 3 from by decide +kernel)
    (.inr ⟨by decide, wmod 128, ((publishedLoop% direct initial_repr) K).2, by decide +kernel⟩)

abbrev OutputCtx : Ctx := publishedContext% P
def output : Solidity.Out K [] OutputCtx := (P.runFC 4 initial).toOption.get (by decide +kernel)
attribute [irreducible] output

def actualAnswer : PrimTy.uint.Denote := TEnv.get .here output.st.env
attribute [irreducible] actualAnswer
theorem fuel_output : P.runFC 4 initial = .ok output := by
  have positive : (P.runFC 4 initial).toOption.isSome = true := by decide +kernel
  cases h : P.runFC 4 initial with
  | error e => rw [h] at positive; cases positive
  | ok o => simp only [output, h, Except.toOption, Option.get_some]
theorem answer_value : actualAnswer = ⟨4, by decide⟩ := by decide +kernel

def post := answerPost P ⟨4, by decide⟩

theorem source : P.run initial = .ok output := by
  have approx := P.runF_approx 4 initial
  rw [Prog.runF_eq, fuel_output] at approx
  exact (approx.eq (by intro bad; cases bad)).symm

theorem diamond : Spec.sat initial (.diamond P post) := by
  rw [Spec.sat, source]
  refine ⟨actualAnswer, ?_, congrArg some answer_value.symm⟩
  simp only [actualAnswer, Tm.eval]

theorem represented : ∃ o m' base' cost,
    P.run initial = .ok o ∧ run out.code machine = .ok m' 0 ∧
    Memory.Loops.Cost out.cert initial o cost ∧
    Memory.StateRepr 1 1 64 out.frag o.st base' m' ∧ m'.stack = [w[77]] ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.GrowsAllocator 1 64 cost initial bases machine o.st base' m' ∧ Spec.sat o.st post := by
  exact loop_diamond (C := K) (b := 1) (L := 1) (frame := 64) (Γ := []) (Δ := OutputCtx) (F := Frag.init []) (P := P) out (σ := initial) (base := bases) (m := machine) input (φ := post) diamond

theorem wrong_frame : ¬ (Compiler.Compilation.memoryLoops out).Input 1 0 bases initial machine := by
  intro h
  have bad := h.2.1
  omega

theorem false_post : ¬ Spec.sat initial (.diamond P (.not .tt)) := by
  intro h
  obtain ⟨o, _, _, _, _, _, _, _, _, _, _, bad⟩ := loop_diamond out input h
  exact bad trivial

def wrongPost : Spec K OutputCtx := answerPost P ⟨5, by decide⟩

theorem wrong_answer : ¬ Spec.sat initial (.diamond P wrongPost) := by
  rw [Spec.sat, source]
  change ¬ (∃ v, (Tm.pvV .here : Tm K OutputCtx (.val .uint)).eval output.st = some v ∧ _ = some v)
  rintro ⟨v, hv, hw⟩
  have actual : (Tm.pvV .here : Tm K OutputCtx (.val .uint)).eval output.st = some actualAnswer := by
    simp only [actualAnswer, Tm.eval]
  rw [actual] at hv
  have values : actualAnswer = (⟨5, by decide⟩ : PrimTy.uint.Denote) :=
    (Option.some.inj hv).trans (Option.some.inj hw).symm
  exact (by decide : (⟨4, by decide⟩ : PrimTy.uint.Denote) ≠ ⟨5, by decide⟩)
    (answer_value.symm.trans values)

end directArraysIR

namespace directRecords
abbrev K := publishedLoop% direct C
abbrev P := publishedLoop% direct records
abbrev compiled := publishedLoop% direct compiledRecords
def out : Memory.Loops.CompiledProg 1 (Frag.init []) P := publishedLoop% direct checkedRecords
attribute [irreducible] out
abbrev bases := publishedLoop% direct bases
abbrev machine := publishedLoop% direct machine
abbrev initial := State.init K

theorem public_path : compiled.isMemoryLoops = true := by decide +kernel

theorem input : (Compiler.Compilation.memoryLoops out).Input 1 64 bases initial machine := by
  refine ⟨((publishedLoop% direct initial_repr) K).1, by decide +kernel, ?_⟩
  exact Memory.Loops.room_of_prefixBudget out.cert
    (show Memory.Loops.prefixBudget out.cert initial = some 2 from by decide +kernel)
    (.inr ⟨by decide, wmod 128, ((publishedLoop% direct initial_repr) K).2, by decide +kernel⟩)

abbrev OutputCtx : Ctx := publishedContext% P
def output : Solidity.Out K [] OutputCtx := (P.runFC 4 initial).toOption.get (by decide +kernel)
attribute [irreducible] output

def actualAnswer : PrimTy.uint.Denote := TEnv.get .here output.st.env
attribute [irreducible] actualAnswer
theorem fuel_output : P.runFC 4 initial = .ok output := by
  have positive : (P.runFC 4 initial).toOption.isSome = true := by decide +kernel
  cases h : P.runFC 4 initial with
  | error e => rw [h] at positive; cases positive
  | ok o => simp only [output, h, Except.toOption, Option.get_some]
theorem answer_value : actualAnswer = ⟨3, by decide⟩ := by decide +kernel

def post := answerPost P ⟨3, by decide⟩

theorem source : P.run initial = .ok output := by
  have approx := P.runF_approx 4 initial
  rw [Prog.runF_eq, fuel_output] at approx
  exact (approx.eq (by intro bad; cases bad)).symm

theorem diamond : Spec.sat initial (.diamond P post) := by
  rw [Spec.sat, source]
  refine ⟨actualAnswer, ?_, congrArg some answer_value.symm⟩
  simp only [actualAnswer, Tm.eval]

theorem represented : ∃ o m' base' cost,
    P.run initial = .ok o ∧ run out.code machine = .ok m' 0 ∧
    Memory.Loops.Cost out.cert initial o cost ∧
    Memory.StateRepr 1 1 64 out.frag o.st base' m' ∧ m'.stack = [w[77]] ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.GrowsAllocator 1 64 cost initial bases machine o.st base' m' ∧ Spec.sat o.st post := by
  exact loop_diamond (C := K) (b := 1) (L := 1) (frame := 64) (Γ := []) (Δ := OutputCtx) (F := Frag.init []) (P := P) out (σ := initial) (base := bases) (m := machine) input (φ := post) diamond

theorem wrong_frame : ¬ (Compiler.Compilation.memoryLoops out).Input 1 0 bases initial machine := by
  intro h
  have bad := h.2.1
  omega

theorem false_post : ¬ Spec.sat initial (.diamond P (.not .tt)) := by
  intro h
  obtain ⟨o, _, _, _, _, _, _, _, _, _, _, bad⟩ := loop_diamond out input h
  exact bad trivial

def wrongPost : Spec K OutputCtx := answerPost P ⟨4, by decide⟩

theorem wrong_answer : ¬ Spec.sat initial (.diamond P wrongPost) := by
  rw [Spec.sat, source]
  change ¬ (∃ v, (Tm.pvV .here : Tm K OutputCtx (.val .uint)).eval output.st = some v ∧ _ = some v)
  rintro ⟨v, hv, hw⟩
  have actual : (Tm.pvV .here : Tm K OutputCtx (.val .uint)).eval output.st = some actualAnswer := by
    simp only [actualAnswer, Tm.eval]
  rw [actual] at hv
  have values : actualAnswer = (⟨4, by decide⟩ : PrimTy.uint.Denote) :=
    (Option.some.inj hv).trans (Option.some.inj hw).symm
  exact (by decide : (⟨3, by decide⟩ : PrimTy.uint.Denote) ≠ ⟨4, by decide⟩)
    (answer_value.symm.trans values)

end directRecords

namespace directRecordsIR
abbrev K := publishedLoop% direct irC
abbrev P := publishedLoop% direct recordsIR
abbrev compiled := publishedLoop% direct compiledRecordsIR
def out : Memory.Loops.CompiledProg 1 (Frag.init []) P := publishedLoop% direct checkedRecordsIR
attribute [irreducible] out
abbrev bases := publishedLoop% direct bases
abbrev machine := publishedLoop% direct machine
abbrev initial := State.init K

theorem public_path : compiled.isMemoryLoops = true := by decide +kernel

theorem input : (Compiler.Compilation.memoryLoops out).Input 1 64 bases initial machine := by
  refine ⟨((publishedLoop% direct initial_repr) K).1, by decide +kernel, ?_⟩
  exact Memory.Loops.room_of_prefixBudget out.cert
    (show Memory.Loops.prefixBudget out.cert initial = some 2 from by decide +kernel)
    (.inr ⟨by decide, wmod 128, ((publishedLoop% direct initial_repr) K).2, by decide +kernel⟩)

abbrev OutputCtx : Ctx := publishedContext% P
def output : Solidity.Out K [] OutputCtx := (P.runFC 4 initial).toOption.get (by decide +kernel)
attribute [irreducible] output

def actualAnswer : PrimTy.uint.Denote := TEnv.get .here output.st.env
attribute [irreducible] actualAnswer
theorem fuel_output : P.runFC 4 initial = .ok output := by
  have positive : (P.runFC 4 initial).toOption.isSome = true := by decide +kernel
  cases h : P.runFC 4 initial with
  | error e => rw [h] at positive; cases positive
  | ok o => simp only [output, h, Except.toOption, Option.get_some]
theorem answer_value : actualAnswer = ⟨3, by decide⟩ := by decide +kernel

def post := answerPost P ⟨3, by decide⟩

theorem source : P.run initial = .ok output := by
  have approx := P.runF_approx 4 initial
  rw [Prog.runF_eq, fuel_output] at approx
  exact (approx.eq (by intro bad; cases bad)).symm

theorem diamond : Spec.sat initial (.diamond P post) := by
  rw [Spec.sat, source]
  refine ⟨actualAnswer, ?_, congrArg some answer_value.symm⟩
  simp only [actualAnswer, Tm.eval]

theorem represented : ∃ o m' base' cost,
    P.run initial = .ok o ∧ run out.code machine = .ok m' 0 ∧
    Memory.Loops.Cost out.cert initial o cost ∧
    Memory.StateRepr 1 1 64 out.frag o.st base' m' ∧ m'.stack = [w[77]] ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.GrowsAllocator 1 64 cost initial bases machine o.st base' m' ∧ Spec.sat o.st post := by
  exact loop_diamond (C := K) (b := 1) (L := 1) (frame := 64) (Γ := []) (Δ := OutputCtx) (F := Frag.init []) (P := P) out (σ := initial) (base := bases) (m := machine) input (φ := post) diamond

theorem wrong_frame : ¬ (Compiler.Compilation.memoryLoops out).Input 1 0 bases initial machine := by
  intro h
  have bad := h.2.1
  omega

theorem false_post : ¬ Spec.sat initial (.diamond P (.not .tt)) := by
  intro h
  obtain ⟨o, _, _, _, _, _, _, _, _, _, _, bad⟩ := loop_diamond out input h
  exact bad trivial

def wrongPost : Spec K OutputCtx := answerPost P ⟨4, by decide⟩

theorem wrong_answer : ¬ Spec.sat initial (.diamond P wrongPost) := by
  rw [Spec.sat, source]
  change ¬ (∃ v, (Tm.pvV .here : Tm K OutputCtx (.val .uint)).eval output.st = some v ∧ _ = some v)
  rintro ⟨v, hv, hw⟩
  have actual : (Tm.pvV .here : Tm K OutputCtx (.val .uint)).eval output.st = some actualAnswer := by
    simp only [actualAnswer, Tm.eval]
  rw [actual] at hv
  have values : actualAnswer = (⟨4, by decide⟩ : PrimTy.uint.Denote) :=
    (Option.some.inj hv).trans (Option.some.inj hw).symm
  exact (by decide : (⟨3, by decide⟩ : PrimTy.uint.Denote) ≠ ⟨4, by decide⟩)
    (answer_value.symm.trans values)

end directRecordsIR

namespace scopeArrays
abbrev K := publishedLoop% scope C
abbrev P := publishedLoop% scope arrays
abbrev compiled := publishedLoop% scope compiledArrays
def out : Memory.LoopScopes.CompiledProg 1 (Frag.init []) P := publishedLoop% scope checkedArrays
attribute [irreducible] out
abbrev bases := publishedLoop% scope bases
abbrev machine := publishedLoop% scope machine
abbrev initial := State.init K

theorem public_path : compiled.isMemoryLoopScopes = true := by decide +kernel

theorem input : (Compiler.Compilation.memoryLoopScopes out).Input 1 64 bases initial machine := by
  refine ⟨((publishedLoop% scope initial_repr) K).1, by decide +kernel, ?_⟩
  exact Memory.LoopScopes.room_of_prefixBudget out.cert
    (show Memory.LoopScopes.prefixBudget out.cert initial = some 3 from by decide +kernel)
    (.inr ⟨by decide, wmod 128, ((publishedLoop% scope initial_repr) K).2, by decide +kernel⟩)

abbrev OutputCtx : Ctx := publishedContext% P
def output : Solidity.Out K [] OutputCtx := (P.runFC 4 initial).toOption.get (by decide +kernel)
attribute [irreducible] output

def actualAnswer : PrimTy.uint.Denote := TEnv.get .here output.st.env
attribute [irreducible] actualAnswer
theorem fuel_output : P.runFC 4 initial = .ok output := by
  have positive : (P.runFC 4 initial).toOption.isSome = true := by decide +kernel
  cases h : P.runFC 4 initial with
  | error e => rw [h] at positive; cases positive
  | ok o => simp only [output, h, Except.toOption, Option.get_some]
theorem answer_value : actualAnswer = ⟨4, by decide⟩ := by decide +kernel

def post := answerPost P ⟨4, by decide⟩

theorem source : P.run initial = .ok output := by
  have approx := P.runF_approx 4 initial
  rw [Prog.runF_eq, fuel_output] at approx
  exact (approx.eq (by intro bad; cases bad)).symm

theorem diamond : Spec.sat initial (.diamond P post) := by
  rw [Spec.sat, source]
  refine ⟨actualAnswer, ?_, congrArg some answer_value.symm⟩
  simp only [actualAnswer, Tm.eval]

theorem represented : ∃ o m' base' cost,
    P.run initial = .ok o ∧ run out.code machine = .ok m' 0 ∧
    Memory.LoopScopes.Cost out.cert initial o cost ∧
    Memory.StateRepr 1 1 64 out.frag o.st base' m' ∧ m'.stack = [w[77]] ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.GrowsAllocator 1 64 cost initial bases machine o.st base' m' ∧ Spec.sat o.st post := by
  exact scoped_loop_diamond (C := K) (b := 1) (L := 1) (frame := 64) (Γ := []) (Δ := OutputCtx) (F := Frag.init []) (P := P) out (σ := initial) (base := bases) (m := machine) input (φ := post) diamond

theorem wrong_frame : ¬ (Compiler.Compilation.memoryLoopScopes out).Input 1 0 bases initial machine := by
  intro h
  have bad := h.2.1
  omega

theorem false_post : ¬ Spec.sat initial (.diamond P (.not .tt)) := by
  intro h
  obtain ⟨o, _, _, _, _, _, _, _, _, _, _, bad⟩ := scoped_loop_diamond out input h
  exact bad trivial

def wrongPost : Spec K OutputCtx := answerPost P ⟨5, by decide⟩

theorem wrong_answer : ¬ Spec.sat initial (.diamond P wrongPost) := by
  rw [Spec.sat, source]
  change ¬ (∃ v, (Tm.pvV .here : Tm K OutputCtx (.val .uint)).eval output.st = some v ∧ _ = some v)
  rintro ⟨v, hv, hw⟩
  have actual : (Tm.pvV .here : Tm K OutputCtx (.val .uint)).eval output.st = some actualAnswer := by
    simp only [actualAnswer, Tm.eval]
  rw [actual] at hv
  have values : actualAnswer = (⟨5, by decide⟩ : PrimTy.uint.Denote) :=
    (Option.some.inj hv).trans (Option.some.inj hw).symm
  exact (by decide : (⟨4, by decide⟩ : PrimTy.uint.Denote) ≠ ⟨5, by decide⟩)
    (answer_value.symm.trans values)

end scopeArrays

namespace scopeArraysIR
abbrev K := publishedLoop% scope irC
abbrev P := publishedLoop% scope arraysIR
abbrev compiled := publishedLoop% scope compiledArraysIR
def out : Memory.LoopScopes.CompiledProg 1 (Frag.init []) P := publishedLoop% scope checkedArraysIR
attribute [irreducible] out
abbrev bases := publishedLoop% scope bases
abbrev machine := publishedLoop% scope machine
abbrev initial := State.init K

theorem public_path : compiled.isMemoryLoopScopes = true := by decide +kernel

theorem input : (Compiler.Compilation.memoryLoopScopes out).Input 1 64 bases initial machine := by
  refine ⟨((publishedLoop% scope initial_repr) K).1, by decide +kernel, ?_⟩
  exact Memory.LoopScopes.room_of_prefixBudget out.cert
    (show Memory.LoopScopes.prefixBudget out.cert initial = some 3 from by decide +kernel)
    (.inr ⟨by decide, wmod 128, ((publishedLoop% scope initial_repr) K).2, by decide +kernel⟩)

abbrev OutputCtx : Ctx := publishedContext% P
def output : Solidity.Out K [] OutputCtx := (P.runFC 4 initial).toOption.get (by decide +kernel)
attribute [irreducible] output

def actualAnswer : PrimTy.uint.Denote := TEnv.get .here output.st.env
attribute [irreducible] actualAnswer
theorem fuel_output : P.runFC 4 initial = .ok output := by
  have positive : (P.runFC 4 initial).toOption.isSome = true := by decide +kernel
  cases h : P.runFC 4 initial with
  | error e => rw [h] at positive; cases positive
  | ok o => simp only [output, h, Except.toOption, Option.get_some]
theorem answer_value : actualAnswer = ⟨4, by decide⟩ := by decide +kernel

def post := answerPost P ⟨4, by decide⟩

theorem source : P.run initial = .ok output := by
  have approx := P.runF_approx 4 initial
  rw [Prog.runF_eq, fuel_output] at approx
  exact (approx.eq (by intro bad; cases bad)).symm

theorem diamond : Spec.sat initial (.diamond P post) := by
  rw [Spec.sat, source]
  refine ⟨actualAnswer, ?_, congrArg some answer_value.symm⟩
  simp only [actualAnswer, Tm.eval]

theorem represented : ∃ o m' base' cost,
    P.run initial = .ok o ∧ run out.code machine = .ok m' 0 ∧
    Memory.LoopScopes.Cost out.cert initial o cost ∧
    Memory.StateRepr 1 1 64 out.frag o.st base' m' ∧ m'.stack = [w[77]] ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.GrowsAllocator 1 64 cost initial bases machine o.st base' m' ∧ Spec.sat o.st post := by
  exact scoped_loop_diamond (C := K) (b := 1) (L := 1) (frame := 64) (Γ := []) (Δ := OutputCtx) (F := Frag.init []) (P := P) out (σ := initial) (base := bases) (m := machine) input (φ := post) diamond

theorem wrong_frame : ¬ (Compiler.Compilation.memoryLoopScopes out).Input 1 0 bases initial machine := by
  intro h
  have bad := h.2.1
  omega

theorem false_post : ¬ Spec.sat initial (.diamond P (.not .tt)) := by
  intro h
  obtain ⟨o, _, _, _, _, _, _, _, _, _, _, bad⟩ := scoped_loop_diamond out input h
  exact bad trivial

def wrongPost : Spec K OutputCtx := answerPost P ⟨5, by decide⟩

theorem wrong_answer : ¬ Spec.sat initial (.diamond P wrongPost) := by
  rw [Spec.sat, source]
  change ¬ (∃ v, (Tm.pvV .here : Tm K OutputCtx (.val .uint)).eval output.st = some v ∧ _ = some v)
  rintro ⟨v, hv, hw⟩
  have actual : (Tm.pvV .here : Tm K OutputCtx (.val .uint)).eval output.st = some actualAnswer := by
    simp only [actualAnswer, Tm.eval]
  rw [actual] at hv
  have values : actualAnswer = (⟨5, by decide⟩ : PrimTy.uint.Denote) :=
    (Option.some.inj hv).trans (Option.some.inj hw).symm
  exact (by decide : (⟨4, by decide⟩ : PrimTy.uint.Denote) ≠ ⟨5, by decide⟩)
    (answer_value.symm.trans values)

end scopeArraysIR

namespace scopeRecords
abbrev K := publishedLoop% scope C
abbrev P := publishedLoop% scope records
abbrev compiled := publishedLoop% scope compiledRecords
def out : Memory.LoopScopes.CompiledProg 1 (Frag.init []) P := publishedLoop% scope checkedRecords
attribute [irreducible] out
abbrev bases := publishedLoop% scope bases
abbrev machine := publishedLoop% scope machine
abbrev initial := State.init K

theorem public_path : compiled.isMemoryLoopScopes = true := by decide +kernel

theorem input : (Compiler.Compilation.memoryLoopScopes out).Input 1 64 bases initial machine := by
  refine ⟨((publishedLoop% scope initial_repr) K).1, by decide +kernel, ?_⟩
  exact Memory.LoopScopes.room_of_prefixBudget out.cert
    (show Memory.LoopScopes.prefixBudget out.cert initial = some 2 from by decide +kernel)
    (.inr ⟨by decide, wmod 128, ((publishedLoop% scope initial_repr) K).2, by decide +kernel⟩)

abbrev OutputCtx : Ctx := publishedContext% P
def output : Solidity.Out K [] OutputCtx := (P.runFC 4 initial).toOption.get (by decide +kernel)
attribute [irreducible] output

def actualAnswer : PrimTy.uint.Denote := TEnv.get .here output.st.env
attribute [irreducible] actualAnswer
theorem fuel_output : P.runFC 4 initial = .ok output := by
  have positive : (P.runFC 4 initial).toOption.isSome = true := by decide +kernel
  cases h : P.runFC 4 initial with
  | error e => rw [h] at positive; cases positive
  | ok o => simp only [output, h, Except.toOption, Option.get_some]
theorem answer_value : actualAnswer = ⟨3, by decide⟩ := by decide +kernel

def post := answerPost P ⟨3, by decide⟩

theorem source : P.run initial = .ok output := by
  have approx := P.runF_approx 4 initial
  rw [Prog.runF_eq, fuel_output] at approx
  exact (approx.eq (by intro bad; cases bad)).symm

theorem diamond : Spec.sat initial (.diamond P post) := by
  rw [Spec.sat, source]
  refine ⟨actualAnswer, ?_, congrArg some answer_value.symm⟩
  simp only [actualAnswer, Tm.eval]

theorem represented : ∃ o m' base' cost,
    P.run initial = .ok o ∧ run out.code machine = .ok m' 0 ∧
    Memory.LoopScopes.Cost out.cert initial o cost ∧
    Memory.StateRepr 1 1 64 out.frag o.st base' m' ∧ m'.stack = [w[77]] ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.GrowsAllocator 1 64 cost initial bases machine o.st base' m' ∧ Spec.sat o.st post := by
  exact scoped_loop_diamond (C := K) (b := 1) (L := 1) (frame := 64) (Γ := []) (Δ := OutputCtx) (F := Frag.init []) (P := P) out (σ := initial) (base := bases) (m := machine) input (φ := post) diamond

theorem wrong_frame : ¬ (Compiler.Compilation.memoryLoopScopes out).Input 1 0 bases initial machine := by
  intro h
  have bad := h.2.1
  omega

theorem false_post : ¬ Spec.sat initial (.diamond P (.not .tt)) := by
  intro h
  obtain ⟨o, _, _, _, _, _, _, _, _, _, _, bad⟩ := scoped_loop_diamond out input h
  exact bad trivial

def wrongPost : Spec K OutputCtx := answerPost P ⟨4, by decide⟩

theorem wrong_answer : ¬ Spec.sat initial (.diamond P wrongPost) := by
  rw [Spec.sat, source]
  change ¬ (∃ v, (Tm.pvV .here : Tm K OutputCtx (.val .uint)).eval output.st = some v ∧ _ = some v)
  rintro ⟨v, hv, hw⟩
  have actual : (Tm.pvV .here : Tm K OutputCtx (.val .uint)).eval output.st = some actualAnswer := by
    simp only [actualAnswer, Tm.eval]
  rw [actual] at hv
  have values : actualAnswer = (⟨4, by decide⟩ : PrimTy.uint.Denote) :=
    (Option.some.inj hv).trans (Option.some.inj hw).symm
  exact (by decide : (⟨3, by decide⟩ : PrimTy.uint.Denote) ≠ ⟨4, by decide⟩)
    (answer_value.symm.trans values)

end scopeRecords

namespace scopeRecordsIR
abbrev K := publishedLoop% scope irC
abbrev P := publishedLoop% scope recordsIR
abbrev compiled := publishedLoop% scope compiledRecordsIR
def out : Memory.LoopScopes.CompiledProg 1 (Frag.init []) P := publishedLoop% scope checkedRecordsIR
attribute [irreducible] out
abbrev bases := publishedLoop% scope bases
abbrev machine := publishedLoop% scope machine
abbrev initial := State.init K

theorem public_path : compiled.isMemoryLoopScopes = true := by decide +kernel

theorem input : (Compiler.Compilation.memoryLoopScopes out).Input 1 64 bases initial machine := by
  refine ⟨((publishedLoop% scope initial_repr) K).1, by decide +kernel, ?_⟩
  exact Memory.LoopScopes.room_of_prefixBudget out.cert
    (show Memory.LoopScopes.prefixBudget out.cert initial = some 2 from by decide +kernel)
    (.inr ⟨by decide, wmod 128, ((publishedLoop% scope initial_repr) K).2, by decide +kernel⟩)

abbrev OutputCtx : Ctx := publishedContext% P
def output : Solidity.Out K [] OutputCtx := (P.runFC 4 initial).toOption.get (by decide +kernel)
attribute [irreducible] output

def actualAnswer : PrimTy.uint.Denote := TEnv.get .here output.st.env
attribute [irreducible] actualAnswer
theorem fuel_output : P.runFC 4 initial = .ok output := by
  have positive : (P.runFC 4 initial).toOption.isSome = true := by decide +kernel
  cases h : P.runFC 4 initial with
  | error e => rw [h] at positive; cases positive
  | ok o => simp only [output, h, Except.toOption, Option.get_some]
theorem answer_value : actualAnswer = ⟨3, by decide⟩ := by decide +kernel

def post := answerPost P ⟨3, by decide⟩

theorem source : P.run initial = .ok output := by
  have approx := P.runF_approx 4 initial
  rw [Prog.runF_eq, fuel_output] at approx
  exact (approx.eq (by intro bad; cases bad)).symm

theorem diamond : Spec.sat initial (.diamond P post) := by
  rw [Spec.sat, source]
  refine ⟨actualAnswer, ?_, congrArg some answer_value.symm⟩
  simp only [actualAnswer, Tm.eval]

theorem represented : ∃ o m' base' cost,
    P.run initial = .ok o ∧ run out.code machine = .ok m' 0 ∧
    Memory.LoopScopes.Cost out.cert initial o cost ∧
    Memory.StateRepr 1 1 64 out.frag o.st base' m' ∧ m'.stack = [w[77]] ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.GrowsAllocator 1 64 cost initial bases machine o.st base' m' ∧ Spec.sat o.st post := by
  exact scoped_loop_diamond (C := K) (b := 1) (L := 1) (frame := 64) (Γ := []) (Δ := OutputCtx) (F := Frag.init []) (P := P) out (σ := initial) (base := bases) (m := machine) input (φ := post) diamond

theorem wrong_frame : ¬ (Compiler.Compilation.memoryLoopScopes out).Input 1 0 bases initial machine := by
  intro h
  have bad := h.2.1
  omega

theorem false_post : ¬ Spec.sat initial (.diamond P (.not .tt)) := by
  intro h
  obtain ⟨o, _, _, _, _, _, _, _, _, _, _, bad⟩ := scoped_loop_diamond out input h
  exact bad trivial

def wrongPost : Spec K OutputCtx := answerPost P ⟨4, by decide⟩

theorem wrong_answer : ¬ Spec.sat initial (.diamond P wrongPost) := by
  rw [Spec.sat, source]
  change ¬ (∃ v, (Tm.pvV .here : Tm K OutputCtx (.val .uint)).eval output.st = some v ∧ _ = some v)
  rintro ⟨v, hv, hw⟩
  have actual : (Tm.pvV .here : Tm K OutputCtx (.val .uint)).eval output.st = some actualAnswer := by
    simp only [actualAnswer, Tm.eval]
  rw [actual] at hv
  have values : actualAnswer = (⟨4, by decide⟩ : PrimTy.uint.Denote) :=
    (Option.some.inj hv).trans (Option.some.inj hw).symm
  exact (by decide : (⟨3, by decide⟩ : PrimTy.uint.Denote) ≠ ⟨4, by decide⟩)
    (answer_value.symm.trans values)

end scopeRecordsIR



namespace blockTurns
open Memory.CompileExamples
abbrev P := publishedLoop% branch blockTurns
abbrev compiled := publishedLoop% branch compiledBlock
def out : Memory.LoopScopes.CompiledProg 0 (Frag.init Memory.CompileExamples.Γ) P := compiled.memoryLoopScopesResult (by decide +kernel)
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
theorem represented : ∃ o m' base' cost, P.run σ = .ok o ∧ run out.code machine = .ok m' 0 ∧
    Memory.LoopScopes.Cost out.cert σ o cost ∧ Memory.StateRepr 1 0 4 out.frag o.st base' m' ∧
    m'.stack = machine.stack ∧ Memory.BaseExtends σ.H base base' ∧
    Memory.GrowsAllocator 0 4 cost σ base machine o.st base' m' ∧ Spec.sat o.st (.tt : Spec C Γ) :=
  scoped_loop_diamond out input diamond
end blockTurns

namespace yesTurns
open Memory.CompileExamples
abbrev P := publishedLoop% branch yesTurns
abbrev compiled := publishedLoop% branch compiledYes
def out : Memory.LoopScopes.CompiledProg 0 (Frag.init Memory.CompileExamples.Γ) P := compiled.memoryLoopScopesResult (by decide +kernel)
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
theorem represented : ∃ o m' base' cost, P.run σ = .ok o ∧ run out.code machine = .ok m' 0 ∧
    Memory.LoopScopes.Cost out.cert σ o cost ∧ Memory.StateRepr 1 0 4 out.frag o.st base' m' ∧
    m'.stack = machine.stack ∧ Memory.BaseExtends σ.H base base' ∧
    Memory.GrowsAllocator 0 4 cost σ base machine o.st base' m' ∧ Spec.sat o.st (.tt : Spec C Γ) :=
  scoped_loop_diamond out input diamond
end yesTurns

namespace noTurns
open Memory.CompileExamples
abbrev P := publishedLoop% branch noTurns
abbrev compiled := publishedLoop% branch compiledNo
def out : Memory.LoopScopes.CompiledProg 0 (Frag.init Memory.CompileExamples.Γ) P := compiled.memoryLoopScopesResult (by decide +kernel)
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
theorem represented : ∃ o m' base' cost, P.run σ = .ok o ∧ run out.code machine = .ok m' 0 ∧
    Memory.LoopScopes.Cost out.cert σ o cost ∧ Memory.StateRepr 1 0 4 out.frag o.st base' m' ∧
    m'.stack = machine.stack ∧ Memory.BaseExtends σ.H base base' ∧
    Memory.GrowsAllocator 0 4 cost σ base machine o.st base' m' ∧ Spec.sat o.st (.tt : Spec C Γ) :=
  scoped_loop_diamond out input diamond
end noTurns

namespace divergent
open Memory.CompileExamples
abbrev compiled := publishedLoop% divergence selectedPublic
abbrev P := publishedLoop% divergence selected
def out : Memory.LoopScopes.CompiledProg 0 (Frag.init Memory.CompileExamples.Γ) P := compiled.memoryLoopScopesResult (by decide +kernel)
attribute [irreducible] out
theorem input : (Compiler.Compilation.memoryLoopScopes out).Input 1 4 base σ machine := by
  exact ⟨fixture_repr, by decide +kernel,
    Memory.LoopScopes.room_nonallocating out.cert (by decide +kernel) σ base machine⟩
theorem source : (publishedLoop% divergence selected).run σ = .error .diverge :=
  publishedLoop% divergence selected_diverges
theorem target : run out.code machine = .fault := scoped_loop_divergence out input source
theorem not_diamond : ¬ Spec.sat σ (.diamond (publishedLoop% divergence selected) .tt) := by
  rw [Spec.sat, source]
  intro h
  cases h
end divergent
end Solidity.Roadmap.V16.MemoryLoopControls



namespace Solidity.Roadmap.V16.MemoryLoopControls
open Solidity.Evm

namespace directArrays
/-- The complete ordered observation is tied to the very witness supplied by
NEW transport. Numeric baselines below are bounded native tests, not proofs. -/
theorem ordered_transport : ∃ o m' base' cost,
    P.run initial = .ok o ∧ run out.code machine = .ok m' 0 ∧
    Memory.Loops.Cost out.cert initial o cost ∧
    Memory.StateRepr 1 1 64 out.frag o.st base' m' ∧ m'.stack = [w[77]] ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.GrowsAllocator 1 64 cost initial bases machine o.st base' m' ∧ Spec.sat o.st post ∧
    (publishedLoop% direct targetCells) [0, 1, 2, 3, 4, 128, 129, 130, 63] (.ok m' 0) = (publishedLoop% direct targetCells) [0, 1, 2, 3, 4, 128, 129, 130, 63] (run out.code machine) := by
  obtain ⟨o, m', base', cost, hs, ht, hc, hr, stack, he, hg, hp⟩ := represented
  exact ⟨o, m', base', cost, hs, ht, hc, hr, stack, he, hg, hp, congrArg ((publishedLoop% direct targetCells) [0, 1, 2, 3, 4, 128, 129, 130, 63]) ht.symm⟩
/-- info: (some 4, some [131, 128, 128, 2, 4, 2, 3, 4, 99]) -/
#guard_msgs in #eval ((publishedLoop% direct sourceTop) .here (P.run initial),
  (publishedLoop% direct targetCells) [0, 1, 2, 3, 4, 128, 129, 130, 63] (run out.code machine))
/-- info: false -/
#guard_msgs in #eval ((publishedLoop% direct targetCells) [0, 1, 2, 3, 4, 128, 129, 130, 63] (run out.code machine) == some [132, 128, 128, 2, 4, 2, 3, 4, 99])
/-- info: false -/
#guard_msgs in #eval ((publishedLoop% direct targetCells) [0, 1, 2, 3, 4, 128, 129, 130, 63] (run out.code machine) == some [131, 129, 128, 2, 4, 2, 3, 4, 99])
end directArrays

namespace directArraysIR
/-- The complete ordered observation is tied to the very witness supplied by
NEW transport. Numeric baselines below are bounded native tests, not proofs. -/
theorem ordered_transport : ∃ o m' base' cost,
    P.run initial = .ok o ∧ run out.code machine = .ok m' 0 ∧
    Memory.Loops.Cost out.cert initial o cost ∧
    Memory.StateRepr 1 1 64 out.frag o.st base' m' ∧ m'.stack = [w[77]] ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.GrowsAllocator 1 64 cost initial bases machine o.st base' m' ∧ Spec.sat o.st post ∧
    (publishedLoop% direct targetCells) [0, 1, 2, 3, 4, 128, 129, 130, 63] (.ok m' 0) = (publishedLoop% direct targetCells) [0, 1, 2, 3, 4, 128, 129, 130, 63] (run out.code machine) := by
  obtain ⟨o, m', base', cost, hs, ht, hc, hr, stack, he, hg, hp⟩ := represented
  exact ⟨o, m', base', cost, hs, ht, hc, hr, stack, he, hg, hp, congrArg ((publishedLoop% direct targetCells) [0, 1, 2, 3, 4, 128, 129, 130, 63]) ht.symm⟩
/-- info: (some 4, some [131, 128, 128, 2, 4, 2, 3, 4, 99]) -/
#guard_msgs in #eval ((publishedLoop% direct sourceTop) .here (P.run initial),
  (publishedLoop% direct targetCells) [0, 1, 2, 3, 4, 128, 129, 130, 63] (run out.code machine))
/-- info: false -/
#guard_msgs in #eval ((publishedLoop% direct targetCells) [0, 1, 2, 3, 4, 128, 129, 130, 63] (run out.code machine) == some [132, 128, 128, 2, 4, 2, 3, 4, 99])
/-- info: false -/
#guard_msgs in #eval ((publishedLoop% direct targetCells) [0, 1, 2, 3, 4, 128, 129, 130, 63] (run out.code machine) == some [131, 129, 128, 2, 4, 2, 3, 4, 99])
end directArraysIR

namespace directRecords
/-- The complete ordered observation is tied to the very witness supplied by
NEW transport. Numeric baselines below are bounded native tests, not proofs. -/
theorem ordered_transport : ∃ o m' base' cost,
    P.run initial = .ok o ∧ run out.code machine = .ok m' 0 ∧
    Memory.Loops.Cost out.cert initial o cost ∧
    Memory.StateRepr 1 1 64 out.frag o.st base' m' ∧ m'.stack = [w[77]] ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.GrowsAllocator 1 64 cost initial bases machine o.st base' m' ∧ Spec.sat o.st post ∧
    (publishedLoop% direct targetCells) [0, 1, 2, 3, 128, 63] (.ok m' 0) = (publishedLoop% direct targetCells) [0, 1, 2, 3, 128, 63] (run out.code machine) := by
  obtain ⟨o, m', base', cost, hs, ht, hc, hr, stack, he, hg, hp⟩ := represented
  exact ⟨o, m', base', cost, hs, ht, hc, hr, stack, he, hg, hp, congrArg ((publishedLoop% direct targetCells) [0, 1, 2, 3, 128, 63]) ht.symm⟩
/-- info: (some 3, some [130, 128, 128, 128, 3, 99]) -/
#guard_msgs in #eval ((publishedLoop% direct sourceTop) .here (P.run initial),
  (publishedLoop% direct targetCells) [0, 1, 2, 3, 128, 63] (run out.code machine))
/-- info: false -/
#guard_msgs in #eval ((publishedLoop% direct targetCells) [0, 1, 2, 3, 128, 63] (run out.code machine) == some [131, 128, 128, 128, 3, 99])
/-- info: false -/
#guard_msgs in #eval ((publishedLoop% direct targetCells) [0, 1, 2, 3, 128, 63] (run out.code machine) == some [130, 129, 128, 128, 3, 99])
end directRecords

namespace directRecordsIR
/-- The complete ordered observation is tied to the very witness supplied by
NEW transport. Numeric baselines below are bounded native tests, not proofs. -/
theorem ordered_transport : ∃ o m' base' cost,
    P.run initial = .ok o ∧ run out.code machine = .ok m' 0 ∧
    Memory.Loops.Cost out.cert initial o cost ∧
    Memory.StateRepr 1 1 64 out.frag o.st base' m' ∧ m'.stack = [w[77]] ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.GrowsAllocator 1 64 cost initial bases machine o.st base' m' ∧ Spec.sat o.st post ∧
    (publishedLoop% direct targetCells) [0, 1, 2, 3, 128, 63] (.ok m' 0) = (publishedLoop% direct targetCells) [0, 1, 2, 3, 128, 63] (run out.code machine) := by
  obtain ⟨o, m', base', cost, hs, ht, hc, hr, stack, he, hg, hp⟩ := represented
  exact ⟨o, m', base', cost, hs, ht, hc, hr, stack, he, hg, hp, congrArg ((publishedLoop% direct targetCells) [0, 1, 2, 3, 128, 63]) ht.symm⟩
/-- info: (some 3, some [130, 0, 5, 128, 3, 99]) -/
#guard_msgs in #eval ((publishedLoop% direct sourceTop) .here (P.run initial),
  (publishedLoop% direct targetCells) [0, 1, 2, 3, 128, 63] (run out.code machine))
/-- info: false -/
#guard_msgs in #eval ((publishedLoop% direct targetCells) [0, 1, 2, 3, 128, 63] (run out.code machine) == some [131, 0, 5, 128, 3, 99])
/-- info: false -/
#guard_msgs in #eval ((publishedLoop% direct targetCells) [0, 1, 2, 3, 128, 63] (run out.code machine) == some [130, 0, 5, 129, 3, 99])
end directRecordsIR

namespace scopeArrays
/-- The complete ordered observation is tied to the very witness supplied by
NEW transport. Numeric baselines below are bounded native tests, not proofs. -/
theorem ordered_transport : ∃ o m' base' cost,
    P.run initial = .ok o ∧ run out.code machine = .ok m' 0 ∧
    Memory.LoopScopes.Cost out.cert initial o cost ∧
    Memory.StateRepr 1 1 64 out.frag o.st base' m' ∧ m'.stack = [w[77]] ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.GrowsAllocator 1 64 cost initial bases machine o.st base' m' ∧ Spec.sat o.st post ∧
    (publishedLoop% scope targetCells) [0, 1, 2, 3, 4, 128, 129, 130, 63] (.ok m' 0) = (publishedLoop% scope targetCells) [0, 1, 2, 3, 4, 128, 129, 130, 63] (run out.code machine) := by
  obtain ⟨o, m', base', cost, hs, ht, hc, hr, stack, he, hg, hp⟩ := represented
  exact ⟨o, m', base', cost, hs, ht, hc, hr, stack, he, hg, hp, congrArg ((publishedLoop% scope targetCells) [0, 1, 2, 3, 4, 128, 129, 130, 63]) ht.symm⟩
/-- info: (some 4, some [131, 128, 128, 2, 4, 2, 3, 4, 99]) -/
#guard_msgs in #eval ((publishedLoop% scope sourceTop) .here (P.run initial),
  (publishedLoop% scope targetCells) [0, 1, 2, 3, 4, 128, 129, 130, 63] (run out.code machine))
/-- info: false -/
#guard_msgs in #eval ((publishedLoop% scope targetCells) [0, 1, 2, 3, 4, 128, 129, 130, 63] (run out.code machine) == some [132, 128, 128, 2, 4, 2, 3, 4, 99])
/-- info: false -/
#guard_msgs in #eval ((publishedLoop% scope targetCells) [0, 1, 2, 3, 4, 128, 129, 130, 63] (run out.code machine) == some [131, 129, 128, 2, 4, 2, 3, 4, 99])
end scopeArrays

namespace scopeArraysIR
/-- The complete ordered observation is tied to the very witness supplied by
NEW transport. Numeric baselines below are bounded native tests, not proofs. -/
theorem ordered_transport : ∃ o m' base' cost,
    P.run initial = .ok o ∧ run out.code machine = .ok m' 0 ∧
    Memory.LoopScopes.Cost out.cert initial o cost ∧
    Memory.StateRepr 1 1 64 out.frag o.st base' m' ∧ m'.stack = [w[77]] ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.GrowsAllocator 1 64 cost initial bases machine o.st base' m' ∧ Spec.sat o.st post ∧
    (publishedLoop% scope targetCells) [0, 1, 2, 3, 4, 128, 129, 130, 63] (.ok m' 0) = (publishedLoop% scope targetCells) [0, 1, 2, 3, 4, 128, 129, 130, 63] (run out.code machine) := by
  obtain ⟨o, m', base', cost, hs, ht, hc, hr, stack, he, hg, hp⟩ := represented
  exact ⟨o, m', base', cost, hs, ht, hc, hr, stack, he, hg, hp, congrArg ((publishedLoop% scope targetCells) [0, 1, 2, 3, 4, 128, 129, 130, 63]) ht.symm⟩
/-- info: (some 4, some [131, 128, 128, 2, 4, 2, 3, 4, 99]) -/
#guard_msgs in #eval ((publishedLoop% scope sourceTop) .here (P.run initial),
  (publishedLoop% scope targetCells) [0, 1, 2, 3, 4, 128, 129, 130, 63] (run out.code machine))
/-- info: false -/
#guard_msgs in #eval ((publishedLoop% scope targetCells) [0, 1, 2, 3, 4, 128, 129, 130, 63] (run out.code machine) == some [132, 128, 128, 2, 4, 2, 3, 4, 99])
/-- info: false -/
#guard_msgs in #eval ((publishedLoop% scope targetCells) [0, 1, 2, 3, 4, 128, 129, 130, 63] (run out.code machine) == some [131, 129, 128, 2, 4, 2, 3, 4, 99])
end scopeArraysIR

namespace scopeRecords
/-- The complete ordered observation is tied to the very witness supplied by
NEW transport. Numeric baselines below are bounded native tests, not proofs. -/
theorem ordered_transport : ∃ o m' base' cost,
    P.run initial = .ok o ∧ run out.code machine = .ok m' 0 ∧
    Memory.LoopScopes.Cost out.cert initial o cost ∧
    Memory.StateRepr 1 1 64 out.frag o.st base' m' ∧ m'.stack = [w[77]] ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.GrowsAllocator 1 64 cost initial bases machine o.st base' m' ∧ Spec.sat o.st post ∧
    (publishedLoop% scope targetCells) [0, 1, 2, 3, 128, 63] (.ok m' 0) = (publishedLoop% scope targetCells) [0, 1, 2, 3, 128, 63] (run out.code machine) := by
  obtain ⟨o, m', base', cost, hs, ht, hc, hr, stack, he, hg, hp⟩ := represented
  exact ⟨o, m', base', cost, hs, ht, hc, hr, stack, he, hg, hp, congrArg ((publishedLoop% scope targetCells) [0, 1, 2, 3, 128, 63]) ht.symm⟩
/-- info: (some 3, some [130, 128, 128, 128, 3, 99]) -/
#guard_msgs in #eval ((publishedLoop% scope sourceTop) .here (P.run initial),
  (publishedLoop% scope targetCells) [0, 1, 2, 3, 128, 63] (run out.code machine))
/-- info: false -/
#guard_msgs in #eval ((publishedLoop% scope targetCells) [0, 1, 2, 3, 128, 63] (run out.code machine) == some [131, 128, 128, 128, 3, 99])
/-- info: false -/
#guard_msgs in #eval ((publishedLoop% scope targetCells) [0, 1, 2, 3, 128, 63] (run out.code machine) == some [130, 129, 128, 128, 3, 99])
end scopeRecords

namespace scopeRecordsIR
/-- The complete ordered observation is tied to the very witness supplied by
NEW transport. Numeric baselines below are bounded native tests, not proofs. -/
theorem ordered_transport : ∃ o m' base' cost,
    P.run initial = .ok o ∧ run out.code machine = .ok m' 0 ∧
    Memory.LoopScopes.Cost out.cert initial o cost ∧
    Memory.StateRepr 1 1 64 out.frag o.st base' m' ∧ m'.stack = [w[77]] ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.GrowsAllocator 1 64 cost initial bases machine o.st base' m' ∧ Spec.sat o.st post ∧
    (publishedLoop% scope targetCells) [0, 1, 2, 3, 128, 63] (.ok m' 0) = (publishedLoop% scope targetCells) [0, 1, 2, 3, 128, 63] (run out.code machine) := by
  obtain ⟨o, m', base', cost, hs, ht, hc, hr, stack, he, hg, hp⟩ := represented
  exact ⟨o, m', base', cost, hs, ht, hc, hr, stack, he, hg, hp, congrArg ((publishedLoop% scope targetCells) [0, 1, 2, 3, 128, 63]) ht.symm⟩
/-- info: (some 3, some [130, 0, 5, 128, 3, 99]) -/
#guard_msgs in #eval ((publishedLoop% scope sourceTop) .here (P.run initial),
  (publishedLoop% scope targetCells) [0, 1, 2, 3, 128, 63] (run out.code machine))
/-- info: false -/
#guard_msgs in #eval ((publishedLoop% scope targetCells) [0, 1, 2, 3, 128, 63] (run out.code machine) == some [131, 0, 5, 128, 3, 99])
/-- info: false -/
#guard_msgs in #eval ((publishedLoop% scope targetCells) [0, 1, 2, 3, 128, 63] (run out.code machine) == some [130, 0, 5, 129, 3, 99])
end scopeRecordsIR

end Solidity.Roadmap.V16.MemoryLoopControls

namespace Solidity.Roadmap.V16.MemoryLoopControls
open Solidity.Evm Memory.CompileExamples
namespace directSpin
abbrev out := publishedLoop% directSpin spinCompiled
theorem input : (Compiler.Compilation.memoryLoops out).Input 1 4 base σ machine := by
  exact ⟨fixture_repr, by decide +kernel,
    Memory.Loops.room_nonallocating out.cert (by decide +kernel) σ base machine⟩
theorem target : run out.code machine = .fault :=
  loop_divergence out input Memory.LoopExamples.source_diverges
theorem not_revert : run out.code machine ≠ .revert := by
  rw [target]
  intro h
  cases h
end directSpin
namespace skippedSpin
abbrev compiled := publishedLoop% divergence skippedPublic
abbrev out := compiled.memoryLoopScopesResult (by decide +kernel)
abbrev P := publishedLoop% divergence skipped
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
theorem target_success : ∃ m', run out.code machine = .ok m' 0 ∧ m'.stack = machine.stack := by
  obtain ⟨_, m', _, _, _, ht, _, _, stack, _⟩ := scoped_loop_diamond out input diamond
  exact ⟨m', ht, stack⟩
theorem not_fault : run out.code machine ≠ .fault := by
  obtain ⟨_, ht, _⟩ := target_success
  rw [ht]
  intro h
  cases h
end skippedSpin
end Solidity.Roadmap.V16.MemoryLoopControls


namespace Solidity.Roadmap.V16.MemoryLoopControls
open Solidity.Evm

namespace directArrays
theorem compiler_identity : Compiler.Compilation.memoryLoops out = compiled := by
  unfold out
  exact loop_reconstruct compiled public_path

theorem public_input : compiled.Input 1 64 bases initial machine := by
  rw [← compiler_identity]
  exact input

theorem public_represented : ∃ o m', P.run initial = .ok o ∧
    run compiled.code machine = .ok m' 0 ∧ m'.stack = machine.stack ∧
    compiled.Rep 1 64 bases initial machine o.st m' ∧ Spec.sat o.st post := by
  exact loop_public_diamond (C := K) (b := 1) (Γ := []) (Δ := OutputCtx)
    (F := Frag.init []) (P := P) compiled public_path (L := 1) (frame := 64)
    (σ := initial) (base := bases) (m := machine) (φ := post) public_input diamond
end directArrays

namespace directArraysIR
theorem compiler_identity : Compiler.Compilation.memoryLoops out = compiled := by
  unfold out
  exact loop_reconstruct compiled public_path

theorem public_input : compiled.Input 1 64 bases initial machine := by
  rw [← compiler_identity]
  exact input

theorem public_represented : ∃ o m', P.run initial = .ok o ∧
    run compiled.code machine = .ok m' 0 ∧ m'.stack = machine.stack ∧
    compiled.Rep 1 64 bases initial machine o.st m' ∧ Spec.sat o.st post := by
  exact loop_public_diamond (C := K) (b := 1) (Γ := []) (Δ := OutputCtx)
    (F := Frag.init []) (P := P) compiled public_path (L := 1) (frame := 64)
    (σ := initial) (base := bases) (m := machine) (φ := post) public_input diamond
end directArraysIR

namespace directRecords
theorem compiler_identity : Compiler.Compilation.memoryLoops out = compiled := by
  unfold out
  exact loop_reconstruct compiled public_path

theorem public_input : compiled.Input 1 64 bases initial machine := by
  rw [← compiler_identity]
  exact input

theorem public_represented : ∃ o m', P.run initial = .ok o ∧
    run compiled.code machine = .ok m' 0 ∧ m'.stack = machine.stack ∧
    compiled.Rep 1 64 bases initial machine o.st m' ∧ Spec.sat o.st post := by
  exact loop_public_diamond (C := K) (b := 1) (Γ := []) (Δ := OutputCtx)
    (F := Frag.init []) (P := P) compiled public_path (L := 1) (frame := 64)
    (σ := initial) (base := bases) (m := machine) (φ := post) public_input diamond
end directRecords

namespace directRecordsIR
theorem compiler_identity : Compiler.Compilation.memoryLoops out = compiled := by
  unfold out
  exact loop_reconstruct compiled public_path

theorem public_input : compiled.Input 1 64 bases initial machine := by
  rw [← compiler_identity]
  exact input

theorem public_represented : ∃ o m', P.run initial = .ok o ∧
    run compiled.code machine = .ok m' 0 ∧ m'.stack = machine.stack ∧
    compiled.Rep 1 64 bases initial machine o.st m' ∧ Spec.sat o.st post := by
  exact loop_public_diamond (C := K) (b := 1) (Γ := []) (Δ := OutputCtx)
    (F := Frag.init []) (P := P) compiled public_path (L := 1) (frame := 64)
    (σ := initial) (base := bases) (m := machine) (φ := post) public_input diamond
end directRecordsIR

namespace scopeArrays
theorem compiler_identity : Compiler.Compilation.memoryLoopScopes out = compiled := by
  unfold out
  exact scoped_loop_reconstruct compiled public_path

theorem public_input : compiled.Input 1 64 bases initial machine := by
  rw [← compiler_identity]
  exact input

theorem public_represented : ∃ o m', P.run initial = .ok o ∧
    run compiled.code machine = .ok m' 0 ∧ m'.stack = machine.stack ∧
    compiled.Rep 1 64 bases initial machine o.st m' ∧ Spec.sat o.st post := by
  exact scoped_loop_public_diamond (C := K) (b := 1) (Γ := []) (Δ := OutputCtx)
    (F := Frag.init []) (P := P) compiled public_path (L := 1) (frame := 64)
    (σ := initial) (base := bases) (m := machine) (φ := post) public_input diamond
end scopeArrays

namespace scopeArraysIR
theorem compiler_identity : Compiler.Compilation.memoryLoopScopes out = compiled := by
  unfold out
  exact scoped_loop_reconstruct compiled public_path

theorem public_input : compiled.Input 1 64 bases initial machine := by
  rw [← compiler_identity]
  exact input

theorem public_represented : ∃ o m', P.run initial = .ok o ∧
    run compiled.code machine = .ok m' 0 ∧ m'.stack = machine.stack ∧
    compiled.Rep 1 64 bases initial machine o.st m' ∧ Spec.sat o.st post := by
  exact scoped_loop_public_diamond (C := K) (b := 1) (Γ := []) (Δ := OutputCtx)
    (F := Frag.init []) (P := P) compiled public_path (L := 1) (frame := 64)
    (σ := initial) (base := bases) (m := machine) (φ := post) public_input diamond
end scopeArraysIR

namespace scopeRecords
theorem compiler_identity : Compiler.Compilation.memoryLoopScopes out = compiled := by
  unfold out
  exact scoped_loop_reconstruct compiled public_path

theorem public_input : compiled.Input 1 64 bases initial machine := by
  rw [← compiler_identity]
  exact input

theorem public_represented : ∃ o m', P.run initial = .ok o ∧
    run compiled.code machine = .ok m' 0 ∧ m'.stack = machine.stack ∧
    compiled.Rep 1 64 bases initial machine o.st m' ∧ Spec.sat o.st post := by
  exact scoped_loop_public_diamond (C := K) (b := 1) (Γ := []) (Δ := OutputCtx)
    (F := Frag.init []) (P := P) compiled public_path (L := 1) (frame := 64)
    (σ := initial) (base := bases) (m := machine) (φ := post) public_input diamond
end scopeRecords

namespace scopeRecordsIR
theorem compiler_identity : Compiler.Compilation.memoryLoopScopes out = compiled := by
  unfold out
  exact scoped_loop_reconstruct compiled public_path

theorem public_input : compiled.Input 1 64 bases initial machine := by
  rw [← compiler_identity]
  exact input

theorem public_represented : ∃ o m', P.run initial = .ok o ∧
    run compiled.code machine = .ok m' 0 ∧ m'.stack = machine.stack ∧
    compiled.Rep 1 64 bases initial machine o.st m' ∧ Spec.sat o.st post := by
  exact scoped_loop_public_diamond (C := K) (b := 1) (Γ := []) (Δ := OutputCtx)
    (F := Frag.init []) (P := P) compiled public_path (L := 1) (frame := 64)
    (σ := initial) (base := bases) (m := machine) (φ := post) public_input diamond
end scopeRecordsIR

end Solidity.Roadmap.V16.MemoryLoopControls

namespace Solidity.Roadmap.V16.MemoryLoopControls
open Solidity.Evm Memory.CompileExamples
namespace divergent
theorem false_box : Spec.sat σ (.box P (.not .tt)) := by
  rw [Spec.sat, source]
  intro h
  cases h
theorem box_fault : run out.code machine = .fault := by
  rcases scoped_loop_box out input false_box with
    ⟨_, _, _, _, _, _, _, _, _, _, _, bad⟩ | ⟨hs, _⟩ | ⟨_, ht⟩
  · exact (bad trivial).elim
  · rw [source] at hs
    cases hs
  · exact ht
end divergent
namespace directSpin
abbrev P := publishedLoop% directSpin spin
theorem false_box : Spec.sat σ (.box P (.not .tt)) := by
  rw [Spec.sat, Memory.LoopExamples.source_diverges]
  intro h
  cases h
theorem box_fault : run out.code machine = .fault := by
  rcases loop_box out input false_box with
    ⟨_, _, _, _, _, _, _, _, _, _, _, bad⟩ | ⟨hs, _⟩ | ⟨_, ht⟩
  · exact (bad trivial).elim
  · rw [Memory.LoopExamples.source_diverges] at hs
    cases hs
  · exact ht
end directSpin
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
