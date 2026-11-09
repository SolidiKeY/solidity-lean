import Solidity.Examples.Roadmap.V16.FiniteHeapConsumer
import Solidity.Examples.Roadmap.V16.CompilerConsumer
import Solidity.Evm.MemoryObjectArrayExamples
import Solidity.Evm.MemoryRefArrayExamples
import Solidity.Evm.MemoryAllocSourceExamples
import Solidity.Evm.MemoryCompileExamples
import Lean

/-! Actual published populated heaps and public compiler outputs, read only.
No replacement source program, AST or execution semantics. -/
open Lean Elab Term in
elab "publishedHeap%" family:ident n:ident : term => do
  let (module, ns) := if family.getId == `objects then
      (`Solidity.Evm.MemoryObjectArrayExamples, `Solidity.Evm.Memory.ObjectArrayExamples)
    else if family.getId == `references then
      (`Solidity.Evm.MemoryRefArrayExamples, `Solidity.Evm.Memory.RefArrayExamples)
    else if family.getId == `memory then
      (`Solidity.Evm.MemoryCompileExamples, `Solidity.Evm.Memory.CompileExamples)
    else (`Solidity.Evm.MemoryAllocSourceExamples, `Solidity.Evm.Memory.AllocSourceExamples)
  let name := mkPrivateNameCore module (ns ++ n.getId)
  unless (← getEnv).contains name do throwError "missing published heap fixture {name}"
  return mkConst name

namespace Solidity.Roadmap.V16.FiniteHeapControls
open Solidity.Evm

theorem get_source {α : Type} {r : TRes α} (h : r.toOption.isSome = true) :
    r = .ok (r.toOption.get h) := by
  cases r with
  | error e => cases h
  | ok o => rfl

namespace objects
abbrev K := publishedHeap% objects C
abbrev Γ : Ctx := publishedHeap% objects Γ
abbrev initial := publishedHeap% objects state
abbrev bases := publishedHeap% objects base
abbrev machine := publishedHeap% objects machine
def P : Prog K Γ Γ := publishedHeap% objects program
attribute [irreducible] P
def compiled : Compiler.Compilation 1 (Frag.init Γ) P := by
  simpa only [P] using (publishedHeap% objects compiled)
attribute [irreducible] compiled
theorem path : compiled.isObject = true := by decide +kernel
theorem input : compiled.Input 1 8 bases initial machine := by
  simpa only [compiled,P] using Memory.ObjectArrayExamples.compiled_input
theorem finite_path : compiled.isMemory = true ∨ compiled.isReferenceArray = true ∨ compiled.isObject = true :=
  .inr (.inr path)

theorem positive : (P.run initial).toOption.isSome = true := by unfold P; decide +kernel
def output : Solidity.Out K initial.H Γ := (P.run initial).toOption.get positive
attribute [irreducible] output
theorem source : P.run initial = .ok output := by simpa only [output] using get_source positive

def readChild (i : Idx Γ (.mem (publishedHeap% objects childTy))) : Tm K Γ (.val .uint) :=
  .app2 .read (.app0 .memory) (.app2 (.mat .dyn) (.pvI i) (.app0 (.lit ⟨0,by decide⟩)))
def post : Spec K Γ :=
  .and (.eq (readChild (.there .here)) (.app0 (.lit ⟨11,by decide⟩)))
    (.eq (readChild (.there (.there .here))) (.app0 (.lit ⟨13,by decide⟩)))
theorem output_post : Spec.sat output.st post := by
  constructor
  · exact ⟨⟨11,by decide⟩,by decide +kernel,rfl⟩
  · exact ⟨⟨13,by decide⟩,by decide +kernel,rfl⟩
theorem diamond : Spec.sat initial (.diamond P post) := by
  simpa only [Spec.sat,source] using output_post

theorem represented : ∃ o m', P.run initial = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ compiled.Rep 1 8 bases initial machine o.st m' ∧ Spec.sat o.st post :=
  finite_heap_diamond compiled finite_path input diamond

theorem source_observed : (publishedHeap% objects observeSource) (P.run initial) =
    some [32,16,24,24,16,11,13] := by
  simpa only [P] using Memory.ObjectArrayExamples.source_observation
theorem target_observed : (publishedHeap% objects observeTarget) (run compiled.code machine) =
    some [32,16,24,24,16,11,13] := by
  simpa only [compiled,P] using Memory.ObjectArrayExamples.target_observation

theorem ordered : ∃ o m', P.run initial = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ compiled.Rep 1 8 bases initial machine o.st m' ∧ Spec.sat o.st post ∧
    (publishedHeap% objects observeSource) (.ok o) = some [32,16,24,24,16,11,13] ∧
    (publishedHeap% objects observeTarget) (.ok m' 0) = some [32,16,24,24,16,11,13] := by
  obtain ⟨o,m',hs,ht,stack,rep,hpost⟩ := represented
  refine ⟨o,m',hs,ht,stack,rep,hpost,?_,?_⟩
  · rw [← hs]; exact source_observed
  · rw [← ht]; exact target_observed

theorem wrong_output : ¬ ∃ m', run compiled.code machine = .ok m' 0 ∧
    (publishedHeap% objects observeTarget) (.ok m' 0) = some [32,16,24,24,16,11,14] := by
  rintro ⟨m',ht,wrong⟩
  obtain ⟨o,n,hs,hn,stack,rep,post,src,good⟩ := ordered
  have eq : n = m' := by cases hn.symm.trans ht; rfl
  subst n
  rw [wrong] at good
  cases good

theorem wrong_alias : ¬ ∃ m', run compiled.code machine = .ok m' 0 ∧
    (publishedHeap% objects observeTarget) (.ok m' 0) = some [32,16,24,16,16,11,13] := by
  rintro ⟨m',ht,wrong⟩
  obtain ⟨o,n,hs,hn,stack,rep,post,src,good⟩ := ordered
  have eq : n = m' := by cases hn.symm.trans ht; rfl
  subst n
  rw [wrong] at good
  cases good

theorem wrong_frame : ¬ compiled.Input 1 0 bases initial machine := by
  intro h
  have hbound := ((compiled.object_input path 1 0 bases initial machine).mp h).2
  omega

theorem wrong_pointer : ¬ compiled.Input 1 8 bases initial (Memory.writeMachine machine 32 w[24]) := by
  intro h
  have rep := ((compiled.object_input path 1 8 bases initial _).mp h).1
  exact Memory.ObjectArrayExamples.wrong_pointer_refuted (rep.heap.arrays .fixed (publishedHeap% objects parent))

theorem allocator : ∃ o m', P.run initial = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    Memory.Objects.AllocatorRepr o.st.heap bases 8 ⟨40,by decide⟩ m' ∧ m'.mem 0 = w[40] := by
  obtain ⟨o,m',hs,ht,stack,rep,post⟩ := represented
  have keeps := ((compiled.object_rep path 1 8 bases initial machine o.st m').mp rep).2
  have ha := keeps ⟨40,by decide⟩ (by decide) Memory.ObjectArrayExamples.initial_allocator
  exact ⟨o,m',hs,ht,ha,ha.free.cell⟩

def badP (k : Fin 3) : Prog K Γ Γ := (publishedHeap% objects failingProgram) k
def badCompiled (k : Fin 3) : Compiler.Compilation 1 (Frag.init Γ) (badP k) := by
  simpa only [badP] using ((publishedHeap% objects failed) k)
attribute [irreducible] badP badCompiled
theorem bad_path (k : Fin 3) : (badCompiled k).isMemory = true ∨
    (badCompiled k).isReferenceArray = true ∨ (badCompiled k).isObject = true := by
  have h : ∀ k : Fin 3, (badCompiled k).isObject = true := by decide +kernel
  exact .inr (.inr (h k))

theorem bad_input (k : Fin 3) : (badCompiled k).Input 1 8 bases initial machine := by
  simpa only [badCompiled,badP] using Memory.ObjectArrayExamples.failed_input k
theorem bad_source (k : Fin 3) : (badP k).run initial = .error .revert := by
  unfold badP
  have old := Memory.ObjectArrayExamples.source_bounds k
  have observation : ∀ r : TRes (Solidity.Out K initial.H Γ),
      (publishedHeap% objects sourceReverted) r =
        (match r with | .error .revert => true | _ => false) := by
    intro r
    cases r with
    | ok o => rfl
    | error e => cases e <;> rfl
  rw [observation] at old
  cases hs : ((publishedHeap% objects failingProgram) k).run initial with
  | ok o => rw [hs] at old; cases old
  | error e =>
    rw [hs] at old
    cases e <;> first | rfl | cases old

theorem exact_failure (k : Fin 3) : (badP k).run initial = .error .revert ∧
    run (badCompiled k).code machine = .revert :=
  ⟨bad_source k,(finite_heap_failure (badCompiled k) (bad_path k) (bad_input k) (bad_source k)).2⟩
theorem false_box (k : Fin 3) : Spec.sat initial (.box (badP k) (.not .tt)) := by
  simp only [Spec.sat,bad_source k,ne_eq,reduceCtorEq,not_false_eq_true]
theorem box_failure (k : Fin 3) : run (badCompiled k).code machine = .revert := by
  rcases finite_heap_box (badCompiled k) (bad_path k) (bad_input k) (false_box k) with
    ⟨o,_,hs,_⟩ | ⟨_,ht⟩
  · rw [bad_source k] at hs; cases hs
  · exact ht
theorem no_diamond (k : Fin 3) : ¬ Spec.sat initial (.diamond (badP k) .tt) := by
  intro h
  obtain ⟨o,_,hs,_⟩ := finite_heap_diamond (badCompiled k) (bad_path k) (bad_input k) h
  rw [bad_source k] at hs; cases hs
theorem no_wrong_payload (k : Fin 3) : (badP k).run initial ≠ .error (.revertWith [9]) := by
  rw [bad_source k]; intro h; cases h
theorem wrong_spec : ¬ Spec.sat initial (.diamond P (.not post)) := by
  intro h
  obtain ⟨o,_,hs,_,_,_,negative⟩ := finite_heap_diamond compiled finite_path input h
  have eq : o = output := Except.ok.inj (hs.symm.trans source)
  subst o
  exact negative output_post
end objects

namespace references
abbrev K := publishedHeap% references C
abbrev Γ : Ctx := publishedHeap% references Γ
abbrev initial := publishedHeap% references state
abbrev bases := publishedHeap% references base
abbrev machine := publishedHeap% references machine
def P : Prog K Γ Γ := publishedHeap% references program
attribute [irreducible] P
def compiled : Compiler.Compilation 1 (Frag.init Γ) P := by
  simpa only [P] using (publishedHeap% references compiled)
attribute [irreducible] compiled
theorem path : compiled.isReferenceArray = true := by decide +kernel
theorem input : compiled.Input 1 8 bases initial machine := by
  simpa only [compiled,P] using Memory.RefArrayExamples.compiled_input
theorem finite_path : compiled.isMemory = true ∨ compiled.isReferenceArray = true ∨ compiled.isObject = true :=
  .inr (.inl path)

theorem positive : (P.run initial).toOption.isSome = true := by unfold P; decide +kernel
def output : Solidity.Out K initial.H Γ := (P.run initial).toOption.get positive
attribute [irreducible] output
theorem source : P.run initial = .ok output := by simpa only [output] using get_source positive

def readChild (i : Idx Γ (.mem (publishedHeap% references childTy))) : Tm K Γ (.val .uint) :=
  .app2 .read (.app0 .memory) (.app2 (.mat .dyn) (.pvI i) (.app0 (.lit ⟨0,by decide⟩)))
def post : Spec K Γ :=
  .and (.eq (readChild (.there .here)) (.app0 (.lit ⟨11,by decide⟩)))
    (.eq (readChild (.there (.there .here))) (.app0 (.lit ⟨13,by decide⟩)))
theorem output_post : Spec.sat output.st post := by
  constructor
  · exact ⟨⟨11,by decide⟩,by decide +kernel,rfl⟩
  · exact ⟨⟨13,by decide⟩,by decide +kernel,rfl⟩
theorem diamond : Spec.sat initial (.diamond P post) := by
  simpa only [Spec.sat,source] using output_post

theorem represented : ∃ o m', P.run initial = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ compiled.Rep 1 8 bases initial machine o.st m' ∧ Spec.sat o.st post :=
  finite_heap_diamond compiled finite_path input diamond

theorem source_observed : (publishedHeap% references observeSource) (P.run initial) =
    some [32,16,24,24,16,11,13] := by
  simpa only [P] using Memory.RefArrayExamples.source_observation
theorem target_observed : (publishedHeap% references observeTarget) (run compiled.code machine) =
    some [32,16,24,24,16,11,13] := by
  simpa only [compiled,P] using Memory.RefArrayExamples.target_observation

theorem ordered : ∃ o m', P.run initial = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ compiled.Rep 1 8 bases initial machine o.st m' ∧ Spec.sat o.st post ∧
    (publishedHeap% references observeSource) (.ok o) = some [32,16,24,24,16,11,13] ∧
    (publishedHeap% references observeTarget) (.ok m' 0) = some [32,16,24,24,16,11,13] := by
  obtain ⟨o,m',hs,ht,stack,rep,hpost⟩ := represented
  refine ⟨o,m',hs,ht,stack,rep,hpost,?_,?_⟩
  · rw [← hs]; exact source_observed
  · rw [← ht]; exact target_observed

theorem wrong_output : ¬ ∃ m', run compiled.code machine = .ok m' 0 ∧
    (publishedHeap% references observeTarget) (.ok m' 0) = some [32,16,24,24,16,11,14] := by
  rintro ⟨m',ht,wrong⟩
  obtain ⟨o,n,hs,hn,stack,rep,post,src,good⟩ := ordered
  have eq : n = m' := by cases hn.symm.trans ht; rfl
  subst n
  rw [wrong] at good
  cases good

theorem wrong_alias : ¬ ∃ m', run compiled.code machine = .ok m' 0 ∧
    (publishedHeap% references observeTarget) (.ok m' 0) = some [32,16,24,16,16,11,13] := by
  rintro ⟨m',ht,wrong⟩
  obtain ⟨o,n,hs,hn,stack,rep,post,src,good⟩ := ordered
  have eq : n = m' := by cases hn.symm.trans ht; rfl
  subst n
  rw [wrong] at good
  cases good

theorem wrong_frame : ¬ compiled.Input 1 0 bases initial machine := by
  intro h
  have hbound := ((compiled.referenceArray_input path 1 0 bases initial machine).mp h).state.locals
  omega

theorem wrong_pointer : ¬ compiled.Input 1 8 bases initial (Memory.writeMachine machine 33 w[24]) := by
  intro h
  have rep := (compiled.referenceArray_input path 1 8 bases initial _).mp h
  exact Memory.RefArrayExamples.wrong_pointer_refuted (rep.arrays.arrays (publishedHeap% references parent))

def badP (k : Fin 3) : Prog K Γ Γ := (publishedHeap% references failingProgram) k
def badCompiled (k : Fin 3) : Compiler.Compilation 1 (Frag.init Γ) (badP k) := by
  simpa only [badP] using ((publishedHeap% references failed) k)
attribute [irreducible] badP badCompiled
theorem bad_path (k : Fin 3) : (badCompiled k).isMemory = true ∨
    (badCompiled k).isReferenceArray = true ∨ (badCompiled k).isObject = true := by
  have h : ∀ k : Fin 3, (badCompiled k).isReferenceArray = true := by decide +kernel
  exact .inr (.inl (h k))

theorem bad_input (k : Fin 3) : (badCompiled k).Input 1 8 bases initial machine := by
  simpa only [badCompiled,badP] using Memory.RefArrayExamples.failed_input k
theorem bad_source (k : Fin 3) : (badP k).run initial = .error .revert := by
  unfold badP
  have old := Memory.RefArrayExamples.source_bounds k
  have observation : ∀ r : TRes (Solidity.Out K initial.H Γ),
      (publishedHeap% references sourceReverted) r =
        (match r with | .error .revert => true | _ => false) := by
    intro r
    cases r with
    | ok o => rfl
    | error e => cases e <;> rfl
  rw [observation] at old
  cases hs : ((publishedHeap% references failingProgram) k).run initial with
  | ok o => rw [hs] at old; cases old
  | error e =>
    rw [hs] at old
    cases e <;> first | rfl | cases old

theorem exact_failure (k : Fin 3) : (badP k).run initial = .error .revert ∧
    run (badCompiled k).code machine = .revert :=
  ⟨bad_source k,(finite_heap_failure (badCompiled k) (bad_path k) (bad_input k) (bad_source k)).2⟩
theorem false_box (k : Fin 3) : Spec.sat initial (.box (badP k) (.not .tt)) := by
  simp only [Spec.sat,bad_source k,ne_eq,reduceCtorEq,not_false_eq_true]
theorem box_failure (k : Fin 3) : run (badCompiled k).code machine = .revert := by
  rcases finite_heap_box (badCompiled k) (bad_path k) (bad_input k) (false_box k) with
    ⟨o,_,hs,_⟩ | ⟨_,ht⟩
  · rw [bad_source k] at hs; cases hs
  · exact ht
theorem no_diamond (k : Fin 3) : ¬ Spec.sat initial (.diamond (badP k) .tt) := by
  intro h
  obtain ⟨o,_,hs,_⟩ := finite_heap_diamond (badCompiled k) (bad_path k) (bad_input k) h
  rw [bad_source k] at hs; cases hs
theorem no_wrong_payload (k : Fin 3) : (badP k).run initial ≠ .error (.revertWith [9]) := by
  rw [bad_source k]; intro h; cases h
theorem wrong_spec : ¬ Spec.sat initial (.diamond P (.not post)) := by
  intro h
  obtain ⟨o,_,hs,_,_,_,negative⟩ := finite_heap_diamond compiled finite_path input h
  have eq : o = output := Except.ok.inj (hs.symm.trans source)
  subst o
  exact negative output_post
end references

namespace allocation
abbrev K := publishedHeap% allocation C
abbrev Γ : Ctx := publishedHeap% allocation Γ
abbrev Δ : Ctx := publishedHeap% allocation Δ
abbrev initial := publishedHeap% allocation σ
abbrev bases := publishedHeap% allocation bases
abbrev machine := publishedHeap% allocation machine
abbrev cursor := publishedHeap% allocation cursor
def P : Prog K Γ Δ := publishedHeap% allocation program
attribute [irreducible] P
def compiled : Compiler.Compilation 1 (Frag.init Γ) P := by
  simpa only [P] using (publishedHeap% allocation compiled)
attribute [irreducible] compiled
theorem path : compiled.isMemory = true := by decide +kernel
theorem finite_path : compiled.isMemory = true ∨ compiled.isReferenceArray = true ∨ compiled.isObject = true := .inl path
theorem source_cost : Memory.allocationCostProg P initial = 4 := by unfold P; decide +kernel
theorem cost : compiled.allocationCost initial = 4 := by
  rw [finite_memory_cost compiled path]; exact source_cost

theorem input : compiled.Input 1 6 bases initial machine := by
  apply (compiled.memory_input path 1 6 bases initial machine).mpr
  exact ⟨Memory.AllocSourceExamples.initial_repr.1,by decide +kernel,
    .inr ⟨by decide,cursor,Memory.AllocSourceExamples.initial_repr.2,by decide +kernel⟩⟩

theorem positive : (P.run initial).toOption.isSome = true := by unfold P; decide +kernel
def output : Solidity.Out K initial.H Δ := (P.run initial).toOption.get positive
attribute [irreducible] output
theorem source : P.run initial = .ok output := by simpa only [output] using get_source positive

def post : Spec K Δ :=
  .and (.eq (.app2 .mlen (.app0 .memory) (.pvI .here)) (.app0 (.lit ⟨0,by decide⟩)))
    (.and (.eq (.app2 .mlen (.app0 .memory) (.pvI (.there .here))) (.app0 (.lit ⟨2,by decide⟩)))
      (.eq (.pvV (.there (.there .here))) (.app0 (.lit ⟨2,by decide⟩))))
theorem output_post : Spec.sat output.st post := by
  refine ⟨⟨⟨0,by decide⟩,by decide +kernel,rfl⟩,?_,?_⟩
  · exact ⟨⟨2,by decide⟩,by decide +kernel,rfl⟩
  · exact ⟨⟨2,by decide⟩,by decide +kernel,rfl⟩
theorem diamond : Spec.sat initial (.diamond P post) := by
  simpa only [Spec.sat,source] using output_post

theorem represented : ∃ o m', P.run initial = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = machine.stack ∧ compiled.Rep 1 6 bases initial machine o.st m' ∧ Spec.sat o.st post :=
  finite_heap_diamond compiled finite_path input diamond

theorem source_observed : (publishedHeap% allocation sourceObserve) (P.run initial) = some [2,1,0,0,2,2] := by
  simpa only [P] using Memory.AllocSourceExamples.source_run
theorem target_observed : (publishedHeap% allocation targetObserve) (run compiled.code machine) =
    some [0,20,2,16,19,99,2,0,0,0] := by
  simpa only [compiled,P] using Memory.AllocSourceExamples.target_run

theorem ordered : ∃ o m', P.run initial = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = machine.stack ∧ compiled.Rep 1 6 bases initial machine o.st m' ∧ Spec.sat o.st post ∧
    (publishedHeap% allocation sourceObserve) (.ok o) = some [2,1,0,0,2,2] ∧
    (publishedHeap% allocation targetObserve) (.ok m' 0) = some [0,20,2,16,19,99,2,0,0,0] := by
  obtain ⟨o,m',hs,ht,stack,rep,hpost⟩ := represented
  refine ⟨o,m',hs,ht,stack,rep,hpost,?_,?_⟩
  · rw [← hs]; exact source_observed
  · rw [← ht]; exact target_observed

theorem cursor20 : ∃ o m' base', P.run initial = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = machine.stack ∧ Memory.StateRepr 1 1 6 compiled.frag o.st base' m' ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.StructAllocatorRepr o.st.heap base' 6 ⟨20,by decide⟩ m' ∧ m'.mem 0 = w[20] := by
  obtain ⟨o,m',hs,ht,stack,rep,hpost⟩ := represented
  obtain ⟨base',repr,extension,grows⟩ := (finite_memory_rep_iff compiled path).mp rep
  rw [cost] at grows
  have ha := grows cursor (by decide) Memory.AllocSourceExamples.initial_repr.2 (by decide +kernel)
  exact ⟨o,m',base',hs,ht,stack,repr,extension,ha,ha.arrays.free.cell⟩

theorem wrong_frame : ¬ compiled.Input 1 0 bases initial machine := by
  intro h
  have hb := ((compiled.memory_input path 1 0 bases initial machine).mp h).2.1
  omega

theorem wrong_allocation_cursor : ¬ ∃ o m' base', P.run initial = .ok o ∧
    run compiled.code machine = .ok m' 0 ∧
    Memory.StructAllocatorRepr o.st.heap base' 6 ⟨19,by decide⟩ m' := by
  rintro ⟨o,m',base',hs,ht,wrong⟩
  obtain ⟨u,n,_,_,hn,_,_,_,_,cell⟩ := cursor20
  have eq : n = m' := by cases hn.symm.trans ht; rfl
  subst n
  have bad : w[20] = w[19] := cell.symm.trans wrong.arrays.free.cell
  exact (by decide +kernel : w[20] ≠ w[19]) bad

def shieldedMachine : Machine := {machine with stack := [w[77]]}
theorem protected_input : compiled.Input 1 6 bases initial shieldedMachine := by
  apply (compiled.memory_input path 1 6 bases initial shieldedMachine).mpr
  exact ⟨Memory.AllocSourceExamples.initial_repr.1.stack _,by decide +kernel,
    .inr ⟨by decide,cursor,Memory.AllocSourceExamples.initial_repr.2.stack _,by decide +kernel⟩⟩
theorem protected_success : ∃ o m', P.run initial = .ok o ∧ run compiled.code shieldedMachine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ compiled.Rep 1 6 bases initial shieldedMachine o.st m' ∧ Spec.sat o.st post :=
  finite_heap_diamond compiled finite_path protected_input diamond
end allocation

namespace badRhs
open Memory.CompileExamples
abbrev P := badRhsRead
abbrev compiled := checkedBadRhs
def machine : Machine := {Memory.CompileExamples.machine with stack := [w[77]]}
theorem path : compiled.isMemory = true := by decide +kernel
theorem finite_path : compiled.isMemory = true ∨ compiled.isReferenceArray = true ∨ compiled.isObject = true := .inl path
theorem input : compiled.Input 1 4 base σ machine := by
  apply (compiled.memory_input path 1 4 base σ machine).mpr
  exact ⟨fixture_repr.stack [w[77]],by decide +kernel,.inl (by decide +kernel)⟩
theorem source : P.run σ = .error .revert :=
  (publishedHeap% memory sourceReverted_sound) (by decide +kernel)
theorem exact_failure : P.run σ = .error .revert ∧ run compiled.code machine = .revert :=
  ⟨source,(finite_heap_failure compiled finite_path input source).2⟩
theorem false_box : Spec.sat σ (.box P (.not .tt)) := by
  simp only [Spec.sat,source,ne_eq,reduceCtorEq,not_false_eq_true]
theorem box_failure : run compiled.code machine = .revert := by
  rcases finite_heap_box compiled finite_path input false_box with ⟨o,_,hs,_⟩ | ⟨_,ht⟩
  · rw [source] at hs; cases hs
  · exact ht
theorem no_diamond : ¬ Spec.sat σ (.diamond P .tt) := by
  intro h
  obtain ⟨o,_,hs,_⟩ := finite_heap_diamond compiled finite_path input h
  rw [source] at hs; cases hs
theorem no_wrong_payload : P.run σ ≠ .error (.revertWith [9]) := by rw [source]; intro h; cases h
end badRhs

namespace badIndex
open Memory.CompileExamples
abbrev P := badIndexRead
abbrev compiled := checkedBadIndex
def machine : Machine := {Memory.CompileExamples.machine with stack := [w[77]]}
theorem path : compiled.isMemory = true := by decide +kernel
theorem finite_path : compiled.isMemory = true ∨ compiled.isReferenceArray = true ∨ compiled.isObject = true := .inl path
theorem input : compiled.Input 1 4 base σ machine := by
  apply (compiled.memory_input path 1 4 base σ machine).mpr
  exact ⟨fixture_repr.stack [w[77]],by decide +kernel,.inl (by decide +kernel)⟩
theorem source : P.run σ = .error .revert :=
  (publishedHeap% memory sourceReverted_sound) (by decide +kernel)
theorem exact_failure : P.run σ = .error .revert ∧ run compiled.code machine = .revert :=
  ⟨source,(finite_heap_failure compiled finite_path input source).2⟩
theorem false_box : Spec.sat σ (.box P (.not .tt)) := by
  simp only [Spec.sat,source,ne_eq,reduceCtorEq,not_false_eq_true]
theorem box_failure : run compiled.code machine = .revert := by
  rcases finite_heap_box compiled finite_path input false_box with ⟨o,_,hs,_⟩ | ⟨_,ht⟩
  · rw [source] at hs; cases hs
  · exact ht
theorem no_diamond : ¬ Spec.sat σ (.diamond P .tt) := by
  intro h
  obtain ⟨o,_,hs,_⟩ := finite_heap_diamond compiled finite_path input h
  rw [source] at hs; cases hs
theorem no_wrong_payload : P.run σ ≠ .error (.revertWith [9]) := by rw [source]; intro h; cases h
end badIndex
end Solidity.Roadmap.V16.FiniteHeapControls

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
    if (`Solidity.Roadmap.V16).isPrefixOf ((privateToUserName? n).getD n) ||
        (`_private.Solidity.Roadmap.V16).isPrefixOf n ||
        (`_private.Solidity.Examples.Roadmap.V16).isPrefixOf n then
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
    if (`Solidity.Roadmap.V16).isPrefixOf ((privateToUserName? n).getD n) ||
        (`_private.Solidity.Roadmap.V16).isPrefixOf n ||
        (`_private.Solidity.Examples.Roadmap.V16).isPrefixOf n then
      if let .defnInfo _ := info then
        let axs ← collectAxioms n
        let ty ← liftTermElabM do return (← Meta.ppExpr info.type).pretty
        definitions := definitions.push (Json.mkObj [
          ("name", toJson n.toString), ("ownerName", toJson ((privateToUserName? n).getD n).toString),
          ("type", toJson ty),
          ("typeConstants", toJson (info.type.getUsedConstants.toList.map Name.toString)),
          ("dependencies", toJson (info.getUsedConstantsAsSet.toList.map Name.toString)),
          ("axioms", toJson (axs.toList.map Name.toString))])
  logInfo m!"V16-INVENTORY {(Json.mkObj [("definitions", .arr definitions), ("modules", toJson (env.header.moduleNames.toList.map Name.toString)), ("inductives", .arr inductives), ("theorems", .arr theorems)]).compress}"
