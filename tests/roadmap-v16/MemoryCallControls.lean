import Solidity.Roadmap.V16.SpecificationControls
import Solidity.Examples.Roadmap.V16.MemoryCallConsumer
import Lean
import Solidity.Evm.MemoryCallExamples

/-!
Test-only references to the published91e94ab5 fixture's private constants. The
elaborator emits only the existing checked constant; it defines no execution or
proof shortcut. Missing/moved constants fail closed. Core never imports this.
Producer source revision/bytes are checked independently by scoped accounting.
-/
open Lean Elab Term in
elab "publishedCall%" n:ident : term => do
  let name := mkPrivateNameCore `Solidity.Evm.MemoryCallExamples
    (`Solidity.Evm.Memory.CallExamples ++ n.getId)
  unless (← getEnv).contains name do
    throwError "missing pinned published memory-call fixture constant {name}"
  return mkConst name

namespace Solidity.Roadmap.V16.MemoryCallPublished
abbrev contract := publishedCall% C
abbrev program := publishedCall% callerOwnership
abbrev compiled := publishedCall% compiledCallerOwnership
abbrev initial := publishedCall% initial
abbrev machine := publishedCall% machine
abbrev bases := publishedCall% bases
abbrev sourceArrays := publishedCall% sourceArrays
abbrev targetWords := publishedCall% targetWords
end Solidity.Roadmap.V16.MemoryCallPublished

namespace Solidity.Roadmap.V16.MemoryCallControls
open Solidity.Evm Solidity.Evm.Memory Solidity.Roadmap.V16.MemoryCallPublished

theorem compiled_path : compiled.isMemoryCalls = true := by decide +kernel

theorem compiled_actual : Compiler.compile 1 (Frag.init []) program = some compiled := by
  with_unfolding_all
    exact (Option.some_get (x := Compiler.compile 1 (Frag.init []) program) (by decide +kernel)).symm

theorem input_inhabited : compiled.Input 1 128 bases initial machine :=
  Solidity.Evm.Memory.CallExamples.callerOwnership_input

theorem source_inhabited : (program.run initial).toOption.isSome = true := by decide +kernel

def sourceOutput := (program.run initial).toOption.get source_inhabited

private theorem success_of_option {α : Type} (res : TRes α) (h : res.toOption.isSome = true) :
    res = .ok (res.toOption.get h) := by
  cases res with
  | ok _ => rfl
  | error _ => cases h

theorem source_success : program.run initial = .ok sourceOutput :=
  success_of_option _ source_inhabited

theorem source_arrays : sourceArrays (program.run initial) [(0, 0), (3, 0), (3, 1), (4, 0), (6, 0)] =
    some [7, 17, 33, 0, 44, 11] := by decide +kernel

theorem reached_cost : compiled.allocationCost initial = 12 := by decide +kernel

abbrev OutputCtx : Ctx := [.mem (.array (.prim .uint)), .mem (.array (.prim .uint)), .mem (.array (.prim .uint)), .mem (.array (.prim .uint)), .mem (.array (.prim .uint)), .mem (.array (.prim .uint)), .mem (.array (.prim .uint)), .mem (.array (.prim .uint)), .mem (.array (.prim .uint)), .mem (.array (.prim .uint)), .val .uint]
def markerIndex : Idx OutputCtx (.val .uint) := (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
def callerIndex : Idx OutputCtx (.mem (.array (.prim .uint))) := (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
def sharedIndex : Idx OutputCtx (.mem (.array (.prim .uint))) := (.there (.there (.there (.there (.there (.there .here))))))
def escapedIndex : Idx OutputCtx (.mem (.array (.prim .uint))) := (.there (.there (.there .here)))

def callerRef : HRef sourceOutput.st.H (.array (.prim .uint)) := ⟨0, by decide +kernel⟩
def escapedRef : HRef sourceOutput.st.H (.array (.prim .uint)) := ⟨3, by decide +kernel⟩

theorem source_marker : TEnv.get markerIndex sourceOutput.st.env = ⟨42, by decide⟩ := by decide +kernel

private theorem option_ref_of_id {H : HTy} {R : RefTy} {value : Option (HRef H R)}
    (r : HRef H R) (ids : value.map HRef.id = some r.id) : value = some r := by
  cases value with
  | none => cases ids
  | some q =>
    have eq : q = r := eq_of_heq (HRef.heq_of_id q r (Option.some.inj ids)).2
    exact congrArg some eq

theorem source_aliases : TEnv.get callerIndex sourceOutput.st.env = some callerRef ∧
    TEnv.get sharedIndex sourceOutput.st.env = some callerRef ∧
    TEnv.get escapedIndex sourceOutput.st.env = some escapedRef :=
  ⟨option_ref_of_id callerRef (by decide +kernel),
    option_ref_of_id callerRef (by decide +kernel),
    option_ref_of_id escapedRef (by decide +kernel)⟩

def markerPost : Spec contract OutputCtx :=
  .eq (.pvV markerIndex) (.app0 (.lit ⟨42, by decide⟩))

theorem source_post : Spec.sat sourceOutput.st markerPost :=
  ⟨⟨42, by decide⟩, congrArg some source_marker, rfl⟩

theorem source_box : Spec.sat initial (.box program markerPost) := by
  simpa only [Spec.sat, source_success] using source_post

/-- Actual compiler output, inhabited input and a nontrivial source specification
instantiate NEW transport; no desired simulation is supplied as a premise. -/
theorem ownership_spec : ∃ m', run compiled.code machine = .ok m' 0 ∧
    m'.stack = machine.stack ∧ compiled.Rep 1 128 bases initial machine sourceOutput.st m' ∧
    Spec.sat sourceOutput.st markerPost :=
  memory_call_spec compiled compiled_path input_inhabited source_success source_box

/-- Aliases returned by a real call share their represented machine pointer;
the escaped callee-local reference is retained in the same actual output relation. -/
theorem ownership_alias : ∃ m' base', run compiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ StateRepr 1 1 128 compiled.frag sourceOutput.st base' m' ∧
    BaseExtends initial.H bases base' ∧
    GrowsAllocator 1 128 (compiled.allocationCost initial) initial bases machine sourceOutput.st base' m' ∧
    m'.mem (cellOf 1 callerIndex) = m'.mem (cellOf 1 sharedIndex) ∧
    m'.mem (cellOf 1 escapedIndex) = .val (base' escapedRef.id) := by
  obtain ⟨m', base', ht, stack, repr, baseExtension, grows⟩ :=
    memory_call_success compiled compiled_path input_inhabited source_success
  obtain ⟨r, hr, hp⟩ := repr.pointers escapedIndex
  have eq : r = escapedRef := Option.some.inj (hr.symm.trans source_aliases.2.2)
  subst r
  exact ⟨m', base', ht, stack, repr, baseExtension, grows,
    memory_call_alias repr callerIndex sharedIndex callerRef source_aliases.1 source_aliases.2.1, hp⟩

theorem ownership_cursor : ∃ m' base', run compiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ StateRepr 1 1 128 compiled.frag sourceOutput.st base' m' ∧
    BaseExtends initial.H bases base' ∧
    StructAllocatorRepr sourceOutput.st.heap base' 128 (wmod 268) m' ∧ m'.mem 0 = w[268] := by
  have hs : (wmod 256).val + compiled.allocationCost initial < W := by
    rw [reached_cost]
    decide +kernel
  simpa only [reached_cost] using memory_call_cursor compiled compiled_path input_inhabited source_success
    (wmod 256) (by decide) Solidity.Evm.Memory.CallExamples.initial_repr.2 hs

/-- Ordered target words are observations of the actual compiler run, not G01
events or byte-EVM behavior. They preserve protected stack and untouched sentinel. -/
theorem ordered_words : targetWords (run compiled.code machine)
    [0, 127, 1, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267] =
    some [77, 268, 99, 42, 1, 17, 0, 0, 2, 33, 0, 1, 44, 0, 1, 11] := by
  with_unfolding_all decide +kernel

/-- Wrong output, alias identity and allocation advance are distinct controls. -/
theorem wrong_output : targetWords (run compiled.code machine) [1] ≠ some [77, 43] := by decide +kernel

theorem wrong_alias : ¬ ∃ m' pc, run compiled.code machine = .ok m' pc ∧
    m'.mem (cellOf 1 callerIndex) ≠ m'.mem (cellOf 1 sharedIndex) := by
  obtain ⟨m', _, ht, _, _, _, _, alias, _⟩ := ownership_alias
  rintro ⟨bad, pc, runBad, wrong⟩
  have eq := Evm.Out.ok.inj (ht.symm.trans runBad)
  cases eq.1
  exact wrong alias

theorem wrong_cursor : ¬ ∃ m' pc, run compiled.code machine = .ok m' pc ∧ m'.mem 0 = w[267] := by
  obtain ⟨m', _, ht, _, _, _, _, cursor⟩ := ownership_cursor
  rintro ⟨bad, pc, runBad, wrong⟩
  have eq := Evm.Out.ok.inj (ht.symm.trans runBad)
  cases eq.1
  have impossible : (w[268] : Evm.Word) ≠ w[267] := by decide +kernel
  exact impossible (cursor.symm.trans wrong)

theorem expanded_frame_refused : ¬ compiled.Input 1 11 bases initial machine :=
  memory_call_small_frame compiled compiled_path (by with_unfolding_all decide +kernel)

theorem reached_allocation_refused :
    ¬ compiled.Input 1 128 bases initial (publishedCall% tooFull) := by
  intro input
  have hi := ((compiled.memoryCalls_input compiled_path 1 128 bases initial (publishedCall% tooFull)).1 input).2.2
  rcases hi with hz | ⟨_, c, ha, hs⟩
  · rw [reached_cost] at hz
    cases hz
  · have eq : c = wmod (W - 4) := Word.val.inj ha.arrays.free.cell.symm
    subst c
    rw [reached_cost] at hs
    have hn : ¬ (wmod (W - 4)).val + 12 < W := by decide +kernel
    exact hn hs

abbrev failureProgram := publishedCall% calleeFailure
abbrev failureCompiled := publishedCall% compiledCalleeFailure

theorem failure_source : failureProgram.run initial = .error .revert :=
  (publishedCall% error_of_halt) _ _ (by decide +kernel)

theorem failure_exact : THalt.revert = .revert ∧ run failureCompiled.code machine = .revert :=
  memory_call_failure failureCompiled (by decide +kernel)
    Solidity.Evm.Memory.CallExamples.calleeFailure_input failure_source

theorem wrong_failure : run failureCompiled.code machine ≠ .fault := by
  rw [failure_exact.2]
  intro h
  cases h

theorem successful_not_revert : run compiled.code machine ≠ .revert := by
  obtain ⟨m', ht, _⟩ := ownership_spec
  rw [ht]
  intro h
  cases h

theorem payload_preserved : Backend.Failure.ResultObserves (fun _ => [])
    ((publishedCall% payloadCall).run initial) (.revert [0xde, 0xad]) :=
  Solidity.Evm.Memory.CallExamples.payloadCall_observed

theorem payload_byte_transport_refused :
    (Compiler.compile 1 (Frag.init []) (publishedCall% payloadCall)).isSome = false := by decide +kernel

/-- A structural cut of the EXISTING intrinsic program, not another syntax or
execution relation. It only selects the caller prefix and remaining actual calls. -/
def cut {C : Contract} {Γ Δ : Ctx} (n : Nat) (P : Prog C Γ Δ) :
    Sigma (fun Ξ : Ctx => Prog C Γ Ξ × Prog C Ξ Δ) :=
  match n with
  | 0 => ⟨Γ, .nil, P⟩
  | n + 1 => match P with
    | .nil => ⟨Γ, .nil, .nil⟩
    | .cons stmt tail =>
      let ⟨Ξ, head, rest⟩ := cut n tail
      ⟨Ξ, .cons stmt head, rest⟩

def split := cut 3 program
abbrev CallerCtx : Ctx := [.mem (.array (.prim .uint)), .val .uint]
def callerPrefix : Prog contract [] CallerCtx := split.2.1
def remainingCalls : Prog contract CallerCtx OutputCtx := split.2.2

def prefixCertificate : Calls.Program 1 (Frag.init []) callerPrefix :=
  (Calls.compile 1 (Frag.init []) callerPrefix).get (by decide +kernel)
def prefixCompiled : Compiler.Compilation 1 (Frag.init []) callerPrefix :=
  .memoryCalls prefixCertificate (by decide +kernel)

attribute [irreducible] prefixCertificate prefixCompiled

theorem prefix_path : prefixCompiled.isMemoryCalls = true := by decide +kernel

theorem prefix_fragment : prefixCompiled.frag = Frag.init CallerCtx := by decide +kernel

theorem prefix_input : prefixCompiled.Input 1 128 bases initial machine := by
  apply (prefixCompiled.memoryCalls_input prefix_path 1 128 bases initial machine).2
  exact ⟨Solidity.Evm.Memory.CallExamples.initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 256, Solidity.Evm.Memory.CallExamples.initial_repr.2, by decide +kernel⟩⟩

theorem prefix_successful : (callerPrefix.run initial).toOption.isSome = true := by decide +kernel
def callerEntry := (callerPrefix.run initial).toOption.get prefix_successful

theorem prefix_source : callerPrefix.run initial = .ok callerEntry :=
  success_of_option _ prefix_successful

theorem populated_caller : callerEntry.st.H.length = 1 ∧ split.1.length = 2 := by decide +kernel

def remainingCompiled : Compiler.Compilation 1 (Frag.init CallerCtx) remainingCalls :=
  (Compiler.compile 1 (Frag.init CallerCtx) remainingCalls).get (by decide +kernel)
attribute [irreducible] remainingCompiled

theorem remaining_path : remainingCompiled.isMemoryCalls = true := by decide +kernel

theorem remaining_source_inhabited : (remainingCalls.run callerEntry.st).toOption.isSome = true := by decide +kernel
def remainingOutput := (remainingCalls.run callerEntry.st).toOption.get remaining_source_inhabited

theorem remaining_source : remainingCalls.run callerEntry.st = .ok remainingOutput :=
  success_of_option _ remaining_source_inhabited

theorem prefix_cost : prefixCompiled.allocationCost initial = 2 := by decide +kernel

theorem remaining_cost : remainingCompiled.allocationCost callerEntry.st = 10 := by decide +kernel

/-- The reached target input is CONSTRUCTED by the actual prefix certificate,
including its allocator growth. No desired suffix simulation/input is assumed. -/
theorem populated_input : ∃ m₁ base₁, run prefixCompiled.code machine = .ok m₁ 0 ∧
    m₁.stack = [w[77]] ∧ remainingCompiled.Input 1 128 base₁ callerEntry.st m₁ ∧
    StructAllocatorRepr callerEntry.st.heap base₁ 128 (wmod 258) m₁ := by
  have hs : (wmod 256).val + prefixCompiled.allocationCost initial < W := by
    rw [prefix_cost]; decide +kernel
  obtain ⟨m₁, base₁, runPrefix, stack, repr, _, allocator, _⟩ :=
    memory_call_cursor prefixCompiled prefix_path prefix_input prefix_source (wmod 256)
      (by decide) Solidity.Evm.Memory.CallExamples.initial_repr.2 hs
  rw [prefix_fragment] at repr
  have entryAllocator : StructAllocatorRepr callerEntry.st.heap base₁ 128 (wmod 258) m₁ := by
    simpa only [prefix_cost] using allocator
  refine ⟨m₁, base₁, runPrefix, stack, ?_, entryAllocator⟩
  apply (remainingCompiled.memoryCalls_input remaining_path 1 128 base₁ callerEntry.st m₁).2
  refine ⟨repr, ?_, .inr ⟨by decide, _, allocator, ?_⟩⟩
  · decide +kernel
  · change (wmod 256).val + prefixCompiled.allocationCost initial +
      remainingCompiled.allocationCost callerEntry.st < W
    rw [prefix_cost, remaining_cost]
    decide +kernel

theorem remaining_actual : Compiler.compile 1 (Frag.init CallerCtx) remainingCalls = some remainingCompiled := by
  with_unfolding_all
    exact (Option.some_get (x := Compiler.compile 1 (Frag.init CallerCtx) remainingCalls)
      (by decide +kernel)).symm

def entryRef : HRef callerEntry.st.H (.array (.prim .uint)) := ⟨0, by decide +kernel⟩
def retainedRef : HRef remainingOutput.st.H (.array (.prim .uint)) := entryRef.wk remainingOutput.ext
def returnedRef : HRef remainingOutput.st.H (.array (.prim .uint)) := ⟨3, by decide +kernel⟩

theorem entry_alias : TEnv.get (.here : Idx CallerCtx (.mem (.array (.prim .uint))))
    callerEntry.st.env = some entryRef := option_ref_of_id entryRef (by decide +kernel)

theorem remaining_aliases : TEnv.get callerIndex remainingOutput.st.env = some retainedRef ∧
    TEnv.get sharedIndex remainingOutput.st.env = some retainedRef ∧
    TEnv.get escapedIndex remainingOutput.st.env = some returnedRef :=
  ⟨option_ref_of_id retainedRef (by decide +kernel),
    option_ref_of_id retainedRef (by decide +kernel),
    option_ref_of_id returnedRef (by decide +kernel)⟩

/-- A real caller object is mutated through shared aliases, a distinct local
escapes by return, and rebinding the parameter does not rebind the caller. -/
theorem populated_mutation :
    (publishedCall% arrayAt) callerEntry.st.heap 0 0 = some 5 ∧
    (publishedCall% arrayAt) remainingOutput.st.heap 0 0 = some 17 ∧
    (publishedCall% arrayAt) remainingOutput.st.heap 3 0 = some 33 ∧
    (publishedCall% arrayAt) remainingOutput.st.heap 4 0 = some 44 := by decide +kernel

theorem remaining_marker : TEnv.get markerIndex remainingOutput.st.env = ⟨42, by decide⟩ := by decide +kernel

theorem remaining_post : Spec.sat remainingOutput.st markerPost :=
  ⟨⟨42, by decide⟩, congrArg some remaining_marker, rfl⟩

theorem remaining_box : Spec.sat callerEntry.st (.box remainingCalls markerPost) := by
  simpa only [Spec.sat, remaining_source] using remaining_post

/-- Public compilation and NEW specification transport at a CONSTRUCTED
populated input. Every source/target run and protected tail is retained. -/
theorem populated_spec : ∃ m₁ base₁ m₂,
    run prefixCompiled.code machine = .ok m₁ 0 ∧
    remainingCompiled.Input 1 128 base₁ callerEntry.st m₁ ∧
    run remainingCompiled.code m₁ = .ok m₂ 0 ∧ m₂.stack = [w[77]] ∧
    remainingCompiled.Rep 1 128 base₁ callerEntry.st m₁ remainingOutput.st m₂ ∧
    Spec.sat remainingOutput.st markerPost := by
  obtain ⟨m₁, base₁, runPrefix, initialStack, input, _⟩ := populated_input
  obtain ⟨m₂, runCall, stack, repr, post⟩ :=
    memory_call_spec remainingCompiled remaining_path input remaining_source remaining_box
  exact ⟨m₁, base₁, m₂, runPrefix, input, runCall, stack.trans initialStack, repr, post⟩

/-- Non-vacuous old-reference preservation, returned-reference representation,
shared alias identity and exact allocator growth at the populated call entry. -/
theorem populated_alias_escape : ∃ m₁ base₁ m₂ base₂,
    run prefixCompiled.code machine = .ok m₁ 0 ∧
    run remainingCompiled.code m₁ = .ok m₂ 0 ∧ m₂.stack = [w[77]] ∧
    StateRepr 1 1 128 remainingCompiled.frag remainingOutput.st base₂ m₂ ∧
    BaseExtends callerEntry.st.H base₁ base₂ ∧
    GrowsAllocator 1 128 (remainingCompiled.allocationCost callerEntry.st)
      callerEntry.st base₁ m₁ remainingOutput.st base₂ m₂ ∧
    m₂.mem (cellOf 1 callerIndex) = m₂.mem (cellOf 1 sharedIndex) ∧
    m₂.mem (cellOf 1 callerIndex) = .val (base₁ entryRef.id) ∧
    m₂.mem (cellOf 1 escapedIndex) = .val (base₂ returnedRef.id) ∧ m₂.mem 0 = w[268] := by
  obtain ⟨m₁, base₁, runPrefix, initialStack, input, allocator⟩ := populated_input
  obtain ⟨m₂, base₂, runCall, stack, repr, baseExtension, grows⟩ :=
    memory_call_success remainingCompiled remaining_path input remaining_source
  have alias := memory_call_alias repr callerIndex sharedIndex retainedRef
    remaining_aliases.1 remaining_aliases.2.1
  obtain ⟨r, hr, ptr⟩ := repr.pointers callerIndex
  have eq : r = retainedRef := Option.some.inj (hr.symm.trans remaining_aliases.1)
  subst r
  have retained : m₂.mem (cellOf 1 callerIndex) = .val (base₁ entryRef.id) :=
    ptr.trans (congrArg Evm.Word.val (baseExtension entryRef))
  obtain ⟨r, hr, escaped⟩ := repr.pointers escapedIndex
  have eq : r = returnedRef := Option.some.inj (hr.symm.trans remaining_aliases.2.2)
  subst r
  have hs : (wmod 258).val + remainingCompiled.allocationCost callerEntry.st < W := by
    rw [remaining_cost]; decide +kernel
  have cursor : m₂.mem 0 = w[268] := by
    simpa only [remaining_cost] using (grows (wmod 258) (by decide) allocator hs).arrays.free.cell
  exact ⟨m₁, base₁, m₂, base₂, runPrefix, runCall, stack.trans initialStack, repr,
    baseExtension, grows, alias, retained, escaped, cursor⟩

/-- Source failure bytes remain a separate observation from the word-machine halt. -/
theorem failure_observation : Backend.Failure.ResultObserves (fun _ => [])
    (failureProgram.run initial) (.revert []) := by
  rw [failure_source]
  exact .failure .empty

theorem wrong_revert_data : ¬ Backend.Failure.ResultObserves (fun _ => [])
    (failureProgram.run initial) (.revert [9]) :=
  Backend.Failure.wrong_observation failure_observation (by decide +kernel)

theorem remaining_diamond : Spec.sat callerEntry.st (.diamond remainingCalls markerPost) := by
  simpa only [Spec.sat, remaining_source] using remaining_post

theorem whole_diamond : Spec.sat initial (.diamond program markerPost) := by
  simpa only [Spec.sat, source_success] using source_post

/-- The NEW diamond consumer, at the actual CONSTRUCTED populated input, supplies
source success and machine/post witnesses without asking for source success. -/
theorem populated_diamond : ∃ m₁ base₁ m₂ base₂,
    run prefixCompiled.code machine = .ok m₁ 0 ∧
    remainingCompiled.Input 1 128 base₁ callerEntry.st m₁ ∧
    remainingCalls.run callerEntry.st = .ok remainingOutput ∧
    run remainingCompiled.code m₁ = .ok m₂ 0 ∧ m₂.stack = [w[77]] ∧
    StateRepr 1 1 128 remainingCompiled.frag remainingOutput.st base₂ m₂ ∧
    BaseExtends callerEntry.st.H base₁ base₂ ∧
    GrowsAllocator 1 128 (remainingCompiled.allocationCost callerEntry.st)
      callerEntry.st base₁ m₁ remainingOutput.st base₂ m₂ ∧
    Spec.sat remainingOutput.st markerPost ∧
    m₂.mem (cellOf 1 callerIndex) = m₂.mem (cellOf 1 sharedIndex) ∧
    m₂.mem (cellOf 1 callerIndex) = .val (base₁ entryRef.id) ∧
    m₂.mem (cellOf 1 escapedIndex) = .val (base₂ returnedRef.id) ∧
    StructAllocatorRepr remainingOutput.st.heap base₂ 128 (wmod 268) m₂ ∧ m₂.mem 0 = w[268] := by
  obtain ⟨m₁, base₁, runPrefix, initialStack, input, allocator⟩ := populated_input
  obtain ⟨o, m₂, base₂, space, source, target, stack, repr, baseExtension, grows, post, next, cursor⟩ :=
    memory_call_diamond_cursor remainingCompiled remaining_path input remaining_diamond
      (wmod 258) (by decide) allocator
  have eq : o = remainingOutput := Except.ok.inj (source.symm.trans remaining_source)
  subst o
  have alias := memory_call_alias repr callerIndex sharedIndex retainedRef
    remaining_aliases.1 remaining_aliases.2.1
  obtain ⟨r, hr, pointer⟩ := repr.pointers callerIndex
  have eq : r = retainedRef := Option.some.inj (hr.symm.trans remaining_aliases.1)
  subst r
  have retained := pointer.trans (congrArg Evm.Word.val (baseExtension entryRef))
  obtain ⟨r, hr, escaped⟩ := repr.pointers escapedIndex
  have eq : r = returnedRef := Option.some.inj (hr.symm.trans remaining_aliases.2.2)
  subst r
  have allocated : StructAllocatorRepr remainingOutput.st.heap base₂ 128 (wmod 268) m₂ := by
    simpa only [remaining_cost] using next
  have exactCursor : m₂.mem 0 = w[268] := by
    simpa only [remaining_cost] using cursor
  exact ⟨m₁, base₁, m₂, base₂, runPrefix, input, source, target,
    stack.trans initialStack, repr, baseExtension, grows, post, alias, retained,
    escaped, allocated, exactCursor⟩

/-- Keep the COMPLETE existing ordered source-array and target-word snapshots,
now tied to the actual target witness produced by NEW diamond transport. -/
theorem diamond_complete_observations : ∃ o m' base',
    program.run initial = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ StateRepr 1 1 128 compiled.frag o.st base' m' ∧
    BaseExtends initial.H bases base' ∧
    GrowsAllocator 1 128 (compiled.allocationCost initial) initial bases machine o.st base' m' ∧
    Spec.sat o.st markerPost ∧
    sourceArrays (.ok o) [(0, 0), (3, 0), (3, 1), (4, 0), (6, 0)] = some [7, 17, 33, 0, 44, 11] ∧
    targetWords (.ok m' 0) [0, 127, 1, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267] =
      some [77, 268, 99, 42, 1, 17, 0, 0, 2, 33, 0, 1, 44, 0, 1, 11] := by
  obtain ⟨o, m', base', source, target, stack, repr, baseExtension, grows, post⟩ :=
    memory_call_diamond compiled compiled_path input_inhabited whole_diamond
  have sources := source_arrays
  rw [source] at sources
  have targets := ordered_words
  rw [target] at targets
  exact ⟨o, m', base', source, target, stack, repr, baseExtension, grows, post, sources, targets⟩

/-- Exact existing callee empty revert has real Input, but even the true-post
source diamond is rejected by NEW success transport. -/
theorem failure_diamond_rejected : ¬ Spec.sat initial (.diamond failureProgram .tt) := by
  intro diamond
  obtain ⟨o, _, _, source, _⟩ := memory_call_diamond failureCompiled (by decide +kernel)
    Solidity.Evm.Memory.CallExamples.calleeFailure_input diamond
  rw [failure_source] at source
  cases source

theorem diamond_false_post_rejected : ¬ Spec.sat initial (.diamond program (.not markerPost)) := by
  intro diamond
  obtain ⟨o, _, _, source, _, _, _, _, _, post⟩ :=
    memory_call_diamond compiled compiled_path input_inhabited diamond
  have eq : o = sourceOutput := Except.ok.inj (source.symm.trans source_success)
  subst o
  exact post source_post

/-- A true source diamond does not provide a missing frame or allocation input. -/
theorem diamond_does_not_supply_frame :
    Spec.sat initial (.diamond program markerPost) ∧ ¬ compiled.Input 1 11 bases initial machine :=
  ⟨whole_diamond, expanded_frame_refused⟩

theorem diamond_does_not_supply_capacity : Spec.sat initial (.diamond program markerPost) ∧
    ¬ compiled.Input 1 128 bases initial (publishedCall% tooFull) :=
  ⟨whole_diamond, reached_allocation_refused⟩

/-- Reuse the already proved genuine exhausted diamond. No source-success law
for arbitrary diamonds follows, and the existing semantics remain unchanged. -/
theorem general_diamond_not_success :
    Spec.sat SpecificationControls.entryState
      (.diamond (Prog.recBase : Prog TransactionControls.contract [] []) .tt) ∧
    ¬ ∃ o, (Prog.recBase : Prog TransactionControls.contract [] []).run
      SpecificationControls.entryState = .ok o :=
  ⟨SpecificationControls.exhausted_diamond,
    fun ⟨o, source⟩ => SpecificationControls.exhausted_has_no_success o source⟩

/-- The certificate-derived exclusion cannot be applied to that exhausted case
without its real Input. This is not a new exclusion in source admission. -/
theorem exhausted_case_not_admitted {b L frame : Nat} {F : Frag []}
    (candidate : Compiler.Compilation (C := TransactionControls.contract) b F .recBase)
    (path : candidate.isMemoryCalls = true) (base : Nat → Fin W) (m : Machine) :
    ¬ candidate.Input L frame base SpecificationControls.entryState m :=
  fun input => memory_call_not_exhausted candidate path input rfl

/-- NEW box transport has no source-success premise. The actual closed source
baseline selects its success branch for this concrete populated application. -/
theorem populated_box : ∃ m₁ base₁ m₂ base₂,
    run prefixCompiled.code machine = .ok m₁ 0 ∧
    remainingCompiled.Input 1 128 base₁ callerEntry.st m₁ ∧
    run remainingCompiled.code m₁ = .ok m₂ 0 ∧ m₂.stack = [w[77]] ∧
    StateRepr 1 1 128 remainingCompiled.frag remainingOutput.st base₂ m₂ ∧
    BaseExtends callerEntry.st.H base₁ base₂ ∧
    GrowsAllocator 1 128 (remainingCompiled.allocationCost callerEntry.st)
      callerEntry.st base₁ m₁ remainingOutput.st base₂ m₂ ∧
    Spec.sat remainingOutput.st markerPost := by
  obtain ⟨m₁, base₁, runPrefix, initialStack, input, _⟩ := populated_input
  rcases memory_call_box remainingCompiled remaining_path input remaining_box with
    ⟨o, m₂, base₂, source, target, stack, repr, baseExtension, grows, post⟩ | ⟨source, _⟩
  · have eq : o = remainingOutput := Except.ok.inj (source.symm.trans remaining_source)
    subst o
    exact ⟨m₁, base₁, m₂, base₂, runPrefix, input, target, stack.trans initialStack,
      repr, baseExtension, grows, post⟩
  · rw [remaining_source] at source
    cases source

/-- The approved box accepts genuine empty revert even with a false post. -/
theorem failure_box_false_post : Spec.sat initial (.box failureProgram (.not .tt)) := by
  simp only [Spec.sat, failure_source, ne_eq, reduceCtorEq, not_false_eq_true]

/-- NEW box transport derives exact source/target failure here, not a fictitious
successful state satisfying the false postcondition. -/
theorem box_false_post_exact_revert : failureProgram.run initial = .error .revert ∧
    run failureCompiled.code machine = .revert := by
  rcases memory_call_box failureCompiled (by decide +kernel)
    Solidity.Evm.Memory.CallExamples.calleeFailure_input failure_box_false_post with
    ⟨_, _, _, _, _, _, _, _, _, post⟩ | failure
  · exact False.elim (post trivial)
  · exact failure

theorem box_not_total_success : Spec.sat initial (.box failureProgram (.not .tt)) ∧
    ¬ ∃ o, failureProgram.run initial = .ok o := by
  refine ⟨failure_box_false_post, ?_⟩
  rintro ⟨o, source⟩
  rw [box_false_post_exact_revert.1] at source
  cases source

theorem box_false_marker_rejected : ¬ Spec.sat initial (.box program (.not markerPost)) := by
  intro box
  rcases memory_call_box compiled compiled_path input_inhabited box with
    ⟨o, _, _, source, _, _, _, _, _, post⟩ | ⟨source, _⟩
  · have eq : o = sourceOutput := Except.ok.inj (source.symm.trans source_success)
    subst o
    exact post source_post
  · rw [source_success] at source
    cases source

/-- Scoped modal duality is instantiated at the same genuinely reached caller. -/
theorem populated_box_diamond_duality : ∃ m₁ base₁,
    run prefixCompiled.code machine = .ok m₁ 0 ∧
    remainingCompiled.Input 1 128 base₁ callerEntry.st m₁ ∧
    (Spec.sat callerEntry.st (.box remainingCalls markerPost) ↔
      ¬ Spec.sat callerEntry.st (.diamond remainingCalls (.not markerPost))) := by
  obtain ⟨m₁, base₁, runPrefix, _, input, _⟩ := populated_input
  exact ⟨m₁, base₁, runPrefix, input, memory_call_box_diamond_dual remainingCompiled remaining_path input⟩

/-- Exhaustion invalidates GENERAL box/diamond duality. The finite certificate
consumer must not become a global rewrite or a change to the approved reading. -/
theorem general_modal_duality_rejected :
    ¬ (Spec.sat SpecificationControls.entryState
      (.box (Prog.recBase : Prog TransactionControls.contract [] []) .tt) ↔
      ¬ Spec.sat SpecificationControls.entryState
        (.diamond (Prog.recBase : Prog TransactionControls.contract [] []) (.not .tt))) := by
  intro dual
  have box : Spec.sat SpecificationControls.entryState
      (.box (Prog.recBase : Prog TransactionControls.contract [] []) .tt) := by
    change (THalt.exhausted ≠ .panic)
    intro impossible
    cases impossible
  exact dual.1 box rfl

end Solidity.Roadmap.V16.MemoryCallControls

#print axioms Solidity.Roadmap.V16.MemoryCallControls.compiled_path
#print axioms Solidity.Roadmap.V16.MemoryCallControls.compiled_actual
#print axioms Solidity.Roadmap.V16.MemoryCallControls.input_inhabited
#print axioms Solidity.Roadmap.V16.MemoryCallControls.source_inhabited
#print axioms Solidity.Roadmap.V16.MemoryCallControls.source_success
#print axioms Solidity.Roadmap.V16.MemoryCallControls.source_arrays
#print axioms Solidity.Roadmap.V16.MemoryCallControls.reached_cost
#print axioms Solidity.Roadmap.V16.MemoryCallControls.source_marker
#print axioms Solidity.Roadmap.V16.MemoryCallControls.source_aliases
#print axioms Solidity.Roadmap.V16.MemoryCallControls.source_post
#print axioms Solidity.Roadmap.V16.MemoryCallControls.source_box
#print axioms Solidity.Roadmap.V16.MemoryCallControls.ownership_spec
#print axioms Solidity.Roadmap.V16.MemoryCallControls.ownership_alias
#print axioms Solidity.Roadmap.V16.MemoryCallControls.ownership_cursor
#print axioms Solidity.Roadmap.V16.MemoryCallControls.ordered_words
#print axioms Solidity.Roadmap.V16.MemoryCallControls.wrong_output
#print axioms Solidity.Roadmap.V16.MemoryCallControls.wrong_alias
#print axioms Solidity.Roadmap.V16.MemoryCallControls.wrong_cursor
#print axioms Solidity.Roadmap.V16.MemoryCallControls.expanded_frame_refused
#print axioms Solidity.Roadmap.V16.MemoryCallControls.reached_allocation_refused
#print axioms Solidity.Roadmap.V16.MemoryCallControls.failure_source
#print axioms Solidity.Roadmap.V16.MemoryCallControls.failure_exact
#print axioms Solidity.Roadmap.V16.MemoryCallControls.wrong_failure
#print axioms Solidity.Roadmap.V16.MemoryCallControls.successful_not_revert
#print axioms Solidity.Roadmap.V16.MemoryCallControls.payload_preserved
#print axioms Solidity.Roadmap.V16.MemoryCallControls.payload_byte_transport_refused
#print axioms Solidity.Roadmap.V16.MemoryCallControls.prefix_path
#print axioms Solidity.Roadmap.V16.MemoryCallControls.prefix_fragment
#print axioms Solidity.Roadmap.V16.MemoryCallControls.prefix_input
#print axioms Solidity.Roadmap.V16.MemoryCallControls.prefix_successful
#print axioms Solidity.Roadmap.V16.MemoryCallControls.prefix_source
#print axioms Solidity.Roadmap.V16.MemoryCallControls.populated_caller
#print axioms Solidity.Roadmap.V16.MemoryCallControls.remaining_path
#print axioms Solidity.Roadmap.V16.MemoryCallControls.remaining_source_inhabited
#print axioms Solidity.Roadmap.V16.MemoryCallControls.remaining_source
#print axioms Solidity.Roadmap.V16.MemoryCallControls.prefix_cost
#print axioms Solidity.Roadmap.V16.MemoryCallControls.remaining_cost
#print axioms Solidity.Roadmap.V16.MemoryCallControls.populated_input
#print axioms Solidity.Roadmap.V16.MemoryCallControls.remaining_actual
#print axioms Solidity.Roadmap.V16.MemoryCallControls.entry_alias
#print axioms Solidity.Roadmap.V16.MemoryCallControls.remaining_aliases
#print axioms Solidity.Roadmap.V16.MemoryCallControls.populated_mutation
#print axioms Solidity.Roadmap.V16.MemoryCallControls.remaining_marker
#print axioms Solidity.Roadmap.V16.MemoryCallControls.remaining_post
#print axioms Solidity.Roadmap.V16.MemoryCallControls.remaining_box
#print axioms Solidity.Roadmap.V16.MemoryCallControls.populated_spec
#print axioms Solidity.Roadmap.V16.MemoryCallControls.populated_alias_escape
#print axioms Solidity.Roadmap.V16.MemoryCallControls.failure_observation
#print axioms Solidity.Roadmap.V16.MemoryCallControls.wrong_revert_data

#print axioms Solidity.Roadmap.V16.MemoryCallControls.remaining_diamond
#print axioms Solidity.Roadmap.V16.MemoryCallControls.whole_diamond
#print axioms Solidity.Roadmap.V16.MemoryCallControls.populated_diamond
#print axioms Solidity.Roadmap.V16.MemoryCallControls.diamond_complete_observations
#print axioms Solidity.Roadmap.V16.MemoryCallControls.failure_diamond_rejected
#print axioms Solidity.Roadmap.V16.MemoryCallControls.diamond_false_post_rejected
#print axioms Solidity.Roadmap.V16.MemoryCallControls.diamond_does_not_supply_frame
#print axioms Solidity.Roadmap.V16.MemoryCallControls.diamond_does_not_supply_capacity
#print axioms Solidity.Roadmap.V16.MemoryCallControls.general_diamond_not_success
#print axioms Solidity.Roadmap.V16.MemoryCallControls.exhausted_case_not_admitted

#print axioms Solidity.Roadmap.V16.MemoryCallControls.populated_box
#print axioms Solidity.Roadmap.V16.MemoryCallControls.failure_box_false_post
#print axioms Solidity.Roadmap.V16.MemoryCallControls.box_false_post_exact_revert
#print axioms Solidity.Roadmap.V16.MemoryCallControls.box_not_total_success
#print axioms Solidity.Roadmap.V16.MemoryCallControls.box_false_marker_rejected
#print axioms Solidity.Roadmap.V16.MemoryCallControls.populated_box_diamond_duality
#print axioms Solidity.Roadmap.V16.MemoryCallControls.general_modal_duality_rejected

/-! Actual checked test closure and definition dependencies; read-only metadata. -/
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
