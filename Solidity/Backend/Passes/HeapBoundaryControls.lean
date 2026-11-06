import Solidity.Backend.Passes.HeapBoundary
import Solidity.Backend.Passes.TripleSequence
import Solidity.Backend.Passes.Controls

/-! A real construction/reference-array/memory composition. Parent construction
owns two distinct default children even after one parent link is overwritten. -/
namespace Solidity.Backend.Passes.HeapBoundaryControls
open Evm Evm.Memory Evm.Compiler
open Backend.Passes.Controls.Fixture
abbrev Child : RefTy := .array (.prim .uint)
abbrev Parent : RefTy := .array (.ref Child)
abbrev Locals : Ctx := [.mem Parent, .mem Child]

def allocate : Prog C [] Locals :=
  .cons (.declMem Child (.user "child") (some (.newArr (.lit 1 rfl) rfl)) rfl rfl)
    (.cons (.declMem Parent (.user "parent") (some (.newArr (.lit 2 rfl) rfl)) rfl rfl) .nil)
def mutate : Prog C Locals Locals :=
  .cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl)))
    (.ref (.var (.there .here) rfl)))
  (.cons (.assignMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 0 rfl)))
    (.val (.simple (.lit 42 rfl)))) .nil)
def read : Prog C Locals (.val .uint :: Locals) :=
  .cons (.declLocal .uint (.user "answer")
    (some (.readMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 0 rfl)))))) .nil

def allocation : Construction.CompiledProg 1 (Frag.init []) allocate :=
  (Construction.compileProg 1 _ allocate).get (by decide +kernel)
def mutation : ReferenceArrays.CompiledProg 1 allocation.frag mutate :=
  (ReferenceArrays.compileProg 1 _ mutate).get (by decide +kernel)
def observation : Memory.CompiledProg 1 mutation.frag read :=
  (Memory.compileProg 1 _ read).get (by decide +kernel)

def initial : State C [] := State.init C
def base : Nat → Fin W := fun _ => wmod 0
def machine : Machine :=
  {Machine.init with mem := fun n => if n = 0 then w[16] else if n = 15 then w[99] else w[0]}

private theorem noRefs {R : RefTy} (r : HRef initial.H R) : False := by
  simpa only [initial, State.init, List.getElem?_nil, reduceCtorEq] using r.get?

theorem empty_heap : Objects.HeapRepr initial.heap base 8 machine := by
  exact ⟨⟨fun r => (noRefs r).elim, fun r => (noRefs r).elim, fun r _ _ => (noRefs r).elim⟩,
    (fun _ r => (noRefs r).elim), (fun r => (noRefs r).elim), (fun r _ => (noRefs r).elim)⟩

theorem physical : Objects.StateRepr 1 1 8 (Frag.init []) initial base machine := by
  have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨⟨hc.store, ?_, ?_, hc.net, hc.netSelf, hc.bound, ?_, hc.env, hc.funds, hc.oracle⟩,
    empty_heap, ?_, by decide⟩
  all_goals intro p i; nomatch i

theorem allocator : Objects.AllocatorRepr initial.heap base 8 ⟨16,by decide⟩ machine := by
  refine ⟨empty_heap, ⟨by decide, by decide, rfl, ?_⟩, fun r => (noRefs r).elim⟩
  intro addr ha
  change 16 ≤ addr at ha
  simp only [machine, if_neg (show addr ≠ 0 by omega), if_neg (show addr ≠ 15 by omega)]

theorem cost : Construction.allocationCostProg allocate initial = 7 := by decide +kernel

theorem input : (Compilation.construction allocation).Input 1 8 base initial machine := by
  refine ⟨physical, by decide +kernel, .inr ⟨by decide, ⟨16,by decide⟩, allocator, ?_⟩⟩
  rw [cost]
  decide +kernel

private theorem first_some : (allocate.run initial).toOption.isSome = true := by decide +kernel
noncomputable def first : Solidity.Out C initial.H Locals := (allocate.run initial).toOption.get first_some

theorem allocation_source : allocate.run initial = .ok first := by
  have h : some first = (allocate.run initial).toOption := Option.some_get first_some
  cases hs : allocate.run initial with
  | ok o =>
    rw [hs] at h
    exact congrArg Except.ok (Option.some.inj h).symm
  | error e => rw [hs] at h; cases h

private theorem second_some : (mutate.run first.st).toOption.isSome = true := by decide +kernel
noncomputable def second : Solidity.Out C first.st.H Locals := (mutate.run first.st).toOption.get second_some

theorem mutation_source : mutate.run first.st = .ok second := by
  have h : some second = (mutate.run first.st).toOption := Option.some_get second_some
  cases hs : mutate.run first.st with
  | ok o =>
    rw [hs] at h
    exact congrArg Except.ok (Option.some.inj h).symm
  | error e => rw [hs] at h; cases h

private theorem third_some : (read.run second.st).toOption.isSome = true := by decide +kernel
noncomputable def third : Solidity.Out C second.st.H (.val .uint :: Locals) :=
  (read.run second.st).toOption.get third_some

theorem observation_source : read.run second.st = .ok third := by
  have h : some third = (read.run second.st).toOption := Option.some_get third_some
  cases hs : read.run second.st with
  | ok o =>
    rw [hs] at h
    exact congrArg Except.ok (Option.some.inj h).symm
  | error e => rw [hs] at h; cases h

theorem reached_link (tail : List Word) :
    ReachedMappedLink (.construction allocation) (.referenceArrays mutation) (.memory observation)
      1 8 base initial {machine with stack := tail} := by
  intro o mid selected _ _ _
  exact referenceArrays_memory_link mutation observation (by decide +kernel) (by decide +kernel)

theorem success (tail : List Word) :
    ∃ (mb nb ob : Nat → Fin W) (mid next final : Machine),
      run allocation.code {machine with stack := tail} = .ok mid 0 ∧
      run mutation.code mid = .ok next 0 ∧
      run observation.code next = .ok final 0 ∧
      run ((allocation.code ++ mutation.code) ++ observation.code) {machine with stack := tail} = .ok final 0 ∧
      run (allocation.code ++ (mutation.code ++ observation.code)) {machine with stack := tail} = .ok final 0 ∧
      final.stack = tail ∧
      MappedOutput (.construction allocation) 1 8 base initial {machine with stack := tail} first.st mid mb ∧
      MappedOutput (.referenceArrays mutation) 1 8 mb first.st mid second.st next nb ∧
      MappedOutput (.memory observation) 1 8 nb second.st next third.st final ob :=
  compilation_triple_success (.construction allocation) (.referenceArrays mutation) (.memory observation)
    (compilation_input_stack (.construction allocation) input tail)
    (construction_referenceArrays_link allocation mutation) (reached_link tail)
    rfl rfl rfl allocation_source mutation_source observation_source

theorem source_answer : (TEnv.get (.here : Idx (.val .uint :: Locals) (.val .uint)) third.st.env).val = 42 := by
  decide +kernel

end Solidity.Backend.Passes.HeapBoundaryControls
