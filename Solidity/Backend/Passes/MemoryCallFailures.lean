import Solidity.Backend.Passes.MemoryCallObservations

/-! Failed arguments versus a reached failing body. A default memory return
is allocated only AFTER arguments succeed; body failure reaches that default,
but neither its later new return allocation nor the caller suffix. No state or
map after a terminal revert is manufactured. -/
namespace Solidity.Backend.Passes.MemoryCallFailures
open Evm Evm.Memory Evm.Compiler MemoryCallControls MemoryCallApplication
abbrev Returned : Ctx := .mem A :: Before

def argumentBody : Prog C [.mem A,.val .uint] [.mem A,.val .uint] :=
  .cons (.rebindMem .here (.newArr (.local (.there .here)) rfl)) .nil
def argumentProgram : Prog C Before Returned :=
  .cons (.call "argumentFailure"
    (.snoc .nil .uint (.user "n")
      (.readMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 1 rfl)))))
    (.mem A (.user "result") rfl rfl) argumentBody) .nil

def failedBody : Prog C [.mem A,.mem A] [.mem A,.mem A] :=
  .cons (.require (.simple (.bool false)))
  (.cons (.rebindMem .here (.newArr (.lit 4 rfl) rfl)) .nil)
def bodyProgram : Prog C Before Returned :=
  .cons (.call "bodyFailure" (.snocMemory .nil A (.user "a") (.var (.there .here) rfl))
    (.mem A (.user "result") rfl rfl) failedBody) .nil

def argument : Calls.Program 1 allocation.frag argumentProgram :=
  (Calls.compile 1 _ argumentProgram).get (by decide +kernel)
def body : Calls.Program 1 allocation.frag bodyProgram :=
  (Calls.compile 1 _ bodyProgram).get (by decide +kernel)
theorem argument_free : Evm.Prog.pushes argumentProgram = 0 := by decide +kernel
theorem body_free : Evm.Prog.pushes bodyProgram = 0 := by decide +kernel

theorem argument_source : argumentProgram.run first.st = .error .revert := by with_unfolding_all rfl
theorem body_source : bodyProgram.run first.st = .error .revert := by with_unfolding_all rfl

theorem costs : argument.cost first.st = 0 ∧ body.cost first.st = 1 := by decide +kernel

theorem frames : 1 + argument.need ≤ 128 ∧ 1 + body.need ≤ 128 := by decide +kernel

def later : Prog C Returned (.mem A :: Returned) :=
  .cons (.declMem A (.user "unreachable") (some (.newArr (.lit 5 rfl) rfl)) rfl rfl) .nil
def laterCode (F : Frag Returned) : CompiledProg 1 F later :=
  (compileProg 1 F later).get (by rfl)

theorem later_cost (F : Frag Returned) (σ : State C Returned) : (laterCode F).cert.cost σ = 6 := by
  with_unfolding_all rfl

/-- The head's ACTUAL representation and selected map supply the failing
call Input and run. No suffix Input or success is needed after that failure. -/
theorem reached {P : Prog C Before Returned} (bad : Calls.Program 1 allocation.frag P)
    (free : Evm.Prog.pushes P = 0) (payment : Evm.Prog.pays P = false)
    (failed : P.run first.st = .error .revert)
    (capacity : 1 + bad.need ≤ 128) (cost : bad.cost first.st ≤ 1) :
    ∃ (mb : Nat → Fin W) (mid : Machine), mid.stack = [] ∧ ∀ tail,
      run allocation.code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
      MappedOutput (.memory allocation) 1 128 base initial {machine with stack := tail}
        first.st {mid with stack := tail} mb ∧
      (Compilation.memoryCalls bad free).Input 1 128 mb first.st {mid with stack := tail} ∧
      run bad.code {mid with stack := tail} = .revert ∧
      run ((allocation.code ++ bad.code) ++ (laterCode bad.frag).code)
        {machine with stack := tail} = .revert := by
  obtain ⟨mid,mb,ht,hstack,hm⟩ :=
    compilation_success_shared_mapped (.memory allocation) input (by decide +kernel) first_source
  refine ⟨mb,mid,hstack,?_⟩
  intro tail
  obtain ⟨ha,ma⟩ := hm tail
  have hi : (Compilation.memoryCalls bad free).Input 1 128 mb first.st {mid with stack := tail} := by
    have entry : MappedBoundaryLink (.memory allocation) (.memoryCalls bad free) 1 128 base initial
        {machine with stack := tail} := by
      apply memory_budgeted_memoryCalls_link allocation bad free capacity
      intro o hs
      have same : first = o := Except.ok.inj (first_source.symm.trans hs)
      subst o
      have tailBudget : AllocationInput 1 128 8 initial base {machine with stack := tail} :=
        .inr ⟨by decide,wmod 256,initial_repr.2.stack tail,by decide +kernel⟩
      exact tailBudget.of_le (by rw [MemoryCallControls.costs.1]; omega)
    simpa only [allocation_free,Nat.add_zero] using entry first {mid with stack := tail} mb first_source ha ma
  have failedRun := (compilation_revert_iff (.memoryCalls bad free) hi payment).mpr (.inl failed)
  change run allocation.code {machine with stack := tail} = .ok {mid with stack := tail} 0 at ha
  change run bad.code {mid with stack := tail} = .revert at failedRun
  refine ⟨ha,by simpa only [allocation_free,Nat.add_zero] using ma,hi,failedRun,?_⟩
  rw [List.append_assoc,run_append_ok ha]
  exact run_append_revert failedRun

theorem argument_reached :
    ∃ (mb : Nat → Fin W) (mid : Machine), mid.stack = [] ∧ ∀ tail,
      run allocation.code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
      MappedOutput (.memory allocation) 1 128 base initial {machine with stack := tail}
        first.st {mid with stack := tail} mb ∧
      (Compilation.memoryCalls argument argument_free).Input 1 128 mb first.st {mid with stack := tail} ∧
      run argument.code {mid with stack := tail} = .revert ∧
      run ((allocation.code ++ argument.code) ++ (laterCode argument.frag).code)
        {machine with stack := tail} = .revert :=
  reached argument argument_free (by decide +kernel) argument_source frames.1 (by rw [costs.1]; decide)

theorem body_reached :
    ∃ (mb : Nat → Fin W) (mid : Machine), mid.stack = [] ∧ ∀ tail,
      run allocation.code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
      MappedOutput (.memory allocation) 1 128 base initial {machine with stack := tail}
        first.st {mid with stack := tail} mb ∧
      (Compilation.memoryCalls body body_free).Input 1 128 mb first.st {mid with stack := tail} ∧
      run body.code {mid with stack := tail} = .revert ∧
      run ((allocation.code ++ body.code) ++ (laterCode body.frag).code)
        {machine with stack := tail} = .revert :=
  reached body body_free (by decide +kernel) body_source frames.2 (by rw [costs.2]; exact Nat.le_refl _)

def wholeArgument : Calls.Program 1 (Frag.init []) (allocate.join (argumentProgram.join later)) :=
  (Calls.compile 1 _ _).get (by decide +kernel)
def wholeBody : Calls.Program 1 (Frag.init []) (allocate.join (bodyProgram.join later)) :=
  (Calls.compile 1 _ _).get (by decide +kernel)

theorem scheduled_costs : wholeArgument.cost initial = 2 ∧ wholeBody.cost initial = 3 := by decide +kernel

theorem source_unreachable :
    (allocate.join (argumentProgram.join later)).run initial = .error .revert ∧
    (allocate.join (bodyProgram.join later)).run initial = .error .revert := by
  have ha : (argumentProgram.join later).run first.st = .error .revert := by
    rw [DeferredSource.join_run]
    simp only [TRun.seq,argument_source]
  have hb : (bodyProgram.join later).run first.st = .error .revert := by
    rw [DeferredSource.join_run]
    simp only [TRun.seq,body_source]
  constructor
  · rw [DeferredSource.join_run]
    simp only [TRun.seq,first_source,ha,Except.map]
  · rw [DeferredSource.join_run]
    simp only [TRun.seq,first_source,hb,Except.map]

theorem wrong_failure_stage : argument.cost first.st ≠ body.cost first.st := by
  rw [costs.1,costs.2]
  decide

end Solidity.Backend.Passes.MemoryCallFailures
