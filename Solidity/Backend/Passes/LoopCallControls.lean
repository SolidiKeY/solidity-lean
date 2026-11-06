import Solidity.Backend.Passes.LoopCallsBoundary
import Solidity.Backend.Passes.LoopAllocatingSuffix
import Solidity.Backend.Passes.MemoryCallFailures

/-! A memory-return call consumes the loop's ACTUAL rebound alias. Its first
body effect needs element1, distinguishing that alias from the old length1
object. No independent Source dispatch/admission theorem is claimed. -/
namespace Solidity.Backend.Passes.LoopCallControls
open Evm Evm.Memory Evm.Compiler
open MemoryCallControls (C A initial base machine)
open LoopScopeControls
open LoopScopeTrace (preparedTarget loopTarget)
abbrev Returned : Ctx := .mem A :: LoopScopeControls.Γ

def argumentEffect : Prog C [.mem A,.mem A] [.mem A,.mem A] :=
  .cons (.assignMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 1 rfl)))
    (.val (.binop .add rfl rfl
      (.readMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 1 rfl))))
      (.simple (.lit 7 rfl))))) .nil

def callee : Prog C [.mem A,.mem A] [.mem A,.mem A,.mem A] :=
  argumentEffect.join MemoryCallControls.body

def call : Prog C LoopScopeControls.Γ Returned :=
  .cons (.call "afterLoop" MemoryCallControls.arguments
    (.mem A (.user "result") rfl rfl) callee) .nil

def producer : Calls.Program 1 enclosed.frag call := (Calls.compile 1 _ call).get (by decide +kernel)
theorem free : Evm.Prog.pushes call = 0 := by decide +kernel
def checkedCall : Compilation 1 enclosed.frag call := .memoryCalls producer free
noncomputable def result : Solidity.Out C loopOut.st.H Returned :=
  (call.run loopOut.st).toOption.get (by decide +kernel)

theorem source : call.run loopOut.st = .ok result := by
  have h : some result = (call.run loopOut.st).toOption := Option.some_get _
  cases hs : call.run loopOut.st with
  | ok o => rw [hs] at h; exact congrArg Except.ok (Option.some.inj h).symm
  | error e => rw [hs] at h; cases h

theorem cost : producer.cost loopOut.st = 6 := by decide +kernel
theorem expanded_frame : frameNeedProg call < producer.need ∧ 1 + producer.need ≤ 128 := by
  decide +kernel

theorem public_recognizer : (Compiler.compile 1 enclosed.frag call).map (·.isMemoryCalls) = some true := by
  decide +kernel

/-- Three independently compiled stages succeed even though the current
single-fragment recognizer has no accepted constructor for the whole mixture. -/
theorem whole_recognizer_refused :
    Compiler.compile 1 (Frag.init []) (prepare.join (wrapped.join call)) = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)

theorem joined_source :
    ((prepare.join wrapped).join call).run initial =
      .ok ⟨result.st,(prepared.ext.trans loopOut.ext).trans result.ext⟩ ∧
    (prepare.join (wrapped.join call)).run initial =
      .ok ⟨result.st,prepared.ext.trans (loopOut.ext.trans result.ext)⟩ :=
  triple_source_success initial prepared_source wrapped_source source

attribute [local irreducible] producer result preparation enclosed prepared loopOut preparedTarget loopTarget

/-- The call receives the exact selected loop map and allocator261. Frame
uses expanded producer.need; capacity uses expanded producer.cost, not legacy0. -/
theorem receiving {mb nb : Nat → Fin W}
    (ha : MappedOutput (.memory preparation) 1 128 base initial machine prepared.st preparedTarget mb)
    (hb : MappedOutput LoopScopeControls.checked 1 128 mb prepared.st preparedTarget loopOut.st loopTarget nb) :
    checkedCall.Input 1 128 nb loopOut.st loopTarget := by
  refine ⟨?_,expanded_frame.2,?_⟩
  · rcases hb with ⟨amount,ext,hcost,state,extension,growth⟩
    exact state
  · exact .inr ⟨by decide,wmod 261,(LoopAllocatingSuffix.actual_resources ha hb).2.1,
      by rw [cost]; decide +kernel⟩

theorem private_frame_refused (selected : Nat → Fin W) (m : Machine) :
    ¬ checkedCall.Input 1 (1 + frameNeedProg call) selected loopOut.st m := by
  intro hi
  have h := hi.2.1
  have gap := expanded_frame.1
  omega

end Solidity.Backend.Passes.LoopCallControls
