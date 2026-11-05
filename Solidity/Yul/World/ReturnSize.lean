import Solidity.Yul.World.AdapterRules

/-! # Exact word-sized last-frame returndata length
The abstract byte list is unbounded, unlike an actually executable EVM return
buffer. Check representability instead of silently reducing length modulo2^256.
A real producer must prove the bound; None here is an adapter refusal, not an
EVM RETURNDATASIZE failure semantics or compiler noninterference theorem.
-/
namespace Solidity.Yul.World
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes)
variable {D : Layout} {L T : Address → SPath → STy}

def checkedReturnSize (bytes : Bytes) : Option Word :=
  if h : bytes.length < 2^256 then some ⟨bytes.length,h⟩ else none

def returndataSize (entry : Effects D L T) : Option Word := checkedReturnSize entry.returndata

theorem checkedReturnSize_exact (bytes : Bytes) (h : bytes.length < 2^256) :
    checkedReturnSize bytes = some ⟨bytes.length,h⟩ := by
  simp only [checkedReturnSize,h,dite_true]

theorem checkedReturnSize_refused (bytes : Bytes) (h : ¬ bytes.length < 2^256) :
    checkedReturnSize bytes = none := by
  simp only [checkedReturnSize,h,dite_false]

theorem returndataSize_value (entry : Effects D L T) (count : Word)
    (h : returndataSize entry = some count) : count.val = entry.returndata.length := by
  unfold returndataSize checkedReturnSize at h
  split at h
  · cases h
    rfl
  · cases h

theorem returndataSize_fresh (entry : Effects D L T) :
    returndataSize (freshChild entry) = some ⟨0,by decide⟩ := rfl

/-- Actual last-frame completion determines size on success and revert alike;
no logical return-value decoding or concatenation is performed. -/
theorem returndataSize_finished (entry : ObservedEffects D L T) (frame : CallFrame)
    (answer : FrameAnswer D L T) (h : (returnData answer.outcome).length < 2^256) :
    returndataSize (finishObserved entry frame answer).effects =
      some ⟨(returnData answer.outcome).length,h⟩ := by
  change checkedReturnSize (complete entry.effects frame.this frame.caller frame.value frame.input
    frame.static answer.operations (committedLogs answer.trace) answer.outcome).returndata = _
  rw [complete_data]
  exact checkedReturnSize_exact _ h

/-- Size and source-copy failure agree exactly, including out-of-range size0.
Destination write behavior remains the concrete byte port's obligation. -/
theorem returndataSize_copy_refusal {Memory : Type} (port : BytePort Memory) (entry : Effects D L T)
    (memory : Memory) (count destination source size : Word)
    (hs : returndataSize entry = some count) (hb : count.val < source.val + size.val) :
    copyReturndata port entry memory destination source size = none := by
  have hv := returndataSize_value entry count hs
  exact copyReturndata_bounds _ _ _ _ _ _ (by omega)

namespace ReturnSizeRules
open Solidity.Yul.World.AdapterRules (Configuration Box)
variable {Memory : Type}

/-- Exact read-only normal-return relation, with the resulting Word indexed. -/
def Step (count : Word) (before after : Configuration Memory D L T) : Prop :=
  returndataSize before.observed.effects = some count ∧ after = before

theorem size_step_eq (before : Configuration Memory D L T) (count : Word)
    (h : returndataSize before.observed.effects = some count) :
    Box (Step count) (fun after => after = before ∧ count.val = after.observed.effects.returndata.length) before := by
  intro after hs
  cases hs.2
  exact ⟨rfl,returndataSize_value _ _ h⟩

end ReturnSizeRules
end Solidity.Yul.World
