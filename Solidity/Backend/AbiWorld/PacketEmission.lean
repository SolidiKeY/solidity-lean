import Solidity.Backend.AbiWorld.EntryTransport

/-! Value-specialized aggregate packet emission. The existing codec produces
all bytes and the existing checked byte-slice executes RETURN. This is not a
runtime encoder reading symbolic words, a source body or a target call. -/
namespace Solidity.Backend.AbiWorld.PacketEmission
open AbiEntry Backend Failure

/-- Compile an already available intrinsic typed tuple, without a selector. -/
def emitResult {ss : List Shape} (a : Nat) (vs : Vals ss) : Program :=
  emit a (.returned (encodeArgs vs))

/-- Complete ordered bytes, exact write interval, unchanged old stack and
unreachable suffix. Fits and the actual two-cell stack bound are explicit. -/
theorem execute_result {ss : List Shape} (a : Nat) (vs : Vals ss)
    (suffix : Program) (m : Slice.Machine) (fits : Fits a (encodeArgs vs))
    (stack : m.stack.length + 2 ≤ 1024) :
    Slice.checkedRun (emitResult a vs ++ suffix) m =
      some ({ m with memory := Slice.putBytes m.memory a (encodeArgs vs) },
        some (.success (encodeArgs vs))) := by
  exact checkedRun_emit_suffix a (.returned (encodeArgs vs)) suffix m fits stack

/-- Older memory bytes strictly outside the emitted interval survive. -/
theorem memory_frame {ss : List Shape} (a x : Nat) (vs : Vals ss) (m : Slice.Machine)
    (outside : x < a ∨ a + (encodeArgs vs).length ≤ x) :
    Slice.putBytes m.memory a (encodeArgs vs) x = m.memory x :=
  emitted_memory_frame a x (.returned (encodeArgs vs)) m outside

/-- The tuple is from the actual accepted entry and bodyValues computation.
The observation callback below is diagnostic, not an admitted source body. -/
theorem accepted_packet {I : AbiEntry.Input} {fuel : Nat} {ps : List Param}
    (vs : Vals (ps.map Param.shape)) (accepted : verdict I fuel ps = .run vs)
    (a : Nat) (suffix : Program) (m : Slice.Machine)
    (fits : Fits a (encodeArgs vs)) (stack : m.stack.length + 2 ≤ 1024) :
    (∃ es, entry I fuel ps = .ok es ∧ bodyValues I fuel ps es 0 = .ok vs ∧
      EntryTransport.bodyObservation I fuel ps encodeArgs = some (encodeArgs vs)) ∧
    Slice.checkedRun (emitResult a vs ++ suffix) m =
      some ({ m with memory := Slice.putBytes m.memory a (encodeArgs vs) },
        some (.success (encodeArgs vs))) :=
  ⟨EntryTransport.body_witness vs encodeArgs accepted,
    execute_result a vs suffix m fits stack⟩

/-- Compile an already available typed custom-error packet. Selector bytes come
from the published codec. Offsets inside encodeArgs remain argument-relative. -/
def customBytes {ss : List Shape} (selector : UInt32) (vs : Vals ss) : List UInt8 :=
  Semantics.selectorBytes selector ++ encodeArgs vs

def emitCustom {ss : List Shape} (a : Nat) (selector : UInt32) (vs : Vals ss) : Program :=
  emit a (.custom (customBytes selector vs))

theorem execute_custom {ss : List Shape} (a : Nat) (selector : UInt32) (vs : Vals ss)
    (suffix : Program) (m : Slice.Machine) (fits : Fits a (customBytes selector vs))
    (stack : m.stack.length + 2 ≤ 1024) :
    Slice.checkedRun (emitCustom a selector vs ++ suffix) m =
      some ({ m with memory := Slice.putBytes m.memory a (customBytes selector vs) },
        some (.revert (customBytes selector vs))) :=
  checkedRun_emit_suffix a (.custom (customBytes selector vs)) suffix m fits stack


/-- For every typed aggregate and runtime-width selector, the prefix is exactly
four bytes and removing it recovers every argument byte in order. -/
theorem selector_split {ss : List Shape} (selector : UInt32) (vs : Vals ss) :
    (customBytes selector vs).take 4 = Semantics.selectorBytes selector ∧
    (customBytes selector vs).drop 4 = encodeArgs vs := by
  constructor <;> rfl

/-- info: 'Solidity.Backend.AbiWorld.PacketEmission.selector_split' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms selector_split

/-- info: 'Solidity.Backend.AbiWorld.PacketEmission.execute_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms execute_result
/-- info: 'Solidity.Backend.AbiWorld.PacketEmission.accepted_packet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_packet
/-- info: 'Solidity.Backend.AbiWorld.PacketEmission.execute_custom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms execute_custom

end Solidity.Backend.AbiWorld.PacketEmission
