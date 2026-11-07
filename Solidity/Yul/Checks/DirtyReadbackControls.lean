import Solidity.Yul.DirtyReadback
import Solidity.Yul.Checks.LocalBlock

/-! Controls of `Solidity.Yul.DirtyReadback` (user decision H109). Each
word-level positive is a probe of `tests/evm-reference/dirty-locals.json`
(pinned solc 0.8.38, optimizer off), in both pipelines, cited by probe name;
the frame-level
ones reuse `Checks.LocalBlock`'s mixed frame (a `bool`, two external function
values, a `uint8` and a `bytes1`) and its `dirtyFalse`/`dirtyTwo` frames.
`LocalBlock`'s `RawCoherent.coherent` refusals of those frames stay as they
are: a dirty frame is not coherent with its clean backup, and the readback is
the separate, explicit cleaning boundary. -/
namespace Solidity.Yul.Checks.DirtyReadbackControls
open Solidity.Yul.Checks.LocalBlock
open Solidity.Yul.DirtyReadback (cleanWord frame)

abbrev D := env.layout
def u8 : Solidity.Source.STy := .int Solidity.Source.IntTy.u8
def u16 : Solidity.Source.STy := .int ⟨false, 16, by decide⟩
def i8 : Solidity.Source.STy := .int ⟨true, 8, by decide⟩
def u32 : Solidity.Source.STy := .int ⟨false, 32, by decide⟩
def i16 : Solidity.Source.STy := .int ⟨true, 16, by decide⟩

def key? (ty : Solidity.Source.STy) (p : DirtyReadback.Pipeline) (w : Nat) : Option (Option Int) :=
  (cleanWord (D := D) p ty (word w)).map Solidity.Source.Val.key

/-! ## Words, per type family and pipeline (`dirty-locals.json`) -/

/-- `uintN`: the low bits (`u8_eq`, `u8_checked_add`, `u16_widen`, `u32_widen`). -/
theorem uint_masked :
    key? u8 .legacy 0x1ff = some (some 255) ∧ key? u8 .viaIR 0x1ff = some (some 255) ∧
    key? u8 .legacy 0x1fe = some (some 254) ∧ key? u8 .viaIR 0x1fe = some (some 254) ∧
    key? u16 .legacy 0xabcd1234 = some (some 0x1234) ∧ key? u16 .viaIR 0xabcd1234 = some (some 0x1234) ∧
    key? u32 .legacy 0x1234567890 = some (some 0x34567890) ∧
    key? u32 .viaIR 0x1234567890 = some (some 0x34567890) := by
  decide

/-- `intN`: the low bits sign-extended (`i8_widen_neg`, `i8_widen_pos`,
`i8_eq_neg1`, `i16_widen`). -/
theorem int_sign_extended :
    key? i8 .legacy 0x80 = some (some (-128)) ∧ key? i8 .viaIR 0x80 = some (some (-128)) ∧
    key? i8 .legacy 0x17f = some (some 127) ∧ key? i8 .viaIR 0x17f = some (some 127) ∧
    key? i8 .legacy 0x1ff = some (some (-1)) ∧ key? i8 .viaIR 0x1ff = some (some (-1)) ∧
    key? i16 .legacy 0x18000 = some (some (-32768)) ∧ key? i16 .viaIR 0x18000 = some (some (-32768)) := by
  decide

/-- `bool`: true exactly when the word is not zero (`b_eq_true`, `b_eq_b`,
`b_ne_false`, `b_store`). -/
theorem bool_nonzero :
    key? .bool .legacy 2 = some (some 1) ∧ key? .bool .viaIR 2 = some (some 1) ∧
    key? .bool .legacy 0 = some (some 0) ∧ key? .bool .viaIR 0 = some (some 0) := by
  decide

/-- Types this readback does not clean are refused. -/
theorem other_refused :
    key? (.address false) .legacy 0x1ff = none ∧ key? (.fixedBytes 1 (by decide)) .viaIR 5 = none ∧
    key? (.enum ⟨none, "E"⟩) .legacy 3 = none := by
  decide

/-! ## Frames -/

/-- The `bool`, `uint8` and `bytes1` keys of a read-back frame. -/
def keys (r : Option (Solidity.Source.Locals env.layout ctx.tys × Solidity.Source.St env)) :
    Option (Option Int × Option Int × Option Int) :=
  r.map fun p => match p.1 with
    | .cons a (.cons _ (.cons c (.cons _ (.cons e .nil)))) => (a.key, c.key, e.key)

/-- **A dirty `uint8` reads back cleaned**: `dirtyTwo` holds 258 in `small`;
the frame reads back `2`, the other locals unchanged, in both pipelines. -/
theorem dirtyTwo_read :
    keys (frame .legacy dirtyTwo) = some (some 1, some 2, some 171) ∧
    keys (frame .viaIR dirtyTwo) = some (some 1, some 2, some 171) := by
  decide

/-- A `bool` rewritten to its clean `false` word (`dirtyFalse` writes `0`
into `flag`, which held true) reads back false: a changed, not a dirty,
word. -/
theorem dirtyFalse_read :
    keys (frame .legacy dirtyFalse) = some (some 0, some 1, some 171) ∧
    keys (frame .viaIR dirtyFalse) = some (some 0, some 1, some 171) := by
  decide

/-- **A dirty `bool` reads back cleaned**: `flag` holding `2` reads back
true, in both pipelines. -/
theorem boolTwo_read :
    keys (frame .legacy (RawFrame.write rawInitial flag (word 2))) = some (some 1, some 1, some 171) ∧
    keys (frame .viaIR (RawFrame.write rawInitial flag (word 2))) = some (some 1, some 1, some 171) := by
  decide

/-- An untouched frame reads back as its clean locals. -/
theorem clean_read : keys (frame .legacy rawInitial) = some (some 1, some 1, some 171) := by
  decide

/-- A dirty `bytes1` is not cleaned here: the frame is refused. -/
theorem dirtyByte_refused : keys (frame .viaIR (RawFrame.write rawInitial byte (word 5))) = none := by
  decide

/-- The coherence refusals of `LocalBlock` are unchanged. -/
theorem coherence_kept :
    RawCoherent.coherent dirtyFalse = false ∧ RawCoherent.coherent dirtyTwo = false := by
  decide

/-- info: 'Solidity.Yul.DirtyReadback.readback_of_clean?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.readback_of_clean?
/-- info: 'Solidity.Yul.DirtyReadback.readback_ofClean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.DirtyReadback.readback_ofClean
/-- info: 'Solidity.Yul.Checks.DirtyReadbackControls.dirtyTwo_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.DirtyReadbackControls.dirtyTwo_read
/-- info: 'Solidity.Yul.Checks.DirtyReadbackControls.int_sign_extended' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.Checks.DirtyReadbackControls.int_sign_extended

end Solidity.Yul.Checks.DirtyReadbackControls
