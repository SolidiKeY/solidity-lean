import Solidity.Backend.AbiEntry.EntryTransport

/-! Enum entry consumers; these proofs use only EntryTransport. Nominal-cardinality consumers of the published enum entry decoder.
No uint8-to-enum assumption, decoder replacement or source admission is added. -/
namespace Solidity.Backend.AbiEntry.EnumEntry
open Solidity.AbiEntry

def param (n : Nat) : Param := {shape := .word (.enumBelow n), loc := .value}

/-- An invalid leading enum rejects before any subsequent parameter is entered,
including a dynamic calldata reference or eager memory allocation. -/
theorem invalid_entry (I : Input) (fuel n : Nat) (ps : List Param)
    (bad : n ≤ load I.data 4) :
    entry I (fuel + 2) (param n :: ps) = .error .revert := by
  have hv : Kind.valid (.enumBelow n) (load I.data 4) = false := by
    simp only [Kind.valid, decide_eq_false_iff_not]
    omega
  unfold entry
  split
  · rfl
  · simp only [enter, param, melem, Shape.dynamic, mdec, hv, Bool.false_eq_true,
      dite_false, ite_false, bind, Except.bind, Nat.add_zero]

/-- Exact selected existing empty-byte REVERT emitter from out-of-range enum entry.
The caller's full old stack/memory survive; no tail decoder is assumed. -/
theorem invalid_revert (I : Input) (fuel n : Nat) (ps : List Param)
    (bad : n ≤ load I.data 4) (a : Nat) (suffix : Backend.Program)
    (m : Backend.Failure.Slice.Machine) (fits : Backend.Failure.Fits a [])
    (stack : m.stack.length + 2 ≤ 1024) :
    EntryTransport.runRejection I (fuel + 2) (param n :: ps) a suffix m =
      some (m, some (.revert [])) :=
  EntryTransport.entry_revert_exec I (fuel + 2) _ a suffix m
    (invalid_entry I fuel n ps bad) fits stack

/-- A genuinely truncated head rejects, even if calldataload would zero-pad it. -/
theorem truncated_revert (I : Input) (fuel n : Nat) (ps : List Param)
    (short : I.size < 4 + headsOf (param n :: ps))
    (a : Nat) (suffix : Backend.Program) (m : Backend.Failure.Slice.Machine)
    (fits : Backend.Failure.Fits a []) (stack : m.stack.length + 2 ≤ 1024) :
    EntryTransport.runRejection I fuel (param n :: ps) a suffix m =
      some (m, some (.revert [])) := by
  apply EntryTransport.entry_revert_exec I fuel _ a suffix m _ fits stack
  simp only [entry, if_pos short]


/-- info: 'Solidity.Backend.AbiEntry.EnumEntry.invalid_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms invalid_entry
/-- info: 'Solidity.Backend.AbiEntry.EnumEntry.invalid_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms invalid_revert
/-- info: 'Solidity.Backend.AbiEntry.EnumEntry.truncated_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms truncated_revert

end Solidity.Backend.AbiEntry.EnumEntry
