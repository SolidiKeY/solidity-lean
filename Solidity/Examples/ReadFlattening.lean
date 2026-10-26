import Solidity.Calculus.LeafArithmetic
import Solidity.Tools.LeafArithmetic
import Solidity.Examples.QueryReduction

/-!
# Source-dependent reads flattened and reconstructed automatically

The source supplies the paths, occurrence positions and alias conditions.
Tests retain existing inputs and failed keys, reject impossible aliases and
reconstruct an actual storage counterstate through the exact leaf bridge.
-/

namespace Solidity.Examples.ReadFlattening

open Solidity.Decide Solidity.Semantics Solidity.ReadRealization
open Solidity.Examples.ReadRealization (Bank balance three four)

def root : LTm Bank (.path (.ref (.mapping .uint (.prim .uint)))) := .app0 (.root "balances" rfl)
def readAt (key : LTm Bank (.val .uint)) : LTm Bank (.val .uint) := .obsW (.index .map root key)
def nested : LTm Bank (.val .uint) := readAt (readAt (.lit (PrimTy.ofLit .uint 3 rfl)))
def leaf : LFml Bank := .eq nested (.lit (PrimTy.ofLit .uint 17 rfl))

def flattened : Solidity.Decide.ReadFlattening leaf 0 := (readFlatten? 256 leaf).get (by decide +kernel)
def encoded : FlattenedArithmetic leaf := (flattenedArithmetic? 256 leaf).get (by decide +kernel)

example : flattened.flat.reads.map ReadOccurrence.slot = [0, 1] := by decide +kernel
example : flattened.flat.reads.map ReadOccurrence.prim = [.uint, .uint] := by decide +kernel
example : encoded.encoding.refs = [] := by decide +kernel

def atoms (k v : PrimTy.uint.Denote) : AEnv :=
  (AEnv.dflt.set .uint 0 k).set .uint 1 v

example : (flattened.layout.entries (State.init Bank)
    (atoms (PrimTy.ofLit .uint 3 rfl) (PrimTy.ofLit .uint 19 rfl))).consistentB = false := by decide +kernel
example : (flattened.layout.entries (State.init Bank)
    (atoms (PrimTy.ofLit .uint 4 rfl) (PrimTy.ofLit .uint 19 rfl))).consistentB = true := by decide +kernel

def countermodel : encoded.Countermodel := leaf_countermodel[encoded]

/-- info: (0, 0) -/
#guard_msgs in #eval ((three.read countermodel.state.storage).val,
  ((balance (three.read countermodel.state.storage)).read countermodel.state.storage).val)

example : ¬ leaf.holds countermodel.state countermodel.atoms := countermodel.refutes

example : encoded.checkCodes [3, 19] = true := by decide +kernel
example : encoded.checkCodes [4, 19] = false := by decide +kernel

def positiveLeaf : LFml Bank := .eq (readAt (.lit (PrimTy.ofLit .uint 3 rfl)))
  (readAt (.lit (PrimTy.ofLit .uint 3 rfl)))
def positive : FlattenedArithmetic positiveLeaf :=
  (flattenedArithmetic? 256 positiveLeaf).get (by decide +kernel)

/-- info: true -/
#guard_msgs in #eval positive.verify.isLeft

theorem positive_valid : positiveLeaf.Valid := positive.valid_of_decide (by decide +kernel)

def rejectForgedCodes : Lean.Elab.Term.TermElabM Bool :=
  Lean.tryCatchRuntimeEx
    (do
      let _ ← Solidity.Tools.leafCountermodelOfCodes (Lean.mkConst ``encoded) [3, 19]
      pure false)
    (fun e => do pure ((← e.toMessageData.toString) == "exact verification: kernel rejected certificate"))

/-- info: true -/
#guard_msgs in #eval rejectForgedCodes

def highLeaf : LFml Bank := .and (.eq (.var (p := .bool) 100) (.var (p := .bool) 100))
  (.eq (readAt (.var 100)) (.var 101))
def high : Solidity.Decide.ReadFlattening highLeaf 102 :=
  (readFlatten? 256 highLeaf).get (by decide +kernel)
def highInputs : AEnv := ((AEnv.dflt.set .bool 100 true).set .uint 100
  (PrimTy.ofLit .uint 3 rfl)).set .uint 101 (PrimTy.ofLit .uint 9 rfl)

example : high.flat.reads.map ReadOccurrence.slot = [102] := by decide +kernel
example : (high.layout.fill (State.init Bank) highInputs).get .bool 100 = true := by decide +kernel
example : (high.layout.fill (State.init Bank) highInputs).get .uint 100 = PrimTy.ofLit .uint 3 rfl := by decide +kernel
example : (high.layout.fill (State.init Bank) highInputs).get .uint 101 = PrimTy.ofLit .uint 9 rfl := by decide +kernel

def failedLeaf : LFml Bank := .eq (readAt .err) (readAt .err)
def failed : FlattenedArithmetic failedLeaf := (flattenedArithmetic? 256 failedLeaf).get (by decide +kernel)

example : (failed.flattening.layout.entries (State.init Bank) AEnv.dflt).length = 0 := by decide +kernel
example : failed.checkCodes [0, 0] = false := by decide +kernel

def overflowKey : LTm Bank (.val .uint) := .app2 (.binop .add rfl)
  (readAt (.lit (PrimTy.ofLit .uint 3 rfl)))
  (.lit (PrimTy.ofLit .uint (uintBound - 1) (by decide +kernel)))
def overflowLeaf : LFml Bank := .eq (readAt overflowKey) (.lit (PrimTy.ofLit .uint 0 rfl))
def overflow : Solidity.Decide.ReadFlattening overflowLeaf 0 :=
  (readFlatten? 256 overflowLeaf).get (by decide +kernel)
def actual : State Bank [] := { State.init Bank with storage := three.write (PrimTy.ofLit .uint 4 rfl) (Storage.init Bank) }

example : (overflow.layout.entries actual (overflow.layout.fill actual AEnv.dflt)).length = 1 := by decide +kernel
example : (overflow.readFree.query.query actual (overflow.layout.fill actual AEnv.dflt)).runStorage actual.storage = false := by
  decide +kernel

def alternativeLeaf : LFml Bank := .eq (.orElse (readAt .err) nested) (.lit (PrimTy.ofLit .uint 0 rfl))
def alternative := (readFlatten? 256 alternativeLeaf).get (by decide +kernel)
example : (alternative.readFree.query.query (State.init Bank)
    (alternative.layout.fill (State.init Bank) AEnv.dflt)).runStorage (Storage.init Bank) = true := by decide +kernel

def conditionalLeaf : LFml Bank := .eq
  (.kite (.lit (PrimTy.ofLit .uint 0 rfl)) (.lit (PrimTy.ofLit .uint 0 rfl)) nested (readAt .err))
  (.lit (PrimTy.ofLit .uint 0 rfl))
def conditional := (readFlatten? 256 conditionalLeaf).get (by decide +kernel)
example : (conditional.readFree.query.query (State.init Bank)
    (conditional.layout.fill (State.init Bank) AEnv.dflt)).runStorage (Storage.init Bank) = true := by decide +kernel

def mixedLeaf : LFml Bank := .and
  (.eq (.obsW (.app0 (.root "debt" rfl))) (.lit (PrimTy.ofLit .int (-2) rfl)))
  (.and (.eq (.obsW (.app0 (.root "paused" rfl))) (.lit true)) leaf)
def mixed := (flattenedArithmetic? 256 mixedLeaf).get (by decide +kernel)
example : mixed.flattening.flat.reads.map ReadOccurrence.prim = [.int, .bool, .uint, .uint] := by decide +kernel
example : mixed.encoding.parameters = [⟨.int, 0⟩, ⟨.uint, 2⟩, ⟨.bool, 1⟩, ⟨.uint, 3⟩] := by decide +kernel
example : mixed.checkCodes [2 ^ 255 - 2, 3, 1, 3] = false := by decide +kernel
def mixedCountermodel := mixed.countermodelOfCodes [2 ^ 255 - 2, 3, 1, 3] (by decide +kernel)
example : Solidity.Examples.ReadRealization.debt.read mixedCountermodel.state.storage = PrimTy.ofLit .int (-2) rfl := by decide +kernel
example : Solidity.Examples.ReadRealization.paused.read mixedCountermodel.state.storage = true := by decide +kernel

def deep : Nat → LTm Bank (.val .uint)
  | 0 => .lit (PrimTy.ofLit .uint 3 rfl)
  | n + 1 => readAt (deep n)
def deepLeaf : LFml Bank := .eq (deep 8) (.lit (PrimTy.ofLit .uint 17 rfl))
example : (readFlatten? 40 deepLeaf).isSome = true := by decide +kernel
example : (flattenedArithmetic? 40 deepLeaf).isNone = true := by decide +kernel
example : (flattenTerm? 2 nested).isNone = true := by decide +kernel
example : (readFlatten? 256 (LFml.all 0 .uint (.tt : LFml Bank))).isNone = true := by decide +kernel
example : (flattenTerm? 256 (LTm.obsL (.err : LTm Bank (.path (.ref (.array (.prim .uint))))))).isNone = true := by decide +kernel

/-- info: 'Solidity.Decide.ReadFlattening.valid_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Decide.ReadFlattening.valid_iff
/-- info: 'Solidity.Decide.FlattenedArithmetic.countermodelOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FlattenedArithmetic.countermodelOf

end Solidity.Examples.ReadFlattening
