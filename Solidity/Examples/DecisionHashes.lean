import Solidity.Calculus.Decision
import Solidity.Examples.Tactics.Hashing

/-!
# The closer's decision on leaves with hashes (M7, plan step 7)

`decideGoal` (`Calculus/Decision.lean`) on leaves whose memory locals are
fresh strings read only by hashes of one kind (`decideHash`): proofs by the
swapped leaf, refutations by strings of a family, kernel-checked coverage
(`Fml.hashCovered`), and leaves outside it.
-/

namespace Solidity.Examples.DecisionHashes

open Solidity.Decide

def verdict {C : Contract} (φ : Fml C []) : String :=
  match decideGoal φ with
  | .proved => "proved"
  | .refuted _ => "refuted"
  | .unknown => "unknown"

/-! ### Leaves with hashes (M7, plan step 7)

The string-keyed mapping of `Examples/Tactics/Hashing.lean` §3 (`Names`,
`mapping(string => uint) ids`, keyed by `keccak256` of the string).  A leaf
over two fresh strings (`Fml.allocAll`, any bytes) is read under its own hash
premise: `keccak256(s) != keccak256(t)` says the strings read different
bytes, and `ids[keccak256(s)]`, `ids[keccak256(t)]` are one entry exactly
where they read the same.  `decideGoal` reads each string as the word it
hashes to (`Fml.swPrefix`), so a proof holds whatever the hash; a refutation
picks the strings (`Fml.swInst`), one of a family of one-word strings with
distinct hashes per class, so it meets the premise.  The leaves are written
with the constructors: `dl!` has no notation for a fresh string or a hash in
a formula. -/

section Hashes

open Solidity.Examples.Tactics.Hashing (Names)

/-- A string: a `uint[]` in memory. -/
abbrev Str : RefTy := .array (.prim .uint)
/-- The two strings' context, `t` innermost. -/
abbrev Γst : Ctx := [.mem Str, .mem Str]

def idsAt {Γ : Ctx} (key : Tm Names Γ (.val .uint)) : Tm Names Γ (.path (.prim .uint)) :=
  .app2 (.at .map) (.app0 (.root "ids" rfl)) key
/-- `find(storage, ids[key])` -/
def idsRead {Γ : Ctx} (key : Tm Names Γ (.val .uint)) : Tm Names Γ (.val .uint) :=
  .app2 .find (.app0 .storage) (idsAt key)
def num {Γ : Ctx} (n : Nat) : Tm Names Γ (.val .uint) := .app0 (.lit (uintOfNat n))
/-- `keccak256(memory, s)` and `keccak256(memory, t)`; `sha256(memory, ·)`. -/
def hS : Tm Names Γst (.val .uint) := .app2 (.hash .keccak) (.app0 .memory) (.pvI (.there .here))
def hT : Tm Names Γst (.val .uint) := .app2 (.hash .keccak) (.app0 .memory) (.pvI .here)
def shaS : Tm Names Γst (.val .uint) := .app2 (.hash .sha256) (.app0 .memory) (.pvI (.there .here))
def shaT : Tm Names Γst (.val .uint) := .app2 (.hash .sha256) (.app0 .memory) (.pvI .here)
/-- `∀ fresh strings s t. φ` -/
def strings (φ : Fml Names Γst) : Fml Names [] :=
  .allocAll (.user "s") Str (.allocAll (.user "t") Str φ)
/-- `{ storage := save(storage, ids[keccak256(t)], 1) } φ`: `ids[t] = 1;`. -/
def setT (φ : Fml Names Γst) : Fml Names Γst :=
  .upd .box (.snoc .nil (.storage (.app3 .save (.app0 .storage) (idsAt hT) (.app1 .sval (num 1))))) φ

/-- **`∀ s t. s ≠ t → ids[s] == 0 → [ ids[t] = 1; ] ids[s] == 0`**, past the
program. -/
def namesSet : Fml Names [] :=
  strings (.imp (.not (.eq hS hT)) (.imp (.eq (idsRead hS) (num 0)) (setT (.eq (idsRead hS) (num 0)))))
/-- Without `s ≠ t`: refuted by two strings with the same bytes. -/
def namesSetBad : Fml Names [] :=
  strings (.imp (.eq (idsRead hS) (num 0)) (setT (.eq (idsRead hS) (num 0))))
/-- Equal hashes, equal entries; and equal hashes alone, refuted by two
strings with different bytes. -/
def namesEq : Fml Names [] := strings (.imp (.eq hS hT) (.eq (idsRead hS) (idsRead hT)))
def namesEqBad : Fml Names [] := strings (.eq hS hT)
/-- Two kinds of hash of one string: valid under the premise (equal
`sha256`s, equal bytes, equal `keccak256`s), in the named fragment, but
`unknown` (`docs/automation.md`, M7). -/
def namesTwoKinds : Fml Names [] := strings (.imp (.eq shaS shaT) (.eq hS hT))

/-- info: ["proved", "refuted", "proved", "refuted", "unknown"] -/
#guard_msgs in #eval [namesSet, namesSetBad, namesEq, namesEqBad, namesTwoKinds].map verdict

/-- info: [true, true, true, true, false] -/
#guard_msgs in
#eval [namesSet, namesSetBad, namesEq, namesEqBad, namesTwoKinds].map Fml.hashCovered

/-- info: [true, true, true, true, true] -/
#guard_msgs in
#eval [namesSet, namesSetBad, namesEq, namesEqBad, namesTwoKinds].map (Fml.inTarget {})

/-- The leaf is covered, by the kernel: its swapped reading and its two
instances (one class, two classes) in `Fml.Covered`, its keyed root `ids`. -/
theorem namesSet_covered : namesSet.hashCovered = true := by decide +kernel

/-- `decideGoal_complete_hash`, applied. -/
theorem namesSet_answers : decideGoal namesSet ≠ .unknown := decideGoal_complete_hash namesSet_covered

theorem namesEqBad_covered : namesEqBad.hashCovered = true := by decide +kernel

/-- The strings as hidden binders (`Fml.bind`), which range over an unset
reference too: its hash reads nothing and a key of nothing reads the
default key `0`, so the verdict turns on whether a string hashes to `0`, a
preimage question.  Outside the named fragment, and `unknown`. -/
def namesBound : Fml Names [] :=
  .bind .box (.user "s") (.mem Str) (.bind .box (.user "t") (.mem Str)
    (.imp (.not (.eq hS hT)) (.imp (.eq (idsRead hS) (num 0)) (setT (.eq (idsRead hS) (num 0))))))

/-- info: (false, "unknown") -/
#guard_msgs in #eval (namesBound.inTarget {}, verdict namesBound)

end Hashes

end Solidity.Examples.DecisionHashes
