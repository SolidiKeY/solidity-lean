import Solidity.Calculus.Decision
import Solidity.Examples.Tactics.Hashing

/-!
# The closer's decision on leaves with hashes (M7, plan step 7)

`decideGoal` (`Calculus/Decision.lean`) on leaves whose memory locals are
fresh strings read only by hashes of one kind or of two (`decideHash`):
proofs by the swapped leaf, refutations by strings of a family,
kernel-checked coverage (`Fml.hashCovered`), and leaves outside it.
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
`sha256`s, equal bytes, equal `keccak256`s).  Each string stands for one
word per kind, the `sha256` words binders of their own linked to the
`keccak256` ones (`Fml.tk`, `Calculus/HashKinds.lean`): proved.  Its false
variant, refuted by one string twice. -/
def namesTwoKinds : Fml Names [] := strings (.imp (.eq shaS shaT) (.eq hS hT))
def namesTwoKindsBad : Fml Names [] := strings (.imp (.eq shaS shaT) (.not (.eq hS hT)))

/-- info: ["proved", "refuted", "proved", "refuted", "proved", "refuted"] -/
#guard_msgs in
#eval [namesSet, namesSetBad, namesEq, namesEqBad, namesTwoKinds, namesTwoKindsBad].map verdict

/-- info: [true, true, true, true, true, true] -/
#guard_msgs in
#eval [namesSet, namesSetBad, namesEq, namesEqBad, namesTwoKinds, namesTwoKindsBad].map Fml.hashCovered

/-- info: [true, true, true, true, true, true] -/
#guard_msgs in
#eval [namesSet, namesSetBad, namesEq, namesEqBad, namesTwoKinds, namesTwoKindsBad].map (Fml.inTarget {})

/-- Two kinds of hash, by the kernel: the reading with the `sha256` words
and its instances covered. -/
theorem namesTwoKinds_covered : namesTwoKinds.hashCovered = true := by decide +kernel

/-- `decideGoal_complete_hash`, applied to two kinds. -/
theorem namesTwoKinds_answers : decideGoal namesTwoKinds ≠ .unknown :=
  decideGoal_complete_hash namesTwoKinds_covered

/-- The leaf is covered, by the kernel: its swapped reading and its two
instances (one class, two classes) in `Fml.Covered`, its keyed root `ids`. -/
theorem namesSet_covered : namesSet.hashCovered = true := by decide +kernel

/-- `decideGoal_complete_hash`, applied. -/
theorem namesSet_answers : decideGoal namesSet ≠ .unknown := decideGoal_complete_hash namesSet_covered

theorem namesEqBad_covered : namesEqBad.hashCovered = true := by decide +kernel

/-! #### A hash past an update

The usual shape past symbolic execution: the hypotheses at the top, the
conclusion past an update.  The premise reads a hash in an update's
continuation where the update lands (`Fml.HashIn`), so the second kind's
words may be read there; the first kind's hash of each string is read at
the top (`Fml.tkBody`). -/

/-- `{ storage := save(storage, ids[0], 1) } φ`: `ids[0] = 1;`. -/
def set0 {Γ : Ctx} (φ : Fml Names Γ) : Fml Names Γ :=
  .upd .box (.snoc .nil (.storage (.app3 .save (.app0 .storage) (idsAt (num 0)) (.app1 .sval (num 1))))) φ

/-- **`sha256(s) == sha256(t) → [ ids[0] = 1; ] keccak256(s) == keccak256(t)`**:
proved; without the hypothesis, refuted. -/
def namesLanded : Fml Names [] := strings (.imp (.eq shaS shaT) (set0 (.eq hS hT)))
def namesLandedBad : Fml Names [] := strings (set0 (.eq hS hT))

/-- A value local set in the leaf (`{ x := 1 }`): `∀ x s t. sha256(s) ==
sha256(t) → { x := 1 } (keccak256(s) == keccak256(t) ∧ x == 1)`, proved;
its false variant (`x == 2`) refuted. -/
abbrev Γx : Ctx := [.mem Str, .mem Str, .val .uint]
def xL : Tm Names Γx (.val .uint) := .pvV (.there (.there .here))
def sha2 (i : Idx Γx (.mem Str)) : Tm Names Γx (.val .uint) := .app2 (.hash .sha256) (.app0 .memory) (.pvI i)
def kec2 (i : Idx Γx (.mem Str)) : Tm Names Γx (.val .uint) := .app2 (.hash .keccak) (.app0 .memory) (.pvI i)
def setX (n : Nat) (φ : Fml Names Γx) : Fml Names Γx :=
  .upd .box (.snoc .nil (.local (.there (.there .here)) (.val (num n)))) φ
def withX (φ : Fml Names Γx) : Fml Names [] :=
  .all (.user "x") .uint (.allocAll (.user "s") Str (.allocAll (.user "t") Str φ))
def namesSetLocal : Fml Names [] :=
  withX (.imp (.eq (sha2 (.there .here)) (sha2 .here))
    (setX 1 (.and (.eq (kec2 (.there .here)) (kec2 .here)) (.eq xL (num 1)))))
def namesSetLocalBad : Fml Names [] :=
  withX (.imp (.eq (sha2 (.there .here)) (sha2 .here))
    (setX 1 (.and (.eq (kec2 (.there .here)) (kec2 .here)) (.eq xL (num 2)))))

/-- info: ["proved", "refuted", "proved", "refuted"] -/
#guard_msgs in #eval [namesLanded, namesLandedBad, namesSetLocal, namesSetLocalBad].map verdict

/-- info: [true, true, true, true] -/
#guard_msgs in
#eval [namesLanded, namesLandedBad, namesSetLocal, namesSetLocalBad].map
  (fun φ => φ.hashCovered && φ.inTarget {})

/-- A hash past an update, by the kernel. -/
theorem namesLanded_covered : namesLanded.hashCovered = true := by decide +kernel

/-- `decideGoal_complete_hash`, applied past an update. -/
theorem namesLanded_answers : decideGoal namesLanded ≠ .unknown :=
  decideGoal_complete_hash namesLanded_covered

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

/-! ### Two kinds as keys

Two mappings keyed by hashes of the strings, one by `keccak256`
(`mapping(string => uint)`), one by `sha256` (a `mapping(uint => uint)`
read at the hash).  The second kind's words key `shas` and are linked to
the first kind's (`Fml.tk`); the relabeling of each kind moves its root's
entries (`Fml.tk_complete`). -/

section TwoKeys

/-- `mapping(string => uint) ids; mapping(uint => uint) shas;` -/
def Names2 : Contract := contract!{ mapping(string => uint) ids; mapping(uint => uint) shas; }

def at2 {Γ : Ctx} (r : Name) (h : Names2.rootType r = some (.ref (.mapping .uint (.prim .uint))))
    (key : Tm Names2 Γ (.val .uint)) : Tm Names2 Γ (.path (.prim .uint)) :=
  .app2 (.at .map) (.app0 (.root _ h)) key
def rd2 {Γ : Ctx} (r : Name) (h : Names2.rootType r = some (.ref (.mapping .uint (.prim .uint))))
    (key : Tm Names2 Γ (.val .uint)) : Tm Names2 Γ (.val .uint) :=
  .app2 .find (.app0 .storage) (at2 r h key)
def n2 {Γ : Ctx} (n : Nat) : Tm Names2 Γ (.val .uint) := .app0 (.lit (uintOfNat n))
def kS : Tm Names2 Γst (.val .uint) := .app2 (.hash .keccak) (.app0 .memory) (.pvI (.there .here))
def kT : Tm Names2 Γst (.val .uint) := .app2 (.hash .keccak) (.app0 .memory) (.pvI .here)
def sS : Tm Names2 Γst (.val .uint) := .app2 (.hash .sha256) (.app0 .memory) (.pvI (.there .here))
def sT : Tm Names2 Γst (.val .uint) := .app2 (.hash .sha256) (.app0 .memory) (.pvI .here)
def strings2 (φ : Fml Names2 Γst) : Fml Names2 [] :=
  .allocAll (.user "s") Str (.allocAll (.user "t") Str φ)
/-- `ids[t] = 1;` -/
def setIdsT (φ : Fml Names2 Γst) : Fml Names2 Γst :=
  .upd .box (.snoc .nil (.storage (.app3 .save (.app0 .storage) (at2 "ids" rfl kT) (.app1 .sval (n2 1))))) φ

/-- **`∀ s t. sha256(s) ≠ sha256(t) → ids[s] == 0 → shas[sha256(s)] == 1 →
[ ids[t] = 1; ] (ids[s] == 0 ∧ shas[sha256(s)] == 1)`**: proved; without the
`sha256`s apart, refuted by one string twice. -/
def twoKeys : Fml Names2 [] :=
  strings2 (.imp (.not (.eq sS sT)) (.imp (.eq (rd2 "ids" rfl kS) (n2 0))
    (.imp (.eq (rd2 "shas" rfl sS) (n2 1))
      (setIdsT (.and (.eq (rd2 "ids" rfl kS) (n2 0)) (.eq (rd2 "shas" rfl sS) (n2 1)))))))
def twoKeysBad : Fml Names2 [] :=
  strings2 (.imp (.eq (rd2 "ids" rfl kS) (n2 0)) (.imp (.eq (rd2 "shas" rfl sS) (n2 1))
    (setIdsT (.and (.eq (rd2 "ids" rfl kS) (n2 0)) (.eq (rd2 "shas" rfl sS) (n2 1))))))

/-- info: ["proved", "refuted"] -/
#guard_msgs in #eval [twoKeys, twoKeysBad].map verdict

/-- info: [true, true] -/
#guard_msgs in #eval [twoKeys, twoKeysBad].map (fun φ => φ.hashCovered && φ.inTarget {})

theorem twoKeys_covered : twoKeys.hashCovered = true := by decide +kernel

end TwoKeys

end Solidity.Examples.DecisionHashes
