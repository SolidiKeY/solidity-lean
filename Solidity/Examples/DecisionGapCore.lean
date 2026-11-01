import Solidity.Examples.DecisionMapping

namespace Solidity.Examples.Decision

open Solidity.Decide

set_option Elab.async false

/-! ## Counterexamples to `DecisionTheorem`

`DecisionTheorem` is not yet true.  One leaf per shape of `Fml.inTarget`
that `decideGoal` still answers `unknown` on: each in the fragment, by the
kernel, and answered `unknown` (the compiled verdicts below).  The list is
`docs/automation.md`'s (M7, "What is not proved"). -/

/-- The roots the shapes read. -/
def Gaps : Contract := contract!{
  struct Acc { uint v; bool live; }
  mapping(uint => mapping(uint => uint)) allow;
  mapping(uint => uint) balances;
  mapping(int => uint) ibal;
  mapping(bool => uint) flags;
  mapping(uint => Acc) accs;
  uint[] arr;
  uint[3] fixedArr;
}

section Gaps

local instance : InContract := ⟨Gaps⟩

/-! ### Quantifiers over contents

Outside `apfPrep`'s shapes once; all decided since (features 16 to 21,
pinned below; `gapArrayBlock` by feature 32, `Examples/DecisionArrays.lean`). -/

/-- A block whose bound index is not the last of its path (`m[i][3]`). -/
def gapColumn : Fml Gaps [] := dl!{ (∀ uint i; i < 10 → allow[i][3] == 0) → allow[1][3] == 0 }
/-- A root read at a bound index at two depths. -/
def gapTwoPaths : Fml Gaps [] :=
  dl!{ (∀ uint k; k < 10 → allow[3][k] == 0 && allow[k][3] == 0) → allow[3][5] == 0 }
/-- A block over a mapping keyed by `int` (feature 20), and by `bool`. -/
def gapIntKeyed : Fml Gaps [] := dl!{ (∀ int k; k < 10 → ibal[k] == 0) → ibal[5] == 0 }
def gapBoolKeyed : Fml Gaps [] := dl!{ (∀ bool b; flags[b] == 0) → flags[true] == 0 }
/-- A block reading a struct's member past the bound index. -/
def gapStructValue : Fml Gaps [] := dl!{ (∀ uint k; k < 10 → accs[k].v == 0) → accs[5].v == 0 }
/-- A block over an array. -/
def gapArrayBlock : Fml Gaps [] :=
  dl!{ (∀ uint i; i < 3 → arr[i] == 0) → arr.length > 5 → arr[1] == 0 }
/-- A block over the ledger (feature 21). -/
def gapLedgerBlock : Fml Gaps [] := dl!{ (∀ uint a; net(a) >= 0) → net(5) >= 0 }
/-- A guard with a partial ground operand (`x - 1` reverts at `0`). -/
def gapPartialGuard : Fml Gaps [] :=
  dl!{ ∀ uint x; (∀ uint k; k < x - 1 → balances[k] == 0) → x > 3 → balances[1] == 0 }
/-- A positive quantifier the prefix does not reach, reading at its variable. -/
def gapPositiveForall : Fml Gaps [] :=
  dl!{ ∀ uint x; balances[x] == 0 → (balances[x] == 0 && (∀ uint k; balances[k] == balances[k])) }

/-- False variants of the shapes decided since (features 16 to 19, below):
another column, another row, the other `bool`, another member, a guard
that halts or bounds at most `1`, a positive `∀` that fails. -/
def columnBad : Fml Gaps [] := dl!{ (∀ uint i; i < 10 → allow[i][3] == 0) → allow[1][4] == 0 }
def twoPathsBad : Fml Gaps [] :=
  dl!{ (∀ uint k; k < 10 → allow[3][k] == 0 && allow[k][3] == 0) → allow[4][5] == 0 }
def boolKeyedBad : Fml Gaps [] := dl!{ (∀ bool b; b == true → flags[b] == 0) → flags[false] == 0 }
def structValueBad : Fml Gaps [] :=
  dl!{ (∀ uint k; k < 10 → accs[k].v == 0) → accs[5].live == false }
def partialGuardBad : Fml Gaps [] :=
  dl!{ ∀ uint x; (∀ uint k; k < x - 1 → balances[k] == 0) → balances[1] == 0 }
def positiveForallBad : Fml Gaps [] :=
  dl!{ ∀ uint x; balances[x] == 0 → (balances[x] == 0 && (∀ uint k; balances[k] == 0)) }

/-- False variants of the blocks over `int` keys and over the ledger
(features 20 and 21, below): a key the guard leaves free, an address past
the guard's bound. -/
def intKeyedBad : Fml Gaps [] := dl!{ (∀ int k; k > 0 → ibal[k] == 0) → ibal[0] == 0 }
def ledgerBlockBad : Fml Gaps [] := dl!{ (∀ uint a; a <= 4 → net(a) >= 0) → net(5) >= 0 }
/-- Leaves of those shapes every refutation of which is astronomically
large: in every state refuting `intTwoSides`, `ibal` holds `1` at each
negative key and `2` at each positive one, so it lists at least
`2^255 - 1` entries; in every state refuting `ledgerFar`, the ledger holds
`1` at each address past `5`, `2^256 - 6` entries.  Decided by the
theorem, their refuting states terms that no evaluation builds (below). -/
def intTwoSides : Fml Gaps [] :=
  dl!{ (∀ int k; k < 0 → ibal[k] == 1) → (∀ int k; k > 0 → ibal[k] == 2) → ibal[0] == 3 }
def ledgerFar : Fml Gaps [] := dl!{ (∀ uint a; a > 5 → net(a) = 1) → net(3) = 1 }

/-- Counterexamples once, decided by the arrays' pipeline (feature 10,
below): a dynamic array's element at a checked index, and a fixed array's
at a literal one. -/
def arrayRead : Fml Gaps [] := dl!{ ∀ uint i; i < arr.length → arr[i] == arr[i] }
def fixedRead : Fml Gaps [] := dl!{ fixedArr[1] == fixedArr[1] }

end Gaps


section GapTerms

/-! ### Memory, the ledger and KeY's `int` without quantifiers -/

/-- Leaves written with the constructors: `dl!` has no notation for them. -/
def litU {Γ : Ctx} (n : Nat) : Tm Gaps Γ (.val .uint) := .app0 (.lit (uintOfNat n))
def litI {Γ : Ctx} (n : Int) (h : PrimTy.int.inRange n = true := by decide) : Tm Gaps Γ (.val .int) :=
  .app0 (.lit (p := .int) ⟨n, h⟩)
def isT {Γ : Ctx} (b : Tm Gaps Γ (.val .bool)) : Fml Gaps Γ := .eq b (.app0 (.lit (p := .bool) true))
def xU : Tm Gaps [.val .uint] (.val .uint) := .pvV .here
def xI : Tm Gaps [.val .int] (.val .int) := .pvV .here
def allU (φ : Fml Gaps [.val .uint]) : Fml Gaps [] := .all (.user "x") .uint φ
def allI (φ : Fml Gaps [.val .int]) : Fml Gaps [] := .all (.user "x") .int φ

/-- A memory read: `∀ fresh s. len(s) > 0 → s[0] == 0`.  A counterexample
once, decided by the fresh arrays' lane (below). -/
def gapMemory : Fml Gaps [] := .allocAll (.user "s") (.array (.prim .uint))
  (.imp (isT (.app2 (.binop .gt rfl) (.app2 .mlen (.app0 .memory) (.pvI .here)) (litU 0)))
    (.eq (.app2 .read (.app0 .memory) (.app2 (.mat .dyn) (.pvI .here) (litU 0))) (litU 0)))
/-- A binder of KeY's unbounded `int`: `∀ int z. z + 1 > z`.  A
counterexample once; proved since feature 26 (the binder read as a ledger
entry, `Fml.zT`). -/
def gapKIntBinder : Fml Gaps [] := .bind .box (.user "z") .kint
  (isT (.app2 (.zcmp .gt rfl) (.app2 (.zbin .add rfl) (.pvZ .here) (.app0 (.zlit 1))) (.pvZ .here)))
/-- Its false variant, `∀ int z. z + 1 > 5`, and two binders,
`∀ int z w. z > w → z > w - 1`. -/
def kintBinderBad : Fml Gaps [] := .bind .box (.user "z") .kint
  (isT (.app2 (.zcmp .gt rfl) (.app2 (.zbin .add rfl) (.pvZ .here) (.app0 (.zlit 1))) (.app0 (.zlit 5))))
def kintBinderTwo : Fml Gaps [] := .bind .box (.user "z") .kint (.bind .box (.user "w") .kint
  (.imp (isT (.app2 (.zcmp .gt rfl) (.pvZ (.there .here)) (.pvZ .here)))
    (isT (.app2 (.zcmp .gt rfl) (.pvZ (.there .here))
      (.app2 (.zbin .add rfl) (.pvZ .here) (.app0 (.zlit (-1))))))))
/-- A binder of KeY's `int` in a negative position, an `∃`: `(∀ int z.
z > 0) → 0 == 1`.  A counterexample once; proved since feature 30 (the
binder read over two words, `Examples/DecisionKInt.lean`). -/
def gapKIntNeg : Fml Gaps [] :=
  .imp (.bind .box (.user "z") .kint (isT (.app2 (.zcmp .gt rfl) (.pvZ .here) (.app0 (.zlit 0)))))
    (.eq (litU 0) (litU 1))
/-- The ledger read past a payment: `{pay(x, 1)} net(x) >= 0`.  A
counterexample once; refuted since feature 25 (the symbolic state keeps
the ledger writes, `NetW`): `x` any address but the contract's, its entry
`0`. -/
def gapLedgerWrite : Fml Gaps [] := allU (.upd .box (.snoc .nil (.pay xU (litU 1)))
  (isT (.app2 (.zcmp .ge rfl) (.app1 .net (.pvV .here)) (.app0 (.zlit 0)))))
/-- Its true variant: `net(x) >= 1 → {pay(x, 1)} net(x) >= 0`; and the
balance a payment leaves, `this.balance >= 2 → x != this → {pay(x, 1)}
this.balance >= 1`, with its false variant (no `x != this`, and
`this.balance >= 2` after: false at a balance of `2` and `x` any other
address). -/
def ledgerWriteOk : Fml Gaps [] := allU (.imp (isT (.app2 (.zcmp .ge rfl) (.app1 .net xU) (.app0 (.zlit 1))))
  (.upd .box (.snoc .nil (.pay xU (litU 1)))
    (isT (.app2 (.zcmp .ge rfl) (.app1 .net (.pvV .here)) (.app0 (.zlit 0))))))
def payBalanceOk : Fml Gaps [] :=
  allU (.imp (isT (.app2 (.binop .ge rfl) (.app0 (.env .selfBalance)) (litU 2)))
    (.imp (isT (.app2 (.binop .neB rfl) xU (.app0 (.env .selfAddress))))
      (.upd .box (.snoc .nil (.pay xU (litU 1)))
        (isT (.app2 (.binop .ge rfl) (.app0 (.env .selfBalance)) (litU 1))))))
def payBalanceBad : Fml Gaps [] :=
  allU (.imp (isT (.app2 (.binop .ge rfl) (.app0 (.env .selfBalance)) (litU 2)))
    (.upd .box (.snoc .nil (.pay xU (litU 1)))
      (isT (.app2 (.binop .ge rfl) (.app0 (.env .selfBalance)) (litU 2)))))
/-- Fifty storage reads: past `Fml.exactBounded`'s bounds. -/
def gapManyReads : Fml Gaps [] :=
  let bal (n : Nat) : Tm Gaps [.val .uint] (.val .uint) :=
    .app2 .find (.app0 .storage) (.app2 (.at .map) (.app0 (.root "balances" rfl)) (litU n))
  allU (.imp (Fml.conjL ((List.range 50).map fun n => .eq (bal n) xU)) (.eq (bal 0) (bal 49)))

/-! ### Operators with a literal operand, not carried through the stages -/

/-- `/`, `%` at `int` by a literal. -/
def gapIntDiv : Fml Gaps [] := allI (.imp (isT (.app2 (.binop .ge rfl) xI (litI 0)))
  (isT (.app2 (.binop .le rfl) (.app2 (.binop .mul rfl) (.app2 (.binop .div rfl) xI (litI 3)) (litI 3)) xI)))
def gapIntMod : Fml Gaps [] := allI (isT (.app2 (.binop .lt rfl) (.app2 (.binop .mod rfl) xI (litI 3)) (litI 3)))
/-- `|`, `^` with a literal, `&` with one that is not a low mask. -/
def gapOr : Fml Gaps [] := allU (isT (.app2 (.binop .ge rfl) (.app2 (.binop .bor rfl) xU (litU 1)) xU))
def gapXor : Fml Gaps [] := allU (isT (.app2 (.binop .neB rfl) (.app2 (.binop .bxor rfl) xU (litU 1)) xU))
def gapAnd : Fml Gaps [] := allU (isT (.app2 (.binop .le rfl) (.app2 (.binop .band rfl) xU (litU 6)) (litU 6)))
/-- `**` by a literal (`x ** 1`), `*%` by a literal. -/
def gapPow : Fml Gaps [] := allU (.eq (.app2 (.binop .pow rfl) xU (litU 1)) xU)
def gapMulW : Fml Gaps [] := allU (isT (.app2 (.binop .ge rfl) (.app2 (.binop .mulW rfl) xU (litU 3)) (litU 0)))

/-- Counterexamples once (decided since feature 22, below): `&` at `int`
with a literal (two's complement), and `addmod` with a literal modulus. -/
def gapIntAnd : Fml Gaps [] := allI (isT (.app2 (.binop .le rfl) (.app2 (.binop .band rfl) xI (litI 6)) (litI 6)))
def gapAddmod : Fml Gaps [] := allU (isT (.app2 (.binop .lt rfl) (.app3 (.modular .addmod) xU xU (litU 7)) (litU 7)))
/-- `x | 1 ≥ x` at `int`; `mulmod` by a literal factor on the left. -/
def intOr : Fml Gaps [] := allI (isT (.app2 (.binop .ge rfl) (.app2 (.binop .bor rfl) xI (litI 1)) xI))
def mulmodLt : Fml Gaps [] := allU (isT (.app2 (.binop .lt rfl) (.app3 (.modular .mulmod) (litU 3) xU (litU 7)) (litU 7)))

/-! ### Operators with a literal operand, decided: false variants -/

def intDivBad : Fml Gaps [] := allI (isT (.app2 (.binop .eqB rfl)
  (.app2 (.binop .mul rfl) (.app2 (.binop .div rfl) xI (litI 3)) (litI 3)) xI))
def intModBad : Fml Gaps [] := allI (isT (.app2 (.binop .ge rfl) (.app2 (.binop .mod rfl) xI (litI 3)) (litI 0)))
def orBad : Fml Gaps [] := allU (isT (.app2 (.binop .gt rfl) (.app2 (.binop .bor rfl) xU (litU 1)) xU))
def xorBad : Fml Gaps [] := allU (isT (.app2 (.binop .gt rfl) (.app2 (.binop .bxor rfl) xU (litU 1)) xU))
def andBad : Fml Gaps [] := allU (isT (.app2 (.binop .lt rfl) (.app2 (.binop .band rfl) (litU 6) xU) (litU 6)))
def powBad : Fml Gaps [] := allU (.eq (.app2 (.binop .pow rfl) xU (litU 0)) xU)
def mulWBad : Fml Gaps [] := allU (isT (.app2 (.binop .ge rfl) (.app2 (.binop .mulW rfl) (litU 3) xU) xU))
def intAndBad : Fml Gaps [] := allI (isT (.app2 (.binop .lt rfl) (.app2 (.binop .band rfl) (litI 6) xI) (litI 6)))
def intXorBad : Fml Gaps [] := allI (isT (.app2 (.binop .gt rfl) (.app2 (.binop .bxor rfl) xI (litI 1)) xI))
def addmodBad : Fml Gaps [] := allU (isT (.app2 (.binop .gt rfl) (.app3 (.modular .addmod) xU (litU 1) (litU 7)) (litU 0)))
def mulmodBad : Fml Gaps [] := allU (isT (.app2 (.binop .gt rfl) (.app3 (.modular .mulmod) xU (litU 3) (litU 7)) (litU 0)))
/-- A zero modulus fails, as `x / 0` does. -/
def addmodZero : Fml Gaps [] := allU (isT (.app2 (.binop .eqB rfl) (.app3 (.modular .addmod) xU (litU 1) (litU 0)) (litU 0)))

end GapTerms

/-! ### Hashes outside `Fml.hashCovered` (three of them inside since features 27 to 29) -/

section GapHashes

open Solidity.Examples.DecisionHashes
open Solidity.Examples.Tactics.Hashing (Names)

/-- Three kinds of hash of one string: a counterexample once, decided since
feature 28 (`Fml.tk3`, below). -/
def gapThreeKinds : Fml Names [] :=
  strings (.imp (.eq hS hT) (.imp (.eq shaS shaT)
    (.eq (.app2 (.hash .ripemd160) (.app0 .memory) (.pvI (.there .here)))
      (.app2 (.hash .ripemd160) (.app0 .memory) (.pvI .here)))))
/-- Two kinds, no string hashed by both: no kind to read the other's words
against.  A counterexample once, decided since feature 27 (one string of
the second kind needs no link, below). -/
def gapMixedKinds : Fml Names2 [] :=
  strings2 (.imp (.eq (rd2 "ids" rfl kS) (n2 1)) (.eq (rd2 "shas" rfl sT) (n2 1)))
/-- Two kinds each hashing two strings, no string hashed by both:
`keccak256(a) == keccak256(b) → sha256(c) == sha256(d)`.  In either order
the second kind's strings have no word of the first to link with, and
there are two of them (feature 27 takes one).  A counterexample once,
decided since feature 29 (the unlinked words moved, `Fml.tk_complete_move`,
below). -/
def gapMixedPairs : Fml Names [] :=
  strings4 (.imp (.eq (h4 .keccak sA) (h4 .keccak sB)) (.eq (h4 .sha256 sC) (h4 .sha256 sD)))
/-- A hash of written memory: `∀ s t. [ s[0] = 1; ] keccak256(s) ==
keccak256(t)`.  The verdict turns on the strings' bytes past the write,
which no stage reads (memory, plan step 6). -/
def gapWrittenMemory : Fml Names [] :=
  strings (.upd .box (.snoc .nil (.memory (.app3 .write (.app0 .memory)
    (.app2 (.mat .dyn) (.pvI (.there .here)) (num 0)) (.app1 .mval (num 1))))) (.eq hS hT))
/-- A hash under a negative value quantifier whose nodes the top premise
does not read: `∀ s t. (∀ x. keccak256(s) != keccak256(t)) → !(∀ y.
keccak256(s) == keccak256(t))`.  Valid as `holds` reads it, and false
under the premise exactly at two strings with different bytes and one
hash, where both inner premises fail: the only refutation is a
collision, which cannot be exhibited.  Outside `Fml.inTarget` since
decision e3″ (2026-10-26, `Fml.negPairUnread`, `docs/automation.md`, M6). -/
def gapHashNegForall : Fml Names [] :=
  let hs : Tm Names (.val .uint :: Γst) (.val .uint) := Tm.wk (.drop .refl) hS
  let ht : Tm Names (.val .uint :: Γst) (.val .uint) := Tm.wk (.drop .refl) hT
  strings (.imp (.all (.user "x") .uint (.not (.eq hs ht))) (.not (.all (.user "y") .uint (.eq hs ht))))

end GapHashes

theorem gapColumn_inTarget : gapColumn.inTarget {} = true := by decide +kernel
theorem gapTwoPaths_inTarget : gapTwoPaths.inTarget {} = true := by decide +kernel
theorem gapIntKeyed_inTarget : gapIntKeyed.inTarget {} = true := by decide +kernel
theorem gapBoolKeyed_inTarget : gapBoolKeyed.inTarget {} = true := by decide +kernel
theorem gapStructValue_inTarget : gapStructValue.inTarget {} = true := by decide +kernel
theorem gapArrayBlock_inTarget : gapArrayBlock.inTarget {} = true := by decide +kernel
theorem gapLedgerBlock_inTarget : gapLedgerBlock.inTarget {} = true := by decide +kernel
theorem gapPartialGuard_inTarget : gapPartialGuard.inTarget {} = true := by decide +kernel
theorem gapPositiveForall_inTarget : gapPositiveForall.inTarget {} = true := by decide +kernel
theorem gapMemory_inTarget : gapMemory.inTarget {} = true := by decide +kernel
theorem gapKIntBinder_inTarget : gapKIntBinder.inTarget {} = true := by decide +kernel
theorem gapKIntNeg_inTarget : gapKIntNeg.inTarget {} = true := by decide +kernel
theorem gapLedgerWrite_inTarget : gapLedgerWrite.inTarget {} = true := by decide +kernel
theorem gapManyReads_inTarget : gapManyReads.inTarget {} = true := by decide +kernel
theorem gapIntDiv_inTarget : gapIntDiv.inTarget {} = true := by decide +kernel
theorem gapIntMod_inTarget : gapIntMod.inTarget {} = true := by decide +kernel
theorem gapOr_inTarget : gapOr.inTarget {} = true := by decide +kernel
theorem gapXor_inTarget : gapXor.inTarget {} = true := by decide +kernel
theorem gapAnd_inTarget : gapAnd.inTarget {} = true := by decide +kernel
theorem gapPow_inTarget : gapPow.inTarget {} = true := by decide +kernel
theorem gapMulW_inTarget : gapMulW.inTarget {} = true := by decide +kernel
theorem gapIntAnd_inTarget : gapIntAnd.inTarget {} = true := by decide +kernel
theorem gapAddmod_inTarget : gapAddmod.inTarget {} = true := by decide +kernel
theorem gapThreeKinds_inTarget : gapThreeKinds.inTarget {} = true := by decide +kernel
theorem gapMixedKinds_inTarget : gapMixedKinds.inTarget {} = true := by decide +kernel
theorem gapMixedPairs_inTarget : gapMixedPairs.inTarget {} = true := by decide +kernel
theorem gapWrittenMemory_inTarget : gapWrittenMemory.inTarget {} = true := by decide +kernel
/-- Outside the fragment (e3″): the negative `∀ x` compares hashes its scope does not read. -/
theorem gapHashNegForall_outside : gapHashNegForall.inTarget {} = false := by decide +kernel


end Solidity.Examples.Decision
