import Solidity.Spec.Tactic

/-!
# Worked SolSpec obligations

The Lean side of `vscode-extension/examples/spec/Bank.sol`, written by
hand in exactly the shape the front-end emits. It is the reference for
the code generator (`vscode-extension/src/spec/emitLean.ts`): if the
generator's output stops looking like this, one of the two is wrong.

The contract:

```solidity
/// @custom:invariant balSender + balTo <= 2**256 - 1
contract Bank {
    uint256 balSender;
    uint256 balTo;

    /// @custom:requires amount <= balSender
    /// @custom:ensures balSender == old(balSender) - amount
    /// @custom:ensures balTo == old(balTo) + amount
    /// @custom:ensures balSender + balTo == old(balSender) + old(balTo)
    /// @custom:modifies balSender, balTo
    function transfer(uint256 amount) public {
        balSender -= amount;
        balTo += amount;
    }
}
```

Four things to notice, because they are the whole design:

* the initial state is built from Lean **variables**, so the obligation
  quantifies over every uint256 store — this is what makes the language
  Dafny-like rather than a test harness over one fixed store;
* `old(balSender)` needs no machinery: the pre-state maps `balSender` to
  the variable `balSender`, so `old(e)` is just `e` read at entry;
* `uint256` is a *hypothesis* (`inRange 0 MAX`) on the way in and an
  *obligation* on the way out — the `_range` theorem is where a
  narrower-width overflow would surface; at 256 bits the interpreter
  itself reverts on overflow (`Semantics.checkArith`), which the partial
  reading accepts and the total reading rejects;
* `@custom:modifies` becomes the `_frame` theorem: every primitive
  global outside the list still holds its entry value.
-/

namespace Solidity
namespace Spec
namespace Examples

open Semantics

/-- `2 ^ 256 - 1`, spelled as the numeral the front-end emits: `omega`
reasons about numerals, not about `2 ^ 256`. `@[simp]` so the
finisher's `simp_all` pass exposes the numeral to `omega` — the checked
arithmetic's `uintBound` guard arrives as a numeral, and `omega` treats
a folded `UINT256_MAX` as an opaque atom. -/
@[simp] abbrev UINT256_MAX : Int :=
  115792089237316195423570985008687907853269984665640564039457584007913129639935

namespace Bank

/-! ## Generated state and body

The generator inlines every expression rather than factoring out a
vocabulary, and this file matches it — which is not cosmetic: `sol_spec`
computes the interpreter's verdict with `rfl` after normalization, so a
storage place hidden behind a named definition stalls the very first
step. Whatever the generator emits has to be transparent to the same
`simp` set, and inlining is how it guarantees that. -/

/-- Entry state of `transfer`: the contract's storage with one Lean
variable per primitive global, and the parameters bound on the stack.
The types come from the Solidity declarations, never from the
`SoliditySyntax` name tables, so the generated program is independent of
any fixed contract schema. -/
def transferState (balSender balTo amount : Int) : State :=
  { storage := [("balSender", SVal.int balSender), ("balTo", SVal.int balTo)],
    env := [("amount", Binding.val (Value.int amount))] }

/-- The body, as an annotated block: `balSender -= amount;
balTo += amount;`. No ghost steps here; a `@custom:assert` in the source
would appear as `Ann.assert`. -/
def transferBody : List Ann :=
  [ Ann.stmt (Stmt.compoundAssign BinOp.sub
      (PlaceExpr.var Kind.storage Ty.uint
        (Field.primitive "balSender" Ty.uint (some StorageOrigin.global)))
      (WrappedExpr.var Kind.stack Ty.uint (Field.primitive "amount" Ty.uint))),
    Ann.stmt (Stmt.compoundAssign BinOp.add
      (PlaceExpr.var Kind.storage Ty.uint
        (Field.primitive "balTo" Ty.uint (some StorageOrigin.global)))
      (WrappedExpr.var Kind.stack Ty.uint
        (Field.primitive "amount" Ty.uint))) ]

/-! ## Generated obligations

One theorem per clause, so a failure lands on the `@custom:` line that
caused it. Hypotheses, in the order the emitter writes them: the range
of every input, the contract invariant, then the `@custom:requires`. -/

theorem transfer_ensures_1 (balSender balTo amount : Int)
    (hrange_balSender : inRange 0 UINT256_MAX balSender)
    (hrange_balTo : inRange 0 UINT256_MAX balTo)
    (hrange_amount : inRange 0 UINT256_MAX amount)
    (hinv_1 : balSender + balTo ≤ UINT256_MAX)
    (hpre_1 : amount ≤ balSender) :
    totalVC (transferState balSender balTo amount) transferBody
      (fun s => intAt s "balSender" [] = balSender - amount) := by
  sol_spec [transferState, transferBody]

theorem transfer_ensures_2 (balSender balTo amount : Int)
    (hrange_balSender : inRange 0 UINT256_MAX balSender)
    (hrange_balTo : inRange 0 UINT256_MAX balTo)
    (hrange_amount : inRange 0 UINT256_MAX amount)
    (hinv_1 : balSender + balTo ≤ UINT256_MAX)
    (hpre_1 : amount ≤ balSender) :
    totalVC (transferState balSender balTo amount) transferBody
      (fun s => intAt s "balTo" [] = balTo + amount) := by
  sol_spec [transferState, transferBody]

/-- Conservation: the interesting one, because it is a property of the
pair rather than of either global. -/
theorem transfer_ensures_3 (balSender balTo amount : Int)
    (hrange_balSender : inRange 0 UINT256_MAX balSender)
    (hrange_balTo : inRange 0 UINT256_MAX balTo)
    (hrange_amount : inRange 0 UINT256_MAX amount)
    (hinv_1 : balSender + balTo ≤ UINT256_MAX)
    (hpre_1 : amount ≤ balSender) :
    totalVC (transferState balSender balTo amount) transferBody
      (fun s =>
        intAt s "balSender" [] + intAt s "balTo" [] = balSender + balTo) := by
  sol_spec [transferState, transferBody]

/-- The `uint256` obligation: no underflow on `balSender -= amount`
(needs `hpre_1`), no overflow on `balTo += amount` (needs the contract
invariant). Drop either hypothesis and this theorem stops being
provable — which is exactly the overflow report. -/
theorem transfer_range (balSender balTo amount : Int)
    (hrange_balSender : inRange 0 UINT256_MAX balSender)
    (hrange_balTo : inRange 0 UINT256_MAX balTo)
    (hrange_amount : inRange 0 UINT256_MAX amount)
    (hinv_1 : balSender + balTo ≤ UINT256_MAX)
    (hpre_1 : amount ≤ balSender) :
    totalVC (transferState balSender balTo amount) transferBody
      (fun s => inRange 0 UINT256_MAX (intAt s "balSender" []) ∧
                inRange 0 UINT256_MAX (intAt s "balTo" [])) := by
  sol_spec [transferState, transferBody]

/-- The contract invariant, re-established on exit. -/
theorem transfer_invariant_1 (balSender balTo amount : Int)
    (hrange_balSender : inRange 0 UINT256_MAX balSender)
    (hrange_balTo : inRange 0 UINT256_MAX balTo)
    (hrange_amount : inRange 0 UINT256_MAX amount)
    (hinv_1 : balSender + balTo ≤ UINT256_MAX)
    (hpre_1 : amount ≤ balSender) :
    totalVC (transferState balSender balTo amount) transferBody
      (fun s => intAt s "balSender" [] + intAt s "balTo" [] ≤ UINT256_MAX) := by
  sol_spec [transferState, transferBody]

end Bank

/-! ## A specification that branches

`require` on a symbolic condition is where `sol_spec` does something
`sol_wp` never had to: the interpreter cannot settle the guard, so the
verdict comes back as an `ite` and the driver splits it. Under the
`@custom:partial` (box) reading the reverting branch discharges itself;
under the default total reading it would not, which is why the
precondition below is what makes the function verifiable at all. -/

namespace Guarded

def bumpState (counter step : Int) : State :=
  { storage := [("counter", SVal.int counter)],
    env := [("step", Binding.val (Value.int step))] }

/-- `require(step <= counter); counter -= step;` -/
def bumpBody : List Ann :=
  [ Ann.stmt (Stmt.requireStmt
      (WrappedExpr.binop BinOp.le
        (WrappedExpr.var Kind.stack Ty.uint (Field.primitive "step" Ty.uint))
        (WrappedExpr.var Kind.storage Ty.uint
          (Field.primitive "counter" Ty.uint (some StorageOrigin.global))))),
    Ann.stmt (Stmt.compoundAssign BinOp.sub
      (PlaceExpr.var Kind.storage Ty.uint
        (Field.primitive "counter" Ty.uint (some StorageOrigin.global)))
      (WrappedExpr.var Kind.stack Ty.uint (Field.primitive "step" Ty.uint))) ]

/-- Total correctness: the precondition rules the reverting branch out,
so the `require` must succeed. -/
theorem bump_ensures_1 (counter step : Int)
    (hrange_counter : inRange 0 UINT256_MAX counter)
    (hrange_step : inRange 0 UINT256_MAX step)
    (hpre_1 : step ≤ counter) :
    totalVC (bumpState counter step) bumpBody
      (fun s => intAt s "counter" [] = counter - step) := by
  sol_spec [bumpState, bumpBody]

/-- Partial correctness: no precondition at all, because the reverting
branch discharges the obligation vacuously. The `@custom:partial` tag
buys exactly this, and costs exactly what the box modality always
costs. -/
theorem bump_partial (counter step : Int)
    (hrange_counter : inRange 0 UINT256_MAX counter)
    (hrange_step : inRange 0 UINT256_MAX step) :
    partialVC (bumpState counter step) bumpBody
      (fun s => intAt s "counter" [] = counter - step) := by
  sol_spec [bumpState, bumpBody]

/-- `@custom:reverts_when step > counter`. -/
theorem bump_reverts_1 (counter step : Int)
    (hrange_counter : inRange 0 UINT256_MAX counter)
    (hrange_step : inRange 0 UINT256_MAX step)
    (hwhen_1 : counter < step) :
    revertsVC (bumpState counter step) bumpBody := by
  sol_spec [bumpState, bumpBody]

end Guarded

end Examples
end Spec
end Solidity
