import Solidity.Tactics.Derivation

namespace Solidity.Examples

open Rules StandardExample SoliditySyntax

set_option maxHeartbeats 8000000

/-! ## Value-operator derivations with operand capture

Binary operators only compute once both operands are simple stack
values; complex operands are first hoisted into the fresh value variable
`pv` (KeY `<op>CaptureLhs`/`<op>CaptureRhs`/`<op>_unfold_result`).

The `pv` these rules produce is a *stack* variable, spelled `pv@uint` /
`pv@bool` in the surface notation: a bare `pv` is a storage alias and
`SoliditySyntax.aliasKind` cannot see the type, so the kind is decided at
the use site (`SoliditySyntax.isStackScratchAlias`).  Before that existed
these derivations had to be written as raw `Stmt` constructors, which is
the one thing `.claude/rules/derivations.md` forbids.

Each administrative run (`localValueDeclInitDrop` → `valueDeclSkip`, plus the
operator step that fills `pv`) is elided into a single `⇝*` line with its
rules listed, the way the calculus collapses such runs. -/

/-! ### `result = i + amount` — both operands already simple
Simple means an *atom* (variable, literal) of any kind, so storage roots
like `age` also count. -/

example :
    solbox!{ result = i + amount } ⇝[.binopAssignment .add] solbox!{} := by
  rule_step

example :
    solbox!{ result = age + amount } ⇝[.binopAssignment .add] solbox!{} := by
  rule_step

/-! ### `result = alice.age + amount` — field operand captured first -/

sol_derivation addFieldOperandCaptured :
    solbox!{ result = alice.age + amount }
  ⇝[.binopUnfoldLeft BinOp.add]
    solbox!{ uint pv = alice.age; result = pv@uint + amount }
  ⇝*[.localValueDeclInitDrop, .valueDeclSkip, .storageFieldReadFind]
    solbox!{ result = pv@uint + amount }
  ⇝[.binopAssignment .add]
    solbox!{}

/-! ### `alice.age = x + y` — result into storage captured via `pv` -/

sol_derivation addResultCaptured :
    solbox!{ alice.age = x + y }
  ⇝[.binopUnfoldResult BinOp.add]
    solbox!{ uint pv = x + y; alice.age = pv@uint }
  ⇝*[.localValueDeclInitDrop, .valueDeclSkip, .binopAssignment .add]
    solbox!{ alice.age = pv@uint }
  ⇝[.storageFieldWriteSave]
    solbox!{}

/-! ### `assert(flag)` — simple condition -/

example : solbox!{ assert(flag) } ⇝[.assertSimple] solbox!{} := by rule_step

/-! ### `assert((i < amount))` — complex condition captured first -/

sol_derivation assertConditionCaptured :
    solbox!{ assert((i < amount)) }
  ⇝[.assertConditionCapture]
    solbox!{ bool pv = (i < amount); assert(pv@bool) }
  ⇝*[.localValueDeclInitDrop, .valueDeclSkip, .binopAssignment .lt]
    solbox!{ assert(pv@bool) }
  ⇝[.assertSimple]
    solbox!{}

/-! ### `to.transfer(amount)` / `owner.transfer(amount)` — simple operands
`transferNoCallback` books the payment on the `net` ledger in one step;
the storage root `owner` is an atom, so it needs no capture either. -/

example :
    solbox!{ to.transfer(amount) } ⇝[.transferNoCallback] solbox!{} := by
  rule_step

example :
    solbox!{ owner.transfer(amount) } ⇝[.transferNoCallback] solbox!{} := by
  rule_step

/-! ### `to.transfer(x + 2)` — complex amount captured first
Mirrors `net-transfer-capture-argument.key`. -/

sol_derivation transferAmountCaptured :
    solbox!{ to.transfer(x + 2) }
  ⇝[.transferUnfoldRightSndArgument]
    solbox!{ uint pv = x + 2; to.transfer(pv@uint) }
  ⇝*[.localValueDeclInitDrop, .valueDeclSkip, .binopAssignment .add]
    solbox!{ to.transfer(pv@uint) }
  ⇝[.transferNoCallback]
    solbox!{}

end Solidity.Examples
