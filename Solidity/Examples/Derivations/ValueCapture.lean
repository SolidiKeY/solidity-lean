import Solidity.Tactics.Derivation

namespace Solidity.Examples

open Rules StandardExample SoliditySyntax

set_option maxHeartbeats 8000000

/-! ## Value-operator derivations with operand capture

Binary operators only compute once both operands are simple stack
values; complex operands are first hoisted into the fresh value variable
`se` (KeY `<op>CaptureLhs`/`<op>CaptureRhs`); a complex value written to storage
is frozen by the write's own `*UnfoldSource` rule.

The `se` these rules produce is a *stack* variable, spelled `se@uint` /
`se@bool` in the surface notation: a bare `se` is a storage alias and
`SoliditySyntax.aliasKind` cannot see the type, so the kind is decided at
the use site (`SoliditySyntax.isStackScratchAlias`).  Before that existed
these derivations had to be written as raw `Stmt` constructors, which is
the one thing `.claude/rules/derivations.md` forbids.

Each administrative run (`localValueDeclInitDrop` → `valueDeclSkip`, plus the
operator step that fills `se`) is elided into a single `⇝*` line with its
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
    solbox!{ uint se = alice.age; result = se@uint + amount }
  ⇝*[.localValueDeclInitDrop, .valueDeclSkip, .storageFieldReadFind]
    solbox!{ result = se@uint + amount }
  ⇝[.binopAssignment .add]
    solbox!{}

/-! ### `alice.age = x + y` — the value source frozen into `se` by the write -/

sol_derivation addResultCaptured :
    solbox!{ alice.age = x + y }
  ⇝[.storageFieldWriteUnfoldSource]
    solbox!{ uint se = x + y; alice.age = se@uint }
  ⇝*[.localValueDeclInitDrop, .valueDeclSkip, .binopAssignment .add]
    solbox!{ alice.age = se@uint }
  ⇝[.storageFieldWriteSave]
    solbox!{}

/-! ### `assert(flag)` — simple condition -/

example : solbox!{ assert(flag) } ⇝[.assertSimple] solbox!{} := by rule_step

/-! ### `assert((i < amount))` — complex condition captured first -/

sol_derivation assertConditionCaptured :
    solbox!{ assert((i < amount)) }
  ⇝[.assertConditionCapture]
    solbox!{ bool se = (i < amount); assert(se@bool) }
  ⇝*[.localValueDeclInitDrop, .valueDeclSkip, .binopAssignment .lt]
    solbox!{ assert(se@bool) }
  ⇝[.assertSimple]
    solbox!{}

/-! ### `to.transfer(amount)` / `owner.transfer(amount)` — simple operands
`transferNoCallbackBox` books the payment on the `net` ledger in one step
(the diamond twin adds the "sufficient funds" obligation);
the storage root `owner` is an atom, so it needs no capture either. -/

example :
    solbox!{ to.transfer(amount) } ⇝[.transferNoCallbackBox] solbox!{} := by
  rule_step

example :
    solbox!{ owner.transfer(amount) } ⇝[.transferNoCallbackBox] solbox!{} := by
  rule_step

/-! ### `to.transfer(x + 2)` — complex amount captured first
Mirrors `net-transfer-capture-argument.key`. -/

sol_derivation transferAmountCaptured :
    solbox!{ to.transfer(x + 2) }
  ⇝[.transferUnfoldRightSndArgument]
    solbox!{ uint se = x + 2; to.transfer(se@uint) }
  ⇝*[.localValueDeclInitDrop, .valueDeclSkip, .binopAssignment .add]
    solbox!{ to.transfer(se@uint) }
  ⇝[.transferNoCallbackBox]
    solbox!{}

end Solidity.Examples
