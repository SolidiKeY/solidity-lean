import Solidity.Calculus.SoundPush

/-!
# Typed primitive push suffix regressions

The actual statement constructors run on empty and recycled primitive slots,
including unsigned failures, zero divisors and signed decrements. Prefix and
postfix forms have the same state result here because these are statements;
returning their expression values is a separate frontend feature.
-/

namespace Solidity.Examples.Tactics.PushSuffixRun

private def compound {C : Contract} {Γ : Ctx} {p : PrimTy} (op : BinOp)
    (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true)
    (b : SPath C Γ (.array (.prim p))) (rhs : Val C Γ p) (σ : State C Γ) :=
  (Stmt.pushOpAssign op hop hp b rhs).run σ

private def bump {C : Contract} {Γ : Ctx} {p : PrimTy} (op : IncDec)
    (hp : p.isNumeric = true) (b : SPath C Γ (.array (.prim p))) (σ : State C Γ) :=
  (Stmt.pushIncDec op hp b).run σ

def Example : Contract := contract!{ uint[] values; }

private def path : SPath Example [] (.array (.prim .uint)) := .loc (.root "values" rfl)
private def ref : SRef Example (.ref (.array (.prim .uint))) := .ofRoot "values" rfl
private def five : Val Example [] .uint := .simple (.lit 5 rfl)
private def two : Val Example [] .uint := .simple (.lit 2 rfl)
private def zero : Val Example [] .uint := .simple (.lit 0 rfl)

private def observe (σ : State Example []) : Option (Int × Int) := do
  let n ← σ.storage.len ref
  let v ← σ.storage.find (ref.index (.arr .dyn) ⟨0, rfl⟩)
  pure (n.1, PrimTy.key (p := .uint) (SVal.view v))

example : (compound .add rfl rfl path five (State.init Example)).toOption.bind (observe ·.st) =
    some (1, 5) := by decide +kernel

example : (compound .mul rfl rfl path five (State.init Example)).toOption.bind (observe ·.st) =
    some (1, 0) := by decide +kernel

example : (compound .div rfl rfl path two (State.init Example)).toOption.bind (observe ·.st) =
    some (1, 0) := by decide +kernel

example : (compound .mod rfl rfl path two (State.init Example)).toOption.bind (observe ·.st) =
    some (1, 0) := by decide +kernel

example : (compound .sub rfl rfl path five (State.init Example)).halt? = some .revert := by decide +kernel
example : (compound .div rfl rfl path zero (State.init Example)).halt? = some .revert := by decide +kernel

private def dirty : State Example [] :=
  (State.init Example).withStorage (.cons (.array .nil (.cons (.prim ⟨9, rfl⟩) .nil) (by decide)) .nil)

example : (compound .add rfl rfl path five dirty).toOption.bind (observe ·.st) = some (1, 5) := by
  decide +kernel

example : (bump .preInc rfl path dirty).toOption.bind (observe ·.st) =
    some (1, 1) := by decide +kernel
example : (bump .postInc rfl path dirty).toOption.bind (observe ·.st) =
    some (1, 1) := by decide +kernel
example : (bump .preDec rfl path (State.init Example)).halt? = some .revert := by decide +kernel
example : (bump .postDec rfl path (State.init Example)).halt? = some .revert := by decide +kernel

def SignedExample : Contract := contract!{ int[] values; }
private def signedPath : SPath SignedExample [] (.array (.prim .int)) :=
  .loc (.root "values" rfl)
private def signedRef : SRef SignedExample (.ref (.array (.prim .int))) := .ofRoot "values" rfl
private def signedTwo : Val SignedExample [] .int := .simple (.lit 2 rfl)
private def signedObserve (σ : State SignedExample []) : Option Int := do
  let v ← σ.storage.find (signedRef.index (.arr .dyn) ⟨0, rfl⟩)
  pure (PrimTy.key (p := .int) (SVal.view v))

example : (compound .sub rfl rfl signedPath signedTwo (State.init SignedExample)).toOption.bind
    (signedObserve ·.st) = some (-2) := by decide +kernel
example : (bump .preDec rfl signedPath (State.init SignedExample)).toOption.bind
    (signedObserve ·.st) = some (-1) := by decide +kernel
example : (bump .postDec rfl signedPath (State.init SignedExample)).toOption.bind
    (signedObserve ·.st) = some (-1) := by decide +kernel
example : (bump .preInc rfl signedPath (State.init SignedExample)).toOption.bind
    (signedObserve ·.st) = some 1 := by decide +kernel
example : (bump .postInc rfl signedPath (State.init SignedExample)).toOption.bind
    (signedObserve ·.st) = some 1 := by decide +kernel

-- A statement keeps the two updates; the second reads the appended storage.
example : (Stmt.pushOpAssign .add rfl rfl path five).step 0 .diamond =
    Premise.updates (Upd.nil.snoc (UpdElem.pushSlot path))
      (PushSuffix.saveOp .add rfl rfl path (.lit 5 rfl)) := rfl

-- The general soundness theorem covers every typed starting state.
example (σ : State Example []) :
    Premise.Runs .diamond (.pushOpAssign .add rfl rfl path five)
      (.updates (Upd.nil.snoc (UpdElem.pushSlot path))
        (PushSuffix.saveOp .add rfl rfl path (.lit 5 rfl))) σ :=
  PushSuffix.sound_pushOp .add rfl rfl path (.lit 5 rfl) rfl σ

end Solidity.Examples.Tactics.PushSuffixRun
