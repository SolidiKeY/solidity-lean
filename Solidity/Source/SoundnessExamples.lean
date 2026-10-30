import Solidity.Source.ValueProgress
import Solidity.Source.WellTyped
import Solidity.Source.TypingExamples

/-!
# Controls of the soundness lane (V04b)

Witnesses and negative controls for `Solidity/Source/ValueProgress.lean`
and `Solidity/Source/WellTyped.lean`: each progress lemma's domain is
inhabited by a value it computes, and each hypothesis is needed (outside
it the operation is `stuck`).

| Theorem | Statement |
|---|---|
| `add_ok`, `add_value` | `1 + 2` at `uint8` is in `binVal`'s domain and is `3` |
| `add_bool_stuck`, `add_bool_outside` | `+` on booleans is `stuck`, and outside `BinOp.FitsAt` |
| `cmp_add_stuck` | `cmpVal` with a non-comparison operator is `stuck` |
| `shift_bool_stuck` | `shiftVal` on a boolean is `stuck` |
| `addSub_opsOK`, `order_opsOK`, `shift_opsOK` | elaborated `a + a`, `a < 1`, `a << 1` (S01's controls) are `OpsOK` |
| `badBinary_not_opsOK` | a resolved `true + false`, which no derivation elaborates to, is not `OpsOK` |
| `refOK_wrong_heap` | a memory reference to an address the heap typing does not give its type does not agree |
-/

namespace Solidity.Source.SoundnessExamples

open Solidity.Source

variable {D : Layout}

def one8 : Val D (.int IntTy.u8) := .int 1 (by decide)
def two8 : Val D (.int IntTy.u8) := .int 2 (by decide)

/-- **Witness**: `+` at `uint8` is in `binVal`'s domain. -/
theorem add_ok : NotStuckR (binVal (D := D) true .add one8 two8) :=
  binVal_ok true (.inl ⟨rfl, rfl⟩) _ _

/-- ... and computes `3`. -/
theorem add_value : (binVal (D := D) true .add one8 two8) = .ok (.int 3 (by decide)) := rfl

/-- **Negative control**: `+` on booleans is `stuck`. -/
theorem add_bool_stuck :
    binVal (D := D) true .add (.bool true) (.bool false) = .error (.stuck "not a boolean operation") := rfl

/-- ... and it is outside `binVal_ok`'s domain. -/
theorem add_bool_outside : ¬ BinOp.add.FitsAt .bool := by
  intro h
  rcases h with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> cases h

/-- **Negative control**: `cmpVal` with an arithmetic operator is `stuck`. -/
theorem cmp_add_stuck : cmpVal (D := D) .add one8 two8 = .error (.stuck "not a comparison") := rfl

/-- **Negative control**: `shiftVal` on a boolean is `stuck`. -/
theorem shift_bool_stuck : shiftVal (D := D) true .shl 1 (.bool true) = .error (.stuck "shift operand") := rfl

open TypingExamples in
/-- **Witnesses**: S01's own derivations elaborate into the domains. -/
theorem addSub_opsOK : w_addSub.toR.OpsOK := Typed.toR_opsOK _

open TypingExamples in
theorem order_opsOK : w_order.toR.OpsOK := Typed.toR_opsOK _

open TypingExamples in
theorem shift_opsOK : w_shift.toR.OpsOK := Typed.toR_opsOK _

/-- **Negative control**: `OpsOK` is not trivial — a resolved `true + false`
(an `RExpr`, which no derivation elaborates to) is not in the domain. -/
theorem badBinary_not_opsOK {E : Env} :
    ¬ (RExpr.binary (E := E) (Γ := []) .add (.bool true) (.bool false)).OpsOK := by
  intro h
  rcases h.1 with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> cases h

/-- **Negative control**: a memory reference agrees only with a heap typing
that gives its address its type. -/
theorem refOK_wrong_heap {E : Env} :
    ¬ (Val.memRef (D := E.layout) (τ := .bytes .memory) rfl 0).RefOK E (fun _ => some .bool) := by
  intro h
  cases h

/-- **Witness**: the same reference agrees with a heap typing that gives
address `0` the type `bytes memory`. -/
theorem refOK_heap {E : Env} :
    (Val.memRef (D := E.layout) (τ := .bytes .memory) rfl 0).RefOK E (fun _ => some (.bytes .memory)) := rfl

end Solidity.Source.SoundnessExamples
