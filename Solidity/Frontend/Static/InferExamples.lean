import Solidity.Frontend.Static.WellFormedCheck
import Solidity.Source.TypingExamples

/-!
# G13 controls: the checkers on S01's own examples

S01's controls (`Solidity/Source/TypingExamples.lean`) are hand-written
derivations and refutations.  Here the checkers compute the same verdicts
in the kernel (`decide`), independently of those proofs:

| Theorem | Statement |
|---|---|
| `counter_checked` | S00's counter is `WellFormed` and in the syntax profile, by `wellFormedB` (no hand derivation) |
| `clashing_checked`, `sameSig_checked`, `ifaceBody_checked`, `twoCtors_checked`, `noVisibility_checked` | S01's five ill-formed units are refused |
| `tooBig_checked`, `fits_checked` | `uint8 x = 300;` has no statement derivation; `uint8 x = 255;` has one |
| `shl18_checked`, `gasleft_checked`, `msgValue_checked` | `1 << 8` has only its folded type; `gasleft()` and `msg.value` in a non-payable public body have none |
| `zero_types`, `addLit_types`, `cond_types` | `0x00` has 33 types (the constant and `bytes1`…`bytes32`); `a + 1` and `b ? a : a` have exactly one |
| `require_checked` | `require(b, "no");` is a statement |
-/

namespace Solidity.Frontend.Static.InferExamples

open Solidity.Source Solidity.Source.TypingExamples Solidity.Frontend.Static

/-- **The counter, checked**: well formed and in the syntax profile. -/
theorem counter_checked : WellFormed counterRes ∧ InProfileSyntax counterRes :=
  ⟨wellFormed_iff.mp (by decide), inProfileSyntaxB_iff.mp (by decide)⟩

/-- A refusal of `wellFormedB` refutes `WellFormed`. -/
theorem refuted {r : Resolution} (h : wellFormedB r = false) : ¬ WellFormed r := fun w => by
  rw [wellFormed_iff.mpr w] at h
  cases h

def legacy : Settings := ⟨.legacy, []⟩

theorem clashing_checked : ¬ WellFormed (resolveUnit legacy clashing) := refuted (by decide)
theorem sameSig_checked : ¬ WellFormed (resolveUnit legacy sameSig) := refuted (by decide)
theorem ifaceBody_checked : ¬ WellFormed (resolveUnit legacy ifaceBody) := refuted (by decide)
theorem twoCtors_checked : ¬ WellFormed (resolveUnit legacy twoCtors) := refuted (by decide)
theorem noVisibility_checked : ¬ WellFormed (resolveUnit legacy noVisibility) := refuted (by decide)

/-- **Negative control**: `uint8 x = 300;` has no derivation (in `Γ`). -/
theorem tooBig_checked (L' : List (String × STy)) : ¬ StmtOK Γ Γ.locals tooBig L' := fun h => by
  have hm := stmtOK_iff.mp h
  have e : (stmtLocals Γ tooBig Γ.locals).isEmpty = true := by decide
  rw [List.isEmpty_iff.mp e] at hm
  cases hm

/-- `uint8 x = 255;` -/
def fits : Syn (.stmt .body) :=
  .simpleStmt (.declVar (.varDecl (.elem (.int false 8 (by decide))) none "x")
    (.some (.lit (.num (.dec 255 0 0)))))

theorem fits_checked : (stmtLocals Γ fits Γ.locals).length = 1 := by decide

/-- `1 << 8` has one type, its folded constant. -/
theorem shl18_checked : (inferTys Γ shl18).map (STy.same (.rational ⟨256, 1, by decide⟩)) = [true] := by
  decide

/-- **Negative control**: `gasleft()` has no type. -/
theorem gasleft_checked : (inferTys Γ (.call (.ident "gasleft") (.positional .nil))).isEmpty = true := by
  decide

/-- **Negative control**: `msg.value` in a non-payable public body has no type. -/
theorem msgValue_checked : (inferTys Γv (.member (.ident "msg") "value")).isEmpty = true := by decide

/-- `0x00`: its constant and every `bytesN`. -/
theorem zero_types : (inferTys Γ (.lit (.num (.hex [0, 0] false)))).length = 33 := by decide

theorem addLit_types : (inferTys Γ (.addSub .add a one)).length = 1 := by decide

theorem cond_types : (inferTys Γ (.cond (.ident "b") a a)).length = 1 := by decide

theorem require_checked :
    (stmtLocals (k := .body) Γ (.simpleStmt (.exprStmt (.call (.ident "require")
      (.positional (.cons (.ident "b") (.cons (.lit (.str [110, 111])) .nil)))))) Γ.locals).length = 1 := by
  decide

end Solidity.Frontend.Static.InferExamples
