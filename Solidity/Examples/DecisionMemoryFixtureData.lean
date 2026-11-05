import Solidity.Examples.DecisionGapData
import Solidity.Calculus.Fml

/-! Existing helpers and gapMemory source, independent of regression chains. -/
namespace Solidity.Examples.Decision

def litU {Γ : Ctx} (n : Nat) : Tm Gaps Γ (.val .uint) := .app0 (.lit (uintOfNat n))
def isT {Γ : Ctx} (b : Tm Gaps Γ (.val .bool)) : Fml Gaps Γ := .eq b (.app0 (.lit (p := .bool) true))
def allU (φ : Fml Gaps [.val .uint]) : Fml Gaps [] := .all (.user "x") .uint φ
/-- A memory read: `∀ fresh s. len(s) > 0 → s[0] == 0`.  A counterexample
once, decided by the fresh arrays' lane (below). -/
def gapMemory : Fml Gaps [] := .allocAll (.user "s") (.array (.prim .uint))
  (.imp (isT (.app2 (.binop .gt rfl) (.app2 .mlen (.app0 .memory) (.pvI .here)) (litU 0)))
    (.eq (.app2 .read (.app0 .memory) (.app2 (.mat .dyn) (.pvI .here) (litU 0))) (litU 0)))

end Solidity.Examples.Decision
