import Solidity.AST
import Cslib.Foundations.Data.HasFresh

/-!
# Variables have fresh names

CSLib's `HasFresh` is a type with a name outside every finite set.  The
calculus's variables (`Var`, `AST.lean`) are one: `Var.fresh "x" k` for
every `k` are pairwise distinct, so CSLib picks one outside any finite set.
-/

namespace Solidity

/-- The fresh names `x1`, `x2`, …, as an embedding of `ℕ`. -/
def Var.freshEmbedding : ℕ ↪ Var :=
  ⟨fun k => .fresh "x" k, fun _ _ h => (Var.fresh.inj h).2⟩

/-- **Variables have fresh names** (CSLib's `HasFresh`). -/
instance : HasFresh Var := HasFresh.ofNatEmbed Var.freshEmbedding

/-- A fresh variable is fresh. -/
theorem Var.fresh_notMem (s : Finset Var) : HasFresh.fresh s ∉ s :=
  HasFresh.fresh_notMem s

end Solidity
