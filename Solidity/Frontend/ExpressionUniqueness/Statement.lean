import Solidity.Frontend.Checked.Print
import Solidity.Frontend.Checked.Prec

/-!
# The original certified expression uniqueness target

This definition preserves the original target. Certified.certifiedYieldUnique
inhabits it by exhaustive intrinsic structural induction.
Layouts are independently existential through the existing `Syn.Derives`.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def CertifiedYieldUnique : Prop :=
  ∀ (a b : Syn .expr) (ts : List Tok),
    a.Derives ts → a.prec = true → b.Derives ts → b.prec = true → a = b

end Solidity.Frontend.ExpressionUniqueness
