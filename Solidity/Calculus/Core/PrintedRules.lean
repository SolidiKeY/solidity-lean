import Solidity.Calculus.Core.RuleShapes
import Solidity.Calculus.PrintedRules

/-!
# The printed rules of the scoped taclets

`Calculus/PrintedRules.lean`'s table for the scoped rules: a constructor is
the printed rule its twin in `Rules.lean` is, the rows read off today's;
`blockEmpty`, scoped only, is a solkey taclet the printed rules leave out.
The partition of the printed rules is today's: scoping claims no printed
rule.
-/

namespace Solidity.Core.PrintedRules

open Solidity (PrintedRule PrintedOrigin LeanOnlyReason)
open Solidity.Core.RuleShapes (scopedName)

/-- Every scoped `Taclet` constructor, and the printed rule it is. -/
def printedOrigins : List (Lean.Name × PrintedOrigin) :=
  Solidity.PrintedRules.printedOrigins.map (fun (n, o) => (scopedName n, o)) ++
  [(``Taclet.blockEmpty, .leanOnly .keyTier)]

#check_constructor_table Solidity.Core.Taclet, printedOrigins.map Prod.fst

/-- Every scoped `LeanTaclet` constructor, and the printed rule it is. -/
def leanPrintedOrigins : List (Lean.Name × PrintedOrigin) :=
  Solidity.PrintedRules.leanPrintedOrigins.map fun (n, o) => (scopedName n, o)

#check_constructor_table Solidity.Core.LeanTaclet, leanPrintedOrigins.map Prod.fst

/-- Whether some row names the printed rule (the callback rows today's). -/
def claims (p : PrintedRule) : Bool :=
  (printedOrigins ++ leanPrintedOrigins ++ Solidity.PrintedRules.callbackPrintedOrigins).any
    fun r => r.2.rules.contains p

/-- **The coverage fact**, scoped: claimed exactly where today's table claims. -/
theorem printed_rules_partitioned :
    PrintedRule.all.all (fun p => claims p !=
      (p.kind != .rule || Solidity.PrintedRules.unclaimedRules.contains p)) = true := by
  decide +kernel

end Solidity.Core.PrintedRules
