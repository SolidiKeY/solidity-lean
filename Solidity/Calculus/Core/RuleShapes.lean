import Solidity.Calculus.Core.Taclet
import Solidity.Calculus.RuleShapes

/-!
# Where each scoped taclet comes from

`Calculus/RuleShapes.lean`'s table for the scoped rules
(`Calculus/Core/Rules.lean`): a constructor transcribes the solkey taclets
its twin of the same name in `Rules.lean` does, the rows read off today's
table (`#check_constructor_table` holds them to `Core.Taclet`'s and
`Core.LeanTaclet`'s constructors).  Scoping claims what today's syntax
could not:

* `blockEmpty`: a block is a statement (`Stmt.block`), its end a frame
  (`Frames.pop .block`); its rule, `Core.Taclet.blockEmpty`, claims solkey's
  `blockEmpty`;
* `functionFrameEmpty`: a call's body runs as a block of its own frame,
  popped (or dropped from under its return variables) after it
  (`Premise.expandCall`); `functionBodyExpand` and `internalCallExpand`
  claim it with the expansion.

The callback taclets keep today's rows (`RuleShapes.callbackOrigins`) until
they are scoped (W2).
-/

namespace Solidity.Core.RuleShapes

open Solidity (KeyTaclet KeyOrigin)

/-- The scoped twin of a constructor of `Rules.lean`: the same name under
`Solidity.Core`. -/
def scopedName (n : Lean.Name) : Lean.Name := n.replacePrefix `Solidity `Solidity.Core

/-- Every scoped `Taclet` constructor, and the solkey taclets it transcribes. -/
def tacletOrigins : List (Lean.Name × KeyOrigin) :=
  (Solidity.RuleShapes.tacletOrigins.map fun (n, o) =>
    let o := if n == ``Solidity.Taclet.functionBodyExpand then
        .merged [.functionBodyExpand, .functionFrameEmpty]
      else if n == ``Solidity.Taclet.internalCallExpand then
        .merged [.internalCallExpand, .functionFrameEmpty]
      else o
    (scopedName n, o)) ++
  [(``Taclet.blockEmpty, .taclet .blockEmpty)]

#check_constructor_table Solidity.Core.Taclet, tacletOrigins.map Prod.fst

/-- Every scoped `LeanTaclet` constructor: today's rules with no taclet. -/
def leanTaclets : List Lean.Name := Solidity.RuleShapes.leanTaclets.map scopedName

#check_constructor_table Solidity.Core.LeanTaclet, leanTaclets

/-- Whether some row names the taclet. -/
def claims (t : KeyTaclet) : Bool :=
  (tacletOrigins ++ Solidity.RuleShapes.callbackOrigins).any fun r => r.2.taclets.contains t

/-- Every taclet some row names. -/
def claimedTaclets : List KeyTaclet := KeyTaclet.all.filter claims

/-- Today's unclaimed taclets (`RuleShapes.unclaimedTaclets`) but the two the
scoped syntax has the structure for. -/
def unclaimedTaclets : List KeyTaclet :=
  Solidity.RuleShapes.unclaimedTaclets.filter (fun t => t != .blockEmpty && t != .functionFrameEmpty)

/-- **The coverage fact**, scoped: the corpus splits into what the scoped
table claims and what it excuses. -/
theorem taclets_partitioned :
    KeyTaclet.all.all (fun t => claims t != unclaimedTaclets.contains t) = true := by
  decide +kernel

theorem claimedTaclets_count : claimedTaclets.length = 308 := by decide +kernel

theorem unclaimedTaclets_count : unclaimedTaclets.length = 15 := by decide +kernel

/-- The rule sets agree within a row (`RuleShapes.heuristics_agree`). -/
theorem heuristics_agree :
    tacletOrigins.all (fun r => (Solidity.RuleShapes.heuristics r.2).length == 1) = true := by
  decide +kernel

end Solidity.Core.RuleShapes
