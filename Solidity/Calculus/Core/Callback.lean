import Solidity.Calculus.Core.Taclet
import Solidity.Calculus.Core.Delab

/-!
# The callback taclets on scoped statements

`Calculus/Rules.lean`'s `CallbackTaclet` (solkey's `…WithCallbackBox`), its
lines read under `open scoped Solidity.Core.Schema` as `Calculus/Core/Rules.lean`
reads the table.  Each premise is the one its no-callback twin leaves, and
so the one `Stmt.step` builds (`CallbackTaclet.toStep`): what a callback
changes is how the premise is read, the invariant owed on exit and the
callee's `{havoc}` (`ProvesC`), not what the rule leaves.

The rules print as today's (`dl[CallbackTaclet C k]{ … }`, `delabCallbackTaclet`),
their goals labelled by their no-callback twins' labels.
-/

namespace Solidity.Core

open Solidity (Modality)

open scoped Solidity.Core.Schema

/-- solkey's callback taclets: a payment, a send and a `try` under the box,
with callbacks into the contract. -/
inductive CallbackTaclet (C : Contract) (k : Nat) :
    Modality → {Γ Γ' : Ctx} → Stmt C Γ Γ' → Premise C Γ Γ' → Prop where
  | transferWithCallbackBox :
      dl[CallbackTaclet C k]{ [ sadr.transfer(se); ] ⇝
        { net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se) } ⟨[ ]⟩ }
  | sendWithCallbackBox :
      dl[CallbackTaclet C k]{ [ pv = sadr.send(se); ] ⇝
          "send succeeded":
            { net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se) ‖ pv := true }
            ⟨[ ]⟩
        ; "send failed": { pv := false } ⟨[ ]⟩ }
  | tryCallWithCallbackBox :
      dl[CallbackTaclet C k]{ [ try call returns (rets) body catch Error errorBody
              catch Panic (code) panicBody catch otherBody; ] ⇝
          "call succeeded": ∀ rets. [ body ] ; "Error caught": [ errorBody ]
          ; "Panic caught": ∀ code. [ panicBody ] ; "other failure caught": [ otherBody ] }

variable {C : Contract}

/-- A callback taclet is its no-callback twin, line for line. -/
theorem CallbackTaclet.toTaclet {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} : CallbackTaclet C k m s p → Taclet C k m s p
  | .transferWithCallbackBox => .transferNoCallbackBox
  | .sendWithCallbackBox => .sendNoCallbackBox
  | .tryCallWithCallbackBox => .tryCallNoCallbackBox

/-- **A callback taclet's premise is the one `Stmt.step` builds.** -/
theorem CallbackTaclet.toStep {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} (d : CallbackTaclet C k m s p) : s.step k m = some p :=
  d.toTaclet.toStep

end Solidity.Core

namespace Solidity.Core.Delab

open Lean Meta PrettyPrinter Delaborator SubExpr
open Solidity (ppStmt ppPremise? ppOn isEscape)

/-- `Core.CallbackTaclet C k m s p`: `dl[CallbackTaclet C k]{ [ s; ] ⇝ p }`,
as `Rules.lean`'s delaborator prints today's, the goals labelled as the
no-callback twin's. -/
@[delab app.Solidity.Core.CallbackTaclet]
def delabCallbackTaclet : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  guard (e.getAppNumArgs == 7)
  let m ← whnf (e.getArg! 2)
  let out? ← withTwins e false fun env => do
    let st ← (tr [] (e.getArg! 5)).run env
    let p ← (tr [] (e.getArg! 6)).run env
    let st' ← whnf st
    let rule? := Solidity.Taclet.labelledBy (st'.getAppFn.constName?.getD Lean.Name.anonymous)
      (m.isConstOf ``Modality.diamond)
    let labels := (do (← Solidity.Taclet.branchLabels.lookup (← rule?))).getD []
    let some p ← ppPremise? p labels (m.isConstOf ``Modality.box) | return none
    return some (← ppStmt st, p)
  let some (s, p) := out? | failure
  if isEscape s then failure
  let args ← (List.range 2).toArray.mapM fun i => withNaryArg i delab
  let J ← `($(mkIdent (← unresolveNameGlobal ``CallbackTaclet)) $args*)
  match_expr m with
  | Modality.box => `(dl[ $J ]{ [ $s:sol_stmt; ] ⇝ $p })
  | Modality.diamond => `(dl[ $J ]{ ⟨ $s:sol_stmt; ⟩ ⇝ $p })
  | _ => `(dl[ $J ]{ ⟨[ $s:sol_stmt; ]⟩ ⇝ $p })

end Solidity.Core.Delab
