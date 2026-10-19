import Solidity.Calculus.Taclet

/-!
# The callback taclets

The unscoped table's `CallbackTaclet` (solkey's `…WithCallbackBox`), its
lines read under `open scoped Solidity.Schema` as `Calculus/Rules.lean`
reads the table.  Each premise is the one its no-callback twin leaves, and
so the one `Stmt.step` builds (`CallbackTaclet.toStep`).  The judgement that
reads them (`ProvesC`) and their printer are `Calculus/Callback.lean`'s;
the rules sit here, below the sequents, so the rule table's checks
(`Calculus/RuleShapes.lean`) need nothing above the table.
-/

namespace Solidity

open Solidity (Modality)

open scoped Solidity.Schema

/-- solkey's callback taclets: a payment, a send and a `try` under the box,
and a send under the diamond, with callbacks into the contract (solkey's
`transferWithCallbackDiamond` is not: no diamond over a `transfer` is
derived, `RuleShapes.unclaimedTaclets`). -/
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
  | sendWithCallbackDiamond :
      dl[CallbackTaclet C k]{ ⟨ pv = sadr.send(se); ⟩ ⇝
          "non-negative amount": 0 <= se
        ; "send succeeded":
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
  | .sendWithCallbackDiamond => .sendNoCallbackDiamond
  | .tryCallWithCallbackBox => .tryCallNoCallbackBox

/-- **A callback taclet's premise is the one `Stmt.step` builds.** -/
theorem CallbackTaclet.toStep {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} (d : CallbackTaclet C k m s p) : s.step k m = p :=
  d.toTaclet.toStep

end Solidity
