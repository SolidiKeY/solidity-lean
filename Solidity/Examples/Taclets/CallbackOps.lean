import Solidity.Examples.Common
import Solidity.CallbackSemantics

/-!
# `transferWithCallback` examples (KeY `transferSemantics:withCallback`)

`HoldsC inv j` is validity under the callback-aware semantics: at each
`transfer`, the contract invariant `inv` must hold in the post-debit
state (KeY branch "invariant on exit"), and the continuation must hold
in *every* havocked state satisfying `inv` (branch "resume after
callback"). Havoc branches are genuinely symbolic — `native_decide`
cannot discharge them — so these proofs go through
`holdsC_transfer_split` and the peeling lemmas.
-/

namespace Solidity
namespace TacletExamples.Callback

open Rules StandardExample SoliditySyntax Examples
open CallbackSemantics Semantics

set_option maxHeartbeats 8000000

/-- Evaluate a concrete `execStmt`/`evalInt` equation whose right-hand side is
an implicit metavariable: simp with the interpreter equations computes the
normal form, `rfl` assigns it. (Replaces `with_unfolding_all rfl`, which
relied on pre-4.29 well-founded definitional unfolding.) -/
local macro "exec_eval" : tactic =>
  `(tactic| (simp [Semantics.execStmt, Semantics.execAssign,
                   Semantics.evalValue, Semantics.evalInt,
                   Semantics.resolveLoc, Semantics.writeValue,
                   bind, Except.bind, Semantics.State.getEnv,
                   Semantics.State.setEnv, Semantics.State.getNet,
                   Semantics.State.setNet, Semantics.State.exampleStore,
                   Semantics.lookupBy, Semantics.setBy,
                   Semantics.applyBinOp, Semantics.Value.asInt,
                   Semantics.resolveS, Semantics.resolveMBase,
                   Semantics.readM, Semantics.State.findStorage,
                   Semantics.State.saveStorage, Semantics.SVal.find,
                   Semantics.SVal.save, Semantics.Value.toSVal,
                   Semantics.SVal.asValue,
                   SoliditySyntax.intLitExpr, SoliditySyntax.varExpr,
                   SoliditySyntax.rootPlace, SoliditySyntax.varPlace,
                   SoliditySyntax.fieldPlace, SoliditySyntax.indexPlace,
                   SoliditySyntax.rootExpr, SoliditySyntax.stackCallExpr,
                   SoliditySyntax.callExpr, SoliditySyntax.fieldFor,
                   SoliditySyntax.originFor, SoliditySyntax.binopExpr];
             try rfl))

/-- The trivial invariant: the callback may do anything. -/
def trivInv : CInvPred := fun _ _ => True

/-- `uint amount = 2; uint addr = 1; result = 1; addr.transfer(amount)`. -/
def setupAndTransfer : Block :=
  sblock!{ uint amount = 2; uint addr = 1; result = 1;
           addr.transfer(amount) }

/-- Locals survive the callback: `result` is set before the transfer
and read only from the caller's frame, so the judgment holds under
*any* callback behaviour (`trivInv`). Branch (a) is trivial; branch (b)
is a symbolic havoc, closed by computation on the untouched `env`. -/
example :
    (SolidityJudgment.mk ⟨.diamond, setupAndTransfer⟩
      sexpr!{ (result == 1) }).HoldsC trivInv := by
  simp only [setupAndTransfer]
  rw [holdsC_cons_det (by simp [IsTransfer]) (by exec_eval),
    holdsC_cons_det (by simp [IsTransfer]) (by exec_eval),
    holdsC_cons_det (by simp [IsTransfer]) (by exec_eval),
    holdsC_transfer_split (by exec_eval)]
  refine ⟨trivial, fun st nt _ _ => ?_⟩
  rw [holdsC_nil]
  simp only [COut.checkOut]
  simp [evalValue, evalInt, State.getEnv, State.getNet, State.havoc,
    State.setEnv, State.setNet, State.exampleStore, lookupBy, setBy,
    applyBinOp, applyUnOp, checkArith, BinOp.retTy, UnOp.retTy,
    Value.asInt, Value.asBool,
    Field.name, Field.primitive,
    bind, Except.bind,
    SoliditySyntax.callExpr, SoliditySyntax.stackCallExpr,
    SoliditySyntax.rootExpr, SoliditySyntax.varExpr,
    SoliditySyntax.fieldFor, SoliditySyntax.originFor,
    SoliditySyntax.intLitExpr, SoliditySyntax.binopExpr]

/-- A contract invariant on the ledger: account `1` still owes exactly
the booked debit. Branch (a) (invariant on exit) is by computation;
branch (b) reads the havocked ledger *through the invariant*. -/
def netInv : CInvPred := fun _ nt => lookupBy (1 : Int) nt = some (-2)

example :
    (SolidityJudgment.mk ⟨.diamond, setupAndTransfer⟩
      sexpr!{ (net(addr) == -2) }).HoldsC netInv := by
  simp only [setupAndTransfer]
  rw [holdsC_cons_det (by simp [IsTransfer]) (by exec_eval),
    holdsC_cons_det (by simp [IsTransfer]) (by exec_eval),
    holdsC_cons_det (by simp [IsTransfer]) (by exec_eval),
    holdsC_transfer_split (by exec_eval)]
  refine ⟨by
      simp [netInv, State.setNet, State.setEnv, State.getNet,
        State.exampleStore, setBy, lookupBy], fun st nt _ hst => ?_⟩
  rw [holdsC_nil]
  simp only [netInv] at hst
  simp only [COut.checkOut]
  simp [evalValue, evalInt, State.getEnv, State.getNet, State.havoc,
    State.setEnv, State.setNet, State.exampleStore, lookupBy, setBy,
    applyBinOp, applyUnOp, checkArith, BinOp.retTy, UnOp.retTy,
    Value.asInt, Value.asBool,
    Field.name, Field.primitive,
    bind, Except.bind,
    SoliditySyntax.callExpr, SoliditySyntax.stackCallExpr,
    SoliditySyntax.rootExpr, SoliditySyntax.varExpr,
    SoliditySyntax.fieldFor, SoliditySyntax.originFor,
    SoliditySyntax.intLitExpr, SoliditySyntax.binopExpr, hst]

/-- KeY's negative shape (the calculus's transfer-before-write flavour):
under the *trivial* invariant nothing pins the havocked ledger, so a
post reading `net` is not valid — the callback may repay the debt. -/
example :
    ¬ (SolidityJudgment.mk ⟨.diamond, setupAndTransfer⟩
        sexpr!{ (net(addr) == -2) }).HoldsC trivInv := by
  intro H
  simp only [setupAndTransfer] at H
  rw [holdsC_cons_det (by simp [IsTransfer]) (by exec_eval),
    holdsC_cons_det (by simp [IsTransfer]) (by exec_eval),
    holdsC_cons_det (by simp [IsTransfer]) (by exec_eval),
    holdsC_transfer_split (by exec_eval)] at H
  -- resume with the debt repaid: `nt = []`
  have := (H.2 State.exampleStore.storage [] 0 trivial)
  rw [holdsC_nil] at this
  simp only [COut.checkOut] at this
  revert this
  simp [evalValue, evalInt, State.getEnv, State.getNet, State.havoc,
    State.setEnv, State.setNet, State.exampleStore, lookupBy, setBy,
    applyBinOp, applyUnOp, checkArith, BinOp.retTy, UnOp.retTy,
    Value.asInt, Value.asBool,
    Field.name, Field.primitive,
    bind, Except.bind,
    SoliditySyntax.callExpr, SoliditySyntax.stackCallExpr,
    SoliditySyntax.rootExpr, SoliditySyntax.varExpr,
    SoliditySyntax.fieldFor, SoliditySyntax.originFor,
    SoliditySyntax.intLitExpr, SoliditySyntax.binopExpr]

/-- The same judgment holds under the deterministic `noCallback`
reading — together with the previous example this is the closed/open
matrix: `HoldsC` is strictly stronger than `Holds`
(`holds_of_holdsC` gives the inclusion). -/
example :
    (SolidityJudgment.mk ⟨.diamond, setupAndTransfer⟩
      sexpr!{ (net(addr) == -2) }).Holds := by
  native_decide

end TacletExamples.Callback
end Solidity
