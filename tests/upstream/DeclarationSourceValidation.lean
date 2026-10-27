import Solidity.Frontend.Testing
import Solidity.Tools.Counterexample
open Solidity Solidity.Frontend
open scoped Solidity.Scoped
solc_import "../solc/CalldataValidation.ast.json" hash 0xbc741802a7ad102c as Group08SourceValidation.Calldata testing
solc_scoped_problems Group08SourceValidation.Calldata decl
namespace Solidity.Tests.Upstream.DeclarationSourceValidation

private def emptyState : State Group08SourceValidation.Calldata [] :=
  { storage := Storage.init Group08SourceValidation.Calldata,
    H := [.array (.prim .uint)], heap := (⟨[], by decide⟩, ()), env := () }
private def emptyRef : HRef [.array (.prim .uint)] (.array (.prim .uint)) := ⟨0, rfl⟩
/-- An initialized empty byte input satisfies every original source premise
but reverts at the slice bound, so the unchanged diamond is not derivable. -/
theorem sliceHashed_notDerivable : ¬ (⊢ Group08SourceValidation.Calldata.sliceHashed.problem) := by
  intro h
  have hx :
      holds (emptyState.push (t := .mem (.array (.prim .uint))) (some emptyRef))
        (Fml.refInputs Group08SourceValidation.Calldata [.mem (.array (.prim .uint))]) →
      holds (emptyState.push (t := .mem (.array (.prim .uint))) (some emptyRef))
        (Problem.callPre Group08SourceValidation.Calldata [(Var.user "b", .mem (.array (.prim .uint)))]
          false [] false [(Var.user "b", 0, 255, none)] true) →
      holds (emptyState.push (t := .mem (.array (.prim .uint))) (some emptyRef))
        (Fml.wt Group08SourceValidation.Calldata) →
      holds (emptyState.push (t := .mem (.array (.prim .uint))) (some emptyRef))
        (.modal .diamond Group08SourceValidation.Calldata.sliceHashed .nil .tt) :=
    h.fmlValid emptyState (some emptyRef)
  have href : holds (emptyState.push (t := .mem (.array (.prim .uint))) (some emptyRef))
      (Fml.refInputs Group08SourceValidation.Calldata [.mem (.array (.prim .uint))]) := by
    change Upd.afterT .diamond _ _ _
    rw [Upd.afterT_applyV]
    intro _ _ _
    trivial
  have hpre : holds (emptyState.push (t := .mem (.array (.prim .uint))) (some emptyRef))
      (Problem.callPre Group08SourceValidation.Calldata [(Var.user "b", .mem (.array (.prim .uint)))]
        false [] false [(Var.user "b", 0, 255, none)] true) := by
    constructor
    · apply Fml.eval3_tt (dom := Tools.poolDom [])
      decide +kernel
    · simp only [Fml.conj, holds]
      intro i hi
      have nonneg : 0 ≤ i.val := (of_decide_eq_true i.property).1
      have hn : ¬ i.val < 0 := by omega
      conv at hi =>
        lhs
        tactic =>
          exact Tm.denote_eval (C := Group08SourceValidation.Calldata) (s := .val .bool)
            ((emptyState.push (t := .mem (.array (.prim .uint))) (some emptyRef)).push (t := .val .uint) i) _ false (by
            rw [Tm.eval_eq_evalM]
            simp only [Tm.evalM, Op2.eval_eq_evalM, Op2.evalM, Op0.eval_eq_evalM, Op0.evalM]
            simp only [emptyState, State.push, TEnv.get, State.glob, State.memT,
              HRef.ofId?, Heap.lenU, Heap.len, Heap.get, MObj.elems]
            change (some (decide (i.val < 0)) : Option Bool) = some false
            simp only [hn, decide_false])
      change (some false : Option Bool) = some true at hi
      contradiction
  have hwt : holds (emptyState.push (t := .mem (.array (.prim .uint))) (some emptyRef)) (Fml.wt Group08SourceValidation.Calldata) := by
    apply Fml.eval3_tt (dom := Tools.poolDom [])
    decide +kernel
  have bad : holds (emptyState.push (t := .mem (.array (.prim .uint))) (some emptyRef))
      (.modal .diamond Group08SourceValidation.Calldata.sliceHashed .nil .tt) := hx href hpre hwt
  have hbad : ¬ holds (emptyState.push (t := .mem (.array (.prim .uint))) (some emptyRef))
      (.modal .diamond Group08SourceValidation.Calldata.sliceHashed .nil .tt) := by
    apply Fml.eval3_ff (dom := Tools.poolDom [])
    decide +kernel
  exact hbad bad


/-- The initialized short input reaches a real revert, not fuel exhaustion. -/
theorem sliceHashed_empty_reverts :
    (match Prog.runFramesF 32
        (emptyState.push (t := .mem (.array (.prim .uint))) (some emptyRef))
        Group08SourceValidation.Calldata.sliceHashed .nil with
      | .error .revert => true
      | _ => false) = true := by
  decide +kernel

private def zeroBytesState (n : Nat) (hn : n < 2 ^ 256) :
    State Group08SourceValidation.Calldata [.mem (.array (.prim .uint))] :=
  { storage := Storage.init Group08SourceValidation.Calldata,
    H := [.array (.prim .uint)],
    heap := (⟨List.replicate n (PrimTy.ofIntD .uint 0), by simpa only [List.length_replicate] using hn⟩, ()),
    env := (some ⟨0, rfl⟩, ()) }

/-- At the exact slice start, the concrete typed run returns normally. -/
theorem sliceHashed_at_start_returns :
    (Prog.runFramesF 32 (zeroBytesState 4 (by decide))
      Group08SourceValidation.Calldata.sliceHashed .nil).toOption.isSome = true := by
  decide +kernel

/-- A one-byte copy also returns normally; no exhaustion is accepted here. -/
theorem sliceHashed_one_byte_returns :
    (Prog.runFramesF 32 (zeroBytesState 5 (by decide))
      Group08SourceValidation.Calldata.sliceHashed .nil).toOption.isSome = true := by
  decide +kernel

#print axioms sliceHashed_empty_reverts
#print axioms sliceHashed_notDerivable
#print axioms sliceHashed_at_start_returns
#print axioms sliceHashed_one_byte_returns
end Solidity.Tests.Upstream.DeclarationSourceValidation
