import Solidity.Lowering.Readonly.SourceDispatchEffects

/-! Additive refutations of frozen dispatch-cut hypotheses. No interface edit,
new premise, axiom, or successful witness is supplied for an impossible cut. -/
namespace Solidity.H62.ReadonlyAudit.ImpossibleDispatch
open Solidity.Source Solidity.Roadmap
variable {E : Env}

theorem getter_empty_infeasible (G : Glob E) (F : Fr) (input : Bytes)
    (d : Decl) (ps : List STy) (r : STy) (empty : input.isEmpty = true)
    (selected : G.pickGetter F input = some (d, ps, r)) : False := by
  unfold Glob.pickGetter at selected
  have picked : (!input.isEmpty && G.selector (sigOf E.layout d.name ps) == input.take 4) = true :=
    @List.find?_some (Decl × List STy × STy)
      (fun (d, ps, _) => !input.isEmpty && G.selector (sigOf E.layout d.name ps) == input.take 4)
      (d, ps, r) (E.getters F.contract) selected
  simp only [empty, Bool.not_true, Bool.false_and, Bool.false_eq_true] at picked

theorem function_empty_infeasible (G : Glob E) (F : Fr) (input : Bytes)
    (d : Decl) (empty : input.isEmpty = true)
    (selected : G.pickFn F input = some d) : False := by
  have nil : input = [] := List.isEmpty_iff.mp empty
  subst input
  unfold Glob.pickFn at selected
  have picked : ((G.prog.body (G.dispatchFn F.contract d)).isSome &&
      match d.fnSig E with
      | some (ps, _) => G.selector (sigOf E.layout d.name ps) == ([] : Bytes).take 4
      | none => false) = true :=
    @List.find?_some Decl
      (fun d => (G.prog.body (G.dispatchFn F.contract d)).isSome && match d.fnSig E with
        | some (ps, _) => G.selector (sigOf E.layout d.name ps) == ([] : Bytes).take 4
        | none => false) d (E.exposed F.contract) selected
  have selectorTest : (match d.fnSig E with
      | some (ps, _) => G.selector (sigOf E.layout d.name ps) == ([] : Bytes).take 4
      | none => false) = true := (Bool.and_eq_true_iff.mp picked).2
  cases sig : d.fnSig E with
  | none => simp only [sig, Bool.false_eq_true] at selectorTest
  | some pair =>
    rcases pair with ⟨ps, rs⟩
    have eq : G.selector (sigOf E.layout d.name ps) = [] := by
      simpa only [sig, List.take_nil, beq_iff_eq] using selectorTest
    have length : (G.selector (sigOf E.layout d.name ps)).length = ([] : Bytes).length :=
      congrArg (fun bytes : Bytes => bytes.length) eq
    simp only [Glob.selector, List.length_take, wordBytes_length, List.length_nil] at length
    change 4 = 0 at length
    exact (by decide : (4 : Nat) ≠ 0) length

#print axioms getter_empty_infeasible
#print axioms function_empty_infeasible
end Solidity.H62.ReadonlyAudit.ImpossibleDispatch
