import Solidity.Lowering.V08.SourceCallableControls

/-! Regression: separately inhabited body/frame/execution facts must refer to
one actual Source call and its reached state. The existing resolved program
supplies all completion premises jointly, for every pipeline/extra horizon and
both argument values. The full heap effect is retained; this manually supplied
Source program is not a parser/body/admission or target compiler certificate. -/
namespace H62.AuditV08Adapters.SourceCallableJoint
open Solidity Source
open Solidity.Lowering.V08
open SourceCallableControls

/-- Original completion premises plus explicit argument-to-frame identity. -/
def Joint (pipeline : Roadmap.Pipeline) (extra : Nat) (first second : Bool) : Prop :=
  (global pipeline).prog.body ((global pipeline).dispatchFn callerFrame.contract functionDecl) =
    some bodyFirst ∧
  ([.bool] : List STy).reverseAux (([.bool,.bool] : List STy).reverseAux []) = bodyFirst.locals ∧
  (Source.Vals.cons (.bool false) .nil).onto ((params first second).onto (Source.L0 E)) =
    initial first second ∧
  (Source.zeroVals (extra+24) [.bool] : Source.EM E [] _).run (Source.L0 E,populated) =
    (.ok (.cons (.bool false) .nil),(Source.L0 E,populated)) ∧
  (Source.runMods (global pipeline) {callerFrame with checked:=true} (extra+24)
    bodyFirst bodyFirst.mods (initial first second)).run (Source.L0 E,populated) =
    (.ok (returned first second),(Source.L0 E,SourceKeccak.afterLiteral populated binary)) ∧
  Source.retVals (returned first second) 0 [.bool] =
    .ok (.cons (.val (.bool first)) .nil)

theorem joint (pipeline : Roadmap.Pipeline) (extra : Nat) (first second : Bool) :
    Joint pipeline extra first second :=
  ⟨selected pipeline, rfl, reached_frame first second, zero_returns extra,
    body_execute pipeline extra first second, rfl⟩

/-- Exact original full Source result/state, using every joint premise. -/
theorem actual (pipeline : Roadmap.Pipeline) (extra : Nat) (first second : Bool) :
    (Source.callInternal (global pipeline) callerFrame (extra+25) functionDecl
      (params first second) [.bool]).run (Source.L0 E,populated) =
    (.ok (.val (.bool first)),(Source.L0 E,SourceKeccak.afterLiteral populated binary)) := by
  have h := joint pipeline extra first second
  exact SourceCallable.complete (global pipeline) callerFrame (extra+24) functionDecl
    (params first second) bodyFirst h.1 (.cons (.bool false) .nil) h.2.1
    (returned first second) (.cons (.val (.bool first)) .nil) populated populated _
    h.2.2.2.1 (by simpa only [h.2.2.1] using h.2.2.2.2.1) h.2.2.2.2.2

/-- Returning the right value cannot justify silently discarding the heap effect. -/
theorem stale_state_refused (pipeline : Roadmap.Pipeline) (extra : Nat) (first second : Bool) :
    (Source.callInternal (global pipeline) callerFrame (extra+25) functionDecl
      (params first second) [.bool]).run (Source.L0 E,populated) ≠
    (.ok (.val (.bool first)),(Source.L0 E,populated)) := by
  rw [actual]
  intro same
  have heapSame := congrArg (fun result => result.2.2.heap.next) same
  change 2 = 1 at heapSame
  cases heapSame

#print axioms joint
#print axioms actual
#print axioms stale_state_refused
end H62.AuditV08Adapters.SourceCallableJoint
