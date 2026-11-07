import Solidity.Lowering.V08.TupleCallable

/-! Guards tuple-call witnesses assembled from different caller snapshots or
lost result ordering/status. Existing signed-int8/uint256 fixtures realize all
selection/range/read premises together; the actual observation retains the full
caller and BOTH outer body and inner result statuses. This is not ABI tuple
encoding, external-call semantics or canonical body/frame/admission adequacy. -/
namespace H62.AuditV08Adapters.TupleCallableJoint
open Solidity Source
open Solidity.Lowering.V07 Solidity.Lowering.V08
open TupleCallable

/-- Seven premise groups of the SAME public transport instance, with repeated
x/y, range proofs, selected global and entire target caller throughout. -/
def Joint {C : Contract} (base : State C []) (p : Roadmap.Pipeline)
    (x y : Int) (hx : leftRange x) (hy : rightRange y) : Prop :=
  (global p).prog.body ((global p).dispatchFn frame.contract declaration) = some sourceBody ∧
  leftRange x ∧ rightRange y ∧
  (sourceCaller x y hx hy).get (.here : Source.Idx [L,R,.bool,L] L) = left x hx ∧
  (sourceCaller x y hx hy).get (.there .here : Source.Idx [L,R,.bool,L] R) = right y hy ∧
  TEnv.get (.here : Idx [.val .int,.val .uint,.val .bool,.val .int] (.val .int))
    (targetCaller base x y hx hy).env = integerValue SignedCallableControls.t x hx ∧
  TEnv.get (.there .here : Idx [.val .int,.val .uint,.val .bool,.val .int] (.val .uint))
    (targetCaller base x y hx hy).env = integerValue Source.IntTy.u256 y hy

theorem joint {C : Contract} (base : State C []) (p : Roadmap.Pipeline)
    (x y : Int) (hx : leftRange x) (hy : rightRange y) : Joint base p x y hx hy :=
  ⟨rfl, hx, hy, rfl, rfl, rfl, rfl⟩

/-- The complete predicate has an actual entered caller and distinct signed
and unsigned values, not merely a conditional base-state inhabitant. -/
theorem inhabited (p : Roadmap.Pipeline) :
    ∃ (base : State ConstructorScalarTransport.Cell []) (x y : Int)
      (hx : leftRange x) (hy : rightRange y), Joint base p x y hx hy :=
  ⟨ConstructorScalarTransport.entered, -128, 7, by decide, by decide, joint _ p _ _ _ _⟩

/-- The full original four-conclusion transport, without assuming execution. -/
theorem actual {C : Contract} (base : State C []) (p : Roadmap.Pipeline)
    (extra : Nat) (bytes : Roadmap.Bytes) (x y : Int) (hx : leftRange x) (hy : rightRange y) :
    (Source.evalE (global p) frame (extra+33) (.call declaration signature
      (arguments .here (.there .here)))).run (sourceCaller x y hx hy,populated bytes) =
      (.ok (.tuple (outputs x y hx hy)),(sourceCaller x y hx hy,populated bytes)) ∧
    observeBody .here (.there .here) (targetCaller base x y hx hy) =
      .ok (targetCaller base x y hx hy,.ok (integerValue SignedCallableControls.t x hx,
        integerValue Source.IntTy.u256 y hy)) ∧
    IntValueRel SignedCallableControls.t (left x hx) (integerValue SignedCallableControls.t x hx) ∧
    IntValueRel Source.IntTy.u256 (right y hy) (integerValue Source.IntTy.u256 y hy) :=
  transport (global p) frame extra rfl .here (.there .here) (sourceCaller x y hx hy)
    (populated bytes) (targetCaller base x y hx hy) .here (.there .here) x y hx hy
    rfl rfl rfl rfl

/-- A tempting protected older target slot changes the actual observed value. -/
theorem older_slot_refused {C : Contract} (base : State C []) :
    observeBody .here (.there .here) (targetCaller base (-128) 7 (by decide) (by decide)) ≠
    observeBody (.there (.there (.there .here))) (.there .here)
      (targetCaller base (-128) 7 (by decide) (by decide)) :=
  wrong_target_slot base

/-- The numeric projection rejects reversed results; the main actual theorem
retains both full status levels rather than this control projection. -/
theorem reversed_result_refused :
    (observeBody .here (.there .here) (targetCaller ConstructorScalarTransport.entered (-128) 7
      (by decide) (by decide))).map
      (fun out => out.2.toOption.map (fun pair => (pair.1.1,pair.2.1))) ≠ .ok (some (7,-128)) :=
  wrong_result_order

/-- Zero horizon is an actual timeout on the SAME populated source model. -/
theorem timeout_actual (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global p) frame 0 (.call declaration signature
      (arguments .here (.there .here)))).run
      (sourceCaller (-128) 7 (by decide) (by decide),populated bytes) =
      (.error .timeout,(sourceCaller (-128) 7 (by decide) (by decide),populated bytes)) :=
  zero_horizon p bytes

#print axioms inhabited
#print axioms actual
#print axioms older_slot_refused
#print axioms reversed_result_refused
#print axioms timeout_actual
end H62.AuditV08Adapters.TupleCallableJoint
