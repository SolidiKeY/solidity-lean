import Solidity.Goals.PanicSource

/-! Pin of `panicSourceAssociation` (plan w3d-panic-dispatch) and checks of the panic dispatch
producers: the theorems hold at the knot's own record, and their axioms. -/

namespace Solidity.Goals

/--
info: proved Solidity.Goals.panicSourceAssociation ← Solidity.Correctness.Panic.source_association plan w3d-panic-dispatch
-/
#guard_msgs in
#roadmap_goal panicSourceAssociation

example : Solidity.Goals.panicSourceAssociation := Solidity.Correctness.Panic.source_association

/--
info: 'Solidity.Correctness.Panic.source_association' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Solidity.Correctness.Panic.source_association

end Solidity.Goals

namespace Solidity.Examples.Goals.PanicSource

open Solidity Solidity.Correctness.Panic

variable [FreshNames] (C : Contract)

/-- The public scalar producer, through its equation: the same fallback. -/
example (h ty : String) (args : List RawExpr) (res : Option (Var × PrimTy)) (resW : Nat)
    (resNew : Bool) (sc : ElabScope) (ps rs : List String)
    (internal : fnParts? ty = some (ps, rs, false)) :
    Post (fnDispatch C h ty args res resW resNew) sc fun P =>
      ∃ (P₀ : SProg C) (Γ : NCtx) (arms : List (DispatchArm C Γ.ctx)),
        P = P₀ ++ [.of Γ (DispatchArm.chain arms
          (if sc.selfFrame || sc.retainFailureData then
            .revertData [.bytes (Semantics.encodePanic 0x51)] else .revert))] :=
  fnDispatch_eq C h ty args res resW resNew ▸
    fnDispatchWith_fallback (panicProducerRec C ()) h ty args res resW resNew sc ps rs internal

/-- info: 'Solidity.Correctness.Panic.fnDispatchWith_fallback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fnDispatchWith_fallback

/-- info: 'Solidity.Correctness.Panic.fnTupleDispatchWith_fallback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fnTupleDispatchWith_fallback

/-- info: 'Solidity.Correctness.Panic.fnMemoryDispatchWith_fallback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fnMemoryDispatchWith_fallback

/-- info: 'Solidity.Correctness.Panic.trySelfBodyWith_instrumented' depends on axioms: [propext] -/
#guard_msgs in #print axioms trySelfBodyWith_instrumented

/-- info: 'Solidity.Correctness.Panic.receiveSelfBodyWith_plain' depends on axioms: [propext] -/
#guard_msgs in #print axioms receiveSelfBodyWith_plain

/-- info: 'Solidity.Correctness.Panic.dispatch_fallback_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dispatch_fallback_run

end Solidity.Examples.Goals.PanicSource
