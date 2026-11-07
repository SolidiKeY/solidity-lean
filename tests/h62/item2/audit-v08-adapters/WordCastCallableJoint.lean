import Solidity.Lowering.V08.WordCastCallable

/-! Guards cast-call witnesses with separately feasible body/read/alias models,
or conflation of a RAW signed caller write with its converted unsigned return.
Existing populated callers and IntegerLocalFamily are reused unchanged. This
is a cast-argument/callable component, not target-callee, ABI, heap/World/frame
compiler correspondence, SourceSpec admission or the canonical H68 bridge. -/
namespace H62.AuditV08Adapters.WordCastCallableJoint
open Solidity Source
open Solidity.Lowering.V07 Solidity.Lowering.V08
open WordCastCallable.Controls

/-- The four public transport premise groups plus the fixture old-value range
share one selected global, signed caller family (including alias reflection),
range proofs and concrete RHS read. The old range is construction data, not
a new restriction on the original public theorem. -/
def Joint {C : Contract} (base : State C []) (p : Roadmap.Pipeline)
    (old x : Int) (ho : range old) (hx : range x) : Prop :=
  IntegerCallable.Inputs (ScalarCallableTransport.global p) ScalarCallableTransport.frame
    ScalarCallableTransport.declaration Source.IntTy.u256 ∧
  IntegerLocalFamily t si ti (locals old x ho hx) (target base old x ho hx).env ∧
  range old ∧ range x ∧ (locals old x ho hx).get (si true) = .int x hx

theorem joint {C : Contract} (base : State C []) (p : Roadmap.Pipeline)
    (old x : Int) (ho : range old) (hx : range x) : Joint base p old x ho hx :=
  ⟨AssignedIntegerCallable.unsigned_inputs p, initial_family base old x ho hx, ho, hx, rfl⟩

/-- The target carrier and signed range are actually inhabited together. -/
theorem inhabited (p : Roadmap.Pipeline) :
    ∃ (base : State ConstructorScalarTransport.Cell []) (ho : range 0) (hx : range (-1)),
      Joint base p 0 (-1) ho hx :=
  ⟨ConstructorScalarTransport.entered, by decide, by decide, joint _ p _ _ _ _⟩

/-- Full original transport, including the converted result relation omitted
from the smaller production client projection. No execution is assumed. -/
theorem actual {C : Contract} (base : State C []) (p : Roadmap.Pipeline) (extra : Nat)
    (bytes : Roadmap.Bytes) (old x : Int) (ho : range old) (hx : range x) :
    (Source.evalE (ScalarCallableTransport.global p) ScalarCallableTransport.frame (extra+14)
      (expression p)).run (locals old x ho hx,ScalarCallableTransport.populated bytes) =
      (.ok (.val (Source.intWrap Source.IntTy.u256 x)),
        ((locals old x ho hx).set (si false) (.int x hx),ScalarCallableTransport.populated bytes)) ∧
    (WordCasts.assignedToUint (ti false) (ti true)).run (target base old x ho hx) =
      .ok (⟨(target base old x ho hx).setLocal (ti false) (integerValue t x hx),List.prefix_refl _⟩,
        .prim (integerValue Source.IntTy.u256 (Source.IntTy.u256.wrap x) (Source.IntTy.u256.wrap_mem x))) ∧
    IntValueRel Source.IntTy.u256 (Source.intWrap Source.IntTy.u256 x : Source.Val fixtureEnv.layout _)
      (integerValue Source.IntTy.u256 (Source.IntTy.u256.wrap x) (Source.IntTy.u256.wrap_mem x)) ∧
    IntegerLocalFamily t si ti ((locals old x ho hx).set (si false) (.int x hx))
      ((target base old x ho hx).setLocal (ti false) (integerValue t x hx)).env :=
  WordCastCallable.transport (ScalarCallableTransport.global p) ScalarCallableTransport.frame
    ScalarCallableTransport.declaration (AssignedIntegerCallable.unsigned_inputs p) extra
    (locals old x ho hx) (ScalarCallableTransport.populated bytes) (target base old x ho hx)
    si ti (initial_family base old x ho hx) false true x hx rfl

/-- A cast's post-write relation cannot use the stale signed source snapshot. -/
theorem stale_caller_refused {C : Contract} (base : State C []) :
    ¬ IntegerLocalFamily t si ti (locals 0 (-1) (by decide) (by decide))
      ((target base 0 (-1) (by decide) (by decide)).setLocal (ti false)
        (integerValue t (-1) (by decide))).env := wrong_snapshot base

/-- For -1 the caller contains raw -1, but the returned unsigned value is max.
The projections here test this distinction; actual above retains full runs. -/
theorem raw_return_separate {C : Contract} (base : State C []) :
    ((WordCasts.assignedToUint (ti false) (ti true)).run
      (target base 0 (-1) (by decide) (by decide))).toOption.map
      (fun out => PrimTy.num? (TEnv.get (ti false) out.1.st.env)) ≠
    ((WordCasts.assignedToUint (ti false) (ti true)).run
      (target base 0 (-1) (by decide) (by decide))).toOption.map
      (fun out => match out.2 with | .prim value => PrimTy.num? value) := raw_return_distinct base

#print axioms inhabited
#print axioms actual
#print axioms stale_caller_refused
#print axioms raw_return_separate
end H62.AuditV08Adapters.WordCastCallableJoint
