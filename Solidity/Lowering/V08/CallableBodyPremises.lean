import Solidity.Lowering.V08.SourceCallable
import Solidity.Semantics.ContractWorld

/-! Kernel-checked relative G20 body-phase contract: fields are
explicit producer duties, not instances, axioms or whole-call preservation.
Proposed producer routing: V07/V09 body/local/layout compilation; V12 the separate
runtime-frame bridge. No P8 admission, frame or bytecode adequacy is inferred. -/
namespace Solidity.Lowering.V08.CallableBodyPremises
open Solidity Source ContractWorld

structure Inputs {E : Source.Env} {C : Contract} {α : Type}
    {ps rs : List STy} (global : Glob E) (frame : Fr) (horizon : Nat)
    (declaration : Decl) (values : Source.Vals E.layout ps)
    (body : RBody E) (entry : Entry C α) (caller : State C [])
    (state initialized final : Source.St E)
    (relation : (Δ : Ctx) → Source.St E → State C Δ → Prop)
    (resultRelation : RVal E.layout (STy.ret rs) → α → Prop) where
  selected : global.prog.body (global.dispatchFn frame.contract declaration) = some body
  zero : Source.Vals E.layout rs
  fits : rs.reverseAux (ps.reverseAux []) = body.locals
  returned : Source.Locals E.layout body.locals
  outputs : RVals E.layout rs
  initialization : (Source.zeroVals horizon rs : Source.EM E [] _).run (Source.L0 E,state) =
    (.ok zero,(Source.L0 E,initialized))
  /-- V07/V09: actual Source body phase; not an assumed callInternal run. -/
  sourceBody : (Source.runMods global {frame with checked := true} horizon body body.mods
    (fits ▸ zero.onto (values.onto (Source.L0 E)))).run (Source.L0 E,initialized) =
    (.ok returned,(Source.L0 E,final))
  extraction : Source.retVals returned 0 rs = .ok outputs
  targetOut : Out C caller.H entry.locals
  /-- V07/V09 body compiler duty, before native result extraction. -/
  targetBody : entry.body.run caller = .ok targetOut
  /-- Unresolved cross-language body post-state preservation duty, assumed
  here rather than derived from initial alignment or compiler selection. -/
  bodyRelated : relation entry.locals final targetOut.st
  value : α
  targetResult : entry.result targetOut.st = .ok value
  /-- Unresolved result preservation duty; not a PassCorrect certificate
  or full-session semantics. -/
  resultRelated : resultRelation (Source.mkRet rs outputs) value

/-- Local body/result phases derive both actual callable boundaries. Every
pending compilation/relation obligation remains visible in Inputs. -/
theorem complete {E : Source.Env} {C : Contract} {α : Type} {ps rs : List STy}
    {global : Glob E} {frame : Fr} {horizon : Nat} {declaration : Decl}
    {values : Source.Vals E.layout ps} {body : RBody E} {entry : Entry C α}
    {caller : State C []} {state initialized final : Source.St E}
    {relation : (Δ : Ctx) → Source.St E → State C Δ → Prop}
    {resultRelation : RVal E.layout (STy.ret rs) → α → Prop}
    (p : Inputs global frame horizon declaration values body entry caller state initialized final
      relation resultRelation) :
    (Source.callInternal global frame (horizon+1) declaration values rs).run (Source.L0 E,state) =
      (.ok (Source.mkRet rs p.outputs),(Source.L0 E,final)) ∧
    (do
      let out ← entry.body.run caller
      let value ← entry.result out.st
      pure (out,value)) = (.ok (p.targetOut,p.value) : TRes (Out C caller.H entry.locals × α)) ∧
    relation entry.locals final p.targetOut.st ∧
    resultRelation (Source.mkRet rs p.outputs) p.value := by
  refine ⟨?_,?_,p.bodyRelated,p.resultRelated⟩
  · exact SourceCallable.complete global frame horizon declaration values body p.selected p.zero
      p.fits p.returned p.outputs state initialized final p.initialization p.sourceBody p.extraction
  · first | simp only [p.targetBody,p.targetResult,bind,Except.bind,pure,Except.pure] | rfl

end Solidity.Lowering.V08.CallableBodyPremises

/-- info: 'Solidity.Lowering.V08.CallableBodyPremises.Inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.CallableBodyPremises.Inputs
/-- info: 'Solidity.Lowering.V08.CallableBodyPremises.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.CallableBodyPremises.complete
