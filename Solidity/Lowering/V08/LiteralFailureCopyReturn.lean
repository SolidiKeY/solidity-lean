import Solidity.Lowering.V08.LiteralFailureCopySequence
import Solidity.Lowering.V08.LiteralFailureReturnSlots

/-! Actual tuple returns after supported local conversions. The argument run,
return-slot overwrite, extraction and encoding are derived together; no target
caller frame, source admission or external-call/world relation is assumed. -/
namespace Solidity.Lowering.V08.LiteralFailureCopyReturn
open Solidity Source
open LiteralFailureCopySequence (Plan)

theorem return_run {E : Env} {Γ types shapes copies}
 {arguments : RConvArgs E (types.reverseAux Γ) types} {encoded : AbiEntry.Vals shapes}
 (G : Glob E) (F : Fr) (extra : Nat) (old : Source.Vals E.layout types)
 (parameters : Locals E.layout Γ) (state : St E)
 (plan : Plan F state (old.onto parameters) arguments encoded copies) :
 ∃ (values : Source.Vals E.layout types) (final : St E),
 (execS G F (types.length+extra+4) Γ.length none (.retTuple arguments :
 RStmt E types false .body (types.reverseAux Γ) (types.reverseAux Γ)) (old.onto parameters)).run (L0 E,state)=
 (.ok (.ret (values.onto parameters)),(L0 E,final)) ∧
 retVals (values.onto parameters) 0 types=.ok values.toR ∧
 (encodeVals F (types.length+extra+3) false values.toR : EM E [] _).run (L0 E,final)=
 (.ok (AbiEntry.encodeArgs encoded),(L0 E,final)) ∧
 LiteralFailureConvertedFields.Keeps F state final ∧
 final.heap.next=state.heap.next+copies ∧ final={state with heap:=final.heap} := by
 rcases LiteralFailureCopySequence.run G F extra (old.onto parameters) state plan with
  ⟨values,final,actual,fields,kept,next,nonheap⟩
 refine ⟨values,final,?_,LiteralFailureReturnSlots.extraction values parameters,?_,kept,next,nonheap⟩
 · exact LiteralFailureReturnSlots.tuple_statement G F (types.length+extra+3) old values
    parameters (old.onto parameters) arguments state final actual
 · exact LiteralFailureLocatedFields.encoding_run F _ (L0 E) final fields

end Solidity.Lowering.V08.LiteralFailureCopyReturn
