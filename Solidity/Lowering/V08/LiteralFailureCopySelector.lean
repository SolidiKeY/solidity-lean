import Solidity.Lowering.V08.LiteralFailureCopyEncoding
import Solidity.Lowering.V08.LiteralFailureSelectorBytes

/-! Actual selector-prefixed standard encoding after supported local conversions.
The selector is a typed caller local; no dispatch or invocation provenance is
inferred from its bytes. -/
namespace Solidity.Lowering.V08.LiteralFailureCopySelector
open Solidity Source
open LiteralFailureCopySequence (Plan)
open LiteralFailureLocatedFields (Fields)
open LiteralFailureConvertedFields (Keeps)
abbrev Selector := LiteralFailureSelectorBytes.Selector

theorem values_injective {D : Layout} {types} {left right : Source.Vals D types}
 (same : left.toR=right.toR) : left=right := by
 induction left with
 | nil => cases right; rfl
 | cons value values ih =>
  cases right with
  | cons other rest =>
   simp only [Source.Vals.toR] at same
   injection same with _ _ head tail
   have valueEq := RVal.val.inj head
   rw [valueEq,ih tail]

theorem arguments_run {E : Env} {Γ types shapes copies} {arguments : RConvArgs E Γ types}
 {encoded : AbiEntry.Vals shapes} (G : Glob E) (F : Fr) (extra : Nat)
 (index : Source.Idx Γ Selector) (locals : Locals E.layout Γ) (state : St E)
 (plan : Plan F state locals arguments encoded copies) :
 ∃ (values : Source.Vals E.layout types) (middle : St E),
 (evalArgs G F (types.length+extra+5) (.cons (.local index) (LiteralFailureCopyEncoding.expressions arguments))).run
 (locals,state)=(.ok (.cons (.val (locals.get index)) values.toR),(locals,middle)) ∧
 Fields F middle values encoded ∧ Keeps F state middle ∧
 middle.heap.next=state.heap.next+copies ∧ middle={state with heap:=middle.heap} := by
 rcases LiteralFailureCopyEncoding.arguments_run G F extra locals state plan with
  ⟨values,middle,actual,fields,kept,next,nonheap⟩
 refine ⟨values,middle,?_,fields,kept,next,nonheap⟩
 rw [evalArgs]
 simp only [evalE,EM.locals,bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,
  ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,
  liftM,monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map]
 dsimp only [ExceptT.run] at actual
 rw [actual]
 rfl

theorem expression_run {E : Env} {Γ types shapes copies} {arguments : RConvArgs E Γ types}
 {encoded : AbiEntry.Vals shapes} (G : Glob E) (F : Fr) (extra : Nat)
 (index : Source.Idx Γ Selector) (locals : Locals E.layout Γ) (state : St E)
 (plan : Plan F state locals arguments encoded copies) :
 ∃ middle : St E,
 (evalE G F (types.length+extra+6) (.abiEncode .encodeWithSelector
  (.cons (.local index) (LiteralFailureCopyEncoding.expressions arguments)))).run (locals,state)=
 (.ok (.val (.memRef rfl middle.heap.next)),(locals,SourceKeccak.afterLiteral middle
  ((locals.get index).bytesOf++AbiEntry.encodeArgs encoded))) ∧
 Keeps F state (SourceKeccak.afterLiteral middle ((locals.get index).bytesOf++AbiEntry.encodeArgs encoded)) ∧
 middle.heap.next=state.heap.next+copies ∧
 (SourceKeccak.afterLiteral middle ((locals.get index).bytesOf++AbiEntry.encodeArgs encoded)).heap.next=state.heap.next+copies+1 ∧
 SourceKeccak.afterLiteral middle ((locals.get index).bytesOf++AbiEntry.encodeArgs encoded)=
 {state with heap:=(SourceKeccak.afterLiteral middle ((locals.get index).bytesOf++AbiEntry.encodeArgs encoded)).heap} := by
 rcases arguments_run G F extra index locals state plan with ⟨values,middle,actual,fields,kept,next,nonheap⟩
 refine ⟨middle,?_,?_,next,?_,?_⟩
 · exact SourceAbi.selector_execute G F (types.length+extra+5) _ locals locals locals locals
    state middle middle middle (.val (locals.get index)) values.toR (locals.get index) _ actual
    (LiteralFailureSelectorBytes.conversion_run F _ _ locals middle)
    (LiteralFailureLocatedFields.encoding_run F _ locals middle fields)
 · intro types shapes values encoded fields
   exact LiteralFailureLocatedFields.fields_after F middle _ (kept values encoded fields)
 · change middle.heap.next+1=state.heap.next+copies+1
   omega
 · exact congrArg (fun source=>{source with heap:=(SourceKeccak.afterLiteral middle
    ((locals.get index).bytesOf++AbiEntry.encodeArgs encoded)).heap}) nonheap

end Solidity.Lowering.V08.LiteralFailureCopySelector
