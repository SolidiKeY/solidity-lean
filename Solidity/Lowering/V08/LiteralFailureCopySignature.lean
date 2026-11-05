import Solidity.Lowering.V08.LiteralFailureCopySelector
import Solidity.Lowering.V08.LiteralFailureSignatureBytes

/-! Signature memory is read after the actual converted argument run. Its old
alias is transported through derived copy effects, not assumed at the reached
state. No signature/declaration or same-invocation correspondence is inferred. -/
namespace Solidity.Lowering.V08.LiteralFailureCopySignature
open Solidity Source
open LiteralFailureCopySequence (Plan)
open LiteralFailureLocatedFields (Fields)
open LiteralFailureConvertedFields (Keeps)

theorem signature_kept {E : Env} {Γ} (F : Fr) (initial final : St E)
 (locals : Locals E.layout Γ) (index : Source.Idx Γ (.bytes .memory)) (signature : Roadmap.Bytes)
 (kept : Keeps F initial final)
 (memory : LiteralFailureDynamicListError.represented locals initial index signature) :
 LiteralFailureDynamicListError.represented locals final index signature := by
 obtain ⟨address,reference,heap⟩ := memory
 have fields : Fields F initial (.cons (.memRef rfl address : Source.Val E.layout (.bytes .memory)) .nil)
  (.cons (.bytes signature) .nil) := .cons (.known (.bytes address signature heap .nil)) .nil
 have reached := kept _ _ fields
 cases reached with
 | cons head tail =>
  cases head with
  | known field =>
   cases field with
   | bytes address signature heap rest => exact ⟨address,reference,heap⟩

theorem arguments_run {E : Env} {Γ σ types shapes copies} {arguments : RConvArgs E Γ types}
 {encoded : AbiEntry.Vals shapes} (G : Glob E) (F : Fr) (extra : Nat)
 (index : Source.Idx Γ σ) (locals : Locals E.layout Γ) (state : St E)
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
 (index : Source.Idx Γ (.bytes .memory)) (locals : Locals E.layout Γ) (state : St E)
 (signature : Roadmap.Bytes) (memory : LiteralFailureDynamicListError.represented locals state index signature)
 (plan : Plan F state locals arguments encoded copies) :
 ∃ middle : St E,
 (evalE G F (types.length+extra+6) (.abiEncode .encodeWithSignature
  (.cons (.local index) (LiteralFailureCopyEncoding.expressions arguments)))).run (locals,state)=
 (.ok (.val (.memRef rfl middle.heap.next)),(locals,SourceKeccak.afterLiteral middle
  ((wordBytes (G.fixed.hash signature)).take 4++AbiEntry.encodeArgs encoded))) ∧
 LiteralFailureDynamicListError.represented locals middle index signature ∧
 Keeps F state (SourceKeccak.afterLiteral middle ((wordBytes (G.fixed.hash signature)).take 4++AbiEntry.encodeArgs encoded)) ∧
 middle.heap.next=state.heap.next+copies ∧
 (SourceKeccak.afterLiteral middle ((wordBytes (G.fixed.hash signature)).take 4++AbiEntry.encodeArgs encoded)).heap.next=state.heap.next+copies+1 ∧
 SourceKeccak.afterLiteral middle ((wordBytes (G.fixed.hash signature)).take 4++AbiEntry.encodeArgs encoded)=
 {state with heap:=(SourceKeccak.afterLiteral middle ((wordBytes (G.fixed.hash signature)).take 4++AbiEntry.encodeArgs encoded)).heap} := by
 rcases arguments_run G F extra index locals state plan with ⟨values,middle,actual,fields,kept,next,nonheap⟩
 have preserved := signature_kept F state middle locals index signature kept memory
 refine ⟨middle,?_,preserved,?_,next,?_,?_⟩
 · exact SourceAbi.signature_execute G F (types.length+extra+5) _ locals locals locals locals
    state middle middle middle (.val (locals.get index)) values.toR signature _ actual
    (LiteralFailureSignatureBytes.signature_read F _ index signature locals locals middle preserved)
    (LiteralFailureLocatedFields.encoding_run F _ locals middle fields)
 · intro types shapes values encoded fields
   exact LiteralFailureLocatedFields.fields_after F middle _ (kept values encoded fields)
 · change middle.heap.next+1=state.heap.next+copies+1
   omega
 · exact congrArg (fun source=>{source with heap:=(SourceKeccak.afterLiteral middle
    ((wordBytes (G.fixed.hash signature)).take 4++AbiEntry.encodeArgs encoded)).heap}) nonheap

end Solidity.Lowering.V08.LiteralFailureCopySignature
