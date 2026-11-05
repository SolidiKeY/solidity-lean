import Solidity.Lowering.V08.LiteralFailureCopySequence

/-! Actual standard ABI expression execution after supported local conversions.
The input plan contains no execution result. Copies and the final packet object
are derived separately from the existing Source evaluator and encoder. -/
namespace Solidity.Lowering.V08.LiteralFailureCopyEncoding
open Solidity Source
open LiteralFailureLocatedFields (Fields)
open LiteralFailureConvertedFields (Keeps)
open LiteralFailureCopySequence (Plan)

/-- Existing converted arguments expressed with explicit intrinsic conversions. -/
def expressions {E : Env} {Γ types} : RConvArgs E Γ types → RArgs E Γ types
 | .nil => .nil
 | .cons expression conversion tail => .cons (.conv expression (.inl conversion)) (expressions tail)

theorem arguments_run {E : Env} {Γ types shapes copies} {arguments : RConvArgs E Γ types}
 {encoded : AbiEntry.Vals shapes} (G : Glob E) (F : Fr) (extra : Nat)
 (locals : Locals E.layout Γ) (state : St E) (plan : Plan F state locals arguments encoded copies) :
 ∃ (values : Source.Vals E.layout types) (final : St E),
 (evalArgs G F (types.length+extra+4) (expressions arguments)).run (locals,state)=
 (.ok values.toR,(locals,final)) ∧ Fields F final values encoded ∧ Keeps F state final ∧
 final.heap.next=state.heap.next+copies ∧ final={state with heap:=final.heap} := by
 induction types generalizing shapes state copies with
 | nil =>
  cases plan
  refine ⟨.nil,state,rfl,.nil,?_,by omega,rfl⟩
  intro types shapes values encoded fields
  exact fields
 | cons type types ih =>
  cases plan with
  | cons index conversion head tail =>
   rcases LiteralFailureCopySequence.step_run F (types.length+extra+3) state head with
    ⟨value,middle,headRun,headField,headKept,headNext,headNonheap⟩
   rcases ih middle (LiteralFailureCopySequence.plan_transport F state middle headKept tail) with
    ⟨values,final,tailRun,tailFields,tailKept,tailNext,tailNonheap⟩
   refine ⟨.cons value values,final,?_,?_,?_,by omega,?_⟩
   · simp only [List.length_cons,expressions]
     rw [evalArgs]
     have fuel : types.length+1+extra+3=types.length+extra+4 := by omega
     simp only [fuel]
     rw [evalE]
     have inner : types.length+extra+3=(types.length+extra+2)+1 := by omega
     rw [inner,evalE]
     simp only [EM.locals,bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,
      ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,
      liftM,monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map]
     dsimp only [ExceptT.run] at headRun tailRun
     rw [← inner,headRun]
     simp only [ExceptT.bindCont,StateT.bind]
     rw [tailRun]
     rfl
   · exact .cons (LiteralFailureConvertedFields.kept_head F middle final tailKept headField) tailFields
   · intro types shapes values encoded fields
     exact tailKept values encoded (headKept values encoded fields)
   · exact tailNonheap.trans (congrArg (fun source=>{source with heap:=final.heap}) headNonheap)

/-- The actual encoder runs after all copies, then allocates one packet object.
The count is Source heap objects, not physical bytes or gas. -/
theorem expression_run {E : Env} {Γ types shapes copies} {arguments : RConvArgs E Γ types}
 {encoded : AbiEntry.Vals shapes} (G : Glob E) (F : Fr) (extra : Nat)
 (locals : Locals E.layout Γ) (state : St E) (plan : Plan F state locals arguments encoded copies) :
 ∃ middle : St E,
 (evalE G F (types.length+extra+5) (.abiEncode .encode (expressions arguments))).run (locals,state)=
 (.ok (.val (.memRef rfl middle.heap.next)),
  (locals,SourceKeccak.afterLiteral middle (AbiEntry.encodeArgs encoded))) ∧
 Keeps F state (SourceKeccak.afterLiteral middle (AbiEntry.encodeArgs encoded)) ∧
 middle.heap.next=state.heap.next+copies ∧
 (SourceKeccak.afterLiteral middle (AbiEntry.encodeArgs encoded)).heap.next=state.heap.next+copies+1 ∧
 SourceKeccak.afterLiteral middle (AbiEntry.encodeArgs encoded)=
  {state with heap:=(SourceKeccak.afterLiteral middle (AbiEntry.encodeArgs encoded)).heap} := by
 rcases arguments_run G F extra locals state plan with ⟨values,middle,actual,fields,kept,next,nonheap⟩
 refine ⟨middle,?_,?_,next,?_,?_⟩
 · exact SourceAbi.execute G F (types.length+extra+4) false (expressions arguments)
    locals locals locals state middle middle values.toR _ actual
    (LiteralFailureLocatedFields.encoding_run F _ locals middle fields)
 · intro types shapes values encoded fields
   exact LiteralFailureLocatedFields.fields_after F middle _ (kept values encoded fields)
 · change middle.heap.next+1=state.heap.next+copies+1
   omega
 · exact congrArg (fun source=>{source with heap:=(SourceKeccak.afterLiteral middle (AbiEntry.encodeArgs encoded)).heap}) nonheap

end Solidity.Lowering.V08.LiteralFailureCopyEncoding
