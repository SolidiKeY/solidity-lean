import Solidity.Lowering.V08.LiteralFailureStringConversion

/-! Evidence for actual converted local arguments with arbitrary interleaving
of identity reads and byte/string calldata copies. Both relations are Prop over
existing intrinsic syntax/values; neither stores a desired run or final state. -/
namespace Solidity.Lowering.V08.LiteralFailureCopySequence
open Solidity Source
open LiteralFailureLocatedFields (Head Fields)
open LiteralFailureConvertedFields (Keeps)

inductive Step {E : Env} {Γ : RCtx} (F : Fr) (state : St E) (locals : Locals E.layout Γ) :
 {σ τ : STy} → (index : Source.Idx Γ σ) → (conversion : σ.implicit E.isBase τ=true) →
 {shape : AbiEntry.Shape} → AbiEntry.Val shape → Nat → Prop
 | read {type shape encoded} (index : Source.Idx Γ type) (typed : type.implicit E.isBase type=true)
   (head : @Head E F state type (locals.get index) shape encoded) :
   Step F state locals index typed encoded 0
 | bytes (index : Source.Idx Γ (.bytes .calldata)) (off len : Nat)
   (present : locals.get index=.cdRef rfl off len) :
   @Step E Γ F state locals (.bytes .calldata) (.bytes .memory) index rfl .bytes
    (.bytes ((F.cd.drop off).take len)) 1
 | string (index : Source.Idx Γ (.string .calldata)) (off len : Nat)
   (present : locals.get index=.cdRef rfl off len) :
   @Step E Γ F state locals (.string .calldata) (.string .memory) index rfl .bytes
    (.bytes ((F.cd.drop off).take len)) 1

inductive Plan {E : Env} {Γ : RCtx} (F : Fr) (state : St E) (locals : Locals E.layout Γ) :
 {types : RCtx} → RConvArgs E Γ types → {shapes : List AbiEntry.Shape} → AbiEntry.Vals shapes → Nat → Prop
 | nil : Plan F state locals .nil .nil 0
 | cons {σ τ types arguments shape shapes encoded encodeds cost copies}
   (index : Source.Idx Γ σ) (conversion : σ.implicit E.isBase τ=true)
   (head : @Step E Γ F state locals σ τ index conversion shape encoded cost)
   (tail : @Plan E Γ F state locals types arguments shapes encodeds copies) :
   Plan F state locals (.cons (.local index) conversion arguments : RConvArgs E Γ (τ::types))
    (.cons encoded encodeds) (cost+copies)

theorem step_transport {E : Env} {Γ σ τ shape cost} {locals : Locals E.layout Γ}
 {index : Source.Idx Γ σ} {conversion : σ.implicit E.isBase τ=true} {encoded : AbiEntry.Val shape}
 (F : Fr) (initial final : St E) (kept : Keeps F initial final)
 (step : Step F initial locals index conversion encoded cost) : Step F final locals index conversion encoded cost := by
 cases step with
 | read index typed head => exact .read index typed (LiteralFailureConvertedFields.kept_head F initial final kept head)
 | bytes index off len present => exact .bytes index off len present
 | string index off len present => exact .string index off len present

theorem plan_transport {E : Env} {Γ types shapes copies} {locals : Locals E.layout Γ}
 {arguments : RConvArgs E Γ types} {encoded : AbiEntry.Vals shapes}
 (F : Fr) (initial final : St E) (kept : Keeps F initial final)
 (plan : Plan F initial locals arguments encoded copies) : Plan F final locals arguments encoded copies := by
 induction plan with
 | nil => exact .nil
 | cons index conversion head tail ih => exact .cons index conversion (step_transport F initial final kept head) ih

theorem step_run {E : Env} {Γ σ τ shape cost} {locals : Locals E.layout Γ}
 {index : Source.Idx Γ σ} {conversion : σ.implicit E.isBase τ=true} {encoded : AbiEntry.Val shape}
 (F : Fr) (fuel : Nat) (state : St E) (step : Step F state locals index conversion encoded cost) :
 ∃ (value : Source.Val E.layout τ) (middle : St E),
 (convRV F fuel τ (.val (locals.get index)) : EM E Γ _).run (locals,state)=(.ok (.val value),(locals,middle)) ∧
 Head F middle value encoded ∧ Keeps F state middle ∧ middle.heap.next=state.heap.next+cost ∧
 middle={state with heap:=middle.heap} := by
 cases step with
 | read index typed head =>
  refine ⟨locals.get index,state,?_,head,?_,by omega,rfl⟩
  · simp only [convRV,↓reduceDIte,pure,ExceptT.pure,ExceptT.run,ExceptT.mk,StateT.pure]
  · intro types shapes values encoded fields
    exact fields
 | bytes index off len present =>
  let bs := (F.cd.drop off).take len
  refine ⟨.memRef rfl state.heap.next,SourceKeccak.afterLiteral state bs,?_,?_,?_,rfl,rfl⟩
  · rw [present]
    exact LiteralFailureCalldataCopy.copy_run F fuel off len locals state
  · exact .known (.bytes state.heap.next bs (.inl (SourceKeccak.allocated state bs)) .nil)
  · intro types shapes values encoded fields
    exact LiteralFailureLocatedFields.fields_after F state bs fields
 | string index off len present =>
  let bs := (F.cd.drop off).take len
  refine ⟨.memRef rfl state.heap.next,LiteralFailureStringConversion.afterString state bs,?_,?_,?_,rfl,rfl⟩
  · rw [present]
    exact LiteralFailureStringConversion.copy_run F fuel off len locals state
  · exact .known (.string state.heap.next bs (LiteralFailureStringConversion.allocated state bs) .nil)
  · intro types shapes values encoded fields
    exact LiteralFailureStringConversion.fields_after F state ⟨.string .memory,.string bs⟩ fields

theorem run {E : Env} {Γ types shapes copies} {arguments : RConvArgs E Γ types}
 {encoded : AbiEntry.Vals shapes} (G : Glob E) (F : Fr) (extra : Nat)
 (locals : Locals E.layout Γ) (state : St E) (plan : Plan F state locals arguments encoded copies) :
 ∃ (values : Source.Vals E.layout types) (final : St E),
 (evalConvArgs G F (types.length+extra+3) arguments).run (locals,state)=(.ok values,(locals,final)) ∧
 Fields F final values encoded ∧ Keeps F state final ∧
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
   rcases step_run F (types.length+extra+3) state head with
    ⟨value,middle,headRun,headField,headKept,headNext,headNonheap⟩
   rcases ih middle (plan_transport F state middle headKept tail) with
    ⟨values,final,tailRun,tailFields,tailKept,tailNext,tailNonheap⟩
   refine ⟨.cons value values,final,?_,?_,?_,by omega,?_⟩
   · simp only [List.length_cons]
     rw [evalConvArgs]
     simp only [evalE,EM.locals,bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,
      ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,
      liftM,monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map]
     have fuel : types.length+1+extra+2=types.length+extra+3 := by omega
     simp only [fuel]
     dsimp only [ExceptT.run] at headRun tailRun
     rw [headRun]
     simp only [getV,RVal.get,EM.lift,bind,pure,Except.pure,ExceptT.pure,
      ExceptT.bindCont,ExceptT.mk,StateT.bind,StateT.pure]
     rw [tailRun]
     rfl
   · exact .cons (LiteralFailureConvertedFields.kept_head F middle final tailKept headField) tailFields
   · intro types shapes values encoded fields
     exact tailKept values encoded (headKept values encoded fields)
   · exact tailNonheap.trans (congrArg (fun source=>{source with heap:=final.heap}) headNonheap)

theorem error_run {E : Env} {Γ types shapes copies} {arguments : RConvArgs E Γ types}
 {encoded : AbiEntry.Vals shapes} (G : Glob E) (F : Fr) (extra : Nat)
 (error : Decl) (typed : error.paramTys E=some types)
 (locals : Locals E.layout Γ) (state : St E) (plan : Plan F state locals arguments encoded copies) :
 ∃ final : St E,
 (execS G F (types.length+extra+4) 0 none
  (.revertError error typed arguments : RStmt E [] false .body Γ Γ) locals).run (L0 E,state)=
 (.error (.revert (G.selector (sigOf E.layout error.name types)++AbiEntry.encodeArgs encoded)),(L0 E,final)) ∧
 Keeps F state final ∧ final.heap.next=state.heap.next+copies ∧ final={state with heap:=final.heap} := by
 rcases run G F extra locals state plan with ⟨values,final,actual,fields,kept,next,nonheap⟩
 refine ⟨final,?_,kept,next,nonheap⟩
 exact SourceCustomErrors.execute G F (types.length+extra+3) error typed arguments
  locals locals state final final values _ actual
  (LiteralFailureLocatedFields.encoding_run F _ (L0 E) final fields)

theorem of_bytes_plan {E : Env} {Γ types shapes copies} {arguments : RConvArgs E Γ types}
 {encoded : AbiEntry.Vals shapes} (F : Fr) (state : St E) (locals : Locals E.layout Γ)
 (plan : LiteralFailureConvertedFields.Plan F state locals arguments encoded copies) :
 Plan F state locals arguments encoded copies := by
 induction plan with
 | nil => exact .nil
 | read index typed head tail ih =>
  simpa only [Nat.zero_add] using Plan.cons index typed (.read index typed head) ih
 | bytes index off len present tail ih =>
  simpa only [Nat.add_comm] using Plan.cons index rfl (.bytes index off len present) ih

end Solidity.Lowering.V08.LiteralFailureCopySequence
