import Solidity.Lowering.V08.LiteralFailureLocatedFields

/-! Proof evidence over actual converted arguments. No final state, converted
value list or desired execution is stored in the evidence: those are derived
from the published identity/conversion/allocation and encoder definitions. -/
namespace Solidity.Lowering.V08.LiteralFailureConvertedFields
open Solidity Source
open LiteralFailureLocatedFields (Head Fields)

inductive Plan {E : Env} {Γ : RCtx} (F : Fr) (state : St E) (locals : Locals E.layout Γ) :
 {types : RCtx} → RConvArgs E Γ types → {shapes : List AbiEntry.Shape} → AbiEntry.Vals shapes → Nat → Prop
 | nil : Plan F state locals .nil .nil 0
 | read {type types arguments shape shapes encoded encodeds copies}
   (index : Source.Idx Γ type) (typed : type.implicit E.isBase E.mapFree type=true)
   (head : @Head E F state type (locals.get index) shape encoded)
   (tail : @Plan E Γ F state locals types arguments shapes encodeds copies) :
   Plan F state locals (.cons (.local index) typed arguments) (.cons encoded encodeds) copies
 | bytes {types arguments shapes encoded copies}
   (index : Source.Idx Γ (.bytes .calldata)) (off len : Nat)
   (present : locals.get index=.cdRef rfl off len)
   (tail : @Plan E Γ F state locals types arguments shapes encoded copies) :
   Plan F state locals (.cons (.local index) rfl arguments : RConvArgs E Γ (.bytes .memory::types))
    (.cons (.bytes ((F.cd.drop off).take len)) encoded) (copies+1)

def Keeps {E : Env} (F : Fr) (initial final : St E) : Prop :=
 ∀ {types shapes} (values : Source.Vals E.layout types) (encoded : AbiEntry.Vals shapes),
 Fields F initial values encoded → Fields F final values encoded

theorem kept_head {E : Env} {type shape} {value : Source.Val E.layout type} {encoded : AbiEntry.Val shape}
 (F : Fr) (initial final : St E) (kept : Keeps F initial final) (head : Head F initial value encoded) :
 Head F final value encoded := by
 have one := kept (.cons value .nil) (.cons encoded .nil) (.cons head .nil)
 cases one with
 | cons head tail => exact head

theorem after_copy {E : Env} {Γ types shapes copies} {arguments : RConvArgs E Γ types}
 {encoded : AbiEntry.Vals shapes} (F : Fr) (state : St E) (locals : Locals E.layout Γ) (bs : Roadmap.Bytes)
 (plan : Plan F state locals arguments encoded copies) :
 Plan F (SourceKeccak.afterLiteral state bs) locals arguments encoded copies := by
 induction plan with
 | nil => exact .nil
 | read index typed head tail ih =>
  have kept : Keeps F state (SourceKeccak.afterLiteral state bs) :=
   fun values encoded fields => LiteralFailureLocatedFields.fields_after F state bs fields
  exact .read index typed (kept_head F _ _ kept head) ih
 | bytes index off len present tail ih => exact .bytes index off len present ih

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
  | read index typed head tail =>
   rcases ih state tail with ⟨values,final,actual,fields,kept,next,nonheap⟩
   refine ⟨.cons (locals.get index) values,final,?_,.cons (kept_head F state final kept head) fields,kept,next,nonheap⟩
   simp only [List.length_cons]
   rw [evalConvArgs]
   simp only [evalE,convRV,↓reduceDIte,getV,RVal.get,EM.locals,EM.lift,
    bind,pure,Except.pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
    StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,liftM,
    monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map]
   have fuel : types.length+1+extra+2=types.length+extra+3 := by omega
   simp only [fuel]
   dsimp only [ExceptT.run] at actual
   rw [actual]
   rfl
  | bytes index off len present tail =>
   let bs := (F.cd.drop off).take len
   let middle := SourceKeccak.afterLiteral state bs
   rcases ih middle (after_copy F state locals bs tail) with ⟨values,final,actual,fields,kept,next,nonheap⟩
   refine ⟨.cons (.memRef rfl state.heap.next) values,final,?_,?_,?_,?_,?_⟩
   · have copied := LiteralFailureCalldataCopy.copy_run F (types.length+extra+3) off len locals state
     simp only [List.length_cons]
     rw [evalConvArgs]
     simp only [evalE,EM.locals,present,bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,
      ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,
      liftM,monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map]
     have fuel : types.length+1+extra+2=types.length+extra+3 := by omega
     simp only [fuel]
     dsimp only [ExceptT.run,middle,bs,LiteralFailureCalldataCopy.copied] at copied actual
     rw [copied]
     simp only [getV,RVal.get,EM.lift,bind,pure,Except.pure,ExceptT.pure,
      ExceptT.bindCont,ExceptT.mk,StateT.bind,StateT.pure]
     rw [actual]
     rfl
   · have created : Head F middle (.memRef rfl state.heap.next : Source.Val E.layout (.bytes .memory)) (.bytes bs) :=
      .known (.bytes state.heap.next bs (.inl (SourceKeccak.allocated state bs)) .nil)
     exact .cons (kept_head F middle final kept created) fields
   · intro types shapes values encoded fields
     exact kept values encoded (LiteralFailureLocatedFields.fields_after F state bs fields)
   · change final.heap.next=state.heap.next+1+_ at next
     omega
   · exact nonheap

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

end Solidity.Lowering.V08.LiteralFailureConvertedFields
