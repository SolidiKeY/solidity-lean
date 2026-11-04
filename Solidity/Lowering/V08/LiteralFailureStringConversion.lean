import Solidity.Lowering.V08.LiteralFailureConvertedFields

/-! Transport through the published intrinsic Heap.alloc, then consume the
actual calldata-string conversion before an existing converted-argument tail.
The state adapter projects that allocation; it is not another allocator or
execution semantics. -/
namespace Solidity.Lowering.V08.LiteralFailureStringConversion
open Solidity Source
open LiteralFailureLocatedFields (Head Fields)
open LiteralFailureConvertedFields (Plan Keeps)

def afterAlloc {E : Env} (state : St E) (object : Σ type, Source.Data E.layout type) : St E :=
 {state with heap:=(state.heap.alloc object).1}

theorem old_lookup {E : Env} (state : St E) (object : Σ type, Source.Data E.layout type)
 (address : Nat) (old : Σ type, Source.Data E.layout type) (present : state.heap.get address=some old) :
 (afterAlloc state object).heap.get address=some old := by
 have different : address≠state.heap.next := by
  intro equal
  have empty := state.heap.bounded address (by omega)
  change state.heap.get address=none at empty
  rw [present] at empty
  cases empty
 exact (Source.Heap.alloc_other state.heap object different).trans present

theorem typed_fields_after {E : Env} {types shapes} {values : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} (state : St E) (object : Σ type, Source.Data E.layout type)
 (fields : LiteralFailureTypedFields.Fields state values encoded) :
 LiteralFailureTypedFields.Fields (afterAlloc state object) values encoded := by
 induction fields with
 | nil => exact .nil
 | uint w tail ih => exact .uint w ih
 | boolean b tail ih => exact .boolean b ih
 | bytes address bs heap tail ih =>
  apply LiteralFailureTypedFields.Fields.bytes address bs _ ih
  rcases heap with heap | heap
  · exact .inl (old_lookup state object address _ heap)
  · exact .inr (old_lookup state object address _ heap)
 | string address bs heap tail ih => exact .string address bs (old_lookup state object address _ heap) ih

theorem head_after {E : Env} {type shape} {value : Source.Val E.layout type} {encoded : AbiEntry.Val shape}
 (F : Fr) (state : St E) (object : Σ type, Source.Data E.layout type) (head : Head F state value encoded) :
 Head F (afterAlloc state object) value encoded := by
 cases head with
 | known field => exact .known (typed_fields_after state object field)
 | calldataBytes off len => exact .calldataBytes off len
 | calldataString off len => exact .calldataString off len

theorem fields_after {E : Env} {types shapes} {values : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} (F : Fr) (state : St E) (object : Σ type, Source.Data E.layout type)
 (fields : Fields F state values encoded) : Fields F (afterAlloc state object) values encoded := by
 induction fields with
 | nil => exact .nil
 | cons head tail ih => exact .cons (head_after F state object head) ih

theorem plan_after {E : Env} {Γ types shapes copies} {arguments : RConvArgs E Γ types}
 {encoded : AbiEntry.Vals shapes} (F : Fr) (state : St E) (locals : Locals E.layout Γ)
 (object : Σ type, Source.Data E.layout type) (plan : Plan F state locals arguments encoded copies) :
 Plan F (afterAlloc state object) locals arguments encoded copies := by
 induction plan with
 | nil => exact .nil
 | read index typed head tail ih => exact .read index typed (head_after F state object head) ih
 | bytes index off len present tail ih => exact .bytes index off len present ih

def afterString {E : Env} (state : St E) (bs : Roadmap.Bytes) :=
 afterAlloc state ⟨.string .memory,.string bs⟩

theorem copy_run {E : Env} {Γ} (F : Fr) (fuel off len : Nat) (locals : Locals E.layout Γ) (state : St E) :
 (convRV F fuel (.string .memory) (.val (.cdRef rfl off len) : RVal E.layout (.string .calldata)) : EM E Γ _).run
 (locals,state)=(.ok (.val (.memRef rfl state.heap.next)),(locals,afterString state ((F.cd.drop off).take len))) := by
 rfl

theorem allocated {E : Env} (state : St E) (bs : Roadmap.Bytes) :
 (afterString state bs).heap.get state.heap.next=some ⟨.string .memory,.string bs⟩ :=
 Source.Heap.alloc_get state.heap _

def arguments {E : Env} {Γ types} (index : Source.Idx Γ (.string .calldata))
 (tail : RConvArgs E Γ types) : RConvArgs E Γ (.string .memory::types) := .cons (.local index) rfl tail

theorem run {E : Env} {Γ types shapes copies} {tail : RConvArgs E Γ types}
 {encoded : AbiEntry.Vals shapes} (G : Glob E) (F : Fr) (extra off len : Nat)
 (locals : Locals E.layout Γ) (state : St E) (index : Source.Idx Γ (.string .calldata))
 (present : locals.get index=.cdRef rfl off len) (plan : Plan F state locals tail encoded copies) :
 ∃ (values : Source.Vals E.layout (.string .memory::types)) (final : St E),
 (evalConvArgs G F (types.length+extra+4) (arguments index tail)).run (locals,state)=(.ok values,(locals,final)) ∧
 Fields F final values (.cons (.bytes ((F.cd.drop off).take len)) encoded) ∧ Keeps F state final ∧
 final.heap.next=state.heap.next+(copies+1) ∧ final={state with heap:=final.heap} := by
 let bs := (F.cd.drop off).take len
 let middle := afterString state bs
 have tailPlan := plan_after F state locals ⟨.string .memory,.string bs⟩ plan
 rcases LiteralFailureConvertedFields.run G F extra locals middle tailPlan with
  ⟨values,final,actual,fields,kept,next,nonheap⟩
 refine ⟨.cons (.memRef rfl state.heap.next) values,final,?_,?_,?_,?_,?_⟩
 · have copied := copy_run F (types.length+extra+3) off len locals state
   simp only [arguments]
   rw [evalConvArgs]
   simp only [evalE,EM.locals,present,bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,
    ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,
    liftM,monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map]
   dsimp only [ExceptT.run,middle,bs] at copied actual
   rw [copied]
   simp only [getV,RVal.get,EM.lift,bind,pure,Except.pure,ExceptT.pure,
    ExceptT.bindCont,ExceptT.mk,StateT.bind,StateT.pure]
   rw [actual]
   rfl
 · have created : Head F middle (.memRef rfl state.heap.next : Source.Val E.layout (.string .memory)) (.bytes bs) :=
    .known (.string state.heap.next bs (allocated state bs) .nil)
   exact .cons (LiteralFailureConvertedFields.kept_head F middle final kept created) fields
 · intro types shapes values encoded fields
   exact kept values encoded (fields_after F state ⟨.string .memory,.string bs⟩ fields)
 · change final.heap.next=state.heap.next+1+_ at next
   omega
 · exact nonheap

theorem error_run {E : Env} {Γ types shapes copies} {tail : RConvArgs E Γ types}
 {encoded : AbiEntry.Vals shapes} (G : Glob E) (F : Fr) (extra off len : Nat)
 (error : Decl) (typed : error.paramTys E=some (.string .memory::types))
 (locals : Locals E.layout Γ) (state : St E) (index : Source.Idx Γ (.string .calldata))
 (present : locals.get index=.cdRef rfl off len) (plan : Plan F state locals tail encoded copies) :
 ∃ final : St E,
 (execS G F (types.length+extra+5) 0 none
  (.revertError error typed (arguments index tail) : RStmt E [] false .body Γ Γ) locals).run (L0 E,state)=
 (.error (.revert (G.selector (sigOf E.layout error.name (.string .memory::types))++
  AbiEntry.encodeArgs (.cons (.bytes ((F.cd.drop off).take len)) encoded))),(L0 E,final)) ∧
 Keeps F state final ∧ final.heap.next=state.heap.next+(copies+1) ∧ final={state with heap:=final.heap} := by
 rcases run G F extra off len locals state index present plan with ⟨values,final,actual,fields,kept,next,nonheap⟩
 refine ⟨final,?_,kept,next,nonheap⟩
 exact SourceCustomErrors.execute G F (types.length+extra+4) error typed (arguments index tail)
  locals locals state final final values _ actual
  (LiteralFailureLocatedFields.encoding_run F _ (L0 E) final fields)

end Solidity.Lowering.V08.LiteralFailureStringConversion
