import Solidity.Lowering.V08.LiteralFailureCalldataPrefix

/-! Compositional evidence for actual heterogeneous Source fields at one frame.
Existing scalar/memory witnesses are reused unchanged. Proof-only pieces connect
existing intrinsic values to existing raw encoder parts; no codec, evaluator,
source admission predicate or runtime memory model is introduced. -/
namespace Solidity.Lowering.V08.LiteralFailureLocatedFields
open Solidity Source

inductive Head {E : Env} (F : Fr) (state : St E) :
 {type : STy} → Source.Val E.layout type → {shape : AbiEntry.Shape} → AbiEntry.Val shape → Prop
 | known {type shape value encoded}
   (field : LiteralFailureTypedFields.Fields state (.cons value .nil) (.cons encoded .nil)) :
   @Head E F state type value shape encoded
 | calldataBytes (off len : Nat) :
   Head F state (.cdRef rfl off len : Source.Val E.layout (.bytes .calldata))
    (.bytes ((F.cd.drop off).take len))
 | calldataString (off len : Nat) :
   Head F state (.cdRef rfl off len : Source.Val E.layout (.string .calldata))
    (.bytes ((F.cd.drop off).take len))

inductive Fields {E : Env} (F : Fr) (state : St E) :
 {types : RCtx} → Source.Vals E.layout types → {shapes : List AbiEntry.Shape} → AbiEntry.Vals shapes → Prop
 | nil : Fields F state .nil .nil
 | cons {type types value values shape shapes encoded encodeds}
   (head : @Head E F state type value shape encoded)
   (tail : @Fields E F state types values shapes encodeds) :
   Fields F state (.cons value values) (.cons encoded encodeds)

inductive Piece : {shape : AbiEntry.Shape} → AbiEntry.Val shape → (Bool × Roadmap.Bytes) → Prop
 | word {kind} (w : AbiEntry.Word kind) : Piece (.word w) (false,AbiEntry.wordBytes w.val)
 | bytes (bs : Roadmap.Bytes) : Piece (.bytes bs) (true,bs)

inductive Pieces : {shapes : List AbiEntry.Shape} → AbiEntry.Vals shapes → List (Bool × Roadmap.Bytes) → Prop
 | nil : Pieces .nil []
 | cons {shape shapes encoded encodeds part parts} (head : @Piece shape encoded part)
   (tail : @Pieces shapes encodeds parts) : Pieces (.cons encoded encodeds) (part::parts)

theorem one_witness {E : Env} {Γ type shape} {value : Source.Val E.layout type}
 {encoded : AbiEntry.Val shape} (F : Fr) (fuel : Nat) (locals : Locals E.layout Γ) (state : St E)
 (head : Head F state value encoded) :
 ∃ part, Piece encoded part ∧
  (encodeOne F fuel false (.val value) : EM E Γ _).run (locals,state)=(.ok part,(locals,state)) := by
 cases head with
 | known field =>
  cases field with
  | uint w rest =>
   refine ⟨_,.word (LiteralFailureDynamicError.abiWord w),?_⟩
   simp only [encodeOne,LiteralFailureDynamicError.marker_word,Bool.false_eq_true,↓reduceIte,
    pure,ExceptT.pure,ExceptT.run,LiteralFailureMixedEncoding.word_agreement]
   rfl
  | boolean b rest =>
   refine ⟨_,.word (BoolErrorAbi.word b),?_⟩
   cases b <;> rfl
  | bytes address bs heap rest =>
   refine ⟨_,.bytes bs,?_⟩
   rcases heap with heap | heap <;>
    simp only [encodeOne,bytesOfRV,heapBytes,heapObj,EM.st,
     bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
     StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,liftM,
     monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map,heap]
  | string address bs heap rest =>
   refine ⟨_,.bytes bs,?_⟩
   simp only [encodeOne,bytesOfRV,heapBytes,heapObj,EM.st,
    bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
    StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,liftM,
    monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map,heap]
 | calldataBytes off len => exact ⟨_,.bytes _,rfl⟩
 | calldataString off len => exact ⟨_,.bytes _,rfl⟩

theorem parts_witness {E : Env} {Γ types shapes} {values : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} (F : Fr) (fuel : Nat) (locals : Locals E.layout Γ) (state : St E)
 (fields : Fields F state values encoded) :
 ∃ parts, Pieces encoded parts ∧
  (encodeParts F fuel false values.toR : EM E Γ _).run (locals,state)=(.ok parts,(locals,state)) := by
 induction fields with
 | nil => exact ⟨[],.nil,rfl⟩
 | cons head tail ih =>
  rcases one_witness F fuel locals state head with ⟨part,piece,actual⟩
  rcases ih with ⟨parts,pieces,tailRun⟩
  refine ⟨part::parts,.cons piece pieces,?_⟩
  simp only [Vals.toR]
  rw [encodeParts]
  dsimp only [ExceptT.run] at actual tailRun
  simp only [bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,
   ExceptT.mk,StateT.bind,StateT.pure,actual,tailRun]

theorem go_agreement {shapes} {encoded : AbiEntry.Vals shapes} {parts}
 (pieces : Pieces encoded parts) (offset : Nat) :
 Source.abiLayout.go parts offset=AbiEntry.assemble.go encoded.parts offset := by
 induction pieces generalizing offset with
 | nil => rfl
 | cons head tail ih =>
  cases head with
  | word w =>
   simp only [Source.abiLayout.go,AbiEntry.Vals.parts,AbiEntry.Shape.dynamic,
    AbiEntry.Val.enc,AbiEntry.assemble.go,Bool.false_eq_true,↓reduceIte,ih]
  | bytes bs =>
   simp only [Source.abiLayout.go,AbiEntry.Vals.parts,AbiEntry.Shape.dynamic,
    AbiEntry.Val.enc,AbiEntry.assemble.go,↓reduceIte]
   rw [LiteralFailureDynamicListError.tail_agreement,ih,LiteralFailureDynamicListError.word_transport]
   simp only [AbiEntry.Val.enc,List.append_assoc]

theorem head_extent {shapes} {encoded : AbiEntry.Vals shapes} {parts}
 (pieces : Pieces encoded parts) (offset : Nat) :
 encoded.parts.foldl (fun acc part=>acc+if part.1 then 32 else part.2.length) offset=
 offset+32*parts.length := by
 induction pieces generalizing offset with
 | nil => simp only [AbiEntry.Vals.parts,List.foldl_nil,List.length_nil,Nat.mul_zero,Nat.add_zero]
 | cons head tail ih =>
  cases head with
  | word w =>
   simp only [AbiEntry.Vals.parts,AbiEntry.Shape.dynamic,AbiEntry.Val.enc,AbiEntry.wordBytes,
    List.length_map,List.length_range,List.foldl_cons,Bool.false_eq_true,↓reduceIte,ih,List.length_cons]
   omega
  | bytes bs =>
   simp only [AbiEntry.Vals.parts,AbiEntry.Shape.dynamic,List.foldl_cons,↓reduceIte,ih,List.length_cons]
   omega

theorem encoding_run {E : Env} {Γ types shapes} {values : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} (F : Fr) (fuel : Nat) (locals : Locals E.layout Γ) (state : St E)
 (fields : Fields F state values encoded) :
 (encodeVals F fuel false values.toR : EM E Γ _).run (locals,state)=
 (.ok (AbiEntry.encodeArgs encoded),(locals,state)) := by
 rcases parts_witness F fuel locals state fields with ⟨parts,pieces,actual⟩
 dsimp only [ExceptT.run] at actual
 have layout : Source.abiLayout parts=AbiEntry.encodeArgs encoded := by
  simp only [Source.abiLayout,AbiEntry.encodeArgs,AbiEntry.assemble,head_extent pieces,
   Nat.zero_add,go_agreement pieces]
 simp only [encodeVals,bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,
  ExceptT.mk,StateT.bind,StateT.pure,actual,Bool.false_eq_true,↓reduceIte,layout]

theorem encodingAt {E : Env} {types shapes} {values : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} (F : Fr) (fuel : Nat) (state : St E)
 (fields : Fields F state values encoded) :
 Backend.FailurePaths.Premises.EncodingAt F fuel values.toR state state (AbiEntry.encodeArgs encoded) :=
 encoding_run F fuel (L0 E) state fields

theorem expression_run {E : Env} {Γ types shapes} {values : Source.Vals E.layout types}
 {arguments : RArgs E Γ types} {encoded : AbiEntry.Vals shapes}
 (G : Glob E) (F : Fr) (extra : Nat) (locals : Locals E.layout Γ) (state : St E)
 (lookups : LiteralFailureMixedExpression.LocalArgs locals arguments values)
 (fields : Fields F state values encoded) :
 (evalE G F (types.length+extra+4) (.abiEncode .encode arguments)).run (locals,state)=
 (.ok (.val (.memRef rfl state.heap.next)),(locals,SourceKeccak.afterLiteral state (AbiEntry.encodeArgs encoded))) :=
 SourceAbi.execute G F (types.length+extra+3) false arguments locals locals locals
 state state state values.toR _ (LiteralFailureMixedExpression.arguments_run G F extra locals state lookups)
 (encoding_run F _ locals state fields)

theorem of_memory_fields {E : Env} {types shapes} {values : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} (F : Fr) (state : St E)
 (fields : LiteralFailureTypedFields.Fields state values encoded) : Fields F state values encoded := by
 induction fields with
 | nil => exact .nil
 | uint w tail ih => exact .cons (.known (.uint w .nil)) ih
 | boolean b tail ih => exact .cons (.known (.boolean b .nil)) ih
 | bytes address bs heap tail ih => exact .cons (.known (.bytes address bs heap .nil)) ih
 | string address bs heap tail ih => exact .cons (.known (.string address bs heap .nil)) ih

theorem fields_after {E : Env} {types shapes} {values : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} (F : Fr) (state : St E) (packet : Roadmap.Bytes)
 (fields : Fields F state values encoded) : Fields F (SourceKeccak.afterLiteral state packet) values encoded := by
 induction fields with
 | nil => exact .nil
 | cons head tail ih =>
  cases head with
  | known field => exact .cons (.known (LiteralFailureTypedFields.fields_after state packet field)) ih
  | calldataBytes off len => exact .cons (.calldataBytes off len) ih
  | calldataString off len => exact .cons (.calldataString off len) ih

theorem bool_not_uint {E : Env} {F : Fr} {state : St E} (b : Bool) (w : Roadmap.Word) :
 ¬Head F state (.bool b) (.word (LiteralFailureDynamicError.abiWord w)) := by
 intro head
 cases head with
 | known field => cases field

end Solidity.Lowering.V08.LiteralFailureLocatedFields
