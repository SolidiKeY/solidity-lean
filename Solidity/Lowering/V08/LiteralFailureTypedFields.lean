import Solidity.Lowering.V08.LiteralFailureBoolPrefix

/-! Synchronized evidence for existing intrinsic Source values and ABI values.
Fields are paired at each indexed position; no source/ABI kind correspondence
is assumed from two independent byte equalities. This is not an evaluator,
codec, source conversion or admission predicate. -/
namespace Solidity.Lowering.V08.LiteralFailureTypedFields
open Solidity Source

inductive SourceWords {E : Env} :
 {types normalizedTypes : RCtx} → Source.Vals E.layout types →
 Source.Vals E.layout normalizedTypes → Prop
 | nil : SourceWords .nil .nil
 | keep {τ types normalizedTypes source normalized} (value : Source.Val E.layout τ)
   (tail : @SourceWords E types normalizedTypes source normalized) :
   SourceWords (.cons value source) (.cons value normalized)
 | boolean {types normalizedTypes source normalized} (b : Bool)
   (tail : @SourceWords E types normalizedTypes source normalized) :
   SourceWords (.cons (.bool b) source)
    (.cons (SourceEnvironment.sourceWord (LiteralFailureBoolPrefix.boolWord b)) normalized)
 | string {types normalizedTypes source normalized} (address : Nat)
   (tail : @SourceWords E types normalizedTypes source normalized) :
   SourceWords (.cons (.memRef rfl address : Source.Val E.layout (.string .memory)) source)
    (.cons (.memRef rfl address : Source.Val E.layout (.bytes .memory)) normalized)

theorem source_parts {E : Env} {Γ types normalizedTypes}
 {source : Source.Vals E.layout types} {normalized : Source.Vals E.layout normalizedTypes}
 (F : Fr) (fuel : Nat) (related : SourceWords source normalized) :
 (encodeParts F fuel false source.toR : EM E Γ _)=encodeParts F fuel false normalized.toR := by
 induction related with
 | nil => rfl
 | keep value tail ih => simp only [Vals.toR,encodeParts,ih]
 | boolean b tail ih =>
  rw [LiteralFailureBoolPrefix.parts_eq]
  simp only [Vals.toR,encodeParts,ih]
 | string address tail ih => simp only [Vals.toR,encodeParts,encodeOne,bytesOfRV,ih]

inductive CodecWords : {shapes normalizedShapes : List AbiEntry.Shape} →
 AbiEntry.Vals shapes → AbiEntry.Vals normalizedShapes → Prop
 | nil : CodecWords .nil .nil
 | keep {shape shapes normalizedShapes source normalized} (value : AbiEntry.Val shape)
   (tail : @CodecWords shapes normalizedShapes source normalized) :
   CodecWords (.cons value source) (.cons value normalized)
 | boolean {shapes normalizedShapes source normalized} (b : Bool)
   (tail : @CodecWords shapes normalizedShapes source normalized) :
   CodecWords (.cons (.word (BoolErrorAbi.word b)) source)
    (.cons (.word (LiteralFailureDynamicError.abiWord (LiteralFailureBoolPrefix.boolWord b))) normalized)

theorem codec_parts {shapes normalizedShapes} {source : AbiEntry.Vals shapes}
 {normalized : AbiEntry.Vals normalizedShapes} (related : CodecWords source normalized) :
 source.parts=normalized.parts := by
 induction related with
 | nil => rfl
 | keep value tail ih => simp only [AbiEntry.Vals.parts,ih]
 | boolean b tail ih => cases b <;> simp only [AbiEntry.Vals.parts,AbiEntry.Shape.dynamic,AbiEntry.Val.enc,ih] <;> rfl

inductive Fields {E : Env} (state : St E) :
 {types : RCtx} → Source.Vals E.layout types →
 {shapes : List AbiEntry.Shape} → AbiEntry.Vals shapes → Prop
 | nil : Fields state .nil .nil
 | uint {types shapes source encoded} (w : Roadmap.Word)
   (tail : @Fields E state types source shapes encoded) :
   Fields state (.cons (SourceEnvironment.sourceWord w) source)
    (.cons (.word (LiteralFailureDynamicError.abiWord w)) encoded)
 | boolean {types shapes source encoded} (b : Bool)
   (tail : @Fields E state types source shapes encoded) :
   Fields state (.cons (.bool b) source) (.cons (.word (BoolErrorAbi.word b)) encoded)
 | bytes {types shapes source encoded} (address : Nat) (bs : Roadmap.Bytes)
   (heap : state.heap.get address=some ⟨.bytes .memory,.bytes bs⟩ ∨
    state.heap.get address=some ⟨.string .memory,.string bs⟩)
   (tail : @Fields E state types source shapes encoded) :
   Fields state (.cons (.memRef rfl address : Source.Val E.layout (.bytes .memory)) source)
    (.cons (.bytes bs) encoded)
 | string {types shapes source encoded} (address : Nat) (bs : Roadmap.Bytes)
   (heap : state.heap.get address=some ⟨.string .memory,.string bs⟩)
   (tail : @Fields E state types source shapes encoded) :
   Fields state (.cons (.memRef rfl address : Source.Val E.layout (.string .memory)) source)
    (.cons (.bytes bs) encoded)

theorem normalized {E : Env} {types shapes} {source : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} (state : St E) (fields : Fields state source encoded) :
 ∃ normalizedTypes, ∃ (sv : Source.Vals E.layout normalizedTypes),
 ∃ normalizedShapes, ∃ (ev : AbiEntry.Vals normalizedShapes), ∃ parts,
 SourceWords source sv ∧ CodecWords encoded ev ∧
 LiteralFailureMixedEncoding.Represented state sv ev parts := by
 induction fields with
 | nil => exact ⟨[],.nil,[],.nil,[],.nil,.nil,.nil⟩
 | uint w tail ih =>
  rcases ih with ⟨ts,sv,ss,ev,ps,rs,ra,rf⟩
  exact ⟨_,.cons (SourceEnvironment.sourceWord w) sv,_,.cons (.word (LiteralFailureDynamicError.abiWord w)) ev,_,.keep _ rs,.keep _ ra,.uint w rf⟩
 | boolean b tail ih =>
  rcases ih with ⟨ts,sv,ss,ev,ps,rs,ra,rf⟩
  exact ⟨_,.cons (SourceEnvironment.sourceWord (LiteralFailureBoolPrefix.boolWord b)) sv,_,.cons (.word (LiteralFailureDynamicError.abiWord (LiteralFailureBoolPrefix.boolWord b))) ev,_,.boolean b rs,.boolean b ra,.uint _ rf⟩
 | bytes address bs heap tail ih =>
  rcases ih with ⟨ts,sv,ss,ev,ps,rs,ra,rf⟩
  exact ⟨_,.cons (.memRef rfl address) sv,_,.cons (.bytes bs) ev,_,.keep _ rs,.keep _ ra,.bytes address bs heap rf⟩
 | string address bs heap tail ih =>
  rcases ih with ⟨ts,sv,ss,ev,ps,rs,ra,rf⟩
  exact ⟨_,.cons (.memRef rfl address) sv,_,.cons (.bytes bs) ev,_,.string address rs,.keep _ ra,.bytes address bs (.inr heap) rf⟩

theorem source_encoding {E : Env} {Γ types normalizedTypes}
 {source : Source.Vals E.layout types} {sv : Source.Vals E.layout normalizedTypes}
 (F : Fr) (fuel : Nat) (related : SourceWords source sv) :
 (encodeVals F fuel false source.toR : EM E Γ _)=encodeVals F fuel false sv.toR := by
 simp only [encodeVals,source_parts F fuel related]

theorem codec_encoding {shapes normalizedShapes} {encoded : AbiEntry.Vals shapes}
 {ev : AbiEntry.Vals normalizedShapes} (related : CodecWords encoded ev) :
 AbiEntry.encodeArgs encoded=AbiEntry.encodeArgs ev := by
 simp only [AbiEntry.encodeArgs,codec_parts related]

theorem encoding_run {E : Env} {Γ types shapes} {source : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} (F : Fr) (fuel : Nat)
 (locals : Locals E.layout Γ) (state : St E) (fields : Fields state source encoded) :
 (encodeVals F fuel false source.toR : EM E Γ _).run (locals,state)=
 (.ok (AbiEntry.encodeArgs encoded),(locals,state)) := by
 rcases normalized state fields with ⟨ts,sv,ss,ev,ps,rs,ra,rf⟩
 rw [source_encoding F fuel rs,codec_encoding ra]
 exact LiteralFailureMixedEncoding.encoding_run F fuel locals state rf

theorem encodingAt {E : Env} {types shapes} {source : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} (F : Fr) (fuel : Nat) (state : St E)
 (fields : Fields state source encoded) :
 Backend.FailurePaths.Premises.EncodingAt F fuel source.toR state state
  (AbiEntry.encodeArgs encoded) := encoding_run F fuel (L0 E) state fields

theorem source_run {E : Env} {Γ types shapes} {source : Source.Vals E.layout types}
 {arguments : RConvArgs E Γ types} {encoded : AbiEntry.Vals shapes}
 (G : Glob E) (F : Fr) (extra : Nat) (error : Decl) (typed : error.paramTys E=some types)
 (locals : Locals E.layout Γ) (state : St E)
 (lookups : LiteralFailureMixedCustomError.LocalArgs locals arguments source)
 (fields : Fields state source encoded) :
 (execS G F (types.length+extra+4) 0 none
  (.revertError error typed arguments : RStmt E [] false .body Γ Γ) locals).run (L0 E,state)=
 (.error (.revert (G.selector (sigOf E.layout error.name types)++AbiEntry.encodeArgs encoded)),
  (L0 E,state)) :=
 SourceCustomErrors.execute G F (types.length+extra+3) error typed arguments
 locals locals state state state source _
 (LiteralFailureMixedCustomError.arguments_run G F extra locals state lookups)
 (encoding_run F _ (L0 E) state fields)

theorem expression_run {E : Env} {Γ types shapes} {source : Source.Vals E.layout types}
 {arguments : RArgs E Γ types} {encoded : AbiEntry.Vals shapes}
 (G : Glob E) (F : Fr) (extra : Nat) (locals : Locals E.layout Γ) (state : St E)
 (lookups : LiteralFailureMixedExpression.LocalArgs locals arguments source)
 (fields : Fields state source encoded) :
 (evalE G F (types.length+extra+4) (.abiEncode .encode arguments)).run (locals,state)=
 (.ok (.val (.memRef rfl state.heap.next)),
  (locals,SourceKeccak.afterLiteral state (AbiEntry.encodeArgs encoded))) :=
 SourceAbi.execute G F (types.length+extra+3) false arguments locals locals locals
 state state state source.toR _
 (LiteralFailureMixedExpression.arguments_run G F extra locals state lookups)
 (encoding_run F _ locals state fields)

theorem fields_after {E : Env} {types shapes} {source : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} (state : St E) (packet : Roadmap.Bytes)
 (fields : Fields state source encoded) :
 Fields (SourceKeccak.afterLiteral state packet) source encoded := by
 induction fields with
 | nil => exact .nil
 | uint w tail ih => exact .uint w ih
 | boolean b tail ih => exact .boolean b ih
 | bytes address bs heap tail ih =>
  apply Fields.bytes address bs _ ih
  rcases heap with heap | heap
  · exact .inl (LiteralFailureMixedExpression.old_object state packet address _ heap)
  · exact .inr (LiteralFailureMixedExpression.old_object state packet address _ heap)
 | string address bs heap tail ih =>
  exact .string address bs (LiteralFailureMixedExpression.old_object state packet address _ heap) ih

end Solidity.Lowering.V08.LiteralFailureTypedFields
