import Solidity.Lowering.V08.LiteralFailureCalldataCopy

/-! Frame-indexed evidence for a finite calldata bytes/string prefix followed
by an existing represented tail. This consumes the published encoder directly;
it is neither a calldata validator nor a new codec or admission predicate. -/
namespace Solidity.Lowering.V08.LiteralFailureCalldataPrefix
open Solidity Source

inductive Located {E : Env} (F : Fr) (state : St E) :
 {types : RCtx} → Source.Vals E.layout types →
 {shapes : List AbiEntry.Shape} → AbiEntry.Vals shapes → List (Bool × Roadmap.Bytes) → Prop
 | base {types shapes source encoded parts}
   (tail : LiteralFailureMixedEncoding.Represented state source encoded parts) :
   @Located E F state types source shapes encoded parts
 | bytes {types shapes source encoded parts} (off len : Nat)
   (tail : @Located E F state types source shapes encoded parts) :
   Located F state (.cons (.cdRef rfl off len : Source.Val E.layout (.bytes .calldata)) source)
    (.cons (.bytes ((F.cd.drop off).take len)) encoded) ((true,(F.cd.drop off).take len)::parts)
 | string {types shapes source encoded parts} (off len : Nat)
   (tail : @Located E F state types source shapes encoded parts) :
   Located F state (.cons (.cdRef rfl off len : Source.Val E.layout (.string .calldata)) source)
    (.cons (.bytes ((F.cd.drop off).take len)) encoded) ((true,(F.cd.drop off).take len)::parts)

theorem parts_run {E : Env} {Γ types shapes} {source : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} {parts} (F : Fr) (fuel : Nat)
 (locals : Locals E.layout Γ) (state : St E)
 (located : Located F state source encoded parts) :
 (encodeParts F fuel false source.toR : EM E Γ _).run (locals,state)=
 (.ok parts,(locals,state)) := by
 induction located with
 | base tail => exact LiteralFailureMixedEncoding.parts_run F fuel locals state tail
 | bytes off len tail ih | string off len tail ih =>
  dsimp only [ExceptT.run] at ih
  simp only [Vals.toR,encodeParts,encodeOne,bytesOfRV,bind,pure,ExceptT.bind,
   ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,ih]

theorem go_agreement {E : Env} {types shapes} {source : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} {parts} (F : Fr) (state : St E)
 (located : Located F state source encoded parts) (offset : Nat) :
 Source.abiLayout.go parts offset=AbiEntry.assemble.go encoded.parts offset := by
 induction located generalizing offset with
 | base tail => exact LiteralFailureMixedEncoding.go_agreement state tail offset
 | bytes off len tail ih | string off len tail ih =>
  simp only [Source.abiLayout.go,AbiEntry.Vals.parts,AbiEntry.Shape.dynamic,
   AbiEntry.Val.enc,AbiEntry.assemble.go,↓reduceIte]
  rw [LiteralFailureDynamicListError.tail_agreement,ih,
   LiteralFailureDynamicListError.word_transport]
  simp only [AbiEntry.Val.enc,List.append_assoc]

theorem head_extent {E : Env} {types shapes} {source : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} {parts} (F : Fr) (state : St E)
 (located : Located F state source encoded parts) (offset : Nat) :
 encoded.parts.foldl (fun acc part=>acc+if part.1 then 32 else part.2.length) offset=
 offset+32*parts.length := by
 induction located generalizing offset with
 | base tail => exact LiteralFailureMixedEncoding.head_extent state tail offset
 | bytes off len tail ih | string off len tail ih =>
  simp only [AbiEntry.Vals.parts,AbiEntry.Shape.dynamic,List.foldl_cons,↓reduceIte,ih,List.length_cons]
  omega

theorem encoding_run {E : Env} {Γ types shapes} {source : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} {parts} (F : Fr) (fuel : Nat)
 (locals : Locals E.layout Γ) (state : St E) (located : Located F state source encoded parts) :
 (encodeVals F fuel false source.toR : EM E Γ _).run (locals,state)=
 (.ok (AbiEntry.encodeArgs encoded),(locals,state)) := by
 have actual := parts_run F fuel locals state located
 dsimp only [ExceptT.run] at actual
 have layout : Source.abiLayout parts=AbiEntry.encodeArgs encoded := by
  simp only [Source.abiLayout,AbiEntry.encodeArgs,AbiEntry.assemble,
   head_extent F state located,Nat.zero_add,go_agreement F state located]
 simp only [encodeVals,bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,
  ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,actual,Bool.false_eq_true,↓reduceIte,layout]

theorem expression_run {E : Env} {Γ types shapes} {source : Source.Vals E.layout types}
 {arguments : RArgs E Γ types} {encoded : AbiEntry.Vals shapes} {parts}
 (G : Glob E) (F : Fr) (extra : Nat) (locals : Locals E.layout Γ) (state : St E)
 (lookups : LiteralFailureMixedExpression.LocalArgs locals arguments source)
 (located : Located F state source encoded parts) :
 (evalE G F (types.length+extra+4) (.abiEncode .encode arguments)).run (locals,state)=
 (.ok (.val (.memRef rfl state.heap.next)),
  (locals,SourceKeccak.afterLiteral state (AbiEntry.encodeArgs encoded))) :=
 SourceAbi.execute G F (types.length+extra+3) false arguments locals locals locals
 state state state source.toR _
 (LiteralFailureMixedExpression.arguments_run G F extra locals state lookups)
 (encoding_run F _ locals state located)

/-- Discharges the existing G38 byte premise; no fetched-code claim. -/
theorem encodingAt {E : Env} {types shapes} {source : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} {parts} (F : Fr) (fuel : Nat) (state : St E)
 (located : Located F state source encoded parts) :
 Backend.FailurePaths.Premises.EncodingAt F fuel source.toR state state
  (AbiEntry.encodeArgs encoded) := encoding_run F fuel (L0 E) state located

end Solidity.Lowering.V08.LiteralFailureCalldataPrefix
