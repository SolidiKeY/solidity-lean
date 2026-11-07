import Solidity.Lowering.V08.LiteralFailureMixedCustomError
import Solidity.Lowering.V08.LiteralFailureMixedExpression

/-! A typed relation between existing indexed value lists. It relates memory
strings to byte-shaped encoding witnesses at the same addresses; it is not a
source conversion, a decoder, or an admission predicate. Existing encoder
computations, including failure order, remain unchanged. -/
namespace Solidity.Lowering.V08.LiteralFailureStringInterleaving
open Solidity Source

inductive StringBytes {E : Env} :
 {sourceTypes witnessTypes : RCtx} →
 Source.Vals E.layout sourceTypes → Source.Vals E.layout witnessTypes → Prop
 | nil : StringBytes .nil .nil
 | keep {τ sourceTypes witnessTypes source witness} (value : Source.Val E.layout τ)
   (tail : @StringBytes E sourceTypes witnessTypes source witness) :
   StringBytes (.cons value source) (.cons value witness)
 | string {sourceTypes witnessTypes source witness} (address : Nat)
   (tail : @StringBytes E sourceTypes witnessTypes source witness) :
   StringBytes (.cons (.memRef rfl address : Source.Val E.layout (.string .memory)) source)
    (.cons (.memRef rfl address : Source.Val E.layout (.bytes .memory)) witness)

theorem parts_eq {E : Env} {Γ sourceTypes witnessTypes}
 {source : Source.Vals E.layout sourceTypes} {witness : Source.Vals E.layout witnessTypes}
 (F : Fr) (fuel : Nat) (packed : Bool) (related : StringBytes source witness) :
 (encodeParts F fuel packed source.toR : EM E Γ _)=encodeParts F fuel packed witness.toR := by
 induction related with
 | nil => rfl
 | keep value tail ih => simp only [Vals.toR,encodeParts,ih]
 | string address tail ih => simp only [Vals.toR,encodeParts,encodeOne,bytesOfRV,ih]

theorem encoding_eq {E : Env} {Γ sourceTypes witnessTypes}
 {source : Source.Vals E.layout sourceTypes} {witness : Source.Vals E.layout witnessTypes}
 (F : Fr) (fuel : Nat) (packed : Bool) (related : StringBytes source witness) :
 (encodeVals F fuel packed source.toR : EM E Γ _)=encodeVals F fuel packed witness.toR := by
 simp only [encodeVals,parts_eq F fuel packed related]

theorem encoding_run {E : Env} {Γ sourceTypes witnessTypes shapes}
 {source : Source.Vals E.layout sourceTypes} {witness : Source.Vals E.layout witnessTypes}
 {encoded : AbiEntry.Vals shapes} {parts} (F : Fr) (fuel : Nat)
 (locals : Locals E.layout Γ) (state : St E) (related : StringBytes source witness)
 (fields : LiteralFailureMixedEncoding.Represented state witness encoded parts) :
 (encodeVals F fuel false source.toR : EM E Γ _).run (locals,state)=
 (.ok (AbiEntry.encodeArgs encoded),(locals,state)) := by
 rw [encoding_eq F fuel false related]
 exact LiteralFailureMixedEncoding.encoding_run F fuel locals state fields

theorem encodingAt {E : Env} {sourceTypes witnessTypes shapes}
 {source : Source.Vals E.layout sourceTypes} {witness : Source.Vals E.layout witnessTypes}
 {encoded : AbiEntry.Vals shapes} {parts} (F : Fr) (fuel : Nat) (state : St E)
 (related : StringBytes source witness)
 (fields : LiteralFailureMixedEncoding.Represented state witness encoded parts) :
 Backend.FailurePaths.Premises.EncodingAt F fuel source.toR state state
  (AbiEntry.encodeArgs encoded) := encoding_run F fuel (L0 E) state related fields

theorem source_run {E : Env} {Γ sourceTypes witnessTypes shapes}
 {source : Source.Vals E.layout sourceTypes} {witness : Source.Vals E.layout witnessTypes}
 {arguments : RConvArgs E Γ sourceTypes} {encoded : AbiEntry.Vals shapes} {parts}
 (G : Glob E) (F : Fr) (extra : Nat) (error : Decl) (typed : error.paramTys E=some sourceTypes)
 (locals : Locals E.layout Γ) (state : St E)
 (lookups : LiteralFailureMixedCustomError.LocalArgs locals arguments source)
 (related : StringBytes source witness)
 (fields : LiteralFailureMixedEncoding.Represented state witness encoded parts) :
 (execS G F (sourceTypes.length+extra+4) 0 none
  (.revertError error typed arguments : RStmt E [] false .body Γ Γ) locals).run (L0 E,state)=
 (.error (.revert (G.selector (sigOf E.layout error.name sourceTypes)++AbiEntry.encodeArgs encoded)),
  (L0 E,state)) :=
 SourceCustomErrors.execute G F (sourceTypes.length+extra+3) error typed arguments
 locals locals state state state source _
 (LiteralFailureMixedCustomError.arguments_run G F extra locals state lookups)
 (encoding_run F _ (L0 E) state related fields)

theorem expression_run {E : Env} {Γ sourceTypes witnessTypes shapes}
 {source : Source.Vals E.layout sourceTypes} {witness : Source.Vals E.layout witnessTypes}
 {arguments : RArgs E Γ sourceTypes} {encoded : AbiEntry.Vals shapes} {parts}
 (G : Glob E) (F : Fr) (extra : Nat) (locals : Locals E.layout Γ) (state : St E)
 (lookups : LiteralFailureMixedExpression.LocalArgs locals arguments source)
 (related : StringBytes source witness)
 (fields : LiteralFailureMixedEncoding.Represented state witness encoded parts) :
 (evalE G F (sourceTypes.length+extra+4) (.abiEncode .encode arguments)).run (locals,state)=
 (.ok (.val (.memRef rfl state.heap.next)),
  (locals,SourceKeccak.afterLiteral state (AbiEntry.encodeArgs encoded))) :=
 SourceAbi.execute G F (sourceTypes.length+extra+3) false arguments locals locals locals
 state state state source.toR _
 (LiteralFailureMixedExpression.arguments_run G F extra locals state lookups)
 (encoding_run F _ locals state related fields)

end Solidity.Lowering.V08.LiteralFailureStringInterleaving
