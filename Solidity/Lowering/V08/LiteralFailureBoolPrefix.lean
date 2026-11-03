import Solidity.Lowering.V08.LiteralFailureStringInterleaving
import Solidity.Lowering.V08.BoolErrorAbi

/-! Actual standard ABI encoding for a typed boolean local before an arbitrary
supported heterogeneous memory-string/uint256/bytes tail. The bool ABI kind
and original Source parameter type remain bool. No decoder, conversion,
admission rule or target encoder is introduced. -/
namespace Solidity.Lowering.V08.LiteralFailureBoolPrefix
open Solidity Source

def boolWord (b : Bool) : Roadmap.Word := Source.toWord (if b then 1 else 0)

theorem parts_eq {E : Env} {Γ types} (F : Fr) (fuel : Nat) (b : Bool)
 (source : Source.Vals E.layout types) :
 (encodeParts F fuel false (Source.Vals.cons (.bool b) source).toR : EM E Γ _)=
 encodeParts F fuel false (Source.Vals.cons (SourceEnvironment.sourceWord (boolWord b)) source).toR := by
 cases b <;> rfl

theorem encoding_eq {E : Env} {Γ types} (F : Fr) (fuel : Nat) (b : Bool)
 (source : Source.Vals E.layout types) :
 (encodeVals F fuel false (Source.Vals.cons (.bool b) source).toR : EM E Γ _)=
 encodeVals F fuel false (Source.Vals.cons (SourceEnvironment.sourceWord (boolWord b)) source).toR := by
 simp only [encodeVals,parts_eq]

theorem abi_eq {shapes} (b : Bool) (encoded : AbiEntry.Vals shapes) :
 AbiEntry.encodeArgs (AbiEntry.Vals.cons (.word (BoolErrorAbi.word b)) encoded)=
 AbiEntry.encodeArgs (AbiEntry.Vals.cons (.word (LiteralFailureDynamicError.abiWord (boolWord b))) encoded) := by
 cases b <;> rfl

theorem encoding_run {E : Env} {Γ sourceTypes witnessTypes shapes}
 {source : Source.Vals E.layout sourceTypes} {witness : Source.Vals E.layout witnessTypes}
 {encoded : AbiEntry.Vals shapes} {parts} (F : Fr) (fuel : Nat) (b : Bool)
 (locals : Locals E.layout Γ) (state : St E)
 (related : LiteralFailureStringInterleaving.StringBytes source witness)
 (fields : LiteralFailureMixedEncoding.Represented state witness encoded parts) :
 (encodeVals F fuel false (Source.Vals.cons (.bool b) source).toR : EM E Γ _).run (locals,state)=
 (.ok (AbiEntry.encodeArgs (.cons (.word (BoolErrorAbi.word b)) encoded)),(locals,state)) := by
 rw [encoding_eq,abi_eq]
 exact LiteralFailureStringInterleaving.encoding_run F fuel locals state
  (.keep (SourceEnvironment.sourceWord (boolWord b)) related) (.uint (boolWord b) fields)

theorem encodingAt {E : Env} {sourceTypes witnessTypes shapes}
 {source : Source.Vals E.layout sourceTypes} {witness : Source.Vals E.layout witnessTypes}
 {encoded : AbiEntry.Vals shapes} {parts} (F : Fr) (fuel : Nat) (b : Bool) (state : St E)
 (related : LiteralFailureStringInterleaving.StringBytes source witness)
 (fields : LiteralFailureMixedEncoding.Represented state witness encoded parts) :
 Backend.FailurePaths.Premises.EncodingAt F fuel (Source.Vals.cons (.bool b) source).toR state state
  (AbiEntry.encodeArgs (.cons (.word (BoolErrorAbi.word b)) encoded)) :=
 encoding_run F fuel b (L0 E) state related fields

theorem source_run {E : Env} {Γ sourceTypes witnessTypes shapes}
 {source : Source.Vals E.layout sourceTypes} {witness : Source.Vals E.layout witnessTypes}
 {arguments : RConvArgs E Γ (.bool::sourceTypes)} {encoded : AbiEntry.Vals shapes} {parts}
 (G : Glob E) (F : Fr) (extra : Nat) (error : Decl) (typed : error.paramTys E=some (.bool::sourceTypes))
 (b : Bool) (locals : Locals E.layout Γ) (state : St E)
 (lookups : LiteralFailureMixedCustomError.LocalArgs locals arguments (.cons (.bool b) source))
 (related : LiteralFailureStringInterleaving.StringBytes source witness)
 (fields : LiteralFailureMixedEncoding.Represented state witness encoded parts) :
 (execS G F ((.bool::sourceTypes).length+extra+4) 0 none
  (.revertError error typed arguments : RStmt E [] false .body Γ Γ) locals).run (L0 E,state)=
 (.error (.revert (G.selector (sigOf E.layout error.name (.bool::sourceTypes))++
  AbiEntry.encodeArgs (.cons (.word (BoolErrorAbi.word b)) encoded))),(L0 E,state)) :=
 SourceCustomErrors.execute G F ((.bool::sourceTypes).length+extra+3) error typed arguments
 locals locals state state state (.cons (.bool b) source) _
 (LiteralFailureMixedCustomError.arguments_run G F extra locals state lookups)
 (encoding_run F _ b (L0 E) state related fields)

theorem expression_run {E : Env} {Γ sourceTypes witnessTypes shapes}
 {source : Source.Vals E.layout sourceTypes} {witness : Source.Vals E.layout witnessTypes}
 {arguments : RArgs E Γ (.bool::sourceTypes)} {encoded : AbiEntry.Vals shapes} {parts}
 (G : Glob E) (F : Fr) (extra : Nat) (b : Bool) (locals : Locals E.layout Γ) (state : St E)
 (lookups : LiteralFailureMixedExpression.LocalArgs locals arguments (.cons (.bool b) source))
 (related : LiteralFailureStringInterleaving.StringBytes source witness)
 (fields : LiteralFailureMixedEncoding.Represented state witness encoded parts) :
 (evalE G F ((.bool::sourceTypes).length+extra+4) (.abiEncode .encode arguments)).run (locals,state)=
 (.ok (.val (.memRef rfl state.heap.next)),(locals,
  SourceKeccak.afterLiteral state (AbiEntry.encodeArgs (.cons (.word (BoolErrorAbi.word b)) encoded)))) :=
 SourceAbi.execute G F ((.bool::sourceTypes).length+extra+3) false arguments locals locals locals
 state state state (Source.Vals.cons (.bool b) source).toR _
 (LiteralFailureMixedExpression.arguments_run G F extra locals state lookups)
 (encoding_run F _ b locals state related fields)

end Solidity.Lowering.V08.LiteralFailureBoolPrefix
