import Solidity.Lowering.V08.LiteralFailureMixedSignature
import Solidity.Lowering.V08.LiteralFailureMixedExpressionControls
namespace Solidity.Lowering.V08.LiteralFailureMixedSignatureControls
open Solidity Source
open LiteralFailureMixedSignature
open LiteralFailureMixedEncodingControls (types parameters locals values abiValues represented x y)
open SourceCustomErrorControls (E frame global)
open LiteralFailureDynamicReturnControls (state)

def tailArgs : RArgs E parameters types := LiteralFailureMixedExpressionControls.arguments
def arguments : RArgs E parameters ((.bytes .memory)::types) := .cons (.local .here) tailArgs

theorem lookups (a b : Roadmap.Word) : LiteralFailureMixedExpression.LocalArgs (locals a b) tailArgs (values a b) :=
 LiteralFailureMixedExpressionControls.lookups a b

theorem signature_memory (first second : Roadmap.Bytes) (a b : Roadmap.Word) :
 LiteralFailureDynamicListError.represented (locals a b) (state first second) .here first := ⟨1,rfl,.inl rfl⟩

def selectorPrefix (first : Roadmap.Bytes) : Roadmap.Bytes := (wordBytes (Roadmap.Controls.toyFixed.hash first)).take 4
def packet (first second : Roadmap.Bytes) (a b : Roadmap.Word) : Roadmap.Bytes :=
 selectorPrefix first++AbiEntry.encodeArgs (abiValues first second a b)

theorem actual_expression (p : Roadmap.Pipeline) (static : Bool)
 (first second : Roadmap.Bytes) (a b : Roadmap.Word) :
 (evalE (global p) {frame with static:=static} 9 (.abiEncode .encodeWithSignature arguments)).run
 (locals a b,state first second)=
 (.ok (.val (.memRef rfl 3)),(locals a b,SourceKeccak.afterLiteral (state first second) (packet first second a b))) :=
 expression_run (global p) {frame with static:=static} 0 .here _ _ (lookups a b)
 first (signature_memory first second a b) (represented first second a b)

theorem actual_rethrow (p : Roadmap.Pipeline) (static : Bool)
 (first second : Roadmap.Bytes) (a b : Roadmap.Word) (statementFuel : Nat) :
 (SourceRethrow.fromExpression (global p) {frame with static:=static} 9 (statementFuel+1)
  (.abiEncode .encodeWithSignature arguments)).run (locals a b,state first second)=
 (.error (.revert (packet first second a b)),(locals a b,SourceKeccak.afterLiteral (state first second) (packet first second a b))) :=
 rethrow_run (global p) {frame with static:=static} 0 statementFuel .here _ _ (lookups a b)
 first (signature_memory first second a b) (represented first second a b)

theorem signature_preserved (first second : Roadmap.Bytes) (a b : Roadmap.Word) :
 LiteralFailureDynamicListError.represented (locals a b)
 (SourceKeccak.afterLiteral (state first second) (packet first second a b)) .here first :=
 LiteralFailureSignatureBytes.reference_preserved _ _ _ _ _ (signature_memory first second a b)

theorem inputs_preserved (first second : Roadmap.Bytes) (a b : Roadmap.Word) :
 LiteralFailureMixedEncoding.Represented
 (SourceKeccak.afterLiteral (state first second) (packet first second a b))
 (values a b) (abiValues first second a b) (LiteralFailureMixedEncodingControls.parts first second a b) :=
 LiteralFailureMixedExpression.fields_after _ _ (represented first second a b)

theorem fresh (first second : Roadmap.Bytes) (a b : Roadmap.Word) :
 (SourceKeccak.afterLiteral (state first second) (packet first second a b)).heap.get 3=
 some ⟨.bytes .memory,.bytes (packet first second a b)⟩ := SourceKeccak.allocated _ _

theorem pinned_prefix (p : Roadmap.Pipeline) (first : Roadmap.Bytes) :
 selectorPrefix first=(Semantics.wordBytes (keccakBytes (first.map (fun b=>(b.toNat : Int)))).1.toNat).take 4 :=
 SourceAbi.signature_prefix_transport (global p) Roadmap.Controls.toyFixed_keccak first

theorem signature_only (p : Roadmap.Pipeline) (first second : Roadmap.Bytes) (a b : Roadmap.Word) :
 (evalE (global p) frame 5 (.abiEncode .encodeWithSignature (.cons (.local .here) .nil))).run
 (locals a b,state first second)=
 (.ok (.val (.memRef rfl 3)),(locals a b,SourceKeccak.afterLiteral (state first second) (selectorPrefix first))) := by
 have result := expression_run (global p) frame 0 .here (locals a b) (state first second)
  LiteralFailureMixedExpression.LocalArgs.nil first (signature_memory first second a b)
  LiteralFailureMixedEncoding.Represented.nil
 simpa only [AbiEntry.encodeArgs,AbiEntry.Vals.parts,AbiEntry.assemble,AbiEntry.assemble.go,
  List.foldl_nil,List.append_nil] using result

theorem full_hash_wrong (first second : Roadmap.Bytes) (a b : Roadmap.Word) :
 packet first second a b≠wordBytes (Roadmap.Controls.toyFixed.hash first)++AbiEntry.encodeArgs (abiValues first second a b) := by
 intro equal
 have lengths := congrArg List.length equal
 simp only [packet,selectorPrefix,List.length_append,List.length_take,wordBytes_length] at lengths
 omega

theorem timeout_after_allocation (first second : Roadmap.Bytes) (a b : Roadmap.Word) :
 (SourceRethrow.fromExpression (global .legacy) frame 9 0 (.abiEncode .encodeWithSignature arguments)).run
 (locals a b,state first second)=
 (.error .timeout,(locals a b,SourceKeccak.afterLiteral (state first second) (packet first second a b))) :=
 statement_timeout (global .legacy) frame 0 .here _ _ (lookups a b)
 first (signature_memory first second a b) (represented first second a b)

theorem no_argument_fuel (p : Roadmap.Pipeline) (first second : Roadmap.Bytes) (a b : Roadmap.Word) :
 (evalE (global p) frame 1 (.abiEncode .encodeWithSignature arguments)).run (locals a b,state first second)=
 (.error .timeout,(locals a b,state first second)) := by rfl

def render (bs : Roadmap.Bytes) := "["++String.intercalate "," (bs.map (fun b=>toString b.toNat))++"]"
def observe (p : Roadmap.Pipeline) (rethrow : Bool) (first second : Roadmap.Bytes) (a b : Roadmap.Word) : String :=
 if rethrow then
  let result := (SourceRethrow.fromExpression (global p) frame 9 1 (.abiEncode .encodeWithSignature arguments)).run
   (locals a b,state first second)
  match result.1 with
  | .error (.revert bs) => "{\"cursor\":"++toString result.2.2.heap.next++",\"bytes\":"++render bs++"}"
  | _ => "{\"bad_run\":true}"
 else
  let result := (evalE (global p) frame 9 (.abiEncode .encodeWithSignature arguments)).run (locals a b,state first second)
  match result.1 with
  | .ok (.val (.memRef _ address)) =>
   match result.2.2.heap.get address with
   | some ⟨_,.bytes bs⟩ => "{\"pointer\":"++toString address++",\"cursor\":"++toString result.2.2.heap.next++",\"bytes\":"++render bs++"}"
   | _ => "{\"bad_heap\":true}"
  | _ => "{\"bad_run\":true}"
def observations (p : Roadmap.Pipeline) (rethrow : Bool) : List String :=
 [observe p rethrow [] [] ⟨0,by decide +kernel⟩ ⟨2^256-1,by omega⟩,
  observe p rethrow [0,255] [128] x y,
  observe p rethrow (List.replicate 31 255) (List.replicate 32 0) y x,
  observe p rethrow (List.replicate 33 128) [] ⟨2^255,by decide +kernel⟩ y,
  observe p rethrow (List.replicate 33 128) (List.replicate 33 128) ⟨2^256-1,by omega⟩ ⟨2^255,by decide +kernel⟩]
#eval IO.println ("MIXED_SIGNATURE_LEGACY=["++String.intercalate "," (observations .legacy false)++"]")
#eval IO.println ("MIXED_SIGNATURE_VIAIR=["++String.intercalate "," (observations .viaIR false)++"]")
#eval IO.println ("MIXED_SIGNATURE_RETHROW_LEGACY=["++String.intercalate "," (observations .legacy true)++"]")
#eval IO.println ("MIXED_SIGNATURE_RETHROW_VIAIR=["++String.intercalate "," (observations .viaIR true)++"]")
#print axioms arguments_run
#print axioms expression_run
#print axioms rethrow_run
#print axioms statement_timeout
#print axioms lookups
#print axioms signature_memory
#print axioms actual_expression
#print axioms actual_rethrow
#print axioms signature_preserved
#print axioms inputs_preserved
#print axioms fresh
#print axioms pinned_prefix
#print axioms signature_only
#print axioms full_hash_wrong
#print axioms timeout_after_allocation
#print axioms no_argument_fuel
end Solidity.Lowering.V08.LiteralFailureMixedSignatureControls
