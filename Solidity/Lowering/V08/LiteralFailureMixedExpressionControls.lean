import Solidity.Lowering.V08.LiteralFailureMixedExpression
import Solidity.Lowering.V08.LiteralFailureMixedEncodingControls
namespace Solidity.Lowering.V08.LiteralFailureMixedExpressionControls
open Solidity Source
open LiteralFailureMixedExpression
open LiteralFailureMixedEncodingControls (types shapes parameters locals values abiValues parts represented packet x y)
open SourceCustomErrorControls (E frame global)
open LiteralFailureDynamicReturnControls (state)

def arguments : RArgs E parameters types :=
 .cons (.local .here) (.cons (.local (.there .here))
  (.cons (.local (.there (.there .here))) (.cons (.local (.there (.there (.there .here)))) .nil)))

theorem lookups (a b : Roadmap.Word) : LocalArgs (locals a b) arguments (values a b) :=
 .cons .here (.cons (.there .here) (.cons (.there (.there .here))
  (.cons (.there (.there (.there .here))) .nil)))

theorem actual_expression (p : Roadmap.Pipeline) (static : Bool)
 (first second : Roadmap.Bytes) (a b : Roadmap.Word) :
 (evalE (global p) {frame with static:=static} 8 (.abiEncode .encode arguments)).run
 (locals a b,state first second)=
 (.ok (.val (.memRef rfl 3)),(locals a b,SourceKeccak.afterLiteral (state first second) (packet first second a b))) :=
 expression_run (global p) {frame with static:=static} 0 _ _ (lookups a b) (represented first second a b)

theorem actual_rethrow (p : Roadmap.Pipeline) (static : Bool)
 (first second : Roadmap.Bytes) (a b : Roadmap.Word) (statementFuel : Nat) :
 (SourceRethrow.fromExpression (global p) {frame with static:=static} 8 (statementFuel+1)
  (.abiEncode .encode arguments)).run (locals a b,state first second)=
 (.error (.revert (packet first second a b)),
  (locals a b,SourceKeccak.afterLiteral (state first second) (packet first second a b))) :=
 rethrow_run (global p) {frame with static:=static} 0 statementFuel _ _ (lookups a b) (represented first second a b)

theorem fresh (first second : Roadmap.Bytes) (a b : Roadmap.Word) :
 (SourceKeccak.afterLiteral (state first second) (packet first second a b)).heap.get 3=
 some ⟨.bytes .memory,.bytes (packet first second a b)⟩ := SourceKeccak.allocated _ _

theorem allocator (first second : Roadmap.Bytes) (a b : Roadmap.Word) :
 (state first second).heap.next=3 ∧
 (SourceKeccak.afterLiteral (state first second) (packet first second a b)).heap.next=4 := ⟨rfl,rfl⟩

theorem old_alias (first second : Roadmap.Bytes) (a b : Roadmap.Word) :
 (SourceKeccak.afterLiteral (state first second) (packet first second a b)).heap.get 0=
 some ⟨.bytes .memory,.bytes [0,255]⟩ := old_object _ _ 0 _ rfl

theorem inputs_retained (first second : Roadmap.Bytes) (a b : Roadmap.Word) :
 LiteralFailureMixedEncoding.Represented
  (SourceKeccak.afterLiteral (state first second) (packet first second a b))
  (values a b) (abiValues first second a b) (parts first second a b) :=
 fields_after _ _ (represented first second a b)

theorem too_little_statement (first second : Roadmap.Bytes) (a b : Roadmap.Word) :
 (SourceRethrow.fromExpression (global .legacy) frame 8 0 (.abiEncode .encode arguments)).run
 (locals a b,state first second)=
 (.error .timeout,(locals a b,SourceKeccak.afterLiteral (state first second) (packet first second a b))) :=
 statement_timeout (global .legacy) frame 0 _ _ (lookups a b) (represented first second a b)

theorem too_little_expression (first second : Roadmap.Bytes) (a b : Roadmap.Word) :
 (SourceRethrow.fromExpression (global .legacy) frame 0 1 (.abiEncode .encode arguments)).run
 (locals a b,state first second)=(.error .timeout,(locals a b,state first second)) :=
 expression_timeout _ _ _ _ _ _

theorem stale_pointer (first second : Roadmap.Bytes) (a b : Roadmap.Word) :
 (evalE (global .legacy) frame 8 (.abiEncode .encode arguments)).run (locals a b,state first second)≠
 (.ok (.val (.memRef rfl 1)),(locals a b,SourceKeccak.afterLiteral (state first second) (packet first second a b))) := by
 rw [actual_expression]
 intro equal
 cases equal

theorem no_allocator_growth (first second : Roadmap.Bytes) (a b : Roadmap.Word) :
 (SourceKeccak.afterLiteral (state first second) (packet first second a b)).heap.next≠3 := by
 change (4 : Nat)≠3
 decide +kernel

def render (bs : Roadmap.Bytes) : String :=
 "["++String.intercalate "," (bs.map (fun b=>toString b.toNat))++"]"
def observe (p : Roadmap.Pipeline) (first second : Roadmap.Bytes) (a b : Roadmap.Word) : String :=
 let result := (evalE (global p) frame 8 (.abiEncode .encode arguments)).run (locals a b,state first second)
 match result.1 with
 | .ok (.val (.memRef _ address)) =>
  match result.2.2.heap.get address with
  | some ⟨_,.bytes bs⟩ => "{\"pointer\":"++toString address++",\"cursor\":"++toString result.2.2.heap.next++",\"bytes\":"++render bs++"}"
  | _ => "{\"bad_heap\":true}"
 | _ => "{\"bad_run\":true}"
def observations (p : Roadmap.Pipeline) : List String :=
 [observe p [] [] ⟨0,by decide +kernel⟩ ⟨2^256-1,by omega⟩,
  observe p [0,255] [128] x y,
  observe p (List.replicate 31 255) (List.replicate 32 0) y x,
  observe p (List.replicate 33 128) [] ⟨2^255,by decide +kernel⟩ y,
  observe p (List.replicate 33 128) (List.replicate 33 128) ⟨2^256-1,by omega⟩ ⟨2^255,by decide +kernel⟩]
#eval IO.println ("MIXED_EXPRESSION_LEGACY=["++String.intercalate "," (observations .legacy)++"]")
#eval IO.println ("MIXED_EXPRESSION_VIAIR=["++String.intercalate "," (observations .viaIR)++"]")
#print axioms arguments_run
#print axioms expression_run
#print axioms old_object
#print axioms fields_after
#print axioms rethrow_run
#print axioms statement_timeout
#print axioms expression_timeout
#print axioms lookups
#print axioms actual_expression
#print axioms actual_rethrow
#print axioms fresh
#print axioms allocator
#print axioms old_alias
#print axioms inputs_retained
#print axioms too_little_statement
#print axioms too_little_expression
#print axioms stale_pointer
#print axioms no_allocator_growth
end Solidity.Lowering.V08.LiteralFailureMixedExpressionControls
