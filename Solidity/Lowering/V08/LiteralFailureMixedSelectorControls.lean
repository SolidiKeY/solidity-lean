import Solidity.Lowering.V08.LiteralFailureMixedSelector
import Solidity.Lowering.V08.LiteralFailureMixedEncodingControls
namespace Solidity.Lowering.V08.LiteralFailureMixedSelectorControls
open Solidity Source
open LiteralFailureMixedSelector
open LiteralFailureMixedEncodingControls (types parameters values abiValues represented x y)
open LiteralFailureDynamicReturnControls (state)
open SourceCustomErrorControls (E frame global)

def caller (selector : Roadmap.Bytes) (extent : selector.length=4) (a b : Roadmap.Word) :
 Locals E.layout (Selector::parameters) :=
 .cons (.fixedBytes selector extent) (LiteralFailureMixedEncodingControls.locals a b)
def tailArgs : RArgs E (Selector::parameters) types :=
 .cons (.local (.there .here)) (.cons (.local (.there (.there .here)))
  (.cons (.local (.there (.there (.there .here))))
   (.cons (.local (.there (.there (.there (.there .here))))) .nil)))
def arguments : RArgs E (Selector::parameters) (Selector::types) := .cons (.local .here) tailArgs

theorem lookups (selector : Roadmap.Bytes) (extent : selector.length=4) (a b : Roadmap.Word) :
 LiteralFailureMixedExpression.LocalArgs (caller selector extent a b) tailArgs (values a b) :=
 .cons (.there .here) (.cons (.there (.there .here))
  (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil)))

def packet (selector first second : Roadmap.Bytes) (a b : Roadmap.Word) : Roadmap.Bytes :=
 selector++AbiEntry.encodeArgs (abiValues first second a b)

theorem actual_expression (p : Roadmap.Pipeline) (static : Bool)
 (selector first second : Roadmap.Bytes) (extent : selector.length=4) (a b : Roadmap.Word) :
 (evalE (global p) {frame with static:=static} 9 (.abiEncode .encodeWithSelector arguments)).run
 (caller selector extent a b,state first second)=
 (.ok (.val (.memRef rfl 3)),(caller selector extent a b,
  SourceKeccak.afterLiteral (state first second) (packet selector first second a b))) :=
 expression_run (global p) {frame with static:=static} 0 .here _ _
 (lookups selector extent a b) (represented first second a b)

theorem actual_rethrow (p : Roadmap.Pipeline) (selector first second : Roadmap.Bytes)
 (extent : selector.length=4) (a b : Roadmap.Word) :
 (SourceRethrow.fromExpression (global p) frame 9 1 (.abiEncode .encodeWithSelector arguments)).run
 (caller selector extent a b,state first second)=
 (.error (.revert (packet selector first second a b)),(caller selector extent a b,
  SourceKeccak.afterLiteral (state first second) (packet selector first second a b))) :=
 rethrow_run (global p) frame 0 0 .here _ _ (lookups selector extent a b) (represented first second a b)

theorem timeout_after_allocation (selector first second : Roadmap.Bytes)
 (extent : selector.length=4) (a b : Roadmap.Word) :
 (SourceRethrow.fromExpression (global .legacy) frame 9 0 (.abiEncode .encodeWithSelector arguments)).run
 (caller selector extent a b,state first second)=
 (.error .timeout,(caller selector extent a b,
  SourceKeccak.afterLiteral (state first second) (packet selector first second a b))) :=
 statement_timeout (global .legacy) frame 0 .here _ _ (lookups selector extent a b) (represented first second a b)

theorem only_selector (p : Roadmap.Pipeline) (selector first second : Roadmap.Bytes)
 (extent : selector.length=4) (a b : Roadmap.Word) :
 (evalE (global p) frame 5 (.abiEncode .encodeWithSelector (.cons (.local .here) .nil))).run
 (caller selector extent a b,state first second)=
 (.ok (.val (.memRef rfl 3)),(caller selector extent a b,SourceKeccak.afterLiteral (state first second) selector)) := by
 have result := expression_run (global p) frame 0 .here (caller selector extent a b) (state first second)
  (LiteralFailureMixedExpression.LocalArgs.nil)
  (LiteralFailureMixedEncoding.Represented.nil)
 simpa only [caller,Locals.get,Source.Val.bytesOf,AbiEntry.encodeArgs,AbiEntry.Vals.parts,
  AbiEntry.assemble,AbiEntry.assemble.go,List.foldl_nil,List.append_nil] using result

theorem inputs_preserved (selector first second : Roadmap.Bytes) (a b : Roadmap.Word) :
 LiteralFailureMixedEncoding.Represented
  (SourceKeccak.afterLiteral (state first second) (packet selector first second a b))
  (values a b) (abiValues first second a b) (LiteralFailureMixedEncodingControls.parts first second a b) :=
 LiteralFailureMixedExpression.fields_after _ _ (represented first second a b)

theorem relative_offset : AbiEntry.load (packet [8,195,121,160] [0,255] [128] x y) 4=128 := by decide +kernel

theorem wrong_absolute_offset : AbiEntry.load (packet [8,195,121,160] [0,255] [128] x y) 4≠132 := by decide +kernel

/-- Existing decoder observation of these supplied selector bytes, not a
same-invocation/catch-dispatch or declared custom-error agreement theorem. -/
theorem error_observation : Semantics.decodeError (packet [8,195,121,160] [0,255] [128] x y)=some [0,255] := by decide +kernel

theorem reason_observation : CatchKind.reason.decode (packet [8,195,121,160] [0,255] [128] x y)=some [0,255] := by decide +kernel

theorem wrong_selector : Semantics.decodeError (packet [1,2,3,4] [0,255] [128] x y)=none := by decide +kernel

theorem truncated : Semantics.decodeError ((packet [8,195,121,160] [0,255] [128] x y).take 4)=none := by decide +kernel

def render (bs : Roadmap.Bytes) := "["++String.intercalate "," (bs.map (fun b=>toString b.toNat))++"]"
def observe (p : Roadmap.Pipeline) (rethrow : Bool) (selector first second : Roadmap.Bytes)
 (extent : selector.length=4) (a b : Roadmap.Word) : String :=
 if rethrow then
  let result := (SourceRethrow.fromExpression (global p) frame 9 1 (.abiEncode .encodeWithSelector arguments)).run
   (caller selector extent a b,state first second)
  match result.1 with
  | .error (.revert bs) => "{\"cursor\":"++toString result.2.2.heap.next++",\"bytes\":"++render bs++"}"
  | _ => "{\"bad_run\":true}"
 else
  let result := (evalE (global p) frame 9 (.abiEncode .encodeWithSelector arguments)).run
   (caller selector extent a b,state first second)
  match result.1 with
  | .ok (.val (.memRef _ address)) =>
   match result.2.2.heap.get address with
   | some ⟨_,.bytes bs⟩ => "{\"pointer\":"++toString address++",\"cursor\":"++toString result.2.2.heap.next++",\"bytes\":"++render bs++"}"
   | _ => "{\"bad_heap\":true}"
  | _ => "{\"bad_run\":true}"
def observations (p : Roadmap.Pipeline) (rethrow : Bool) : List String :=
 [observe p rethrow [0,0,0,0] [] [] rfl ⟨0,by decide +kernel⟩ ⟨2^256-1,by omega⟩,
  observe p rethrow [8,195,121,160] [0,255] [128] rfl x y,
  observe p rethrow [255,0,128,1] (List.replicate 31 255) (List.replicate 32 0) rfl y x,
  observe p rethrow [78,72,123,113] (List.replicate 33 128) [] rfl ⟨2^255,by decide +kernel⟩ y,
  observe p rethrow [1,2,3,4] (List.replicate 33 128) (List.replicate 33 128) rfl ⟨2^256-1,by omega⟩ ⟨2^255,by decide +kernel⟩]
#eval IO.println ("MIXED_SELECTOR_LEGACY=["++String.intercalate "," (observations .legacy false)++"]")
#eval IO.println ("MIXED_SELECTOR_VIAIR=["++String.intercalate "," (observations .viaIR false)++"]")
#eval IO.println ("MIXED_SELECTOR_RETHROW_LEGACY=["++String.intercalate "," (observations .legacy true)++"]")
#eval IO.println ("MIXED_SELECTOR_RETHROW_VIAIR=["++String.intercalate "," (observations .viaIR true)++"]")
#print axioms arguments_run
#print axioms expression_run
#print axioms rethrow_run
#print axioms statement_timeout
#print axioms lookups
#print axioms actual_expression
#print axioms actual_rethrow
#print axioms timeout_after_allocation
#print axioms only_selector
#print axioms inputs_preserved
#print axioms relative_offset
#print axioms wrong_absolute_offset
#print axioms error_observation
#print axioms reason_observation
#print axioms wrong_selector
#print axioms truncated
end Solidity.Lowering.V08.LiteralFailureMixedSelectorControls
