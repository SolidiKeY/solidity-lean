import Solidity.Lowering.V08.LiteralFailureEncodedRethrow
import Solidity.Lowering.V08.LiteralFailureSelectorBytesControls
import Solidity.Lowering.V08.LiteralFailureSignatureBytesControls

namespace Solidity.Lowering.V08.LiteralFailureEncodedRethrowControls
open Solidity Source LiteralFailureDynamicListError
open LiteralFailureDynamicListErrorControls LiteralFailureEncodedRethrow

theorem selector_client (pipeline : Roadmap.Pipeline) (selector first second : Roadmap.Bytes)
 (extent : selector.length = 4) :
 (SourceRethrow.fromExpression (global 3 pipeline) frame 8 1
  (.abiEncode .encodeWithSelector (LiteralFailureSelectorBytes.args .here
   LiteralFailureSelectorBytesControls.tailRefs))).run
 (LiteralFailureSelectorBytesControls.caller selector extent,state 3 first second) =
 (.error (.revert (LiteralFailureSelectorBytesControls.packet selector first second)),
  (LiteralFailureSelectorBytesControls.caller selector extent,
   SourceKeccak.afterLiteral (state 3 first second)
    (LiteralFailureSelectorBytesControls.packet selector first second))) :=
 selector_rethrow (global 3 pipeline) frame 0 0 .here _ [first,second,first] _ _
  (LiteralFailureSelectorBytesControls.memory_tail selector first second extent)

theorem signature_client (pipeline : Roadmap.Pipeline) (first second : Roadmap.Bytes) :
 (SourceRethrow.fromExpression (global 3 pipeline) frame 8 1
  (.abiEncode .encodeWithSignature (LiteralFailurePackedBytes.args (.here::refs)))).run
 (locals 3,state 3 first second) =
 (.error (.revert (LiteralFailureSignatureBytesControls.packet first second)),
  (locals 3,SourceKeccak.afterLiteral (state 3 first second)
   (LiteralFailureSignatureBytesControls.packet first second))) :=
 signature_rethrow (global 3 pipeline) frame 0 0 .here refs first [first,second,first] _ _
  ⟨1,rfl,.inl rfl⟩ (memory_three first second)

theorem empty_packed_client (pipeline : Roadmap.Pipeline) (first second : Roadmap.Bytes) :
 (SourceRethrow.fromExpression (global 3 pipeline) frame 4 1
  (.abiEncode .encodePacked (LiteralFailurePackedBytes.args []))).run (locals 3,state 3 first second) =
 (.error (.revert []),(locals 3,SourceKeccak.afterLiteral (state 3 first second) [])) :=
 packed_rethrow (global 3 pipeline) frame 0 0 [] [] _ _ trivial

theorem statement_timeout_not_revert (pipeline : Roadmap.Pipeline) (selector first second : Roadmap.Bytes)
 (extent : selector.length = 4) :
 ((SourceRethrow.fromExpression (global 3 pipeline) frame 8 0
  (.abiEncode .encodeWithSelector (LiteralFailureSelectorBytes.args .here
   LiteralFailureSelectorBytesControls.tailRefs))).run
 (LiteralFailureSelectorBytesControls.caller selector extent,state 3 first second)).1 ≠
 .error (.revert (LiteralFailureSelectorBytesControls.packet selector first second)) := by
 have execution := selector_statement_timeout (global 3 pipeline) frame 0 .here _ [first,second,first] _ _
  (LiteralFailureSelectorBytesControls.memory_tail selector first second extent)
 simp only [LiteralFailureSelectorBytesControls.tailRefs,List.length_cons,List.length_nil,Nat.add_zero] at execution ⊢
 rw [execution]
 intro bad
 cases bad

theorem statement_timeout_cursor (pipeline : Roadmap.Pipeline) (selector first second : Roadmap.Bytes)
 (extent : selector.length = 4) :
 ((SourceRethrow.fromExpression (global 3 pipeline) frame 8 0
  (.abiEncode .encodeWithSelector (LiteralFailureSelectorBytes.args .here
   LiteralFailureSelectorBytesControls.tailRefs))).run
 (LiteralFailureSelectorBytesControls.caller selector extent,state 3 first second)).2.2.heap.next = 4 := by
 have execution := selector_statement_timeout (global 3 pipeline) frame 0 .here _ [first,second,first] _ _
  (LiteralFailureSelectorBytesControls.memory_tail selector first second extent)
 simp only [LiteralFailureSelectorBytesControls.tailRefs,List.length_cons,List.length_nil,Nat.add_zero] at execution ⊢
 rw [execution]
 rfl

def selectorRun (selector first second : Roadmap.Bytes) (extent : selector.length = 4)
 (expressionFuel statementFuel : Nat) :=
 (SourceRethrow.fromExpression (global 3 .legacy) frame expressionFuel statementFuel
  (.abiEncode .encodeWithSelector (LiteralFailureSelectorBytes.args .here
   LiteralFailureSelectorBytesControls.tailRefs))).run
 (LiteralFailureSelectorBytesControls.caller selector extent,state 3 first second)
def selectorOnlyRun :=
 (SourceRethrow.fromExpression (global 3 .legacy) frame 5 1
  (.abiEncode .encodeWithSelector (LiteralFailureSelectorBytes.args .here []))).run
 (LiteralFailureSelectorBytesControls.caller [0,0,0,0] rfl,state 3 [] [])
def signatureRun :=
 (SourceRethrow.fromExpression (global 3 .legacy) frame 8 1
  (.abiEncode .encodeWithSignature (LiteralFailurePackedBytes.args (.here::refs)))).run
 (locals 3,state 3 [0,255] [128])
def packedRun :=
 (SourceRethrow.fromExpression (global 3 .legacy) frame 7 1
  (.abiEncode .encodePacked (LiteralFailurePackedBytes.args refs))).run
 (locals 3,state 3 [0,255] [128])
def emptyPackedRun :=
 (SourceRethrow.fromExpression (global 3 .legacy) frame 4 1
  (.abiEncode .encodePacked (LiteralFailurePackedBytes.args []))).run
 (locals 3,state 3 [] [])

def capture {α : Type} : Except Source.Halt α → String
 | .error (.revert bytes) => render bytes
 | _ => "NONREVERT"
def classify {α : Type} : Except Source.Halt α → String
 | .error (.revert _) => "revert"
 | .error .timeout => "timeout"
 | .ok _ => "ok"
 | _ => "other"

#eval String.intercalate "\n"
 [capture selectorOnlyRun.1,
  capture (selectorRun [222,173,190,239] [] [] rfl 8 1).1,
  capture (selectorRun [0,255,128,1] [0,255] [128] rfl 8 1).1,
  capture (selectorRun [255,0,255,0] (List.replicate 31 0) [] rfl 8 1).1,
  capture (selectorRun [1,2,3,4] (List.replicate 32 255) (List.replicate 33 128) rfl 8 1).1,
  capture (selectorRun [4,3,2,1] (List.replicate 33 128) (List.replicate 32 255) rfl 8 1).1,
  capture emptyPackedRun.1,capture signatureRun.1,capture packedRun.1]
#eval String.intercalate "\n"
 [classify (selectorRun [0,255,128,1] [0,255] [128] rfl 8 1).1 ++ "," ++
   toString (selectorRun [0,255,128,1] [0,255] [128] rfl 8 1).2.2.heap.next,
  classify (selectorRun [0,255,128,1] [0,255] [128] rfl 8 0).1 ++ "," ++
   toString (selectorRun [0,255,128,1] [0,255] [128] rfl 8 0).2.2.heap.next,
  classify (selectorRun [0,255,128,1] [0,255] [128] rfl 0 1).1 ++ "," ++
   toString (selectorRun [0,255,128,1] [0,255] [128] rfl 0 1).2.2.heap.next,
  classify emptyPackedRun.1 ++ "," ++ toString emptyPackedRun.2.2.heap.next,
  classify signatureRun.1 ++ "," ++ toString signatureRun.2.2.heap.next,
  classify packedRun.1 ++ "," ++ toString packedRun.2.2.heap.next]
#print axioms selector_rethrow
#print axioms signature_rethrow
#print axioms packed_rethrow
#print axioms selector_statement_timeout
#print axioms selector_expression_timeout
#print axioms selector_client
#print axioms signature_client
#print axioms empty_packed_client
#print axioms statement_timeout_not_revert
#print axioms statement_timeout_cursor
end Solidity.Lowering.V08.LiteralFailureEncodedRethrowControls
