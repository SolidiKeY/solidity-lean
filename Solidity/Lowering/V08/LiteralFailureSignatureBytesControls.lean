import Solidity.Lowering.V08.LiteralFailureSignatureBytes
import Solidity.Lowering.V08.LiteralFailureDynamicListErrorControls

namespace Solidity.Lowering.V08.LiteralFailureSignatureBytesControls
open Solidity Source LiteralFailureDynamicListError
open LiteralFailureDynamicListErrorControls

def packet (first second : Roadmap.Bytes) : Roadmap.Bytes :=
 (wordBytes (Roadmap.Controls.toyFixed.hash first)).take 4 ++
 AbiEntry.encodeArgs (abiValues [first,second,first])

theorem populated (pipeline : Roadmap.Pipeline) (first second : Roadmap.Bytes) :
 (evalE (global 3 pipeline) frame 8 (.abiEncode .encodeWithSignature
   (LiteralFailurePackedBytes.args (.here::refs)))).run (locals 3,state 3 first second) =
 (.ok (.val (.memRef rfl 3)),(locals 3,SourceKeccak.afterLiteral (state 3 first second) (packet first second))) := by
 exact LiteralFailureSignatureBytes.expression_run (global 3 pipeline) frame 0 .here refs first
  [first,second,first] (locals 3) (state 3 first second) ⟨1,rfl,.inl rfl⟩ (memory_three first second)

theorem signature_only (pipeline : Roadmap.Pipeline) (first second : Roadmap.Bytes) :
 (evalE (global 3 pipeline) frame 5 (.abiEncode .encodeWithSignature
   (LiteralFailurePackedBytes.args [.here]))).run (locals 3,state 3 first second) =
 (.ok (.val (.memRef rfl 3)),(locals 3,SourceKeccak.afterLiteral (state 3 first second)
  ((wordBytes (Roadmap.Controls.toyFixed.hash first)).take 4))) := by
 have execution := LiteralFailureSignatureBytes.expression_run (global 3 pipeline) frame 0 .here [] first
  [] (locals 3) (state 3 first second) ⟨1,rfl,.inl rfl⟩ trivial
 simpa only [abiValues,AbiEntry.encodeArgs,AbiEntry.Vals.parts,AbiEntry.assemble,
  AbiEntry.assemble.go,List.foldl_nil,List.append_nil] using execution

theorem source_alias_survives (first second : Roadmap.Bytes) :
 represented (locals 3) (SourceKeccak.afterLiteral (state 3 first second) (packet first second)) .here first :=
 LiteralFailureSignatureBytes.reference_preserved _ _ _ _ _ ⟨1,rfl,.inl rfl⟩

theorem old_object_survives (first second : Roadmap.Bytes) :
 (SourceKeccak.afterLiteral (state 3 first second) (packet first second)).heap.get 0 =
 some ⟨.bytes .memory,.bytes [9,7]⟩ :=
 LiteralFailureSignatureBytes.object_preserved _ _ _ _ rfl

theorem fresh_output (first second : Roadmap.Bytes) :
 (SourceKeccak.afterLiteral (state 3 first second) (packet first second)).heap.get 3 =
 some ⟨.bytes .memory,.bytes (packet first second)⟩ :=
 SourceKeccak.allocated _ _

theorem pinned_prefix (first : Roadmap.Bytes) :
 (wordBytes (Roadmap.Controls.toyFixed.hash first)).take 4 =
 (Semantics.wordBytes (keccakBytes (first.map (fun byte => (byte.toNat : Int)))).1.toNat).take 4 :=
 SourceAbi.signature_prefix_transport (global 3 .legacy) Roadmap.Controls.toyFixed_keccak first

theorem rejects_full_hash_prefix (first second : Roadmap.Bytes) :
 packet first second ≠ wordBytes (Roadmap.Controls.toyFixed.hash first) ++
 AbiEntry.encodeArgs (abiValues [first,second,first]) := by
 intro bad
 have lengths := congrArg List.length bad
 simp only [packet,List.length_append,List.length_take,wordBytes_length] at lengths
 omega

theorem rejects_swapped_body (lead : Roadmap.Bytes) :
 lead ++ AbiEntry.encodeArgs (abiValues [[0,255],[128],[0,255]]) ≠
 lead ++ AbiEntry.encodeArgs (abiValues [[0,255],[0,255],[128]]) := by
 intro bad
 exact wrong_order (List.append_cancel_left bad)

theorem no_argument_fuel (pipeline : Roadmap.Pipeline) (first second : Roadmap.Bytes) :
 (evalE (global 3 pipeline) frame 1 (.abiEncode .encodeWithSignature
  (LiteralFailurePackedBytes.args (.here::refs)))).run (locals 3,state 3 first second) =
 (.error .timeout,(locals 3,state 3 first second)) := by rfl

def samples : List (Roadmap.Bytes × Roadmap.Bytes) :=
 [([],[]),([0,255],[128]),(List.replicate 31 0,[]),
  (List.replicate 32 255,List.replicate 33 128),
  (List.replicate 33 128,List.replicate 32 255)]
#eval String.intercalate "\n" ((render ((wordBytes (Roadmap.Controls.toyFixed.hash [])).take 4)) ::
 (samples.map (fun sample => render (packet sample.1 sample.2))))
#print axioms LiteralFailureSignatureBytes.signature_read
#print axioms LiteralFailureSignatureBytes.expression_run
#print axioms LiteralFailureSignatureBytes.object_preserved
#print axioms LiteralFailureSignatureBytes.reference_preserved
#print axioms populated
#print axioms signature_only
#print axioms source_alias_survives
#print axioms old_object_survives
#print axioms fresh_output
#print axioms pinned_prefix
#print axioms rejects_full_hash_prefix
#print axioms rejects_swapped_body
#print axioms no_argument_fuel
end Solidity.Lowering.V08.LiteralFailureSignatureBytesControls
