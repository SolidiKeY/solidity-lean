import Solidity.Lowering.V08.SourceAbi
import Solidity.Lowering.V08.SourceCustomErrorControls
import Solidity.Lowering.V08.CryptoControls
import Solidity.Lowering.V08.SourceTransient
namespace Solidity.Lowering.V08.SourceAbiControls
open Solidity Source
open SourceCustomErrorControls

def long33 : Roadmap.Bytes := List.replicate 33 254

theorem literal_complete (pipeline : Roadmap.Pipeline) (static packed : Bool) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) {frame with static:=static} 4 (SourceAbi.literal packed bytes)).run
      (locals,populated) =
      (.ok (.val (.memRef rfl 1)),(locals,SourceKeccak.afterLiteral populated
        (if packed then bytes else Source.abiLayout [(true,bytes)]))) :=
  SourceAbi.literal_execution (global pipeline) {frame with static:=static} 0 packed bytes locals populated

theorem literal_vector (packed : Bool) (bytes : Roadmap.Bytes) :
    let data := if packed then bytes else Source.abiLayout [(true,bytes)]
    let final := SourceKeccak.afterLiteral populated data
    (final.ex.world.accounts sender).balance.val = 93 ∧
    (final.ex.world.accounts self).balance.val = 7 ∧
    (final.ex.world.accounts self).code = some 0 ∧
    (final.ex.world.accounts self).nonce = 1 ∧
    (final.ex.world.accounts self).storage.read saved = some (.bool true) ∧
    (final.ex.transient.cells self).read scratch = some (.bool true) ∧
    final.ex.journal.length = 3 ∧ final.heap.next = 2 ∧
    final.heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    final.heap.get 1 = some ⟨.bytes .memory,.bytes data⟩ ∧
    final.events = populated.events ∧ final.logs = populated.logs ∧ final.fnLocals = populated.fnLocals :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem empty_binary_unaligned_lengths :
    ((Source.abiLayout [(true,[])]).length,
      (Source.abiLayout [(true,binary)]).length,
      (Source.abiLayout [(true,long33)]).length) = (64,96,128) := by decide +kernel

theorem literal_cases (pipeline : Roadmap.Pipeline) (static packed : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 4 (SourceAbi.literal packed [])).run (locals,populated) =
      (.ok (.val (.memRef rfl 1)),(locals,SourceKeccak.afterLiteral populated
        (if packed then [] else Source.abiLayout [(true,[])]))) ∧
    (Source.evalE (global pipeline) {frame with static:=static} 4 (SourceAbi.literal packed binary)).run (locals,populated) =
      (.ok (.val (.memRef rfl 1)),(locals,SourceKeccak.afterLiteral populated
        (if packed then binary else Source.abiLayout [(true,binary)]))) ∧
    (Source.evalE (global pipeline) {frame with static:=static} 4 (SourceAbi.literal packed long33)).run (locals,populated) =
      (.ok (.val (.memRef rfl 1)),(locals,SourceKeccak.afterLiteral populated
        (if packed then long33 else Source.abiLayout [(true,long33)]))) :=
  ⟨literal_complete pipeline static packed [],literal_complete pipeline static packed binary,
    literal_complete pipeline static packed long33⟩

def arguments : RArgs E [.bool] [.stringLit binary,.bool,.bool,.stringLit long33,STy.bytes32] :=
  .cons (.str binary) (.cons setFalse (.cons (.local .here)
    (.cons (.str long33) (.cons (SourceKeccak.literal binary) .nil))))
def values (pipeline : Roadmap.Pipeline) : Source.RVals E.layout [.stringLit binary,.bool,.bool,.stringLit long33,STy.bytes32] :=
  .cons (.strLit binary) (.cons (.val (.bool false)) (.cons (.val (.bool false))
    (.cons (.strLit long33) (.cons (.val (digest pipeline)) .nil))))
def data (packed : Bool) (pipeline : Roadmap.Pipeline) : Roadmap.Bytes :=
  if packed then binary ++ [0] ++ [0] ++ long33 ++ Source.wordBytes (digestWord pipeline)
  else Source.abiLayout [(true,binary),(false,zeroWord),(false,zeroWord),(true,long33),
    (false,Source.wordBytes (digestWord pipeline))]

theorem arguments_execute (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalArgs (global pipeline) {frame with static:=static} 16 arguments).run (locals,populated) =
      (.ok (values pipeline),(.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary)) := rfl

theorem digest_word (pipeline : Roadmap.Pipeline) :
    (digest pipeline).word = some ((global pipeline).fixed.hash binary) :=
  SourceAbi.word_bytes_field ((global pipeline).fixed.hash binary)

theorem digestWord_eq (pipeline : Roadmap.Pipeline) : digestWord pipeline = (global pipeline).fixed.hash binary := by
  apply Fin.ext
  simp only [digestWord,Source.fitBytes,List.take_left' (Source.wordBytes_length ((global pipeline).fixed.hash binary)),
    Source.wordBytes_length,Nat.sub_self,List.replicate_zero,List.append_nil,Source.wordBytes_value,
    Source.toWord,Nat.mod_eq_of_lt ((global pipeline).fixed.hash binary).isLt]

theorem encoding_execute (pipeline : Roadmap.Pipeline) (static packed : Bool) :
    (Source.encodeVals {frame with static:=static} 16 packed (values pipeline) : Source.EM E [.bool] _).run
      (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary) =
      (.ok (data packed pipeline),(.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary)) := by
  have wordRead : (digest pipeline).word = some (digestWord pipeline) := by
    rw [digestWord_eq]
    exact digest_word pipeline
  have wordEncoded := SourceAbi.encode_fixed_bytes32 (E:=E) (Γ:=[.bool])
    {frame with static:=static} 16 packed (digest pipeline) (digestWord pipeline) wordRead
  have literalEncoded (bytes : Roadmap.Bytes) :
      (Source.encodeOne {frame with static:=static} 16 packed (.strLit bytes) : Source.EM E [.bool] _) =
        pure (true,bytes) := rfl
  have falseEncoded :
      (Source.encodeOne {frame with static:=static} 16 packed (.val (.bool false)) : Source.EM E [.bool] _) =
        pure (false,if packed then [0] else zeroWord) := by
    cases packed <;> rfl
  unfold data
  generalize wordEquation : digestWord pipeline = word at wordEncoded ⊢
  simp only [values,Source.encodeVals,Source.encodeParts]
  rw [literalEncoded binary,falseEncoded,literalEncoded long33,wordEncoded]
  cases packed <;> simp only [Bool.false_eq_true,↓reduceIte,bind,pure,
    ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,
    List.foldr_cons,List.foldr_nil,List.append_nil,List.append_assoc]

theorem mixed_complete (pipeline : Roadmap.Pipeline) (static packed : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 17
      (.abiEncode (if packed then .encodePacked else .encode) arguments)).run (locals,populated) =
      (.ok (.val (.memRef rfl 2)),(.cons (.bool false) .nil,
        SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary) (data packed pipeline))) :=
  SourceAbi.execute (global pipeline) {frame with static:=static} 16 packed arguments
    locals (.cons (.bool false) .nil) (.cons (.bool false) .nil) populated _ _ (values pipeline) _
    (arguments_execute pipeline static) (encoding_execute pipeline static packed)

theorem mixed_vector (pipeline : Roadmap.Pipeline) (packed : Bool) :
    let final := SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary) (data packed pipeline)
    (final.ex.world.accounts sender).balance.val = 93 ∧
    (final.ex.world.accounts self).balance.val = 7 ∧
    (final.ex.world.accounts self).code = some 0 ∧
    (final.ex.world.accounts self).nonce = 1 ∧
    (final.ex.world.accounts self).storage.read saved = some (.bool true) ∧
    (final.ex.transient.cells self).read scratch = some (.bool true) ∧
    final.ex.journal.length = 3 ∧ final.heap.next = 3 ∧
    final.heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    final.heap.get 1 = some ⟨.bytes .memory,.bytes binary⟩ ∧
    final.heap.get 2 = some ⟨.bytes .memory,.bytes (data packed pipeline)⟩ ∧
    final.events = populated.events ∧ final.logs = populated.logs ∧ final.fnLocals = populated.fnLocals :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩


def reversedArguments : RArgs E [.bool] [.stringLit long33,.bool,.bool,.stringLit binary,STy.bytes32] :=
  .cons (.str long33) (.cons (.local .here) (.cons setFalse
    (.cons (.str binary) (.cons (SourceKeccak.literal binary) .nil))))
def reversedData (pipeline : Roadmap.Pipeline) : Roadmap.Bytes :=
  Source.abiLayout [(true,long33),(false,oneWord),(false,zeroWord),(true,binary),
    (false,Source.wordBytes (digestWord pipeline))]

theorem reversed_execution (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 17 (.abiEncode .encode reversedArguments)).run
      (locals,populated) =
      (.ok (.val (.memRef rfl 2)),(.cons (.bool false) .nil,
        SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary) (reversedData pipeline))) := rfl


theorem complete_offset_words (pipeline : Roadmap.Pipeline) :
    (data false pipeline).take 32 = Source.wordBytes (Source.toWord 160) ∧
    ((data false pipeline).drop 96).take 32 = Source.wordBytes (Source.toWord 224) ∧
    ((reversedData pipeline).drop 96).take 32 = Source.wordBytes (Source.toWord 256) := by
  constructor
  · simp only [data,Bool.false_eq_true,↓reduceIte,SourceAbi.five_parts,SourceAbi.take_word]
  · constructor
    · rw [data]
      simp only [Bool.false_eq_true,↓reduceIte,SourceAbi.five_parts,zeroWord]
      rw [SourceAbi.drop_word _ _ 64,SourceAbi.drop_word _ _ 32,SourceAbi.drop_word _ _ 0,
        List.drop_zero,SourceAbi.take_word]
      rfl
    · rw [reversedData,SourceAbi.five_parts]
      unfold oneWord zeroWord
      rw [SourceAbi.drop_word _ _ 64,SourceAbi.drop_word _ _ 32,SourceAbi.drop_word _ _ 0,
        List.drop_zero,SourceAbi.take_word]
      rfl

theorem mixed_standard_offsets (pipeline : Roadmap.Pipeline) :
    (data false pipeline)[31]? = some 160 ∧ (data false pipeline)[127]? = some 224 := by
  constructor
  · have obs := congrArg (fun bytes : Roadmap.Bytes => bytes[31]?) (complete_offset_words pipeline).1
    simpa only [List.getElem?_take,Nat.reduceLT,↓reduceIte] using obs
  · have obs := congrArg (fun bytes : Roadmap.Bytes => bytes[31]?) (complete_offset_words pipeline).2.1
    simpa only [List.getElem?_take,List.getElem?_drop,Nat.reduceAdd,Nat.reduceLT,↓reduceIte] using obs

theorem reversed_standard_offsets (pipeline : Roadmap.Pipeline) :
    (reversedData pipeline)[31]? = some 160 ∧ (reversedData pipeline)[127]? = some 0 := by
  constructor
  · have first : (reversedData pipeline).take 32 = Source.wordBytes (Source.toWord 160) := by
      rw [reversedData,SourceAbi.five_parts,SourceAbi.take_word]
    have obs := congrArg (fun bytes : Roadmap.Bytes => bytes[31]?) first
    simpa only [List.getElem?_take,Nat.reduceLT,↓reduceIte] using obs
  · have obs := congrArg (fun bytes : Roadmap.Bytes => bytes[31]?) (complete_offset_words pipeline).2.2
    simpa only [List.getElem?_take,List.getElem?_drop,Nat.reduceAdd,Nat.reduceLT,↓reduceIte] using obs

theorem different_ordered_bytes (pipeline : Roadmap.Pipeline) : data false pipeline ≠ reversedData pipeline := by
  intro same
  have offset := congrArg (fun bytes : Roadmap.Bytes => bytes[127]?) same
  change (data false pipeline)[127]? = (reversedData pipeline)[127]? at offset
  rw [(mixed_standard_offsets pipeline).2,(reversed_standard_offsets pipeline).2] at offset
  exact (by decide +kernel : (some 224 : Option UInt8) ≠ some 0) offset

/-- The hash is not reached at this horizon: the actual earlier local assignment
survives timeout. This is not transaction rollback or an admission cutoff. -/
theorem insufficient_after_effects (pipeline : Roadmap.Pipeline) (static packed : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 6
      (.abiEncode (if packed then .encodePacked else .encode) arguments)).run (locals,populated) =
      (.error .timeout,(.cons (.bool false) .nil,populated)) := rfl

theorem wrong_stale_pointer (pipeline : Roadmap.Pipeline) (static packed : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 17
      (.abiEncode (if packed then .encodePacked else .encode) arguments)).run (locals,populated) ≠
      (.ok (.val (.memRef rfl 1)),(.cons (.bool false) .nil,
        SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary) (data packed pipeline))) := by
  rw [mixed_complete]
  intro same
  have pointer := congrArg (fun result => match result.1 with
    | .ok (.val (.memRef _ address)) => some address
    | _ => none) same
  exact (by decide +kernel : (some 2 : Option Nat) ≠ some 1) pointer

theorem wrong_skipped_hash (pipeline : Roadmap.Pipeline) (static packed : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 17
      (.abiEncode (if packed then .encodePacked else .encode) arguments)).run (locals,populated) ≠
      (.ok (.val (.memRef rfl 1)),(.cons (.bool false) .nil,
        SourceKeccak.afterLiteral populated (data packed pipeline))) := by
  rw [mixed_complete]
  intro same
  have next := congrArg (fun result => result.2.2.heap.next) same
  exact (by decide +kernel : (3 : Nat) ≠ 2) next

theorem wrong_returned_locals (pipeline : Roadmap.Pipeline) (static packed : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 17
      (.abiEncode (if packed then .encodePacked else .encode) arguments)).run (locals,populated) ≠
      (.ok (.val (.memRef rfl 2)),(locals,
        SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary) (data packed pipeline))) := by
  rw [mixed_complete]
  intro same
  have localValue := congrArg (fun result => result.2.1.get .here) same
  cases localValue


def allocatedByteAt (state : Source.St E) (address index : Nat) : Option UInt8 :=
  match state.heap.get address with
  | some ⟨_,.bytes bytes⟩ => bytes[index]?
  | _ => none

def allocatedLength (state : Source.St E) (address : Nat) : Option Nat :=
  match state.heap.get address with
  | some ⟨_,.bytes bytes⟩ => some bytes.length
  | _ => none

theorem actual_different_order (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 17 (.abiEncode .encode arguments)).run (locals,populated) ≠
    (Source.evalE (global pipeline) {frame with static:=static} 17 (.abiEncode .encode reversedArguments)).run (locals,populated) := by
  have actual := mixed_complete pipeline static false
  simp only [Bool.false_eq_true,↓reduceIte] at actual
  rw [actual,reversed_execution]
  intro same
  have offset := congrArg (fun result => allocatedByteAt result.2.2 2 127) same
  change (data false pipeline)[127]? = (reversedData pipeline)[127]? at offset
  rw [(mixed_standard_offsets pipeline).2,(reversed_standard_offsets pipeline).2] at offset
  exact (by decide +kernel : (some 224 : Option UInt8) ≠ some 0) offset

theorem actual_different_packing (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 4 (SourceAbi.literal false binary)).run (locals,populated) ≠
    (Source.evalE (global pipeline) {frame with static:=static} 4 (SourceAbi.literal true binary)).run (locals,populated) := by
  rw [literal_complete,literal_complete]
  intro same
  have length := congrArg (fun result => allocatedLength result.2.2 1) same
  change (some 96 : Option Nat) = some 3 at length
  exact (by decide +kernel : (some 96 : Option Nat) ≠ some 3) length

theorem mixed_lengths (pipeline : Roadmap.Pipeline) :
    (data false pipeline).length = 320 ∧ (data true pipeline).length = 70 := by
  constructor
  · simp only [data,Bool.false_eq_true,↓reduceIte,Source.abiLayout,Source.abiLayout.go,
      List.length_append,Source.wordBytes_length] <;> rfl
  · simp only [data,↓reduceIte,List.length_append,Source.wordBytes_length] <;> rfl

#print axioms literal_complete
#print axioms literal_vector
#print axioms empty_binary_unaligned_lengths
#print axioms literal_cases
#print axioms arguments_execute
#print axioms encoding_execute
#print axioms mixed_complete
#print axioms mixed_vector
#print axioms mixed_standard_offsets
#print axioms reversed_execution
#print axioms reversed_standard_offsets
#print axioms different_ordered_bytes
#print axioms insufficient_after_effects
#print axioms wrong_stale_pointer
#print axioms wrong_skipped_hash
#print axioms wrong_returned_locals
#print axioms complete_offset_words
#print axioms actual_different_order
#print axioms actual_different_packing
#print axioms mixed_lengths
#print axioms digest_word
#print axioms digestWord_eq

/-- Binary selector and an empty signature are valid ABI-prefix inputs; neither
is treated as source declaration metadata or callable admission. -/
def selectorBytes : Roadmap.Bytes := [0,255,128,1]
def selectorArgs : RArgs E [.bool]
    [.stringLit selectorBytes,.stringLit binary,.bool,.bool,.stringLit long33,STy.bytes32] :=
  .cons (.str selectorBytes) arguments
def signatureArgs : RArgs E [.bool]
    [.stringLit [],.stringLit binary,.bool,.bool,.stringLit long33,STy.bytes32] :=
  .cons (.str []) arguments


theorem selector_value_bytes :
    (Source.mkBytes (n:=4) (h:=by decide +kernel) selectorBytes :
      Source.Val E.layout (.fixedBytes 4 (by decide +kernel))).bytesOf = selectorBytes := rfl

theorem selector_drop (tail : Roadmap.Bytes) (index : Nat) :
    (selectorBytes ++ tail).drop (4+index) = tail.drop index := by
  simpa only [show selectorBytes.length = 4 from rfl] using
    (List.drop_length_add_append (l₁:=selectorBytes) (l₂:=tail) index)

theorem selector_byte_at (tail : Roadmap.Bytes) (index : Nat) :
    allocatedByteAt (SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary)
      (selectorBytes ++ tail)) 2 (4+index) = tail[index]? := by
  change (selectorBytes ++ tail)[4+index]? = tail[index]?
  have drop : (selectorBytes ++ tail).drop 4 = tail := rfl
  simpa only [List.getElem?_drop] using congrArg (fun bytes : Roadmap.Bytes => bytes[index]?) drop

theorem selector_arguments_execute (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalArgs (global pipeline) {frame with static:=static} 17 selectorArgs).run (locals,populated) =
      (.ok (.cons (.strLit selectorBytes) (values pipeline)),
        (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary)) := rfl

theorem signature_arguments_execute (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalArgs (global pipeline) {frame with static:=static} 17 signatureArgs).run (locals,populated) =
      (.ok (.cons (.strLit []) (values pipeline)),
        (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary)) := rfl

theorem selector_mixed_complete (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 18
      (.abiEncode .encodeWithSelector selectorArgs)).run (locals,populated) =
      (.ok (.val (.memRef rfl 2)),(.cons (.bool false) .nil,
        SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary)
          (selectorBytes ++ data false pipeline))) := by
  have conversion : (Source.convRV {frame with static:=static} 17 (.fixedBytes 4 (by decide +kernel))
      (.strLit selectorBytes) : Source.EM E [.bool] _).run
      (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary) =
      (.ok (.val (Source.mkBytes (n:=4) (h:=by decide +kernel) selectorBytes)),
        (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary)) := rfl
  have result := SourceAbi.selector_execute (global pipeline) {frame with static:=static} 17 selectorArgs
    locals (.cons (.bool false) .nil) (.cons (.bool false) .nil) (.cons (.bool false) .nil)
    populated (SourceKeccak.afterLiteral populated binary) (SourceKeccak.afterLiteral populated binary)
    (SourceKeccak.afterLiteral populated binary) (.strLit selectorBytes) (values pipeline)
    (Source.mkBytes (n:=4) (h:=by decide +kernel) selectorBytes) (data false pipeline)
    (selector_arguments_execute pipeline static) conversion (encoding_execute pipeline static false)
  simpa only [selector_value_bytes] using result

theorem signature_mixed_complete (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 18
      (.abiEncode .encodeWithSignature signatureArgs)).run (locals,populated) =
      (.ok (.val (.memRef rfl 2)),(.cons (.bool false) .nil,
        SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary)
          ((Source.wordBytes ((global pipeline).fixed.hash [])).take 4 ++ data false pipeline))) := by
  apply SourceAbi.signature_execute (global pipeline) {frame with static:=static} 17 signatureArgs
    locals (.cons (.bool false) .nil) (.cons (.bool false) .nil) (.cons (.bool false) .nil)
    populated (SourceKeccak.afterLiteral populated binary) (SourceKeccak.afterLiteral populated binary)
    (SourceKeccak.afterLiteral populated binary) (.strLit []) (values pipeline) [] (data false pipeline)
  · exact signature_arguments_execute pipeline static
  · rfl
  · exact encoding_execute pipeline static false

/-- Independent checked empty-Keccak vector, not a collision/injectivity premise. -/
theorem empty_signature_prefix (pipeline : Roadmap.Pipeline) :
    (Source.wordBytes ((global pipeline).fixed.hash [])).take 4 = [197,210,70,1] := by
  rw [SourceAbi.signature_prefix_transport (global pipeline) Roadmap.Controls.toyFixed_keccak []]
  simp only [List.map_nil]
  rw [CryptoControls.empty_hash]
  rfl

/-- The entire old ordered vector is retained, with the prefixed output object.
Both successful return values and caller locals are in the execution theorems. -/
theorem prefixed_complete_vector (prefixData : Roadmap.Bytes) (pipeline : Roadmap.Pipeline) :
    let final := SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary)
      (prefixData ++ data false pipeline)
    (final.ex.world.accounts sender).balance.val = 93 ∧
    (final.ex.world.accounts self).balance.val = 7 ∧
    (final.ex.world.accounts self).code = some 0 ∧
    (final.ex.world.accounts self).nonce = 1 ∧
    (final.ex.world.accounts self).storage.read saved = some (.bool true) ∧
    (final.ex.transient.cells self).read scratch = some (.bool true) ∧
    final.ex.journal.length = 3 ∧ final.heap.next = 3 ∧
    final.heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    final.heap.get 1 = some ⟨.bytes .memory,.bytes binary⟩ ∧
    final.heap.get 2 = some ⟨.bytes .memory,.bytes (prefixData ++ data false pipeline)⟩ ∧
    final.events = populated.events ∧ final.logs = populated.logs ∧ final.fnLocals = populated.fnLocals :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem prefixed_offsets_and_length (pipeline : Roadmap.Pipeline) :
    (selectorBytes ++ data false pipeline).length = 324 ∧
    ((selectorBytes ++ data false pipeline).drop 4).take 32 = Source.wordBytes (Source.toWord 160) ∧
    ((selectorBytes ++ data false pipeline).drop 100).take 32 = Source.wordBytes (Source.toWord 224) := by
  constructor
  · rw [List.length_append,(mixed_lengths pipeline).1]
    rfl
  · constructor
    · rw [show (4:Nat) = 4+0 from rfl,selector_drop,List.drop_zero]
      exact (complete_offset_words pipeline).1
    · rw [show (100:Nat) = 4+96 from rfl,selector_drop]
      exact (complete_offset_words pipeline).2.1

/-- Reached local effects remain, but the later hash and output allocation have
not occurred. Timeout is distinct from revert/divergence. -/
theorem prefixed_timeout_after_effects (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 7
      (.abiEncode .encodeWithSelector selectorArgs)).run (locals,populated) =
      (.error .timeout,(.cons (.bool false) .nil,populated)) := by
  apply SourceAbi.prefixed_arguments_failure (global pipeline) {frame with static:=static} 6
    .encodeWithSelector selectorArgs locals (.cons (.bool false) .nil) populated populated .timeout
  rfl

theorem prefixed_zero_horizon (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 0
      (.abiEncode .encodeWithSignature signatureArgs)).run (locals,populated) =
      (.error .timeout,(locals,populated)) := rfl

theorem wrong_selector_bytes (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 18
      (.abiEncode .encodeWithSelector selectorArgs)).run (locals,populated) ≠
      (.ok (.val (.memRef rfl 2)),(.cons (.bool false) .nil,
        SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary)
          ([1,255,128,1] ++ data false pipeline))) := by
  rw [selector_mixed_complete]
  intro same
  have byte := congrArg (fun result => allocatedByteAt result.2.2 2 0) same
  exact (by decide +kernel : (some 0 : Option UInt8) ≠ some 1) byte

theorem wrong_signature_prefix (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 18
      (.abiEncode .encodeWithSignature signatureArgs)).run (locals,populated) ≠
      (.ok (.val (.memRef rfl 2)),(.cons (.bool false) .nil,
        SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary)
          ([0,0,0,0] ++ data false pipeline))) := by
  rw [signature_mixed_complete,empty_signature_prefix]
  intro same
  have byte := congrArg (fun result => allocatedByteAt result.2.2 2 0) same
  exact (by decide +kernel : (some 197 : Option UInt8) ≠ some 0) byte

theorem prefixed_wrong_pointer (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 18
      (.abiEncode .encodeWithSelector selectorArgs)).run (locals,populated) ≠
      (.ok (.val (.memRef rfl 1)),(.cons (.bool false) .nil,
        SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary)
          (selectorBytes ++ data false pipeline))) := by
  rw [selector_mixed_complete]
  intro same
  have pointer := congrArg (fun result => match result.1 with
    | .ok (.val (.memRef _ address)) => some address
    | _ => none) same
  exact (by decide +kernel : (some 2 : Option Nat) ≠ some 1) pointer

theorem prefixed_skipped_effects (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 18
      (.abiEncode .encodeWithSignature signatureArgs)).run (locals,populated) ≠
      (.ok (.val (.memRef rfl 1)),(locals,
        SourceKeccak.afterLiteral populated
          ((Source.wordBytes ((global pipeline).fixed.hash [])).take 4 ++ data false pipeline))) := by
  rw [signature_mixed_complete]
  intro same
  have next := congrArg (fun result => result.2.2.heap.next) same
  exact (by decide +kernel : (3 : Nat) ≠ 2) next

#print axioms selector_arguments_execute
#print axioms signature_arguments_execute
#print axioms selector_mixed_complete
#print axioms signature_mixed_complete
#print axioms empty_signature_prefix
#print axioms prefixed_complete_vector
#print axioms prefixed_offsets_and_length
#print axioms prefixed_timeout_after_effects
#print axioms prefixed_zero_horizon
#print axioms wrong_selector_bytes
#print axioms wrong_signature_prefix
#print axioms prefixed_wrong_pointer
#print axioms prefixed_skipped_effects

/-- Existing primitive argument values encode without reading or changing the
machine; this permits application at a genuinely different reached heap. -/
theorem prefixed_values_encoding (pipeline : Roadmap.Pipeline) (static : Bool) (horizon : Nat) :
    (Source.encodeVals {frame with static:=static} horizon false (values pipeline) : Source.EM E [.bool] _) =
      pure (data false pipeline) := by
  have wordRead : (digest pipeline).word = some (digestWord pipeline) := by
    rw [digestWord_eq]
    exact digest_word pipeline
  have wordEncoded := SourceAbi.encode_fixed_bytes32 (E:=E) (Γ:=[.bool])
    {frame with static:=static} horizon false (digest pipeline) (digestWord pipeline) wordRead
  have literalEncoded (bytes : Roadmap.Bytes) :
      (Source.encodeOne {frame with static:=static} horizon false (.strLit bytes) : Source.EM E [.bool] _) =
        pure (true,bytes) := rfl
  have falseEncoded :
      (Source.encodeOne {frame with static:=static} horizon false (.val (.bool false)) : Source.EM E [.bool] _) =
        pure (false,zeroWord) := rfl
  simp only [values,Source.encodeVals,Source.encodeParts]
  rw [literalEncoded binary,falseEncoded,literalEncoded long33,wordEncoded]
  rfl

/-- The first argument really allocates a string-memory reference; its contents
are read after the successful effecting tail at the new reached heap. -/
def afterSignature (state : Source.St E) : Source.St E :=
  {state with heap:=(state.heap.alloc ⟨.string .memory,.string []⟩).1}

def memorySignature : RExpr E [.bool] (.string .memory) := .conv (.str []) (Or.inl rfl)
def memorySignatureArgs : RArgs E [.bool]
    [.string .memory,.stringLit binary,.bool,.bool,.stringLit long33,STy.bytes32] :=
  .cons memorySignature arguments

theorem memory_signature_arguments (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalArgs (global pipeline) {frame with static:=static} 17 memorySignatureArgs).run (locals,populated) =
      (.ok (.cons (.val (.memRef rfl 1)) (values pipeline)),
        (.cons (.bool false) .nil,SourceKeccak.afterLiteral (afterSignature populated) binary)) := rfl

theorem memory_signature_complete (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 18
      (.abiEncode .encodeWithSignature memorySignatureArgs)).run (locals,populated) =
      (.ok (.val (.memRef rfl 3)),(.cons (.bool false) .nil,
        SourceKeccak.afterLiteral (SourceKeccak.afterLiteral (afterSignature populated) binary)
          ((Source.wordBytes ((global pipeline).fixed.hash [])).take 4 ++ data false pipeline))) := by
  let reached := SourceKeccak.afterLiteral (afterSignature populated) binary
  apply SourceAbi.signature_execute (global pipeline) {frame with static:=static} 17 memorySignatureArgs
    locals (.cons (.bool false) .nil) (.cons (.bool false) .nil) (.cons (.bool false) .nil)
    populated reached reached reached (.val (.memRef rfl 1)) (values pipeline) [] (data false pipeline)
  · exact memory_signature_arguments pipeline static
  · rfl
  · rw [prefixed_values_encoding]
    rfl

theorem memory_signature_vector (pipeline : Roadmap.Pipeline) :
    let payload := (Source.wordBytes ((global pipeline).fixed.hash [])).take 4 ++ data false pipeline
    let final := SourceKeccak.afterLiteral (SourceKeccak.afterLiteral (afterSignature populated) binary) payload
    (final.ex.world.accounts sender).balance.val = 93 ∧
    (final.ex.world.accounts self).balance.val = 7 ∧
    (final.ex.world.accounts self).code = some 0 ∧
    (final.ex.world.accounts self).nonce = 1 ∧
    (final.ex.world.accounts self).storage.read saved = some (.bool true) ∧
    (final.ex.transient.cells self).read scratch = some (.bool true) ∧
    final.ex.journal.length = 3 ∧ final.heap.next = 4 ∧
    final.heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    final.heap.get 1 = some ⟨.string .memory,.string []⟩ ∧
    final.heap.get 2 = some ⟨.bytes .memory,.bytes binary⟩ ∧
    final.heap.get 3 = some ⟨.bytes .memory,.bytes payload⟩ ∧
    final.events = populated.events ∧ final.logs = populated.logs ∧ final.fnLocals = populated.fnLocals :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def selectorReversedArgs : RArgs E [.bool]
    [.stringLit selectorBytes,.stringLit long33,.bool,.bool,.stringLit binary,STy.bytes32] :=
  .cons (.str selectorBytes) reversedArguments

theorem selector_reversed_complete (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 18
      (.abiEncode .encodeWithSelector selectorReversedArgs)).run (locals,populated) =
      (.ok (.val (.memRef rfl 2)),(.cons (.bool false) .nil,
        SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary)
          (selectorBytes ++ reversedData pipeline))) := rfl

theorem actual_prefixed_different_order (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 18
      (.abiEncode .encodeWithSelector selectorArgs)).run (locals,populated) ≠
    (Source.evalE (global pipeline) {frame with static:=static} 18
      (.abiEncode .encodeWithSelector selectorReversedArgs)).run (locals,populated) := by
  rw [selector_mixed_complete,selector_reversed_complete]
  intro same
  have offset := congrArg (fun result => allocatedByteAt result.2.2 2 131) same
  dsimp only at offset
  rw [selector_byte_at (data false pipeline) 127,selector_byte_at (reversedData pipeline) 127] at offset
  rw [(mixed_standard_offsets pipeline).2,(reversed_standard_offsets pipeline).2] at offset
  exact (by decide +kernel : (some 224 : Option UInt8) ≠ some 0) offset

theorem memory_signature_wrong_pointer (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 18
      (.abiEncode .encodeWithSignature memorySignatureArgs)).run (locals,populated) ≠
      (.ok (.val (.memRef rfl 2)),(.cons (.bool false) .nil,
        SourceKeccak.afterLiteral (SourceKeccak.afterLiteral (afterSignature populated) binary)
          ((Source.wordBytes ((global pipeline).fixed.hash [])).take 4 ++ data false pipeline))) := by
  rw [memory_signature_complete]
  intro same
  have pointer := congrArg (fun result => match result.1 with
    | .ok (.val (.memRef _ address)) => some address
    | _ => none) same
  exact (by decide +kernel : (some 3 : Option Nat) ≠ some 2) pointer

#print axioms prefixed_values_encoding
#print axioms memory_signature_arguments
#print axioms memory_signature_complete
#print axioms memory_signature_vector
#print axioms selector_reversed_complete
#print axioms actual_prefixed_different_order
#print axioms memory_signature_wrong_pointer

#print axioms selector_value_bytes
#print axioms selector_drop
#print axioms selector_byte_at

/-- These are the published ABI argument predicates, not full source-unit admission. -/
theorem selector_argsOK : AbiKind.encodeWithSelector.argsOK E.isBase
    [.stringLit selectorBytes,.stringLit binary,.bool,.bool,.stringLit long33,STy.bytes32] = true := rfl

theorem signature_argsOK : AbiKind.encodeWithSignature.argsOK E.isBase
    [.stringLit [],.stringLit binary,.bool,.bool,.stringLit long33,STy.bytes32] = true := rfl

theorem memory_signature_argsOK : AbiKind.encodeWithSignature.argsOK E.isBase
    [.string .memory,.stringLit binary,.bool,.bool,.stringLit long33,STy.bytes32] = true := rfl

/-- Generic resolved evaluation is broader than admitted typing: this published
rejection is preserved, with no new profile rule or restriction. -/
theorem overlong_selector_not_argsOK : AbiKind.encodeWithSelector.argsOK E.isBase
    [.stringLit long33,.stringLit binary] = false := rfl

#print axioms selector_argsOK
#print axioms signature_argsOK
#print axioms memory_signature_argsOK
#print axioms overlong_selector_not_argsOK

/-- A reached transaction-opening state using the published source endTx. -/
def transientOpening : Source.St E := SourceTransient.endExecution populated
def transientWritten : Source.St E :=
  SourceTransient.transientUpdate transientOpening self scratch (.bool true)
def setScratch : RExpr E [.bool] .bool := .assign (.state scratchDecl rfl rfl) (.bool true)

theorem source_transient_write (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) frame 4 setScratch).run (locals,transientOpening) =
      (.ok (.val (.bool true)),(locals,transientWritten)) := rfl

theorem source_transient_read (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) frame 2 (.state scratchDecl rfl : RExpr E [.bool] .bool)).run
      (locals,transientWritten) = (.ok (.val (.bool true)),(locals,transientWritten)) := rfl

theorem source_transient_read_end (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) frame 2 (.state scratchDecl rfl : RExpr E [.bool] .bool)).run
      (locals,SourceTransient.endExecution transientWritten) =
      (.ok (.val (.bool false)),(locals,SourceTransient.endExecution transientWritten)) := rfl

theorem source_transient_rollback :
    {transientWritten with ex:=transientWritten.ex.undo} = transientOpening :=
  SourceTransient.transient_undo transientOpening self scratch (.bool true)

/-- Static refusal follows a real RHS local effect; source execution does not
undo those locals merely because the storage operation reverts. -/
theorem source_transient_static_after_effect (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) {frame with static:=true} 6
      (.assign (.state scratchDecl rfl rfl) setFalse)).run (locals,transientOpening) =
      (.error (.revert []),(.cons (.bool false) .nil,transientOpening)) := rfl

theorem source_transient_zero_horizon (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) frame 0 setScratch).run (locals,transientOpening) =
      (.error .timeout,(locals,transientOpening)) := rfl

theorem source_transient_complete_vector :
    (transientWritten.ex.world.accounts sender).balance.val = 93 ∧
    (transientWritten.ex.world.accounts self).balance.val = 7 ∧
    (transientWritten.ex.world.accounts self).code = some 0 ∧
    (transientWritten.ex.world.accounts self).nonce = 1 ∧
    (transientWritten.ex.world.accounts self).storage.read saved = some (.bool true) ∧
    (transientOpening.ex.transient.cells self).read scratch = some (.bool false) ∧
    (transientWritten.ex.transient.cells self).read scratch = some (.bool true) ∧
    ((SourceTransient.endExecution transientWritten).ex.transient.cells self).read scratch = some (.bool false) ∧
    transientOpening.ex.journal.length = 0 ∧ transientWritten.ex.journal.length = 1 ∧
    (SourceTransient.endExecution transientWritten).ex.journal.length = 0 ∧
    transientWritten.heap.next = 1 ∧
    transientWritten.heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    transientWritten.events = populated.events ∧ transientWritten.logs = populated.logs ∧
    transientWritten.fnLocals = populated.fnLocals :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def BoolTransientCell : Contract := contract!{ bool saved; bool transient scratch; }
def boolCatalog : Unit → Contract := fun _ => BoolTransientCell
def boolInitial : ContractWorld.World boolCatalog := ContractWorld.World.empty boolCatalog
  (fun address => if address = Controls.sender then ⟨100,by decide +kernel⟩ else ⟨0,by decide +kernel⟩)
def boolEntry : ContractWorld.Entry BoolTransientCell (List UInt8) :=
  {locals:=[],body:=sol[BoolTransientCell]{ saved = true; scratch = true; },
   payable:=true,result:=fun _ => .ok [0,255,128]}
def boolExecution : TRes (ContractWorld.World boolCatalog × List UInt8) := do
  let (world,_) ← boolInitial.create () Controls.self .nil Controls.ctx
  world.call (⟨Controls.self⟩ : ContractWorld.Handle ()) boolEntry Controls.paidCtx

def boolObservation (world : ContractWorld.World boolCatalog) :
    Option (Int × Int × Bool × Bool) := do
  let storage ← world.storage? (⟨Controls.self⟩ : ContractWorld.Handle ())
  let .prim saved ← storage.find (SRef.ofRoot "saved" rfl)
  let .prim scratch ← storage.find (SRef.ofRoot "scratch" rfl)
  pure ((world.balance Controls.sender).1,(world.balance Controls.self).1,saved,scratch)

theorem intrinsic_transient_write :
    (boolExecution.map (fun result => (boolObservation result.1,result.2))).toOption =
      some (some (93,7,true,true),[0,255,128]) := by decide +kernel

theorem intrinsic_transient_reset :
    (boolExecution.map (fun result => (boolObservation result.1.resetTransient,result.2))).toOption =
      some (some (93,7,true,false),[0,255,128]) := by decide +kernel

/-- Instantiates the generic typed-path reset theorem on the actual installed
catalog. No canonical source-to-contract layout relation is inferred. -/
theorem intrinsic_selected_reset (world : ContractWorld.World boolCatalog) :
    (world.resetTransient.storage? (⟨Controls.self⟩ : ContractWorld.Handle ())).bind
        (fun storage => storage.find (SRef.ofRoot "scratch" rfl)) =
      (world.storage? (⟨Controls.self⟩ : ContractWorld.Handle ())).bind
        (fun _ => some (.prim false)) := by
  exact SourceTransient.target_transient_reset world (⟨Controls.self⟩ : ContractWorld.Handle ())
    (SRef.ofRoot "scratch" rfl) (by decide +kernel)

theorem wrong_source_stale_transient (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) frame 2 (.state scratchDecl rfl : RExpr E [.bool] .bool)).run
      (locals,SourceTransient.endExecution transientWritten) ≠
      (.ok (.val (.bool true)),(locals,SourceTransient.endExecution transientWritten)) := by
  rw [source_transient_read_end]
  intro same
  cases same

theorem wrong_intrinsic_stale_transient :
    (boolExecution.map (fun result => (boolObservation result.1.resetTransient,result.2))).toOption ≠
      some (some (93,7,true,true),[0,255,128]) := by decide +kernel

theorem wrong_transient_payload :
    (boolExecution.map (fun result => (boolObservation result.1.resetTransient,result.2))).toOption ≠
      some (some (93,7,true,false),[0,255,127]) := by decide +kernel

#print axioms source_transient_write
#print axioms source_transient_read
#print axioms source_transient_read_end
#print axioms source_transient_rollback
#print axioms source_transient_static_after_effect
#print axioms source_transient_zero_horizon
#print axioms source_transient_complete_vector
#print axioms intrinsic_transient_write
#print axioms intrinsic_transient_reset
#print axioms intrinsic_selected_reset
#print axioms wrong_source_stale_transient
#print axioms wrong_intrinsic_stale_transient
#print axioms wrong_transient_payload
end Solidity.Lowering.V08.SourceAbiControls
