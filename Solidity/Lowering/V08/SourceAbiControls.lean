import Solidity.Lowering.V08.SourceAbi
import Solidity.Lowering.V08.SourceCustomErrorControls
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
end Solidity.Lowering.V08.SourceAbiControls
