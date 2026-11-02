import Solidity.Lowering.V08.SourceAbiControls
import Solidity.Semantics.AbiEntryProofs

/-! Actual source allocation and published eager/lazy entry decoding of its bytes.
These concrete inputs discharge the decoder size premise; it is not a Source
admission bound. No Source calldata-reference, body, layout or bytecode adequacy
is asserted. The source machine equalities retain its entire populated state. -/
namespace Solidity.Lowering.V08.SourceAbiEntryControls
open Solidity Source
open SourceCustomErrorControls

/-- The selector is supplied explicitly; the argument bytes are the actual
source encoder's allocated object, not a second encoder. -/
def input (bytes : Roadmap.Bytes) : AbiEntry.Input :=
  { data := [0,0,0,0] ++ Source.abiLayout [(true,bytes)], free := 2 ^ 32 }

def bytesValue : AbiEntry.Val .bytes → Roadmap.Bytes
  | .bytes bytes => bytes

/-- Both branches and their exact values survive this decidable observer. -/
def observeResult {α : Type} : Except AbiEntry.Fail α → Option α × Option AbiEntry.Fail
  | .ok value => (some value,none)
  | .error failure => (none,some failure)

theorem observeResult_injective {α : Type} : Function.Injective (observeResult (α:=α)) := by
  intro left right same
  cases left with
  | error a =>
    cases right with
    | error b =>
      have equal : a = b := Option.some.inj (congrArg Prod.snd same)
      exact congrArg Except.error equal
    | ok b =>
      have impossible : (some a : Option AbiEntry.Fail) = none := congrArg Prod.snd same
      cases impossible
  | ok a =>
    cases right with
    | error b =>
      have impossible : (none : Option AbiEntry.Fail) = some b := congrArg Prod.snd same
      cases impossible
    | ok b =>
      have equal : a = b := Option.some.inj (congrArg Prod.fst same)
      exact congrArg Except.ok equal

def observeBytes (result : Except AbiEntry.Fail (AbiEntry.Val .bytes)) :
    Option Roadmap.Bytes × Option AbiEntry.Fail := observeResult (result.map bytesValue)

theorem observeBytes_injective : Function.Injective observeBytes := by
  intro left right same
  cases left with
  | error a =>
    cases right with
    | error b =>
      have equal : a = b := Option.some.inj (congrArg Prod.snd same)
      exact congrArg Except.error equal
    | ok value =>
      cases value
      have impossible : (some a : Option AbiEntry.Fail) = none := congrArg Prod.snd same
      cases impossible
  | ok leftValue =>
    cases leftValue with
    | bytes a =>
      cases right with
      | error b =>
        have impossible : (none : Option AbiEntry.Fail) = some b := congrArg Prod.snd same
        cases impossible
      | ok rightValue =>
        cases rightValue with
        | bytes b =>
          have equal : a = b := Option.some.inj (congrArg Prod.fst same)
          cases equal
          rfl

theorem binary_eager : AbiEntry.eager (input binary) 4 .bytes 0 =
    .ok (.bytes binary) := by
  apply observeBytes_injective
  decide +kernel

theorem empty_eager : AbiEntry.eager (input []) 4 .bytes 0 =
    .ok (.bytes []) := by
  apply observeBytes_injective
  decide +kernel

theorem long33_eager : AbiEntry.eager (input SourceAbiControls.long33) 4 .bytes 0 =
    .ok (.bytes SourceAbiControls.long33) := by
  apply observeBytes_injective
  decide +kernel

/-- Actual lengths, including the supplied selector; all are below the
published decoder's bound without restricting general Source inputs. -/
theorem input_sizes :
    ((input []).size,(input binary).size,(input SourceAbiControls.long33).size) =
      (68,100,132) := by decide +kernel

theorem binary_lazy : ∃ addr len,
    AbiEntry.cref (input binary) .bytes 4 0 = .ok (addr,len) ∧
    AbiEntry.cval (input binary) 3 .bytes addr len = .ok (.bytes binary) :=
  AbiEntry.eager_cref (by decide +kernel) binary_eager

/-- Full actual source machine, exact heap object and exact decoded value,
for either pipeline and either static mode. Only entry decoding is applied. -/
theorem binary_source_entry (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 4
      (SourceAbi.literal false binary)).run (locals,populated) =
      (.ok (.val (.memRef rfl 1)),(locals,SourceKeccak.afterLiteral populated
        (Source.abiLayout [(true,binary)]))) ∧
    (SourceKeccak.afterLiteral populated (Source.abiLayout [(true,binary)])).heap.get 1 =
      some ⟨.bytes .memory,.bytes ((input binary).data.drop 4)⟩ ∧
    AbiEntry.eager (input binary) 4 .bytes 0 = .ok (.bytes binary) ∧
    (∃ addr len, AbiEntry.cref (input binary) .bytes 4 0 = .ok (addr,len) ∧
      AbiEntry.cval (input binary) 3 .bytes addr len = .ok (.bytes binary)) :=
  ⟨SourceAbiControls.literal_complete pipeline static false binary,rfl,binary_eager,binary_lazy⟩

/-- The actual lazy reference points beyond the head and length words. -/
theorem binary_reference : AbiEntry.cref (input binary) .bytes 4 0 = .ok (68,3) := by
  apply observeResult_injective
  decide +kernel

theorem empty_lazy : ∃ addr len,
    AbiEntry.cref (input []) .bytes 4 0 = .ok (addr,len) ∧
    AbiEntry.cval (input []) 3 .bytes addr len = .ok (.bytes []) :=
  AbiEntry.eager_cref (by decide +kernel) empty_eager

theorem long33_lazy : ∃ addr len,
    AbiEntry.cref (input SourceAbiControls.long33) .bytes 4 0 = .ok (addr,len) ∧
    AbiEntry.cval (input SourceAbiControls.long33) 3 .bytes addr len =
      .ok (.bytes SourceAbiControls.long33) :=
  AbiEntry.eager_cref (by decide +kernel) long33_eager

/-- Decoding at the next head slot is not decoding the actual argument. -/
theorem shifted_head : observeBytes (AbiEntry.eager (input binary) 4 .bytes 32) ≠
    (some binary,none) := by decide +kernel

/-- Removing the third data byte causes a real empty revert, not a different
successful value. The canonical padding is also absent in this input. -/
theorem truncated_data : AbiEntry.eager
    {input binary with data := (input binary).data.take 70} 4 .bytes 0 =
      .error .revert := by
  apply observeBytes_injective
  decide +kernel

theorem wrong_decoded_bytes : observeBytes (AbiEntry.eager (input binary) 4 .bytes 0) ≠
    (some [0,128,255],none) := by decide +kernel

theorem wrong_reference : AbiEntry.cref (input binary) .bytes 4 0 ≠ .ok (36,3) := by
  rw [binary_reference]
  intro same
  cases same

#print axioms observeResult_injective
#print axioms observeBytes_injective
#print axioms binary_eager
#print axioms empty_eager
#print axioms long33_eager
#print axioms input_sizes
#print axioms binary_lazy
#print axioms binary_source_entry
#print axioms binary_reference
#print axioms empty_lazy
#print axioms long33_lazy
#print axioms shifted_head
#print axioms truncated_data
#print axioms wrong_decoded_bytes
#print axioms wrong_reference
/-- Existing argument effects: binary, write false, read false, 33 bytes,
then the pinned hash. Parameter locations are explicit decoder inputs. -/
def mixedParams : List AbiEntry.Param :=
  [{shape:=.bytes,loc:=.memory},
   {shape:=.word .bool,loc:=.value},
   {shape:=.word .bool,loc:=.value},
   {shape:=.bytes,loc:=.calldata},
   {shape:=.word (.fixedBytes 32),loc:=.value}]

def mixedInput (pipeline : Roadmap.Pipeline) : AbiEntry.Input :=
  {data:=[0,0,0,0] ++ SourceAbiControls.data false pipeline,free:=2^32}

/-- Observe every decoded argument's canonical bytes and preserve the three
verdict branches. This is a byte observation, not a general injectivity law. -/
def entryObservation (input : AbiEntry.Input) : Option Roadmap.Bytes × Option String × Bool :=
  match AbiEntry.verdict input 16 mixedParams with
  | .run values => (some (AbiEntry.encodeArgs values),none,false)
  | .revert => (none,none,true)
  | .blocked reason => (none,some reason,false)

theorem mixed_entry (pipeline : Roadmap.Pipeline) :
    entryObservation (mixedInput pipeline) =
      (some (SourceAbiControls.data false pipeline),none,false) := by
  cases pipeline <;> decide +kernel

theorem mixed_input_bytes (pipeline : Roadmap.Pipeline) :
    (mixedInput pipeline).data.drop 4 = SourceAbiControls.data false pipeline := by
  simp only [mixedInput,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero]

theorem mixed_heap_object (bytes : Roadmap.Bytes) :
    (SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary) bytes).heap.get 2 =
      some ⟨.bytes .memory,.bytes bytes⟩ := rfl

/-- Complete reached Source state after the real write/read/hash arguments,
and the actual decoder observation of precisely its new heap object's bytes. -/
theorem mixed_effects_and_entry (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 17
      (.abiEncode .encode SourceAbiControls.arguments)).run (locals,populated) =
      (.ok (.val (.memRef rfl 2)),(.cons (.bool false) .nil,
        SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary)
          (SourceAbiControls.data false pipeline))) ∧
    (SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary)
      (SourceAbiControls.data false pipeline)).heap.get 2 =
        some ⟨.bytes .memory,.bytes ((mixedInput pipeline).data.drop 4)⟩ ∧
    entryObservation (mixedInput pipeline) =
      (some (SourceAbiControls.data false pipeline),none,false) :=
by
  constructor
  · exact SourceAbiControls.mixed_complete pipeline static false
  constructor
  · rw [mixed_input_bytes]
    exact mixed_heap_object (SourceAbiControls.data false pipeline)
  · exact mixed_entry pipeline

theorem mixed_second_reference (pipeline : Roadmap.Pipeline) :
    AbiEntry.cref (mixedInput pipeline) .bytes 4 96 = .ok (260,33) := by
  apply observeResult_injective
  cases pipeline <;> decide +kernel

/-- Reading before the write changes the encoded argument value and offsets;
the complete target byte observation detects it without a hash premise. -/
theorem wrong_argument_order (pipeline : Roadmap.Pipeline) :
    entryObservation {mixedInput pipeline with
      data := [0,0,0,0] ++ SourceAbiControls.reversedData pipeline} ≠
      (some (SourceAbiControls.data false pipeline),none,false) := by
  cases pipeline <;> decide +kernel

/-- Packed bytes are not silently reinterpreted as the canonical tuple. -/
theorem packed_not_entry (pipeline : Roadmap.Pipeline) :
    entryObservation {mixedInput pipeline with
      data := [0,0,0,0] ++ SourceAbiControls.data true pipeline} = (none,none,true) := by
  cases pipeline <;> decide +kernel

#print axioms mixed_input_bytes
#print axioms mixed_heap_object
#print axioms mixed_entry
#print axioms mixed_effects_and_entry
#print axioms mixed_second_reference
#print axioms wrong_argument_order
#print axioms packed_not_entry

end Solidity.Lowering.V08.SourceAbiEntryControls
