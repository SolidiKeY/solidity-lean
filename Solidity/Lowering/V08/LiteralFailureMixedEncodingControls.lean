import Solidity.Lowering.V08.LiteralFailureMixedEncoding
import Solidity.Lowering.V08.LiteralFailureReturnSlotsControls
namespace Solidity.Lowering.V08.LiteralFailureMixedEncodingControls
open Solidity Source Backend
open LiteralFailureMixedEncoding
open SourceCustomErrorControls (E frame global populated)
open LiteralFailureDynamicReturnControls (state saved live)

def types : RCtx := [.bytes .memory,.int IntTy.u256,.bytes .memory,.int IntTy.u256]
def shapes : List AbiEntry.Shape := [.bytes,.word (.uint 256),.bytes,.word (.uint 256)]
def parameters : RCtx := types ++ [.bytes .memory,.bool]
def locals (x y : Roadmap.Word) : Locals E.layout parameters :=
 .cons (.memRef rfl 1 : Source.Val E.layout (.bytes .memory)) (.cons (SourceEnvironment.sourceWord x)
  (.cons (.memRef rfl 2) (.cons (SourceEnvironment.sourceWord y)
   (.cons (.memRef rfl 0) (.cons (.bool true) .nil)))))
def values (x y : Roadmap.Word) : Source.Vals E.layout types :=
 .cons (.memRef rfl 1 : Source.Val E.layout (.bytes .memory)) (.cons (SourceEnvironment.sourceWord x)
  (.cons (.memRef rfl 2) (.cons (SourceEnvironment.sourceWord y) .nil)))
def old : Source.Vals E.layout types :=
 .cons (.memRef rfl 0) (.cons (SourceEnvironment.sourceWord ⟨7,by decide +kernel⟩)
  (.cons (.memRef rfl 0) (.cons (SourceEnvironment.sourceWord ⟨11,by decide +kernel⟩) .nil)))
def abiValues (first second : Roadmap.Bytes) (x y : Roadmap.Word) : AbiEntry.Vals shapes :=
 .cons (.bytes first) (.cons (.word (LiteralFailureDynamicError.abiWord x))
  (.cons (.bytes second) (.cons (.word (LiteralFailureDynamicError.abiWord y)) .nil)))
def parts (first second : Roadmap.Bytes) (x y : Roadmap.Word) : List (Bool × Roadmap.Bytes) :=
 [(true,first),(false,wordBytes x),(true,second),(false,wordBytes y)]

theorem represented (first second : Roadmap.Bytes) (x y : Roadmap.Word) :
 Represented (state first second) (values x y) (abiValues first second x y) (parts first second x y) :=
 .bytes 1 first (.inl rfl) (.uint x (.bytes 2 second (.inl rfl) (.uint y .nil)))

def arguments : RConvArgs E (types.reverseAux parameters) types := (.cons (.local (.there (.there (.there (.there .here))))) rfl (.cons (.local (.there (.there (.there (.there (.there .here)))))) rfl (.cons (.local (.there (.there (.there (.there (.there (.there .here))))))) rfl (.cons (.local (.there (.there (.there (.there (.there (.there (.there .here)))))))) rfl .nil))))
def statement : RStmt E types false .body (types.reverseAux parameters) (types.reverseAux parameters) :=
 .retTuple arguments

theorem arguments_run (p : Roadmap.Pipeline) (static : Bool) (first second : Roadmap.Bytes)
 (x y : Roadmap.Word) :
 (evalConvArgs (global p) {frame with static:=static} 8 arguments).run
 (old.onto (locals x y),state first second)=
 (.ok (values x y),(old.onto (locals x y),state first second)) := by rfl

theorem body_return (p : Roadmap.Pipeline) (static : Bool) (first second : Roadmap.Bytes)
 (x y : Roadmap.Word) :
 (execS (global p) {frame with static:=static} 9 6 none statement (old.onto (locals x y))).run
 (L0 E,state first second)=
 (.ok (.ret ((values x y).onto (locals x y))),(L0 E,state first second)) :=
 LiteralFailureReturnSlots.tuple_statement (global p) {frame with static:=static} 8 old (values x y)
 (locals x y) (old.onto (locals x y)) arguments (state first second) (state first second)
 (arguments_run p static first second x y)

theorem extracted (x y : Roadmap.Word) :
 retVals ((values x y).onto (locals x y)) 0 types=.ok (values x y).toR :=
 LiteralFailureReturnSlots.extraction _ _

theorem encoding (F : Fr) (fuel : Nat) (first second : Roadmap.Bytes) (x y : Roadmap.Word) :
 FailurePaths.Premises.EncodingAt F fuel (values x y).toR (state first second) (state first second)
 (AbiEntry.encodeArgs (abiValues first second x y)) :=
 encodingAt F fuel _ (represented first second x y)

def packet (first second : Roadmap.Bytes) (x y : Roadmap.Word) :=
 AbiEntry.encodeArgs (abiValues first second x y)

theorem transport (first second : Roadmap.Bytes) (x y : Roadmap.Word)
 (fits : Failure.Fits 8 (packet first second x y)) :
 Failure.Local.execute (Failure.Local.save (MemoryOps.Physical.worldJournal populated.ex saved))
 8 (.returned (packet first second x y)) (MemoryOps.Physical.worldJournal (state first second).ex live)=
 some (MemoryOps.Physical.worldJournal (state first second).ex
  {live with memory:=Failure.Slice.putBytes live.memory 8 (packet first second x y)},
  .success (packet first second x y)) :=
 (FailurePaths.encoded_return frame 0 8 (values x y).toR (state first second) (state first second)
  populated (packet first second x y) (encoding frame 0 first second x y) saved live fits (by decide)).2.2

theorem old_alias (x y : Roadmap.Word) :
 ((values x y).onto (locals x y)).getAt 8 (.bytes .memory)=.ok (.memRef rfl 0) := by rfl

theorem repeated_alias (first second : Roadmap.Bytes) (x : Roadmap.Word) :
 Represented (state first second)
  (.cons (.memRef rfl 1 : Source.Val E.layout (.bytes .memory)) (.cons (SourceEnvironment.sourceWord x) (.cons (.memRef rfl 1 : Source.Val E.layout (.bytes .memory)) .nil)))
  (.cons (.bytes first) (.cons (.word (LiteralFailureDynamicError.abiWord x)) (.cons (.bytes first) .nil)))
  [(true,first),(false,wordBytes x),(true,first)] :=
 .bytes 1 first (.inl rfl) (.uint x (.bytes 1 first (.inl rfl) .nil))

def x : Roadmap.Word := ⟨42,by decide +kernel⟩
def y : Roadmap.Word := ⟨300,by decide +kernel⟩
theorem finite_fits : Failure.Fits 8 (packet [0,255] [128] x y) := by
 have length : (packet [0,255] [128] x y).length=256 := by decide +kernel
 simp only [Failure.Fits,length]
 decide +kernel

theorem finite_transport :
 Failure.Local.execute (Failure.Local.save (MemoryOps.Physical.worldJournal populated.ex saved))
 8 (.returned (packet [0,255] [128] x y)) (MemoryOps.Physical.worldJournal (state [0,255] [128]).ex live)=
 some (MemoryOps.Physical.worldJournal (state [0,255] [128]).ex
  {live with memory:=Failure.Slice.putBytes live.memory 8 (packet [0,255] [128] x y)},
  .success (packet [0,255] [128] x y)) := transport [0,255] [128] x y finite_fits

theorem wrong_order : packet [0,255] [128] x y≠packet [128] [0,255] x y := by decide +kernel

theorem first_offset : AbiEntry.load (packet [0,255] [128] x y) 0=128 := by decide +kernel

theorem second_offset : AbiEntry.load (packet [0,255] [128] x y) 64=192 := by decide +kernel

theorem empty_encoding (F : Fr) (fuel : Nat) (first second : Roadmap.Bytes) :
 FailurePaths.Premises.EncodingAt F fuel (.nil : Source.RVals E.layout [])
 (state first second) (state first second) (AbiEntry.encodeArgs (.nil : AbiEntry.Vals [])) :=
 encodingAt F fuel _ Represented.nil

theorem wrong_head : AbiEntry.load (packet [0,255] [128] x y) 0≠64 := by decide +kernel

def packets : List Roadmap.Bytes :=
 [packet [] [] ⟨0,by decide +kernel⟩ ⟨2^256-1,by omega⟩,
  packet [0,255] [128] x y,
  packet (List.replicate 31 255) (List.replicate 32 0) y x,
  packet (List.replicate 33 128) [] ⟨2^255,by decide +kernel⟩ y,
  packet (List.replicate 33 128) (List.replicate 33 128) ⟨2^256-1,by omega⟩ ⟨2^255,by decide +kernel⟩]
def render (bs : Roadmap.Bytes) : String :=
 "["++String.intercalate "," (bs.map (fun b=>toString b.toNat))++"]"
#eval IO.println ("MIXED_ENCODING_PACKETS=["++String.intercalate "," (packets.map render)++"]")
#print axioms word_agreement
#print axioms parts_run
#print axioms go_agreement
#print axioms head_extent
#print axioms encoding_run
#print axioms encodingAt
#print axioms represented
#print axioms arguments_run
#print axioms body_return
#print axioms extracted
#print axioms encoding
#print axioms transport
#print axioms old_alias
#print axioms repeated_alias
#print axioms finite_fits
#print axioms finite_transport
#print axioms wrong_order
#print axioms first_offset
#print axioms second_offset
#print axioms empty_encoding
#print axioms wrong_head
end Solidity.Lowering.V08.LiteralFailureMixedEncodingControls
