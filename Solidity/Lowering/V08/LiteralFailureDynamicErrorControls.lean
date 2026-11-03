import Solidity.Lowering.V08.LiteralFailureDynamicError
import Solidity.Lowering.V08.SourceCustomErrorControls

namespace Solidity.Lowering.V08.LiteralFailureDynamicErrorControls
open Solidity Source LiteralFailureDynamicError

def declaration : Decl :=
 ⟨.error,"Mixed",some "C",false,.error "Mixed"
  (.cons (.errorParam (.elem .bytes) none)
   (.cons (.errorParam (.elem (.int false 256 (by decide +kernel))) none) .nil))⟩
def environment : Env := ⟨[declaration]⟩
theorem member : declaration ∈ environment.decls := List.mem_cons_self
theorem typed : declaration.paramTys environment = some types := rfl

def empty : St environment :=
 ⟨⟨⟨fun _ => Account.empty _⟩,Transient.empty,[]⟩,Source.Heap.empty,[],[],⟨[],.nil⟩, Source.FailureExecution.Cursor.empty⟩
def frame := SourceCustomErrorControls.frame

def object (bytes : Roadmap.Bytes) (asString : Bool) : Σ τ, Data environment.layout τ :=
 if asString then ⟨.string .memory,.string bytes⟩ else ⟨.bytes .memory,.bytes bytes⟩
def state (bytes : Roadmap.Bytes) (asString : Bool) : St environment :=
 {empty with heap := (((Source.Heap.empty.alloc ⟨.bytes .memory,.bytes [9,7]⟩).1).alloc (object bytes asString)).1
             ex := empty.ex.run [.account frame.this (fun account => {account with balance:=⟨73,by decide +kernel⟩,nonce:=4})]}
def older : Locals environment.layout [.bytes .memory,.bool] :=
 .cons (.memRef rfl 0) (.cons (.bool true) .nil)

def program : Program environment :=
 {body:=fun _=>none,consts:=fun _=>none,inits:=fun _=>[],ctor:=fun _=>none,
  ctorLocals:=fun _=>[],baseArgs:=fun _=>[],contracts:=["C"]}
def global (pipeline : Roadmap.Pipeline) : Glob environment :=
 {prog:=program,pipeline:=pipeline,fixed:=Roadmap.Controls.toyFixed,
  balance0:=fun _=>⟨100,by decide +kernel⟩,hasCode:=fun _ _=>false,
  callee:=fun _=>.answer (.success []),timestamp:=⟨12345,by decide +kernel⟩}

theorem heap_agrees (bytes : Roadmap.Bytes) (asString : Bool) :
 (state bytes asString).heap.get 1 = some ⟨.bytes .memory,.bytes bytes⟩ ∨
 (state bytes asString).heap.get 1 = some ⟨.string .memory,.string bytes⟩ := by
 cases asString
 · exact .inl rfl
 · exact .inr rfl

theorem client (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes)
 (marker : Roadmap.Word) (asString : Bool) :
 (execS (global pipeline) frame 6 0 none (statement declaration typed)
  (caller 1 marker older)).run (Source.L0 environment,state bytes asString) =
 (.error (.revert ((global pipeline).selector (sigOf environment.layout declaration.name types) ++
  AbiEntry.encodeArgs (abiValues bytes marker))),(Source.L0 environment,state bytes asString)) :=
 source_typed (global pipeline) frame 0 declaration typed 1 marker bytes older
  (state bytes asString) (heap_agrees bytes asString)

theorem old_alias (bytes : Roadmap.Bytes) (asString : Bool) :
 (state bytes asString).heap.get 0 = some ⟨.bytes .memory,.bytes [9,7]⟩ ∧
 (state bytes asString).heap.next = 2 := by cases asString <;> exact ⟨rfl,rfl⟩

def threeHundred : Roadmap.Word := ⟨300,by decide +kernel⟩
def maxWord : Roadmap.Word := ⟨2^256-1,by decide +kernel⟩

theorem wrong_marker : AbiEntry.encodeArgs (abiValues [0,255,128] threeHundred) ≠
 AbiEntry.encodeArgs (abiValues [0,255,128] ⟨44,by decide +kernel⟩) := by decide +kernel

theorem wrong_offset : (AbiEntry.encodeArgs (abiValues [0,255,128] threeHundred)).take 32 ≠
 AbiEntry.wordBytes 32 := by decide +kernel

/-- Corrupt initial pointer, outside the theorem's valid heap premise.
This is stuck memory, not a certified ABI validation revert. -/
theorem corrupt_reference (pipeline : Roadmap.Pipeline) :
 (execS (global pipeline) frame 6 0 none (statement declaration typed)
  (caller 2 threeHundred older)).run (Source.L0 environment,state [0,255,128] false) =
 (.error (.stuck "dangling memory reference"),(Source.L0 environment,state [0,255,128] false)) := by rfl

/-- Test-only lossless decimal-byte rendering. -/
def render (bytes : Roadmap.Bytes) : String :=
 "[" ++ String.intercalate "," (bytes.map (fun b => toString b.toNat)) ++ "]"
def samples : List (Roadmap.Bytes × Roadmap.Word) :=
 [([],threeHundred),([0,255,128],threeHundred),(List.replicate 31 0,maxWord),
  (List.replicate 32 255,threeHundred),(List.replicate 33 128,maxWord)]
#eval String.intercalate "\n" (samples.map (fun (bytes,marker) =>
 render (abiLayout [(true,bytes),(false,wordBytes marker)])))
#eval String.intercalate "\n" (samples.map (fun (bytes,marker) =>
 render (AbiEntry.encodeArgs (abiValues bytes marker))))

#print axioms arguments_run
#print axioms marker_word
#print axioms encoding_run
#print axioms source_run
#print axioms layout
#print axioms abi_agreement
#print axioms source_typed
#print axioms client
#print axioms heap_agrees
#print axioms old_alias
#print axioms wrong_marker
#print axioms wrong_offset
#print axioms corrupt_reference
end Solidity.Lowering.V08.LiteralFailureDynamicErrorControls
