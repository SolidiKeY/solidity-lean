import Solidity.Lowering.V08.LiteralFailureStorageDecode
import Solidity.Lowering.V08.SourceCustomErrorControls

namespace Solidity.Lowering.V08.LiteralFailureStorageDecodeControls
open Solidity Source LiteralFailureStorageDecode

def declaration : Decl :=
 ⟨.stateVar,"packet",some "C",false,.stateVar (.elem .bytes) none none none false "packet" .none⟩
def environment : Env := ⟨[declaration]⟩
def path : Source.SPath := declaration.path

theorem typed : environment.pathTy path = some (.bytes .storage) := rfl

def empty : St environment :=
 ⟨⟨⟨fun _ => Account.empty _⟩,Transient.empty,[]⟩,Source.Heap.empty,[],[],⟨[],.nil⟩, Source.FailureExecution.Cursor.empty⟩
def frame := SourceCustomErrorControls.frame

def populated : St environment :=
 {empty with
  heap := (Source.Heap.empty.alloc ⟨.bytes .memory,.bytes [9,7]⟩).1
  ex := empty.ex.run [.account frame.this (fun account =>
   {account with balance := 43, storage := ((account.storage.write path (.int 2 (by decide +kernel))).write (path.go (.index 0)) (.fixedBytes [255] rfl)).write (path.go (.index 1)) (.fixedBytes [7] rfl)})]}

def caller : Locals environment.layout [.bytes .memory,.bool] :=
 .cons (.memRef rfl 0) (.cons (.bool true) .nil)

theorem length_two : (readLen frame path).run (caller,populated) =
 (.ok 2,(caller,populated)) := by rfl

theorem byte_zero : (readAt frame (path.go (.index 0)) (.fixedBytes 1 (by decide))).run
 (caller,populated) = (.ok (.fixedBytes [255] rfl),(caller,populated)) := by rfl

theorem byte_one : (readAt frame (path.go (.index 1)) (.fixedBytes 1 (by decide))).run
 (caller,populated) = (.ok (.fixedBytes [7] rfl),(caller,populated)) := by rfl

/-- Raw cell access has no source indexing bounds check; do not confuse it
with an accepted byte-array index expression. -/
theorem default_cell : (readAt frame (path.go (.index 2)) (.fixedBytes 1 (by decide))).run
 (caller,populated) = (.ok (.fixedBytes [0] rfl),(caller,populated)) := by rfl

theorem wrong_type : (readAt frame path .bool).run (caller,populated) =
 (.error (.stuck "storage cell type"),(caller,populated)) := by rfl

def length_client := length_read frame path typed (fun y => y = (caller,populated))
def byte_client (i : Nat) := byte_read frame path i typed (fun y => y = (caller,populated))

theorem old_alias : populated.heap.get 0 = some ⟨.bytes .memory,.bytes [9,7]⟩ := rfl

def reference : RVal environment.layout (.bytes .storage) := .val (.storRef rfl path)

theorem copied : (bytesOfRV frame 4 reference).run (caller,populated) =
 (.ok [255,7],(caller,populated)) := by rfl

theorem copy_exhausted : (bytesOfRV frame 3 reference).run (caller,populated) =
 (.error .timeout,(caller,populated)) := by rfl

theorem zero_fuel_empty : (loadBytes frame 0 path 0 0).run (caller,populated) =
 (.error .timeout,(caller,populated)) := by rfl

def program : Program environment :=
 {body:=fun _=>none,consts:=fun _=>none,inits:=fun _=>[],ctor:=fun _=>none,
  ctorLocals:=fun _=>[],baseArgs:=fun _=>[],contracts:=["C"]}
def global (pipeline : Roadmap.Pipeline) : Glob environment :=
 {prog:=program,pipeline:=pipeline,fixed:=Roadmap.Controls.toyFixed,
  balance0:=fun _=>⟨100,by decide +kernel⟩,hasCode:=fun _ _=>false,
  callee:=fun _=>.answer (.success []),timestamp:=⟨12345,by decide +kernel⟩}
def decoder : RExpr environment (.bytes .storage :: [.bytes .memory,.bool]) .bool :=
 .abiDecode (τs:=[.bool]) (.local .here) rfl rfl

theorem short_decode (pipeline : Roadmap.Pipeline) :
 (evalE (global pipeline) frame 5 decoder).run (.cons (.storRef rfl path) caller,populated) =
 (.error (.revert []),(.cons (.storRef rfl path) caller,populated)) := by rfl

theorem timeout_before_head (pipeline : Roadmap.Pipeline) :
 (evalE (global pipeline) frame 4 decoder).run (.cons (.storRef rfl path) caller,populated) =
 (.error .timeout,(.cons (.storRef rfl path) caller,populated)) := by rfl

/-- Canonical bool input held in actual storage: zero cells use the real
storage default, and only the final byte is explicitly nonzero. -/
def canonical : St environment :=
 {populated with ex := populated.ex.apply (.account frame.this (fun account =>
  {account with storage := (((account.storage.write path (.int 32 (by decide +kernel))).write (path.go (.index 0)) (.fixedBytes [0] rfl)).write (path.go (.index 1)) (.fixedBytes [0] rfl)).write (path.go (.index 31)) (.fixedBytes [1] rfl)}))}

def generic_client (pipeline : Roadmap.Pipeline) (fuel : Nat) {H : HeapTy} :=
 local_ok (H:=H) (global pipeline) frame fuel
  (.here : Source.Idx (.bytes .storage :: [.bytes .memory,.bool]) (.bytes .storage))
  (types:=[.bool]) rfl

/-- Test-only outcome rendering: host observations are not kernel proofs. -/
def render (bytes : List UInt8) : String :=
 "[" ++ String.intercalate "," (bytes.map (fun b => toString b.toNat)) ++ "]"
def observe_copy (fuel : Nat) (state : St environment) : String :=
 match (bytesOfRV frame fuel reference).run (caller,state) |>.1 with
 | .ok bytes => "{\"ok\":" ++ render bytes ++ "}"
 | .error .timeout => "{\"timeout\":true}"
 | .error _ => "{\"other_error\":true}"
#eval String.intercalate "\n" [observe_copy 4 populated,observe_copy 3 populated,observe_copy 34 canonical]
#eval match (evalE (global .legacy) frame 35 decoder).run
 (.cons (.storRef rfl path) caller,canonical) |>.1 with
 | .ok (.val (.bool value)) => if value then "{\"ok_bool\":true}" else "{\"ok_bool\":false}"
 | _ => "{\"other\":true}"

#print axioms load_bytes
#print axioms load_memory
#print axioms stored_bytes
#print axioms bytes_ok
#print axioms arm
#print axioms local_ok
#print axioms copied
#print axioms copy_exhausted
#print axioms zero_fuel_empty
#print axioms short_decode
#print axioms timeout_before_head
#print axioms generic_client
#print axioms read_cell
#print axioms read_at
#print axioms bytes_cell
#print axioms index_cell
#print axioms length_read
#print axioms byte_read
#print axioms length_two
#print axioms byte_zero
#print axioms byte_one
#print axioms default_cell
#print axioms wrong_type
#print axioms length_client
#print axioms byte_client
#print axioms old_alias
end Solidity.Lowering.V08.LiteralFailureStorageDecodeControls
