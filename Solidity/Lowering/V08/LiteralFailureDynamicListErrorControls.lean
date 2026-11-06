import Solidity.Lowering.V08.LiteralFailureDynamicListError
import Solidity.Lowering.V08.SourceCustomErrorControls

namespace Solidity.Lowering.V08.LiteralFailureDynamicListErrorControls
open Solidity Source LiteralFailureDynamicListError

def parameters : Nat → Source.Syn (.list .errorParam)
 | 0 => .nil
 | n+1 => .cons (.errorParam (.elem .bytes) none) (parameters n)
def declaration (n : Nat) : Decl :=
 let name := "Many" ++ toString n
 ⟨.error,name,some "C",false,.error name (parameters n)⟩
def environment (n : Nat) : Env := ⟨[declaration n]⟩

theorem parameter_types (E : Env) (n : Nat) :
 (parameters n).tys E (some "C") .memory = some (List.replicate n (.bytes .memory)) := by
 induction n with
 | zero => rfl
 | succ n ih =>
   simp only [parameters,Source.Syn.tys,Source.Elem.ty,ih,List.replicate_succ]
   rfl

def context : RCtx := [.bytes .memory,.bytes .memory,.bytes .memory,.bool]
def locals (n : Nat) : Locals (environment n).layout context :=
 .cons (.memRef rfl 1) (.cons (.memRef rfl 2) (.cons (.memRef rfl 0) (.cons (.bool true) .nil)))
def refs : List (Source.Idx context (.bytes .memory)) := [.here,.there .here,.here]
def repeated (n : Nat) : List (Source.Idx context (.bytes .memory)) := List.replicate n .here

def empty (n : Nat) : St (environment n) :=
 ⟨⟨⟨fun _ => Account.empty _⟩,Transient.empty,[]⟩,Source.Heap.empty,[],[],⟨[],.nil⟩, Source.FailureExecution.Cursor.empty⟩
def frame := SourceCustomErrorControls.frame
def state (n : Nat) (first second : Roadmap.Bytes) : St (environment n) :=
 {empty n with
  heap := ((((Source.Heap.empty.alloc ⟨.bytes .memory,.bytes [9,7]⟩).1).alloc ⟨.bytes .memory,.bytes first⟩).1.alloc ⟨.string .memory,.string second⟩).1
  ex := (empty n).ex.run [.account frame.this (fun account => {account with balance := 73,nonce:=4})]}
def program (n : Nat) : Program (environment n) :=
 {body:=fun _=>none,consts:=fun _=>none,inits:=fun _=>[],ctor:=fun _=>none,
  ctorLocals:=fun _=>[],baseArgs:=fun _=>[],contracts:=["C"]}
def global (n : Nat) (pipeline : Roadmap.Pipeline) : Glob (environment n) :=
 {prog:=program n,pipeline:=pipeline,fixed:=Roadmap.Controls.toyFixed,
  balance0:=fun _=>⟨100,by decide +kernel⟩,hasCode:=fun _ _=>false,
  callee:=fun _=>.answer (.success []),timestamp:=⟨12345,by decide +kernel⟩}

theorem member (n : Nat) : declaration n ∈ (environment n).decls := List.mem_cons_self

theorem typed_three : (declaration 3).paramTys (environment 3) = some (types refs) := rfl

theorem typed_repeat (n : Nat) :
 (declaration n).paramTys (environment n) = some (types (repeated n)) := by
 change (parameters n).tys (environment n) (some "C") .memory =
  some (List.replicate (List.replicate n (.here : Source.Idx context (.bytes .memory))).length (.bytes .memory))
 rw [parameter_types,List.length_replicate]

theorem memory_three (first second : Roadmap.Bytes) :
 all_represented (locals 3) (state 3 first second) refs [first,second,first] :=
 ⟨⟨1,rfl,.inl rfl⟩,⟨⟨2,rfl,.inr rfl⟩,⟨⟨1,rfl,.inl rfl⟩,trivial⟩⟩⟩

theorem three_client (pipeline : Roadmap.Pipeline) (first second : Roadmap.Bytes) :
 (execS (global 3 pipeline) frame 7 0 none (statement (declaration 3) refs typed_three)
  (locals 3)).run (Source.L0 (environment 3),state 3 first second) =
 (.error (.revert ((global 3 pipeline).selector (sigOf (environment 3).layout (declaration 3).name (types refs)) ++
  AbiEntry.encodeArgs (abiValues [first,second,first]))),
  (Source.L0 (environment 3),state 3 first second)) :=
 source_typed (global 3 pipeline) frame 0 (declaration 3) refs typed_three _
  (locals 3) (state 3 first second) (memory_three first second)

theorem repeated_client (n extra : Nat) (pipeline : Roadmap.Pipeline) (first second : Roadmap.Bytes) :
 (execS (global n pipeline) frame (n+extra+4) 0 none
  (statement (declaration n) (repeated n) (typed_repeat n)) (locals n)).run
  (Source.L0 (environment n),state n first second) =
 (.error (.revert ((global n pipeline).selector
  (sigOf (environment n).layout (declaration n).name (types (repeated n))) ++
  AbiEntry.encodeArgs (abiValues (List.replicate n first)))),
  (Source.L0 (environment n),state n first second)) := by
 have memory : all_represented (locals n) (state n first second) (repeated n) (List.replicate n first) :=
  repeat_represented _ _ .here first ⟨1,rfl,.inl rfl⟩ n
 have result := source_typed (global n pipeline) frame extra (declaration n) (repeated n) (typed_repeat n)
  (List.replicate n first) (locals n) (state n first second) memory
 simpa only [repeated,List.length_replicate] using result

theorem wrong_head : (AbiEntry.encodeArgs (abiValues [[0,255],[128],[0,255]])).take 32 ≠
 AbiEntry.wordBytes 64 := by decide +kernel

theorem wrong_order : AbiEntry.encodeArgs (abiValues [[0,255],[128],[0,255]]) ≠
 AbiEntry.encodeArgs (abiValues [[0,255],[0,255],[128]]) := by decide +kernel

theorem wrong_count (first second : Roadmap.Bytes) :
 ¬ all_represented (locals 3) (state 3 first second) refs [first,second] := by
 intro memory
 have count := represented_length refs [first,second] _ _ memory
 change 3 = 2 at count
 cases count

theorem older_alias (n : Nat) (first second : Roadmap.Bytes) :
 (state n first second).heap.get 0 = some ⟨.bytes .memory,.bytes [9,7]⟩ ∧
 (state n first second).heap.next = 3 := ⟨rfl,rfl⟩

def render (bytes : Roadmap.Bytes) : String :=
 "[" ++ String.intercalate "," (bytes.map (fun b => toString b.toNat)) ++ "]"
def samples : List (List Roadmap.Bytes) :=
 [[],[[0,255]], [[],[],[]],[[0,255],[128],[0,255]],
  [List.replicate 31 0,[],List.replicate 31 0],
  [List.replicate 32 255,List.replicate 33 128,List.replicate 32 255],
  [List.replicate 33 128,List.replicate 32 255,List.replicate 33 128]]
#eval String.intercalate "\n" (samples.map (fun packets => render (abiLayout (packets.map (fun bytes => (true,bytes))))))
#eval String.intercalate "\n" (samples.map (fun packets => render (AbiEntry.encodeArgs (abiValues packets))))

#print axioms arguments_run
#print axioms represented_length
#print axioms repeat_represented
#print axioms part_run
#print axioms parts_run
#print axioms encoding_run
#print axioms source_run
#print axioms word_transport
#print axioms tail_agreement
#print axioms tail_extent
#print axioms source_tail_extent
#print axioms go_agreement
#print axioms heads_acc
#print axioms abi_agreement
#print axioms source_typed
#print axioms parameter_types
#print axioms typed_repeat
#print axioms three_client
#print axioms repeated_client
#print axioms wrong_head
#print axioms wrong_order
#print axioms wrong_count
#print axioms older_alias
end Solidity.Lowering.V08.LiteralFailureDynamicListErrorControls
