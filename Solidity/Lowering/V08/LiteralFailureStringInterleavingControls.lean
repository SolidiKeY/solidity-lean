import Solidity.Lowering.V08.LiteralFailureStringInterleaving
import Solidity.Lowering.V08.SourceCustomErrorControls
namespace Solidity.Lowering.V08.LiteralFailureStringInterleavingControls
open Solidity Source
open LiteralFailureStringInterleaving

def types : RCtx := [.int IntTy.u256,.string .memory,.bytes .memory,.string .memory,.int IntTy.u256]
def declaration : Decl := ⟨.error,"Interleaved",some "C",false,.error "Interleaved"
 (.cons (.errorParam (.elem (.int false 256 (by decide +kernel))) none)
  (.cons (.errorParam (.elem .string) none)
   (.cons (.errorParam (.elem .bytes) none)
    (.cons (.errorParam (.elem .string) none)
     (.cons (.errorParam (.elem (.int false 256 (by decide +kernel))) none) .nil)))))⟩
def environment : Env := ⟨[SourceCustomErrorControls.savedDecl,SourceCustomErrorControls.scratchDecl,declaration]⟩
theorem member : declaration ∈ environment.decls := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
theorem typed : declaration.paramTys environment=some types := rfl

def frame := SourceCustomErrorControls.frame
def empty : St environment :=
 ⟨⟨⟨fun _=>Account.empty _⟩,Transient.empty,[]⟩,Source.Heap.empty,[],[],⟨[],.nil⟩⟩
def state (first second third : Roadmap.Bytes) : St environment :=
 {empty with
  heap:=((((Source.Heap.empty.alloc ⟨.bytes .memory,.bytes [9,7]⟩).1.alloc
   ⟨.string .memory,.string first⟩).1.alloc ⟨.bytes .memory,.bytes second⟩).1.alloc
   ⟨.string .memory,.string third⟩).1
  ex:=empty.ex.run [.account frame.this (fun account=>{account with balance:=⟨73,by decide +kernel⟩,nonce:=4,storage:=account.storage.write SourceCustomErrorControls.saved (.bool true)}),
   .transient frame.this (fun transient=>transient.write SourceCustomErrorControls.scratch (.bool true))]
  events:=[.call frame.this ⟨7,by decide +kernel⟩ [0,255] false]
  logs:=[(frame.this,[171,0,255])]
  fnLocals:=⟨[.bool],.cons (.bool true) .nil⟩}
def context : RCtx := types++[.bytes .memory,.bool]
def locals (last : Nat) (a b : Roadmap.Word) : Locals environment.layout context :=
 .cons (SourceEnvironment.sourceWord a) (.cons (.memRef rfl 1)
  (.cons (.memRef rfl 2) (.cons (.memRef rfl last) (.cons (SourceEnvironment.sourceWord b)
   (.cons (.memRef rfl 0) (.cons (.bool true) .nil))))))
def values (last : Nat) (a b : Roadmap.Word) : Source.Vals environment.layout types :=
 .cons (SourceEnvironment.sourceWord a) (.cons (.memRef rfl 1)
  (.cons (.memRef rfl 2) (.cons (.memRef rfl last) (.cons (SourceEnvironment.sourceWord b) .nil))))
def witness (last : Nat) (a b : Roadmap.Word) :
 Source.Vals environment.layout [.int IntTy.u256,.bytes .memory,.bytes .memory,.bytes .memory,.int IntTy.u256] :=
 .cons (SourceEnvironment.sourceWord a) (.cons (.memRef rfl 1)
  (.cons (.memRef rfl 2) (.cons (.memRef rfl last) (.cons (SourceEnvironment.sourceWord b) .nil))))
theorem related (last : Nat) (a b : Roadmap.Word) : StringBytes (values last a b) (witness last a b) :=
 .keep _ (.string 1 (.keep _ (.string last (.keep _ .nil))))
def arguments : RConvArgs environment context types :=
 .cons (.local .here) rfl (.cons (.local (.there .here)) rfl
  (.cons (.local (.there (.there .here))) rfl (.cons (.local (.there (.there (.there .here)))) rfl
   (.cons (.local (.there (.there (.there (.there .here))))) rfl .nil))))
def expressionArguments : RArgs environment context types :=
 .cons (.local .here) (.cons (.local (.there .here))
  (.cons (.local (.there (.there .here))) (.cons (.local (.there (.there (.there .here))))
   (.cons (.local (.there (.there (.there (.there .here))))) .nil))))
theorem lookups (last : Nat) (a b : Roadmap.Word) :
 LiteralFailureMixedCustomError.LocalArgs (locals last a b) arguments (values last a b) :=
 .cons .here rfl (.cons (.there .here) rfl (.cons (.there (.there .here)) rfl
  (.cons (.there (.there (.there .here))) rfl (.cons (.there (.there (.there (.there .here)))) rfl .nil))))
theorem expression_lookups (last : Nat) (a b : Roadmap.Word) :
 LiteralFailureMixedExpression.LocalArgs (locals last a b) expressionArguments (values last a b) :=
 .cons .here (.cons (.there .here) (.cons (.there (.there .here))
  (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil))))
def program : Program environment :=
 {body:=fun _=>none,consts:=fun _=>none,inits:=fun _=>[],ctor:=fun _=>none,
  ctorLocals:=fun _=>[],baseArgs:=fun _=>[],contracts:=["C"]}
def global (p : Roadmap.Pipeline) : Glob environment :=
 {prog:=program,pipeline:=p,fixed:=Roadmap.Controls.toyFixed,balance0:=fun _=>⟨100,by decide +kernel⟩,
  hasCode:=fun _ _=>false,callee:=fun _=>.answer (.success []),timestamp:=⟨12345,by decide +kernel⟩}
def encoded (first second last : Roadmap.Bytes) (a b : Roadmap.Word) :
 AbiEntry.Vals [.word (.uint 256),.bytes,.bytes,.bytes,.word (.uint 256)] :=
 .cons (.word (LiteralFailureDynamicError.abiWord a)) (.cons (.bytes first)
  (.cons (.bytes second) (.cons (.bytes last) (.cons (.word (LiteralFailureDynamicError.abiWord b)) .nil))))
def parts (first second last : Roadmap.Bytes) (a b : Roadmap.Word) :=
 [(false,wordBytes a),(true,first),(true,second),(true,last),(false,wordBytes b)]
theorem fields (first second third lastBytes : Roadmap.Bytes) (last : Nat) (a b : Roadmap.Word)
 (heap : (state first second third).heap.get last=some ⟨.string .memory,.string lastBytes⟩) :
 LiteralFailureMixedEncoding.Represented (state first second third) (witness last a b)
  (encoded first second lastBytes a b) (parts first second lastBytes a b) :=
 .uint a (.bytes 1 first (.inr rfl) (.bytes 2 second (.inl rfl)
  (.bytes last lastBytes (.inr heap) (.uint b .nil))))
def packet (p : Roadmap.Pipeline) (first second last : Roadmap.Bytes) (a b : Roadmap.Word) : Roadmap.Bytes :=
 (global p).selector (sigOf environment.layout declaration.name types)++AbiEntry.encodeArgs (encoded first second last a b)
def statement : RStmt environment [] false .body context context := .revertError declaration typed arguments

theorem actual_error (p : Roadmap.Pipeline) (first second third lastBytes : Roadmap.Bytes)
 (last : Nat) (a b : Roadmap.Word)
 (heap : (state first second third).heap.get last=some ⟨.string .memory,.string lastBytes⟩) :
 (execS (global p) frame 9 0 none statement (locals last a b)).run (L0 environment,state first second third)=
 (.error (.revert (packet p first second lastBytes a b)),(L0 environment,state first second third)) :=
 source_run (global p) frame 0 declaration typed _ _ (lookups last a b) (related last a b)
  (fields first second third lastBytes last a b heap)
theorem actual_expression (p : Roadmap.Pipeline) (first second third lastBytes : Roadmap.Bytes)
 (last : Nat) (a b : Roadmap.Word)
 (heap : (state first second third).heap.get last=some ⟨.string .memory,.string lastBytes⟩) :
 (evalE (global p) frame 9 (.abiEncode .encode expressionArguments)).run (locals last a b,state first second third)=
 (.ok (.val (.memRef rfl 4)),(locals last a b,
  SourceKeccak.afterLiteral (state first second third) (AbiEntry.encodeArgs (encoded first second lastBytes a b)))) :=
 expression_run (global p) frame 0 _ _ (expression_lookups last a b) (related last a b)
  (fields first second third lastBytes last a b heap)
theorem retained (first second third lastBytes : Roadmap.Bytes) (last : Nat) (a b : Roadmap.Word)
 (heap : (state first second third).heap.get last=some ⟨.string .memory,.string lastBytes⟩) :
 LiteralFailureMixedEncoding.Represented
  (SourceKeccak.afterLiteral (state first second third) (AbiEntry.encodeArgs (encoded first second lastBytes a b)))
  (witness last a b) (encoded first second lastBytes a b) (parts first second lastBytes a b) :=
 LiteralFailureMixedExpression.fields_after _ _ (fields first second third lastBytes last a b heap)
theorem older (first second third : Roadmap.Bytes) (bs : Roadmap.Bytes) :
 (SourceKeccak.afterLiteral (state first second third) bs).heap.get 0=some ⟨.bytes .memory,.bytes [9,7]⟩ :=
 LiteralFailureMixedExpression.old_object _ _ _ _ rfl

theorem unused_third (first second third bs : Roadmap.Bytes) :
 (SourceKeccak.afterLiteral (state first second third) bs).heap.get 3=some ⟨.string .memory,.string third⟩ :=
 LiteralFailureMixedExpression.old_object _ _ _ _ rfl

theorem alias_error (p : Roadmap.Pipeline) (first second third : Roadmap.Bytes) (a b : Roadmap.Word) :
 (execS (global p) frame 9 0 none statement (locals 1 a b)).run (L0 environment,state first second third)=
 (.error (.revert (packet p first second first a b)),(L0 environment,state first second third)) :=
 actual_error p first second third first 1 a b rfl

theorem fresh (first second third : Roadmap.Bytes) (bs : Roadmap.Bytes) :
 (SourceKeccak.afterLiteral (state first second third) bs).heap.get 4=some ⟨.bytes .memory,.bytes bs⟩ ∧
 (SourceKeccak.afterLiteral (state first second third) bs).heap.next=5 :=
 ⟨SourceKeccak.allocated _ _,rfl⟩
theorem timeout (first second third : Roadmap.Bytes) (a b : Roadmap.Word) :
 (execS (global .legacy) frame 1 0 none statement (locals 3 a b)).run (L0 environment,state first second third)=
 (.error .timeout,(L0 environment,state first second third)) := rfl

theorem dangling_error (first second third : Roadmap.Bytes) :
 (execS (global .legacy) frame 9 0 none statement
  (locals 99 ⟨42,by decide +kernel⟩ ⟨300,by decide +kernel⟩)).run (L0 environment,state first second third)=
 (.error (.stuck "dangling memory reference"),(L0 environment,state first second third)) := by
 first | rfl | decide +kernel | omega

theorem dangling_expression (first second third : Roadmap.Bytes) :
 (evalE (global .legacy) frame 9 (.abiEncode .encode expressionArguments)).run
  (locals 99 ⟨42,by decide +kernel⟩ ⟨300,by decide +kernel⟩,state first second third)=
 (.error (.stuck "dangling memory reference"),
  (locals 99 ⟨42,by decide +kernel⟩ ⟨300,by decide +kernel⟩,state first second third)) := by
 first | rfl | decide +kernel | omega

theorem wrong_cursor (first second third bs : Roadmap.Bytes) :
 (SourceKeccak.afterLiteral (state first second third) bs).heap.next≠4 := by
 change (5 : Nat)≠4
 decide +kernel

theorem static_error (p : Roadmap.Pipeline) (first second third : Roadmap.Bytes) (a b : Roadmap.Word) :
 (execS (global p) {frame with static:=true} 9 0 none statement (locals 3 a b)).run
 (L0 environment,state first second third)=
 (.error (.revert (packet p first second third a b)),(L0 environment,state first second third)) :=
 source_run (global p) {frame with static:=true} 0 declaration typed _ _ (lookups 3 a b)
 (related 3 a b) (fields first second third third 3 a b rfl)

def render (bs : Roadmap.Bytes) := "["++String.intercalate "," (bs.map (fun b=>toString b.toNat))++"]"
def observe (p : Roadmap.Pipeline) (expression : Bool) (first second third : Roadmap.Bytes)
 (last : Nat) (a b : Roadmap.Word) : String :=
 let initial := (locals last a b,state first second third)
 if expression then
  let result := (evalE (global p) frame 9 (.abiEncode .encode expressionArguments)).run initial
  match result.1 with
  | .ok (.val (.memRef _ address)) =>
   match result.2.2.heap.get address with
   | some ⟨_,.bytes bs⟩ => "{\"pointer\":"++toString address++",\"cursor\":"++toString result.2.2.heap.next++",\"bytes\":"++render bs++"}"
   | _ => "{\"bad_heap\":true}"
  | _ => "{\"bad_run\":true}"
 else
  let result := (execS (global p) frame 9 0 none statement initial.1).run (L0 environment,initial.2)
  match result.1 with
  | .error (.revert bs) => "{\"cursor\":"++toString result.2.2.heap.next++",\"bytes\":"++render bs++"}"
  | _ => "{\"bad_run\":true}"
def observations (p : Roadmap.Pipeline) (expression : Bool) : List String :=
 [observe p expression [] [] [] 3 ⟨0,by decide +kernel⟩ ⟨2^256-1,by omega⟩,
  observe p expression [0,255] [128] [195,169] 3 ⟨42,by decide +kernel⟩ ⟨300,by decide +kernel⟩,
  observe p expression (List.replicate 31 255) (List.replicate 32 0) (List.replicate 33 128) 3 ⟨300,by decide +kernel⟩ ⟨42,by decide +kernel⟩,
  observe p expression (List.replicate 33 128) [] (List.replicate 31 0) 3 ⟨2^255,by decide +kernel⟩ ⟨300,by decide +kernel⟩,
  observe p expression [] (List.replicate 33 128) (List.replicate 32 255) 3 ⟨2^256-1,by omega⟩ ⟨2^255,by decide +kernel⟩,
  observe p expression [0,255] [128] [171] 1 ⟨42,by decide +kernel⟩ ⟨300,by decide +kernel⟩]
#eval IO.println ("INTERLEAVED_ERROR_LEGACY=["++String.intercalate "," (observations .legacy false)++"]")
#eval IO.println ("INTERLEAVED_ERROR_VIAIR=["++String.intercalate "," (observations .viaIR false)++"]")
#eval IO.println ("INTERLEAVED_EXPRESSION_LEGACY=["++String.intercalate "," (observations .legacy true)++"]")
#eval IO.println ("INTERLEAVED_EXPRESSION_VIAIR=["++String.intercalate "," (observations .viaIR true)++"]")
#print axioms parts_eq
#print axioms encoding_eq
#print axioms encoding_run
#print axioms encodingAt
#print axioms source_run
#print axioms expression_run
#print axioms member
#print axioms typed
#print axioms related
#print axioms lookups
#print axioms expression_lookups
#print axioms fields
#print axioms actual_error
#print axioms actual_expression
#print axioms retained
#print axioms older
#print axioms unused_third
#print axioms alias_error
#print axioms fresh
#print axioms timeout
#print axioms dangling_error
#print axioms dangling_expression
#print axioms wrong_cursor
#print axioms static_error
end Solidity.Lowering.V08.LiteralFailureStringInterleavingControls
