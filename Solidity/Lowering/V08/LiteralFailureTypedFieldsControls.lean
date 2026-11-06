import Solidity.Lowering.V08.LiteralFailureTypedFields
import Solidity.Lowering.V08.SourceCustomErrorControls
namespace Solidity.Lowering.V08.LiteralFailureTypedFieldsControls
open Solidity Source
open LiteralFailureTypedFields

def types : RCtx := [.bool,.string .memory,.int IntTy.u256,.bool,.bytes .memory,.string .memory,.bool]
def declaration : Decl := ⟨.error,"FieldMix7",some "C",false,.error "FieldMix7"
 (.cons (.errorParam (.elem .bool) none) (.cons (.errorParam (.elem .string) none) (.cons (.errorParam (.elem (.int false 256 (by decide +kernel))) none) (.cons (.errorParam (.elem .bool) none) (.cons (.errorParam (.elem .bytes) none) (.cons (.errorParam (.elem .string) none) (.cons (.errorParam (.elem .bool) none) (.nil))))))))⟩
def environment : Env := ⟨[SourceCustomErrorControls.savedDecl,SourceCustomErrorControls.scratchDecl,declaration]⟩
theorem member : declaration ∈ environment.decls := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
theorem typed : declaration.paramTys environment=some types := rfl

def frame := SourceCustomErrorControls.frame
def empty : St environment :=
 ⟨⟨⟨fun _=>Account.empty _⟩,Transient.empty,[]⟩,Source.Heap.empty,[],[],⟨[],.nil⟩,Source.FailureExecution.Cursor.empty⟩
def state (first second third : Roadmap.Bytes) : St environment :=
 {empty with
  heap:=((((Source.Heap.empty.alloc ⟨.bytes .memory,.bytes [9,7]⟩).1.alloc
   ⟨.string .memory,.string first⟩).1.alloc ⟨.bytes .memory,.bytes second⟩).1.alloc
   ⟨.string .memory,.string third⟩).1
  ex:=empty.ex.run [.account frame.this (fun account=>{account with balance:=73,nonce:=4,storage:=account.storage.write SourceCustomErrorControls.saved (.bool true)}),
   .transient frame.this (fun transient=>transient.write SourceCustomErrorControls.scratch (.bool true))]
  events:=[.call frame.this ⟨7,by decide +kernel⟩ [0,255] false]
  logs:=[(frame.this,[171,0,255])]
  fnLocals:=⟨[.bool],.cons (.bool true) .nil⟩}
def context : RCtx := types++[.bytes .memory,.bool]
def locals (x y z : Bool) (last : Nat) (w : Roadmap.Word) : Locals environment.layout context :=
 .cons (.bool x) (.cons (.memRef rfl 1) (.cons (SourceEnvironment.sourceWord w) (.cons (.bool y) (.cons (.memRef rfl 2) (.cons (.memRef rfl last) (.cons (.bool z) (.cons (.memRef rfl 0) (.cons (.bool true) (.nil)))))))))
def values (x y z : Bool) (last : Nat) (w : Roadmap.Word) : Source.Vals environment.layout types :=
 .cons (.bool x) (.cons (.memRef rfl 1) (.cons (SourceEnvironment.sourceWord w) (.cons (.bool y) (.cons (.memRef rfl 2) (.cons (.memRef rfl last) (.cons (.bool z) (.nil)))))))
def arguments : RConvArgs environment context types :=
 .cons (.local .here) rfl (.cons (.local (.there .here)) rfl (.cons (.local (.there (.there .here))) rfl (.cons (.local (.there (.there (.there .here)))) rfl (.cons (.local (.there (.there (.there (.there .here))))) rfl (.cons (.local (.there (.there (.there (.there (.there .here)))))) rfl (.cons (.local (.there (.there (.there (.there (.there (.there .here))))))) rfl (.nil)))))))
def expressionArguments : RArgs environment context types :=
 .cons (.local .here) (.cons (.local (.there .here)) (.cons (.local (.there (.there .here))) (.cons (.local (.there (.there (.there .here)))) (.cons (.local (.there (.there (.there (.there .here))))) (.cons (.local (.there (.there (.there (.there (.there .here)))))) (.cons (.local (.there (.there (.there (.there (.there (.there .here))))))) (.nil)))))))
theorem lookups (x y z : Bool) (last : Nat) (w : Roadmap.Word) :
 LiteralFailureMixedCustomError.LocalArgs (locals x y z last w) arguments (values x y z last w) :=
 .cons (.here) rfl (.cons ((.there .here)) rfl (.cons ((.there (.there .here))) rfl (.cons ((.there (.there (.there .here)))) rfl (.cons ((.there (.there (.there (.there .here))))) rfl (.cons ((.there (.there (.there (.there (.there .here)))))) rfl (.cons ((.there (.there (.there (.there (.there (.there .here))))))) rfl (.nil)))))))
theorem expression_lookups (x y z : Bool) (last : Nat) (w : Roadmap.Word) :
 LiteralFailureMixedExpression.LocalArgs (locals x y z last w) expressionArguments (values x y z last w) :=
 .cons (.here) (.cons ((.there .here)) (.cons ((.there (.there .here))) (.cons ((.there (.there (.there .here)))) (.cons ((.there (.there (.there (.there .here))))) (.cons ((.there (.there (.there (.there (.there .here)))))) (.cons ((.there (.there (.there (.there (.there (.there .here))))))) (.nil)))))))
def program : Program environment :=
 {body:=fun _=>none,consts:=fun _=>none,inits:=fun _=>[],ctor:=fun _=>none,
  ctorLocals:=fun _=>[],baseArgs:=fun _=>[],contracts:=["C"]}
def global (p : Roadmap.Pipeline) : Glob environment :=
 {prog:=program,pipeline:=p,fixed:=Roadmap.Controls.toyFixed,balance0:=fun _=>⟨100,by decide +kernel⟩,
  hasCode:=fun _ _=>false,callee:=fun _=>.answer (.success []),timestamp:=⟨12345,by decide +kernel⟩}
def encoded (x y z : Bool) (first second lastBytes : Roadmap.Bytes) (w : Roadmap.Word) :
 AbiEntry.Vals [.word .bool,.bytes,.word (.uint 256),.word .bool,.bytes,.bytes,.word .bool] :=
 .cons (.word (BoolErrorAbi.word x)) (.cons (.bytes first) (.cons (.word (LiteralFailureDynamicError.abiWord w)) (.cons (.word (BoolErrorAbi.word y)) (.cons (.bytes second) (.cons (.bytes lastBytes) (.cons (.word (BoolErrorAbi.word z)) (.nil)))))))
theorem fields (x y z : Bool) (first second third lastBytes : Roadmap.Bytes) (last : Nat) (w : Roadmap.Word)
 (heap : (state first second third).heap.get last=some ⟨.string .memory,.string lastBytes⟩) :
 Fields (state first second third) (values x y z last w) (encoded x y z first second lastBytes w) :=
 .boolean x (.string 1 first rfl (.uint w (.boolean y
  (.bytes 2 second (.inl rfl) (.string last lastBytes heap (.boolean z .nil))))))
def body (x y z : Bool) (first second lastBytes : Roadmap.Bytes) (w : Roadmap.Word) :=
 AbiEntry.encodeArgs (encoded x y z first second lastBytes w)
def packet (p : Roadmap.Pipeline) (x y z : Bool) (first second lastBytes : Roadmap.Bytes) (w : Roadmap.Word) :=
 (global p).selector (sigOf environment.layout declaration.name types)++body x y z first second lastBytes w
def statement : RStmt environment [] false .body context context := .revertError declaration typed arguments

theorem actual_error (p : Roadmap.Pipeline) (x y z : Bool)
 (first second third lastBytes : Roadmap.Bytes) (last : Nat) (w : Roadmap.Word)
 (heap : (state first second third).heap.get last=some ⟨.string .memory,.string lastBytes⟩) :
 (execS (global p) frame 11 0 none statement (locals x y z last w)).run (L0 environment,state first second third)=
 (.error (.revert (packet p x y z first second lastBytes w)),(L0 environment,state first second third)) :=
 source_run (global p) frame 0 declaration typed _ _ (lookups x y z last w)
 (fields x y z first second third lastBytes last w heap)
theorem actual_expression (p : Roadmap.Pipeline) (x y z : Bool)
 (first second third lastBytes : Roadmap.Bytes) (last : Nat) (w : Roadmap.Word)
 (heap : (state first second third).heap.get last=some ⟨.string .memory,.string lastBytes⟩) :
 (evalE (global p) frame 11 (.abiEncode .encode expressionArguments)).run
 (locals x y z last w,state first second third)=
 (.ok (.val (.memRef rfl 4)),(locals x y z last w,
  SourceKeccak.afterLiteral (state first second third) (body x y z first second lastBytes w))) :=
 expression_run (global p) frame 0 _ _ (expression_lookups x y z last w)
 (fields x y z first second third lastBytes last w heap)
theorem retained (x y z : Bool) (first second third lastBytes : Roadmap.Bytes) (last : Nat) (w : Roadmap.Word)
 (heap : (state first second third).heap.get last=some ⟨.string .memory,.string lastBytes⟩) :
 Fields (SourceKeccak.afterLiteral (state first second third) (body x y z first second lastBytes w))
 (values x y z last w) (encoded x y z first second lastBytes w) :=
 fields_after _ _ (fields x y z first second third lastBytes last w heap)
theorem old0 (first second third bs : Roadmap.Bytes) :
 (SourceKeccak.afterLiteral (state first second third) bs).heap.get 0=some ⟨.bytes .memory,.bytes [9,7]⟩ :=
 LiteralFailureMixedExpression.old_object _ _ _ _ rfl
theorem unused3 (first second third bs : Roadmap.Bytes) :
 (SourceKeccak.afterLiteral (state first second third) bs).heap.get 3=some ⟨.string .memory,.string third⟩ :=
 LiteralFailureMixedExpression.old_object _ _ _ _ rfl
theorem fresh (first second third bs : Roadmap.Bytes) :
 (SourceKeccak.afterLiteral (state first second third) bs).heap.get 4=some ⟨.bytes .memory,.bytes bs⟩ ∧
 (SourceKeccak.afterLiteral (state first second third) bs).heap.next=5 :=
 ⟨SourceKeccak.allocated _ _,rfl⟩
theorem wrong_kind (st : St environment) (b : Bool) :
 ¬Fields st (Source.Vals.cons (.bool b) .nil)
  (AbiEntry.Vals.cons (.word (LiteralFailureDynamicError.abiWord (LiteralFailureBoolPrefix.boolWord b))) .nil) := by
 intro bad
 cases bad

theorem dangling_error (first second third : Roadmap.Bytes) :
 (execS (global .legacy) frame 11 0 none statement
  (locals false true false 99 ⟨300,by decide +kernel⟩)).run (L0 environment,state first second third)=
 (.error (.stuck "dangling memory reference"),(L0 environment,state first second third)) := rfl
theorem dangling_expression (first second third : Roadmap.Bytes) :
 (evalE (global .legacy) frame 11 (.abiEncode .encode expressionArguments)).run
 (locals false true false 99 ⟨300,by decide +kernel⟩,state first second third)=
 (.error (.stuck "dangling memory reference"),(locals false true false 99 ⟨300,by decide +kernel⟩,state first second third)) := rfl
theorem timeout (x y z : Bool) (first second third : Roadmap.Bytes) (w : Roadmap.Word) :
 (execS (global .legacy) frame 1 0 none statement (locals x y z 3 w)).run (L0 environment,state first second third)=
 (.error .timeout,(L0 environment,state first second third)) := rfl

def render (bs : Roadmap.Bytes) := "["++String.intercalate "," (bs.map (fun b=>toString b.toNat))++"]"
def observe (p : Roadmap.Pipeline) (expression : Bool) (x y z : Bool)
 (first second third : Roadmap.Bytes) (last : Nat) (w : Roadmap.Word) : String :=
 let initial := (locals x y z last w,state first second third)
 if expression then
  let result := (evalE (global p) frame 11 (.abiEncode .encode expressionArguments)).run initial
  match result.1 with
  | .ok (.val (.memRef _ address)) =>
   match result.2.2.heap.get address with
   | some ⟨_,.bytes bs⟩ => "{\"pointer\":"++toString address++",\"cursor\":"++toString result.2.2.heap.next++",\"bytes\":"++render bs++"}"
   | _ => "{\"bad_heap\":true}"
  | _ => "{\"bad_run\":true}"
 else
  let result := (execS (global p) frame 11 0 none statement initial.1).run (L0 environment,initial.2)
  match result.1 with
  | .error (.revert bs) => "{\"cursor\":"++toString result.2.2.heap.next++",\"bytes\":"++render bs++"}"
  | _ => "{\"bad_run\":true}"
def observations (p : Roadmap.Pipeline) (expression : Bool) : List String :=
 [observe p expression false false false [] [] [] 3 ⟨0,by decide +kernel⟩,
  observe p expression true false true [0,255] [128] [195,169] 3 ⟨300,by decide +kernel⟩,
  observe p expression false true false (List.replicate 31 255) (List.replicate 32 0) (List.replicate 33 128) 3 ⟨42,by decide +kernel⟩,
  observe p expression true true true (List.replicate 33 128) [] (List.replicate 31 0) 3 ⟨2^256-1,by omega⟩,
  observe p expression false false true [] (List.replicate 33 128) (List.replicate 32 255) 3 ⟨2^255,by decide +kernel⟩,
  observe p expression true false false [0,255] [128] [171] 1 ⟨300,by decide +kernel⟩]
#eval IO.println ("TYPED_FIELDS_ERROR_LEGACY=["++String.intercalate "," (observations .legacy false)++"]")
#eval IO.println ("TYPED_FIELDS_ERROR_VIAIR=["++String.intercalate "," (observations .viaIR false)++"]")
#eval IO.println ("TYPED_FIELDS_EXPRESSION_LEGACY=["++String.intercalate "," (observations .legacy true)++"]")
#eval IO.println ("TYPED_FIELDS_EXPRESSION_VIAIR=["++String.intercalate "," (observations .viaIR true)++"]")
#print axioms source_parts
#print axioms codec_parts
#print axioms normalized
#print axioms source_encoding
#print axioms codec_encoding
#print axioms encoding_run
#print axioms encodingAt
#print axioms source_run
#print axioms expression_run
#print axioms fields_after
#print axioms member
#print axioms typed
#print axioms lookups
#print axioms expression_lookups
#print axioms fields
#print axioms actual_error
#print axioms actual_expression
#print axioms retained
#print axioms old0
#print axioms unused3
#print axioms fresh
#print axioms wrong_kind
#print axioms dangling_error
#print axioms dangling_expression
#print axioms timeout
end Solidity.Lowering.V08.LiteralFailureTypedFieldsControls
