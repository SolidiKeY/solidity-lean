import Solidity.Lowering.V08.LiteralFailureCalldataCopy
import Solidity.Lowering.V08.SourceCustomErrorControls
namespace Solidity.Lowering.V08.LiteralFailureCalldataCopyControls
open Solidity Source
open LiteralFailureCalldataCopy

def tailTypes : RCtx := [.bool,.string .memory,.int IntTy.u256]
def types : RCtx := .bytes .memory::tailTypes
def declaration : Decl := ⟨.error,"Copied",some "C",false,.error "Copied"
 (.cons (.errorParam (.elem .bytes) none) (.cons (.errorParam (.elem .bool) none)
  (.cons (.errorParam (.elem .string) none)
   (.cons (.errorParam (.elem (.int false 256 (by decide +kernel))) none) .nil))))⟩
def environment : Env := ⟨[SourceCustomErrorControls.savedDecl,SourceCustomErrorControls.scratchDecl,declaration]⟩
theorem member : declaration ∈ environment.decls := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
theorem typed : declaration.paramTys environment=some types := rfl

def frame (data : Roadmap.Bytes) : Fr := {SourceCustomErrorControls.frame with cd:=data}
def empty : St environment :=
 ⟨⟨⟨fun _=>Account.empty _⟩,Transient.empty,[]⟩,Source.Heap.empty,[],[],⟨[],.nil⟩,Source.FailureExecution.Cursor.empty⟩
def state (text : Roadmap.Bytes) : St environment :=
 {empty with
  heap:=(((Source.Heap.empty.alloc ⟨.bytes .memory,.bytes [9,7]⟩).1.alloc
   ⟨.string .memory,.string text⟩).1.alloc ⟨.string .memory,.string [171,0]⟩).1
  ex:=empty.ex.run [.account (frame []).this (fun account=>{account with balance:=73,nonce:=4,storage:=account.storage.write SourceCustomErrorControls.saved (.bool true)}),
   .transient (frame []).this (fun transient=>transient.write SourceCustomErrorControls.scratch (.bool true))]
  events:=[.call (frame []).this ⟨7,by decide +kernel⟩ [0,255] false]
  logs:=[((frame []).this,[171,0,255])]
  fnLocals:=⟨[.bool],.cons (.bool true) .nil⟩}
def olderTypes : RCtx := tailTypes++[.bytes .memory,.bool]
def older (flag : Bool) (address : Nat) (w : Roadmap.Word) : Locals environment.layout olderTypes :=
 .cons (.bool flag) (.cons (.memRef rfl address)
  (.cons (SourceEnvironment.sourceWord w) (.cons (.memRef rfl 0) (.cons (.bool true) .nil))))
def values (flag : Bool) (address : Nat) (w : Roadmap.Word) : Source.Vals environment.layout tailTypes :=
 .cons (.bool flag) (.cons (.memRef rfl address) (.cons (SourceEnvironment.sourceWord w) .nil))
def tailArguments : RConvArgs environment (.bytes .calldata::olderTypes) tailTypes :=
 .cons (.local (.there .here)) rfl (.cons (.local (.there (.there .here))) rfl
  (.cons (.local (.there (.there (.there .here)))) rfl .nil))
theorem lookups (off len : Nat) (flag : Bool) (address : Nat) (w : Roadmap.Word) :
 LiteralFailureMixedCustomError.LocalArgs (initial off len (older flag address w)) tailArguments (values flag address w) :=
 .cons (.there .here) rfl (.cons (.there (.there .here)) rfl (.cons (.there (.there (.there .here))) rfl .nil))
def encoded (flag : Bool) (text : Roadmap.Bytes) (w : Roadmap.Word) :
 AbiEntry.Vals [.word .bool,.bytes,.word (.uint 256)] :=
 .cons (.word (BoolErrorAbi.word flag)) (.cons (.bytes text)
  (.cons (.word (LiteralFailureDynamicError.abiWord w)) .nil))
theorem fields (flag : Bool) (text : Roadmap.Bytes) (w : Roadmap.Word) :
 LiteralFailureTypedFields.Fields (state text) (values flag 1 w) (encoded flag text w) :=
 .boolean flag (.string 1 text rfl (.uint w .nil))
def program : Program environment :=
 {body:=fun _=>none,consts:=fun _=>none,inits:=fun _=>[],ctor:=fun _=>none,
  ctorLocals:=fun _=>[],baseArgs:=fun _=>[],contracts:=["C"]}
def global (p : Roadmap.Pipeline) : Glob environment :=
 {prog:=program,pipeline:=p,fixed:=Roadmap.Controls.toyFixed,balance0:=fun _=>⟨100,by decide +kernel⟩,
  hasCode:=fun _ _=>false,callee:=fun _=>.answer (.success []),timestamp:=⟨12345,by decide +kernel⟩}
def packet (p : Roadmap.Pipeline) (data : Roadmap.Bytes) (off len : Nat) (flag : Bool)
 (text : Roadmap.Bytes) (w : Roadmap.Word) : Roadmap.Bytes :=
 (global p).selector (sigOf environment.layout declaration.name types)++
 AbiEntry.encodeArgs (.cons (.bytes (copied (frame data) off len)) (encoded flag text w))
def statement : RStmt environment [] false .body (.bytes .calldata::olderTypes) (.bytes .calldata::olderTypes) :=
 .revertError declaration typed (arguments tailArguments)

theorem actual_error (p : Roadmap.Pipeline) (data : Roadmap.Bytes) (off len : Nat)
 (flag : Bool) (text : Roadmap.Bytes) (w : Roadmap.Word) :
 (execS (global p) (frame data) 8 0 none statement (initial off len (older flag 1 w))).run
 (L0 environment,state text)=
 (.error (.revert (packet p data off len flag text w)),
  (L0 environment,SourceKeccak.afterLiteral (state text) (copied (frame data) off len))) :=
 source_run (global p) (frame data) 0 declaration typed off len _ _ (lookups off len flag 1 w) (fields flag text w)
theorem copied_object (data text : Roadmap.Bytes) (off len : Nat) :
 (SourceKeccak.afterLiteral (state text) (copied (frame data) off len)).heap.get 3=
 some ⟨.bytes .memory,.bytes (copied (frame data) off len)⟩ ∧
 (SourceKeccak.afterLiteral (state text) (copied (frame data) off len)).heap.next=4 :=
 ⟨SourceKeccak.allocated _ _,rfl⟩
theorem old0 (data text : Roadmap.Bytes) (off len : Nat) :
 (SourceKeccak.afterLiteral (state text) (copied (frame data) off len)).heap.get 0=
 some ⟨.bytes .memory,.bytes [9,7]⟩ := LiteralFailureMixedExpression.old_object _ _ _ _ rfl
theorem old1 (data text : Roadmap.Bytes) (off len : Nat) :
 (SourceKeccak.afterLiteral (state text) (copied (frame data) off len)).heap.get 1=
 some ⟨.string .memory,.string text⟩ := LiteralFailureMixedExpression.old_object _ _ _ _ rfl

theorem timeout_before (data text : Roadmap.Bytes) (off len : Nat) (flag : Bool) (w : Roadmap.Word) :
 (execS (global .legacy) (frame data) 1 0 none statement (initial off len (older flag 1 w))).run
 (L0 environment,state text)=(.error .timeout,(L0 environment,state text)) := rfl
theorem timeout_after (data text : Roadmap.Bytes) (off len : Nat) (flag : Bool) (w : Roadmap.Word) :
 (execS (global .legacy) (frame data) 3 0 none statement (initial off len (older flag 1 w))).run
 (L0 environment,state text)=
 (.error .timeout,(L0 environment,SourceKeccak.afterLiteral (state text) (copied (frame data) off len))) := rfl
theorem dangling_after (data text : Roadmap.Bytes) (off len : Nat) :
 (execS (global .legacy) (frame data) 8 0 none statement
  (initial off len (older false 99 ⟨300,by decide +kernel⟩))).run (L0 environment,state text)=
 (.error (.stuck "dangling memory reference"),
  (L0 environment,SourceKeccak.afterLiteral (state text) (copied (frame data) off len))) := rfl

theorem revert_cursor (p : Roadmap.Pipeline) (data text : Roadmap.Bytes) (off len : Nat)
 (flag : Bool) (w : Roadmap.Word) :
 ((execS (global p) (frame data) 8 0 none statement (initial off len (older flag 1 w))).run
  (L0 environment,state text)).2.2.heap.next=4 := by
 rw [actual_error]
 rfl

theorem initial_state_wrong (p : Roadmap.Pipeline) (data text : Roadmap.Bytes) (off len : Nat)
 (flag : Bool) (w : Roadmap.Word) :
 (execS (global p) (frame data) 8 0 none statement (initial off len (older flag 1 w))).run
 (L0 environment,state text)≠(.error (.revert (packet p data off len flag text w)),(L0 environment,state text)) := by
 rw [actual_error]
 intro equal
 have cursor := congrArg (fun result => result.2.2.heap.next) equal
 change (4 : Nat)=3 at cursor
 cases cursor

def render (bs : Roadmap.Bytes) := "["++String.intercalate "," (bs.map (fun b=>toString b.toNat))++"]"
def observe (p : Roadmap.Pipeline) (data : Roadmap.Bytes) (off len : Nat) (flag : Bool)
 (text : Roadmap.Bytes) (w : Roadmap.Word) : String :=
 let result := (execS (global p) (frame data) 8 0 none statement
  (initial off len (older flag 1 w))).run (L0 environment,state text)
 match result.1 with
 | .error (.revert bs) =>
  match result.2.2.heap.get 3 with
  | some ⟨_,.bytes input⟩ => "{\"pointer\":3,\"cursor\":"++toString result.2.2.heap.next++",\"copied\":"++render input++",\"bytes\":"++render bs++"}"
  | _ => "{\"bad_heap\":true}"
 | _ => "{\"bad_run\":true}"
def observations (p : Roadmap.Pipeline) : List String :=
 [observe p [] 0 0 false [] ⟨0,by decide +kernel⟩,
  observe p [99,0,255,128,77] 1 3 true [195,169] ⟨300,by decide +kernel⟩,
  observe p ([171,0]++List.replicate 31 255++[7,8]) 2 31 false (List.replicate 32 0) ⟨2^256-1,by omega⟩,
  observe p [0,255,128] 1 33 true [] ⟨2^255,by decide +kernel⟩,
  observe p [1,2] 99 33 true (List.replicate 33 128) ⟨300,by decide +kernel⟩,
  observe p ([1]++List.replicate 33 128++[255]) 1 33 false (List.replicate 31 0) ⟨42,by decide +kernel⟩]
#eval IO.println ("CALLDATA_COPY_LEGACY=["++String.intercalate "," (observations .legacy)++"]")
#eval IO.println ("CALLDATA_COPY_VIAIR=["++String.intercalate "," (observations .viaIR)++"]")
#print axioms copy_run
#print axioms keep_reference
#print axioms arguments_run
#print axioms prefix_suffix
#print axioms copied_fields
#print axioms source_run
#print axioms member
#print axioms typed
#print axioms lookups
#print axioms fields
#print axioms actual_error
#print axioms copied_object
#print axioms old0
#print axioms old1
#print axioms timeout_before
#print axioms timeout_after
#print axioms dangling_after
#print axioms revert_cursor
#print axioms initial_state_wrong
end Solidity.Lowering.V08.LiteralFailureCalldataCopyControls
