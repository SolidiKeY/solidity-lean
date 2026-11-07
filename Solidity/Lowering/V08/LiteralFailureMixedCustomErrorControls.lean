import Solidity.Lowering.V08.LiteralFailureMixedCustomError
import Solidity.Lowering.V08.SourceCustomErrorControls
namespace Solidity.Lowering.V08.LiteralFailureMixedCustomErrorControls
open Solidity Source
open LiteralFailureMixedCustomError

def types : RCtx := [.bytes .memory,.int IntTy.u256,.bytes .memory,.int IntTy.u256]
def declaration : Decl := ⟨.error,"Mixed4",some "C",false,.error "Mixed4"
 (.cons (.errorParam (.elem .bytes) none)
  (.cons (.errorParam (.elem (.int false 256 (by decide +kernel))) none)
   (.cons (.errorParam (.elem .bytes) none)
    (.cons (.errorParam (.elem (.int false 256 (by decide +kernel))) none) .nil))))⟩
def emptyDeclaration : Decl := ⟨.error,"Empty",some "C",false,.error "Empty" .nil⟩
def environment : Env := ⟨[SourceCustomErrorControls.savedDecl,SourceCustomErrorControls.scratchDecl,declaration,emptyDeclaration]⟩
theorem member : declaration ∈ environment.decls := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
theorem typed : declaration.paramTys environment=some types := rfl
theorem empty_member : emptyDeclaration ∈ environment.decls := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

def frame := SourceCustomErrorControls.frame
def empty : St environment :=
 ⟨⟨⟨fun _=>Account.empty _⟩,Transient.empty,[]⟩,Source.Heap.empty,[],[],⟨[],.nil⟩,Source.FailureExecution.Cursor.empty⟩
def state (first second : Roadmap.Bytes) : St environment :=
 {empty with
  heap:=(((Source.Heap.empty.alloc ⟨.bytes .memory,.bytes [9,7]⟩).1.alloc ⟨.bytes .memory,.bytes first⟩).1.alloc ⟨.bytes .memory,.bytes second⟩).1
  ex:=empty.ex.run [.account frame.this (fun account=>{account with balance:=73,nonce:=4,storage:=account.storage.write SourceCustomErrorControls.saved (.bool true)}),
   .transient frame.this (fun transient=>transient.write SourceCustomErrorControls.scratch (.bool true))]
  events:=[.call frame.this ⟨7,by decide +kernel⟩ [0,255] false]
  logs:=[(frame.this,[171,0,255])]
  fnLocals:=⟨[.bool],.cons (.bool true) .nil⟩}
def context : RCtx := types++[.bytes .memory,.bool]
def locals (firstAddress : Nat) (a b : Roadmap.Word) : Locals environment.layout context :=
 .cons (.memRef rfl firstAddress) (.cons (SourceEnvironment.sourceWord a)
  (.cons (.memRef rfl 2) (.cons (SourceEnvironment.sourceWord b)
   (.cons (.memRef rfl 0) (.cons (.bool true) .nil)))))
def values (a b : Roadmap.Word) : Source.Vals environment.layout types :=
 .cons (.memRef rfl 1) (.cons (SourceEnvironment.sourceWord a)
  (.cons (.memRef rfl 2) (.cons (SourceEnvironment.sourceWord b) .nil)))
def arguments : RConvArgs environment context types :=
 .cons (.local .here) rfl (.cons (.local (.there .here)) rfl
  (.cons (.local (.there (.there .here))) rfl (.cons (.local (.there (.there (.there .here)))) rfl .nil)))
def program : Program environment :=
 {body:=fun _=>none,consts:=fun _=>none,inits:=fun _=>[],ctor:=fun _=>none,
  ctorLocals:=fun _=>[],baseArgs:=fun _=>[],contracts:=["C"]}
def global (p : Roadmap.Pipeline) : Glob environment :=
 {prog:=program,pipeline:=p,fixed:=Roadmap.Controls.toyFixed,balance0:=fun _=>⟨100,by decide +kernel⟩,
  hasCode:=fun _ _=>false,callee:=fun _=>.answer (.success []),timestamp:=⟨12345,by decide +kernel⟩}
def encoded (first second : Roadmap.Bytes) (a b : Roadmap.Word) : AbiEntry.Vals [.bytes,.word (.uint 256),.bytes,.word (.uint 256)] :=
 .cons (.bytes first) (.cons (.word (LiteralFailureDynamicError.abiWord a))
  (.cons (.bytes second) (.cons (.word (LiteralFailureDynamicError.abiWord b)) .nil)))
theorem lookups (a b : Roadmap.Word) : LocalArgs (locals 1 a b) arguments (values a b) :=
 .cons .here rfl (.cons (.there .here) rfl (.cons (.there (.there .here)) rfl
  (.cons (.there (.there (.there .here))) rfl .nil)))
theorem fields (first second : Roadmap.Bytes) (a b : Roadmap.Word) :
 LiteralFailureMixedEncoding.Represented (state first second) (values a b) (encoded first second a b)
 [(true,first),(false,wordBytes a),(true,second),(false,wordBytes b)] :=
 .bytes 1 first (.inl rfl) (.uint a (.bytes 2 second (.inl rfl) (.uint b .nil)))
def packet (p : Roadmap.Pipeline) (first second : Roadmap.Bytes) (a b : Roadmap.Word) : Roadmap.Bytes :=
 (global p).selector (sigOf environment.layout declaration.name types)++AbiEntry.encodeArgs (encoded first second a b)
def statement : RStmt environment [] false .body context context := .revertError declaration typed arguments

theorem actual_error (p : Roadmap.Pipeline) (static : Bool) (first second : Roadmap.Bytes) (a b : Roadmap.Word) :
 (execS (global p) {frame with static:=static} 8 0 none statement (locals 1 a b)).run (L0 environment,state first second)=
 (.error (.revert (packet p first second a b)),(L0 environment,state first second)) :=
 source_run (global p) {frame with static:=static} 0 declaration typed _ _ (lookups a b) (fields first second a b)

theorem empty_error (p : Roadmap.Pipeline) (first second : Roadmap.Bytes) (a b : Roadmap.Word) :
 (execS (global p) frame 4 0 none
  (.revertError emptyDeclaration rfl .nil : RStmt environment [] false .body context context) (locals 1 a b)).run
 (L0 environment,state first second)=
 (.error (.revert ((global p).selector (sigOf environment.layout emptyDeclaration.name []))),
  (L0 environment,state first second)) := by
 have result := source_run (global p) frame 0 emptyDeclaration rfl (locals 1 a b) (state first second)
  LocalArgs.nil LiteralFailureMixedEncoding.Represented.nil
 simpa only [AbiEntry.encodeArgs,AbiEntry.Vals.parts,AbiEntry.assemble,AbiEntry.assemble.go,
  List.foldl_nil,List.append_nil] using result

theorem initial_snapshot (first second : Roadmap.Bytes) :
 (state first second).heap.next=3 ∧ (state first second).heap.get 0=some ⟨.bytes .memory,.bytes [9,7]⟩ ∧
 ((state first second).ex.world.accounts frame.this).nonce=4 ∧
 ((state first second).ex.world.accounts frame.this).storage.read SourceCustomErrorControls.saved=some (.bool true) ∧
 ((state first second).ex.transient.cells frame.this).read SourceCustomErrorControls.scratch=some (.bool true) :=
 ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem corrupt_reference (p : Roadmap.Pipeline) (first second : Roadmap.Bytes) (a b : Roadmap.Word) :
 (execS (global p) frame 8 0 none statement (locals 99 a b)).run (L0 environment,state first second)=
 (.error (.stuck "dangling memory reference"),(L0 environment,state first second)) := by rfl

theorem insufficient_fuel (first second : Roadmap.Bytes) (a b : Roadmap.Word) :
 (execS (global .legacy) frame 1 0 none statement (locals 1 a b)).run (L0 environment,state first second)=
 (.error .timeout,(L0 environment,state first second)) := by rfl

theorem signature_utf8 : "Mixed4(bytes,uint256,bytes,uint256)".toUTF8.toList=[77,105,120,101,100,52,40,98,121,116,101,115,44,117,105,110,116,50,53,54,44,98,121,116,101,115,44,117,105,110,116,50,53,54,41] := by
 change ((⟨#[77,105,120,101,100,52,40,98,121,116,101,115,44,117,105,110,116,50,53,54,44,98,121,116,101,115,44,117,105,110,116,50,53,54,41]⟩ : ByteArray).toList)=_
 have size : (⟨#[77,105,120,101,100,52,40,98,121,116,101,115,44,117,105,110,116,50,53,54,44,98,121,116,101,115,44,117,105,110,116,50,53,54,41]⟩ : ByteArray).size=35 := rfl
 unfold ByteArray.toList
 repeat' (rw [ByteArray.toList.loop]; simp only [size,Nat.reduceLT,Nat.reduceAdd,if_true,if_false])
 rfl

theorem signature_bytes : asciiBytes (sigOf environment.layout declaration.name types)="Mixed4(bytes,uint256,bytes,uint256)".toUTF8.toList := by
 rw [signature_utf8]
 rfl

theorem selector_transport (p : Roadmap.Pipeline) :
 (global p).selector (sigOf environment.layout declaration.name types)=
 Semantics.selectorBytes (Semantics.customSelector "Mixed4(bytes,uint256,bytes,uint256)") :=
 SourceCustomErrors.selector_of_bytes (global p) Roadmap.Controls.toyFixed_keccak _ "Mixed4(bytes,uint256,bytes,uint256)" signature_bytes

def render (bs : Roadmap.Bytes) := "["++String.intercalate "," (bs.map (fun b=>toString b.toNat))++"]"
def observe (p : Roadmap.Pipeline) (first second : Roadmap.Bytes) (a b : Roadmap.Word) : String :=
 let result := (execS (global p) frame 8 0 none statement (locals 1 a b)).run (L0 environment,state first second)
 match result.1 with
 | .error (.revert bs) => "{\"cursor\":"++toString result.2.2.heap.next++",\"bytes\":"++render bs++"}"
 | _ => "{\"bad_run\":true}"
def observeEmpty (p : Roadmap.Pipeline) : String :=
 let result := (execS (global p) frame 4 0 none
  (.revertError emptyDeclaration rfl .nil : RStmt environment [] false .body context context)
  (locals 1 ⟨42,by decide +kernel⟩ ⟨300,by decide +kernel⟩)).run (L0 environment,state [] [])
 match result.1 with
 | .error (.revert bs) => "{\"cursor\":"++toString result.2.2.heap.next++",\"bytes\":"++render bs++"}"
 | _ => "{\"bad_run\":true}"
def observations (p : Roadmap.Pipeline) : List String :=
 [observe p [] [] ⟨0,by decide +kernel⟩ ⟨2^256-1,by omega⟩,
  observe p [0,255] [128] ⟨42,by decide +kernel⟩ ⟨300,by decide +kernel⟩,
  observe p (List.replicate 31 255) (List.replicate 32 0) ⟨300,by decide +kernel⟩ ⟨42,by decide +kernel⟩,
  observe p (List.replicate 33 128) [] ⟨2^255,by decide +kernel⟩ ⟨300,by decide +kernel⟩,
  observe p (List.replicate 33 128) (List.replicate 33 128) ⟨2^256-1,by omega⟩ ⟨2^255,by decide +kernel⟩,
  observeEmpty p]
#eval IO.println ("MIXED_CUSTOM_LEGACY=["++String.intercalate "," (observations .legacy)++"]")
#eval IO.println ("MIXED_CUSTOM_VIAIR=["++String.intercalate "," (observations .viaIR)++"]")
#print axioms arguments_run
#print axioms source_run
#print axioms member
#print axioms typed
#print axioms empty_member
#print axioms lookups
#print axioms fields
#print axioms actual_error
#print axioms empty_error
#print axioms initial_snapshot
#print axioms corrupt_reference
#print axioms insufficient_fuel
#print axioms signature_utf8
#print axioms signature_bytes
#print axioms selector_transport
end Solidity.Lowering.V08.LiteralFailureMixedCustomErrorControls
