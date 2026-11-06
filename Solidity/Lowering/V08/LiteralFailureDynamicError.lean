import Solidity.Lowering.V08.SourceCustomErrors
import Solidity.Lowering.V08.SourceEnvironment
import Solidity.Lowering.V08.SourceAbi
import Solidity.Semantics.AbiEntry

/-! Actual heap-backed Source custom-error encoding. No runtime target encoder
or independent source/target simulation is introduced. -/
namespace Solidity.Lowering.V08.LiteralFailureDynamicError
open Solidity Source

def types : List STy := [.bytes .memory,.int IntTy.u256]
def context (Γ : RCtx) : RCtx := .bytes .memory :: .int IntTy.u256 :: Γ

def arguments {E : Env} {Γ : RCtx} : RConvArgs E (context Γ) types :=
 .cons (.local .here) rfl (.cons (.local (.there .here)) rfl .nil)

def caller {E : Env} {Γ : RCtx} (address : Nat) (marker : Roadmap.Word)
 (older : Locals E.layout Γ) : Locals E.layout (context Γ) :=
 .cons (.memRef rfl address) (.cons (SourceEnvironment.sourceWord marker) older)

def values {E : Env} (address : Nat) (marker : Roadmap.Word) : Vals E.layout types :=
 .cons (.memRef rfl address) (.cons (SourceEnvironment.sourceWord marker) .nil)

theorem arguments_run {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 (address : Nat) (marker : Roadmap.Word) (older : Locals E.layout Γ) (state : St E) :
 (evalConvArgs G F (n+5) (arguments (E:=E) (Γ:=Γ))).run (caller address marker older,state) =
 (.ok (values address marker),(caller address marker older,state)) := by
 rfl

theorem marker_word {D : Source.Layout} (marker : Roadmap.Word) :
 (SourceEnvironment.sourceWord (D:=D) marker).word = some marker := by
 have modular : (marker.val : Int) % (2^256 : Nat) = (marker.val : Int) :=
  Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr marker.isLt)
 simp only [SourceEnvironment.sourceWord,Val.word,intWord,modular,Int.toNat_natCast]
 congr 1
 apply Fin.ext
 exact Nat.mod_eq_of_lt marker.isLt

/-- Intrinsic heap contents, not an assumed encoder result. Both existing
bytes/string memory object shapes are accepted by heapBytes. -/
theorem encoding_run {E : Env} {Γ : RCtx} (F : Fr) (fuel : Nat)
 (address : Nat) (marker : Roadmap.Word) (bytes : Roadmap.Bytes)
 (locals : Locals E.layout Γ) (state : St E)
 (heap : state.heap.get address = some ⟨.bytes .memory,.bytes bytes⟩ ∨
  state.heap.get address = some ⟨.string .memory,.string bytes⟩) :
 (encodeVals F fuel false (values (E:=E) address marker).toR : EM E Γ _).run (locals,state) =
 (.ok (abiLayout [(true,bytes),(false,wordBytes marker)]),(locals,state)) := by
 rcases heap with heap | heap <;>
  simp only [values,Vals.toR,encodeVals,encodeParts,encodeOne,marker_word,
   bytesOfRV,heapBytes,heapObj,EM.st,bind,pure,ExceptT.bind,ExceptT.pure,
   ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,StateT.get,
   get,getThe,MonadStateOf.get,liftM,monadLift,MonadLift.monadLift,ExceptT.lift,
   Functor.map,StateT.map,heap,Bool.false_eq_true,↓reduceIte]

def statement {E : Env} {Γ : RCtx} (error : Decl)
 (typed : error.paramTys E = some types) : RStmt E [] false .body (context Γ) (context Γ) :=
 .revertError error typed arguments

theorem source_run {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 (error : Decl) (typed : error.paramTys E = some types)
 (address : Nat) (marker : Roadmap.Word) (bytes : Roadmap.Bytes)
 (older : Locals E.layout Γ) (state : St E)
 (heap : state.heap.get address = some ⟨.bytes .memory,.bytes bytes⟩ ∨
  state.heap.get address = some ⟨.string .memory,.string bytes⟩) :
 (execS G F (n+6) 0 none (statement (Γ:=Γ) error typed)
  (caller address marker older)).run (Source.L0 E,state) =
 (.error (.revert (G.selector (sigOf E.layout error.name types) ++
  abiLayout [(true,bytes),(false,wordBytes marker)])),(Source.L0 E,state)) :=
 SourceCustomErrors.execute G F (n+5) error typed arguments
  (caller address marker older) (caller address marker older) state state state
  (values address marker) _ (arguments_run G F n address marker older state)
  (encoding_run F (n+5) address marker bytes (Source.L0 E) state heap)

theorem layout (bytes : Roadmap.Bytes) (marker : Roadmap.Word) :
 abiLayout [(true,bytes),(false,wordBytes marker)] =
 Semantics.wordBytes 64 ++ Semantics.wordBytes marker.val ++
  (Semantics.wordBytes bytes.length ++ Semantics.pad32 bytes) := by
 simp only [abiLayout,abiLayout.go,List.length_cons,List.length_nil,
  List.append_nil,List.append_assoc]
 rw [natWordBytes_transport,natWordBytes_transport,wordBytes_transport,pad32_transport]

def abiWord (marker : Roadmap.Word) : AbiEntry.Word (.uint 256) :=
 ⟨marker.val,by simpa only [AbiEntry.W_eq] using marker.isLt,
  by simpa only [AbiEntry.Kind.valid,decide_eq_true_eq] using marker.isLt⟩

def abiValues (bytes : Roadmap.Bytes) (marker : Roadmap.Word) :
 AbiEntry.Vals [.bytes,.word (.uint 256)] :=
 .cons (.bytes bytes) (.cons (.word (abiWord marker)) .nil)

/-- Complete byte identity with the existing independent typed codec; natural
length metadata still has the original modulo-word behavior. -/
theorem abi_agreement (bytes : Roadmap.Bytes) (marker : Roadmap.Word) :
 abiLayout [(true,bytes),(false,wordBytes marker)] =
 AbiEntry.encodeArgs (abiValues bytes marker) := by
 have padding : AbiEntry.roundUp bytes.length - bytes.length = (32-bytes.length%32)%32 := by
  unfold AbiEntry.roundUp
  omega
 have byte_mod (number : Nat) : UInt8.ofNat (number % 256) = UInt8.ofNat number :=
  UInt8.ofNat_mod_size
 rw [layout]
 simp only [abiValues,abiWord,AbiEntry.encodeArgs,AbiEntry.Vals.parts,
  AbiEntry.Shape.dynamic,AbiEntry.Val.enc,AbiEntry.assemble,List.foldl_cons,
  List.foldl_nil,List.length_map,List.length_range,Bool.false_eq_true,↓reduceIte,Nat.zero_add,
  AbiEntry.assemble.go,List.append_nil,List.append_assoc,padding,
  AbiEntry.wordBytes,Semantics.wordBytes,Semantics.pad32,Nat.toUInt8,byte_mod,List.length_map,List.length_range]

theorem source_typed {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 (error : Decl) (typed : error.paramTys E = some types)
 (address : Nat) (marker : Roadmap.Word) (bytes : Roadmap.Bytes)
 (older : Locals E.layout Γ) (state : St E)
 (heap : state.heap.get address = some ⟨.bytes .memory,.bytes bytes⟩ ∨
  state.heap.get address = some ⟨.string .memory,.string bytes⟩) :
 (execS G F (n+6) 0 none (statement (Γ:=Γ) error typed)
  (caller address marker older)).run (Source.L0 E,state) =
 (.error (.revert (G.selector (sigOf E.layout error.name types) ++
  AbiEntry.encodeArgs (abiValues bytes marker))),(Source.L0 E,state)) := by
 simpa only [abi_agreement] using source_run G F n error typed address marker bytes older state heap

end Solidity.Lowering.V08.LiteralFailureDynamicError
