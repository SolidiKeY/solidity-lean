import Solidity.Lowering.V08.LiteralFailureDynamicError

/-! Arbitrary-length typed local-reference custom-error encoding, consuming the
existing heap/codec. No alternate argument AST or machine is introduced. -/
namespace Solidity.Lowering.V08.LiteralFailureDynamicListError
open Solidity Source

def types {Γ : RCtx} (refs : List (Source.Idx Γ (.bytes .memory))) : List STy :=
 List.replicate refs.length (.bytes .memory)

def arguments {E : Env} {Γ : RCtx} :
 (refs : List (Source.Idx Γ (.bytes .memory))) → RConvArgs E Γ (types refs)
 | [] => .nil
 | index :: refs => .cons (.local index) rfl (arguments refs)

def values {E : Env} {Γ : RCtx} (locals : Locals E.layout Γ) :
 (refs : List (Source.Idx Γ (.bytes .memory))) → Vals E.layout (types refs)
 | [] => .nil
 | index :: refs => .cons (locals.get index) (values locals refs)

/-- Only actual intrinsic local/heap field equations, no evaluator result. -/
def represented {E : Env} {Γ : RCtx} (locals : Locals E.layout Γ) (state : St E)
 (index : Source.Idx Γ (.bytes .memory)) (bytes : Roadmap.Bytes) : Prop :=
 ∃ address, locals.get index = .memRef rfl address ∧
  (state.heap.get address = some ⟨.bytes .memory,.bytes bytes⟩ ∨
   state.heap.get address = some ⟨.string .memory,.string bytes⟩)

theorem arguments_run {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (extra : Nat)
 (refs : List (Source.Idx Γ (.bytes .memory))) (locals : Locals E.layout Γ) (state : St E) :
 (evalConvArgs G F (refs.length+extra+3) (arguments refs)).run (locals,state) =
 (.ok (values locals refs),(locals,state)) := by
 induction refs with
 | nil => rfl
 | cons index refs ih =>
   simp only [List.length_cons,arguments,values]
   rw [evalConvArgs]
   simp only [evalE,convRV,getV,RVal.get,EM.locals,EM.lift,
    bind,pure,Except.pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
    StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,liftM,
    monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map,↓reduceDIte]
   have fuel : refs.length+1+extra+2 = refs.length+extra+3 := by omega
   simp only [fuel,bind,pure,ExceptT.bindCont,StateT.bind,StateT.pure]
   have tail := ih
   simp only [ExceptT.run] at tail
   rw [tail]
   rfl

/-- Ordered local/heap representation only, including exact list lengths.
This is not a decoder, evaluator or source admission predicate. -/
def all_represented {E : Env} {Γ : RCtx} (caller : Locals E.layout Γ) (state : St E) :
 List (Source.Idx Γ (.bytes .memory)) → List Roadmap.Bytes → Prop
 | [], [] => True
 | index :: refs, bytes :: packets => represented caller state index bytes ∧
   all_represented caller state refs packets
 | _, _ => False

theorem represented_length {E : Env} {Γ : RCtx}
 (refs : List (Source.Idx Γ (.bytes .memory))) (packets : List Roadmap.Bytes)
 (caller : Locals E.layout Γ) (state : St E)
 (memory : all_represented caller state refs packets) : refs.length = packets.length := by
 induction refs generalizing packets with
 | nil => cases packets with
   | nil => rfl
   | cons _ _ => cases memory
 | cons index refs ih => cases packets with
   | nil => cases memory
   | cons bytes packets => exact congrArg Nat.succ (ih packets memory.2)

theorem repeat_represented {E : Env} {Γ : RCtx}
 (caller : Locals E.layout Γ) (state : St E) (index : Source.Idx Γ (.bytes .memory))
 (bytes : Roadmap.Bytes) (single : represented caller state index bytes) (count : Nat) :
 all_represented caller state (List.replicate count index) (List.replicate count bytes) := by
 induction count with
 | zero => trivial
 | succ count ih => exact ⟨single,ih⟩

theorem part_run {E : Env} {Γ Δ : RCtx} (F : Fr) (fuel : Nat)
 (index : Source.Idx Γ (.bytes .memory)) (bytes : Roadmap.Bytes)
 (caller : Locals E.layout Γ) (locals : Locals E.layout Δ) (state : St E)
 (memory : represented caller state index bytes) :
 (encodeOne F fuel false (.val (caller.get index)) : EM E Δ _).run (locals,state) =
 (.ok (true,bytes),(locals,state)) := by
 obtain ⟨address,reference,heap⟩ := memory
 rw [reference]
 rcases heap with heap | heap <;>
  simp only [encodeOne,bytesOfRV,heapBytes,heapObj,EM.st,bind,pure,
   ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
   StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,liftM,
   monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map,heap]

theorem parts_run {E : Env} {Γ Δ : RCtx} (F : Fr) (fuel : Nat)
 (refs : List (Source.Idx Γ (.bytes .memory))) (packets : List Roadmap.Bytes)
 (caller : Locals E.layout Γ) (locals : Locals E.layout Δ) (state : St E)
 (memory : all_represented caller state refs packets) :
 (encodeParts F fuel false (values caller refs).toR : EM E Δ _).run (locals,state) =
 (.ok (packets.map (fun bytes => (true,bytes))),(locals,state)) := by
 induction refs generalizing packets with
 | nil =>
   cases packets with
   | nil => rfl
   | cons bytes packets => cases memory
 | cons index refs ih =>
   cases packets with
   | nil => cases memory
   | cons bytes packets =>
     obtain ⟨head,tail⟩ := memory
     simp only [values,Vals.toR,encodeParts,List.map_cons]
     have step := part_run F fuel index bytes caller locals state head
     have rest := ih packets tail
     simp only [ExceptT.run] at step rest
     simp only [bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
      StateT.bind,StateT.pure]
     rw [step]
     simp only [StateT.bind,ExceptT.bindCont,StateT.pure]
     rw [rest]
     rfl

theorem encoding_run {E : Env} {Γ Δ : RCtx} (F : Fr) (fuel : Nat)
 (refs : List (Source.Idx Γ (.bytes .memory))) (packets : List Roadmap.Bytes)
 (caller : Locals E.layout Γ) (locals : Locals E.layout Δ) (state : St E)
 (memory : all_represented caller state refs packets) :
 (encodeVals F fuel false (values caller refs).toR : EM E Δ _).run (locals,state) =
 (.ok (abiLayout (packets.map (fun bytes => (true,bytes)))),(locals,state)) := by
 have actual := parts_run F fuel refs packets caller locals state memory
 simp only [ExceptT.run] at actual
 simp only [encodeVals,bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,
  ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,actual,Bool.false_eq_true,↓reduceIte]

def statement {E : Env} {Γ : RCtx} (error : Decl)
 (refs : List (Source.Idx Γ (.bytes .memory)))
 (typed : error.paramTys E = some (types refs)) : RStmt E [] false .body Γ Γ :=
 .revertError error typed (arguments refs)

theorem source_run {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (extra : Nat)
 (error : Decl) (refs : List (Source.Idx Γ (.bytes .memory)))
 (typed : error.paramTys E = some (types refs)) (packets : List Roadmap.Bytes)
 (locals : Locals E.layout Γ) (state : St E)
 (memory : all_represented locals state refs packets) :
 (execS G F (refs.length+extra+4) 0 none (statement error refs typed) locals).run (Source.L0 E,state) =
 (.error (.revert (G.selector (sigOf E.layout error.name (types refs)) ++
  abiLayout (packets.map (fun bytes => (true,bytes))))),(Source.L0 E,state)) :=
 SourceCustomErrors.execute G F (refs.length+extra+3) error typed (arguments refs)
  locals locals state state state (values locals refs) _
  (arguments_run G F extra refs locals state)
  (encoding_run F (refs.length+extra+3) refs packets locals (Source.L0 E) state memory)

def abiValues : (packets : List Roadmap.Bytes) → AbiEntry.Vals (List.replicate packets.length .bytes)
 | [] => .nil
 | bytes :: packets => .cons (.bytes bytes) (abiValues packets)

theorem word_transport (number : Nat) :
 wordBytes (toWord number) = AbiEntry.wordBytes number := by
 rw [natWordBytes_transport]
 unfold Semantics.wordBytes AbiEntry.wordBytes
 apply List.map_congr_left
 intro index member
 exact UInt8.ofNat_mod_size

theorem tail_agreement (bytes : Roadmap.Bytes) :
 wordBytes (toWord bytes.length) ++ Source.pad32 bytes =
 AbiEntry.Val.enc (AbiEntry.Val.bytes bytes) := by
 have padding : AbiEntry.roundUp bytes.length - bytes.length = (32-bytes.length%32)%32 := by
  unfold AbiEntry.roundUp
  omega
 rw [word_transport]
 simp only [AbiEntry.Val.enc,Source.pad32,padding,List.append_assoc]

theorem tail_extent (bytes : Roadmap.Bytes) :
 (AbiEntry.Val.enc (AbiEntry.Val.bytes bytes)).length = 32 + AbiEntry.roundUp bytes.length := by
 simp only [AbiEntry.Val.enc,AbiEntry.wordBytes,List.length_append,List.length_map,
  List.length_range,List.length_replicate]
 unfold AbiEntry.roundUp
 omega

theorem source_tail_extent (bytes : Roadmap.Bytes) :
 (wordBytes (toWord bytes.length) ++ Source.pad32 bytes).length =
 32 + AbiEntry.roundUp bytes.length := by
 rw [tail_agreement]
 exact tail_extent bytes

theorem go_agreement (packets : List Roadmap.Bytes) (offset : Nat) :
 Source.abiLayout.go (packets.map (fun bytes => (true,bytes))) offset =
 AbiEntry.assemble.go (AbiEntry.Vals.parts (abiValues packets)) offset := by
 induction packets generalizing offset with
 | nil => rfl
 | cons bytes packets ih =>
   simp only [List.map_cons,Source.abiLayout.go,abiValues,AbiEntry.Vals.parts,
    AbiEntry.Shape.dynamic,AbiEntry.assemble.go,↓reduceIte]
   simp only [tail_agreement,ih,word_transport]
   have tail := tail_agreement bytes
   rw [word_transport] at tail
   rw [tail]

theorem heads_acc (packets : List Roadmap.Bytes) (offset : Nat) :
 (AbiEntry.Vals.parts (abiValues packets)).foldl
  (fun acc part => acc + if part.1 then 32 else part.2.length) offset =
 offset + 32 * packets.length := by
 induction packets generalizing offset with
 | nil => rfl
 | cons bytes packets ih =>
   simp only [abiValues,AbiEntry.Vals.parts,AbiEntry.Shape.dynamic,List.foldl_cons,
    ↓reduceIte,ih,List.length_cons]
   omega

theorem abi_agreement (packets : List Roadmap.Bytes) :
 abiLayout (packets.map (fun bytes => (true,bytes))) = AbiEntry.encodeArgs (abiValues packets) := by
 simp only [abiLayout,List.length_map,AbiEntry.encodeArgs,AbiEntry.assemble,
  heads_acc,Nat.zero_add,go_agreement]

theorem source_typed {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (extra : Nat)
 (error : Decl) (refs : List (Source.Idx Γ (.bytes .memory)))
 (typed : error.paramTys E = some (types refs)) (packets : List Roadmap.Bytes)
 (locals : Locals E.layout Γ) (state : St E)
 (memory : all_represented locals state refs packets) :
 (execS G F (refs.length+extra+4) 0 none (statement error refs typed) locals).run (Source.L0 E,state) =
 (.error (.revert (G.selector (sigOf E.layout error.name (types refs)) ++
  AbiEntry.encodeArgs (abiValues packets))),(Source.L0 E,state)) := by
 simpa only [abi_agreement] using source_run G F extra error refs typed packets locals state memory

end Solidity.Lowering.V08.LiteralFailureDynamicListError
