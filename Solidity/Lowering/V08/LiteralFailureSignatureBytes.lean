import Solidity.Lowering.V08.LiteralFailurePackedBytes

namespace Solidity.Lowering.V08.LiteralFailureSignatureBytes
open Solidity Source LiteralFailureDynamicListError

theorem signature_read {E : Env} {Γ Δ : RCtx} (F : Fr) (fuel : Nat)
 (index : Source.Idx Γ (.bytes .memory)) (bytes : Roadmap.Bytes)
 (caller : Locals E.layout Γ) (locals : Locals E.layout Δ) (state : St E)
 (memory : represented caller state index bytes) :
 (bytesOfRV F fuel (.val (caller.get index)) : EM E Δ _).run (locals,state) =
 (.ok bytes,(locals,state)) := by
 obtain ⟨address,reference,heap⟩ := memory
 rw [reference]
 rcases heap with heap | heap <;>
  simp only [bytesOfRV,heapBytes,heapObj,EM.st,bind,pure,
   ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
   StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,liftM,
   monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map,heap]

theorem expression_run {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (extra : Nat)
 (signature : Source.Idx Γ (.bytes .memory))
 (refs : List (Source.Idx Γ (.bytes .memory))) (text : Roadmap.Bytes)
 (packets : List Roadmap.Bytes) (locals : Locals E.layout Γ) (state : St E)
 (sigMemory : represented locals state signature text)
 (memory : all_represented locals state refs packets) :
 (evalE G F (refs.length+extra+5)
  (.abiEncode .encodeWithSignature (LiteralFailurePackedBytes.args (signature::refs)))).run (locals,state) =
 (.ok (.val (.memRef rfl state.heap.next)),(locals,
  SourceKeccak.afterLiteral state
   ((wordBytes (G.fixed.hash text)).take 4 ++ AbiEntry.encodeArgs (abiValues packets)))) := by
 have horizon : (signature::refs).length+extra+3 = refs.length+extra+4 := by
  simp only [List.length_cons]
  omega
 have arguments := LiteralFailurePackedBytes.args_run G F extra (signature::refs) locals state
 simp only [horizon,values,Vals.toR] at arguments
 have reading := signature_read F (refs.length+extra+4) signature text locals locals state sigMemory
 have encoded := LiteralFailureDynamicListError.encoding_run F (refs.length+extra+4)
  refs packets locals locals state memory
 have execution := SourceAbi.signature_execute G F (refs.length+extra+4)
  (LiteralFailurePackedBytes.args (signature::refs)) locals locals locals locals
  state state state state (.val (locals.get signature)) (values locals refs).toR
  text (abiLayout (packets.map (fun bytes => (true,bytes)))) arguments reading encoded
 simpa only [abi_agreement,Nat.add_assoc] using execution

theorem object_preserved {E : Env} (state : St E) (output : Roadmap.Bytes)
 (address : Nat) (object : Σ τ, Source.Data E.layout τ)
 (present : state.heap.get address = some object) :
 (SourceKeccak.afterLiteral state output).heap.get address = some object := by
 have distinct : address ≠ state.heap.next := by
  intro same
  have empty := state.heap.bounded address (by omega)
  change state.heap.get address = none at empty
  rw [present] at empty
  contradiction
 exact (state.heap.alloc_other ⟨.bytes .memory,.bytes output⟩ distinct).trans present

theorem reference_preserved {E : Env} {Γ : RCtx} (locals : Locals E.layout Γ)
 (state : St E) (output : Roadmap.Bytes) (index : Source.Idx Γ (.bytes .memory))
 (bytes : Roadmap.Bytes) (memory : represented locals state index bytes) :
 represented locals (SourceKeccak.afterLiteral state output) index bytes := by
 obtain ⟨address,reference,heap⟩ := memory
 refine ⟨address,reference,?_⟩
 rcases heap with heap | heap
 · exact .inl (object_preserved state output address _ heap)
 · exact .inr (object_preserved state output address _ heap)

end Solidity.Lowering.V08.LiteralFailureSignatureBytes
