import Solidity.Lowering.V08.LiteralFailureDynamicListError

namespace Solidity.Lowering.V08.LiteralFailurePackedBytes
open Solidity Source LiteralFailureDynamicListError

/-- The actual packed encoder retains byte boundaries only through concatenation. -/
theorem packed_parts (packets : List Roadmap.Bytes) :
 (packets.map (fun bytes => (true,bytes))).foldr (fun p acc => p.2 ++ acc) [] =
 packets.flatten := by
 induction packets with
 | nil => rfl
 | cons bytes packets ih =>
   simp only [List.map_cons,List.foldr_cons,List.flatten_cons,ih]

theorem part_run {E : Env} {Γ Δ : RCtx} (F : Fr) (fuel : Nat)
 (index : Source.Idx Γ (.bytes .memory)) (bytes : Roadmap.Bytes)
 (caller : Locals E.layout Γ) (locals : Locals E.layout Δ) (state : St E)
 (memory : represented caller state index bytes) :
 (encodeOne F fuel true (.val (caller.get index)) : EM E Δ _).run (locals,state) =
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
 (encodeParts F fuel true (values caller refs).toR : EM E Δ _).run (locals,state) =
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


/-- Actual heap reads, not an assumed encoder result. Both contexts are retained. -/
theorem encoding_run {E : Env} {Γ Δ : RCtx} (F : Fr) (fuel : Nat)
 (refs : List (Source.Idx Γ (.bytes .memory))) (packets : List Roadmap.Bytes)
 (caller : Locals E.layout Γ) (locals : Locals E.layout Δ) (state : St E)
 (memory : all_represented caller state refs packets) :
 (encodeVals F fuel true (values caller refs).toR : EM E Δ _).run (locals,state) =
 (.ok packets.flatten,(locals,state)) := by
 have actual := parts_run F fuel refs packets caller locals state memory
 simp only [ExceptT.run] at actual
 simp only [encodeVals,bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,
  ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,actual,↓reduceIte,packed_parts]

def args {E : Env} {Γ : RCtx} :
 (refs : List (Source.Idx Γ (.bytes .memory))) → RArgs E Γ (types refs)
 | [] => .nil
 | index :: refs => .cons (.local index) (args refs)

theorem args_run {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (extra : Nat)
 (refs : List (Source.Idx Γ (.bytes .memory))) (locals : Locals E.layout Γ) (state : St E) :
 (evalArgs G F (refs.length+extra+3) (args refs)).run (locals,state) =
 (.ok (values locals refs).toR,(locals,state)) := by
 induction refs with
 | nil => rfl
 | cons index refs ih =>
   simp only [List.length_cons,args,values,Vals.toR]
   rw [evalArgs]
   simp only [evalE,EM.locals,EM.lift,bind,pure,Except.pure,
    ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
    StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,liftM,
    monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map]
   have fuel : refs.length+1+extra+2 = refs.length+extra+3 := by omega
   simp only [fuel,bind,pure,ExceptT.bindCont,StateT.bind,StateT.pure]
   have tail := ih
   simp only [ExceptT.run] at tail
   rw [tail]
   rfl

theorem expression_run {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (extra : Nat)
 (refs : List (Source.Idx Γ (.bytes .memory))) (packets : List Roadmap.Bytes)
 (locals : Locals E.layout Γ) (state : St E)
 (memory : all_represented locals state refs packets) :
 (evalE G F (refs.length+extra+4) (.abiEncode .encodePacked (args refs))).run (locals,state) =
 (.ok (.val (.memRef rfl state.heap.next)),
  (locals,{state with heap := (state.heap.alloc ⟨.bytes .memory,.bytes packets.flatten⟩).1})) := by
 have arguments := args_run G F extra refs locals state
 have encoded := encoding_run F (refs.length+extra+3) refs packets locals locals state memory
 simp only [ExceptT.run] at arguments encoded
 rw [evalE]
 simp only [bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
  StateT.bind,StateT.pure,arguments]
 rw [encoded]
 rfl

end Solidity.Lowering.V08.LiteralFailurePackedBytes
