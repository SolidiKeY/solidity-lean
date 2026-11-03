import Solidity.Lowering.V08.LiteralFailureSignatureBytes

namespace Solidity.Lowering.V08.LiteralFailureSelectorBytes
open Solidity Source LiteralFailureDynamicListError

abbrev Selector := STy.fixedBytes 4 (by decide +kernel)

def args {E : Env} {Γ : RCtx} (selector : Source.Idx Γ Selector)
 (refs : List (Source.Idx Γ (.bytes .memory))) : RArgs E Γ (Selector :: types refs) :=
 .cons (.local selector) (LiteralFailurePackedBytes.args refs)

theorem arguments_run {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (extra : Nat)
 (selector : Source.Idx Γ Selector) (refs : List (Source.Idx Γ (.bytes .memory)))
 (locals : Locals E.layout Γ) (state : St E) :
 (evalArgs G F (refs.length+extra+4) (args selector refs)).run (locals,state) =
 (.ok (.cons (.val (locals.get selector)) (values locals refs).toR),(locals,state)) := by
 simp only [args]
 rw [evalArgs]
 simp only [evalE,EM.locals,EM.lift,bind,pure,Except.pure,
  ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
  StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,liftM,
  monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map]
 have tail := LiteralFailurePackedBytes.args_run G F extra refs locals state
 simp only [ExceptT.run] at tail
 rw [tail]
 rfl

theorem selector_extent {D : Layout} (value : Source.Val D Selector) : value.bytesOf.length = 4 := by
 cases value with
 | fixedBytes bytes extent => exact extent
 | memRef impossible _ => cases impossible
 | storRef impossible _ => cases impossible
 | cdRef impossible _ _ => cases impossible

theorem conversion_run {E : Env} {Γ : RCtx} (F : Fr) (fuel : Nat)
 (value : Source.Val E.layout Selector) (locals : Locals E.layout Γ) (state : St E) :
 (convRV F fuel Selector (.val value) : EM E Γ _).run (locals,state) =
 (.ok (.val value),(locals,state)) := by rfl

theorem expression_run {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (extra : Nat)
 (selector : Source.Idx Γ Selector) (refs : List (Source.Idx Γ (.bytes .memory)))
 (packets : List Roadmap.Bytes) (locals : Locals E.layout Γ) (state : St E)
 (memory : all_represented locals state refs packets) :
 (evalE G F (refs.length+extra+5) (.abiEncode .encodeWithSelector (args selector refs))).run (locals,state) =
 (.ok (.val (.memRef rfl state.heap.next)),(locals,
  SourceKeccak.afterLiteral state ((locals.get selector).bytesOf ++ AbiEntry.encodeArgs (abiValues packets)))) := by
 have arguments := arguments_run G F extra selector refs locals state
 have conversion := conversion_run F (refs.length+extra+4) (locals.get selector) locals state
 have encoded := LiteralFailureDynamicListError.encoding_run F (refs.length+extra+4)
  refs packets locals locals state memory
 have execution := SourceAbi.selector_execute G F (refs.length+extra+4) (args selector refs)
  locals locals locals locals state state state state (.val (locals.get selector))
  (values locals refs).toR (locals.get selector)
  (abiLayout (packets.map (fun bytes => (true,bytes)))) arguments conversion encoded
 simpa only [abi_agreement,Nat.add_assoc] using execution

theorem prefix_readback {D : Layout} (value : Source.Val D Selector) (data : Roadmap.Bytes) :
 (value.bytesOf ++ data).take 4 = value.bytesOf := by
 rw [← selector_extent value]
 simp only [List.take_append,List.take_length,Nat.sub_self,List.take_zero,List.append_nil]

theorem body_readback {D : Layout} (value : Source.Val D Selector) (data : Roadmap.Bytes) :
 (value.bytesOf ++ data).drop 4 = data := by
 rw [← selector_extent value]
 simp only [List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append]

end Solidity.Lowering.V08.LiteralFailureSelectorBytes
