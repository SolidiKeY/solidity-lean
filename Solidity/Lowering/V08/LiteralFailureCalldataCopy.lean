import Solidity.Lowering.V08.LiteralFailureTypedFields
import Solidity.Source.Calldata

/-! Actual published calldata-to-memory argument copy before custom-error
encoding. Slice extraction remains exactly drop/take; no entry-admission,
copy semantics, decoder, heap or target machine is added. -/
namespace Solidity.Lowering.V08.LiteralFailureCalldataCopy
open Solidity Source

def copied (F : Fr) (off len : Nat) := (F.cd.drop off).take len

theorem copy_run {E : Env} {Γ : RCtx} (F : Fr) (fuel off len : Nat)
 (locals : Locals E.layout Γ) (state : St E) :
 (convRV F fuel (.bytes .memory)
  (.val (.cdRef rfl off len) : RVal E.layout (.bytes .calldata)) : EM E Γ _).run (locals,state)=
 (.ok (.val (.memRef rfl state.heap.next)),(locals,SourceKeccak.afterLiteral state (copied F off len))) := by
 rfl

theorem keep_reference {E : Env} {Γ : RCtx} (F : Fr) (fuel off len : Nat)
 (locals : Locals E.layout Γ) (state : St E) :
 (convRV F fuel (.bytes .calldata)
  (.val (.cdRef rfl off len) : RVal E.layout (.bytes .calldata)) : EM E Γ _).run (locals,state)=
 (.ok (.val (.cdRef rfl off len)),(locals,state)) := rfl

def initial {E : Env} {Γ : RCtx} (off len : Nat) (older : Locals E.layout Γ) :
 Locals E.layout (.bytes .calldata::Γ) := .cons (.cdRef rfl off len) older

def arguments {E : Env} {Γ types} (tail : RConvArgs E (.bytes .calldata::Γ) types) :
 RConvArgs E (.bytes .calldata::Γ) (.bytes .memory::types) :=
 .cons (.local .here) rfl tail

theorem arguments_run {E : Env} {Γ types} {tail : RConvArgs E (.bytes .calldata::Γ) types}
 {source : Source.Vals E.layout types} (G : Glob E) (F : Fr) (extra off len : Nat)
 (older : Locals E.layout Γ) (state : St E)
 (lookups : LiteralFailureMixedCustomError.LocalArgs (initial off len older) tail source) :
 (evalConvArgs G F (types.length+extra+4) (arguments tail)).run (initial off len older,state)=
 (.ok (.cons (.memRef rfl state.heap.next) source),
  (initial off len older,SourceKeccak.afterLiteral state (copied F off len))) := by
 have headRun := copy_run F (types.length+extra+3) off len (initial off len older) state
 have tailRun := LiteralFailureMixedCustomError.arguments_run G F extra (initial off len older)
  (SourceKeccak.afterLiteral state (copied F off len)) lookups
 simp only [arguments]
 rw [evalConvArgs]
 simp only [evalE,EM.locals,initial,Locals.get,bind,pure,ExceptT.bind,
  ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,
  StateT.get,get,getThe,MonadStateOf.get,liftM,monadLift,MonadLift.monadLift,
  ExceptT.lift,Functor.map,StateT.map]
 dsimp only [ExceptT.run,initial] at headRun tailRun
 rw [headRun]
 simp only [getV,RVal.get,EM.lift,bind,pure,Except.pure,
  ExceptT.pure,ExceptT.bindCont,ExceptT.mk,StateT.bind,StateT.pure]
 rw [tailRun]
 rfl

theorem prefix_suffix (F : Fr) (before payload suffix : Roadmap.Bytes) :
 copied {F with cd:=before++payload++suffix} before.length payload.length=payload := by
 simp only [copied,List.append_assoc,List.drop_left,List.take_left]

theorem copied_fields {E : Env} {types shapes} {source : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} (F : Fr) (off len : Nat) (state : St E)
 (fields : LiteralFailureTypedFields.Fields state source encoded) :
 LiteralFailureTypedFields.Fields (SourceKeccak.afterLiteral state (copied F off len))
  (.cons (.memRef rfl state.heap.next : Source.Val E.layout (.bytes .memory)) source)
  (.cons (.bytes (copied F off len)) encoded) :=
 .bytes state.heap.next (copied F off len) (.inl (SourceKeccak.allocated state _))
  (LiteralFailureTypedFields.fields_after state _ fields)

theorem source_run {E : Env} {Γ types shapes}
 {tail : RConvArgs E (.bytes .calldata::Γ) types} {source : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} (G : Glob E) (F : Fr) (extra : Nat) (error : Decl)
 (typed : error.paramTys E=some (.bytes .memory::types)) (off len : Nat)
 (older : Locals E.layout Γ) (state : St E)
 (lookups : LiteralFailureMixedCustomError.LocalArgs (initial off len older) tail source)
 (fields : LiteralFailureTypedFields.Fields state source encoded) :
 (execS G F (types.length+extra+5) 0 none
  (.revertError error typed (arguments tail) : RStmt E [] false .body (.bytes .calldata::Γ) (.bytes .calldata::Γ))
  (initial off len older)).run (L0 E,state)=
 (.error (.revert (G.selector (sigOf E.layout error.name (.bytes .memory::types))++
  AbiEntry.encodeArgs (.cons (.bytes (copied F off len)) encoded))),
  (L0 E,SourceKeccak.afterLiteral state (copied F off len))) :=
 SourceCustomErrors.execute G F (types.length+extra+4) error typed (arguments tail)
 (initial off len older) (initial off len older) state _ _
 (.cons (.memRef rfl state.heap.next) source) _
 (arguments_run G F extra off len older state lookups)
 (LiteralFailureTypedFields.encoding_run F _ (L0 E) _ (copied_fields F off len state fields))

end Solidity.Lowering.V08.LiteralFailureCalldataCopy
