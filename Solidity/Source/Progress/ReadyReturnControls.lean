import Solidity.Source.Progress.ReadyReturns
import Solidity.Source.Preservation.MemoryProgramControls

/-! Actual source-elaborated alias and allocating reference returns. Default
return-slot allocation persists through success, allocation panic and body
timeout. These kernel source controls do not assert compiler refinement. -/
namespace Solidity.Source.Progress.ReadyReturnControls
open EM Preservation.MemoryProgramControls

def resultExpr : RExpr E (returnContext [Aty] Aty) Aty := .local (.there .here)
def same : Aty.implicit E.isBase E.mapFree Aty = true := by decide +kernel
def callee : {called : Decl // called ∈ Solidity.Lowering.P9.WholeProgram.functions resolution ∧
    called.fnSig E = some ([Aty],[Aty])} := ⟨d,by decide +kernel,signature⟩

theorem body (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (glob p fixed).prog.body ((glob p fixed).dispatchFn frame.contract callee.val) =
      some (singleReturningBody [Aty] Aty resultExpr same) := by
  dsimp only [callee]
  rw [show frame.contract = "Memory" from rfl,Preservation.MemoryProgramControls.dispatch]
  exact source_body

theorem checked (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (n : Nat) :
    NS (callInternal (glob p fixed) frame n d arguments [Aty]) ∧
    Hoare (fun y => MemOK E seed.ty y ∧ RValsOK E y.2.heap.ty arguments.toR)
      (callInternal (glob p fixed) frame n d arguments [Aty])
      (fun v y => MemOK E seed.ty y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E seed.ty y) :=
  single_return_from_elaborate resolution actual_elaboration (glob p fixed) rfl "Memory" [] (value_check p fixed)
    frame rfl [Aty] Aty callee resultExpr same (.inr rfl) (.local _) (.memory (.array _))
    (body p fixed) arguments seed.ty n

theorem progress_and_alias (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (callInternal (glob p fixed) frame 20 d arguments [Aty]) ∧
    MemOK E seed.ty ((.nil : Locals E.layout []),after) ∧
    RValOK E after.heap.ty (.val (.memRef rfl 0) : RVal E.layout Aty) := by
  have actual := (checked p fixed 20).2 (.nil,initial) ⟨entry_mem,arguments_valid⟩
  rw [Preservation.MemoryProgramControls.run] at actual
  exact ⟨(checked p fixed 20).1,actual⟩

theorem body_timeout (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (callInternal (glob p fixed) frame 4 d arguments [Aty]).run (.nil,initial) =
      (.error .timeout,(.nil,after)) := by
  have hb : (glob p fixed).prog.body d = some flatBody := source_body
  rw [callInternal,show frame.contract = "Memory" from rfl,Preservation.MemoryProgramControls.dispatch,hb]
  cases p <;> rfl

theorem timeout_mem (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    MemOK E seed.ty ((.nil : Locals E.layout []),after) := by
  have actual := (checked p fixed 4).2 (.nil,initial) ⟨entry_mem,arguments_valid⟩
  rw [body_timeout] at actual
  exact actual

theorem storage_default_refused : ¬ZeroReady E (.bytes .storage) := by
  intro ready
  rcases ready.boundary with default | memory
  · cases default
  · cases memory

theorem storage_zero_run :
    (zeroVal (E := E) (Γ := []) 2 (.bytes .storage)).run (.nil,initial) =
      (.error (.stuck "no default value"),(.nil,initial)) := rfl

#print axioms storage_zero_run
#print axioms checked
#print axioms progress_and_alias
#print axioms timeout_mem
end Solidity.Source.Progress.ReadyReturnControls

namespace Solidity.Source.Progress.ReadyFreshReturnControls
open EM Solidity.Lowering.P9

def uintType : Syn .typeName := .elem (.int false 256 (by decide))
def arrayType : Syn .typeName := .array uintType .none
def function : Syn (.part true) := .function (.ident "fresh")
  (.cons (.param uintType none (some "n")) .nil) none none .nil false none
  (.cons (.param arrayType (some .memory) none) .nil)
  (.some (.block (.cons (.stmtItem (.returnStmt (.some
    (.call (.new arrayType) (.positional (.cons (.ident "n") .nil)))))) .nil)))
def unit : Syn .unit := .unit (.cons (.topPart function) .nil)
def resolution := Source.resolveUnit {pipeline := .legacy} unit
abbrev E := resolution.env
abbrev U : STy := .int .u256
abbrev Aty : STy := .array .memory U none
def d : Decl := ⟨.function,"fresh",none,true,function⟩
def sourceFrame := (d.frame? E).get (by rfl)
def inferred := (ItemsD.infer (sourceFrame.ctx E d.scope) sourceFrame.locals sourceFrame.body).get (by rfl)
def inferredBody := RBody.ofDerivation sourceFrame inferred.2 []
def resultExpr : RExpr E (returnContext [U] Aty) Aty := .newArray rfl (.local (.there .here)) rfl
def same : Aty.implicit E.isBase E.mapFree Aty = true := by decide +kernel
def body := singleReturningBody [U] Aty resultExpr same

theorem signature : d.fnSig E = some ([U],[Aty]) := rfl
theorem source_frame : d.frame? E = some sourceFrame := rfl
theorem source_inferred : ItemsD.infer (sourceFrame.ctx E d.scope) sourceFrame.locals sourceFrame.body = some inferred := rfl
theorem invs : d.modInvs.invList = [] := by rw [show d.modInvs = .nil from rfl,Syn.invList]
theorem body_exists : (Source.elabBody E d).isSome = true :=
  InferenceCuts.body_some _ _ _ source_frame (by rw [source_inferred]; rfl) invs
theorem body_flat : inferredBody = body := rfl

theorem source_body : (Source.progOf E).body d = some body := by
  have hm : (Source.elabMods E d sourceFrame d.modInvs.invList).map Subtype.val = some [] := by
    rw [invs,Source.elabMods]; rfl
  simp only [Source.progOf,Source.elabBody,source_frame,source_inferred]
  cases actual : Source.elabMods E d sourceFrame d.modInvs.invList with
  | none => rw [actual] at hm; cases hm
  | some value =>
    rcases value with ⟨ms,hms⟩
    simp only [actual,Option.map_some,Option.some.injEq] at hm
    subst ms
    exact congrArg some body_flat

theorem elaborates : Source.elaborates E = true := by
  change (((((true && ((Source.elabBody E d).isSome && true)) && true) && true))) = true
  rw [body_exists]
  rfl
theorem actual_elaboration : (Source.elaborate resolution).isSome = true := by
  simp only [Source.elaborate,elaborates,↓reduceIte,Option.isSome_some]

def glob (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) : Glob E :=
  ⟨Source.progOf E,p,fixed,fun _ => ⟨0,by decide⟩,fun _ _ => true,
    fun _ => .answer (.success []),⟨0,by decide⟩⟩
def frame : Fr where
  this := ⟨17,by decide⟩
  sender := ⟨19,by decide⟩
  value := ⟨0,by decide⟩
  static := false
  contract := "Memory"

theorem dispatch (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) : (glob p fixed).dispatchFn "Memory" d = d := by
  unfold Glob.dispatchFn
  rw [signature]
  rfl

def original : Data E.layout Aty := .array 1 (fun _ h => nomatch h) (fun _ => .val (.int 7 (by decide)))
def empty : Data E.layout Aty := .array 0 (fun _ h => nomatch h) (fun i => i.elim0)
def fresh : Data E.layout Aty := .array 2 (fun _ h => nomatch h) (fun _ => .val (.int 0 (by decide)))
def seed : Heap E.layout := (Heap.empty.alloc ⟨Aty,original⟩).1
def initial : St E where
  ex := ⟨⟨fun _ => Account.empty _⟩,Transient.empty,[]⟩
  heap := seed
  events := []
  logs := [(⟨17,by decide⟩,[9])]
  fnLocals := ⟨[],.nil⟩
def defaulted : St E := {initial with heap := (seed.alloc ⟨Aty,empty⟩).1}
def after : St E := {defaulted with heap := (defaulted.heap.alloc ⟨Aty,fresh⟩).1}
def arguments : Vals E.layout [U] := .cons (.int 2 (by decide)) .nil
def huge : Vals E.layout [U] := .cons (.int (2^64) (by decide)) .nil
def callee : {called : Decl // called ∈ WholeProgram.functions resolution ∧ called.fnSig E = some ([U],[Aty])} :=
  ⟨d,by decide +kernel,signature⟩

theorem entry_mem : MemOK E seed.ty ((.nil : Locals E.layout []),initial) := by
  have heap : HeapOK (E := E) seed := HeapOK.empty.alloc (.array (fun _ => .val trivial))
  have shape : HeapShaped seed := HeapShaped.empty.alloc trivial
  have inner : HeapInner seed := HeapInner.empty.alloc (fun _ => ⟨_,rfl⟩)
  exact ⟨⟨⟨heap,HeapTy.Le.refl _⟩,trivial⟩,shape,inner⟩

theorem selected_body (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (glob p fixed).prog.body ((glob p fixed).dispatchFn frame.contract callee.val) = some body := by
  dsimp only [callee]
  rw [show frame.contract = "Memory" from rfl,dispatch]
  exact source_body

theorem checked (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (vs : Vals E.layout [U]) (n : Nat) :
    NS (callInternal (glob p fixed) frame n d vs [Aty]) ∧
    Hoare (fun y => MemOK E seed.ty y ∧ RValsOK E y.2.heap.ty vs.toR)
      (callInternal (glob p fixed) frame n d vs [Aty])
      (fun v y => MemOK E seed.ty y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E seed.ty y) :=
  single_return_from_elaborate resolution actual_elaboration (glob p fixed) rfl "Memory" [] rfl
    frame rfl [U] Aty callee resultExpr same (.inr rfl)
    (.newArray (.array U rfl rfl) rfl (.local _)) (.memory (.array _)) (selected_body p fixed) vs seed.ty n

theorem success_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (callInternal (glob p fixed) frame 20 d arguments [Aty]).run (.nil,initial) =
      (.ok (.val (.memRef rfl 2)),(.nil,after)) := by
  have hb : (glob p fixed).prog.body d = some body := source_body
  rw [callInternal,show frame.contract = "Memory" from rfl,dispatch,hb]
  cases p <;> rfl

theorem panic_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (callInternal (glob p fixed) frame 20 d huge [Aty]).run (.nil,initial) =
      (.error (.revert (panicData .alloc)),(.nil,defaulted)) := by
  have hb : (glob p fixed).prog.body d = some body := source_body
  rw [callInternal,show frame.contract = "Memory" from rfl,dispatch,hb]
  cases p <;> rfl

theorem preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (callInternal (glob p fixed) frame 20 d arguments [Aty]) ∧
    (MemOK E seed.ty ((.nil : Locals E.layout []),after) ∧
      RValOK E after.heap.ty (.val (.memRef rfl 2) : RVal E.layout Aty)) ∧
    MemOK E seed.ty ((.nil : Locals E.layout []),defaulted) := by
  have success := (checked p fixed arguments 20).2 (.nil,initial) ⟨entry_mem,trivial,trivial⟩
  have panic := (checked p fixed huge 20).2 (.nil,initial) ⟨entry_mem,trivial,trivial⟩
  rw [success_run] at success
  rw [panic_run] at panic
  exact ⟨(checked p fixed arguments 20).1,success,panic⟩

def caller : Locals E.layout [U,Aty] := .cons (.int 2 (by decide)) (.cons (.memRef rfl 0) .nil)
def callArgs : RConvArgs E [U,Aty] [U] := .cons (.local .here) rfl .nil

theorem caller_mem : MemOK E seed.ty (caller,initial) :=
  Preservation.relocalize entry_mem caller ⟨trivial,⟨Aty,rfl,rfl⟩,trivial⟩

theorem argument_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalConvArgs (glob p fixed) frame 20 callArgs).run (caller,initial) =
      (.ok arguments,(caller,initial)) := by
  simp only [callArgs,evalConvArgs,Hoare.run_bind,evalE,convRV,↓reduceDIte,getV,pure_bind]
  rfl

theorem expression_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 21 (.call d signature callArgs)).run (caller,initial) =
      (.ok (.val (.memRef rfl 2)),(caller,after)) := by
  rw [evalE,Hoare.run_bind,argument_run]
  dsimp only
  rw [Hoare.run_bind]
  have inner : callInternal (plan := none) (calldataKnown := true) (glob p fixed) frame 20 d arguments [Aty] (.nil,initial) =
      (.ok (.val (.memRef rfl 2)),(.nil,after)) := success_run p fixed
  simp only [EM.sub,ExceptT.run,ExceptT.mk,inner]
  rfl

theorem expression_progress_and_memory (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (glob p fixed) frame 21 (.call d signature callArgs)) ∧
    MemOK E seed.ty (caller,after) ∧ RValOK E after.heap.ty (.val (.memRef rfl 2) : RVal E.layout Aty) := by
  have joint := single_return_expr_from_elaborate resolution actual_elaboration (glob p fixed) rfl "Memory" [] rfl
    frame rfl [U] Aty callee resultExpr same (.inr rfl)
    (.newArray (.array U rfl rfl) rfl (.local _)) (.memory (.array _)) (selected_body p fixed)
    callArgs (.cons rfl (.inl rfl) (.local _) .nil) seed.ty 20
  have actual := joint.2 (caller,initial) caller_mem
  dsimp only [callee] at joint actual
  rw [expression_run] at actual
  exact ⟨joint.1,actual⟩

#print axioms expression_progress_and_memory
#print axioms expression_run
#print axioms actual_elaboration
#print axioms checked
#print axioms preserved
#print axioms success_run
#print axioms panic_run
end Solidity.Source.Progress.ReadyFreshReturnControls
