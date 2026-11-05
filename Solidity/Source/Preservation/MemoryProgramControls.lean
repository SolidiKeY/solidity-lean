import Solidity.Source.Preservation.MemoryProgram
import Solidity.Lowering.P9.InferenceCuts
import Solidity.Roadmap.Controls

/-! A source-elaborated memory parameter and ordinary single-reference return.
The complete memory catalogue consumes derived frame facts, actual call runs
and inhabited heap typing; the old value-only checker still refuses this body. -/
namespace Solidity.Source.Preservation.MemoryProgramControls
open EM Solidity.Lowering.P9

def uintType : Syn .typeName := .elem (.int false 256 (by decide))
def arrayType : Syn .typeName := .array uintType .none
def function : Syn (.part true) := .function (.ident "identity")
  (.cons (.param arrayType (some .memory) (some "a")) .nil) none none .nil false none
  (.cons (.param arrayType (some .memory) none) .nil)
  (.some (.block (.cons (.stmtItem (.returnStmt (.some (.ident "a")))) .nil)))
def unit : Syn .unit := .unit (.cons (.topPart function) .nil)
def resolution := Source.resolveUnit {pipeline := .legacy} unit
abbrev E := resolution.env
abbrev Aty : STy := .array .memory (.int .u256) none
def d : Decl := ⟨.function,"identity",none,true,function⟩
def sourceFrame := (d.frame? E).get (by rfl)
def inferred := (ItemsD.infer (sourceFrame.ctx E d.scope) sourceFrame.locals sourceFrame.body).get (by rfl)
def inferredBody := RBody.ofDerivation sourceFrame inferred.2 []
def flatBody : RBody E where
  ps := [Aty]; rs := [Aty]; inModifier := false
  locals := [Aty,Aty]; out := [Aty,Aty]
  items := .stmt (.retVal rfl (.local (.there .here)) (by decide +kernel)) .nil

theorem signature : d.fnSig E = some ([Aty],[Aty]) := rfl
theorem source_frame : d.frame? E = some sourceFrame := rfl
theorem source_inferred : ItemsD.infer (sourceFrame.ctx E d.scope) sourceFrame.locals sourceFrame.body = some inferred := rfl
theorem invs : d.modInvs.invList = [] := by rw [show d.modInvs = .nil from rfl,Syn.invList]
theorem body_exists : (Source.elabBody E d).isSome = true :=
  InferenceCuts.body_some _ _ _ source_frame (by rw [source_inferred]; rfl) invs
theorem body_flat : inferredBody = flatBody := rfl

theorem source_body : (Source.progOf E).body d = some flatBody := by
  have hm : (Source.elabMods E d sourceFrame d.modInvs.invList).map Subtype.val = some [] := by
    rw [invs,Source.elabMods]; rfl
  simp only [Source.progOf,Source.elabBody,source_frame,source_inferred]
  cases actual : Source.elabMods E d sourceFrame d.modInvs.invList with
  | none => rw [actual] at hm; cases hm
  | some v =>
    rcases v with ⟨ms,hms⟩
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
theorem fragment : MemoryItems (fun d => d ∈ ([] : List Decl)) [Aty] false flatBody.items :=
  .stmt (.returnValue rfl (by decide +kernel) (.base (.local _))) .nil

theorem value_check (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    WholeProgram.check resolution (glob p fixed) "Memory" [] = true := rfl

theorem catalogue (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    MemoryCatalogue (fun d => d ∈ ([] : List Decl)) (glob p fixed) "Memory" [d] := by
  intro called member
  rcases List.mem_singleton.mp member with rfl
  refine ⟨by decide +kernel,[Aty],[Aty],[Aty],flatBody,signature,?_,?_,rfl,fragment⟩
  · rw [dispatch]; exact signature
  · rw [dispatch]; exact source_body

theorem coverage : (WholeProgram.functions resolution).all (fun called => decide (called ∈ [d])) = true := by decide +kernel
theorem omitted_refused : (WholeProgram.functions resolution).all (fun called => decide (called ∈ ([] : List Decl))) = false := by decide +kernel

def original : Data E.layout Aty := .array 1 (fun _ h => nomatch h) (fun _ => .val (.int 7 (by decide)))
def empty : Data E.layout Aty := .array 0 (fun _ h => nomatch h) (fun i => i.elim0)
def seed : Heap E.layout := (Heap.empty.alloc ⟨Aty,original⟩).1
def initial : St E where
  ex := ⟨⟨fun _ => Account.empty _⟩,Transient.empty,[]⟩
  heap := seed
  events := []
  logs := [(⟨17,by decide⟩,[9])]
  fnLocals := ⟨[],.nil⟩
def after : St E := {initial with heap := (seed.alloc ⟨Aty,empty⟩).1}
def arguments : Vals E.layout [Aty] := .cons (.memRef rfl 0) .nil

theorem entry_mem : MemOK E seed.ty ((.nil : Locals E.layout []),initial) := by
  have heap : HeapOK (E := E) seed := HeapOK.empty.alloc (.array (fun _ => .val trivial))
  have shape : HeapShaped seed := HeapShaped.empty.alloc trivial
  have inner : HeapInner seed := HeapInner.empty.alloc (fun _ => ⟨_,rfl⟩)
  exact ⟨⟨⟨heap,HeapTy.Le.refl _⟩,trivial⟩,shape,inner⟩
theorem arguments_valid : RValsOK E initial.heap.ty arguments.toR := ⟨⟨Aty,rfl,rfl⟩,trivial⟩

theorem run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (callInternal (glob p fixed) frame 20 d arguments [Aty]).run (.nil,initial) =
      (.ok (.val (.memRef rfl 0)),(.nil,after)) := by
  have hb : (glob p fixed).prog.body d = some flatBody := source_body
  rw [callInternal,show frame.contract = "Memory" from rfl,dispatch,hb]
  cases p <;> rfl

theorem preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    MemOK E seed.ty ((.nil : Locals E.layout []),after) ∧
      RValOK E after.heap.ty (.val (.memRef rfl 0) : RVal E.layout Aty) := by
  have actual := checked_memory_call resolution actual_elaboration (glob p fixed) rfl "Memory" [] [d]
    (value_check p fixed) (catalogue p fixed) coverage frame rfl d signature
    (by decide +kernel) arguments seed.ty 20 (.nil,initial) ⟨entry_mem,arguments_valid⟩
  rw [run] at actual
  exact actual

theorem legacy_refused (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    WholeProgram.checkFunctions resolution (glob p fixed) "Memory" = false := by
  change WholeProgram.check resolution (glob p fixed) "Memory" [d] = false
  unfold WholeProgram.check
  simp only [List.all_cons,List.all_nil]
  unfold WholeProgram.checkBody
  have hb : (glob p fixed).prog.body d = some flatBody := source_body
  simp only [signature,dispatch,hb]
  rfl

def caller : Locals E.layout [Aty] := .cons (.memRef rfl 0) .nil
def callArgs : RConvArgs E [Aty] [Aty] := .cons (.local .here) (by decide +kernel) .nil

theorem caller_mem : MemOK E seed.ty (caller,initial) :=
  relocalize entry_mem caller ⟨⟨Aty,rfl,rfl⟩,trivial⟩

theorem argument_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalConvArgs (glob p fixed) frame 20 callArgs).run (caller,initial) =
      (.ok arguments,(caller,initial)) := by
  simp only [callArgs,evalConvArgs,Hoare.run_bind,evalE,convRV,↓reduceDIte,getV,pure_bind]
  rfl

theorem expression_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 21 (.call d signature callArgs)).run (caller,initial) =
      (.ok (.val (.memRef rfl 0)),(caller,after)) := by
  rw [evalE,Hoare.run_bind,argument_run]
  dsimp only
  rw [Hoare.run_bind]
  have inner : callInternal (glob p fixed) frame 20 d arguments [Aty] (.nil,initial) =
      (.ok (.val (.memRef rfl 0)),(.nil,after)) := run p fixed
  simp only [EM.sub,ExceptT.run,ExceptT.mk,inner]
  rfl

theorem expression_preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    MemOK E seed.ty (caller,after) ∧
      RValOK E after.heap.ty (.val (.memRef rfl 0) : RVal E.layout Aty) := by
  have actual := memory_expr_from_elaborate resolution actual_elaboration (glob p fixed) rfl "Memory" [] [d]
    (value_check p fixed) (catalogue p fixed) frame rfl d signature (by decide +kernel)
    callArgs (.cons _ (.local _) .nil) seed.ty 20 (caller,initial) caller_mem
  rw [expression_run] at actual
  exact actual

theorem retained_objects : after.heap.next = 2 ∧
    after.heap.get 0 = some ⟨Aty,original⟩ ∧ after.heap.get 1 = some ⟨Aty,empty⟩ := ⟨rfl,rfl,rfl⟩

theorem timeout_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (callInternal (glob p fixed) frame 0 d arguments [Aty]).run (.nil,initial) =
      (.error .timeout,(.nil,initial)) := rfl

#print axioms expression_preserved
#print axioms expression_run
#print axioms actual_elaboration
#print axioms preserved
#print axioms run
#print axioms legacy_refused
end Solidity.Source.Preservation.MemoryProgramControls
