import Solidity.Source.Progress.ReadyProgram
import Solidity.Lowering.P9.InferenceCuts
import Solidity.Roadmap.Controls
import Solidity.Source.Progress.ReadyReturnControls

/-! A real mixed source unit: a scalar helper supplies the allocation length
of a memory-returning function. Both functions are accounted for; exact nested
runs retain a live memory prefix. Omission and old-checker refusals remain. -/
namespace Solidity.Source.Progress.ReadyProgramControls
open EM Solidity.Lowering.P9

def uintType : Syn .typeName := .elem (.int false 256 (by decide))
def arrayType : Syn .typeName := .array uintType .none
def countReturn : Syn (.stmt .body) := .returnStmt (.some (.lit (.num (.dec 2 0 0))))
def countFunction : Syn (.part true) := .function (.ident "count") .nil none none .nil false none
  (.cons (.param uintType none none) .nil)
  (.some (.block (.cons (.stmtItem countReturn) .nil)))
def countCall : Syn .expr := .call (.ident "count") (.positional .nil)
def freshFunction : Syn (.part true) := .function (.ident "fresh") .nil none none .nil false none
  (.cons (.param arrayType (some .memory) none) .nil)
  (.some (.block (.cons (.stmtItem (.returnStmt (.some
    (.call (.new arrayType) (.positional (.cons countCall .nil)))))) .nil)))
def unit : Syn .unit := .unit (.cons (.topPart countFunction) (.cons (.topPart freshFunction) .nil))
def resolution := Source.resolveUnit {pipeline := .legacy} unit
abbrev E := resolution.env
abbrev U : STy := .int .u256
abbrev Aty : STy := .array .memory U none
def countDecl : Decl := ⟨.function,"count",none,true,countFunction⟩
def freshDecl : Decl := ⟨.function,"fresh",none,true,freshFunction⟩
def countFrame := (countDecl.frame? E).get (by rfl)
def countInferred := (ItemsD.infer (countFrame.ctx E countDecl.scope) countFrame.locals countFrame.body).get (by rfl)
def countBody := RBody.ofDerivation countFrame countInferred.2 []
def freshFrame := (freshDecl.frame? E).get (by rfl)
def freshInferred := (ItemsD.infer (freshFrame.ctx E freshDecl.scope) freshFrame.locals freshFrame.body).get (by rfl)
def freshBody := RBody.ofDerivation freshFrame freshInferred.2 []

theorem count_frame : countDecl.frame? E = some countFrame := rfl
theorem count_inferred : ItemsD.infer (countFrame.ctx E countDecl.scope) countFrame.locals countFrame.body = some countInferred := rfl
theorem count_invs : countDecl.modInvs.invList = [] := by rw [show countDecl.modInvs = .nil from rfl,Syn.invList]
theorem count_exists : (Source.elabBody E countDecl).isSome = true :=
  InferenceCuts.body_some _ _ _ count_frame (by rw [count_inferred]; rfl) count_invs

theorem fresh_frame : freshDecl.frame? E = some freshFrame := rfl
theorem fresh_inferred : ItemsD.infer (freshFrame.ctx E freshDecl.scope) freshFrame.locals freshFrame.body = some freshInferred := rfl
theorem fresh_invs : freshDecl.modInvs.invList = [] := by rw [show freshDecl.modInvs = .nil from rfl,Syn.invList]
theorem fresh_exists : (Source.elabBody E freshDecl).isSome = true :=
  InferenceCuts.body_some _ _ _ fresh_frame (by rw [fresh_inferred]; rfl) fresh_invs

theorem count_body : (Source.progOf E).body countDecl = some countBody := by
  have hm : (Source.elabMods E countDecl countFrame countDecl.modInvs.invList).map Subtype.val = some [] := by
    rw [count_invs,Source.elabMods]; rfl
  simp only [Source.progOf,Source.elabBody,count_frame,count_inferred]
  cases actual : Source.elabMods E countDecl countFrame countDecl.modInvs.invList with
  | none => rw [actual] at hm; cases hm
  | some value =>
    rcases value with ⟨ms,hms⟩
    simp only [actual,Option.map_some,Option.some.injEq] at hm
    subst ms
    rfl

theorem fresh_body : (Source.progOf E).body freshDecl = some freshBody := by
  have hm : (Source.elabMods E freshDecl freshFrame freshDecl.modInvs.invList).map Subtype.val = some [] := by
    rw [fresh_invs,Source.elabMods]; rfl
  simp only [Source.progOf,Source.elabBody,fresh_frame,fresh_inferred]
  cases actual : Source.elabMods E freshDecl freshFrame freshDecl.modInvs.invList with
  | none => rw [actual] at hm; cases hm
  | some value =>
    rcases value with ⟨ms,hms⟩
    simp only [actual,Option.map_some,Option.some.injEq] at hm
    subst ms
    rfl

theorem count_signature : countDecl.fnSig E = some ([],[U]) := rfl
theorem fresh_signature : freshDecl.fnSig E = some ([],[Aty]) := rfl

def flatCount : RBody E where
  ps := []; rs := [U]; inModifier := false; locals := [U]; out := [U]
  items := .stmt (.retVal rfl (.const (Q.ofInt 2)) (by decide +kernel)) .nil
def resultExpr : RExpr E (returnContext [] Aty) Aty :=
  .newArray rfl (.call countDecl count_signature .nil) rfl
def same : Aty.implicit E.isBase Aty = true := by decide +kernel
def flatFresh := singleReturningBody [] Aty resultExpr same

theorem count_flat : countBody = flatCount := rfl
theorem fresh_flat : freshBody = flatFresh := rfl

theorem elaborates : Source.elaborates E = true := by
  change (((((true && ((Source.elabBody E countDecl).isSome &&
    ((Source.elabBody E freshDecl).isSome && true))) && true) && true))) = true
  rw [count_exists,fresh_exists]
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

theorem count_dispatch (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (glob p fixed).dispatchFn "Memory" countDecl = countDecl := by
  unfold Glob.dispatchFn
  rw [count_signature]
  rfl
theorem fresh_dispatch (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (glob p fixed).dispatchFn "Memory" freshDecl = freshDecl := by
  unfold Glob.dispatchFn
  rw [fresh_signature]
  rfl

theorem value_check (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    WholeProgram.check resolution (glob p fixed) "Memory" [countDecl] = true := by
  simp only [WholeProgram.check,List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq]
  refine ⟨rfl,by decide +kernel,?_⟩
  have hb : (glob p fixed).prog.body countDecl = some flatCount := count_body.trans (congrArg some count_flat)
  simp only [WholeProgram.checkBody,count_signature,count_dispatch,hb]
  rfl

theorem expression_ready : ReadyExpr (fun d => d ∈ [countDecl]) resultExpr :=
  .newArray (.array U rfl rfl) rfl (.value ⟨by decide +kernel,trivial⟩ trivial)

theorem catalogue (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    ReadyReturnCatalogue resolution (glob p fixed) "Memory" [countDecl] [freshDecl] := by
  intro called member
  rcases List.mem_singleton.mp member with rfl
  refine ⟨by decide +kernel,[],Aty,resultExpr,same,fresh_signature,.inr rfl,expression_ready,.memory (.array U),?_⟩
  rw [fresh_dispatch]
  exact fresh_body.trans (congrArg some fresh_flat)

theorem coverage : readyCoverage resolution [countDecl] [freshDecl] = true := by decide +kernel
theorem omitted_value_refused : readyCoverage resolution [] [freshDecl] = false := by decide +kernel
theorem omitted_memory_refused : readyCoverage resolution [countDecl] [] = false := by decide +kernel

theorem all_calls (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) : ReadyProgramCalls resolution (glob p fixed) "Memory" :=
  ready_program_calls resolution actual_elaboration (glob p fixed) rfl "Memory" [countDecl] [freshDecl]
    (value_check p fixed) (catalogue p fixed) coverage

def cachedGlob (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) : Glob E :=
  {glob p fixed with prog := {(glob p fixed).prog with body := fun called => if called = countDecl then some flatCount else if called = freshDecl then some flatFresh else (glob p fixed).prog.body called}}

theorem cachedGlob_eq (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) : cachedGlob p fixed = glob p fixed := by
  have hc : (glob p fixed).prog.body countDecl = some flatCount := count_body.trans (congrArg some count_flat)
  have hf : (glob p fixed).prog.body freshDecl = some flatFresh := fresh_body.trans (congrArg some fresh_flat)
  have hp : (fun called => if called = countDecl then some flatCount else if called = freshDecl then some flatFresh
      else (glob p fixed).prog.body called) = (glob p fixed).prog.body := by
    funext called
    split
    next h => subst called; exact hc.symm
    next h =>
      split
      next h => subst called; exact hf.symm
      next h => rfl
  unfold cachedGlob
  rw [hp]

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
def after : St E := {initial with heap := ((seed.alloc ⟨Aty,empty⟩).1.alloc ⟨Aty,fresh⟩).1}
def caller : Locals E.layout [Aty] := .cons (.memRef rfl 0) .nil

theorem initial_mem : MemOK E seed.ty ((.nil : Locals E.layout []),initial) := by
  have heap : HeapOK (E := E) seed := HeapOK.empty.alloc (.array (fun _ => .val trivial))
  have shape : HeapShaped seed := HeapShaped.empty.alloc trivial
  have inner : HeapInner seed := HeapInner.empty.alloc (fun _ => ⟨_,rfl⟩)
  exact ⟨⟨⟨heap,HeapTy.Le.refl _⟩,trivial⟩,shape,inner⟩

theorem scalar_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (callInternal (glob p fixed) frame 20 countDecl (.nil : Vals E.layout []) [U]).run (.nil,initial) =
      (.ok (.val (.int 2 (by decide))),(.nil,initial)) := by
  rw [←cachedGlob_eq p fixed]
  cases p <;> rfl

theorem memory_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (callInternal (glob p fixed) frame 20 freshDecl (.nil : Vals E.layout []) [Aty]).run (.nil,initial) =
      (.ok (.val (.memRef rfl 2)),(.nil,after)) := by
  rw [←cachedGlob_eq p fixed]
  cases p <;> rfl

theorem both_branches_preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (NS (callInternal (glob p fixed) frame 20 countDecl (.nil : Vals E.layout []) [U]) ∧
      MemOK E seed.ty ((.nil : Locals E.layout []),initial)) ∧
    (NS (callInternal (glob p fixed) frame 20 freshDecl (.nil : Vals E.layout []) [Aty]) ∧
      MemOK E seed.ty ((.nil : Locals E.layout []),after) ∧
      RValOK E after.heap.ty (.val (.memRef rfl 2) : RVal E.layout Aty)) := by
  have scalar := all_calls p fixed frame rfl countDecl count_signature (by decide +kernel) .nil seed.ty 20
  have memory := all_calls p fixed frame rfl freshDecl fresh_signature (by decide +kernel) .nil seed.ty 20
  have hs := scalar.2 (.nil,initial) ⟨initial_mem,trivial⟩
  have hm := memory.2 (.nil,initial) ⟨initial_mem,trivial⟩
  rw [scalar_run] at hs
  rw [memory_run] at hm
  exact ⟨⟨scalar.1,hs.1⟩,memory.1,hm⟩

def expression : RExpr E [Aty] Aty := .call freshDecl fresh_signature .nil

theorem expression_ns (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) : NS (evalE (glob p fixed) frame 21 expression) :=
  ready_program_expr_ns resolution actual_elaboration (glob p fixed) rfl "Memory" [countDecl] [freshDecl]
    (value_check p fixed) (catalogue p fixed) coverage frame rfl 21 expression ⟨by decide +kernel,trivial⟩ trivial

theorem expression_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 21 expression).run (caller,initial) =
      (.ok (.val (.memRef rfl 2)),(caller,after)) := by
  rw [←cachedGlob_eq p fixed]
  cases p <;> rfl

theorem expression_memory_witness (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (glob p fixed) frame 21 expression) ∧
    MemOK E seed.ty (caller,after) ∧ RValOK E after.heap.ty (.val (.memRef rfl 2) : RVal E.layout Aty) := by
  have call := (all_calls p fixed frame rfl freshDecl fresh_signature (by decide +kernel) .nil seed.ty 20).2
    (.nil,initial) ⟨initial_mem,trivial⟩
  rw [memory_run] at call
  have before : LocalsOK E seed.ty caller := ⟨⟨Aty,rfl,rfl⟩,trivial⟩
  have retained := LocalsOK.mono call.1.le caller before
  exact ⟨expression_ns p fixed,Preservation.relocalize call.1 caller retained,call.2⟩

theorem old_checker_refused (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    WholeProgram.checkFunctions resolution (glob p fixed) "Memory" = false := by
  change WholeProgram.check resolution (glob p fixed) "Memory" [countDecl,freshDecl] = false
  have hc : (glob p fixed).prog.body countDecl = some flatCount := count_body.trans (congrArg some count_flat)
  have hf : (glob p fixed).prog.body freshDecl = some flatFresh := fresh_body.trans (congrArg some fresh_flat)
  unfold WholeProgram.check
  simp only [List.all_cons,List.all_nil]
  unfold WholeProgram.checkBody
  simp only [count_signature,fresh_signature,count_dispatch,fresh_dispatch,hc,hf]
  rfl

#print axioms actual_elaboration
#print axioms all_calls
#print axioms both_branches_preserved
#print axioms memory_run
#print axioms expression_ns
#print axioms expression_run
#print axioms old_checker_refused
#print axioms expression_memory_witness
end Solidity.Source.Progress.ReadyProgramControls

namespace Solidity.Source.Progress.ReadyProgramIdentityControls
open EM Preservation.MemoryProgramControls
open ReadyReturnControls (resultExpr same)

theorem catalogue (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    ReadyReturnCatalogue resolution (glob p fixed) "Memory" [] [d] := by
  intro called member
  rcases List.mem_singleton.mp member with rfl
  refine ⟨by decide +kernel,[Aty],Aty,resultExpr,same,signature,.inr rfl,.local _,.memory (.array _),?_⟩
  exact ReadyReturnControls.body p fixed

theorem coverage : readyCoverage resolution [] [d] = true := by decide +kernel

theorem checked (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) : ReadyProgramCalls resolution (glob p fixed) "Memory" :=
  ready_program_calls resolution actual_elaboration (glob p fixed) rfl "Memory" [] [d]
    (value_check p fixed) (catalogue p fixed) coverage

theorem inhabited (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (callInternal (glob p fixed) frame 20 d arguments [Aty]) ∧
    MemOK E seed.ty ((.nil : Locals E.layout []),after) ∧
    RValOK E after.heap.ty (.val (.memRef rfl 0) : RVal E.layout Aty) := by
  have joint := checked p fixed frame rfl d signature (by decide +kernel) arguments seed.ty 20
  have actual := joint.2 (.nil,initial) ⟨entry_mem,arguments_valid⟩
  rw [Preservation.MemoryProgramControls.run] at actual
  exact ⟨joint.1,actual⟩

#print axioms checked
#print axioms inhabited
end Solidity.Source.Progress.ReadyProgramIdentityControls
