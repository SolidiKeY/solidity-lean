import Solidity.Source.Progress.ReadyBodyCalls
import Solidity.Lowering.P9.InferenceCuts
import Solidity.Roadmap.Controls

/-! Actual elaborated declarations, a nested allocation scope and a reference
return. Locals leave scope while every reached allocation remains in the heap.
Both evaluator pipelines retain their actual panic and horizon behavior. -/
namespace Solidity.Source.Progress.ReadyBodyControls
open EM Solidity.Lowering.P9

def uintType : Syn .typeName := .elem (.int false 256 (by decide))
def arrayType : Syn .typeName := .array uintType .none
def lengthExpr : Syn .expr := .ident "n"
def newExpr : Syn .expr := .call (.new arrayType) (.positional (.cons lengthExpr .nil))
def emptyDecl : Syn (.stmt .body) := .simpleStmt (.declVar (.varDecl arrayType (some .memory) "a") .none)
def temporaryDecl : Syn (.stmt .body) := .simpleStmt
  (.declVar (.varDecl arrayType (some .memory) "temporary") (.some newExpr))
def nested : Syn (.stmt .body) := .blockStmt (.block (.cons (.stmtItem temporaryDecl) .nil))
def resultDecl : Syn (.stmt .body) := .simpleStmt
  (.declVar (.varDecl arrayType (some .memory) "b") (.some newExpr))
def resultReturn : Syn (.stmt .body) := .returnStmt (.some (.ident "b"))
def function : Syn (.part true) := .function (.ident "fresh")
  (.cons (.param uintType none (some "n")) .nil) none none .nil false none
  (.cons (.param arrayType (some .memory) none) .nil)
  (.some (.block (.cons (.stmtItem emptyDecl) (.cons (.stmtItem nested)
    (.cons (.stmtItem resultDecl) (.cons (.stmtItem resultReturn) .nil))))))

def unit : Syn .unit := .unit (.cons (.topPart function) .nil)
def resolution := Source.resolveUnit {pipeline := .legacy} unit
abbrev E := resolution.env
abbrev Aty : STy := .array .memory (.int .u256) none
def d : Decl := ⟨.function,"fresh",none,true,function⟩
def sourceFrame := (d.frame? E).get (by rfl)
def inferred := (ItemsD.infer (sourceFrame.ctx E d.scope) sourceFrame.locals sourceFrame.body).get (by rfl)
def inferredBody := RBody.ofDerivation sourceFrame inferred.2 []
abbrev U : STy := .int .u256
def flatBody : RBody E where
  ps := [U]; rs := [Aty]; inModifier := false
  locals := [Aty,U]; out := [Aty,Aty,Aty,U]
  items := .stmt (.declVar Aty)
    (.stmt (.block (.stmt (.declInit (τ := Aty)
      (.newArray (τ := Aty) rfl (.local (.there (.there .here))) rfl) (by decide +kernel)) .nil))
    (.stmt (.declInit (τ := Aty) (.newArray (τ := Aty) rfl (.local (.there (.there .here))) rfl) (by decide +kernel))
    (.stmt (.retVal rfl (.local .here) (by decide +kernel)) .nil)))

theorem signature : d.fnSig E = some ([U],[Aty]) := rfl

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
theorem value_check (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    WholeProgram.check resolution (glob p fixed) "Memory" [] = true := rfl

theorem fragment : ReadyItems (fun d => d ∈ ([] : List Decl)) [Aty] false flatBody.items :=
  .stmt (.declVar Aty (.memory (.array _)))
    (.stmt (.block (.stmt (.declInit _ (.inr rfl)
      (.newArray (.array U rfl rfl) rfl (.local _))) .nil))
    (.stmt (.declInit _ (.inr rfl) (.newArray (.array U rfl rfl) rfl (.local _)))
    (.stmt (.returnValue rfl _ (.inr rfl) (.local _)) .nil)))

theorem joint (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed)
    (vs : Vals E.layout [U]) (H : HeapTy) (n : Nat) :
    NS (callInternal (glob p fixed) frame n d vs [Aty]) ∧
    Hoare (fun y => MemOK E H y ∧ RValsOK E y.2.heap.ty vs.toR)
      (callInternal (glob p fixed) frame n d vs [Aty])
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) :=
  ready_body_call_from_elaborate resolution actual_elaboration (glob p fixed) rfl "Memory" []
    (value_check p fixed) frame rfl [U] [Aty] ⟨d,by decide +kernel,signature⟩ flatBody
    (by rw [show frame.contract = "Memory" from rfl,dispatch]; exact source_body)
    rfl rfl rfl rfl (fun τ member => by
      rcases List.mem_singleton.mp member with rfl
      exact .memory (.array _)) fragment vs H n

def original : Data E.layout Aty := .array 1 (fun _ h => nomatch h)
  (fun _ => .val (.int 7 (by decide)))
def empty : Data E.layout Aty := .array 0 (fun _ h => nomatch h) (fun i => i.elim0)
def fresh : Data E.layout Aty := .array 2 (fun _ h => nomatch h)
  (fun _ => .val (.int 0 (by decide)))
def seed : Heap E.layout := (Heap.empty.alloc ⟨Aty,original⟩).1
def initial : St E where
  ex := ⟨⟨fun _ => Account.empty _⟩,Transient.empty,[]⟩
  heap := seed
  events := []
  logs := [(⟨17,by decide⟩,[9])]
  fnLocals := ⟨[.bool],.cons (.bool true) .nil⟩
def defaulted : Heap E.layout := ((seed.alloc ⟨Aty,empty⟩).1.alloc ⟨Aty,empty⟩).1
def after : St E := {initial with heap :=
  ((defaulted.alloc ⟨Aty,fresh⟩).1.alloc ⟨Aty,fresh⟩).1}
def arguments : Vals E.layout [U] := .cons (.int 2 (by decide)) .nil

theorem entry_mem : MemOK E seed.ty ((.nil : Locals E.layout []),initial) := by
  have heap : HeapOK (E := E) seed := HeapOK.empty.alloc (.array (fun _ => .val trivial))
  have shape : HeapShaped seed := HeapShaped.empty.alloc trivial
  have inner : HeapInner seed := HeapInner.empty.alloc (fun _ => ⟨_,rfl⟩)
  exact ⟨⟨⟨heap,HeapTy.Le.refl _⟩,trivial⟩,shape,inner⟩

def cachedGlob (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) : Glob E :=
  {glob p fixed with prog := { (glob p fixed).prog with
    body := fun called => if called = d then some flatBody else (glob p fixed).prog.body called }}

theorem cachedGlob_eq (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) : cachedGlob p fixed = glob p fixed := by
  have bodies : (cachedGlob p fixed).prog.body = (glob p fixed).prog.body := by
    funext called
    by_cases same : called = d
    · subst called
      simp only [cachedGlob]
      exact source_body.symm
    · exact if_neg same
  exact congrArg (fun body => {glob p fixed with prog := {(glob p fixed).prog with body := body}}) bodies

theorem run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (callInternal (glob p fixed) frame 30 d arguments [Aty]).run (.nil,initial) =
      (.ok (.val (.memRef rfl 4)),(.nil,after)) := by
  rw [←cachedGlob_eq p fixed]
  cases p <;> rfl

theorem inhabited (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (callInternal (glob p fixed) frame 30 d arguments [Aty]) ∧
    MemOK E seed.ty ((.nil : Locals E.layout []),after) ∧
    RValOK E after.heap.ty (.val (.memRef rfl 4) : RVal E.layout Aty) := by
  have checked := joint p fixed arguments seed.ty 30
  have actual := checked.2 (.nil,initial) ⟨entry_mem,trivial,trivial⟩
  rw [run] at actual
  exact ⟨checked.1,actual⟩

def huge : Vals E.layout [U] := .cons (.int (2^64) (by decide)) .nil
theorem huge_normalized : huge =
    (.cons (.int 18446744073709551616 (by decide)) .nil : Vals E.layout [U]) := rfl

def stopped : St E := {initial with heap := defaulted}

theorem panic_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (callInternal (glob p fixed) frame 30 d huge [Aty]).run (.nil,initial) =
      (.error (.revert (panicData .alloc)),(.nil,stopped)) := by
  rw [huge_normalized,←cachedGlob_eq p fixed]
  cases p <;> rfl

theorem timeout_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (callInternal (glob p fixed) frame 8 d arguments [Aty]).run (.nil,initial) =
      (.error .timeout,(.nil,stopped)) := by
  rw [←cachedGlob_eq p fixed]
  cases p <;> rfl

theorem halted_memory (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    MemOK E seed.ty ((.nil : Locals E.layout []),stopped) := by
  have actual := (joint p fixed huge seed.ty 30).2 (.nil,initial) ⟨entry_mem,trivial,trivial⟩
  rw [panic_run] at actual
  exact actual

theorem storage_default_refused : ¬ ZeroReady E (.bytes .storage) := by
  intro ready
  rcases ready.boundary with absent | location
  · cases absent
  · cases location

def caller : Locals E.layout [Aty,U] :=
  .cons (.memRef rfl 0) (.cons (.int 2 (by decide)) .nil)
def args : RConvArgs E [Aty,U] [U] :=
  .cons (.local (.there .here)) (by decide +kernel) .nil
def expression : RExpr E [Aty,U] Aty := .call d signature args

theorem caller_mem : MemOK E seed.ty (caller,initial) :=
  Preservation.relocalize entry_mem caller ⟨⟨Aty,rfl,rfl⟩,trivial,trivial⟩

theorem expression_joint (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (glob p fixed) frame 31 expression) ∧
    Hoare (MemOK E seed.ty) (evalE (glob p fixed) frame 31 expression)
      (fun v y => MemOK E seed.ty y ∧ RValOK E y.2.heap.ty v)
      (fun _ y => MemOK E seed.ty y) :=
  ready_body_expr_progress_and_memory
    (WholeProgram.from_elaborate resolution actual_elaboration (glob p fixed) rfl "Memory" [] (value_check p fixed))
    frame rfl d [U] [Aty] signature flatBody
    (by rw [show frame.contract = "Memory" from rfl,dispatch]; exact source_body)
    rfl rfl rfl rfl (fun τ member => by
      rcases List.mem_singleton.mp member with rfl
      exact .memory (.array _)) fragment args
    (.cons _ (.inl rfl) (.local _) .nil) seed.ty 30

theorem expression_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 31 expression).run (caller,initial) =
      (.ok (.val (.memRef rfl 4)),(caller,after)) := by
  rw [←cachedGlob_eq p fixed]
  cases p <;> rfl

theorem caller_restored (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (glob p fixed) frame 31 expression) ∧
    MemOK E seed.ty (caller,after) ∧
    RValOK E after.heap.ty (.val (.memRef rfl 4) : RVal E.layout Aty) := by
  have checked := expression_joint p fixed
  have actual := checked.2 (caller,initial) caller_mem
  rw [expression_run] at actual
  exact ⟨checked.1,actual⟩

theorem old_checker_refused (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    WholeProgram.checkFunctions resolution (glob p fixed) "Memory" = false := by
  change WholeProgram.check resolution (glob p fixed) "Memory" [d] = false
  unfold WholeProgram.check
  simp only [List.all_cons,List.all_nil]
  unfold WholeProgram.checkBody
  have hb : (glob p fixed).prog.body d = some flatBody := source_body
  simp only [signature,dispatch,hb]
  rfl

#print axioms panic_run
#print axioms timeout_run
#print axioms halted_memory
#print axioms expression_joint
#print axioms expression_run
#print axioms caller_restored
#print axioms storage_default_refused
#print axioms old_checker_refused

#print axioms actual_elaboration
#print axioms joint
#print axioms run
#print axioms inhabited
end Solidity.Source.Progress.ReadyBodyControls
