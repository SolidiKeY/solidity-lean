import Solidity.Source.Progress.AllocationBodyCalls
import Solidity.Lowering.P9.InferenceCuts
import Solidity.Roadmap.Controls

/-! Source-elaborated memory-call controls for allocation-parent prefixes.
Both caller and callee use the actual selected body. No target/compiler
correspondence or general memory-call graph is asserted. -/
namespace Solidity.Source.Progress.AllocationBodyCallControls
open EM Solidity.Lowering.P9

def bytesType : Syn .typeName := .elem .bytes
def uintType : Syn .typeName := .elem (.int false 256 (by decide))
def structPart : Syn (.part false) := .struct "Pair" (.structMember bytesType "old")
  (.cons (.structMember bytesType "fresh") .nil)
def freshSyntax : Syn .expr := .call (.new bytesType) (.positional (.cons (.ident "n") .nil))
def parentSyntax : Syn .expr := .call (.ident "Pair")
  (.positional (.cons (.ident "a") (.cons freshSyntax .nil)))
def function : Syn (.part false) := .function (.ident "keep")
  (.cons (.param bytesType (some .memory) (some "a"))
    (.cons (.param uintType none (some "n")) .nil))
  (some .priv) none .nil false none (.cons (.param bytesType (some .memory) none) .nil)
  (.some (.block (.cons (.stmtItem (.simpleStmt (.exprStmt parentSyntax)))
    (.cons (.stmtItem (.returnStmt (.some (.ident "a")))) .nil))))
def unit : Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons structPart (.cons function .nil))) .nil)
def resolution := Source.resolveUnit {pipeline:=.legacy} unit
abbrev E := resolution.env
abbrev Bty : STy := .bytes .memory
abbrev U : STy := .int .u256
abbrev ps : List STy := [Bty,U]
abbrev rs : List STy := [Bty]
abbrev Δ : RCtx := [Bty,U,Bty]
def dn : DeclName := ⟨some "C","Pair"⟩
def d : Decl := ⟨.function,"keep",some "C",false,function⟩
def sourceFrame := (d.frame? E).get (by rfl)
def inferred := (ItemsD.infer (sourceFrame.ctx E d.scope) sourceFrame.locals sourceFrame.body).get (by rfl)
def inferredBody := RBody.ofDerivation sourceFrame inferred.2 []

theorem fields_typed : (E.structFields dn .memory).map (·.map Prod.snd) = some [Bty,Bty] := rfl
def parentArgs : RConvArgs E Δ [Bty,Bty] :=
  .cons (.local (.there (.there .here))) rfl
    (.cons (.newArray (τ:=Bty) rfl (.local (.there .here)) rfl) rfl .nil)
def parent : RExpr E Δ (.struct .memory dn) := .structNew fields_typed parentArgs
def flatBody : RBody E where
  ps:=ps;rs:=rs;inModifier:=false;locals:=Δ;out:=Δ
  items:=.stmt (.expr parent) (.stmt (.retVal rfl (.local (.there (.there .here))) rfl) .nil)

theorem signature : d.fnSig E = some (ps,rs) := rfl
theorem source_frame : d.frame? E = some sourceFrame := rfl
theorem source_inferred :
    ItemsD.infer (sourceFrame.ctx E d.scope) sourceFrame.locals sourceFrame.body = some inferred := rfl
theorem body_flat : inferredBody = flatBody := rfl

#print axioms fields_typed
#print axioms signature
#print axioms source_frame
#print axioms source_inferred
#print axioms body_flat

theorem invs : d.modInvs.invList = [] := by
  rw [show d.modInvs = .nil from rfl,Syn.invList]
theorem body_exists : (Source.elabBody E d).isSome = true :=
  InferenceCuts.body_some E d sourceFrame source_frame (by rw [source_inferred];rfl) invs
theorem source_body : (Source.progOf E).body d = some flatBody := by
  have hm : (Source.elabMods E d sourceFrame d.modInvs.invList).map Subtype.val = some [] := by
    rw [invs,Source.elabMods];rfl
  simp only [Source.progOf,Source.elabBody,source_frame,source_inferred]
  cases actual : Source.elabMods E d sourceFrame d.modInvs.invList with
  | none => rw [actual] at hm;cases hm
  | some value =>
    rcases value with ⟨mods,hmods⟩
    simp only [actual,Option.map_some,Option.some.injEq] at hm
    subst mods
    exact congrArg some body_flat
theorem base_arguments : (Source.elabBaseArgs E "C").isSome = true :=
  InferenceCuts.base_some E "C" (by rw [show E.inheritOf "C" = .nil from rfl,Syn.inheritList]) rfl
theorem elaborates : Source.elaborates E = true := by
  change ((((Source.elabBody E d).isSome && true) && true) &&
    ((Source.elabBaseArgs E "C").isSome && true)) = true
  rw [body_exists,base_arguments]
  rfl
theorem actual_elaboration : (Source.elaborate resolution).isSome = true := by
  simp only [Source.elaborate,elaborates,↓reduceIte,Option.isSome_some]

def globals (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) : Glob E :=
  ⟨Source.progOf E,p,fixed,fun _=>⟨0,by decide⟩,fun _ _=>true,
    fun _=>.answer (.success []),⟨0,by decide⟩⟩
def frame : Fr where
  this := ⟨17,by decide⟩
  sender := ⟨19,by decide⟩
  value := ⟨0,by decide⟩
  static := false
  contract := "C"

theorem local_functions : E.fnIn "C" d.name ps = [d] := by
  first | rfl | decide | omega | simp only

theorem dispatch (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (globals p fixed).dispatchFn "C" d = d := by
  unfold Glob.dispatchFn
  rw [signature]
  simp only [show E.linearize "C" = some ["C"] from rfl,Option.getD_some]
  change (if true then
    (List.findSome? (fun s=>List.find? (fun d'=>((globals p fixed).prog.body d').isSome)
      (E.fnIn s d.name ps)) ["C"]).getD d else d) = d
  simp only [ite_true,List.findSome?_cons,local_functions,List.find?_cons]
  rw [show (globals p fixed).prog.body d = some flatBody from source_body]
  rfl
theorem value_checked (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    WholeProgram.check resolution (globals p fixed) "C" [] = true := rfl
theorem declared : d ∈ WholeProgram.functions resolution := by
  change d ∈ [d]
  exact List.mem_cons_self
theorem parent_ready {A : Decl → Prop} : ReadyArgs A parentArgs :=
  .cons rfl (.inr rfl) (.local _)
    (.cons rfl (.inr rfl) (.newArray .bytes rfl (.local _)) .nil)
theorem admitted {A : Decl → Prop} : AllocationItems A rs false flatBody.items :=
  .expr (.structNew fields_typed parent_ready)
    (.ready (.stmt (.returnValue rfl rfl (.inr rfl) (.local _)) .nil))

def seed : Heap E.layout := (Heap.empty.alloc ⟨Bty,.bytes [42,77]⟩).1
def initial : St E :=
  {ex:=⟨⟨fun _=>Account.empty _⟩,Transient.empty,[]⟩,heap:=seed,events:=[],
   logs:=[(⟨17,by decide⟩,[9])],fnLocals:=⟨[.bool],.cons (.bool false) .nil⟩}
def defaulted : Heap E.layout := (seed.alloc ⟨Bty,.bytes []⟩).1
def childHeap : Heap E.layout := (defaulted.alloc ⟨Bty,.bytes [0,0]⟩).1
def fields : Data E.layout (.struct .memory dn) :=
  .struct (.cons (.val (.memRef rfl 0)) (.cons (.val (.memRef rfl 2)) .nil))
def reached : St E := {initial with heap:=(childHeap.alloc ⟨_,fields⟩).1}
def stopped : St E := {initial with heap:=defaulted}
def parameters : Vals E.layout ps := .cons (.memRef rfl 0) (.cons (.int 2 (by decide)) .nil)
def hugeParameters : Vals E.layout ps := .cons (.memRef rfl 0) (.cons (.int (2^64) (by decide)) .nil)
abbrev Γ : RCtx := [Bty,U,.bool]
def caller : Locals E.layout Γ := .cons (.memRef rfl 0) (.cons (.int 2 (by decide)) (.cons (.bool true) .nil))
def hugeCaller : Locals E.layout Γ := .cons (.memRef rfl 0)
  (.cons (.int (2^64) (by decide)) (.cons (.bool true) .nil))
def args : RConvArgs E Γ ps :=
  .cons (.local .here) rfl (.cons (.local (.there .here)) rfl .nil)
def expression : RExpr E Γ Bty := .call d signature args

theorem args_ready {A : Decl → Prop} : ReadyArgs A args :=
  .cons rfl (.inr rfl) (.local _) (.cons rfl (.inl rfl) (.local _) .nil)
theorem entry_mem : MemOK E seed.ty (L0 E,initial) := by
  have heap : HeapOK (E:=E) seed := HeapOK.empty.alloc (.bytes [42,77])
  have shape : HeapShaped seed := HeapShaped.empty.alloc trivial
  have inner : HeapInner seed := HeapInner.empty.alloc trivial
  exact ⟨⟨⟨heap,HeapTy.Le.refl _⟩,trivial⟩,shape,inner⟩
theorem caller_mem : MemOK E seed.ty (caller,initial) ∧ MemOK E seed.ty (hugeCaller,initial) :=
  ⟨Preservation.relocalize entry_mem caller ⟨⟨Bty,rfl,rfl⟩,⟨trivial,⟨trivial,trivial⟩⟩⟩,
    Preservation.relocalize entry_mem hugeCaller ⟨⟨Bty,rfl,rfl⟩,⟨trivial,⟨trivial,trivial⟩⟩⟩⟩
theorem parameters_ok : RValsOK E initial.heap.ty parameters.toR ∧ RValsOK E initial.heap.ty hugeParameters.toR :=
  ⟨⟨⟨Bty,rfl,rfl⟩,⟨trivial,trivial⟩⟩,⟨⟨Bty,rfl,rfl⟩,⟨trivial,trivial⟩⟩⟩

theorem checked_call (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (vs : Vals E.layout ps) (n : Nat) :
    NS (callInternal (globals p fixed) frame n d vs rs) ∧
    Hoare (fun y=>MemOK E seed.ty y ∧ RValsOK E y.2.heap.ty vs.toR)
      (callInternal (globals p fixed) frame n d vs rs)
      (fun v y=>MemOK E seed.ty y ∧ RValOK E y.2.heap.ty v) (fun _ y=>MemOK E seed.ty y) :=
  allocation_body_from_elaborate resolution actual_elaboration (globals p fixed) rfl "C" []
    (value_checked p fixed) frame rfl ps rs ⟨d,declared,signature⟩ flatBody
    (by rw [show frame.contract = "C" from rfl,dispatch];exact source_body)
    rfl rfl rfl rfl
    (fun τ member=>by simp only [List.mem_singleton] at member;subst τ;exact .memory .bytes)
    admitted vs seed.ty n

theorem checked_expression (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (globals p fixed) frame 22 expression) ∧
    Hoare (MemOK E seed.ty) (evalE (globals p fixed) frame 22 expression)
      (fun v y=>MemOK E seed.ty y ∧ RValOK E y.2.heap.ty v) (fun _ y=>MemOK E seed.ty y) :=
  allocation_body_expr_progress_and_memory
    (WholeProgram.from_elaborate resolution actual_elaboration (globals p fixed) rfl "C" [] (value_checked p fixed))
    frame rfl d ps rs signature flatBody
    (by rw [show frame.contract = "C" from rfl,dispatch];exact source_body)
    rfl rfl rfl rfl
    (fun τ member=>by simp only [List.mem_singleton] at member;subst τ;exact .memory .bytes)
    admitted args args_ready seed.ty 21

theorem call_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (callInternal (globals p fixed) frame 20 d parameters rs).run (L0 E,initial) =
      (.ok (.val (.memRef rfl 0)),(L0 E,reached)) := by
  have body : (globals p fixed).prog.body d = some flatBody := source_body
  rw [callInternal,show frame.contract = "C" from rfl,dispatch,body]
  cases p <;> rfl

theorem arguments_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalConvArgs (globals p fixed) frame 21 args).run (caller,initial) =
      (.ok parameters,(caller,initial)) := by
  simp only [args,evalConvArgs,Hoare.run_bind,evalE,convRV,↓reduceDIte,getV,pure_bind]
  rfl

theorem caller_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (globals p fixed) frame 22 expression).run (caller,initial) =
      (.ok (.val (.memRef rfl 0)),(caller,reached)) := by
  change (evalE (globals p fixed) frame 22 (.call d signature args)).run (caller,initial) = _
  rw [evalE,Hoare.run_bind,arguments_run]
  dsimp only
  rw [Hoare.run_bind]
  have inner : callInternal (plan := none) (calldataKnown := true) (globals p fixed) frame 21 d parameters rs (L0 E,initial) =
      (.ok (.val (.memRef rfl 0)),(L0 E,reached)) := by
    have body : (globals p fixed).prog.body d = some flatBody := source_body
    rw [callInternal,show frame.contract = "C" from rfl,dispatch,body]
    cases p <;> rfl
  simp only [EM.sub,ExceptT.run,ExceptT.mk,inner]
  rfl

theorem call_preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (callInternal (globals p fixed) frame 20 d parameters rs) ∧
    MemOK E seed.ty (L0 E,reached) ∧
    RValOK E reached.heap.ty (.val (.memRef rfl 0) : RVal E.layout Bty) := by
  have joint := checked_call p fixed parameters 20
  have actual := joint.2 (L0 E,initial) ⟨entry_mem,parameters_ok.1⟩
  rw [call_run] at actual
  exact ⟨joint.1,actual⟩

theorem caller_preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (globals p fixed) frame 22 expression) ∧
    MemOK E seed.ty (caller,reached) ∧
    RValOK E reached.heap.ty (.val (.memRef rfl 0) : RVal E.layout Bty) := by
  have actual := (checked_expression p fixed).2 (caller,initial) caller_mem.1
  rw [caller_run] at actual
  exact ⟨(checked_expression p fixed).1,actual⟩

theorem heap_and_frame :
    reached.heap.get 0 = seed.get 0 ∧ reached.heap.get 1 = some ⟨Bty,.bytes []⟩ ∧
    reached.heap.get 2 = some ⟨Bty,.bytes [0,0]⟩ ∧
    reached.heap.get 3 = some ⟨.struct .memory dn,fields⟩ ∧
    reached.heap.next = 4 ∧ reached.fnLocals = initial.fnLocals ∧ reached.logs = initial.logs :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem old_ready_refused : ¬ReadyItems (fun _=>False) rs false flatBody.items := by
  intro ready
  cases ready with
  | stmt head tail =>
    cases head with
    | value fragment _ => exact fragment
    | expr expression =>
      cases expression with
      | value fragment _ => exact fragment

#print axioms invs
#print axioms body_exists
#print axioms source_body
#print axioms base_arguments
#print axioms elaborates
#print axioms actual_elaboration
#print axioms local_functions
#print axioms dispatch
#print axioms value_checked
#print axioms declared
#print axioms parent_ready
#print axioms admitted
#print axioms args_ready
#print axioms entry_mem
#print axioms caller_mem
#print axioms parameters_ok
#print axioms checked_call
#print axioms checked_expression
#print axioms call_run
#print axioms arguments_run
#print axioms caller_run
#print axioms call_preserved
#print axioms caller_preserved
#print axioms heap_and_frame
#print axioms old_ready_refused

/-- Allocation panic keeps the callee's already-created return default. -/
def hugeCallee : Locals E.layout Δ :=
  .cons (.memRef rfl 1) (.cons (.int (2^64) (by decide)) (.cons (.memRef rfl 0) .nil))

theorem parent_panic (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (n : Nat) :
    (evalE (globals p fixed) {frame with checked:=true} (n+10) parent).run (hugeCallee,stopped) =
      (.error (.revert (panicData .alloc)),(hugeCallee,stopped)) := by
  first | rfl | decide | omega | simp only

theorem body_panic (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (n : Nat) :
    (runMods (globals p fixed) {frame with checked:=true} (n+13) flatBody [] hugeCallee).run (L0 E,stopped) =
      (.error (.revert (panicData .alloc)),(L0 E,stopped)) := by
  rw [runMods,Hoare.run_bind]
  have item : (execItems (globals p fixed) {frame with checked:=true} (n+12) flatBody.ps.length none
      flatBody.items hugeCallee).run (L0 E,stopped) =
      (.error (.revert (panicData .alloc)),(L0 E,stopped)) := by
    dsimp only [flatBody]
    rw [execItems,Hoare.run_bind]
    have statement : (execS (globals p fixed) {frame with checked:=true} (n+11) flatBody.ps.length none
        (.expr (R:=rs) (M:=false) (k:=⟨false,false⟩) parent) hugeCallee).run (L0 E,stopped) =
        (.error (.revert (panicData .alloc)),(L0 E,stopped)) := by
      rw [execS,Hoare.run_bind]
      simp only [EM.sub,ExceptT.run,ExceptT.mk]
      rfl
    dsimp only [flatBody] at statement
    rw [statement]
  rw [item]

theorem call_panic_at (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (n : Nat) :
    (callInternal (globals p fixed) frame (n+14) d hugeParameters rs).run (L0 E,initial) =
      (.error (.revert (panicData .alloc)),(L0 E,stopped)) := by
  have body : (globals p fixed).prog.body d = some flatBody := source_body
  rw [callInternal,show (globals p fixed).dispatchFn frame.contract d = d from dispatch p fixed,body,Hoare.run_bind]
  have zero : (zeroVals (n+13) rs (E:=E)).run (L0 E,initial) =
      (.ok (.cons (.memRef rfl 1) .nil),(L0 E,stopped)) := rfl
  rw [zero]
  dsimp only
  rw [dif_pos (show rs.reverseAux (ps.reverseAux []) = flatBody.locals from rfl),Hoare.run_bind]
  rw [show flatBody.mods = [] from rfl,
    show (Vals.cons (Val.memRef (τ:=Bty) rfl 1) .nil).onto (hugeParameters.onto (L0 E)) = hugeCallee from rfl,
    body_panic]

theorem call_panic (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (callInternal (globals p fixed) frame 20 d hugeParameters rs).run (L0 E,initial) =
      (.error (.revert (panicData .alloc)),(L0 E,stopped)) :=
  call_panic_at p fixed 6

theorem huge_arguments_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalConvArgs (globals p fixed) frame 21 args).run (hugeCaller,initial) =
      (.ok hugeParameters,(hugeCaller,initial)) := by
  simp only [args,evalConvArgs,Hoare.run_bind,evalE,convRV,↓reduceDIte,getV,pure_bind]
  rfl

theorem caller_panic (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (globals p fixed) frame 22 expression).run (hugeCaller,initial) =
      (.error (.revert (panicData .alloc)),(hugeCaller,stopped)) := by
  change (evalE (globals p fixed) frame 22 (.call d signature args)).run (hugeCaller,initial) = _
  rw [evalE,Hoare.run_bind,huge_arguments_run]
  dsimp only
  rw [Hoare.run_bind]
  have inner : callInternal (plan := none) (calldataKnown := true) (globals p fixed) frame 21 d hugeParameters rs (L0 E,initial) =
      (.error (.revert (panicData .alloc)),(L0 E,stopped)) := call_panic_at p fixed 7
  simp only [EM.sub,ExceptT.run,ExceptT.mk,inner]

theorem panic_preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    MemOK E seed.ty (L0 E,stopped) ∧ MemOK E seed.ty (hugeCaller,stopped) := by
  have internal := (checked_call p fixed hugeParameters 20).2
    (L0 E,initial) ⟨entry_mem,parameters_ok.2⟩
  have external := (checked_expression p fixed).2 (hugeCaller,initial) caller_mem.2
  rw [call_panic] at internal
  rw [caller_panic] at external
  exact ⟨internal,external⟩

theorem panic_heap_and_frame :
    stopped.heap.get 0 = seed.get 0 ∧ stopped.heap.get 1 = some ⟨Bty,.bytes []⟩ ∧
    stopped.heap.get 2 = none ∧ stopped.heap.next = 2 ∧
    stopped.fnLocals = initial.fnLocals ∧ stopped.logs = initial.logs :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem zero_horizon (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (callInternal (globals p fixed) frame 0 d parameters rs).run (L0 E,initial) =
      (.error .timeout,(L0 E,initial)) ∧
    (evalE (globals p fixed) frame 0 expression).run (caller,initial) =
      (.error .timeout,(caller,initial)) := ⟨rfl,rfl⟩

#print axioms parent_panic
#print axioms body_panic
#print axioms call_panic_at
#print axioms call_panic
#print axioms huge_arguments_run
#print axioms caller_panic
#print axioms panic_preserved
#print axioms panic_heap_and_frame
#print axioms zero_horizon

end Solidity.Source.Progress.AllocationBodyCallControls
