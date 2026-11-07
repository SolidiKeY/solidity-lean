import Solidity.Source.Preservation.ReferenceReturns
import Solidity.Source.Preservation.AllocatingControls

/-! An actual intrinsic return-only call with a memory parameter and two
reference results. Return-slot defaults allocate objects 1 and 2; the body
returns parameter object 0 and a fresh object 3. No elaboration or compiler
certificate is claimed for this hand-built resolved fixture. -/
namespace Solidity.Source.Preservation.ReferenceReturnControls
open EM Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls

abbrev ps : List STy := [.bytes .memory]
abbrev rs : List STy := [.bytes .memory,.bytes .memory]
abbrev Δ : RCtx := rs.reverseAux (ps.reverseAux [])
def results : RConvArgs E Δ rs :=
  .cons (.local (.there (.there .here))) (by decide +kernel)
    (.cons (.newArray (τ := .bytes .memory) rfl (.const (Q.ofInt 2)) (by decide +kernel))
      (by decide +kernel) .nil)
def body : RBody E := returningBody ps rs results
def globals (pipeline : Roadmap.Pipeline) : Glob E :=
  {Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.globals pipeline with
    prog := {program with body := fun _ => some body}}
def d : Decl := ⟨.function, "returnRefs", none, true,
  .function (.ident "returnRefs")
    (.cons (.param (.elem .bytes) (some .memory) (some "p")) .nil)
    none none .nil false none
    (.cons (.param (.elem .bytes) (some .memory) none)
      (.cons (.param (.elem .bytes) (some .memory) none) .nil)) .none⟩
def parameters : Vals E.layout ps := .cons (.memRef rfl 0) .nil
def after : St E := {state with heap :=
  (((seed.alloc ⟨.bytes .memory,.bytes []⟩).1.alloc ⟨.bytes .memory,.bytes []⟩).1.alloc
    ⟨.bytes .memory,.bytes [0,0]⟩).1}
def returned : RVal E.layout (STy.ret rs) :=
  .tuple (.cons (.val (.memRef rfl 0)) (.cons (.val (.memRef rfl 3)) .nil))

theorem results_admitted : ExactArgs (fun _ => False) results :=
  .cons _ (.local _) (.cons _ (.newArray rfl _ (.value trivial trivial)) .nil)
theorem calls (pipeline : Roadmap.Pipeline) : CallsOK (fun _ => False) (globals pipeline) frame.contract := by
  intro d ps rs signature impossible
  cases impossible

theorem run (pipeline : Roadmap.Pipeline) :
    (callInternal (globals pipeline) frame 12 d parameters rs).run (.nil,state) =
      (.ok returned, (.nil,after)) := rfl

theorem caller_run (pipeline : Roadmap.Pipeline) :
    (sub .nil (callInternal (globals pipeline) frame 12 d parameters rs)).run (small,state) =
      (.ok (returned,.nil), (small,after)) := rfl

theorem parameter_valid : RValsOK E seed.ty parameters.toR :=
  ⟨⟨.bytes .memory,rfl,rfl⟩,trivial⟩
theorem initial_mem : MemOK E seed.ty ((.nil : Locals E.layout []), state) :=
  relocalize Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.initial_mem.1 .nil trivial

theorem escaped_valid (pipeline : Roadmap.Pipeline) :
    MemOK E seed.ty ((.nil : Locals E.layout []), after) ∧ RValOK E after.heap.ty returned := by
  have actual := call_returning_mem (calls pipeline) frame rfl d ps rs results results_admitted
    rfl parameters seed.ty 12 (.nil,state) ⟨initial_mem,parameter_valid⟩
  rw [run] at actual
  exact actual

theorem caller_valid (pipeline : Roadmap.Pipeline) : MemOK E seed.ty (small,after) :=
  relocalize (escaped_valid pipeline).1 small
    (LocalsOK.mono (escaped_valid pipeline).1.le small
      Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.initial_mem.1.1.2)

theorem low_horizon (pipeline : Roadmap.Pipeline) :
    (callInternal (globals pipeline) frame 1 d parameters rs).run (.nil,state) =
      (.error .timeout, (.nil,state)) := rfl

theorem allocations_and_alias : after.heap.next = 4 ∧
    after.heap.get 0 = seed.get 0 ∧ after.heap.get 1 = some ⟨.bytes .memory,.bytes []⟩ ∧
    after.heap.get 2 = some ⟨.bytes .memory,.bytes []⟩ ∧
    after.heap.get 3 = some ⟨.bytes .memory,.bytes [0,0]⟩ := ⟨rfl,rfl,rfl,rfl,rfl⟩


theorem signature : d.fnSig E = some (ps,rs) := rfl
def actualArgs : RConvArgs E Γ ps := .cons (.local (.there .here)) (by decide +kernel) .nil
def expression : RExpr E Γ (STy.ret rs) := .call d signature actualArgs

theorem expression_run (pipeline : Roadmap.Pipeline) :
    (evalE (globals pipeline) frame 14 expression).run (small,state) =
      (.ok returned, (small,after)) := rfl

theorem expression_preserved (pipeline : Roadmap.Pipeline) :
    MemOK E seed.ty (small,after) ∧ RValOK E after.heap.ty returned := by
  have actual := eval_call_returning_mem (calls pipeline) frame rfl d ps rs signature results
    results_admitted rfl actualArgs (.cons _ (.local _) .nil) seed.ty 13
    (small,state) Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.initial_mem.1
  have observation : (evalE (globals pipeline) frame (13+1) (.call d signature actualArgs)).run
      (small,state) = (.ok returned,(small,after)) := expression_run pipeline
  rw [observation] at actual
  exact actual


/-- The normalized literal denotes exactly the original allocation bound. -/
theorem panic_literal_exact : Q.ofInt 18446744073709551616 = Q.ofInt (2^64) := by decide +kernel

def panicResults : RConvArgs E Δ rs :=
  .cons (.local (.there (.there .here))) (by decide +kernel)
    (.cons (.newArray (τ := .bytes .memory) rfl (.const (Q.ofInt 18446744073709551616)) (by decide +kernel))
      (by decide +kernel) .nil)
def panicGlobals (pipeline : Roadmap.Pipeline) : Glob E :=
  {Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.globals pipeline with
    prog := {program with body := fun _ => some (returningBody ps rs panicResults)}}
def panicAfter : St E := {state with heap :=
  ((seed.alloc ⟨.bytes .memory,.bytes []⟩).1.alloc ⟨.bytes .memory,.bytes []⟩).1}

theorem panic_admitted : ExactArgs (fun _ => False) panicResults :=
  .cons _ (.local _) (.cons _ (.newArray rfl _ (.value trivial trivial)) .nil)
def defaultLocals : Locals E.layout Δ :=
  .cons (.memRef rfl 2) (.cons (.memRef rfl 1) (.cons (.memRef rfl 0) .nil))
def panicTail (pipeline : Roadmap.Pipeline) : EM E [] (RVal E.layout (STy.ret rs)) := do
  let last ← runMods (panicGlobals pipeline) {frame with checked := true} 11
    (returningBody ps rs panicResults) [] defaultLocals
  let out ← lift (retVals last 0 rs)
  pure (mkRet rs out)

theorem panic_selected (pipeline : Roadmap.Pipeline) :
    (panicGlobals pipeline).prog.body ((panicGlobals pipeline).dispatchFn frame.contract d) =
      some (returningBody ps rs panicResults) := rfl

theorem panic_run (pipeline : Roadmap.Pipeline) :
    (callInternal (panicGlobals pipeline) frame 12 d parameters rs).run (.nil,state) =
      (.error (.revert (panicData .alloc)), (.nil,panicAfter)) := by
  calc
    _ = (panicTail pipeline).run (.nil,panicAfter) := rfl
    _ = _ := rfl

theorem panic_preserved (pipeline : Roadmap.Pipeline) :
    MemOK E seed.ty ((.nil : Locals E.layout []),panicAfter) ∧ panicAfter.heap.next = 3 := by
  have admittedCalls : CallsOK (fun _ => False) (panicGlobals pipeline) frame.contract := by
    intro d ps rs signature impossible
    cases impossible
  have actual := call_returning_mem admittedCalls frame rfl d ps rs panicResults panic_admitted
    (panic_selected pipeline) parameters seed.ty 12 (.nil,state) ⟨initial_mem,parameter_valid⟩
  rw [panic_run] at actual
  exact ⟨actual,rfl⟩

#print axioms escaped_valid
#print axioms caller_valid
#print axioms run
#print axioms expression_preserved
#print axioms panic_preserved
end Solidity.Source.Preservation.ReferenceReturnControls
