import Solidity.Roadmap.V16.SSCP2.NewAllocation
import Solidity.Roadmap.Controls

/-! Actual dynamic-new controls with a live caller memory reference.
These are evaluator and MemOK witnesses, not compiler/admission certificates. -/
namespace Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls
open Solidity.Source

def E : Env := ⟨[]⟩
abbrev Γ : RCtx := [.int .u256,.bytes .memory,.bool]
def seed : Heap E.layout := (Heap.empty.alloc ⟨.bytes .memory,.bytes [42,77]⟩).1

def state : St E :=
  {ex := ⟨⟨fun _ => Account.empty _⟩,Transient.empty,[]⟩,heap := seed,
   events := [],logs := [(⟨13,by decide⟩,[9])],fnLocals := ⟨[.bool],.cons (.bool false) .nil⟩}
def small : Locals E.layout Γ := .cons (.int 2 (by decide)) (.cons (.memRef rfl 0) (.cons (.bool true) .nil))
def huge : Locals E.layout Γ := .cons (.int (2^64) (by decide)) (.cons (.memRef rfl 0) (.cons (.bool true) .nil))
def frame : Fr := {this := ⟨41,by decide⟩,sender := ⟨37,by decide⟩,value := ⟨5,by decide⟩,static := false,contract := "fixture"}
def program : Program E := ⟨fun _ => none,fun _ => none,fun _ => [],fun _ => none,fun _ => [],fun _ => [],[]⟩
def globals (pipeline : Solidity.Roadmap.Pipeline) : Glob E :=
  ⟨program,pipeline,Solidity.Roadmap.Controls.toyFixed,fun _ => ⟨0,by decide⟩,fun _ _ => false,fun _ => .answer (.success []),⟨101,by decide⟩⟩
def expression : RExpr E Γ (.array .memory .bool none) := .newArray rfl (.local .here) rfl
def zeros : Data E.layout (.array .memory .bool none) := .array 2 (fun _ h => nomatch h) (fun _ => .val (.bool false))
def after : St E := {state with heap := (seed.alloc ⟨.array .memory .bool none,zeros⟩).1}

theorem initial_mem : Solidity.Source.MemOK Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.E Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.seed.ty (Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.small,Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.state) ∧ Solidity.Source.MemOK Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.E Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.seed.ty (Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.huge,Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.state) := by
  have heap : Solidity.Source.HeapOK (E := Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.E) Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.seed := Solidity.Source.HeapOK.empty.alloc (.bytes [42,77])
  have shaped : Solidity.Source.HeapShaped Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.seed := Solidity.Source.HeapShaped.empty.alloc trivial
  have inner : Solidity.Source.HeapInner Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.seed := Solidity.Source.HeapInner.empty.alloc trivial
  have reference : (Solidity.Source.Val.memRef (D := Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.E.layout) (τ := .bytes .memory) rfl 0).RefOK Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.E Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.seed.ty := ⟨.bytes .memory,rfl,rfl⟩
  exact ⟨⟨⟨⟨heap,Solidity.Source.HeapTy.Le.refl _⟩,trivial,reference,trivial,trivial⟩,shaped,inner⟩,⟨⟨⟨heap,Solidity.Source.HeapTy.Le.refl _⟩,trivial,reference,trivial,trivial⟩,shaped,inner⟩⟩

theorem runs : ∀ pipeline : Solidity.Roadmap.Pipeline, (Solidity.Source.evalE (Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.globals pipeline) Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.frame 2 Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.expression).run (Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.small,Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.state) = (.ok (.val (.memRef rfl 1)),(Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.small,Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.after)) ∧ (Solidity.Source.evalE (Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.globals pipeline) Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.frame 2 Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.expression).run (Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.huge,Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.state) = (.error (.revert (Solidity.Source.panicData .alloc)),(Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.huge,Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.state)) := by
  intro pipeline
  exact ⟨rfl,rfl⟩

def refusedState : St E := {state with heap := (seed.alloc ⟨.bytes .storage,.bytes [0,0]⟩).1}

theorem preserved : ∀ _pipeline : Solidity.Roadmap.Pipeline, Solidity.Source.MemOK Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.E Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.seed.ty (Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.small,Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.after) ∧ Solidity.Source.RValOK Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.E Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.after.heap.ty (Solidity.Source.RVal.val (τ := .array .memory .bool none) (.memRef rfl 1)) ∧ Solidity.Source.MemOK Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.E Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.seed.ty (Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.huge,Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.state) := by
  intro pipeline
  have actual := Solidity.Roadmap.V16.SSCP2.NewAllocation.local_new_mem Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.E Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.Γ (Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.globals pipeline) Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.frame 0 Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.seed.ty (.array .memory .bool none) rfl .here
  have success := actual (Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.small,Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.state) Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.initial_mem.1
  have failure := actual (Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.huge,Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.state) Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.initial_mem.2
  exact ⟨success.1,success.2,failure⟩

theorem refusals : (Solidity.Source.newData (D := Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.E.layout) (.array .memory (.array .memory .bool none) none) 2 : Solidity.Source.R (Solidity.Source.Data Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.E.layout (.array .memory (.array .memory .bool none) none))) = .error (.stuck "new of this element type") ∧ ((Solidity.Source.EM.lift (E := Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.E) (Γ := Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.Γ) (Solidity.Source.newData (D := Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.E.layout) (.bytes .storage) 2)) >>= fun (x : Solidity.Source.Data Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.E.layout (.bytes .storage)) => Solidity.Source.allocRef (E := Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.E) (Γ := Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.Γ) x).run (Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.small,Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.state) = (.error (.stuck "memory reference type"),(Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.small,Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.refusedState)) ∧ Solidity.Source.STy.newable (.array .memory (.array .memory .bool none) none) = false := by
  exact ⟨rfl,rfl,rfl⟩

theorem frame_observations : Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.after.heap.get 0 = Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.seed.get 0 ∧ Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.after.heap.get 1 = some ⟨.array .memory .bool none,Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.zeros⟩ ∧ Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.after.heap.next = 2 ∧ Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.small.get (.there .here) = .memRef rfl 0 ∧ {Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.after with heap := Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.state.heap} = Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.state := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem wrong_reference : ¬ Solidity.Source.RValOK Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.E Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.after.heap.ty (Solidity.Source.RVal.val (τ := .array .memory .bool none) (.memRef rfl 0)) := by
  intro wrong
  obtain ⟨σ,cell,shape⟩ := wrong
  have old : Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.after.heap.ty 0 = some (.bytes .memory) := rfl
  rw [old] at cell
  have same := Option.some.inj cell
  subst σ
  cases shape

theorem wrong_output : (Solidity.Source.evalE (Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.globals .legacy) Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.frame 2 Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.expression).run (Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.small,Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.state) ≠ (.ok (.val (.memRef rfl 0)),(Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.small,Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.after)) ∧ Solidity.Source.panicData .alloc ≠ Solidity.Source.panicData .index ∧ Solidity.Source.panicData .alloc ≠ [] := by
  refine ⟨?_,by decide +kernel,by decide +kernel⟩
  intro wrong
  have result := congrArg Prod.fst ((Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.runs .legacy).1.symm.trans wrong)
  cases result

theorem refused_mem : Solidity.Source.MemOK Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.E Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.seed.ty (Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.small,Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.refusedState) ∧ Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.refusedState.heap.next = 2 := by
  have actual := Solidity.Roadmap.V16.SSCP2.NewAllocation.allocation_mem Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.E Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.Γ Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.seed.ty (.bytes .storage) 2
  exact ⟨actual (Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.small,Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.state) Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.initial_mem.1,rfl⟩

theorem low_fuel : ∀ pipeline : Solidity.Roadmap.Pipeline, (Solidity.Source.evalE (Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.globals pipeline) Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.frame 0 Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.expression).run (Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.small,Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.state) = (.error .timeout,(Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.small,Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.state)) ∧ (Solidity.Source.evalE (Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.globals pipeline) Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.frame 1 Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.expression).run (Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.small,Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.state) = (.error .timeout,(Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.small,Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.state)) := by
  intro pipeline
  exact ⟨rfl,rfl⟩

/-- info: 'Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.initial_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms initial_mem

/-- info: 'Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms runs

/-- info: 'Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms preserved

/-- info: 'Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.refusals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms refusals

/-- info: 'Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.frame_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms frame_observations

/-- info: 'Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.wrong_reference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_reference

/-- info: 'Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.wrong_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_output

/-- info: 'Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.refused_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms refused_mem

/-- info: 'Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls.low_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms low_fuel
end Solidity.Roadmap.V16.SSCP2.NewAllocation.Controls
