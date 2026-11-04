import Solidity.Source.Progress.ReadyRebinding
import Solidity.Source.Preservation.MemoryBodyControls

/-! Direct intrinsic body/program controls, not an elaborated unit. A parameter
is rebound to fresh object2 while a second parameter returns old object0. The
actual call restores caller locals/function locals and retains both allocations. -/
namespace Solidity.Source.Progress.ReadyRebindingControls
open EM Preservation.MemoryBodyControls

def rebindingBody : RBody E := {body with
  items := .stmt (.expr rebind) (.stmt (.retTuple results) .nil)}
def rebindingProgram : Program E := {program with body := fun _ => some rebindingBody}
def globals (p : Roadmap.Pipeline) : Glob E := {glob p with prog := rebindingProgram}
def reached : St E := {initial with heap := (defaulted.alloc ⟨Aty,fresh⟩).1}

theorem calls_ready (p : Roadmap.Pipeline) : CallsOK (fun _ => False) (globals p) frame.contract := by
  intro d ps rs signature impossible
  cases impossible

theorem prefix_ready : RebindingItems (fun _ => False) rs false rebindingBody.items :=
  .rebind aIndex (.inr rfl) (.newArray (.array U rfl rfl) _ (.value trivial trivial))
    (.ready (.stmt (.returns (.cons _ (.inr rfl) (.local _) .nil)) .nil))

theorem args_ready : ReadyArgs (fun _ => False) args :=
  .cons _ (.inr rfl) (.local _) (.cons _ (.inr rfl) (.local _)
    (.cons _ (.inl rfl) (.local _) .nil))

theorem call_progress (p : Roadmap.Pipeline) (n : Nat) :
    NS (callInternal (globals p) frame n d parameters rs) :=
  call_rebinding_body_ns (calls_ready p) frame rfl d ps rs rebindingBody rfl rfl rfl rfl rfl
    (fun τ member => by simp only [rs,List.mem_singleton] at member; subst τ; exact .memory (.array _))
    prefix_ready parameters n

theorem call_run (p : Roadmap.Pipeline) :
    (callInternal (globals p) frame 20 d parameters rs).run (.nil,initial) =
      (.ok (.val (.memRef rfl 0)),(.nil,reached)) := rfl

theorem caller_run (p : Roadmap.Pipeline) :
    (evalE (globals p) frame 22 expression).run (caller,initial) =
      (.ok (.val (.memRef rfl 0)),(caller,reached)) := rfl

theorem caller_joint (p : Roadmap.Pipeline) :
    NS (evalE (globals p) frame 22 expression) ∧
    MemOK E seed.ty (caller,reached) ∧
    RValOK E reached.heap.ty (.val (τ := Aty) (.memRef rfl 0)) := by
  have joint := rebinding_body_expr_progress_and_memory (calls_ready p) frame rfl d ps rs signature
    rebindingBody rfl rfl rfl rfl rfl
    (fun τ member => by simp only [rs,List.mem_singleton] at member; subst τ; exact .memory (.array _))
    prefix_ready args args_ready seed.ty 21
  have actual := joint.2 (caller,initial) initial_mem
  have observed : (evalE (globals p) frame (21+1) (.call d signature args)).run (caller,initial) =
      (.ok (.val (.memRef rfl 0)),(caller,reached)) := caller_run p
  rw [observed] at actual
  exact ⟨joint.1,actual⟩

def entryLocals : Locals E.layout Δ := .cons (.memRef rfl 1)
  (.cons (.int 42 (by decide)) (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil)))
def entered : St E := {initial with heap := defaulted}

theorem local_rebind (p : Roadmap.Pipeline) :
    (evalE (globals p) frame 5 rebind).run (entryLocals,entered) =
      (.ok (.val (.memRef rfl 2)),(entryLocals.set aIndex (.memRef rfl 2),reached)) := rfl

theorem different_aliases :
    (entryLocals.set aIndex (.memRef rfl 2)).get aIndex = .memRef rfl 2 ∧
    (entryLocals.set aIndex (.memRef rfl 2)).get bIndex = .memRef rfl 0 ∧
    caller.get (.here : Idx Γ Aty) = .memRef rfl 0 := ⟨rfl,rfl,rfl⟩

theorem persistent_growth : reached.heap.next = 3 ∧ reached.heap.get 0 = seed.get 0 ∧
    reached.heap.get 2 = some ⟨Aty,fresh⟩ ∧ reached.fnLocals = initial.fnLocals := ⟨rfl,rfl,rfl,rfl⟩

theorem old_alias_read :
    (readLoc frame (.mem (τ := U) 0 0) : EM E [] _).run (.nil,reached) =
      (.ok (.int 7 (by decide)),(.nil,reached)) := rfl

theorem fresh_read :
    (readLoc frame (.mem (τ := U) 2 0) : EM E [] _).run (.nil,reached) =
      (.ok (.int 0 (by decide)),(.nil,reached)) := rfl

theorem low_horizon (p : Roadmap.Pipeline) :
    (evalE (globals p) frame 0 expression).run (caller,initial) =
      (.error .timeout,(caller,initial)) := rfl

theorem old_ready_refuses : ¬ ReadyExpr (fun _ => False) rebind := by
  intro ready
  cases ready with
  | value fragment _ => cases fragment.2.2

theorem calldata_excluded : ¬ PlainResultType (.bytes .calldata) := by
  intro plain
  rcases plain with value | memory
  · cases value
  · cases memory

def allocationFailure : RExpr E Δ Aty := .assign (.local aIndex)
  (.newArray (τ := Aty) rfl (.const (Q.ofInt (2^64))) (by decide))

theorem allocation_failure_progress (p : Roadmap.Pipeline) (n : Nat) :
    NS (evalE (globals p) frame n allocationFailure) :=
  eval_ready_rebind_ns (calls_ready p) frame rfl n aIndex _ (.inr rfl)
    (.newArray (.array U rfl rfl) _ (.value trivial trivial))

theorem allocation_failure_run (p : Roadmap.Pipeline) :
    (evalE (globals p) frame 5 allocationFailure).run (entryLocals,entered) =
      (.error (.revert (panicData .alloc)),(entryLocals,entered)) := rfl

#print axioms allocation_failure_progress
#print axioms allocation_failure_run
#print axioms prefix_ready
#print axioms call_progress
#print axioms call_run
#print axioms caller_joint
#print axioms local_rebind
#print axioms different_aliases
#print axioms persistent_growth
#print axioms old_alias_read
#print axioms fresh_read
#print axioms low_horizon
#print axioms old_ready_refuses
#print axioms calldata_excluded
end Solidity.Source.Progress.ReadyRebindingControls
