import Solidity.Source.Preservation.MemoryBodyControls

/-! Conditional memory statements over inhabited runtime inputs. Branch selection
keeps pointer rebinding distinct from block-local restoration; a skipped bounds
failure is not executed. These are source, not compiler or frontend controls. -/
namespace Solidity.Source.Preservation.MemoryBranchControls
open EM MemoryBodyControls

def locals (flag : Bool) : Locals E.layout Γ := .cons (.memRef rfl 0)
  (.cons (.memRef rfl 0) (.cons (.int 42 (by decide)) (.cons (.bool flag) .nil)))
def condition : RExpr E Γ .bool := .local (.there (.there (.there .here)))
def replacement : RExpr E Γ Aty := .assign (.local .here)
  (.newArray (τ := Aty) rfl (.const (Q.ofInt 2)) (by decide +kernel))
def alternative : RStmt E [] false .body Γ Γ := .ifElse condition scopedBody (.expr replacement)
def rebound : Locals E.layout Γ := .cons (.memRef rfl 1)
  (.cons (.memRef rfl 0) (.cons (.int 42 (by decide)) (.cons (.bool false) .nil)))
def replaced : St E := {initial with heap := (seed.alloc ⟨Aty,fresh⟩).1}

theorem admitted : MemoryStmt (fun _ => False) [] false alternative :=
  .ifElse (.base (.local _)) scope_admitted
    (.expr (.rebind _ (.newArray rfl _ (.value trivial trivial))))

theorem yes_run (p : Roadmap.Pipeline) :
    (execS (glob p) frame 12 0 none alternative (locals true)).run (.nil,initial) =
      (.ok (.normal (locals true)),(.nil,scopeAfter)) := rfl

theorem no_run (p : Roadmap.Pipeline) :
    (execS (glob p) frame 12 0 none alternative (locals false)).run (.nil,initial) =
      (.ok (.normal rebound),(.nil,replaced)) := rfl

theorem entry_mem (flag : Bool) : MemOK E seed.ty (locals flag,initial) :=
  relocalize initial_mem (locals flag)
    ⟨initial_mem.1.2.1,initial_mem.1.2.2.1,trivial,trivial,trivial⟩

theorem branch_preserved (p : Roadmap.Pipeline) :
    (MemOK E seed.ty ((.nil : Locals E.layout []),scopeAfter) ∧
      LocalsOK E scopeAfter.heap.ty (locals true)) ∧
    (MemOK E seed.ty ((.nil : Locals E.layout []),replaced) ∧
      LocalsOK E replaced.heap.ty rebound) := by
  have entry (b : Bool) : MemOK E seed.ty ((.nil : Locals E.layout []),initial) ∧
      LocalsOK E initial.heap.ty (locals b) :=
    ⟨relocalize (entry_mem b) .nil trivial,(entry_mem b).1.2⟩
  have yes := (memory_body_at (calls p) 12).stmt frame rfl 0 none alternative admitted
    (locals true) seed.ty (.nil,initial) (entry true)
  have no := (memory_body_at (calls p) 12).stmt frame rfl 0 none alternative admitted
    (locals false) seed.ty (.nil,initial) (entry false)
  rw [yes_run] at yes
  rw [no_run] at no
  exact ⟨yes,no⟩

def badWrite : RExpr E Γ U := .assign
  (.indexArray (.local (Idx.here : Idx Γ Aty)) (by decide)
    (.const (Q.ofInt 1)) (by decide +kernel)) (.local (.there (.there .here)))
def guarded : RStmt E [] false .body Γ Γ := .ifThen condition (.expr badWrite)

theorem guarded_admitted : MemoryStmt (fun _ => False) [] false guarded :=
  .ifThen (.base (.local _))
    (.expr (.arrayWrite _ rfl (.local _) (.value trivial trivial) (.local _)))

theorem skip_run (p : Roadmap.Pipeline) :
    (execS (glob p) frame 12 0 none guarded (locals false)).run (.nil,initial) =
      (.ok (.normal (locals false)),(.nil,initial)) := rfl

theorem bounds_run (p : Roadmap.Pipeline) :
    (execS (glob p) frame 12 0 none guarded (locals true)).run (.nil,initial) =
      (.error (.revert (panicData .index)),(.nil,initial)) := rfl

theorem bounds_preserved (p : Roadmap.Pipeline) :
    MemOK E seed.ty ((.nil : Locals E.layout []),initial) := by
  have actual := (memory_body_at (calls p) 12).stmt frame rfl 0 none guarded guarded_admitted
    (locals true) seed.ty (.nil,initial)
    ⟨relocalize (entry_mem true) .nil trivial,(entry_mem true).1.2⟩
  rw [bounds_run] at actual
  exact actual

def effectful : RStmt E [] false .body Γ Γ := .ifThen
  (.assign (.local (.there (.there (.there .here)))) (.bool true)) scopedBody

theorem effectful_admitted : MemoryStmt (fun _ => False) [] false effectful :=
  .ifThen (.rebind _ (.value trivial trivial)) scope_admitted

theorem effectful_run (p : Roadmap.Pipeline) :
    (execS (glob p) frame 12 0 none effectful (locals false)).run (.nil,initial) =
      (.ok (.normal (locals true)),(.nil,scopeAfter)) := rfl

theorem effectful_preserved (p : Roadmap.Pipeline) :
    MemOK E seed.ty ((.nil : Locals E.layout []),scopeAfter) ∧
      LocalsOK E scopeAfter.heap.ty (locals true) := by
  have actual := (memory_body_at (calls p) 12).stmt frame rfl 0 none effectful effectful_admitted
    (locals false) seed.ty (.nil,initial)
    ⟨relocalize (entry_mem false) .nil trivial,(entry_mem false).1.2⟩
  rw [effectful_run] at actual
  exact actual

#print axioms effectful_preserved
#print axioms effectful_run
#print axioms branch_preserved
#print axioms bounds_preserved
#print axioms yes_run
#print axioms bounds_run
end Solidity.Source.Preservation.MemoryBranchControls
