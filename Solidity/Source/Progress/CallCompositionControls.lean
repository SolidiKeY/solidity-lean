import Solidity.Source.Progress.CallComposition
import Solidity.Source.Progress.ReadyCatalogueControls

/-! Intrinsic nested calls over an actual elaborated memory-identity unit.
A fresh argument escapes through two alias-returning calls; earlier argument
references survive the later nested call. Both source evaluator pipelines keep
their actual allocation, timeout and caller-restoration behavior. -/
namespace Solidity.Source.Progress.CallCompositionControls
open EM Preservation.MemoryProgramControls
abbrev U : STy := .int .u256
abbrev Γ : RCtx := [U,Aty]

def small : Locals E.layout Γ := .cons (.int 2 (by decide)) (.cons (.memRef rfl 0) .nil)
def huge : Locals E.layout Γ := .cons (.int (2^64) (by decide)) (.cons (.memRef rfl 0) .nil)
def freshExpr : RExpr E Γ Aty := .newArray (τ := Aty) rfl (.local .here) rfl
def innerArgs : RConvArgs E Γ [Aty] := .cons freshExpr (by decide +kernel) .nil
def inner : RExpr E Γ Aty := .call d signature innerArgs
def outerArgs : RConvArgs E Γ [Aty] := .cons inner (by decide +kernel) .nil
def outer : RExpr E Γ Aty := .call d signature outerArgs
def chosen (flag : Bool) : RExpr E Γ Aty :=
  .cond (.bool flag) (.conv outer (.inr rfl)) (.local (.there .here))
def arguments2 : RConvArgs E Γ [Aty,Aty] :=
  .cons (.local (.there .here)) (by decide +kernel) (.cons inner (by decide +kernel) .nil)

theorem fresh_ready : ComposedExpr (fun d => d ∈ ([] : List Decl)) (fun called => called ∈ [d]) freshExpr :=
  .newArray (.array U rfl rfl) rfl (.base (.local _))
theorem inner_ready : ComposedExpr (fun d => d ∈ ([] : List Decl)) (fun called => called ∈ [d]) inner :=
  .call signature (by decide +kernel) (.cons _ (.inr rfl) fresh_ready .nil)
theorem outer_ready : ComposedExpr (fun d => d ∈ ([] : List Decl)) (fun called => called ∈ [d]) outer :=
  .call signature (by decide +kernel) (.cons _ (.inr rfl) inner_ready .nil)
theorem chosen_ready (flag : Bool) :
    ComposedExpr (fun d => d ∈ ([] : List Decl)) (fun called => called ∈ [d]) (chosen flag) :=
  .branch (.base (.value trivial trivial)) (.same (.inr rfl) outer_ready) (.base (.local _))
theorem arguments_ready : ComposedArgs (fun d => d ∈ ([] : List Decl)) (fun called => called ∈ [d]) arguments2 :=
  .cons _ (.inr rfl) (.base (.local _)) (.cons _ (.inr rfl) inner_ready .nil)

def fresh : Data E.layout Aty := .array 2 (fun _ h => nomatch h) (fun _ => .val (.int 0 (by decide)))
def afterInner : St E := {initial with heap := ((seed.alloc ⟨Aty,fresh⟩).1.alloc ⟨Aty,empty⟩).1}
def afterOuter : St E := {initial with heap := (afterInner.heap.alloc ⟨Aty,empty⟩).1}
def returnedArgs : Vals E.layout [Aty,Aty] := .cons (.memRef rfl 0) (.cons (.memRef rfl 1) .nil)

theorem small_mem : MemOK E seed.ty (small,initial) :=
  Preservation.relocalize entry_mem small ⟨trivial,⟨Aty,rfl,rfl⟩,trivial⟩
theorem huge_mem : MemOK E seed.ty (huge,initial) :=
  Preservation.relocalize entry_mem huge ⟨trivial,⟨Aty,rfl,rfl⟩,trivial⟩

theorem checked (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (n : Nat) :
    CompositionAt (fun d => d ∈ ([] : List Decl)) (glob p fixed) "Memory" [d] n :=
by
  have all : Solidity.Lowering.P9.WholeProgram.functions resolution = [d] := rfl
  have result := composition_program_from_elaborate resolution actual_elaboration (glob p fixed) rfl "Memory" [] [d]
    (value_check p fixed) (ReadyCatalogueIdentityControls.catalogue p fixed) (by decide +kernel) n
  rw [all] at result
  exact result

def cachedGlob (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) : Glob E :=
  {glob p fixed with prog := {(glob p fixed).prog with
    body := fun called => if called = d then some flatBody else (glob p fixed).prog.body called}}

theorem cachedGlob_eq (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) : cachedGlob p fixed = glob p fixed := by
  have actual : (glob p fixed).prog.body d = some flatBody := source_body
  have bodies : (fun called => if called = d then some flatBody else (glob p fixed).prog.body called) =
      (glob p fixed).prog.body := by
    funext called
    split
    next same => subst called; exact actual.symm
    next different => rfl
  exact congrArg (fun body => {glob p fixed with prog := {(glob p fixed).prog with body := body}}) bodies

theorem nested_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 20 outer).run (small,initial) =
      (.ok (.val (.memRef rfl 1)),(small,afterOuter)) := by
  rw [←cachedGlob_eq p fixed]
  cases p <;> rfl

theorem nested_preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalE (glob p fixed) frame 20 outer) ∧
    MemOK E seed.ty (small,afterOuter) ∧
    RValOK E afterOuter.heap.ty (.val (.memRef rfl 1) : RVal E.layout Aty) := by
  have joint := (checked p fixed 20).expr frame rfl outer outer_ready seed.ty
  have actual := joint.2 (small,initial) small_mem
  rw [nested_run] at actual
  exact ⟨joint.1,actual⟩

theorem chosen_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (flag : Bool) :
    (evalE (glob p fixed) frame 20 (chosen flag)).run (small,initial) =
      (.ok (.val (.memRef rfl (if flag then 1 else 0))),(small,if flag then afterOuter else initial)) := by
  rw [←cachedGlob_eq p fixed]
  cases p <;> cases flag <;> rfl

theorem chosen_preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (flag : Bool) :
    NS (evalE (glob p fixed) frame 20 (chosen flag)) ∧
    MemOK E seed.ty (small,if flag then afterOuter else initial) ∧
    RValOK E (if flag then afterOuter else initial).heap.ty
      (.val (.memRef rfl (if flag then 1 else 0)) : RVal E.layout Aty) := by
  have joint := (checked p fixed 20).expr frame rfl (chosen flag) (chosen_ready flag) seed.ty
  have actual := joint.2 (small,initial) small_mem
  rw [chosen_run] at actual
  exact ⟨joint.1,actual⟩

theorem arguments_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalConvArgs (glob p fixed) frame 20 arguments2).run (small,initial) =
      (.ok returnedArgs,(small,afterInner)) := by
  rw [←cachedGlob_eq p fixed]
  cases p <;> rfl

theorem arguments_preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    NS (evalConvArgs (glob p fixed) frame 20 arguments2) ∧
    MemOK E seed.ty (small,afterInner) ∧ RValsOK E afterInner.heap.ty returnedArgs.toR := by
  have joint := (checked p fixed 20).args frame rfl arguments2 arguments_ready seed.ty
  have actual := joint.2 (small,initial) small_mem
  rw [arguments_run] at actual
  exact ⟨joint.1,actual⟩

theorem huge_normalized : huge =
    (.cons (.int 18446744073709551616 (by decide)) (.cons (.memRef rfl 0) .nil) : Locals E.layout Γ) := rfl

theorem panic_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 20 outer).run (huge,initial) =
      (.error (.revert (panicData .alloc)),(huge,initial)) := by
  rw [huge_normalized,←cachedGlob_eq p fixed]
  cases p <;> rfl

theorem timeout_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 6 outer).run (small,initial) =
      (.error .timeout,(small,afterInner)) := by
  rw [←cachedGlob_eq p fixed]
  cases p <;> rfl

theorem halt_preserved (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    MemOK E seed.ty (huge,initial) ∧ MemOK E seed.ty (small,afterInner) := by
  have panic := ((checked p fixed 20).expr frame rfl outer outer_ready seed.ty).2 (huge,initial) huge_mem
  have timeout := ((checked p fixed 6).expr frame rfl outer outer_ready seed.ty).2 (small,initial) small_mem
  rw [panic_run] at panic
  rw [timeout_run] at timeout
  exact ⟨panic,timeout⟩

theorem raw_constant_argument_refused : ¬ PlainResultType (.rational (Q.ofInt 2)) := by
  unfold PlainResultType
  decide

private def headCallee {Δ : RCtx} {τ : STy} : RExpr E Δ τ → Option Decl
  | .call called _ _ => some called
  | _ => none

private theorem head_allowed {A B : Decl → Prop} {Δ : RCtx} {τ : STy} {e : RExpr E Δ τ}
    (ready : ComposedExpr A B e) : ∀ called, headCallee e = some called → A called ∨ B called := by
  cases ready with
  | base certified =>
    cases certified with
    | @value τ e fragment operations =>
      intro called observed
      cases e with
      | call target signature args =>
        have same : target = called := Option.some.inj observed
        subst called
        exact .inl fragment.1
      | _ => cases observed
    | _ => intro called observed; cases observed
  | @call target ps rs signature args member arguments =>
    intro called observed
    have same : target = called := Option.some.inj observed
    subst called
    exact .inr member
  | _ => intro called observed; cases observed

theorem unavailable_call_refused : ¬ ComposedExpr (fun _ => False) (fun _ => False) outer := by
  intro admitted
  rcases head_allowed admitted d rfl with impossible | impossible <;> exact impossible

#print axioms checked
#print axioms nested_run
#print axioms nested_preserved
#print axioms chosen_preserved
#print axioms arguments_preserved
#print axioms panic_run
#print axioms timeout_run
#print axioms halt_preserved
#print axioms raw_constant_argument_refused
#print axioms unavailable_call_refused
end Solidity.Source.Progress.CallCompositionControls
