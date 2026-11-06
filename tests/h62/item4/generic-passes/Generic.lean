import Solidity.Backend.Passes.MappedTail
import Solidity.Backend.Passes.CapturedValueStability

/-! Additive candidate for audit item 9's assignment twins. This factors only
physical prefix/value composition. Operator-specific Source transport remains
with the live producer and must be retained by any eventual owner migration.
No type, width, branch, map, input or saved-tail premise is discarded. -/
namespace Solidity.Backend.Passes.H62Generic
open Evm Evm.Memory Evm.Compiler
variable {C : Contract} {Γ Δ : Ctx} {b L frame : Nat} {F : Frag Γ}
  {P : Prog C Γ Δ} {p : PrimTy}

/-- Intrinsic prefix composition; evaluates the selected value at the ACTUAL
mapped output state and fixes both witnesses before all arbitrary saved tails. -/
theorem prefix_value (programCode : CompiledProg b F P)
    (e : Val C Δ p) (operand : CompiledVal b programCode.frag e)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (input : (Compilation.memory programCode).Input L frame base state machine)
    (noPay : Evm.Prog.pays P = false) (out : Solidity.Out C state.H Δ)
    (sourceRun : P.run state = .ok out) (v : p.Denote)
    (evaluated : e.evalT out.st = .ok v) :
    ∃ (canonical : Machine) (addresses : Nat → Fin W) (word : Word),
      ReprV p v word ∧ canonical.stack = [] ∧ ∀ tail,
        run programCode.code {machine with stack := tail} = .ok {canonical with stack := tail} 0 ∧
        MappedOutput (.memory programCode) (L + Evm.Prog.pushes P) frame base state
          {machine with stack := tail} out.st {canonical with stack := tail} addresses ∧
        run operand.code {canonical with stack := tail} =
          .ok ({canonical with stack := tail}.push word) 0 ∧
        run (programCode.code ++ operand.code) {machine with stack := tail} =
          .ok ({canonical with stack := tail}.push word) 0 := by
  obtain ⟨canonical, addresses, _, empty, runs⟩ :=
    compilation_success_shared_mapped (.memory programCode) input noPay sourceRun
  have represented := (runs []).2.1
  obtain ⟨word, repr, values⟩ :=
    CapturedValueStability.value_shared e operand represented v evaluated
  refine ⟨canonical, addresses, word, repr, empty, ?_⟩
  intro tail
  refine ⟨(runs tail).1, (runs tail).2, values tail, ?_⟩
  exact (run_append_ok (c₂ := operand.code) (runs tail).1).trans (values tail)

/-- Same ordered observation used by all fixture rows. No vector generator. -/
def observe (cells : List Nat) : Evm.Out → Option (List Word × List Word)
  | .ok machine 0 => some (cells.map machine.mem, machine.stack)
  | _ => none

/-- A wrong saved tail cannot be hidden by a correct emitted head. -/
theorem saved_tail_refused (code : List Instr) (initial final : Machine)
    (word sentinel wrong : Word) (tail : List Word)
    (executed : run code {initial with stack := sentinel :: tail} =
      .ok ({final with stack := sentinel :: tail}.push word) 0)
    (different : sentinel ≠ wrong) :
    run code {initial with stack := sentinel :: tail} ≠
      .ok ({final with stack := wrong :: tail}.push word) 0 := by
  intro bad
  have stack := congrArg Machine.stack (Evm.Out.ok.inj (executed.symm.trans bad)).1
  exact different (List.cons.inj (List.cons.inj stack).2).1

end Solidity.Backend.Passes.H62Generic
