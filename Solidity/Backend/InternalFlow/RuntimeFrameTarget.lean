import Solidity.Backend.InternalFlow.RuntimeFrameSemantics
import Solidity.Evm.MemoryCalls

/-! Checked target producers for existing intrinsic runtime-call syntax.
There is no user call-depth search limit. Compilation still uses the published
finite-body memory emitter; this does NOT assert an unbounded target call stack. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame
open Evm Evm.Memory
variable {C : Contract}

/-- Retarget the real emitter certificate through exact intrinsic execution
agreement. All producer metadata and representation premises are retained. -/
def ofProgram {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} (P : Prog C Γ Δ)
    (out : Calls.Program b F (program P)) : Calls.Program b F P where
  frag := out.frag
  code := out.code
  need := out.need
  cost := out.cost
  allocates := out.allocates
  zeroCost := out.zeroCost
  sound := by
    intro L frame σ base m repr room capacity
    have actual := out.sound repr room capacity
    rw [program_outcome] at actual
    exact actual

/-- Actual selection: unsupported memory/storage/tuple/body cases still fail
in the unchanged published compiler. No hypothetical certificate is supplied. -/
def compile (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) :
    Option (Calls.Program b F P) :=
  (Calls.compile b F (program P)).map (ofProgram P)

theorem single_outcome {Γ Δ : Ctx} (s : Stmt C Γ Δ) (σ : State C Γ) :
    (Prog.cons s .nil).run σ = s.run σ := by
  change TRun.seq s.runR TRun.nil σ = s.runR σ
  cases hs : s.runR σ with
  | error e => simp only [TRun.seq,hs]
  | ok out => simp only [TRun.seq,hs,TRun.nil,Except.map]

/-- A checked singleton program is an actual statement producer, including
callRec after runtime-frame normalization; no target run is assumed. -/
def ofStatement {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} (s : Stmt C Γ Δ)
    (out : Calls.Program b F (.cons s .nil)) : Calls.Statement b F s where
  frag := out.frag
  code := out.code
  need := out.need
  cost := out.cost
  allocates := out.allocates
  zeroCost := out.zeroCost
  sound := by
    intro L frame σ base m repr room capacity
    have actual := out.sound repr room capacity
    rw [single_outcome] at actual
    exact actual

def compileStatement (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (s : Stmt C Γ Δ) :
    Option (Calls.Statement b F s) :=
  (compile b F (.cons s .nil)).map (ofStatement s)

/-- The quotation-only callRec index is not inspected by either normalization
or target code selection. The body thunk itself remains exact. -/
theorem callRec_index {b : Nat} {Γ Δ ps rs : Ctx} (F : Frag Γ)
    (f : Name) (d e : Nat) (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
    (body : Unit → Prog C (rs ++ ps) (rs ++ ps)) :
    (compileStatement b F (.callRec f d args ret body)).map (·.code) =
    (compileStatement b F (.callRec f e args ret body)).map (·.code) := by
  simp only [compileStatement,compile,Option.map_map]
  rfl
end Solidity.Backend.InternalFlow.RuntimeFrame
