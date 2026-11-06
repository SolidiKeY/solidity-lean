import Solidity.Backend.Passes.CapturedValueStability
namespace Solidity.Backend.Passes
open Evm Evm.Memory Evm.Compiler
theorem capture_stage_revert_iff
  {C : Contract} {Γ : Ctx} {p : PrimTy} {b L frame : Nat} {F : Frag Γ}
  (x : Var) (e : Val C Γ p) (code : CompiledVal b F e)
  {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
  (input : (CapturedValueStability.captureStage x e code).Input L frame base σ m)
  (tail : List Word) :
  run (CapturedValueStability.captureStage x e code).code (appendTail m tail) = .revert ↔
    e.evalT σ = .error .revert
 := by
  have represented : StateRepr L b frame F σ base (appendTail m tail) :=
    input.1.stack (m.stack ++ tail)
  rcases code.cert.correct represented with
    ⟨value,word,sourceRun,repr,targetRun⟩ | ⟨sourceRun,targetRun⟩
  · have success : run (CapturedValueStability.captureStage x e code).code (appendTail m tail) =
        .ok (writeMachine (appendTail m tail) (cell (b+Γ.length)) word) 0 := by
      change run ((code.code ++ [.mstore (cell (b+Γ.length))]) ++ []) _ = _
      rw [List.append_nil,run_append_ok targetRun]
      rfl
    constructor
    · intro failed; rw [success] at failed; cases failed
    · intro failed; rw [sourceRun] at failed; cases failed
  · have failed : run (CapturedValueStability.captureStage x e code).code (appendTail m tail) = .revert := by
      change run ((code.code ++ [.mstore (cell (b+Γ.length))]) ++ []) _ = .revert
      exact run_append_revert (run_append_revert targetRun)
    exact ⟨fun _ => sourceRun,fun _ => failed⟩

end Solidity.Backend.Passes
