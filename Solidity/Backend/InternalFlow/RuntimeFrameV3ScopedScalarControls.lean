import Solidity.Backend.InternalFlow.RuntimeFrameV3ScopedScalarClient

/-! Refusal and full-outcome controls for the exact scoped selector.
Initialization, observable writes and extra inner locals are not silently
accepted as dead defaults. No target payload/world claim is inferred. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScopedScalarCompiler.Controls
open Evm Evm.Memory ScalarRecursiveSource
open Client (C A)
open DisjointScalarReturn.Client (Γ F reference)

def invoke (inner : Prog C (Frame A) (Frame A)) : Stmt C Γ Γ :=
 ScalarSourceCompiler.call rfl reference ScalarReentry.count .here
   (.user "alias") (.user "count") (.user "result") "scalarCountdown" 4 (fun _ => inner)

def initialized : Prog C (Frame A) (Frame A) :=
 .cons (.block (.cons (.block (body A rfl 4))
   (.cons (.declLocal .uint (.user "privateDefault") (some (.simple (.lit 99 rfl)))) .nil))) .nil

theorem initialized_refused : compile 1 5 16 9 8 F (invoke initialized)=none := rfl

def protectedWrite : Prog C (Frame A) (Frame A) :=
 .cons (.block (.cons (.block (body A rfl 4))
   (.cons (.assignLocal (.there .here) (.simple (.lit 99 rfl))) .nil))) .nil

theorem protected_write_refused : compile 1 5 16 9 8 F (invoke protectedWrite)=none := rfl

def extraInnerLocal : Prog C (Frame A) (Frame A) :=
 .cons (.block (.cons (.block (.cons (.declLocal .uint (.user "inner") none) .nil))
   (.cons (.declLocal .bool (.user "outer") none) .nil))) .nil

theorem extra_inner_context_refused : compile 1 5 16 9 8 F (invoke extraInnerLocal)=none := rfl

theorem noncanonical_body_refused : compile 1 5 16 9 8 F
 (invoke (ScopedSource.decorate (.cons .revert .nil) .uint (.user "privateDefault")))=none := rfl

/-- The general source equation preserves panic and payload as distinct
source outcomes. It provides no target compilation for these refused bodies. -/
theorem panic_preserved {C : Contract} {Γ : Ctx} (σ : State C Γ) :
 (ScopedSource.decorate (.cons (.assert (.simple (.bool false))) .nil) .uint (.user "private")).run σ=
   .error .panic := by
 change (ScopedSource.decorate _ _ _).runR σ=_
 rw [ScopedSource.decorate_run]
 rfl

theorem payload_preserved {C : Contract} {Γ : Ctx} (σ : State C Γ) :
 (ScopedSource.decorate (.cons (.revertData [.bytes [1,2]]) .nil) .bool (.user "private")).run σ=
   .error (.revertWith [1,2]) := by
 change (ScopedSource.decorate _ _ _).runR σ=_
 rw [ScopedSource.decorate_run]
 rfl

theorem wrong_frontier : ScalarReentry.Endpoint.machine.mem 0≠w[22] := ScalarReentry.Controls.wrong_frontier

end Solidity.Backend.InternalFlow.RuntimeFrame.ScopedScalarCompiler.Controls
