import Solidity.Yul.RawSourceAdapter

/-! Void-return transport beside the existing raw LOCAL frame. The ordinary
Source outcome is an explicit clean projection; the authoritative raw frame is
retained unchanged. No ordinary local read, cleanup, valued return or general
assembly admission is supplied by this module. -/
namespace Solidity.Yul.RawSourceVoidReturn

def run {ctx : Solidity.Source.Ctx} {output : Solidity.Source.RCtx}
    (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R (Solidity.Source.Out ctx.env.layout ctx.tys output) × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | _+1 => (.ok (.ret state.clean),state)

def items {ctx : Solidity.Source.Ctx} {output : Solidity.Source.RCtx}
    (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R (Solidity.Source.Out ctx.env.layout ctx.tys output) × RawFrame.State ctx :=
  match fuel with
  | 0 => run 0 state
  | n+1 => run n state

def block {ctx : Solidity.Source.Ctx} (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R (Solidity.Source.Out ctx.env.layout ctx.tys ctx.tys) × RawFrame.State ctx :=
  match fuel with
  | 0 => run 0 state
  | n+1 => items n state

def project {ctx : Solidity.Source.Ctx} {output : Solidity.Source.RCtx}
    (result : Solidity.Source.R (Solidity.Source.Out ctx.env.layout ctx.tys output) × RawFrame.State ctx) :=
  (result.1,(Solidity.Source.L0 ctx.env,result.2.world))

theorem statement_correct : ∀ (ctx : Solidity.Source.Ctx) (modifier : Bool) (control : Solidity.Source.SCtx)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph ctx.env)) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSourceVoidReturn.run (output := ctx.tys) fuel state).2 = state ∧
 (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.ret (E := ctx.env) (R := []) (M := modifier) (k := control) (Γ := ctx.tys) rfl) state.clean).run
 (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawSourceVoidReturn.project (Solidity.Yul.RawSourceVoidReturn.run (output := ctx.tys) fuel state) := by
  intro ctx modifier control glob frame fuel nps ph state
  cases fuel <;> exact ⟨rfl,rfl⟩

theorem items_correct : ∀ (ctx : Solidity.Source.Ctx) (modifier : Bool) (control : Solidity.Source.SCtx)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph ctx.env)) (state : Solidity.Yul.RawFrame.State ctx) (output : Solidity.Source.RCtx)
 (rest : Solidity.Source.RItems ctx.env [] modifier control ctx.tys output),
 (Solidity.Yul.RawSourceVoidReturn.items (output := output) fuel state).2 = state ∧
 (Solidity.Source.execItems glob frame fuel nps ph (.stmt (Solidity.Source.RStmt.ret (E := ctx.env) (R := []) (M := modifier) (k := control) (Γ := ctx.tys) rfl) rest) state.clean).run
 (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawSourceVoidReturn.project (Solidity.Yul.RawSourceVoidReturn.items (output := output) fuel state) := by
  intro ctx modifier control glob frame fuel nps ph state output rest
  cases fuel with
  | zero => exact ⟨rfl,rfl⟩
  | succ fuel => cases fuel <;> exact ⟨rfl,rfl⟩

theorem block_correct : ∀ (ctx : Solidity.Source.Ctx) (modifier : Bool) (control : Solidity.Source.SCtx)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph ctx.env)) (state : Solidity.Yul.RawFrame.State ctx) (output : Solidity.Source.RCtx)
 (rest : Solidity.Source.RItems ctx.env [] modifier control ctx.tys output),
 (Solidity.Yul.RawSourceVoidReturn.block fuel state).2 = state ∧
 (Solidity.Source.execS glob frame fuel nps ph (.block (.stmt (Solidity.Source.RStmt.ret (E := ctx.env) (R := []) (M := modifier) (k := control) (Γ := ctx.tys) rfl) rest)) state.clean).run
 (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawSourceVoidReturn.project (Solidity.Yul.RawSourceVoidReturn.block fuel state) := by
  intro ctx modifier control glob frame fuel nps ph state output rest
  cases fuel with
  | zero => exact ⟨rfl,rfl⟩
  | succ fuel =>
    cases fuel with
    | zero => exact ⟨rfl,rfl⟩
    | succ fuel => cases fuel <;> exact ⟨rfl,rfl⟩

end Solidity.Yul.RawSourceVoidReturn
