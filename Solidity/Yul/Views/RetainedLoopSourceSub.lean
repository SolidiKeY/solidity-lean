import Solidity.Yul.Views.RetainedLoopSourceWrite

/-! Actual local-context substitution for captured-snapshot Source writes.
Caller locals return on success and halt; an ordinary later halt preserves
prior writes. No transaction/frame rollback or external call is inferred. -/
namespace Solidity.Yul.Views.RetainedLoopSourceSub

theorem sub_run {E Γ Δ} (F : Source.Fr) (operation : Source.Op E.layout E.lay E.lay)
    (caller : Source.Locals E.layout Γ) (child : Source.Locals E.layout Δ) (state : Source.St E) :
    (Source.EM.sub (E:=E) (Γ:=Γ) (Γ':=Δ) child (Source.applyOp (E:=E) (Γ:=Δ) F operation)).run (caller,state)=
      ((if F.static then (.error (.revert []),(caller,state))
      else (.ok ((),child),(caller,{state with ex := state.ex.apply operation}))) :
        Except Source.Halt (Unit × Source.Locals E.layout Δ) × Source.EMState E Γ) := by
  rw [actualSub_endpoints,actualApplyOp_run]
  cases F.static <;> rfl

/-- A child write followed by a caller-context halt is ordinary interpreter
sequencing, with no rollback operation. -/
def writeThenHalt {E Γ Δ} (F : Source.Fr) (operation : Source.Op E.layout E.lay E.lay)
    (child : Source.Locals E.layout Δ) (error : Source.Halt) : Source.EM E Γ Unit := do
  let _ ← Source.EM.sub (E:=E) (Γ:=Γ) (Γ':=Δ) child (Source.applyOp (E:=E) (Γ:=Δ) F operation)
  Source.EM.halt error

theorem halt_run {E Γ Δ} (F : Source.Fr) (operation : Source.Op E.layout E.lay E.lay)
    (caller : Source.Locals E.layout Γ) (child : Source.Locals E.layout Δ)
    (state : Source.St E) (error : Source.Halt) (static : F.static=false) :
    (writeThenHalt (E:=E) (Γ:=Γ) (Δ:=Δ) F operation child error).run (caller,state)=
      ((.error error,(caller,{state with ex := state.ex.apply operation})) :
        Except Source.Halt Unit × Source.EMState E Γ) := by
  unfold writeThenHalt
  rw [Source.Hoare.run_bind,sub_run,static]
  rfl

theorem halt_reencode {E Γ Δ τ b child active} (F : Source.Fr)
    {layout : @RetainedArrayLayout E τ b child active F.this} {fixed history scopes length}
    (image : CapturedArrayImage layout fixed history scopes length) (raw : SlotView)
    (caller : Source.Locals E.layout Γ) (callee : Source.Locals E.layout Δ)
    (state : Source.St E) (operation : Source.Op E.layout E.lay E.lay) (error : Source.Halt)
    (static : F.static=false) (checked : packedSeparationCheck (image.snapshot raw)=true)
    (prepared : finiteAccountWrite? F.this (image.snapshot raw) raw=some operation) :
    finiteEncode (image.snapshot raw)
      (((writeThenHalt (E:=E) (Γ:=Γ) (Δ:=Δ) F operation callee error).run (caller,state)).2.2.ex.world.accounts F.this).storage
      (packedMask (image.snapshot raw) raw)=some raw := by
  rw [halt_run F operation caller callee state error static]
  exact RetainedLoopWriteback.account_reencode image raw state.ex operation checked prepared

end Solidity.Yul.Views.RetainedLoopSourceSub
