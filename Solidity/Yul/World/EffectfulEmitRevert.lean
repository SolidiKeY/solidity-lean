import Solidity.Yul.World.EffectfulEmitRollback

/-! Actual typed emit/assignment followed by ordinary custom-error execution.
This selected block is not universal external-call or compiler adequacy. -/
namespace Solidity.Yul.World.EffectfulEmitRevert
open Solidity.Source
open Solidity.Roadmap (Bytes)
open Solidity.Yul.World.EffectfulEmitSource

def failure (indexed anonymous : Bool) : RStmt (env indexed anonymous) [] false ⟨false,false⟩ [] [] :=
  .revertError ReturningCall.errorDecl rfl
    (.cons (.const (Q.ofInt ReturningCall.value)) (by cases indexed <;> cases anonymous <;> decide) .nil)
def block (indexed anonymous : Bool) : RItems (env indexed anonymous) [] false ⟨false,false⟩ [] [] :=
  .stmt (statement indexed anonymous) (.stmt (failure indexed anonymous) .nil)
def data {indexed anonymous} (G : Glob (env indexed anonymous)) : Bytes :=
  G.selector (sigOf (env indexed anonymous).layout "Denied" [ReturningCall.uint])++ReturningCall.output

def run {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (F : Fr)
    (n : Nat) (s : EMState (env indexed anonymous) Γ) :=
  (Source.EM.sub (Source.L0 (env indexed anonymous))
    (Source.execItems G F n 0 none (block indexed anonymous) .nil)).run s

/-- Actual fixed-horizon Source block execution, not a supplied failure result.
The state on halt retains the assignment and legacy log until frame rollback. -/
theorem actual {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (F : Fr)
    (s : EMState (env indexed anonymous) Γ) (normal : F.static=false) :
    run G F 9 s=(.error (.revert (data G)),after G F s) := by
  cases F with
  | mk owner sender value st contract checked depth =>
    cases st
    · cases indexed <;> cases anonymous <;> cases G with
      | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl
    · cases normal

end Solidity.Yul.World.EffectfulEmitRevert
