import Solidity.Calculus.Core.Fml

/-!
# The cover goal of a branch

A condition can be stuck: M3's `Run.ite` is stuck on a `bool` local that
holds no `bool` (`guardOk`), and a scoped formula ranges over every value
(`Fml.bind`, `Fml.all`, `{anon(…)}`).  So a branch's two conditions need not
cover every state, as today (`Calculus/Logic.lean`): a box goal is true of a
stuck run anyway, and a diamond goal owes that one of them holds, the third
goal of `Proves.split` and of `Proves.inv` (after the frame's anonymising
update, the invariant and the condition's update), today's
`Premise.cover`.  `Premise.Sound` (`Calculus/Core/SoundKit.lean`) takes it
as a premise.
-/

namespace Solidity.Core

open Solidity (Modality)

variable {C : Contract}

/-- `φ ∨ ψ`, as `¬(¬φ ∧ ¬ψ)` (`Core.Fml.show` prints it `φ ∨ ψ`). -/
abbrev Fml.or {Γ : Ctx} (φ ψ : Fml C Γ) : Fml C Γ := .not (.and (.not φ) (.not ψ))

/-- What a premise owes under the modality `m` besides its formula
(`Premise.fml`): under the diamond, one of a branch's conditions holds, for a
loop's invariant rule where the invariant holds after the frame's update;
`true` otherwise. -/
def Premise.cover {Γ Γ' : Ctx} (m : Modality) (p : Premise C Γ Γ') : Fml C Γ :=
  match m with
  | .box => .tt
  | .diamond => Premise.casesOn (motive := fun _ _ => Fml C Γ) p
      (fun _ => .tt) (fun _ _ => .tt) (fun _ _ _ => .tt)
      (fun _ c c' _ _ => .or c c')
      (fun _ => .tt) (fun _ => .tt) (fun _ => .tt) (fun _ _ => .tt)
      (fun I xs hv U c c' _ _ _ _ => Fml.anonHavoc xs hv (.imp I (.upd .diamond U (.or c c'))))
      (fun _ _ => .tt)

end Solidity.Core
