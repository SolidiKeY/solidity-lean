import Solidity.Syntax.Scoped

/-!
# Joining scoped programs

`P` then `Q`, for the elaborator's blocks (`Blk.append`,
`Syntax/Elab.lean`) and the calculus's block arms (`Calculus/Blocks.lean`).
It sits below both so that the core reaches no elaborator
(`docs/parallelism.md`).
-/

namespace Solidity

variable {C : Contract}

/-- `P` then `Q`. -/
def Prog.join {Γ Δ Ε : Ctx} : Prog C Γ Δ → Prog C Δ Ε → Prog C Γ Ε
  | .nil, Q => Q
  | .cons s P, Q => .cons s (Prog.join P Q)

end Solidity
