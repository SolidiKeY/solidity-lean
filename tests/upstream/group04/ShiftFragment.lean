import Solidity.Calculus.Decision
import Solidity.Calculus.Surface
namespace Solidity.Group04ShiftFragment
open Solidity.Decide
set_option Elab.async false
def Bank : Contract := contract!{ mapping(uint => uint) balances; }
local instance : InContract := ⟨Bank⟩
def shrInt : Fml Bank [] := dl!{ ∀ int x; x < 0 → [ int y = x >> 1; ] y < 0 }
def shrIntBad : Fml Bank [] := dl!{ ∀ int x; [ int y = x >> 1; ] y < x }
def verdict (φ : Fml Bank []) : String := match decideGoal φ with
  | .proved => "proved"
  | .refuted _ => "refuted"
  | .unknown => "unknown"
/-- info: ["proved", "refuted"] -/
#guard_msgs in #eval [shrInt, shrIntBad].map verdict
theorem shr_covered : shrInt.Covered = true := by decide +kernel
/-- error: Solidity elaboration failed: a int where a uint is expected -/
#guard_msgs in #check sol[Bank]{ int x = -1; int y = x >> -1; }
end Solidity.Group04ShiftFragment
