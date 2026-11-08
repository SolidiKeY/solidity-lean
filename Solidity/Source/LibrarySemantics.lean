import Solidity.Source.Machine

/-! Generic delegated-library calldata guard. Regression purpose: a typed
entry with unavailable storage-pointer ABI bytes must refuse calldata
observations explicitly, while ordinary entries execute the original action.
No storage word, linked address or physical ABI adequacy is fabricated. -/
namespace Solidity.Source
open EM

mutual
/-- Calldata references nested in array/tuple values. A delegated entry
without pointer ABI bytes refuses their observation, including transitive
internal calls; normal entries retain the existing evaluator behavior. -/
def STy.containsCalldata : STy → Bool
  | .bytes .calldata | .string .calldata | .struct .calldata _ => true
  | .array loc element _ => loc == .calldata || element.containsCalldata
  | .tuple types => STy.listContainsCalldata types
  | _ => false

def STy.listContainsCalldata : List STy → Bool
  | [] => false
  | ty :: rest => ty.containsCalldata || STy.listContainsCalldata rest
end


/-- One typed guard shared by all evaluator cases and transitive internal
calls. The ordinary mode reduces definitionally to the supplied action. -/
abbrev withLibraryCalldata {E : Env} {Γ : RCtx} {α : Type}
    (known : Bool) (ty : STy) (action : EM E Γ α) : EM E Γ α :=
  Bool.casesOn known
    (if ty.containsCalldata then halt (.stuck "unsupported calldata observation") else action) action

/-- Ordinary entries retain the exact action, for every result type. -/
theorem withLibraryCalldata_known {E : Env} {Γ : RCtx} {α : Type}
    (ty : STy) (action : EM E Γ α) : withLibraryCalldata true ty action = action := by
  rfl

/-- An unavailable calldata observation refuses before the action runs. -/
theorem withLibraryCalldata_unavailable {E : Env} {Γ : RCtx} {α : Type}
    (ty : STy) (action : EM E Γ α) (unavailable : ty.containsCalldata = true) :
    withLibraryCalldata false ty action = halt (.stuck "unsupported calldata observation") := by
  simp only [withLibraryCalldata, unavailable, if_true]

/-- Non-calldata observations remain available in a typed pointer entry. -/
theorem withLibraryCalldata_noncalldata {E : Env} {Γ : RCtx} {α : Type}
    (ty : STy) (action : EM E Γ α) (clean : ty.containsCalldata = false) :
    withLibraryCalldata false ty action = action := by
  simp only [withLibraryCalldata, clean, Bool.false_eq_true, if_false]

end Solidity.Source
