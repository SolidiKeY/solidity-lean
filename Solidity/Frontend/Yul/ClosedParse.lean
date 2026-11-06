import Solidity.Yul.ClosedSyntax
import Solidity.Frontend.Yul.DeclarationParse

/-! Source parsing composed with the independent Yul preparation certificate. -/
namespace Solidity.Yul.ClosedSyntax
open Solidity.Source (Syn)
open Solidity.Frontend.Checked

structure Parsed (outside : List String) (src : Bytes) where
  parsed : AssemblyParse src
  checked : Checked outside parsed.body

def parse (outside : List String) (src : Bytes) : Except Error (Parsed outside src) :=
  match parseAssembly src with
  | none => .error .grammar
  | some parsed => (check outside parsed.body).map (fun checked => ⟨parsed, checked⟩)

theorem Parsed.complete {outside src} (p : Parsed outside src) :
    parse outside src = .ok p := by
  cases p with
  | mk parsed checked =>
      unfold parse
      rw [parsed.complete]
      change (check outside parsed.body).map
        (fun d => (⟨parsed, d⟩ : Parsed outside src)) = _
      rw [checked.complete]
      rfl

theorem parse_iff (outside : List String) (src : Bytes) :
    (parse outside src).toOption.isSome = true ↔ Nonempty (Parsed outside src) := by
  constructor
  · intro h
    cases hc : parse outside src with
    | error reason => simp only [hc, Except.toOption, Option.isSome] at h; cases h
    | ok p => exact ⟨p⟩
  · rintro ⟨p⟩
    rw [p.complete]
    rfl

end Solidity.Yul.ClosedSyntax
