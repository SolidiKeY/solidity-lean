import Solidity.Yul.WordSyntax
import Solidity.Frontend.Yul.ClosedParse

/-! Source parsing composed with the independent Yul preparation certificate. -/
namespace Solidity.Yul.WordSyntax
open Solidity.Source (Syn)
open Solidity.Frontend.Checked
open Solidity.Yul.Closed

structure Parsed (outside : List String) (src : Bytes) where
  parsed : AssemblyParse src
  prepared : Prepared outside parsed.body

def parse (outside : List String) (src : Bytes) : Except Error (Parsed outside src) :=
  match parseAssembly src with
  | none => .error (.input .grammar)
  | some parsed => (prepare outside parsed.body).map (fun prepared => ⟨parsed, prepared⟩)

theorem Parsed.complete {outside src} (p : Parsed outside src) :
    parse outside src = .ok p := by
  cases p with
  | mk parsed prepared =>
      unfold parse
      rw [parsed.complete]
      change (prepare outside parsed.body).map (fun p => (⟨parsed, p⟩ : Parsed outside src)) = _
      rw [prepared.complete]
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

end Solidity.Yul.WordSyntax
