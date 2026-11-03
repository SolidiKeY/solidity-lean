import Solidity.Yul.OccurrenceSyntax
import Solidity.Frontend.Yul.WordParse

/-! Source parsing composed with the independent Yul preparation certificate. -/
namespace Solidity.Yul.OccurrenceSyntax
open Solidity.Source (Syn)
open Solidity.Frontend.Checked

structure Parsed (outside localNames : List String) (src : Bytes) where
  parsed : AssemblyParse src
  prepared : Prepared outside localNames parsed.body

def parse (outside localNames : List String) (src : Bytes) :
    Except Error (Parsed outside localNames src) :=
  match parseAssembly src with
  | none => .error .grammar
  | some parsed => (prepare outside localNames parsed.body).map
      (fun prepared => ⟨parsed, prepared⟩)

theorem Parsed.complete {outside localNames src} (p : Parsed outside localNames src) :
    parse outside localNames src = .ok p := by
  cases p with
  | mk parsed prepared =>
    unfold parse
    rw [parsed.complete]
    change (prepare outside localNames parsed.body).map _ = _
    rw [prepared.complete]
    rfl

theorem parse_iff (outside localNames : List String) (src : Bytes) :
    (parse outside localNames src).isOk = true ↔ Nonempty (Parsed outside localNames src) := by
  constructor
  · intro h
    cases actual : parse outside localNames src with
    | error reason => rw [actual] at h; cases h
    | ok p => exact ⟨p⟩
  · rintro ⟨p⟩
    rw [p.complete]
    rfl

end Solidity.Yul.OccurrenceSyntax
