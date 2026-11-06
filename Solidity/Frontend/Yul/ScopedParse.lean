import Solidity.Yul.ScopedSyntax
import Solidity.Frontend.Yul.WordParse

/-! Source parsing composed with the independent Yul preparation certificate. -/
namespace Solidity.Yul.ScopedSyntax
open Solidity.Source (Syn)
open Solidity.Frontend.Checked
open Solidity.Yul.BlockScope (Scope)

structure Parsed {X} (scope : Scope X) (tier : Tier) (outside localNames : List String)
    (src : Bytes) where
  parsed : AssemblyParse src
  prepared : Prepared scope tier outside localNames parsed.body

def parse {X} (scope : Scope X) (tier : Tier) (outside localNames : List String) (src : Bytes) :
    Except Error (Parsed scope tier outside localNames src) :=
  match parseAssembly src with
  | none => .error .grammar
  | some parsed => (prepare scope tier outside localNames parsed.body).map
      (fun prepared => ⟨parsed, prepared⟩)

theorem Parsed.complete {X scope tier outside localNames src}
    (p : @Parsed X scope tier outside localNames src) :
    parse scope tier outside localNames src = .ok p := by
  cases p with
  | mk parsed prepared =>
    unfold parse
    rw [parsed.complete]
    change (prepare scope tier outside localNames parsed.body).map _ = _
    rw [prepared.complete]
    rfl

theorem parse_iff {X} (scope : Scope X) (tier : Tier) (outside localNames : List String)
    (src : Bytes) :
    (parse scope tier outside localNames src).isOk = true ↔
      Nonempty (Parsed scope tier outside localNames src) := by
  constructor
  · intro h
    cases actual : parse scope tier outside localNames src with
    | error reason => rw [actual] at h; cases h
    | ok p => exact ⟨p⟩
  · rintro ⟨p⟩
    rw [p.complete]
    rfl

end Solidity.Yul.ScopedSyntax
