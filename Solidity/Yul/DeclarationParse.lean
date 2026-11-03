import Solidity.Yul.CheckedParse
import Solidity.Yul.DeclarationScope

/-! Concrete composition of G08–G11 grammar certification and the complete
declaration-visibility component. This is NOT full Yul typing or admission:
references, capture, arity, control placement, metadata/safety and tier checks
remain independent obligations. Both root namespaces retain their real
provenance premises; neither is inferred from the source text here. -/
namespace Solidity.Yul
open Solidity.Source
open Solidity.Frontend.Checked

/-- Every independently certified assembly parse is reconstructed exactly.
This uses the ORIGINAL parser's checked equation, not a new parser or fuel. -/
theorem AssemblyParse.complete {src : Bytes} (p : AssemblyParse src) :
    parseAssembly src = some p := by
  cases p with
  | mk evmasm flags body layout checked =>
      unfold parseAssembly
      split
      · next err he =>
          have bad := he.symm.trans checked
          cases bad
      · next t L he =>
          have same : (t, L) = (Syn.assembly evmasm flags body, layout) :=
            Except.ok.inj (he.symm.trans checked)
          cases same
          rfl

structure DeclarationAssembly (outside visible : List String) (src : Bytes) where
  parsed : AssemblyParse src
  final : List String
  declarations : DeclarationScope.BlockD outside visible parsed.body final

def parseDeclarationAssembly (outside visible : List String) (src : Bytes) :
    Option (DeclarationAssembly outside visible src) := do
  let parsed ← parseAssembly src
  let ⟨final, declarations⟩ ← DeclarationScope.checkBlock outside visible parsed.body
  pure ⟨parsed, final, declarations⟩

/-- Exact composition: every grammar-plus-declaration derivation succeeds.
No assumption that either checker succeeds is substituted for these certificates
(the existing checked-parser equation and independent declaration derivation), and no full static-admission theorem is claimed. -/
theorem DeclarationAssembly.complete {outside visible src}
    (p : DeclarationAssembly outside visible src) :
    parseDeclarationAssembly outside visible src = some p := by
  cases p with
  | mk parsed final declarations =>
      unfold parseDeclarationAssembly
      rw [parsed.complete]
      change (DeclarationScope.checkBlock outside visible parsed.body).bind _ = _
      rw [declarations.complete]
      rfl

theorem parseDeclarationAssembly_iff (outside visible : List String) (src : Bytes) :
    (parseDeclarationAssembly outside visible src).isSome = true ↔
      Nonempty (DeclarationAssembly outside visible src) := by
  constructor
  · intro h
    cases hc : parseDeclarationAssembly outside visible src with
    | none => simp only [hc, Option.isSome] at h; cases h
    | some p => exact ⟨p⟩
  · rintro ⟨p⟩
    rw [p.complete]
    rfl

end Solidity.Yul
