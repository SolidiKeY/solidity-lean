import Solidity.Frontend.SolcJson.YulNames
import Solidity.Frontend.SolcJson.YulScopedParse
import Solidity.Yul.ScopedWordSyntax

/-! Concrete metadata-selected namespace to the existing guarded parser,
intrinsic elaboration and raw-word execution. Original bindings, typed table,
outside/local-name provenance, documentation attachment and initial raw cells
remain explicit inputs; this does not install general frontend admission. -/
namespace Solidity.Frontend.YulJson.MetadataWords
open Solidity.Yul
open Solidity.Frontend.Checked

structure Input {X} (table : DeclarationTable X) (original : Names.Original) where
  names : ScopedNames.Checked (Names.declarations table original)

def input? {X} (table : DeclarationTable X) (original : Names.Original) :
    Option (Input table original) :=
  (ScopedNames.check (Names.declarations table original)).map Input.mk

theorem Input.complete {X table original} (input : @Input X table original) :
    input? table original = some input := by
  cases input with
  | mk names => unfold input?; rw [names.complete]; rfl

def Input.scope {X table original} (input : @Input X table original) : BlockScope.Scope X :=
  .external input.names .root

abbrev Checked {X table original} (input : @Input X table original)
    (outside localNames : List String) (documentation : Option String) (src : Bytes) :=
  ScopedParse.Checked input.scope .A outside localNames documentation src

def check {X table original} (input : @Input X table original)
    (outside localNames : List String) (documentation : Option String) (src : Bytes) :
    Except ScopedParse.Error (Checked input outside localNames documentation src) :=
  ScopedParse.check input.scope .A outside localNames documentation src

theorem complete {X table original} (input : @Input X table original)
    {outside localNames documentation src}
    (checked : Checked input outside localNames documentation src) :
    check input outside localNames documentation src = .ok checked :=
  checked.complete

def run {X table original} {input : @Input X table original}
    {outside localNames documentation src}
    (checked : Checked input outside localNames documentation src)
    (fuel : Nat) (cells : WordCells X) :=
  checked.prepared.rawRun fuel cells

theorem run_stable {X table original} {input : @Input X table original}
    {outside localNames documentation src}
    (checked : Checked input outside localNames documentation src) (cells : WordCells X)
    {lo hi} (increasing : lo ≤ hi) {result}
    (done : run checked lo cells = some result) :
    run checked hi cells = some result :=
  checked.prepared.rawRun_stable cells increasing done

theorem rawRule_sound {X table original} {input : @Input X table original}
    {outside localNames documentation src}
    (checked : Checked input outside localNames documentation src) (mode : Solidity.Modality)
    (post : WordAdapter.Outcome X ClosedSyntax.rootControl 0 → Prop) :
    ∃ premise : Logic.Fml (0 + wordCellCount X), ∀ cells : WordCells X,
      WordAdapter.rawHolds mode checked.prepared.typing.code checked.prepared.policy post
        ⟨Fin.elim0,cells⟩ ↔
      premise.holds (WordState.pack (X := X) (n := 0) ⟨Fin.elim0,cells⟩) :=
  checked.prepared.rawState_rule_sound mode post

end Solidity.Frontend.YulJson.MetadataWords
