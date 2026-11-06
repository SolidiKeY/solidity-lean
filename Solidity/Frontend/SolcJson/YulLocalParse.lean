import Solidity.Frontend.SolcJson.YulBuiltinUse
import Solidity.Yul.OpenLocal
import Solidity.Yul.OpenScoped
import Solidity.Yul.LocalBlockLogic
/-! Actual guarded source preparation to the typed LOCAL Source extension.
The external context is EXACTLY localExternalTypes ctx. Namespace/solc-ID/
Source attachment and pipeline refinement remain separate obligations; this
does not install old Source.RStmt, session or G51 dispatch. -/
namespace Solidity.Frontend.YulJson.LocalParse
open Solidity.Yul
open Solidity.Yul.BlockScope (Scope)

abbrev Checked (ctx : Solidity.Source.Ctx) (scope : Scope (localExternalTypes ctx))
    (outside localNames : List String) (documentation : Option String)
    (src : Solidity.Frontend.Checked.Bytes) :=
  BuiltinGuard.Parsed scope .A outside localNames documentation src

def run {ctx scope outside localNames documentation src}
    (checked : Checked ctx scope outside localNames documentation src)
    (fuel : Nat) (state : LocalState ctx.env ctx.tys) :
    Option (LocalBlockOutcome ctx ClosedSyntax.rootControl) :=
  runLocalBlock ctx checked.original.prepared.typing.code checked.original.prepared.policy fuel state

theorem projection {ctx scope outside localNames documentation src}
    (checked : Checked ctx scope outside localNames documentation src)
    (fuel : Nat) (state : LocalState ctx.env ctx.tys) :
    (run checked fuel state).map LocalBlockOutcome.project =
      checked.original.prepared.rawRun fuel (localWordCells ctx state.1) :=
  runLocalBlock_projection ctx checked.original.prepared.typing.code checked.original.prepared.policy fuel state

theorem open_projection {ctx scope outside localNames documentation src}
    (checked : Checked ctx scope outside localNames documentation src)
    (fuel : Nat) (state : LocalState ctx.env ctx.tys) :
    (run checked fuel state).map LocalBlockOutcome.project =
      checked.original.prepared.openRun fuel (localWordCells ctx state.1) := by
  rw [checked.original.prepared.openRun_eq_rawRun]
  exact projection checked fuel state

/-- Exact G08--G11 source certificate coupled to execution of the SAME
prepared block. This does not establish Source-name/JSON provenance or
completeness of the underlying grammar recognizer. -/
theorem source_execution {ctx scope outside localNames documentation src}
    (checked : Checked ctx scope outside localNames documentation src)
    (state : LocalState ctx.env ctx.tys) :
    ∃ pieces, Solidity.Frontend.Checked.lex src = .ok pieces ∧
      Solidity.Frontend.Checked.Lexed src pieces ∧
      (Solidity.Source.Syn.assembly (k := Solidity.Source.SCtx.body)
        checked.original.parsed.evmasm checked.original.parsed.flags
        checked.original.parsed.body).toks checked.original.parsed.layout =
          some (Solidity.Frontend.Checked.tokensOf pieces) ∧
      (Solidity.Source.Syn.assembly (k := Solidity.Source.SCtx.body)
        checked.original.parsed.evmasm checked.original.parsed.flags
        checked.original.parsed.body).prec = true ∧
      ∀ fuel, (run checked fuel state).map LocalBlockOutcome.project =
        checked.original.prepared.openRun fuel (localWordCells ctx state.1) := by
  obtain ⟨pieces, lexed, certificate, tokens, precedence⟩ := checked.original.parsed.sound
  exact ⟨pieces, lexed, certificate, tokens, precedence,
    fun fuel => open_projection checked fuel state⟩

theorem world {ctx scope outside localNames documentation src}
    (checked : Checked ctx scope outside localNames documentation src)
    (fuel : Nat) (state : LocalState ctx.env ctx.tys) {result}
    (done : run checked fuel state = some result) : result.state.2 = state.2 :=
  runLocalBlock_world ctx checked.original.prepared.typing.code checked.original.prepared.policy fuel state done

theorem nonword {ctx scope outside localNames documentation src}
    (checked : Checked ctx scope outside localNames documentation src)
    (fuel : Nat) (state : LocalState ctx.env ctx.tys) {result}
    (done : run checked fuel state = some result)
    (ref : SourceLocalRef ctx) {kind} (shape : DeclaredSourceTypeD ctx.env ref.ty kind)
    (zero : wordCellWidth kind = 0) :
    result.state.1.get ref.index = state.1.get ref.index :=
  runLocalBlock_nonword ctx checked.original.prepared.typing.code checked.original.prepared.policy
    fuel state done ref shape zero

theorem stable {ctx scope outside localNames documentation src}
    (checked : Checked ctx scope outside localNames documentation src)
    (state : LocalState ctx.env ctx.tys) {lo hi} (increasing : lo ≤ hi) {result}
    (done : run checked lo state = some result) : run checked hi state = some result :=
  runLocalBlock_stable ctx checked.original.prepared.typing.code checked.original.prepared.policy
    state increasing done

theorem zero {ctx scope outside localNames documentation src}
    (checked : Checked ctx scope outside localNames documentation src)
    (state : LocalState ctx.env ctx.tys) : run checked 0 state = none := rfl

def holds {ctx scope outside localNames documentation src}
    (checked : Checked ctx scope outside localNames documentation src)
    (mode : Solidity.Modality) (post : LocalBlockOutcome ctx ClosedSyntax.rootControl → Prop)
    (state : LocalState ctx.env ctx.tys) : Prop :=
  LocalBlockLogic.holds mode checked.original.prepared.typing.code checked.original.prepared.policy post state

/-- Actual state-captured Lean-only rule composition for the checked program;
not uniform Source/G51 normalization or compiler adequacy. -/
theorem rule_sound {ctx scope outside localNames documentation src}
    (checked : Checked ctx scope outside localNames documentation src)
    (mode : Solidity.Modality) (post : LocalBlockOutcome ctx ClosedSyntax.rootControl → Prop)
    (state : LocalState ctx.env ctx.tys) :
    ∃ premise : Logic.Fml (0+wordCellCount (localExternalTypes ctx)),
      holds checked mode post state ↔
        premise.holds (WordState.pack (n := 0) ⟨Fin.elim0,localWordCells ctx state.1⟩) :=
  LocalBlockLogic.rule_sound mode checked.original.prepared.typing.code checked.original.prepared.policy post state


def formula {ctx scope outside localNames documentation src}
    (checked : Checked ctx scope outside localNames documentation src)
    (mode : Solidity.Modality) (post : LocalBlockOutcome ctx ClosedSyntax.rootControl → Prop)
    (state : LocalState ctx.env ctx.tys) :
    Logic.Fml (0+wordCellCount (localExternalTypes ctx)) :=
  LocalBlockLogic.formula mode checked.original.prepared.typing.code checked.original.prepared.policy post state

theorem formula_iff {ctx scope outside localNames documentation src}
    (checked : Checked ctx scope outside localNames documentation src)
    (mode : Solidity.Modality) (post : LocalBlockOutcome ctx ClosedSyntax.rootControl → Prop)
    (state : LocalState ctx.env ctx.tys) :
    (formula checked mode post state).holds
      (WordState.pack (n := 0) ⟨Fin.elim0,localWordCells ctx state.1⟩) ↔
      holds checked mode post state :=
  LocalBlockLogic.formula_iff mode checked.original.prepared.typing.code checked.original.prepared.policy post state

/-- Existing concrete rule object and its soundness, for SAME checked program
and SAME explicitly captured initial LOCAL state. No RuleExists premise. -/
theorem rule_step {ctx scope outside localNames documentation src}
    (checked : Checked ctx scope outside localNames documentation src)
    (mode : Solidity.Modality) (post : LocalBlockOutcome ctx ClosedSyntax.rootControl → Prop)
    (state : LocalState ctx.env ctx.tys) :
    ∃ premise : Logic.Fml (0+wordCellCount (localExternalTypes ctx)),
    ∃ _rule : Logic.Rule (formula checked mode post state) premise,
      holds checked mode post state ↔
        premise.holds (WordState.pack (n := 0) ⟨Fin.elim0,localWordCells ctx state.1⟩) := by
  obtain ⟨premise,⟨rule⟩⟩ := LocalBlockLogic.rule_exists mode
    checked.original.prepared.typing.code checked.original.prepared.policy post state
  exact ⟨premise,rule,(formula_iff checked mode post state).symm.trans (rule.sound _)⟩


theorem completed_unique {ctx scope outside localNames documentation src}
    (checked : Checked ctx scope outside localNames documentation src)
    (state : LocalState ctx.env ctx.tys) {left right first second}
    (one : run checked left state = some first)
    (two : run checked right state = some second) : first = second :=
  LocalBlockLogic.completed_unique checked.original.prepared.typing.code
    checked.original.prepared.policy state one two


def runJson (ctx : Solidity.Source.Ctx) {table names input outside localNames bound node}
    (checked : @BuiltinGuard.JsonChecked (localExternalTypes ctx) table names input outside localNames bound node)
    (fuel : Nat) (state : LocalState ctx.env ctx.tys) :
    Option (LocalBlockOutcome ctx ClosedSyntax.rootControl) :=
  runLocalBlock ctx checked.original.imported.prepared.typing.code
    checked.original.imported.prepared.policy fuel state

theorem json_projection (ctx : Solidity.Source.Ctx) {table names input outside localNames bound node}
    (checked : @BuiltinGuard.JsonChecked (localExternalTypes ctx) table names input outside localNames bound node)
    (fuel : Nat) (state : LocalState ctx.env ctx.tys) :
    (runJson ctx checked fuel state).map LocalBlockOutcome.project =
      checked.run fuel (localWordCells ctx state.1) := by
  rw [checked.run_agrees]
  exact runLocalBlock_projection ctx checked.original.imported.prepared.typing.code
    checked.original.imported.prepared.policy fuel state

theorem json_world (ctx : Solidity.Source.Ctx) {table names input outside localNames bound node}
    (checked : @BuiltinGuard.JsonChecked (localExternalTypes ctx) table names input outside localNames bound node)
    (fuel : Nat) (state : LocalState ctx.env ctx.tys) {result}
    (done : runJson ctx checked fuel state = some result) : result.state.2 = state.2 :=
  runLocalBlock_world ctx checked.original.imported.prepared.typing.code
    checked.original.imported.prepared.policy fuel state done

end Solidity.Frontend.YulJson.LocalParse
