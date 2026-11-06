import Solidity.Frontend.SolcJson.YulBlockPath
import Solidity.Frontend.SolcJson.YulForwardJson

/-! The actual JSON import's original direct block statement certificates.
Positions are relative to its extracted AST value, not the outer InlineAssembly
object. Nested/leaf/backward metadata and Source provenance remain separate. -/
namespace Solidity.Frontend.YulJson
open Solidity.Yul

def ScopedJson.Checked.statementTrace {X table original input outside localNames bound node}
    (checked : @ScopedJson.Checked X table original input outside localNames bound node) :
    TypingStatements.Trace := TypingStatements.block checked.prepared.typing

theorem ScopedJson.Checked.statement_positions {X table original input outside localNames bound node}
    (checked : @ScopedJson.Checked X table original input outside localNames bound node) :
    TypingStatements.All (fun ordinal item =>
      Nonempty (BlockPath.Witness bound checked.ast (ordinal,item))) checked.statementTrace :=
  BlockPath.decoded_block bound checked.shaped.parsed checked.prepared.typing

def ForwardJson.Checked.statementTrace {X table original input outside localNames bound node}
    (checked : @ForwardJson.Checked X table original input outside localNames bound node) :
    TypingStatements.Trace := checked.imported.statementTrace

theorem ForwardJson.Checked.statement_positions {X table original input outside localNames bound node}
    (checked : @ForwardJson.Checked X table original input outside localNames bound node) :
    TypingStatements.All (fun ordinal item =>
      Nonempty (BlockPath.Witness bound checked.imported.ast (ordinal,item))) checked.statementTrace :=
  checked.imported.statement_positions

end Solidity.Frontend.YulJson
