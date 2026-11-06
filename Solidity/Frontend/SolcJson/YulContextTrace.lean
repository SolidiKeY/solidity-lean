import Solidity.Frontend.SolcJson.YulForwardJson
import Solidity.Yul.TypingSites

/-! Context sites constructed from the ACTUAL combined JSON import's existing
typing certificate, not a supplied context-provider law. These are expression/
assignment sites; individual variable-leaf and JSON-position alignment, backward
reference accounting and Source provenance/admission remain separate. -/
namespace Solidity.Frontend.YulJson.ForwardJson
open Solidity.Yul

def Checked.contextTrace {X table original input outside localNames bound node}
    (checked : @Checked X table original input outside localNames bound node) :
    TypingSites.Trace :=
  TypingSites.block checked.imported.prepared.typing []

theorem Checked.context_coverage {X table original input outside localNames bound node}
    (checked : @Checked X table original input outside localNames bound node)
    (predicate : TypingSites.Path → TypingSites.Site → Prop) :
    TypingSites.All predicate checked.contextTrace ↔
      TypingSites.everyBlock checked.imported.prepared.typing [] predicate :=
  TypingSites.all_block checked.imported.prepared.typing [] predicate

end Solidity.Frontend.YulJson.ForwardJson
