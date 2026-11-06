import Solidity.Frontend.SolcJson.YulContextTrace
import Solidity.Yul.TypingLeafScope

/-! Actual combined JSON certificate to individual typed read/target leaves,
with original intrinsic contexts. Relative grammar paths are NOT yet proved
equal to JSON positions, and exact external metadata accounting is separate. -/
namespace Solidity.Frontend.YulJson.ForwardJson
open Solidity.Yul

def Checked.leafTrace {X table original input outside localNames bound node}
    (checked : @Checked X table original input outside localNames bound node) :
    TypingLeaves.ContextTrace :=
  TypingLeaves.contextual checked.contextTrace

theorem Checked.leaf_coverage {X table original input outside localNames bound node}
    (checked : @Checked X table original input outside localNames bound node)
    (predicate : TypingLeaves.ContextPosition → TypingLeaves.Leaf → Prop) :
    TypingLeaves.AllContexts predicate checked.leafTrace ↔
      TypingSites.everyBlock checked.imported.prepared.typing []
        (fun context site => TypingLeaves.everySite site
          (fun position leaf => predicate (context,position) leaf)) :=
  (TypingLeaves.all_contextual checked.contextTrace predicate).trans
    (checked.context_coverage _)

theorem Checked.leaf_scoped {X table original input outside localNames bound node}
    (checked : @Checked X table original input outside localNames bound node) :
    TypingLeaves.AllContexts (fun _ leaf => leaf.scopedCorrect) checked.leafTrace :=
  TypingLeaves.contextual_scoped checked.contextTrace

end Solidity.Frontend.YulJson.ForwardJson
