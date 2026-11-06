import Solidity.Yul.WordRules
import Lean.PrettyPrinter.Delaborator.Builtins

/-! Matching printers for the closed-word DSL. This module is imported through
the surface layer only (nothing imports it yet), not through Solidity.Yul's core
import. -/
namespace Solidity.Yul.Logic
open Lean PrettyPrinter
open scoped Solidity.Yul.Logic

@[app_unexpander Term.mk] def unexpandWordTerm : Unexpander
  | `($_ $code $words) => `(tm{ yul $code | $words })
  | _ => throw ()

@[app_unexpander Program.mk] def unexpandWordProgram : Unexpander
  | `($_ $code $words) => `(dl{ yul program $code | $words })
  | _ => throw ()

@[app_unexpander Fml.modal] def unexpandWordModal : Unexpander
  | `($_ $mode $model $prog $post) => `(dl{ yul $mode ; $model ; $prog ; $post })
  | _ => throw ()

@[app_unexpander Fml.termModal] def unexpandWordTermModal : Unexpander
  | `($_ $mode $model $term $post) => `(dl{ yul eval $mode ; $model ; $term => $post })
  | _ => throw ()

@[app_unexpander Fml.loopModal] def unexpandWordLoopModal : Unexpander
  | `($_ $control $mode $model $condition $step $body $post) =>
      `(dl{ yul loop $control ; $mode ; $model ; $condition ; $step ; $body ; $post })
  | _ => throw ()

@[app_unexpander Fml.feed] def unexpandWordFeed : Unexpander
  | `($_ $read $post) => `(dl{ yul feed $read | $post })
  | _ => throw ()

@[app_unexpander Fml.subst] def unexpandWordSubst : Unexpander
  | `($_ $update $post) => `(dl{ yul subst $update ; $post })
  | _ => throw ()

@[app_unexpander Fml.atom] def unexpandWordAtom : Unexpander
  | `($_ $predicate) => `(dl{ yul atom $predicate })
  | _ => throw ()

@[app_unexpander Rule] def unexpandWordRule : Unexpander
  | `($_ $first $second) => `(dl{ yul $first ⇝ $second })
  | _ => throw ()

end Solidity.Yul.Logic
