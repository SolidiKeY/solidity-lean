import Solidity.Yul.Syntax
import Solidity.Yul.BlockTyping
import Solidity.Yul.Words
import Solidity.Yul.WordAdapter
import Solidity.Yul.RawFrame
import Solidity.Yul.RawSourceAdapter
import Solidity.Yul.RawSourceVoidReturn

/-!
# Syntax and bounded raw-local Source interface

This import boundary reuses the published declarations without aliases or a
second representation. Expr and Stmt retain their context/arity/control indices.
RawFrame.State keeps raw words beside unchanged intrinsic Source locals.

RawSourceAdapter.Adapter and ItemAdapter are indexed by actual same-context
Source syntax. Their run fields are executable; their correct fields require
coherent input and exact Source execution equality, including the represented
world and control result. A consumer accepting an Adapter must receive both
fields. No instance for arbitrary statements is supplied by this boundary.

These bounded contracts do not establish general assembly admission, arbitrary
dirty-local Solidity readback, context-changing execution or whole-program
Source-to-EVM adequacy. RawSourceVoidReturn exports the existing void-return
slice separately; it does not generalize Adapter's loop-control result.

Concrete inhabited use and refusal/horizon controls already live in
Solidity.Yul.Checks.RawLiteralScope (adapterTrue, mixed, mixedSource, timeouts).
The core import boundary deliberately does not import that checks module.
-/
