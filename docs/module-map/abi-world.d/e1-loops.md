| `Correctness/Lowering/Loops/Family.lean` | Loop-lowering family: shapes, output association, endpoint and the `LowerLoopsCorrect` statement. |
| `Correctness/Lowering/Loops/WhileBreak.lean` | While/break leaf: generic flag-loop target run plus G19 Source half. |
| `Correctness/Lowering/Loops/Correct.lean` | `lowerLoops_correct` and kernel acceptance of actual producer outputs. |
| `Correctness/Lowering/Loops/ForBreak.lean` | For/break leaf: generic flag-loop target run with a never-run update, plus G19 Source half. |
| `Correctness/Lowering/Loops/Capture.lean` | Actual `lowerLoops` + `elabStmtsP` outputs for the loop-family samples, quoted. |
| `Correctness/Lowering/Loops/Horizon.lean` | Identity conversions in `while`/`do` conditions and bodies cost one Source horizon (monotonicity transport). |
| `Correctness/Lowering/Loops/WhileContinue.lean` | While/continue leaf: two-path flag-loop target run plus G19 Source half through the horizon transport. |
| `Correctness/Lowering/Loops/DoBreak.lean` | Do-while/break leaf: first-flag loop with short-circuited condition, plus G19 Source half. |
| `Correctness/Lowering/Loops/WhileReset.lean` | While leaf with a resetting body: two-path flag-loop target run plus G19 Source half. |
| `Correctness/Lowering/Loops/DoContinue.lean` | Do-while/continue leaf: one-turn first-flag loop plus G19 Source half. |
