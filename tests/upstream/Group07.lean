import Solidity.Frontend.Testing
import Solidity.Semantics.Run

/-! Kernel certificates for the programs emitted from pinned Group07 source.
These certify emitted-program behavior, not a universal solc equivalence theorem. -/
solc_import "../solc/Group07.ast.json" hash 0xe8d2f4010c7b455e as Group07 testing

namespace Group07Checks
open Solidity

-- The frontend still rejects indexed push-call spelling; the native spelling
-- below separately checks exactly-once receiver capture.
#guard (Group07.report.find? (·.name == "pushIndexOnce")).any fun r =>
  r.status == .unsupported

-- Receiver effects may mutate a stack-local RHS; do not hoist such a push.
#guard (Group07.report.find? (·.name == "effectfulPushReceiver")).any fun r =>
  r.status == .unsupported

/-- `lazyDiscard` terminates normally with its source assertions retained. -/
theorem lazyDiscard : (Prog.run (State.init Group07) Group07.lazyDiscard).isOk = true := by
  decide +kernel

/-- `uncheckedNegation` terminates normally with its source assertions retained. -/
theorem uncheckedNegation : (Prog.run (State.init Group07) Group07.uncheckedNegation).isOk = true := by
  decide +kernel

/-- `lazyTuple` terminates normally with its source assertions retained. -/
theorem lazyTuple : (Prog.run (State.init Group07) Group07.lazyTuple).isOk = true := by
  decide +kernel

/-- `overlappingMemory` terminates normally with its source assertions retained. -/
theorem overlappingMemory : (Prog.run (State.init Group07) Group07.overlappingMemory).isOk = true := by
  decide +kernel

/-- `scalarDelete` terminates normally with its source assertions retained. -/
theorem scalarDelete : (Prog.run (State.init Group07) Group07.scalarDelete).isOk = true := by
  decide +kernel

/-- `orderedDiscard` retains its revert, rather than dropping the expression. -/
theorem orderedDiscard :
    (match Prog.run (State.init Group07) Group07.orderedDiscard with
      | .error .revert => true
      | _ => false) = true := by
  decide +kernel

/-- The existing standalone narrow guard rejects checked negation with revert.
This pins rejection, not the source ABI Panic(0x11) encoding; self-call frames
have a separate panic-data reading. -/
theorem checkedNegation :
    (match Prog.run (State.init Group07) Group07.checkedNegation with
      | .error .revert => true
      | _ => false) = true := by
  decide +kernel

/-- Only the selected literal string is allocated, with its exact bytes. -/
theorem literalStringChoice :
    (Prog.run (State.init Group07) Group07.literalStringChoice).isOk = true := by
  decide +kernel

/-- Reference push operands use one typed push-bind, preserving the fresh slot. -/
theorem pushReference :
    (Prog.run (State.init Group07) Group07.pushReference).isOk = true := by
  decide +kernel

/-- An effectful reference-push argument captures its receiver index once. -/
theorem pushIndexOnce :
    (Prog.run (State.init Group07)
      (sol[Group07]{ rows.push(); uint i = 0; set((rows[i++].push)(), 31);
        assert(i == 1 && rows[0].length == 1 && rows[0][0].x == 31); } :
        Prog Group07 [] _)).isOk = true := by
  decide +kernel

#print axioms pushIndexOnce
#print axioms pushReference
#print axioms literalStringChoice
#print axioms lazyDiscard
#print axioms checkedNegation
#print axioms overlappingMemory
end Group07Checks
