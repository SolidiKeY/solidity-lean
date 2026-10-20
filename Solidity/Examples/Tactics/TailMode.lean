import Solidity.Calculus.DecideComplete
import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Typing.Constructibility

/-!
# Clean array tails, as an option (`docs/options.md`, O6)

An empty `push` on `Token[] tokens` recycles the first slot past the live
end as it is (`pushSlot`, as solc does), and a write through an alias left
dangling by a `pop` may have left something there (`Tokens.dangling`,
reachable: `Examples/Tactics/CleanTail.lean`).  So `tokens.push()` followed
by a read of the new element proves nothing under `ValidTail .solc`, and is
refuted at a reachable storage; under `ValidTail .clean` the starting
storage's tails are assumed clean (`cleanTail(storage) = true`), and the
strategy proves it: the closer reads a starting slot past a live end as the
default (`Calculus/DecideCleanTail.lean`).  A dirty write the program itself
makes is tracked by the elimination, under either option.
-/

namespace Solidity.Examples.Tactics.TailMode

local instance : InContract := ⟨Tokens⟩

open scoped Scoped

/-- `tokens.push(); assert(tokens[tokens.length - 1].value == 0);` -/
abbrev pushRead : Fml Tokens [] :=
  dl!{ [ tokens.push(); assert(tokens[tokens.length - 1].value == 0); ] true }

/-- The premise is `cleanTail(storage) = true`, as written. -/
example : (dl!{ cleanTail(storage) = true } : Fml Tokens []) = Fml.cleanTail Tokens := rfl

/-! ## 1 · Under `.clean`, by the strategy -/

/-- **The recycled slot reads the default**, the starting tails clean. -/
theorem pushRead_clean : ValidTail .clean pushRead := by
  show ⊨ dl!{ cleanTail(storage) = true →
    [ tokens.push(); assert(tokens[tokens.length - 1].value == 0); ] true }
  sol_prove

/-- The same as a postcondition: `sol_symex; sol_decide`. -/
theorem pushRead_clean_box :
    ValidTail .clean dl!{ [ tokens.push(); ] tokens[tokens.length - 1].value == 0 } := by
  show ⊨ dl!{ cleanTail(storage) = true → [ tokens.push(); ] tokens[tokens.length - 1].value == 0 }
  sol_symex
  sol_decide

/-- Through the alias `push()` returns, the slot at the old length. -/
theorem pushAlias_clean :
    ValidTail .clean dl!{ [ Token storage r = tokens.push(); ] r.value == 0 } := by
  show ⊨ dl!{ cleanTail(storage) = true → [ Token storage r = tokens.push(); ] r.value == 0 }
  sol_symex
  sol_decide

/-- So it holds in the initial state, whose tails are clean. -/
theorem pushRead_init : holds (State.init Tokens) pushRead := pushRead_clean.holds_init

/-! ## 2 · Under `.solc`, refuted -/

/-- error: sol_decide: the closer does not close the leaf -/
#guard_msgs in
/-- Without the premise the closer reads the recycled slot as it is. -/
example : ⊨ dl!{ [ tokens.push(); ] tokens[tokens.length - 1].value == 0 } := by
  sol_symex
  sol_decide

/-- A storage that is reachable (`dangling_slot_reachable`) with a dirty tail. -/
def danglingState : State Tokens [] := { State.init Tokens with storage := Tokens.dangling }

/-- **Refuted under `.solc`**: from `Tokens.dangling` the `assert` fails. -/
theorem pushRead_solc_refuted : ¬ ValidTail .solc pushRead :=
  fun h => Modality.afterRunTR_not_panic (h danglingState) (by decide +kernel)

/-! ## 3 · A dirty write the program makes

The elimination tracks writes through a dangling alias: only the starting
storage's tails are assumed clean, so a slot the program dirties is read as
written, under either option. -/

/-- `r` dangles after the `pop`; the write through it is what the next `push`
recycles. -/
theorem recycledWrite_solc : ValidTail .solc dl!{ [ Token storage r = tokens.push(); tokens.pop();
    r.value = 7; tokens.push(); assert(tokens[tokens.length - 1].value == 7); ] true } := by
  show ⊨ dl!{ [ Token storage r = tokens.push(); tokens.pop();
    r.value = 7; tokens.push(); assert(tokens[tokens.length - 1].value == 7); ] true }
  sol_prove

theorem recycledWrite_clean : ValidTail .clean dl!{ [ Token storage r = tokens.push(); tokens.pop();
    r.value = 7; tokens.push(); assert(tokens[tokens.length - 1].value == 7); ] true } :=
  ValidTail.clean_of_solc recycledWrite_solc

/-! ## 4 · As a contract's invariant

Clean tails are kept by a contract none of whose programs shrinks an array
of references while an alias may be held (`Prog.exposesNone`,
`Typing/CleanTailRun.lean`): its storages all have clean tails
(`ReachableBy.cleanTail`), so what `.clean` proves holds in every state it
reaches. -/

/-- A push bound to an alias and written through it exposes nothing. -/
example : (sol{ Token storage r = tokens.push(); r.value = 3; } :
    Prog Tokens [] _).exposesNone = true := by decide

/-- A `pop` with no alias in scope exposes nothing: what it pops is cleared. -/
example : (sol{ tokens.pop(); delete tokens; } : Prog Tokens [] _).exposesNone = true := by
  decide

/-- The `pop` that leaves `r` dangling fails the check. -/
example : (sol{ Token storage r = tokens.push(); tokens.pop(); r.value = 7; } :
    Prog Tokens [] _).exposesNone = false := by decide

/-- **The recycled slot reads the default in every state the contract
reaches** through programs that expose nothing. -/
theorem pushRead_reachable (σ : State Tokens [])
    (hσ : ReachableBy Tokens (fun _ _ P => P.exposesNone = true) σ.storage) :
    holds σ pushRead :=
  pushRead_clean.holds_reachable (fun _ h => h) σ hσ

end Solidity.Examples.Tactics.TailMode
