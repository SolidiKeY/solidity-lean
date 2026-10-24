import Lean

/-!
# A step's heartbeats, within the declaration's

The closers' bounded steps each run with a budget of their own
(`withCurrHeartbeats`, the context's `maxHeartbeats`: the limit
`checkMaxHeartbeats` reads, not the option).  A fresh count alone would let
a step started late spend its whole budget past what the enclosing limit has
left, and the enclosing check after it would then throw a timeout nobody
catches.  So a step's limit is its budget capped at the heartbeats the
enclosing limit has left (`remaining`), never zero (which would mean
unlimited): a step past either fails, and is caught where it runs.
-/

namespace Solidity.Budget

open Lean Elab Tactic

/-- The raw heartbeats the enclosing limit has left, `none` when it is
unlimited. -/
def remaining : CoreM (Option Nat) := do
  let c ← read
  if c.maxHeartbeats == 0 then return none
  return some (c.maxHeartbeats - ((← IO.getNumHeartbeats) - c.initHeartbeats))

/-- The raw limit of a step of `n` thousand heartbeats: `n` thousand, and
never past what the enclosing limit has left (at least one). -/
def limit (n : Nat) : CoreM Nat := do
  match ← remaining with
  | none => return n * 1000
  | some r => return max 1 (min r (n * 1000))

/-- `x` with `n` thousand heartbeats of its own, within the enclosing
limit's (`limit`). -/
def within {m : Type → Type} {α : Type} [Monad m] [MonadLiftT CoreM m] [MonadControlT CoreM m]
    [MonadWithReaderOf Core.Context m] (n : Nat) (x : m α) : m α := do
  let lim ← (limit n : CoreM Nat)
  withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats := lim }) x

/-- `x` within `n` thousand heartbeats (`within`); `none`, the state as it
was, where it fails or runs past them. -/
def bounded {α : Type} (n : Nat) (x : TacticM α) : TacticM (Option α) := do
  let saved ← saveState
  let r ← tryCatchRuntimeEx (within n (some <$> x)) fun _ => pure none
  if r.isNone then saved.restore
  return r

end Solidity.Budget
