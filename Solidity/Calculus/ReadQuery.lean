import Solidity.Calculus.ReadRealization

/-!
# Finite computations over typed storage reads

A query records the dependency of a later location on an earlier read.
For example, `balances[owners[a]]` first reads `owners[a]` and uses its
value to construct the second location. A trace follows only the selected
branches. Materializing that finite trace preserves the whole computation,
including its choice of locations; no enumeration of mapping keys is used.

This is a computation interface for read abstraction, not a second formula
language or an executable validity decision procedure.
-/

namespace Solidity.ReadRealization

variable {C : Contract} {α β : Type}

/-- A terminating computation whose only storage effect is a typed read.
The continuation may choose its next location from the value just read. -/
inductive Query (C : Contract) (α : Type) where
  | pure (value : α)
  | read (ref : Ref C) (next : ref.Value → Query C α)

namespace Query

/-- Compose computations without forgetting the dependencies of reads. -/
def bind (q : Query C α) (f : α → Query C β) : Query C β :=
  match q with
  | .pure x => f x
  | .read r k => .read r (fun v => (k v).bind f)

/-- One primitive read. -/
def get (r : Ref C) : Query C r.Value := .read r .pure

/-- Interpret reads in a valuation of actual typed locations. Such a
valuation gives aliases the same value by construction. -/
def run (rd : (r : Ref C) → r.Value) : Query C α → α
  | .pure x => x
  | .read r k => (k (rd r)).run rd

/-- The finite reads selected by this particular valuation, in dependency
order. Later locations may depend on earlier values. -/
def footprint (rd : (r : Ref C) → r.Value) : Query C α → List (Ref C)
  | .pure _ => []
  | .read r k => r :: (k (rd r)).footprint rd

/-- A computation over actual storage. -/
def runStorage (q : Query C α) (st : Storage C) : α := q.run (fun r => r.read st)

/-- Reconstruct storage by saving the selected finite reads. -/
def realize (q : Query C α) (rd : (r : Ref C) → r.Value) : Storage C :=
  ReadRealization.realize rd (q.footprint rd)

/-- Agreement on the selected trace preserves both the values read and
the locations selected later in the computation. -/
theorem run_congr (q : Query C α) (rd rd' : (r : Ref C) → r.Value)
    (h : ∀ r ∈ q.footprint rd, rd' r = rd r) : q.run rd' = q.run rd := by
  induction q with
  | pure x => rfl
  | read r k ih =>
    simp only [run, h r List.mem_cons_self]
    exact ih (rd r) (fun q hq => h q (List.mem_cons_of_mem r hq))

/-- Every finite read in the selected trace is present in the reconstructed
interpreter storage with precisely its assigned value. -/
theorem realize_read (q : Query C α) (rd : (r : Ref C) → r.Value)
    (r : Ref C) (hr : r ∈ q.footprint rd) : r.read (q.realize rd) = rd r :=
  ReadRealization.realize_read rd (q.footprint rd) r hr

/-- Finite materialization preserves the complete query, including reads
whose keys depend on other reads. -/
theorem run_realize (q : Query C α) (rd : (r : Ref C) → r.Value) :
    q.runStorage (q.realize rd) = q.run rd :=
  q.run_congr rd (fun r => r.read (q.realize rd)) (q.realize_read rd)

/-- Running a composed query is ordinary function composition with the
same read valuation. -/
theorem run_bind (q : Query C α) (f : α → Query C β) (rd : (r : Ref C) → r.Value) :
    (q.bind f).run rd = (f (q.run rd)).run rd := by
  induction q with
  | pure x => rfl
  | read r k ih => exact ih (rd r)

/-- The trace of composition includes the reads used to compute its
argument, followed by the continuation's selected trace. -/
theorem footprint_bind (q : Query C α) (f : α → Query C β) (rd : (r : Ref C) → r.Value) :
    (q.bind f).footprint rd = q.footprint rd ++ (f (q.run rd)).footprint rd := by
  induction q with
  | pure x => rfl
  | read r k ih => exact congrArg (List.cons r) (ih (rd r))

end Query

end Solidity.ReadRealization
