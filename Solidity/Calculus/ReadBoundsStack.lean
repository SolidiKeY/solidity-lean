import Solidity.Calculus.DecideLang

/-! Guards the ReadBounds fitsM stack-overflow regression with an explicit typed
worklist. This module changes no admission limit or logical specification. Each
occurrence is counted, including shared subtrees, in the original child order.
ReadBoundsStackCorrect proves exact equality to the existing counters. -/
namespace Solidity.Decide
variable {C : Contract}

/-- Intrinsic work items retain each term's sort; shared children are pushed
once per occurrence, so the existing tree budget is never turned into a DAG
budget. These implementation types are public for the separate equality proof, not an admission API. -/
inductive ReadBoundsStack.Task (C : Contract) where
  | term {s : Srt} (t : LTm C s)
  | formula (φ : LFml C)

def ReadBoundsStack.termChildren : {s : Srt} → LTm C s → List (ReadBoundsStack.Task C)
  | _, .var _ | _, .app0 _ | _, .err => []
  | _, .app1 _ x | _, .obsW x | _, .obsL x | _, .obsH x => [.term x]
  | _, .app2 _ x y | _, .index _ x y | _, .seq x y | _, .orElse x y => [.term x, .term y]
  | _, .app3 _ x y z => [.term x, .term y, .term z]
  | _, .kite a b t e => [.term a, .term b, .term t, .term e]

def ReadBoundsStack.formulaChildren : LFml C → List (ReadBoundsStack.Task C)
  | .tt => []
  | .eq a b => [.term a, .term b]
  | .not φ | .all _ _ φ => [.formula φ]
  | .and φ ψ | .imp φ ψ => [.formula φ, .formula ψ]

def ReadBoundsStack.Task.children : ReadBoundsStack.Task C → List (ReadBoundsStack.Task C)
  | .term t => ReadBoundsStack.termChildren t
  | .formula φ => ReadBoundsStack.formulaChildren φ

/-- Consume one unit per visited node, in the original left-to-right order.
The recursive call is in tail position; only the explicit worklist grows. -/
def ReadBoundsStack.work : Nat → List (ReadBoundsStack.Task C) → Option Nat
  | n, [] => some n
  | 0, _ :: _ => none
  | n + 1, task :: rest => ReadBoundsStack.work n (task.children ++ rest)

/-- Stack-safe compiled term counter; its exact recursor equality is proved below. -/
def LTm.fitsStack {s : Srt} (t : LTm C s) (n : Nat) : Option Nat :=
  ReadBoundsStack.work n [.term t]

/-- Stack-safe compiled formula counter with the same tree/fuel semantics. -/
def LFml.fitsStack (φ : LFml C) (n : Nat) : Option Nat :=
  ReadBoundsStack.work n [.formula φ]

end Solidity.Decide
