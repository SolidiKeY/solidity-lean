import Solidity.Backend.LabelExec.ScalarTransfer
import Solidity.Backend.Scalar.Heights
import Solidity.Backend.Control

/-!
# The admitted numeric/control fragment and its stack effects (G45.03)

Only static arities are recorded, through the existing numeric-dispatch tables.
No field asserts a chosen execution result. Heights do not imply value-frame
preservation: a condition may change words below its result, and any simulation
must carry the actual resulting stack. Raw JUMP/JUMPI/JUMPDEST cannot enter
straight-line code through this type. Numeric operations themselves remain
Scalar.step; this is not a second arithmetic or source evaluator.

Code capacity reuses Scalar.stackBound, which checks every numeric boundary.
Capacity is for the full declared input height; adding a tail requires a new
capacity check. The structured test needs two temporary words above its tail:
its extra PUSH must not be hidden by a final-height or tail-preservation claim.
Erasure is a subtype projection, not a hot match on an indexed datatype (G0).
-/
namespace Solidity.Backend.LabelExec

/-- Operand/result counts in the published numeric-dispatch precedence. -/
def numericArity (o : Op) : Option (Nat × Nat) :=
  match Scalar.unary o with
  | some _ => some (1,1)
  | none => match Scalar.binary o with
    | some _ => some (2,1)
    | none => match Scalar.ternary o with
      | some _ => some (3,1)
      | none => none

/-- Minimal input/output heights; a suffix height is added by InstrShape. -/
def arity : Instr → Option (Nat × Nat)
  | .push .. => some (0,1)
  | .op (.DUP n) => some (n.val+1,n.val+2)
  | .op (.SWAP n) => some (n.val+2,n.val+2)
  | .op .POP => some (1,0)
  | .op o => numericArity o

/-- Syntactic stack effect, with no run/certificate/value premise. -/
inductive InstrShape (i : Instr) (input output : Nat) : Prop where
  | mk (consumed produced suffix : Nat)
      (row : arity i = some (consumed,produced))
      (input_eq : input = consumed + suffix)
      (output_eq : output = produced + suffix) : InstrShape i input output

/-- Exact stack-height composition of a numeric instruction list. -/
inductive CodeShape : Program → Nat → Nat → Prop where
  | nil (n : Nat) : CodeShape [] n n
  | cons {i : Instr} {p : Program} {n m k : Nat}
      (head : InstrShape i n m) (rest : CodeShape p m k) : CodeShape (i::p) n k

/-- An intrinsic numeric code fragment with independently checked prefix capacity. -/
structure Code (input output : Nat) where
  instructions : Program
  shape : CodeShape instructions input output
  capacity : Scalar.stackBound instructions (input : Int) = true

/-- Refinement of the EXISTING structured Block, not a replacement syntax. -/
inductive BlockShape : Block → Nat → Nat → Prop where
  | code {n m : Nat} (p : Code n m) : BlockShape (.code p.instructions) n m
  | seq {a b : Block} {n m k : Nat}
      (left : BlockShape a n m) (right : BlockShape b m k) : BlockShape (.seq a b) n k
  | ite {n m : Nat} {cond : Code n (n+1)} {thn els : Block}
      (left : BlockShape thn n m) (right : BlockShape els n m)
      (testCapacity : n+2 ≤ 1024) : BlockShape (.ite cond.instructions thn els) n m
  | loop {n : Nat} {cond : Code n (n+1)} {body : Block}
      (bodyShape : BlockShape body n n) (testCapacity : n+2 ≤ 1024) :
      BlockShape (.loop cond.instructions body) n n

/-- The raw block is retained with its intrinsically indexed refinement. -/
abbrev Structured (input output : Nat) := { b : Block // BlockShape b input output }

end Solidity.Backend.LabelExec
