import Solidity.Backend.Scalar.Heights
import Solidity.Backend.LabelExec.FragmentSound
import Solidity.Backend.LabelExec.Boundaries
import Solidity.Evm.Machine

/-!
# Executable bytecode selection contracts

Statements only: fields are obligations, not assumed theorems. The existing
compiler IR, Backend.Block, numeric slice and fetched-byte machine retain their
own types. No source, memory, storage or account evaluator is introduced here.
-/
namespace Solidity.Backend.Selection

/-- Numeric IR words; symbolic storage slots are deliberately not coerced. -/
abbrev irStack (s : Scalar.Stack) : List Evm.Word :=
  s.map (fun w => .val (Evm.wmod w.toNat))

/-- Selection of one IR instruction, including physical operand refusal.
All nonstack machine fields must be preserved by a successful scalar step. -/
structure InstructionCertificate (i : Evm.Instr) where
  code : Program
  success : ∀ (input output : Scalar.Stack) (m : Evm.Machine),
    m.stack = irStack input →
    (i.step m = .ok { m with stack := irStack output } 0 ↔
      Scalar.run code input = some output)
  refusal : ∀ (input : Scalar.Stack) (m : Evm.Machine),
    m.stack = irStack input →
    (i.step m = .fault ↔ Scalar.run code input = none)

/-- A physical frame transformation, uniformly over every untouched suffix.
Capacity is checked at the full physical height, including that suffix. -/
structure FrameCertificate (input output : Scalar.Stack) where
  code : Program
  frame : ∀ tail : Scalar.Stack,
    Scalar.run code (input ++ tail) = some (output ++ tail)
  prefixes : ∀ (tail : Scalar.Stack),
    Scalar.stackBound code ((input ++ tail).length : Int) = true →
    ∀ (before after : Program) (reached : Scalar.Stack),
      before ++ after = code → Scalar.run before (input ++ tail) = some reached →
      reached.length ≤ 1024

/-- Finite structured execution of the EXISTING Backend.Block. Conditions
carry their actual resulting stack, rather than assuming a protected tail.
This is a relational specification for the control-realization proof, not a
second block language or an alternative numeric evaluator. -/
inductive StructuredExec : Block → Scalar.Stack → Scalar.Stack → Prop where
  | code {p : Program} {s t : Scalar.Stack}
      (run : Scalar.run p s = some t) : StructuredExec (.code p) s t
  | seq {a b : Block} {s u t : Scalar.Stack}
      (left : StructuredExec a s u) (right : StructuredExec b u t) :
      StructuredExec (.seq a b) s t
  | iteTrue {c : Program} {a b : Block} {s u t : Scalar.Stack} {w : Scalar.Word}
      (condition : Scalar.run c s = some (w :: u)) (nonzero : w ≠ 0)
      (body : StructuredExec a u t) : StructuredExec (.ite c a b) s t
  | iteFalse {c : Program} {a b : Block} {s u t : Scalar.Stack}
      (condition : Scalar.run c s = some (0 :: u))
      (body : StructuredExec b u t) : StructuredExec (.ite c a b) s t
  | loopDone {c : Program} {b : Block} {s t : Scalar.Stack}
      (condition : Scalar.run c s = some (0 :: t)) :
      StructuredExec (.loop c b) s t
  | loopMore {c : Program} {b : Block} {s u v t : Scalar.Stack} {w : Scalar.Word}
      (condition : Scalar.run c s = some (w :: u)) (nonzero : w ≠ 0)
      (body : StructuredExec b u v) (rest : StructuredExec (.loop c b) v t) :
      StructuredExec (.loop c b) s t

/-- Refine existing shape evidence with room for each branch's emitted
join-jump operand. Condition capacity alone does not bound this output peak.
The predicate refines the existing block/shape interface; it creates no new syntax. -/
def ExpansionRoom : Block → Nat → Nat → Prop
  | .code _, _, _ => True
  | .seq left right, n, m => ∃ middle : Nat,
      LabelExec.BlockShape left n middle ∧ LabelExec.BlockShape right middle m ∧
      ExpansionRoom left n middle ∧ ExpansionRoom right middle m
  | .ite _ left right, n, m =>
      ExpansionRoom left n m ∧ ExpansionRoom right n m ∧ m + 1 ≤ 1024
  | .loop _ body, n, _ => ExpansionRoom body n n

/-- Whole execution at a real assembled byte placement. The exit is after the
emitted block, including its final JUMPDEST; arbitrary prefix/suffix items are
retained. No reached-body, favourable target or backedge execution premise. -/
structure ControlCertificate (b : Block) (input output : Nat) where
  shape : LabelExec.BlockShape b input output
  room : ExpansionRoom b input output
  realize : ∀ (before after : List (Item Nat Empty)) (label : Nat)
    (out : Assembled Empty),
    assemble 0 LabelExec.emptyLink (before ++ (b.expand label).1 ++ after) = some out →
    ∀ (s t : Scalar.Stack), s.length = input → StructuredExec b s t →
    ∃ steps : Nat,
      LabelExec.advance steps (encode out.code)
        ⟨size (LabelExec.emitPrefix (before ++ (b.expand label).1 ++ after) before), s⟩ =
        some ⟨size (LabelExec.emitPrefix (before ++ (b.expand label).1 ++ after)
          (before ++ (b.expand label).1)), t⟩ ∧
      ∀ k : Nat, k ≤ steps → ∃ reached : LabelExec.State,
        LabelExec.advance k (encode out.code)
          ⟨size (LabelExec.emitPrefix (before ++ (b.expand label).1 ++ after) before), s⟩ =
          some reached ∧ reached.stack.length ≤ 1024

/-- Full IR-to-block lowering obligation, including the scalar caller frame.
It must be proved by selection/stack/control composition, not supplied as
a premise. The existing IR runner is unchanged. -/
structure LoweringCertificate (ir : List Evm.Instr) (b : Block) where
  success : ∀ (s t : Scalar.Stack) (m : Evm.Machine),
    m.stack = irStack s →
    (Evm.run ir m = .ok { m with stack := irStack t } 0 ↔ StructuredExec b s t)

/-- Assembly/encoding and behavior are tied to the SAME emitted program.
The decoder equation alone is never treated as executable behavior. -/
structure CompositionCertificate (ir : List Evm.Instr) (b : Block) (input output : Nat) where
  lowering : LoweringCertificate ir b
  control : ControlCertificate b input output
  assembled : Assembled Empty
  assembly : assemble 0 LabelExec.emptyLink (b.expand 0).1 = some assembled
  roundtrip : decode (encode assembled.code) = some assembled.code

end Solidity.Backend.Selection
