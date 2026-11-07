import Solidity.Backend.PrimitivePackets.Bitwise.Source
import Solidity.Evm.MemoryCompile

/-! Public memory-compiler selection and exact runtime-local execution. This is
an interpreter-code leaf, not a physical EvmYul or deployed-call certificate. -/
namespace Solidity.Backend.PrimitivePackets.Bitwise
open Solidity Evm

def coreOp : Source.BinOp → Solidity.BinOp
  | .bitAnd => .band | .bitOr => .bor | .bitXor => .bxor | _ => .band

def instruction : Source.BinOp → Instr
  | .bitAnd => .and | .bitOr => .or | .bitXor => .xor | _ => .and

def context : Ctx := [.val .uint, .val .uint]

/-- The operands are locals, not embedded constants. -/
def expression (C : Contract) (op : Source.BinOp) : Solidity.Val C context .uint :=
  .binop (coreOp op) (by cases op <;> rfl) (by cases op <;> rfl)
    (.simple (.local .here)) (.simple (.local (.there .here)))

def code (base : Nat) (op : Source.BinOp) : List Instr :=
  [.mload (base + 1), .mload base, instruction op]

/-- Selection is proved for the public compiler, not supplied as a premise. -/
theorem selected (C : Contract) (base : Nat) (op : Source.BinOp)
    (hop : Supported op) :
    (Memory.compileVal base (Frag.init context) (expression C op)).map
      (fun c => c.code) = some (code base op) := by
  rcases hop with rfl | rfl | rfl <;> rfl

/-- Read arbitrary runtime operands from the two cells. Every other machine
field and the arbitrary saved stack tail survive the generated code. -/
theorem execute (base : Nat) (op : Source.BinOp) (hop : Supported op)
    (w : Fin 32) (x y : Nat)
    (hx : x < 2 ^ (unsigned w).bits) (hy : y < 2 ^ (unsigned w).bits)
    (m : Machine) (left : m.mem (base + 1) = .val (wmod x))
    (right : m.mem base = .val (wmod y)) :
    run (code base op) m =
      .ok {m with stack := .val (wmod (value op x y)) :: m.stack} 0 := by
  have hp : 2 ^ (unsigned w).bits ≤ W :=
    Nat.pow_le_pow_right (by decide) (unsigned w).valid.2.2
  have hxW : x < W := Nat.lt_of_lt_of_le hx hp
  have hyW : y < W := Nat.lt_of_lt_of_le hy hp
  have hrW : value op x y < W := Nat.lt_of_lt_of_le (value_lt op hop _ _ _ hx hy) hp
  rcases hop with rfl | rfl | rfl <;>
    simp only [code, instruction, run, exec, Instr.step, Machine.next, Out.bind,
      left, right, wmod, Nat.mod_eq_of_lt hxW, Nat.mod_eq_of_lt hyW,
      value, Nat.and_comm, Nat.or_comm, Nat.xor_comm] at * <;>
    congr 3 <;> simp only [Nat.mod_eq_of_lt hrW]

/-- A selected-code client combines an actual compiler result with Source
binVal and execution, without a CompiledVal or desired-run hypothesis. -/
theorem source_selected {D : Source.Layout} (C : Contract) (checked : Bool)
    (base : Nat) (op : Source.BinOp) (hop : Supported op) (w : Fin 32)
    (x y : Nat) (hx : x < 2 ^ (unsigned w).bits) (hy : y < 2 ^ (unsigned w).bits)
    (m : Machine) (left : m.mem (base + 1) = .val (wmod x))
    (right : m.mem base = .val (wmod y)) :
    Source.binVal checked op (operand (D := D) w x hx) (operand w y hy) =
        .ok (operand w (value op x y) (value_lt op hop _ _ _ hx hy)) ∧
    (Memory.compileVal base (Frag.init context) (expression C op)).map
        (fun c => run c.code m) =
      some (.ok {m with stack := .val (wmod (value op x y)) :: m.stack} 0) := by
  refine ⟨binVal_operand checked w op hop x y hx hy, ?_⟩
  have hs := congrArg (Option.map (fun c => run c m)) (selected C base op hop)
  simpa only [Option.map_map, Option.map_some, Function.comp_def,
    execute base op hop w x y hx hy m left right] using hs

/-- The signed carrier: since H87 the memory compiler accepts `&`, `|`, `^` at
`int` (the opcode on two's-complement words, `Evm.stail_simT`). -/
def signedExpression (C : Contract) (op : Source.BinOp) :
    Solidity.Val C [.val .int, .val .int] .int :=
  .binop (coreOp op) (by cases op <;> rfl) (by cases op <;> rfl)
    (.simple (.local .here)) (.simple (.local (.there .here)))

theorem signed_accepted (C : Contract) (base : Nat) (op : Source.BinOp)
    (hop : Supported op) :
    (Memory.compileVal base (Frag.init _) (signedExpression C op)).isSome = true := by
  rcases hop with rfl | rfl | rfl <;> rfl

/-- There is no dirty-word extension of the narrow Source operand relation. -/
theorem dirty_refused (w : Fin 32) (x : Nat) (dirty : 2 ^ (unsigned w).bits ≤ x) :
    ¬ x < 2 ^ (unsigned w).bits := by omega

/-- Same operand association on both sides, with actual Source pipeline and
horizon, public compiler selection and exact generated-code execution. -/
theorem evalE_selected {E : Source.Env} (G : Source.Glob E) (F : Source.Fr)
    (n : Nat) (s : Source.St E) (C : Contract) (base : Nat)
    (op : Source.BinOp) (hop : Supported op) (w : Fin 32) (x y : Nat)
    (hx : x < 2 ^ (unsigned w).bits) (hy : y < 2 ^ (unsigned w).bits)
    (m : Machine) (left : m.mem (base + 1) = .val (wmod x))
    (right : m.mem base = .val (wmod y)) :
    let ls := Source.Locals.cons (operand (D := E.layout) w x hx)
      (.cons (operand w y hy) .nil)
    (Source.evalE G F (n + 3) (sourceExpr E w op)).run (ls, s) =
      (.ok (.val (operand w (value op x y) (value_lt op hop _ _ _ hx hy))), (ls, s)) ∧
    (Memory.compileVal base (Frag.init context) (expression C op)).map
        (fun c => run c.code m) =
      some (.ok {m with stack := .val (wmod (value op x y)) :: m.stack} 0) :=
  ⟨evalE_operand G F n w op hop x y hx hy s,
    (source_selected (D := E.layout) C F.checked base op hop w x y hx hy m left right).2⟩

end Solidity.Backend.PrimitivePackets.Bitwise
