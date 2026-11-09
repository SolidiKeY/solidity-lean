import Solidity.Backend.PrimitivePackets.Bitwise.Selected
import Solidity.Backend.PrimitivePackets.BitNot.Controls

/-! Regression: bitwise AND/OR/XOR must read the two runtime cells in the
selected public code, preserve populated caller memory and every saved stack,
and match clean Source operands at all byte widths. The full initial physical
fixture is inhabited, not a supplied run. This does not identify a complete
Source world with a target heap, or prove gas/session/fetched-EVM adequacy. -/
namespace H62.PrimitivePackets.BitwiseCorrespondence
open Solidity Solidity.Evm Solidity.Evm.Memory
open Solidity.Backend.PrimitivePackets.Bitwise
open Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture
  (machine target represented F wide_bound)

theorem cell_reads (w : Fin 32) (x y : Nat)
    (hx : x < 2^(unsigned w).bits) (hy : y < 2^(unsigned w).bits) (saved : List Word) :
    ({machine (unsigned w).bits (unsigned w).valid x y hx hy with stack := saved} : Machine).mem 5 =
      .val (wmod x) ∧
    ({machine (unsigned w).bits (unsigned w).valid x y hx hy with stack := saved} : Machine).mem 4 =
      .val (wmod y) := by
  have hxW := wide_bound (unsigned w).bits (unsigned w).valid x hx
  have hyW := wide_bound (unsigned w).bits (unsigned w).valid y hy
  simp only [machine, writeMachine, upd, wmod, Nat.mod_eq_of_lt hxW, Nat.mod_eq_of_lt hyW]
  constructor <;> rfl

theorem joint {E : Source.Env} (G : Source.Glob E) (fr : Source.Fr) (fuel : Nat)
    (state : Source.St E) (op : Source.BinOp) (hop : Supported op)
    (w : Fin 32) (x y : Nat) (hx : x < 2^(unsigned w).bits) (hy : y < 2^(unsigned w).bits)
    (saved : List Word) :
    StateRepr 1 0 8 F (target (unsigned w).bits (unsigned w).valid x y hx hy)
      CompileExamples.base (machine (unsigned w).bits (unsigned w).valid x y hx hy) ∧
    (Source.evalE G fr (fuel+3) (sourceExpr E w op)).run
      (.cons (operand w x hx) (.cons (operand w y hy) .nil),state) =
      (.ok (.val (operand w (value op x y) (value_lt op hop _ _ _ hx hy))),
        (.cons (operand w x hx) (.cons (operand w y hy) .nil),state)) ∧
    (compileVal 4 (Frag.init context) (expression CompileExamples.C op)).map
      (fun compiled => run compiled.code
        {machine (unsigned w).bits (unsigned w).valid x y hx hy with stack := saved}) =
      some (.ok {machine (unsigned w).bits (unsigned w).valid x y hx hy with
        stack := .val (wmod (value op x y)) :: saved} 0) := by
  have reads := cell_reads w x y hx hy saved
  exact ⟨represented (unsigned w).bits (unsigned w).valid x y hx hy,
    evalE_selected G fr fuel state CompileExamples.C 4 op hop w x y hx hy
      {machine (unsigned w).bits (unsigned w).valid x y hx hy with stack := saved}
      reads.1 reads.2⟩

theorem reject_all_refuted (op : Source.BinOp) (hop : Supported op)
    (w : Fin 32) (x y : Nat) (hx : x < 2^(unsigned w).bits) (hy : y < 2^(unsigned w).bits)
    (saved : List Word) :
    run (code 4 op) {machine (unsigned w).bits (unsigned w).valid x y hx hy with stack := saved} ≠
      .revert := by
  have reads := cell_reads w x y hx hy saved
  rw [execute 4 op hop w x y hx hy _ reads.1 reads.2]
  intro h
  cases h

#print axioms cell_reads
#print axioms joint
#print axioms reject_all_refuted
end H62.PrimitivePackets.BitwiseCorrespondence
