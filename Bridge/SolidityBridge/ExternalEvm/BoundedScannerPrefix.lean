import SolidityBridge.ExternalEvm.BoundedScannerInterface

/-! Factored equations and accumulator monotonicity for the actual vendor scan.
These are proofs over D_J_scan, not a new scanner/evaluator or a chosen table. -/
namespace Solidity.Evm.External.Assembly
open EvmYul EvmYul.EVM

theorem scanner_byte_step (code : ByteArray) (pc : Nat) (byte : UInt8)
    (width : Nat) (jump : Bool) (acc : Array UInt256)
    (hb : code.get? pc = some byte)
    (hw : (parseInstr byte).map argOnNBytesOfInstr = some width)
    (hj : (parseInstr byte).map (fun op => decide (op = (Operation.JUMPDEST : Operation .EVM))) = some jump) :
    D_J_scan code pc acc = D_J_scan code (pc+1+width)
      (if jump then acc.push (.ofNat pc) else acc) := by
  have inside : pc < code.size := by
    by_contra outside
    simp only [ByteArray.get?,dif_neg outside] at hb
    cases hb
  cases hp : parseInstr byte with
  | none => simp only [hp,Option.map_none] at hw; cases hw
  | some op =>
    have widthEq : argOnNBytesOfInstr op = width := by
      simpa only [hp,Option.map_some,Option.some.injEq] using hw
    have jumpEq : decide (op = (Operation.JUMPDEST : Operation .EVM)) = jump := by
      simpa only [hp,Option.map_some,Option.some.injEq] using hj
    rw [D_J_scan,dif_pos inside,hb]
    change (match parseInstr byte with
      | none => acc
      | some op => D_J_scan code (pc+1+argOnNBytesOfInstr op)
          (if op = (Operation.JUMPDEST : Operation .EVM) then acc.push (.ofNat pc) else acc)) = _
    rw [hp]
    change D_J_scan code (pc+1+argOnNBytesOfInstr op)
      (if op = (Operation.JUMPDEST : Operation .EVM) then acc.push (.ofNat pc) else acc) = _
    rw [widthEq]
    by_cases here : op = (Operation.JUMPDEST : Operation .EVM)
    · simp only [here,decide_true] at jumpEq
      rw [←jumpEq,if_pos here]
      rfl
    · simp only [here,decide_false] at jumpEq
      rw [←jumpEq,if_neg here]
      rfl

theorem scanner_preserves_contains (code : ByteArray) (pc : Nat)
    (acc : Array UInt256) (target : UInt256) (h : acc.contains target = true) :
    (D_J_scan code pc acc).contains target = true := by
  rw [D_J_scan]
  split
  next inside =>
    cases hp : code.get? pc >>= parseInstr with
    | none => exact h
    | some op =>
      apply scanner_preserves_contains
      by_cases jump : op = (Operation.JUMPDEST : Operation .EVM)
      · simp only [if_pos jump,Array.contains_push,h,Bool.true_or]
      · simpa only [if_neg jump] using h
  next outside => exact h
termination_by code.size - pc
decreasing_by omega

end Solidity.Evm.External.Assembly
