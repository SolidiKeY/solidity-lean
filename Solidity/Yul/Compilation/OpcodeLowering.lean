import Solidity.Yul.Compilation.ArgumentLowering

/-! Concrete selections for the existing target numeric table. No new Yul
builtin semantics or admission table is defined. Native BYTE/CLZ and physical/
world opcodes outside Scalar remain unselected, pending real target adapters. -/
namespace Solidity.Yul.Compilation
open Backend Scalar

def selectBinaryOpcode : Op → Option BinarySelection
  | .ADD => some ⟨.ADD, (binary .ADD).getD (fun _ _ => 0), fun _ _ _ => rfl⟩
  | .SUB => some ⟨.SUB, (binary .SUB).getD (fun _ _ => 0), fun _ _ _ => rfl⟩
  | .MUL => some ⟨.MUL, (binary .MUL).getD (fun _ _ => 0), fun _ _ _ => rfl⟩
  | .DIV => some ⟨.DIV, (binary .DIV).getD (fun _ _ => 0), fun _ _ _ => rfl⟩
  | .MOD => some ⟨.MOD, (binary .MOD).getD (fun _ _ => 0), fun _ _ _ => rfl⟩
  | .SDIV => some ⟨.SDIV, (binary .SDIV).getD (fun _ _ => 0), fun _ _ _ => rfl⟩
  | .SMOD => some ⟨.SMOD, (binary .SMOD).getD (fun _ _ => 0), fun _ _ _ => rfl⟩
  | .EXP => some ⟨.EXP, (binary .EXP).getD (fun _ _ => 0), fun _ _ _ => rfl⟩
  | .LT => some ⟨.LT, (binary .LT).getD (fun _ _ => 0), fun _ _ _ => rfl⟩
  | .GT => some ⟨.GT, (binary .GT).getD (fun _ _ => 0), fun _ _ _ => rfl⟩
  | .SLT => some ⟨.SLT, (binary .SLT).getD (fun _ _ => 0), fun _ _ _ => rfl⟩
  | .SGT => some ⟨.SGT, (binary .SGT).getD (fun _ _ => 0), fun _ _ _ => rfl⟩
  | .EQ => some ⟨.EQ, (binary .EQ).getD (fun _ _ => 0), fun _ _ _ => rfl⟩
  | .AND => some ⟨.AND, (binary .AND).getD (fun _ _ => 0), fun _ _ _ => rfl⟩
  | .OR => some ⟨.OR, (binary .OR).getD (fun _ _ => 0), fun _ _ _ => rfl⟩
  | .XOR => some ⟨.XOR, (binary .XOR).getD (fun _ _ => 0), fun _ _ _ => rfl⟩
  | .SHL => some ⟨.SHL, (binary .SHL).getD (fun _ _ => 0), fun _ _ _ => rfl⟩
  | .SHR => some ⟨.SHR, (binary .SHR).getD (fun _ _ => 0), fun _ _ _ => rfl⟩
  | .SAR => some ⟨.SAR, (binary .SAR).getD (fun _ _ => 0), fun _ _ _ => rfl⟩
  | .SIGNEXTEND => some ⟨.SIGNEXTEND, (binary .SIGNEXTEND).getD (fun _ _ => 0), fun _ _ _ => rfl⟩
  | _ => none

def selectUnaryOpcode : Op → Option UnarySelection
  | .ISZERO => some selectIsZero
  | .NOT => some selectNot
  | _ => none

/-- Accepted opcode mapping cannot silently select a different instruction. -/
theorem selectBinaryOpcode_opcode (opcode : Op) (selected : BinarySelection)
    (accepts : selectBinaryOpcode opcode = some selected) : selected.opcode = opcode := by
  cases opcode <;> simp only [selectBinaryOpcode, Option.some.injEq, reduceCtorEq] at accepts
  all_goals cases accepts; rfl

/-- Exact domains are checked against existing dispatch, not a second list. -/
theorem selectBinaryOpcode_domain (opcode : Op) :
    (selectBinaryOpcode opcode).isSome = (binary opcode).isSome := by
  cases opcode <;> rfl

theorem selectUnaryOpcode_domain (opcode : Op) :
    (selectUnaryOpcode opcode).isSome = (unary opcode).isSome := by
  cases opcode <;> rfl

structure TernarySelection where
  opcode : Op
  value : Word → Word → Word → Word
  correct : ∀ (a b c : Word) (tail : Stack),
    step (.op opcode) (a :: b :: c :: tail) = some (value a b c :: tail)

def selectAddMod : TernarySelection :=
  ⟨.ADDMOD, (ternary .ADDMOD).getD (fun _ _ _ => 0), fun _ _ _ _ => rfl⟩
def selectMulMod : TernarySelection :=
  ⟨.MULMOD, (ternary .MULMOD).getD (fun _ _ _ => 0), fun _ _ _ _ => rfl⟩

def selectTernaryOpcode : Op → Option TernarySelection
  | .ADDMOD => some selectAddMod
  | .MULMOD => some selectMulMod
  | _ => none

theorem selectTernaryOpcode_domain (opcode : Op) :
    (selectTernaryOpcode opcode).isSome = (ternary opcode).isSome := by
  cases opcode <;> rfl

private theorem vector_triple (v : Vector Word 3) : v.toList = [v[0], v[1], v[2]] := by
  apply List.ext_getElem
  · exact Vector.length_toList
  · intro i hi hj
    have h : i = 0 ∨ i = 1 ∨ i = 2 := by simp only [Vector.length_toList] at hi; omega
    rcases h with h | h | h <;> subst i <;>
      simp only [Vector.getElem_toList, List.getElem_cons_zero, List.getElem_cons_succ]

def ternaryAritySlice (op : TernarySelection) :
    AritySlice 3 1 (fun input => #v[op.value input[0] input[1] input[2]]) where
  code := [.op op.opcode]
  correct := by
    intro input tail
    rw [vector_triple]
    simp only [run, List.cons_append, List.nil_append, op.correct, Option.bind_some]
    rfl

/-- Modulus is computed first, followed by the right and then left operand.
The primitive itself retains its unbounded intermediate before final modulus. -/
def lowerTernary {n : Nat} {a b c : Vector Word n → Word} (op : TernarySelection)
    (left : LoweredExpr n a) (right : LoweredExpr n b) (modulus : LoweredExpr n c) :
    LoweredExpr n (fun locals => op.value (a locals) (b locals) (c locals)) :=
  let arguments := lowerArgCons left (lowerArgCons right (lowerArgCons modulus (lowerNoArgs n)))
  let compiled := lowerInline arguments (ternaryAritySlice op)
  { code := compiled.code
    correct := by
      intro depth p selected locals newer tail
      exact compiled.correct depth p selected locals newer tail }

#print axioms selectBinaryOpcode_domain
#print axioms selectUnaryOpcode_domain
#print axioms selectTernaryOpcode_domain
#print axioms selectBinaryOpcode
#print axioms selectUnaryOpcode
#print axioms selectBinaryOpcode_opcode
#print axioms ternaryAritySlice
#print axioms lowerTernary
end Solidity.Yul.Compilation
