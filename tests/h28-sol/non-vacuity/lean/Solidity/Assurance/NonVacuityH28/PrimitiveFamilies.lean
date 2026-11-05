import Solidity.Assurance.NonVacuityH28.Locals

/-! Arbitrary-family primitive representation witnesses, including signed words. -/
namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics
variable (C : Contract)

def representedLiteral {Γ : Ctx} : (p : PrimTy) → p.Denote → Simple C Γ p
  | .uint, n => .lit n.val n.property
  | .bool, b => .bool b
  | .int, n => .lit n.val n.property

def literalWord : (p : PrimTy) → p.Denote → Evm.Word
  | .uint, n => .val (Evm.wmod (Evm.toWord n.val))
  | .bool, b => .val (Evm.bword b)
  | .int, n => .val (Evm.wmod (Evm.toWord n.val))

def primitiveProgram (p : PrimTy) (v : p.Denote) : Prog C [] [.val p] :=
  .cons (.declLocal p (.user "v") (some (.simple (representedLiteral C p v)))) .nil

def primitiveValueMachine (p : PrimTy) (v : p.Denote) : Evm.Machine :=
  {localMachine with mem := Evm.upd localMachine.mem 0 (literalWord p v)}

theorem primitive_value_fragment (p : PrimTy) (v : p.Denote) :
    Evm.inFragP (Evm.Frag.init []) (primitiveProgram C p v) = some (Evm.Frag.init [.val p]) := by
  cases p <;> rfl

theorem primitive_value_source (p : PrimTy) (v : p.Denote) :
    Prog.run (localSource C) (primitiveProgram C p v) =
      .ok ⟨(localSource C).push v, List.prefix_refl _⟩ := by
  cases p <;> rfl

theorem primitive_value_target (p : PrimTy) (v : p.Denote) :
    Evm.run (Evm.compileProg 0 (primitiveProgram C p v)) localMachine =
      .ok (primitiveValueMachine p v) 0 := by
  cases p <;> rfl

theorem all_primitive_values_represented (p : PrimTy) (v : p.Denote) :
    Evm.Sim C 1 0 (Evm.Frag.init [.val p]) ((localSource C).push v)
      (primitiveValueMachine p v) :=
  represented_success (primitive_value_fragment C p v) (closed_simulation C)
    (by change 1 ≤ Evm.Lmax; decide) (primitive_value_source C p v) (primitive_value_target C p v)

theorem all_primitive_value_fields (C : Contract) (p : PrimTy) (v : p.Denote) :
    Evm.ReprV p v ((primitiveValueMachine p v).memAt
      (Evm.lvl 0 (.here : Idx [.val p] (.val p)))) :=
  (all_primitive_values_represented C p v).vals .here

theorem negative_int_word :
    (primitiveValueMachine .int (⟨-1, rfl⟩ : PrimTy.int.Denote)).mem 0 =
      .val (Evm.wmod (Evm.W - 1)) := by
  decide +kernel

theorem negative_int_observation_not_erased :
    (primitiveValueMachine .int (⟨-1, rfl⟩ : PrimTy.int.Denote)).mem 0 ≠
      Evm.Word.val (Evm.wmod 0) := by
  decide +kernel

end Solidity.Assurance.NonVacuityH28
