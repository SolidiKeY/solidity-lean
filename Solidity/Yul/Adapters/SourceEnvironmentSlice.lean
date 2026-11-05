import Solidity.Yul.Views.SourceBalanceOperands
import Solidity.Backend.Environment.Composition

/-! Actual Source environment reads and executed target environment slices.
Conversions, Source expressions, target Frame, instructions and evaluator are
all published definitions. This is the existing gas-free local slice, not a
compiler, target resource bound or independent runtime/world ledger theorem.
Balance uses the actual post-operand Source snapshot when operands have effects. -/
namespace Solidity.Yul.Adapters.SourceEnvironmentSlice
open Solidity.Yul.Views

/-- Target order matches the actual Source magic sequence; stack order reverses
those three pushes. No second statement syntax or opcode semantics is added. -/
def magicCode : List Backend.Instr :=
  [Backend.Environment.select .timestamp,Backend.Environment.select .msgSender,Backend.Environment.select .msgValue]

theorem magic_target {E} (G : Source.Glob E) (F : Source.Fr)
    (funds : ContractWorld.Address → Backend.Environment.Word)
    (tail : List Backend.Environment.Word) (memory : Backend.Environment.Memory) :
    Backend.Environment.runSlice (sourceEnvironmentFrame G F funds) magicCode ⟨tail,memory⟩=
      some ⟨environmentWord F.value::environmentWord (addressInputWord F.sender)::environmentWord G.timestamp::tail,memory⟩ := by
  first | omega | decide | skip
  change some (⟨environmentWord F.value::(environmentAddress F.sender).1::environmentWord G.timestamp::tail,memory⟩ : Backend.Environment.Slice)=_
  rw [environmentAddress_word]

/-- Same actual source values, complete Source state and ordered executed
slice. An unrelated target ledger is harmless because this code never reads it. -/
theorem magic {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ)
    (funds : ContractWorld.Address → Backend.Environment.Word)
    (tail : List Backend.Environment.Word) (memory : Backend.Environment.Memory) :
    (sourceMagicReads G F (n+1)).run s=
      (.ok (.val (uintValueOfWord E.layout G.timestamp),.val (Source.Val.address F.sender),
        .val (uintValueOfWord E.layout F.value)),s) ∧
    Backend.Environment.runSlice (sourceEnvironmentFrame G F funds) magicCode ⟨tail,memory⟩=
      some ⟨environmentWord F.value::environmentWord (addressInputWord F.sender)::environmentWord G.timestamp::tail,memory⟩ ∧
    (uintValueOfWord E.layout G.timestamp).word.map environmentWord=some (environmentWord G.timestamp) ∧
    (Source.Val.address (D:=E.layout) (p:=false) F.sender).word.map environmentWord=
      some (environmentWord (addressInputWord F.sender)) ∧
    (uintValueOfWord E.layout F.value).word.map environmentWord=some (environmentWord F.value) := by
  first | omega | decide | skip
  refine ⟨sourceMagic_sequence G F n s,magic_target G F funds tail memory,?_,?_,?_⟩
  · rw [uintValueOfWord_word];rfl
  · rw [sourceAddress_input_word];rfl
  · rw [uintValueOfWord_word];rfl

/-- Actual BALANCE consumes the exact converted account operand. Its funds are
constructed from Source code-presence/history observations, not postulated. -/
theorem balance_target {E Γ} (G : Source.Glob E) (F : Source.Fr) (s : Source.EMState E Γ)
    (address : Roadmap.Address) (tail : List Backend.Environment.Word) (memory : Backend.Environment.Memory) :
    Backend.Environment.runSlice (sourceEnvironmentFrame G F (sourceObservedFunds G s)) [.op .BALANCE]
      ⟨environmentWord (addressInputWord address)::tail,memory⟩=
        some ⟨environmentWord (sourceObservedBalance G s address)::tail,memory⟩ := by
  first | omega | decide | skip
  change some (⟨sourceObservedFunds G s (environmentAddress address)::tail,memory⟩ : Backend.Environment.Slice)=_
  rw [sourceObservedFunds_address]

theorem balance_local {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ)
    (index : Source.Idx Γ (.address false)) (address : Roadmap.Address)
    (localValue : s.1.get index=Source.Val.address address)
    (tail : List Backend.Environment.Word) (memory : Backend.Environment.Memory) :
    (Source.evalE G F (n+2) (sourceBalanceExpr index)).run s=
      (.ok (.val (uintValueOfWord E.layout (sourceObservedBalance G s address))),s) ∧
    Backend.Environment.runSlice (sourceEnvironmentFrame G F (sourceObservedFunds G s)) [.op .BALANCE]
      ⟨environmentWord (addressInputWord address)::tail,memory⟩=
        some ⟨environmentWord (sourceObservedBalance G s address)::tail,memory⟩ := by
  first | omega | decide | skip
  exact ⟨sourceBalanceLocal_run G F n s index address localValue,balance_target G F s address tail memory⟩

/-- Actual effectful operand results select the post-operand snapshot. This
assumes an actual evaluator equation, never target operand compilation or a
final physical/Source agreement theorem. Operand halts remain the owner law. -/
theorem balance_operand {E Γ payable} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (operand : Source.RExpr E Γ (.address payable)) (s after : Source.EMState E Γ) (address : Roadmap.Address)
    (actual : (Source.evalE G F n operand).run s=(.ok (.val (.address address)),after))
    (tail : List Backend.Environment.Word) (memory : Backend.Environment.Memory) :
    (Source.evalE G F (n+1) (.balance operand)).run s=
      (.ok (.val (uintValueOfWord E.layout (sourceObservedBalance G after address))),after) ∧
    Backend.Environment.runSlice (sourceEnvironmentFrame G F (sourceObservedFunds G after)) [.op .BALANCE]
      ⟨environmentWord (addressInputWord address)::tail,memory⟩=
        some ⟨environmentWord (sourceObservedBalance G after address)::tail,memory⟩ := by
  first | omega | decide | skip
  exact ⟨sourceBalanceOperand_run G F n operand s after address actual,balance_target G F after address tail memory⟩

theorem magic_bytes : (magicCode.map Backend.Instr.encode).flatten=[0x42,0x33,0x34] := by decide
end Solidity.Yul.Adapters.SourceEnvironmentSlice
