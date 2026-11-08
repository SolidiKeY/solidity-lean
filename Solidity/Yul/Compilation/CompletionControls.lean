import Solidity.Yul.Compilation.ProducerExpressions
import Solidity.Yul.Compilation.MachineAdapter
/-! Shared normal-completion frame transport. The original intrinsic source,
full-word locals, newer prefix and arbitrary caller/nonstack state are retained.
This header adds no source or model execution premise to a family theorem. -/
namespace Solidity.Yul.Compilation.CompletionControls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

theorem sourceLocals_injective {n : Nat} : Function.Injective (@sourceLocals n) := by
  intro a b same
  apply Vector.ext
  intro i hi
  have words := congrFun same (⟨i,hi⟩ : Fin n)
  apply BitVec.eq_of_toNat_eq
  exact congrArg Fin.val words

/-- A reflected normal outcome determines its full-word output. This transports
an arbitrary target postcondition, so callers keep their complete machine frame
rather than repeating output extraction or assuming a chosen target result. -/
theorem normal_output {c : Control} {n : Nat} (out : Vector Scalar.Word n)
    (target : Vector Scalar.Word n → Prop)
    (transport : ∃ actual : Vector Scalar.Word n,
      (⟨sourceLocals out, .normal⟩ : Outcome c n) = ⟨sourceLocals actual, .normal⟩ ∧
        target actual) : target out := by
  obtain ⟨actual, same, done⟩ := transport
  have equal : out = actual := sourceLocals_injective (congrArg Outcome.vars same)
  cases equal
  exact done

theorem frame_locals_injective {n depth : Nat} (newer : Vector Scalar.Word depth)
    (out actual : Vector Scalar.Word n) (caller : List Evm.Word)
    (same : (newer.toList ++ out.toList).map coreWord ++ caller =
      (newer.toList ++ actual.toList).map coreWord ++ caller) : out = actual := by
  have mapped : (newer.toList ++ out.toList).map coreWord =
      (newer.toList ++ actual.toList).map coreWord := List.append_cancel_right same
  have lists : newer.toList ++ out.toList = newer.toList ++ actual.toList :=
    (List.map_inj_right (fun _ _ h => coreWord_injective h)).mp mapped
  exact Vector.toList_inj.mp (List.append_cancel_left lists)

theorem frame_height {n depth : Nat} (newer : Vector Scalar.Word depth)
    (out : Vector Scalar.Word n) (m final : Evm.Machine) (caller : List Evm.Word)
    (frame : final = {m with stack := (newer.toList ++ out.toList).map coreWord ++ caller}) :
    final.stack.length = depth + n + caller.length := by
  rw [frame]
  simp only [List.length_append, List.length_map, Vector.length_toList]

/-- Normal source-to-model transport plus actual model reflection give exact
normal-success equivalence. Neither a chosen horizon nor an expected output is
assumed in the reflection law. -/
theorem completion_iff {c : Control} {n depth : Nat} (stmt : Stmt [] [] c n)
    (profile : StmtWordP stmt) (code : List Evm.Instr)
    (forward : ∀ (horizon : Nat) (locals out : Vector Scalar.Word n),
      evalStmt horizon .nil True.intro stmt profile (sourceLocals locals) =
        some ⟨sourceLocals out,.normal⟩ →
      ∀ (newer : Vector Scalar.Word depth) (m : Evm.Machine) (caller : List Evm.Word),
      Evm.run code {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} =
        .ok {m with stack := (newer.toList ++ out.toList).map coreWord ++ caller} 0)
    (backward : ∀ (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
      (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat),
      Evm.run code {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} = .ok final skip →
      ∃ (horizon : Nat) (out : Vector Scalar.Word n),
      evalStmt horizon .nil True.intro stmt profile (sourceLocals locals) =
        some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧
        final = {m with stack := (newer.toList ++ out.toList).map coreWord ++ caller})
    (locals out : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
    (m : Evm.Machine) (caller : List Evm.Word) :
    (∃ horizon, evalStmt horizon .nil True.intro stmt profile (sourceLocals locals) =
      some ⟨sourceLocals out,.normal⟩) ↔
    Evm.run code {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} =
      .ok {m with stack := (newer.toList ++ out.toList).map coreWord ++ caller} 0 := by
  constructor
  · rintro ⟨horizon,source⟩
    exact forward horizon locals out source newer m caller
  · intro ran
    obtain ⟨horizon,actual,source,_,frame⟩ := backward locals newer m
      {m with stack := (newer.toList ++ out.toList).map coreWord ++ caller} caller 0 ran
    have equal : out = actual := frame_locals_injective newer out actual caller (congrArg Evm.Machine.stack frame)
    cases equal
    exact ⟨horizon,source⟩
/-- Empty-prefix specialization of the shared full-frame completion law.
It retains every original source horizon and the whole machine/caller result. -/
theorem completion_iff_zero {c : Control} {n : Nat} (stmt : Stmt [] [] c n)
    (profile : StmtWordP stmt) (code : List Evm.Instr)
    (forward : ∀ (horizon : Nat) (locals out : Vector Scalar.Word n),
      evalStmt horizon .nil True.intro stmt profile (sourceLocals locals) =
        some ⟨sourceLocals out, .normal⟩ → ∀ (m : Evm.Machine) (caller : List Evm.Word),
      Evm.run code {m with stack := locals.toList.map coreWord ++ caller} =
        .ok {m with stack := out.toList.map coreWord ++ caller} 0)
    (backward : ∀ (locals : Vector Scalar.Word n) (m final : Evm.Machine)
      (caller : List Evm.Word) (skip : Nat),
      Evm.run code {m with stack := locals.toList.map coreWord ++ caller} = .ok final skip →
      ∃ (horizon : Nat) (out : Vector Scalar.Word n),
      evalStmt horizon .nil True.intro stmt profile (sourceLocals locals) =
        some ⟨sourceLocals out, .normal⟩ ∧ skip = 0 ∧
        final = {m with stack := out.toList.map coreWord ++ caller})
    (locals out : Vector Scalar.Word n) (m : Evm.Machine) (caller : List Evm.Word) :
    (∃ horizon, evalStmt horizon .nil True.intro stmt profile (sourceLocals locals) =
      some ⟨sourceLocals out, .normal⟩) ↔
    Evm.run code {m with stack := locals.toList.map coreWord ++ caller} =
      .ok {m with stack := out.toList.map coreWord ++ caller} 0 := by
  have forward' (horizon : Nat) (locals out : Vector Scalar.Word n)
      (ran : evalStmt horizon .nil True.intro stmt profile (sourceLocals locals) =
        some ⟨sourceLocals out, .normal⟩) (newer : Vector Scalar.Word 0)
      (m : Evm.Machine) (caller : List Evm.Word) :
      Evm.run code {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} =
        .ok {m with stack := (newer.toList ++ out.toList).map coreWord ++ caller} 0 := by
    have empty : newer.toList = [] := List.length_eq_zero_iff.mp (by simp only [Vector.length_toList])
    simpa only [empty, List.nil_append] using forward horizon locals out ran m caller
  have backward' (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word 0)
      (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
      (ran : Evm.run code {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} =
        .ok final skip) :
      ∃ (horizon : Nat) (out : Vector Scalar.Word n),
      evalStmt horizon .nil True.intro stmt profile (sourceLocals locals) =
        some ⟨sourceLocals out, .normal⟩ ∧ skip = 0 ∧
        final = {m with stack := (newer.toList ++ out.toList).map coreWord ++ caller} := by
    have empty : newer.toList = [] := List.length_eq_zero_iff.mp (by simp only [Vector.length_toList])
    simp only [empty, List.nil_append] at ran
    simpa only [empty, List.nil_append] using backward locals m final caller skip ran
  simpa only [Vector.toList_empty, List.nil_append] using
    completion_iff stmt profile code forward' backward' locals out #v[] m caller
/-- Full completed-source transport specializes to normal-success equivalence
without repeating output/frame injectivity in each family. -/
theorem completion_iff_of_transport {c : Control} {n depth : Nat} (stmt : Stmt [] [] c n)
    (profile : StmtWordP stmt) (code : List Evm.Instr)
    (forward : ∀ (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n),
      evalStmt horizon .nil True.intro stmt profile (sourceLocals locals) = some result →
      ∀ (newer : Vector Scalar.Word depth) (m : Evm.Machine) (caller : List Evm.Word),
      ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out, .normal⟩ ∧
      Evm.run code {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} =
        .ok {m with stack := (newer.toList ++ out.toList).map coreWord ++ caller} 0)
    (backward : ∀ (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
      (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat),
      Evm.run code {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} = .ok final skip →
      ∃ (horizon : Nat) (out : Vector Scalar.Word n),
      evalStmt horizon .nil True.intro stmt profile (sourceLocals locals) =
        some ⟨sourceLocals out, .normal⟩ ∧ skip = 0 ∧
        final = {m with stack := (newer.toList ++ out.toList).map coreWord ++ caller})
    (locals out : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
    (m : Evm.Machine) (caller : List Evm.Word) :
    (∃ horizon, evalStmt horizon .nil True.intro stmt profile (sourceLocals locals) =
      some ⟨sourceLocals out, .normal⟩) ↔
    Evm.run code {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} =
      .ok {m with stack := (newer.toList ++ out.toList).map coreWord ++ caller} 0 := by
  apply completion_iff stmt profile code ?_ backward locals out newer m caller
  intro horizon locals out ran newer m caller
  obtain ⟨actual, same, target⟩ := forward horizon locals ⟨sourceLocals out, .normal⟩ ran newer m caller
  have equal : out = actual := sourceLocals_injective (congrArg Outcome.vars same)
  cases equal
  exact target
end Solidity.Yul.Compilation.CompletionControls
