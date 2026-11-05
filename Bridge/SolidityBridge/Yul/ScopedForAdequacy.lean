import SolidityBridge.Yul.ScopedForReflection

/-! Exact-result and noncompletion correspondence for the compiled closed,
normal scope/switch FOR slice. Numeric model fault means no finite outcome;
it is not a native exceptional halt or a logical Source/G24 theorem. -/
namespace SolidityBridge.Yul.ScopedForAdequacy
open Solidity Backend Scalar Selection
open Solidity.Yul.Closed Solidity.Yul.Compilation ProducerExpressions
section
variable {c : Solidity.Yul.Control} {n compilerFuel : Nat}
  {pre : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
  {condition : Solidity.Yul.Expr [] [] n 1}
  {post : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
  {body : Solidity.Yul.Stmt [] [] ⟨c.function,true⟩ n}
  (compiled : ScopedFor.Prepared compilerFuel (c := c) pre condition post body)
  (packet : ScopedFor.Packet compiled)

/-- Equality is over the full original source locals and actual full model
result, including caller tail and zero pending skip. -/
theorem output_iff (base : Nat) (bounded : compilerFuel ≤ base)
    (locals final : Vector Scalar.Word n) (caller : Stack) (m : Evm.Machine)
    (represented : m.stack = irStack (locals.toList ++ caller)) :
    (∃ horizon, evalStmt horizon .nil True.intro (.for_ (c := c) pre condition post body)
      (ScopedFor.profile compiled) (sourceLocals locals) = some ⟨sourceLocals final,.normal⟩) ↔
    Evm.run packet.selected.realization.ir m = .ok {m with stack := irStack (final.toList ++ caller)} 0 := by
  constructor
  · rintro ⟨horizon,completed⟩
    exact (ScopedForCompletion.transport_output compiled packet horizon locals final completed caller m represented).2
  · intro ran
    obtain ⟨count,source,frame,_⟩ := ScopedForReflection.source_of_model compiled packet base bounded
      locals caller m _ 0 represented ran
    have stacks := ArithmeticSelection.irStack_injective (congrArg Evm.Machine.stack frame)
    have lists : final.toList = (Nat.repeat (ScopedFor.update compiled) count
        (compiled.before.update locals)).toList := List.append_cancel_right stacks
    have same : final = Nat.repeat (ScopedFor.update compiled) count (compiled.before.update locals) := Vector.toList_inj.mp lists
    rw [←same] at source
    exact ⟨base+(count+2),source⟩

/-- Exact all-horizon noncompletion, not the insufficiency of any one horizon.
The selected model has no other outcomes for this concrete compiled slice. -/
theorem no_source_iff_fault (base : Nat) (bounded : compilerFuel ≤ base)
    (locals : Vector Scalar.Word n) (caller : Stack) (m : Evm.Machine)
    (represented : m.stack = irStack (locals.toList ++ caller)) :
    (∀ horizon, evalStmt horizon .nil True.intro (.for_ (c := c) pre condition post body)
      (ScopedFor.profile compiled) (sourceLocals locals) = none) ↔
    Evm.run packet.selected.realization.ir m = .fault := by
  constructor
  · intro never
    rcases packet.selected.classified (locals.toList ++ caller) m represented with
      fault | ⟨output,executed,completed⟩
    · exact fault
    · obtain ⟨count,source,_⟩ := ScopedForReflection.source_of_structured compiled packet base bounded
        locals caller output executed
      rw [never] at source
      cases source
  · intro fault horizon
    cases completed : evalStmt horizon .nil True.intro (.for_ (c := c) pre condition post body)
        (ScopedFor.profile compiled) (sourceLocals locals) with
    | none => rfl
    | some out =>
      obtain ⟨count,bound,result,executed,ran⟩ := ScopedForCompletion.transport compiled packet horizon
        locals out completed caller m represented
      rw [fault] at ran
      cases ran
end
/-- info: 'SolidityBridge.Yul.ScopedForAdequacy.output_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms output_iff
/-- info: 'SolidityBridge.Yul.ScopedForAdequacy.no_source_iff_fault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms no_source_iff_fault
end SolidityBridge.Yul.ScopedForAdequacy
