import Solidity.Backend.PrimitivePackets.Shifts.Transport
import Solidity.Lowering.V07.SourceReads

/-! Arbitrary source/target contexts and local indices. Only initial local
word representation is assumed; compilation and both executions are derived.
The target remains the published symbolic EVM memory compiler/model, not a
physical bytecode/ABI/frame admission theorem. -/
namespace Solidity.Backend.PrimitivePackets.Shifts.General
open Solidity Solidity.Evm Solidity.Evm.Memory

variable {E : Source.Env} {C : Contract} {Γ : Ctx} {srcΓ : Source.RCtx}

def target (left : Bool) (i j : Idx Γ (.val .uint)) : Solidity.Val C Γ .uint :=
  .binop (targetOp left) (by cases left <;> rfl) (by cases left <;> rfl)
    (.simple (.local i)) (.simple (.local j))

def selected (b : Nat) (left : Bool) (i j : Idx Γ (.val .uint)) :
    CompiledVal b (Frag.init Γ) (target (C:=C) left i j) :=
  (compileVal b (Frag.init Γ) (target (C:=C) left i j)).get
    (by first | rfl | (cases left <;> rfl))

theorem public_selection (b : Nat) (left : Bool) (i j : Idx Γ (.val .uint)) :
    compileVal b (Frag.init Γ) (target (C:=C) left i j) = some (selected b left i j) := by
  first | rfl | (cases left <;> rfl)

theorem selected_code (b : Nat) (left : Bool) (i j : Idx Γ (.val .uint)) :
    (selected (C:=C) b left i j).code =
      [.mload (cellOf b i),.mload (cellOf b j),if left then .shl else .shr] := by
  first | rfl | (cases left <;> rfl)

theorem runtime_execution (b : Nat) (left : Bool) (i j : Idx Γ (.val .uint))
    (x k : Fin W) (m : Machine)
    (value : m.mem (cellOf b i) = .val x) (amount : m.mem (cellOf b j) = .val k) :
    run (selected (C:=C) b left i j).code m = .ok (m.push (.val (resultWord left x k))) 0 := by
  first
  | rfl
  | cases left <;> simp only [selected_code, Bool.false_eq_true, if_false, if_true,
      run, exec, Instr.step, Out.bind, Machine.next, Machine.push, value, amount, resultWord]

def expression (left : Bool) (i j : Source.Idx srcΓ (.int Source.IntTy.u256)) :
    Source.RExpr E srcΓ (.int Source.IntTy.u256) :=
  .shiftLike (sourceOp left) (.local i) (.local j) rfl

/-- The V07 pure local-pair producer supplies BOTH pipeline orders. No
individual argument execution or whole-expression equation is a premise. -/
theorem source_execution (global : Source.Glob E) (frame : Source.Fr) (extra : Nat)
    (left : Bool) (i j : Source.Idx srcΓ (.int Source.IntTy.u256))
    (locals : Source.Locals E.layout srcΓ) (state : Source.St E) (x k : Fin W)
    (value : locals.get i = .int (x.val : Int) (word_range x))
    (amount : locals.get j = .int (k.val : Int) (word_range k)) :
    (Source.evalE global {frame with checked:=false} (extra+3) (expression left i j)).run
      (locals,state) =
      (.ok (.val (.int ((resultWord left x k).val : Int) (word_range (resultWord left x k)))),
        (locals,state)) := by
  first
  | rfl
  | have paired := Lowering.V07.source_local_pair global {frame with checked:=false}
      extra (locals,state) Source.IntTy.u256 i j (x.val : Int) (k.val : Int)
      (word_range x) (word_range k) value amount
    rw [expression, Source.evalE, Source.Hoare.run_bind, paired]
    simp only [Source.RVal.amount, Source.getV, Source.RVal.get, Source.EM.lift,
      Int.toNat_natCast, source_word_value, bind, pure, ExceptT.bind, ExceptT.pure,
      ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure, Except.pure]

/-- General unsigned256 runtime shift transport, including equal local indices
when their initial reads agree. No public context-length or count cutoff. -/
theorem transport (global : Source.Glob E) (frame : Source.Fr) (extra b : Nat)
    (left : Bool) (si sj : Source.Idx srcΓ (.int Source.IntTy.u256))
    (ti tj : Idx Γ (.val .uint)) (locals : Source.Locals E.layout srcΓ)
    (state : Source.St E) (x k : Fin W) (machine : Machine)
    (sourceValue : locals.get si = .int (x.val : Int) (word_range x))
    (sourceAmount : locals.get sj = .int (k.val : Int) (word_range k))
    (targetValue : machine.mem (cellOf b ti) = .val x)
    (targetAmount : machine.mem (cellOf b tj) = .val k) :
    compileVal b (Frag.init Γ) (target (C:=C) left ti tj) = some (selected b left ti tj) ∧
    (Source.evalE global {frame with checked:=false} (extra+3) (expression left si sj)).run
      (locals,state) =
      (.ok (.val (.int ((resultWord left x k).val : Int) (word_range (resultWord left x k)))),
        (locals,state)) ∧
    run (selected (C:=C) b left ti tj).code machine =
      .ok (machine.push (.val (resultWord left x k))) 0 ∧
    Lowering.V07.IntValueRel Source.IntTy.u256
      (.int ((resultWord left x k).val : Int) (word_range (resultWord left x k)) :
        Source.Val E.layout (.int Source.IntTy.u256))
      (Lowering.V07.integerValue Source.IntTy.u256 ((resultWord left x k).val : Int)
        (word_range (resultWord left x k))) ∧
    ReprV .uint
      (Lowering.V07.integerValue Source.IntTy.u256 ((resultWord left x k).val : Int)
        (word_range (resultWord left x k))) (.val (resultWord left x k)) := by
  first
  | rfl
  | exact ⟨public_selection b left ti tj,
      source_execution global frame extra left si sj locals state x k sourceValue sourceAmount,
      runtime_execution (C:=C) b left ti tj x k machine targetValue targetAmount,
      Lowering.V07.integer_related _ _ _, ReprV.uint_of rfl⟩

end Solidity.Backend.PrimitivePackets.Shifts.General

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.General.target' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.General.target

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.General.selected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.General.selected

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.General.public_selection' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.General.public_selection

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.General.selected_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.General.selected_code

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.General.runtime_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.General.runtime_execution

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.General.expression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.General.expression

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.General.source_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.General.source_execution

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.General.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.General.transport
