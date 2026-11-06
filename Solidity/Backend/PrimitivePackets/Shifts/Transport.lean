import Solidity.Evm.MemoryCompile
import Solidity.Source.Eval
import Solidity.Lowering.V07.Scalar

/-! G25-SHIFT-1104 runtime uint256 shifts. Actual Source local evaluation,
public intrinsic compiler selection and the all-count numeric result law
compose in the arbitrary-context General module.
No Source admission, calldata decoding or whole-CALL correspondence is asserted. -/
namespace Solidity.Backend.PrimitivePackets.Shifts
open Solidity
open Solidity.Evm Solidity.Evm.Memory

abbrev TargetCtx : Ctx := [.val .uint, .val .uint]
abbrev SourceCtx : Source.RCtx := [.int Source.IntTy.u256, .int Source.IntTy.u256]

def targetOp (left : Bool) : Solidity.BinOp := if left then .shl else .shr
def sourceOp (left : Bool) : Source.BinOp := if left then .shl else .shr

def target {C : Contract} (left : Bool) : Solidity.Val C TargetCtx .uint :=
  .binop (targetOp left) (by cases left <;> rfl) (by first | rfl | (cases left <;> rfl))
    (.simple (.local .here)) (.simple (.local (.there .here)))

def selected {C : Contract} (b : Nat) (left : Bool) :
    CompiledVal b (Frag.init TargetCtx) (target (C:=C) left) :=
  (compileVal b (Frag.init TargetCtx) (target (C:=C) left)).get
    (by first | rfl | (cases left <;> rfl))

theorem public_selection {C : Contract} (b : Nat) (left : Bool) :
    compileVal b (Frag.init TargetCtx) (target (C:=C) left) = some (selected b left) := by
  first | rfl | (cases left <;> rfl)

/-- No compiled certificate or desired machine run is an input. The certificate
comes from the public compiler, and the complete saved machine is retained by
ValOutT on its success branch. -/
theorem selected_execution {C : Contract} {L b frame : Nat}
    (left : Bool) (state : State C TargetCtx) (base : Nat → Fin W)
    (machine : Machine)
    (represented : StateRepr L b frame (Frag.init TargetCtx) state base machine) :
    ValOutT .uint ((target (C:=C) left).evalT state)
      (run (selected (C:=C) b left).code machine) machine := by
  first | rfl | exact (selected (C:=C) b left).cert.correct represented

def expression {E : Source.Env} (left : Bool) :
    Source.RExpr E SourceCtx (.int Source.IntTy.u256) :=
  .shiftLike (sourceOp left) (.local .here) (.local (.there .here)) rfl

abbrev Range (n : Int) := Source.IntTy.u256.lo ≤ n ∧ n ≤ Source.IntTy.u256.hi

def locals {E : Source.Env} (x : Int) (hx : Range x) (k : Int) (hk : Range k) :
    Source.Locals E.layout SourceCtx := .cons (.int x hx) (.cons (.int k hk) .nil)

/-- Exact Source result and complete unchanged Source machine, including both
operand locals. The shift amount is a runtime local. -/
theorem source_execution {E : Source.Env} (global : Source.Glob E)
    (frame : Source.Fr) (extra : Nat) (left : Bool)
    (x : Int) (hx : Range x) (k : Int) (hk : Range k) (state : Source.St E) :
    (Source.evalE global {frame with checked:=false} (extra+3) (expression left)).run
      (locals x hx k hk,state) =
      ((Source.shiftVal false (sourceOp left) k.toNat
        (.int x hx : Source.Val E.layout (.int Source.IntTy.u256))).map Source.RVal.val,
        (locals x hx k hk,state)) := by
  rcases global with ⟨prog,p,fx,balance0,hasCode,callee,timestamp⟩
  cases p <;> cases left <;> rfl

/-- Saturation is a proved branch of the existing Source operation, not an
admission cutoff: every runtime count at least 256 is included. -/
theorem source_value_saturated {D : Source.Layout} (left : Bool)
    (x : Int) (hx : Range x) (k : Nat) (large : 256 ≤ k) :
    Source.shiftVal false (sourceOp left) k
      (.int x hx : Source.Val D (.int Source.IntTy.u256)) =
      .ok (Source.intWrap Source.IntTy.u256 0) := by
  first
  | rfl
  | cases left <;> simp only [sourceOp, Bool.false_eq_true, if_false, if_true,
      Source.shiftVal, Source.IntTy.u256, large, false_and, pure, Except.pure]

def zero : PrimTy.uint.Denote := ⟨0, by decide⟩

/-- The actual intrinsic shift returns zero at every saturated runtime count.
No input run or desired output equality is a premise. -/
theorem target_value_saturated {C : Contract} (left : Bool) (state : State C TargetCtx)
    (large : 256 ≤ (TEnv.get (.there .here : Idx TargetCtx (.val .uint)) state.env).val) :
    (target left).evalT state = .ok zero := by
  first
  | rfl
  | have positive := (TEnv.get (.here : Idx TargetCtx (.val .uint)) state.env).property
    simp only [PrimTy.inRange, decide_eq_true_eq] at positive
    have nonnegative : ¬ (TEnv.get (.here : Idx TargetCtx (.val .uint)) state.env).val < 0 := by omega
    have high : ¬ (TEnv.get (.there .here : Idx TargetCtx (.val .uint)) state.env).val < 256 := by omega
    have zeroRange : PrimTy.uint.inRange 0 = true := zero.property
    cases left <;> simp only [target, targetOp, Bool.false_eq_true, if_false, if_true,
      Solidity.Val.evalT, Simple.evalT, BinOp.shortT, BinOp.evalT, BinOp.evalNum,
      BinOp.arithInt, high, nonnegative, TRes.ofOpt, zero, PrimTy.ofInt?,
      Option.bind_some, bind, Except.bind, dif_pos zeroRange]

/-- Complete actual Source state survives a saturated local shift. -/
theorem source_saturated {E : Source.Env} (global : Source.Glob E)
    (frame : Source.Fr) (extra : Nat) (left : Bool)
    (x : Int) (hx : Range x) (k : Int) (hk : Range k) (state : Source.St E)
    (large : 256 ≤ k) :
    (Source.evalE global {frame with checked:=false} (extra+3) (expression left)).run
      (locals x hx k hk,state) =
      (.ok (.val (Source.intWrap Source.IntTy.u256 0)), (locals x hx k hk,state)) := by
  first
  | rfl
  | rw [source_execution, source_value_saturated left x hx k.toNat (by omega)]
    rfl

/-- A genuine Source-to-selected-code result join at saturated counts. Initial
local correspondence supplies the runtime shift amount; neither execution is
assumed. The target result retains the entire saved machine via push. -/
theorem saturated_transport {E : Source.Env} {C : Contract} {L b frameSize : Nat}
    (global : Source.Glob E) (frame : Source.Fr) (extra : Nat) (left : Bool)
    (x : Int) (hx : Range x) (k : Int) (hk : Range k) (source : Source.St E)
    (state : State C TargetCtx) (base : Nat → Fin W) (machine : Machine)
    (represented : StateRepr L b frameSize (Frag.init TargetCtx) state base machine)
    (count : TEnv.get (.there .here : Idx TargetCtx (.val .uint)) state.env =
      Lowering.V07.integerValue Source.IntTy.u256 k hk)
    (large : 256 ≤ k) :
    (Source.evalE global {frame with checked:=false} (extra+3) (expression left)).run
      (locals x hx k hk,source) =
      (.ok (.val (Source.intWrap Source.IntTy.u256 0)), (locals x hx k hk,source)) ∧
    Lowering.V07.IntValueRel Source.IntTy.u256
      (Source.intWrap Source.IntTy.u256 0 : Source.Val E.layout (.int Source.IntTy.u256)) zero ∧
    ∃ word, ReprV .uint zero word ∧
      run (selected (C:=C) b left).code machine = .ok (machine.push word) 0 := by
  first
  | rfl
  | have high : 256 ≤ (TEnv.get (.there .here : Idx TargetCtx (.val .uint)) state.env).val := by
      rw [count]
      exact large
    have actual := selected_execution left state base machine represented
    rw [target_value_saturated left state high] at actual
    refine ⟨source_saturated global frame extra left x hx k hk source large, (by rfl), ?_⟩
    rcases actual with ⟨value,word,equal,related,ran⟩ | ⟨bad,_⟩
    · cases equal
      exact ⟨word,related,ran⟩
    · cases bad

/-- The mathematical result word, with the exact existing SHL/SHR saturation.
This is an output observation, not a new evaluator. -/
def resultWord (left : Bool) (x k : Fin W) : Fin W :=
  if left then
    if k.val < 256 then wmod (x.val * 2^k.val) else ⟨0,W_pos⟩
  else
    if k.val < 256 then
      ⟨x.val / 2^k.val, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt⟩
    else ⟨0,W_pos⟩

theorem word_range (x : Fin W) : Range (x.val : Int) := by
  first
  | omega
  | change 0 ≤ (x.val : Int) ∧ (x.val : Int) ≤ ((2^256-1 : Nat) : Int)
    have bound : x.val < 2^256 := x.isLt
    omega

theorem selected_code {C : Contract} (b : Nat) (left : Bool) :
    (selected (C:=C) b left).code =
      [.mload (b+1),.mload b,if left then .shl else .shr] := by
  first | rfl | (cases left <;> rfl)

/-- Exact emitted execution from actual runtime local words. All fields of m
other than the newly pushed word, including its saved stack tail, are retained. -/
theorem runtime_execution {C : Contract} (b : Nat) (left : Bool) (x k : Fin W)
    (m : Machine) (value : m.mem (b+1) = .val x) (amount : m.mem b = .val k) :
    run (selected (C:=C) b left).code m = .ok (m.push (.val (resultWord left x k))) 0 := by
  first
  | rfl
  | cases left <;> simp only [selected_code, Bool.false_eq_true, if_false, if_true,
      run, exec, Instr.step, Out.bind, Machine.next, Machine.push, value, amount, resultWord]

theorem wrapped_word (x : Fin W) : Source.IntTy.u256.wrap (x.val : Int) = (x.val : Int) := by
  first
  | rfl
  | change (x.val : Int) % (W : Int) = (x.val : Int)
    have bound := x.isLt
    apply Int.emod_eq_of_lt <;> omega

/-- Independent Source shift and the actual native result agree at EVERY
runtime word count, with no admitted length/depth cutoff. -/
theorem source_word_value {D : Source.Layout} (left : Bool) (x k : Fin W) :
    Source.shiftVal false (sourceOp left) k.val
      (.int (x.val : Int) (word_range x) : Source.Val D (.int Source.IntTy.u256)) =
      .ok (.int ((resultWord left x k).val : Int) (word_range (resultWord left x k))) := by
  first
  | rfl
  | have high : (256 ≤ k.val) ↔ ¬ k.val < 256 := by omega
    cases left <;> by_cases low : k.val < 256 <;>
      simp only [sourceOp, Source.shiftVal, Source.IntTy.u256, Bool.false_eq_true,
        false_and, if_false, if_true, resultWord, high, low, not_true_eq_false,
        not_false_eq_true, pure, Except.pure] <;> try rfl
    · have input : Source.wrapBits false 256 (x.val : Int) = (x.val : Int) := wrapped_word x
      rw [input, Int.toNat_natCast]
      have bound : x.val / 2^k.val < W :=
        Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt
      have result := wrapped_word (⟨x.val / 2^k.val,bound⟩ : Fin W)
      unfold Source.intWrap
      congr 2
    · have product : Source.IntTy.u256.wrap ((x.val : Int) * 2^k.val) =
          ((wmod (x.val * 2^k.val)).val : Int) := by
        change ((x.val : Int) * (2 : Int)^k.val) % (W : Int) =
          (((x.val * 2^k.val) % W : Nat) : Int)
        rw [Int.natCast_emod, Int.natCast_mul, Int.natCast_pow]
        rfl
      unfold Source.intWrap
      congr 2

/-- General unchecked uint256 local-to-selected-code transport. The two
memory equations are INITIAL operand representations, not execution premises.
Actual Source and emitted execution, typed value agreement, entire unchanged
Source machine and entire saved target machine are all conclusions. -/
theorem transport {E : Source.Env} {C : Contract} (global : Source.Glob E)
    (frame : Source.Fr) (extra b : Nat) (left : Bool) (x k : Fin W)
    (state : Source.St E) (machine : Machine)
    (value : machine.mem (b+1) = .val x) (amount : machine.mem b = .val k) :
    (Source.evalE global {frame with checked:=false} (extra+3) (expression left)).run
      (locals (x.val : Int) (word_range x) (k.val : Int) (word_range k),state) =
      (.ok (.val (.int ((resultWord left x k).val : Int) (word_range (resultWord left x k)))),
        (locals (x.val : Int) (word_range x) (k.val : Int) (word_range k),state)) ∧
    run (selected (C:=C) b left).code machine =
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
  | refine ⟨?_,runtime_execution (C:=C) b left x k machine value amount,
        Lowering.V07.integer_related _ _ _, ReprV.uint_of rfl⟩
    rw [source_execution global frame extra left (x.val : Int) (word_range x)
      (k.val : Int) (word_range k) state]
    simp only [Int.toNat_natCast, source_word_value, Except.map]

theorem result_zero_count (left : Bool) (x : Fin W) :
    resultWord left x ⟨0,W_pos⟩ = x := by
  first
  | rfl
  | cases left <;> simp only [resultWord, Bool.false_eq_true, if_false, if_true,
      Nat.zero_lt_succ, Nat.pow_zero, Nat.mul_one, Nat.div_one, wmod_of_lt x.isLt]

theorem result_saturated (left : Bool) (x k : Fin W) (large : 256 ≤ k.val) :
    resultWord left x k = ⟨0,W_pos⟩ := by
  first
  | rfl
  | have high : ¬ k.val < 256 := by omega
    cases left <;> simp only [resultWord, Bool.false_eq_true, if_false, if_true, high]

end Solidity.Backend.PrimitivePackets.Shifts

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.public_selection' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.public_selection

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.selected_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.selected_execution

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.source_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.source_execution

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.source_value_saturated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.source_value_saturated

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.target_value_saturated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.target_value_saturated

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.source_saturated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.source_saturated

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.saturated_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.saturated_transport


/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.TargetCtx' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.TargetCtx

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.SourceCtx' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.SourceCtx

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.targetOp' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.targetOp

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.sourceOp' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.sourceOp

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.target' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.target

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.selected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.selected

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.expression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.expression

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.Range' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.Range

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.locals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.locals

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.zero' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.zero

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.resultWord' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.resultWord

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.word_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.word_range

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.selected_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.selected_code

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.runtime_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.runtime_execution

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.wrapped_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.wrapped_word

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.source_word_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.source_word_value

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.transport

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.result_zero_count' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.result_zero_count

/-- info: 'Solidity.Backend.PrimitivePackets.Shifts.result_saturated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.PrimitivePackets.Shifts.result_saturated
