import Solidity.Yul.Compilation.ShapeCapacity
import Solidity.Yul.Compilation.ScopedStatements
import Solidity.Backend.Selection.FrameCapacityV2
/-! Exact actual-trace spare words for the existing nonvacuous V2 frame type.
Execution/operand existence and capacity remain distinct. The whole unchanged
heightTrace, including entry/exit, determines peak; no code-length allowance or
final-height-only substitute. This is scalar capacity, not native/G24 adequacy. -/
namespace Solidity.Yul.Compilation.TraceFrameCapacity
open Backend Scalar

private def ceiling : List Int → Int
 | [] => 0
 | h::rest => max h (ceiling rest)

private theorem ceiling_nonnegative (xs : List Int) : 0 ≤ ceiling xs := by
 induction xs with
 | nil => decide
 | cons h rest ih => exact Int.le_trans ih (Int.le_max_right h (ceiling rest))

private theorem ceiling_upper (xs : List Int) : ∀ h, h ∈ xs → h ≤ ceiling xs := by
 induction xs with
 | nil => intro h member; cases member
 | cons x rest ih =>
   intro h member
   rcases List.mem_cons.mp member with same | inside
   · subst h; exact Int.le_max_left x (ceiling rest)
   · exact Int.le_trans (ih h inside) (Int.le_max_right x (ceiling rest))

private theorem ceiling_attained (xs : List Int) : ceiling xs = 0 ∨ ceiling xs ∈ xs := by
 induction xs with
 | nil => exact Or.inl rfl
 | cons h rest ih =>
   by_cases below : h ≤ ceiling rest
   · change max h (ceiling rest) = 0 ∨ max h (ceiling rest) ∈ h::rest
     rw [Int.max_eq_right below]
     rcases ih with zero | member
     · exact Or.inl zero
     · exact Or.inr (List.mem_cons_of_mem h member)
   · change max h (ceiling rest) = 0 ∨ max h (ceiling rest) ∈ h::rest
     rw [Int.max_eq_left (by omega)]
     exact Or.inr List.mem_cons_self

/-- Computed extra height above entry, using the actual zero-based trace. -/
def peak (p : Program) : Nat := (ceiling (heightTrace p 0)).toNat

private theorem entry (p : Program) : (0 : Int) ∈ heightTrace p 0 := by
 cases p <;> exact List.mem_cons_self

/-- The computed maximum is attained, and bounds every actual boundary. -/
theorem peak_spec (p : Program) :
 (peak p : Int) ∈ heightTrace p 0 ∧ ∀ h, h ∈ heightTrace p 0 → h ≤ (peak p : Int) := by
 have same : (peak p : Int) = ceiling (heightTrace p 0) := by
   simp only [peak]
   have bound := ceiling_nonnegative (heightTrace p 0)
   omega
 rw [same]
 constructor
 · rcases ceiling_attained (heightTrace p 0) with zero | member
   · rw [zero]; exact entry p
   · exact member
 · exact ceiling_upper (heightTrace p 0)

private theorem peak_member (p : Program) (height : Nat) :
 ((height+peak p : Nat) : Int) ∈ heightTrace p (height : Int) := by
 have shifted := ShapeCapacity.trace_shift p 0 (height : Int)
 simp only [Int.zero_add] at shifted
 rw [shifted]
 exact List.mem_map.mpr ⟨(peak p : Int),(peak_spec p).1,by omega⟩

/-- Given genuine base capacity, this is the EXACT admitted extra-height
condition, not merely a conservative estimate or an empty caller domain. -/
theorem capacity_iff (p : Program) (height extra : Nat)
 (base : stackBound p (height : Int) = true) :
 stackBound p ((height+extra : Nat) : Int) = true ↔ height+extra+peak p ≤ 1024 := by
 constructor
 · intro capacity
   have safe := List.all_eq_true.mp capacity _ (peak_member p (height+extra))
   have bounds : 0 ≤ ((height+extra+peak p : Nat) : Int) ∧
     ((height+extra+peak p : Nat) : Int) ≤ 1024 := of_decide_eq_true safe
   omega
 · intro room
   change stackBound p ((height : Int)+(extra : Int)) = true
   apply (ShapeCapacity.capacity_shift p (height : Int) (extra : Int)).mpr
   intro h member
   have safe := List.all_eq_true.mp base h member
   have low : 0 ≤ h ∧ h ≤ 1024 := of_decide_eq_true safe
   have shifted := ShapeCapacity.trace_shift p 0 (height : Int)
   simp only [Int.zero_add] at shifted
   rw [shifted] at member
   obtain ⟨raw,rawMember,same⟩ := List.mem_map.mp member
   have high := (peak_spec p).2 raw rawMember
   constructor <;> omega

/-- Actual run plus checked empty-tail capacity inhabit the EXISTING V2
contract. Its all-caller capacity field is proved from the attained peak. -/
def frame (p : Program) (input output : Stack)
 (ran : Scalar.run p input = some output) (bounded : stackBound p (input.length : Int) = true) :
 Selection.V2.FrameCertificate input output where
 code := p
 peak := peak p
 inputRoom := by
   have room := (capacity_iff p input.length 0 bounded).mp (by simpa only [Nat.add_zero] using bounded)
   simpa only [Nat.add_zero] using room
 frame := fun tail => Scalar.run_frame ran tail
 capacity := by
   intro tail room
   have admitted : input.length+tail.length+peak p ≤ 1024 := by
     simpa only [List.length_append] using room
   simpa only [List.length_append] using (capacity_iff p input.length tail.length bounded).mpr admitted

/-- The executable check is real capacity; failure does not erase the gasless
run law or claim source/native refusal. -/
def frame? (p : Program) (input output : Stack) (ran : Scalar.run p input = some output) :
 Option (Selection.V2.FrameCertificate input output) :=
 if bounded : stackBound p (input.length : Int) = true then some (frame p input output ran bounded) else none

/-- Real original-expression compiler correctness supplies the run premise. -/
def expression {fuel n r : Nat} {expr : Solidity.Yul.Expr [] [] n r}
 (compiled : ProducerExpressions.Compiled fuel expr) (depth : Nat) (p : Program)
 (emitted : compiled.lowered.code depth = some p)
 (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
 (bounded : stackBound p ((newer.toList++locals.toList).length : Int) = true) :
 Selection.V2.FrameCertificate (newer.toList++locals.toList)
   (compiled.value locals::(newer.toList++locals.toList)) :=
 frame p _ _ (by simpa only [List.append_nil] using compiled.lowered.correct depth p emitted locals newer []) bounded

/-- Real original-statement compiler correctness supplies the exact update. -/
def statement {fuel n : Nat} {c : Solidity.Yul.Control} {stmt : Solidity.Yul.Stmt [] [] c n}
 (compiled : ProducerStatements.Compiled fuel stmt) (depth : Nat) (p : Program)
 (emitted : compiled.lowered.code depth = some p)
 (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
 (bounded : stackBound p ((newer.toList++locals.toList).length : Int) = true) :
 Selection.V2.FrameCertificate (newer.toList++locals.toList)
   (newer.toList++(compiled.update locals).toList) :=
 frame p _ _ (by simpa only [List.append_nil] using compiled.lowered.correct depth p emitted locals newer []) bounded

/-- info: 'Solidity.Yul.Compilation.TraceFrameCapacity.peak_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms peak_spec
/-- info: 'Solidity.Yul.Compilation.TraceFrameCapacity.capacity_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms capacity_iff
/-- info: 'Solidity.Yul.Compilation.TraceFrameCapacity.frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms frame
/-- info: 'Solidity.Yul.Compilation.TraceFrameCapacity.frame?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms frame?
/-- info: 'Solidity.Yul.Compilation.TraceFrameCapacity.expression' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms expression
/-- info: 'Solidity.Yul.Compilation.TraceFrameCapacity.statement' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms statement
end Solidity.Yul.Compilation.TraceFrameCapacity
