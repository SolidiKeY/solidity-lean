import Solidity.Yul.Compilation.NestedWrites

/-!
# Depth-indexed consumer lowering

These are compiler outputs indexed by their word evaluator/update, not a new
source AST. VY1 can supply its actual constructor denotations at this boundary.
All accepted code is concrete PUSH/DUP/numeric/SWAP/POP. Temporary prefixes,
local bounds, right-before-left operand order and refusal remain explicit.
-/
namespace Solidity.Yul.Compilation
open Backend Scalar

/-- A compiled expression may refuse an inaccessible local depth. Capacity
is a separate property of the emitted instruction trace. -/
structure LoweredExpr (n : Nat) (value : Vector Word n → Word) where
  code : Nat → Option Program
  correct : ∀ (depth : Nat) (p : Program), code depth = some p →
    ∀ (locals : Vector Word n) (newer : Vector Word depth) (tail : Stack),
      run p (newer.toList ++ (locals.toList ++ tail)) =
        some (value locals :: (newer.toList ++ (locals.toList ++ tail)))

def lowerLiteral {n : Nat} (value : Word) : LoweredExpr n (fun _ => value) where
  code := fun _ => some [pushWord value]
  correct := by
    intro depth p selected locals newer tail
    cases selected
    simp only [run, step_pushWord, Option.bind_some]

def lowerLocal {n : Nat} (i : Fin n) : LoweredExpr n (fun locals => locals[i.val]) where
  code := fun depth => if h : depth + i.val < 16 then
    some [readSlot ⟨depth + i.val, h⟩] else none
  correct := by
    intro depth p selected locals newer tail
    split at selected
    next h =>
      cases selected
      simp only [run, read_under_prefix, Option.bind_some]
    next h => cases selected

/-- A target primitive selection with its concrete one-instruction law.
The supplied selections below discharge this law by reduction. -/
structure BinarySelection where
  opcode : Op
  value : Word → Word → Word
  correct : ∀ (a b : Word) (tail : Stack),
    Scalar.step (.op opcode) (a :: b :: tail) = some (value a b :: tail)

/-- Right expression runs first; left expression runs one word deeper. Thus
SUB/DIV/etc receive the left operand on top, exactly as the existing executor. -/
def lowerBinary {n : Nat} {left right : Vector Word n → Word}
    (op : BinarySelection) (a : LoweredExpr n left) (b : LoweredExpr n right) :
    LoweredExpr n (fun locals => op.value (left locals) (right locals)) where
  code := fun depth => (b.code depth).bind (fun rb =>
    (a.code (1 + depth)).map (fun la => rb ++ la ++ [.op op.opcode]))
  correct := by
    intro depth p selected locals newer tail
    cases hr : b.code depth with
    | none => simp only [hr, Option.bind_none] at selected; cases selected
    | some rb =>
      cases hl : a.code (1 + depth) with
      | none => simp only [hr, hl, Option.bind_some, Option.map_none] at selected; cases selected
      | some la =>
        simp only [hr, hl, Option.bind_some, Option.map_some] at selected
        cases selected
        apply run_comp (t := left locals :: right locals ::
          (newer.toList ++ (locals.toList ++ tail)))
        · apply run_comp (b.correct depth rb hr locals newer tail)
          have h := a.correct (1 + depth) la hl locals
            (#v[right locals] ++ newer) tail
          simpa only [Vector.toList_append, List.cons_append, List.nil_append] using h
        · simp only [run, op.correct, Option.bind_some]

def selectAdd : BinarySelection := ⟨.ADD, (· + ·), fun _ _ _ => rfl⟩
def selectSub : BinarySelection := ⟨.SUB, (· - ·), fun _ _ _ => rfl⟩
def selectMul : BinarySelection := ⟨.MUL, (· * ·), fun _ _ _ => rfl⟩
def selectAnd : BinarySelection := ⟨.AND, (· &&& ·), fun _ _ _ => rfl⟩

/-- Reuse the existing DIV/MOD dispatch functions, including zero divisor. -/
def selectDiv : BinarySelection :=
  ⟨.DIV, (binary .DIV).getD (fun _ _ => 0), fun _ _ _ => rfl⟩
def selectMod : BinarySelection :=
  ⟨.MOD, (binary .MOD).getD (fun _ _ => 0), fun _ _ _ => rfl⟩

structure UnarySelection where
  opcode : Op
  value : Word → Word
  correct : ∀ (a : Word) (tail : Stack),
    Scalar.step (.op opcode) (a :: tail) = some (value a :: tail)

def lowerUnary {n : Nat} {value : Vector Word n → Word}
    (op : UnarySelection) (a : LoweredExpr n value) :
    LoweredExpr n (fun locals => op.value (value locals)) where
  code := fun depth => (a.code depth).map (fun p => p ++ [.op op.opcode])
  correct := by
    intro depth p selected locals newer tail
    cases ha : a.code depth with
    | none => simp only [ha, Option.map_none] at selected; cases selected
    | some x =>
      simp only [ha, Option.map_some] at selected
      cases selected
      apply run_comp (a.correct depth x ha locals newer tail)
      simp only [run, op.correct, Option.bind_some]

def selectIsZero : UnarySelection :=
  ⟨.ISZERO, (unary .ISZERO).getD (fun _ => 0), fun _ _ => rfl⟩
def selectNot : UnarySelection :=
  ⟨.NOT, (unary .NOT).getD (fun _ => 0), fun _ _ => rfl⟩

def LoweredExpr.congr {n : Nat} {a b : Vector Word n → Word}
    (compiled : LoweredExpr n a) (equal : ∀ locals, a locals = b locals) : LoweredExpr n b where
  code := compiled.code
  correct := by
    intro depth p selected locals newer tail
    rw [← equal locals]
    exact compiled.correct depth p selected locals newer tail

/-- Branch-free selection is valid only for these total pure word expressions.
Both arms and the condition may be evaluated more than once; no effectful or
nondeterministic source operation is admitted by this constructor. -/
def lowerSelect {n : Nat} {condition yes no : Vector Word n → Word}
    (c : LoweredExpr n condition) (a : LoweredExpr n yes) (b : LoweredExpr n no) :
    LoweredExpr n (fun locals => if condition locals = 0 then no locals else yes locals) :=
  let zero := lowerUnary selectIsZero c
  let nonzero := lowerUnary selectIsZero zero
  let chosen := lowerBinary selectAdd (lowerBinary selectMul nonzero a)
    (lowerBinary selectMul zero b)
  chosen.congr (by
    intro locals
    change flag (flag (condition locals == 0) == 0) * yes locals +
      flag (condition locals == 0) * no locals = _
    by_cases hz : condition locals = 0
    · have hb : (condition locals == 0) = true := by
        simp only [beq_iff_eq]; exact hz
      rw [hb]
      change (0#256) * yes locals + (1#256) * no locals = _
      simp only [BitVec.zero_mul, BitVec.one_mul, BitVec.zero_add, hz, ite_true]
    · have hb : (condition locals == 0) = false := by
        simp only [beq_eq_false_iff_ne]; exact hz
      rw [hb]
      change (1#256) * yes locals + (0#256) * no locals = _
      simp only [BitVec.one_mul, BitVec.zero_mul, BitVec.add_zero, hz, ite_false])

/-- A compiled local-state update, with an arbitrary retained temporary prefix. -/
structure LoweredStmt (n : Nat) (update : Vector Word n → Vector Word n) where
  code : Nat → Option Program
  correct : ∀ (depth : Nat) (p : Program), code depth = some p →
    ∀ (locals : Vector Word n) (newer : Vector Word depth) (tail : Stack),
      run p (newer.toList ++ (locals.toList ++ tail)) =
        some (newer.toList ++ ((update locals).toList ++ tail))

def lowerAssign {n : Nat} (i : Fin n) {value : Vector Word n → Word}
    (rhs : LoweredExpr n value) :
    LoweredStmt n (fun locals => locals.set i.val (value locals) i.isLt) where
  code := fun depth => if h : depth + i.val < 16 then
    (rhs.code depth).map (fun expr => expr ++ writeSlot ⟨depth + i.val, h⟩)
    else none
  correct := by
    intro depth p selected locals newer tail
    split at selected
    next h =>
      cases he : rhs.code depth with
      | none => simp only [he, Option.map_none] at selected; cases selected
      | some expr =>
        simp only [he, Option.map_some] at selected
        cases selected
        exact run_comp (rhs.correct depth expr he locals newer tail)
          (write_under_prefix locals newer i h (value locals) tail)
    next h => cases selected

def lowerSkip (n : Nat) : LoweredStmt n id where
  code := fun _ => some []
  correct := by intro depth p selected locals newer tail; cases selected; rfl

def lowerSeq {n : Nat} {first second : Vector Word n → Vector Word n}
    (a : LoweredStmt n first) (b : LoweredStmt n second) :
    LoweredStmt n (fun locals => second (first locals)) where
  code := fun depth => (a.code depth).bind (fun x =>
    (b.code depth).map (fun y => x ++ y))
  correct := by
    intro depth p selected locals newer tail
    cases ha : a.code depth with
    | none => simp only [ha, Option.bind_none] at selected; cases selected
    | some x =>
      cases hb : b.code depth with
      | none => simp only [ha, hb, Option.bind_some, Option.map_none] at selected; cases selected
      | some y =>
        simp only [ha, hb, Option.bind_some, Option.map_some] at selected
        cases selected
        exact run_comp (a.correct depth x ha locals newer tail)
          (b.correct depth y hb (first locals) newer tail)

/-- Consume a finite block of already lowered statements. This is compiler
output composition, not a second source statement syntax. -/
def lowerBlock {n : Nat} :
    List (Σ update : Vector Word n → Vector Word n, LoweredStmt n update) →
      (Σ update : Vector Word n → Vector Word n, LoweredStmt n update)
  | [] => ⟨id, lowerSkip n⟩
  | first :: rest =>
    let suffix := lowerBlock rest
    ⟨(fun locals => suffix.1 (first.1 locals)), lowerSeq first.2 suffix.2⟩

/-- Finite iteration-prefix lowering, not a claim about a source loop's
condition, termination, divergence or execution horizon. -/
def lowerFixedRepeat {n : Nat} {update : Vector Word n → Vector Word n}
    (body : LoweredStmt n update) :
    (count : Nat) → LoweredStmt n (Nat.repeat update count)
  | 0 => lowerSkip n
  | count + 1 => lowerSeq (first := Nat.repeat update count) (second := update)
      (lowerFixedRepeat body count) body

/-- Any accepted compiled update preserves the caller under actual execution. -/
theorem LoweredStmt.caller {n : Nat} {update : Vector Word n → Vector Word n}
    (compiled : LoweredStmt n update) (depth : Nat) (p : Program)
    (selected : compiled.code depth = some p) (locals : Vector Word n)
    (newer : Vector Word depth) (tail : Stack) :
    (run p (newer.toList ++ (locals.toList ++ tail))).map (List.drop (depth + n)) =
      some tail := by
  rw [compiled.correct depth p selected]
  simp only [Option.map_some, ← List.append_assoc]
  exact congrArg some (List.drop_left' (by
    simp only [List.length_append, Vector.length_toList]))

/-- No resource theorem is inferred from scalar execution alone. -/
theorem LoweredExpr.capacity {n : Nat} {value : Vector Word n → Word}
    (compiled : LoweredExpr n value) (depth : Nat) (p : Program)
    (selected : compiled.code depth = some p) (locals : Vector Word n)
    (newer : Vector Word depth) (tail : Stack)
    (bounded : stackBound p ((depth + n + tail.length : Nat) : Int) = true) :
    depth + n + tail.length + 1 ≤ 1024 := by
  have h := run_capacity (compiled.correct depth p selected locals newer tail)
  simp only [List.length_cons, List.length_append, Vector.length_toList] at h
  simpa only [Nat.add_assoc] using h (by simpa only [Nat.add_assoc] using bounded)

#print axioms lowerLiteral
#print axioms lowerLocal
#print axioms lowerSelect
#print axioms lowerUnary
#print axioms lowerBinary
#print axioms lowerAssign
#print axioms lowerSkip
#print axioms lowerFixedRepeat
#print axioms lowerBlock
#print axioms lowerSeq
#print axioms LoweredStmt.caller
#print axioms LoweredExpr.capacity
end Solidity.Yul.Compilation
