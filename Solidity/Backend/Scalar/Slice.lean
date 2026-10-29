import Solidity.Backend.Assembler

/-!
# Independent numeric instruction-slice semantics

Osaka numeric stack slices over the existing `Backend.Instr`, with the top
of stack first. This is a local, gasless relation, with sufficient EVM stack
capacity assumed by an eventual caller. `none` means outside this supported
slice or stack underflow, not a claim about EVM failure observations. No source
compiler or source evaluation occurs in these definitions.
-/
namespace Solidity.Backend.Scalar

abbrev Word := BitVec 256
abbrev Stack := List Word

def flag (b : Bool) : Word := if b then 1 else 0

/-- Unsigned immediate bytes, in code order, most significant first. -/
def immediate (bs : List UInt8) : Word :=
  BitVec.ofNat 256 (ofBytesBE bs)

/-- Unary Osaka numeric operations in this slice. -/
def unary : Op → Option (Word → Word)
  | .ISZERO => some (fun a => flag (a == 0))
  | .NOT => some (fun a => ~~~a)
  | _ => none

/-- The first argument is the top word. Shift counts are on top; EXP's
base is on top. Division by zero is EVM zero, not Solidity failure. -/
def binary : Op → Option (Word → Word → Word)
  | .ADD => some (fun a b => a + b)
  | .SUB => some (fun a b => a - b)
  | .MUL => some (fun a b => a * b)
  | .DIV => some (fun a b => if b == 0 then 0 else BitVec.ofNat 256 (a.toNat / b.toNat))
  | .MOD => some (fun a b => if b == 0 then 0 else BitVec.ofNat 256 (a.toNat % b.toNat))
  | .SDIV => some (fun a b => if b == 0 then 0 else BitVec.ofInt 256 (a.toInt.tdiv b.toInt))
  | .SMOD => some (fun a b => if b == 0 then 0 else BitVec.ofInt 256 (a.toInt.tmod b.toInt))
  | .EXP => some (fun a b => BitVec.ofNat 256 (a.toNat ^ b.toNat))
  | .LT => some (fun a b => flag (a.toNat < b.toNat))
  | .GT => some (fun a b => flag (b.toNat < a.toNat))
  | .SLT => some (fun a b => flag (a.toInt < b.toInt))
  | .SGT => some (fun a b => flag (b.toInt < a.toInt))
  | .EQ => some (fun a b => flag (a == b))
  | .AND => some (fun a b => a &&& b)
  | .OR => some (fun a b => a ||| b)
  | .XOR => some (fun a b => a ^^^ b)
  | .SHL => some (fun a b => if a.toNat < 256 then b <<< a.toNat else 0)
  | .SHR => some (fun a b => if a.toNat < 256 then b >>> a.toNat else 0)
  | .SAR => some (fun a b => if a.toNat < 256 then
      BitVec.ofInt 256 (b.toInt / (2 ^ a.toNat : Int))
      else if b.toInt < 0 then BitVec.ofInt 256 (-1) else 0)
  | .SIGNEXTEND => some (fun a b => if a.toNat < 32 then
      let bits := 8 * (a.toNat + 1)
      let low := b.toNat % 2 ^ bits
      BitVec.ofInt 256 (if low < 2 ^ (bits - 1) then (low : Int)
        else (low : Int) - (2 ^ bits : Nat))
      else b)
  | _ => none

/-- ADDMOD/MULMOD have an unbounded intermediate, reduced only at the end. -/
def ternary : Op → Option (Word → Word → Word → Word)
  | .ADDMOD => some (fun a b k => if k == 0 then 0
      else BitVec.ofNat 256 ((a.toNat + b.toNat) % k.toNat))
  | .MULMOD => some (fun a b k => if k == 0 then 0
      else BitVec.ofNat 256 ((a.toNat * b.toNat) % k.toNat))
  | _ => none

def applyUnary (f : Word → Word) : Stack → Option Stack
  | a :: st => some (f a :: st)
  | _ => none

def applyBinary (f : Word → Word → Word) : Stack → Option Stack
  | a :: b :: st => some (f a b :: st)
  | _ => none

def applyTernary (f : Word → Word → Word → Word) : Stack → Option Stack
  | a :: b :: k :: st => some (f a b k :: st)
  | _ => none

/-- DUPn's existing opcode index is zero-based. -/
def duplicate (n : Nat) (st : Stack) : Option Stack :=
  st[n]?.map (fun a => a :: st)

/-- Replace one stack cell, returning its previous word. -/
def exchange (a : Word) : Nat → Stack → Option (Word × Stack)
  | 0, b :: st => some (b, a :: st)
  | n + 1, b :: st => (exchange a n st).map (fun p => (p.1, b :: p.2))
  | _, [] => none

def swap (n : Nat) : Stack → Option Stack
  | a :: st => (exchange a n st).map (fun p => p.1 :: p.2)
  | [] => none

def pop : Stack → Option Stack
  | _ :: st => some st
  | [] => none

/-- Numeric dispatch is separate from the real stack-operation families. -/
def numericStep (o : Op) (st : Stack) : Option Stack :=
  match unary o with
  | some f => applyUnary f st
  | none => match binary o with
    | some f => applyBinary f st
    | none => match ternary o with
      | some f => applyTernary f st
      | none => none

/-- One instruction from the independently specified numeric/stack slice. -/
def step : Instr → Stack → Option Stack
  | .push _ bs, st => some (immediate bs.toList :: st)
  | .op o, st => match o with
    | .DUP n => duplicate n.val st
    | .SWAP n => swap n.val st
    | .POP => pop st
    | _ => numericStep o st

/-- A whole straight-line slice; no jumps or source semantics. -/
def run : Program → Stack → Option Stack
  | [], st => some st
  | i :: p, st => (step i st).bind (run p)

/-- Sequential code composition, including slice failure. -/
theorem run_append (p q : Program) (st : Stack) :
    run (p ++ q) st = (run p st).bind (run q) := by
  induction p generalizing st with
  | nil => rfl
  | cons i p ih =>
    simp only [List.cons_append, run]
    rw [Option.bind_assoc]
    cases step i st with
    | none => rfl
    | some t => exact ih t

/-- Successful sequential slices compose without changing the remaining stack. -/
theorem run_comp {p q : Program} {s t u : Stack}
    (hp : run p s = some t) (hq : run q t = some u) :
    run (p ++ q) s = some u := by
  rw [run_append, hp]
  exact hq

/-- A one-byte immediate really is a PUSH1, not a symbolic pseudo instruction. -/
def pushByte (b : UInt8) : Instr := .push ⟨1, by decide⟩ #v[b]

theorem step_pushByte (b : UInt8) (st : Stack) :
    step (pushByte b) st = some (BitVec.ofNat 256 b.toNat :: st) := by
  change some (BitVec.ofNat 256 (0 * 256 + b.toNat) :: st) = _
  rw [Nat.zero_mul, Nat.zero_add]

/-- Extending a successful unary input preserves the extra tail. -/
theorem applyUnary_frame (f : Word → Word) {s t : Stack}
    (h : applyUnary f s = some t) (tail : Stack) :
    applyUnary f (s ++ tail) = some (t ++ tail) := by
  cases s with
  | nil => cases h
  | cons a s => cases h; rfl

theorem applyBinary_frame (f : Word → Word → Word) {s t : Stack}
    (h : applyBinary f s = some t) (tail : Stack) :
    applyBinary f (s ++ tail) = some (t ++ tail) := by
  cases s with
  | nil => cases h
  | cons a s =>
    cases s with
    | nil => cases h
    | cons b s => cases h; rfl

theorem applyTernary_frame (f : Word → Word → Word → Word) {s t : Stack}
    (h : applyTernary f s = some t) (tail : Stack) :
    applyTernary f (s ++ tail) = some (t ++ tail) := by
  cases s with
  | nil => cases h
  | cons a s =>
    cases s with
    | nil => cases h
    | cons b s =>
      cases s with
      | nil => cases h
      | cons k s => cases h; rfl

theorem duplicate_frame (n : Nat) {s t : Stack}
    (h : duplicate n s = some t) (tail : Stack) :
    duplicate n (s ++ tail) = some (t ++ tail) := by
  cases hh : s[n]? with
  | none => simp only [duplicate, hh, Option.map_none, reduceCtorEq] at h
  | some a =>
    simp only [duplicate, hh, Option.map_some, Option.some.injEq] at h
    subst t
    rw [duplicate, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hh).1, hh]
    rfl

theorem exchange_frame (a : Word) (n : Nat) {s t : Stack} {b : Word}
    (h : exchange a n s = some (b, t)) (tail : Stack) :
    exchange a n (s ++ tail) = some (b, t ++ tail) := by
  induction n generalizing s t with
  | zero =>
    cases s with
    | nil => cases h
    | cons x s => cases h; rfl
  | succ n ih =>
    cases s with
    | nil => cases h
    | cons x s =>
      obtain ⟨⟨y, ys⟩, hh, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      rcases he with ⟨rfl, rfl⟩
      simp only [List.cons_append, exchange, ih hh, Option.map_some]

theorem swap_frame (n : Nat) {s t : Stack}
    (h : swap n s = some t) (tail : Stack) :
    swap n (s ++ tail) = some (t ++ tail) := by
  cases s with
  | nil => cases h
  | cons a s =>
    obtain ⟨⟨b, bs⟩, hh, he⟩ := Option.map_eq_some_iff.mp h
    subst t
    simp only [List.cons_append, swap, exchange_frame a n hh tail, Option.map_some]

theorem pop_frame {s t : Stack} (h : pop s = some t) (tail : Stack) :
    pop (s ++ tail) = some (t ++ tail) := by
  cases s with
  | nil => cases h
  | cons a s => cases h; rfl

theorem numericStep_frame {o : Op} {s t : Stack} (h : numericStep o s = some t)
    (tail : Stack) : numericStep o (s ++ tail) = some (t ++ tail) := by
  cases hu : unary o with
  | some f =>
    simp only [numericStep, hu] at h ⊢
    exact applyUnary_frame f h tail
  | none =>
    cases hb : binary o with
    | some f =>
      simp only [numericStep, hu, hb] at h ⊢
      exact applyBinary_frame f h tail
    | none =>
      cases ht : ternary o with
      | some f =>
        simp only [numericStep, hu, hb, ht] at h ⊢
        exact applyTernary_frame f h tail
      | none => simp only [numericStep, hu, hb, ht, reduceCtorEq] at h

/-- Successful instructions never read beyond their operands. -/
theorem step_frame {i : Instr} {s t : Stack} (h : step i s = some t)
    (tail : Stack) : step i (s ++ tail) = some (t ++ tail) := by
  cases i with
  | push n bs => cases h; rfl
  | op o =>
    cases o <;> simp only [step] at h ⊢
    case DUP n => exact duplicate_frame n.val h tail
    case SWAP n => exact swap_frame n.val h tail
    case POP => exact pop_frame h tail
    all_goals exact numericStep_frame h tail

/-- Arbitrary successful slices preserve any untouched suffix. -/
theorem run_frame {p : Program} {s t : Stack} (h : run p s = some t)
    (tail : Stack) : run p (s ++ tail) = some (t ++ tail) := by
  induction p generalizing s with
  | nil => cases h; rfl
  | cons i p ih =>
    cases hs : step i s with
    | none => simp only [run, hs, Option.bind_none, reduceCtorEq] at h
    | some u =>
      simp only [run, hs, Option.bind_some] at h
      rw [run, step_frame hs tail]
      exact ih h

/-- Emit every word as a concrete, well-sized PUSH32. -/
def pushWord (w : Word) : Instr := .push ⟨32, by decide⟩ (toBytesBE 32 w.toNat)

theorem step_pushWord (w : Word) (st : Stack) :
    step (pushWord w) st = some (w :: st) := by
  have h : w.toNat < 256 ^ 32 := w.isLt
  simp only [pushWord, step, immediate, ofBytesBE_toBytesBE 32 w.toNat h]
  have hw : BitVec.ofNat 256 w.toNat = w := by
    apply BitVec.eq_of_toNat_eq
    exact Nat.mod_eq_of_lt w.isLt
  rw [hw]

/-- The emitted immediate is really 33 bytes including its opcode. -/
theorem encode_pushWord (w : Word) :
    (pushWord w).encode = 0x7f :: (toBytesBE 32 w.toNat).toList := rfl

/-- A noncommutative positive control: top operand is the minuend. -/
example : run [.op .SUB] [7, 3, 99] = some [4, 99] := by decide +kernel

/-- Negative control: swapping SUB inputs changes its result. -/
example : run [.op .SUB] [3, 7, 99] ≠ some [4, 99] := by decide +kernel

/-- EVM zero division is successful zero, so Solidity needs a guard. -/
example : run [.op .DIV] [7, 0, 99] = some [0, 99] := by decide +kernel

/-- Modulo arithmetic is wide before reduction, unlike ADD followed by MOD. -/
example : run [.op .ADDMOD] [BitVec.ofInt 256 (-1), 1, 7, 99] =
    some [2, 99] := by decide +kernel


/-- info: 'Solidity.Backend.Scalar.unary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms unary
/-- info: 'Solidity.Backend.Scalar.binary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms binary
/-- info: 'Solidity.Backend.Scalar.ternary' does not depend on any axioms -/
#guard_msgs in #print axioms ternary
/-- info: 'Solidity.Backend.Scalar.step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms step
/-- info: 'Solidity.Backend.Scalar.run_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms run_append
/-- info: 'Solidity.Backend.Scalar.run_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms run_frame
/-- info: 'Solidity.Backend.Scalar.step_pushWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_pushWord

end Solidity.Backend.Scalar
