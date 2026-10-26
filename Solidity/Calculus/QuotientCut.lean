import Solidity.Calculus.FlattenReads
import Solidity.Calculus.BitArith

/-!
# Operators cut out of a leaf into fresh atoms

The arithmetic compiler encodes a scalar term as one affine code.  An
operator that is not affine in its operand's code (a quotient, a word
conversion, wrapping arithmetic) is cut out of the leaf first: each such
node is replaced by a fresh atom `q`, sequenced after the operands it
needs (`seq g q`), and the atom's defining equation `g == g → e == q`
(`LFml.defn`, `e` the node) goes to the antecedent.  Where the operands
return the equation pins `q` to the node's value; where they fail, the node
fails, and so does its replacement.  So the leaf is valid exactly when the
cut one is, in a universal reading of the fresh atoms (`LFml.cutAll_valid_iff`);
a countermodel of the cut leaf refutes the leaf at the same point
(`LFml.holds_cutAll`).

A node written twice gets one atom (`quotAtom` finds its earlier
definition).  A remainder and a left shift by a literal are written through the
quotient's atom (`a % c` as `a - q * c`, `a << n` as
`(a - q * 2^(256-n)) * 2^n`, `q` the atom of `a / c`, `a / 2^(256-n)`); the
compiler encodes the defining equations exactly
(`Calculus/CheckedLinear.lean`, `StorageEncoding.special?`).
-/

namespace Solidity.Decide

open Semantics

variable {C : Contract}

/-! ## Literals -/

theorem uint_inRange_pow {k : Nat} (hk : k < 256) : PrimTy.uint.inRange ((2 ^ k : Nat) : Int) = true := by
  have h : 2 ^ k < 2 ^ 256 := Nat.pow_lt_pow_right (by decide) hk
  simp only [PrimTy.inRange, decide_eq_true_eq]
  exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr h⟩

/-- `2^k` as a `uint` literal. -/
def uintPow (k : Nat) (hk : k < 256) : PrimTy.uint.Denote := ⟨((2 ^ k : Nat) : Int), uint_inRange_pow hk⟩

/-! ## Cut terms -/

/-- The definition of the atom `k`: where `g` returns, `e` returns `k`'s value. -/
def LFml.defn {p r : PrimTy} (g : LTm C (.val p)) (e : LTm C (.val r)) (k : Nat) : LFml C :=
  .imp (.eq g g) (.eq e (.var k))

/-- Every definition holds. -/
def LFml.AllHold (g : State C []) (ν : AEnv) (ds : List (LFml C)) : Prop := ∀ d ∈ ds, d.holds g ν

/-- The conjunction of the definitions. -/
def LFml.conj : List (LFml C) → LFml C
  | [] => .tt
  | [d] => d
  | d :: ds => .and d (LFml.conj ds)

/-- A term with its cut operators replaced by fresh atoms: the term, the
atoms' definitions in the order they were made, the next free atom. -/
structure CutTm (C : Contract) (s : Srt) where
  term : LTm C s
  defs : List (LFml C)
  next : Nat

/-- `a - q * c`: the remainder through the quotient's atom `q`. -/
def LTm.remOf (a : LTm C (.val .uint)) (q : Nat) (c : PrimTy.uint.Denote) : LTm C (.val .uint) :=
  .app2 (.binop .sub rfl) a (.app2 (.binop .mul rfl) (.var q) (.app0 (.lit c)))

/-- `a / c` at `uint`. -/
def LTm.divLit (a : LTm C (.val .uint)) (c : PrimTy.uint.Denote) : LTm C (.val .uint) :=
  .app2 (.binop .div rfl) a (.app0 (.lit c))

/-- The atom `m` of a definition `defn g e m`, the terms compared by identity. -/
def LFml.defnAtom? {p r : PrimTy} (g : LTm C (.val p)) (e : LTm C (.val r)) : LFml C → Option Nat
  | .imp (.eq g₁ g₂) (.eq e₁ (.var m)) =>
    if g₁.beqR g && g₂.beqR g && e₁.beqR e then some m else none
  | _ => none

/-- The atom an earlier definition gives `e` after `g`. -/
def LFml.findAtom? {p r : PrimTy} (g : LTm C (.val p)) (e : LTm C (.val r)) :
    List (LFml C) → Option Nat
  | [] => none
  | d :: ds =>
    match LFml.defnAtom? g e d with
    | some m => some m
    | none => LFml.findAtom? g e ds

/-- **The atom of the node `e` after `g`**: one an earlier definition (in
`prev` or `ds`) already gives it, so that a node written twice is one atom;
else `m`, defined now.  The atom, the definitions made, the next free atom. -/
def quotAtom {p r : PrimTy} (prev ds : List (LFml C)) (g : LTm C (.val p)) (e : LTm C (.val r))
    (m : Nat) : Nat × List (LFml C) × Nat :=
  match LFml.findAtom? g e (prev ++ ds) with
  | some k => (k, ds, m)
  | none => (m, ds ++ [LFml.defn g e m], m + 1)

/-- The node `e` replaced by its atom, sequenced after `g`. -/
def CutTm.atom {p r : PrimTy} (prev ds : List (LFml C)) (g : LTm C (.val p)) (e : LTm C (.val r))
    (m : Nat) : CutTm C (.val r) :=
  ⟨.seq g (.var (quotAtom prev ds g e m).1), (quotAtom prev ds g e m).2.1,
    (quotAtom prev ds g e m).2.2⟩

/-- `a % c` through the atom of `a / c`. -/
def CutTm.rem (prev : List (LFml C)) (a : LTm C (.val .uint)) (c : PrimTy.uint.Denote)
    (ds : List (LFml C)) (m : Nat) : CutTm C (.val .uint) :=
  ⟨a.remOf (quotAtom prev ds a (a.divLit c) m).1 c, (quotAtom prev ds a (a.divLit c) m).2.1,
    (quotAtom prev ds a (a.divLit c) m).2.2⟩

/-- `a << k` (`0 < k < 256`): `(a % 2^(256-k)) * 2^k`, the remainder through
the atom of `a / 2^(256-k)`. -/
def CutTm.shl (prev : List (LFml C)) (a : LTm C (.val .uint)) (k : Nat) (hk : 256 - k < 256)
    (hk' : k < 256) (ds : List (LFml C)) (m : Nat) : CutTm C (.val .uint) :=
  ⟨.app2 (.binop .mul rfl)
      (a.remOf (quotAtom prev ds a (a.divLit (uintPow (256 - k) hk)) m).1 (uintPow (256 - k) hk))
      (.app0 (.lit (uintPow k hk'))),
    (quotAtom prev ds a (a.divLit (uintPow (256 - k) hk)) m).2.1,
    (quotAtom prev ds a (a.divLit (uintPow (256 - k) hk)) m).2.2⟩

/-- The `k` of a low mask `2^k - 1`, `k ≤ 256`. -/
def lowMask? (v : PrimTy.uint.Denote) : Option Nat :=
  (List.range 257).find? fun k => decide (((2 ^ k : Nat) : Int) - 1 = v.val)

/-- `a & (2^k - 1)`: `a % 2^k`, through the atom of `a / 2^k`; `a` itself at
`k = 256`. -/
def maskCut (prev : List (LFml C)) (a : LTm C (.val .uint)) (k : Nat) (ds : List (LFml C))
    (m : Nat) : CutTm C (.val .uint) :=
  if hk : k < 256 then CutTm.rem prev a (uintPow k hk) ds m else ⟨a, ds, m⟩

/-- The `k` of a literal low mask `2^k - 1`. -/
def LTm.maskOf? : LTm C (.val .uint) → Option Nat
  | .app0 (.lit v) => lowMask? v
  | _ => none

/-! ## Operators with a literal, written through the cut ones

`x & c`, `x | c`, `x ^ c` and `x *% c` at a literal `c` that is not a low
mask are written through quotient atoms by `2` and wrapped sums: `x & c`
bit by bit from the lowest (`bandGo`: the atom `q` of `x / 2`, the low
bit `x - 2q`, the rest `2 · (q & ⌊c/2⌋)`), `x | c` as `(x - (x & c)) + c`,
`x ^ c` as `(x - (x & c)) + (c - (x & c))`, and `x *% c` by doubling
(`mulWGo`: `x *% c` from `x *% ⌊c/2⌋`, a wrapped sum with itself and, for
an odd `c`, with `x`).  Each stays within the compiler's definitions
(`defDiv`, `defAddW`). -/

/-- `2` at `uint`. -/
def uintTwo : PrimTy.uint.Denote := ⟨2, uint_inRange (by decide) (by decide)⟩

/-- `x & c` for `0 < c < 2^f`, the operand `a` returning: the low bit through the atom of
`a / 2`, the rest after it. -/
def bandGo (prev : List (LFml C)) : Nat → LTm C (.val .uint) → Nat → List (LFml C) → Nat →
    CutTm C (.val .uint)
  | 0, _, _, ds, m => ⟨.app0 (.lit (PrimTy.dflt .uint)), ds, m⟩
  | f + 1, a, c, ds, m =>
    if c / 2 = 0 then
      ⟨a.remOf (quotAtom prev ds a (a.divLit uintTwo) m).1 uintTwo,
        (quotAtom prev ds a (a.divLit uintTwo) m).2.1, (quotAtom prev ds a (a.divLit uintTwo) m).2.2⟩
    else
      let Q := quotAtom prev ds a (a.divLit uintTwo) m
      let R := bandGo prev f (.var Q.1) (c / 2) Q.2.1 Q.2.2
      let hi : LTm C (.val .uint) := .app2 (.binop .mul rfl) (.app0 (.lit uintTwo)) R.term
      if c % 2 = 0 then ⟨hi, R.defs, R.next⟩
      else ⟨.app2 (.binop .add rfl) (a.remOf Q.1 uintTwo) hi, R.defs, R.next⟩

/-- `a & c` at a literal `c`, `a` evaluated first. -/
def bandLit (prev : List (LFml C)) (a : LTm C (.val .uint)) (c : Nat) (ds : List (LFml C)) (m : Nat) :
    CutTm C (.val .uint) :=
  if c = 0 then ⟨.seq a (.app0 (.lit (PrimTy.dflt .uint))), ds, m⟩
  else ⟨.seq a (bandGo prev c a c ds m).term, (bandGo prev c a c ds m).defs,
    (bandGo prev c a c ds m).next⟩

/-- `a | c`: `(a - (a & c)) + c`. -/
def borLit (prev : List (LFml C)) (a : LTm C (.val .uint)) (v : PrimTy.uint.Denote)
    (ds : List (LFml C)) (m : Nat) : CutTm C (.val .uint) :=
  if v.val.toNat = 0 then ⟨a, ds, m⟩
  else ⟨.app2 (.binop .add rfl) (.app2 (.binop .sub rfl) a (bandGo prev v.val.toNat a v.val.toNat ds m).term)
      (.app0 (.lit v)), (bandGo prev v.val.toNat a v.val.toNat ds m).defs, (bandGo prev v.val.toNat a v.val.toNat ds m).next⟩

/-- `a ^ c`: `(a - (a & c)) + (c - (a & c))`. -/
def bxorLit (prev : List (LFml C)) (a : LTm C (.val .uint)) (v : PrimTy.uint.Denote)
    (ds : List (LFml C)) (m : Nat) : CutTm C (.val .uint) :=
  if v.val.toNat = 0 then ⟨a, ds, m⟩
  else ⟨.app2 (.binop .add rfl) (.app2 (.binop .sub rfl) a (bandGo prev v.val.toNat a v.val.toNat ds m).term)
      (.app2 (.binop .sub rfl) (.app0 (.lit v)) (bandGo prev v.val.toNat a v.val.toNat ds m).term),
    (bandGo prev v.val.toNat a v.val.toNat ds m).defs, (bandGo prev v.val.toNat a v.val.toNat ds m).next⟩

/-- `a *% c` for `0 < c < 2^f`: from `a *% ⌊c/2⌋`, doubled by a wrapped sum
and, for an odd `c`, a wrapped sum with `a`; each sum an atom defined after `a`. -/
def mulWGo (prev : List (LFml C)) (a : LTm C (.val .uint)) : Nat → Nat → List (LFml C) → Nat →
    CutTm C (.val .uint)
  | 0, _, ds, m => ⟨a, ds, m⟩
  | f + 1, c, ds, m =>
    if c / 2 = 0 then ⟨a, ds, m⟩
    else
      let H := mulWGo prev a f (c / 2) ds m
      let D := quotAtom prev H.defs a (.app2 (.binop .addW rfl) H.term H.term) H.next
      if c % 2 = 0 then ⟨.seq a (.var D.1), D.2.1, D.2.2⟩
      else
        let E := quotAtom prev D.2.1 a (.app2 (.binop .addW rfl) (.seq a (.var D.1)) a) D.2.2
        ⟨.seq a (.var E.1), E.2.1, E.2.2⟩

/-- `a *% c` at a literal `c`. -/
def mulWLit (prev : List (LFml C)) (a : LTm C (.val .uint)) (c : Nat) (ds : List (LFml C)) (m : Nat) :
    CutTm C (.val .uint) :=
  if c = 0 then ⟨.seq a (.app0 (.lit (PrimTy.dflt .uint))), ds, m⟩ else mulWGo prev a c c ds m

/-- `1` at `uint`. -/
def uintOne : PrimTy.uint.Denote := ⟨1, uint_inRange (by decide) (by decide)⟩

/-- `a ** v`, `a **% v` at `v ∈ {0, 1}`: `1` after `a`, `a`; the node otherwise. -/
def powLit (h : LTm C (.val .uint)) (a : LTm C (.val .uint)) (v : PrimTy.uint.Denote) :
    LTm C (.val .uint) :=
  if v.val = 0 then .seq a (.app0 (.lit uintOne)) else if v.val = 1 then a else h

/-- **The operators the cut writes through others at a literal right
operand**: `&`, `|`, `^`, `*%` (any literal), `**`, `**%` at `0` and `1`,
`/` and `%` at `int` (any literal), `/` and `%` at `uint` by `0`. -/
def litCutR : (op : BinOp) → (p : PrimTy) → p.Denote → Bool
  | .band, .uint, _ | .bor, .uint, _ | .bxor, .uint, _ | .mulW, .uint, _ => true
  | .band, .int, _ | .bor, .int, _ | .bxor, .int, _ => true
  | .pow, .uint, v | .powW, .uint, v => v.val == 0 || v.val == 1
  | .div, .int, _ | .mod, .int, _ => true
  | .div, .uint, v | .mod, .uint, v => v.val == 0
  | _, _, _ => false

/-- At a literal left operand: the commutative ones. -/
def litCutL : BinOp → PrimTy → Bool
  | .band, .uint | .bor, .uint | .bxor, .uint | .mulW, .uint => true
  | .band, .int | .bor, .int | .bxor, .int => true
  | _, _ => false

/-- `a & b` at `uint`, either side a low mask. -/
def cutBand (prev : List (LFml C)) (h : BinOp.band.accepts .uint = true) (A B : CutTm C (.val .uint)) :
    CutTm C (.val .uint) :=
  match B.term.maskOf? with
  | some k => maskCut prev A.term k (A.defs ++ B.defs) B.next
  | none =>
    match A.term.maskOf? with
    | some k => maskCut prev B.term k (A.defs ++ B.defs) B.next
    | none =>
      match B.term.lit?, A.term.lit? with
      | some r, _ => bandLit prev A.term r.1.val.toNat (A.defs ++ B.defs) B.next
      | none, some r => bandLit prev B.term r.1.val.toNat (A.defs ++ B.defs) B.next
      | none, none => ⟨.app2 (.binop .band h) A.term B.term, A.defs ++ B.defs, B.next⟩

/-- An `int` literal's two's complement word. -/
def intWord (v : PrimTy.int.Denote) : PrimTy.uint.Denote :=
  ⟨v.val % Semantics.uintBound, uint_inRange (Int.emod_nonneg _ (by decide)) (Int.emod_lt_of_pos _ (by decide))⟩

/-- **`a ⊙ v` at `int`** (`⊙` one of `&`, `|`, `^`, `v` a literal) through the
words: `int(uint(a) ⊙ word(v))`, each conversion an atom, the `uint`
operator at the literal word written by `mk` (`bandLit`, `borLit`,
`bxorLit`). -/
def intBit (prev : List (LFml C)) (mk : LTm C (.val .uint) → List (LFml C) → Nat → CutTm C (.val .uint))
    (a : LTm C (.val .int)) (ds : List (LFml C)) (m : Nat) : CutTm C (.val .int) :=
  let U := CutTm.atom prev ds a (.app1 (.unop .toUint rfl) a) m
  let T := mk U.term U.defs U.next
  CutTm.atom prev T.defs T.term (.app1 (.unop .toInt rfl) T.term) T.next

/-- The `uint` side of `intBit`, by the operator. -/
def intBitMk (op : BinOp) (prev : List (LFml C)) (v : PrimTy.int.Denote) :
    LTm C (.val .uint) → List (LFml C) → Nat → CutTm C (.val .uint) :=
  match op with
  | .band => fun t ds m => bandLit prev t (intWord v).val.toNat ds m
  | .bor => fun t ds m => borLit prev t (intWord v) ds m
  | _ => fun t ds m => bxorLit prev t (intWord v) ds m

/-- A unary node, its operand cut; `prev` the definitions made before it. -/
def cut1 : {a s : Srt} → Op1 C a s → List (LFml C) → CutTm C a → CutTm C s
  | _, _, .unop .toInt (p := .uint) h, prev, A =>
    CutTm.atom prev A.defs A.term (.app1 (.unop .toInt h) A.term) A.next
  | _, _, .unop .toUint (p := .int) h, prev, A =>
    CutTm.atom prev A.defs A.term (.app1 (.unop .toUint h) A.term) A.next
  | _, _, o, _, A => ⟨.app1 o A.term, A.defs, A.next⟩

/-- `a << v` at `uint`, `a` cut. -/
def cutShl (prev : List (LFml C)) (A : CutTm C (.val .uint)) (v : PrimTy.uint.Denote)
    (ds : List (LFml C)) (m : Nat) : CutTm C (.val .uint) :=
  if h0 : v.val = 0 then ⟨A.term, ds, m⟩
  else if hk : v.val < 256 then
    CutTm.shl prev A.term v.val.toNat (by have := uint_val_nonneg v; omega)
      (by have := uint_val_nonneg v; omega) ds m
  else ⟨.seq A.term (.app0 (.lit (PrimTy.dflt .uint))), ds, m⟩

/-- A binary node, its operands cut. -/
def cut2 : {a b s : Srt} → Op2 C a b s → List (LFml C) → CutTm C a → CutTm C b → CutTm C s
  | _, _, _, .binop .div (p := .uint) h, prev, A, B =>
    match B.term with
    | .app0 (.lit v) =>
      if v.val = 0 then ⟨.seq A.term .err, A.defs ++ B.defs, B.next⟩
      else CutTm.atom prev (A.defs ++ B.defs) A.term (.app2 (.binop .div h) A.term B.term) B.next
    | _ => ⟨.app2 (.binop .div h) A.term B.term, A.defs ++ B.defs, B.next⟩
  | _, _, _, .binop .mod (p := .uint) h, prev, A, B =>
    match B.term with
    | .app0 (.lit v) =>
      if v.val = 0 then ⟨.seq A.term .err, A.defs ++ B.defs, B.next⟩
      else CutTm.rem prev A.term v (A.defs ++ B.defs) B.next
    | _ => ⟨.app2 (.binop .mod h) A.term B.term, A.defs ++ B.defs, B.next⟩
  | _, _, _, .binop .div (p := .int) h, prev, A, B =>
    match B.term with
    | .app0 (.lit v) =>
      if v.val = 0 then ⟨.seq A.term .err, A.defs ++ B.defs, B.next⟩
      else if v.val = -1 then ⟨.app1 (.unop .neg rfl) A.term, A.defs ++ B.defs, B.next⟩
      else CutTm.atom prev (A.defs ++ B.defs) A.term (.app2 (.binop .div h) A.term B.term) B.next
    | _ => ⟨.app2 (.binop .div h) A.term B.term, A.defs ++ B.defs, B.next⟩
  | _, _, _, .binop .mod (p := .int) h, prev, A, B =>
    match B.term with
    | .app0 (.lit v) =>
      if v.val = 0 then ⟨.seq A.term .err, A.defs ++ B.defs, B.next⟩
      else if v.val = -1 then ⟨.seq A.term (.app0 (.lit (PrimTy.dflt .int))), A.defs ++ B.defs, B.next⟩
      else
        let Q := quotAtom prev (A.defs ++ B.defs) A.term (.app2 (.binop .div rfl) A.term B.term) B.next
        ⟨.app2 (.binop .sub rfl) A.term (.app2 (.binop .mul rfl) (.var Q.1) (.app0 (.lit v))), Q.2.1, Q.2.2⟩
    | _ => ⟨.app2 (.binop .mod h) A.term B.term, A.defs ++ B.defs, B.next⟩
  | _, _, _, .binop .pow (p := .uint) h, _, A, B =>
    match B.term with
    | .app0 (.lit v) =>
      ⟨powLit (.app2 (.binop .pow h) A.term B.term) A.term v, A.defs ++ B.defs, B.next⟩
    | _ => ⟨.app2 (.binop .pow h) A.term B.term, A.defs ++ B.defs, B.next⟩
  | _, _, _, .binop .powW (p := .uint) h, _, A, B =>
    match B.term with
    | .app0 (.lit v) =>
      ⟨powLit (.app2 (.binop .powW h) A.term B.term) A.term v, A.defs ++ B.defs, B.next⟩
    | _ => ⟨.app2 (.binop .powW h) A.term B.term, A.defs ++ B.defs, B.next⟩
  | _, _, _, .binop .mulW (p := .uint) h, prev, A, B =>
    match B.term.lit?, A.term.lit? with
    | some r, _ => mulWLit prev A.term r.1.val.toNat (A.defs ++ B.defs) B.next
    | none, some r => mulWLit prev B.term r.1.val.toNat (A.defs ++ B.defs) B.next
    | none, none => ⟨.app2 (.binop .mulW h) A.term B.term, A.defs ++ B.defs, B.next⟩
  | _, _, _, .binop .bor (p := .uint) h, prev, A, B =>
    match B.term.lit?, A.term.lit? with
    | some r, _ => borLit prev A.term r.1 (A.defs ++ B.defs) B.next
    | none, some r => borLit prev B.term r.1 (A.defs ++ B.defs) B.next
    | none, none => ⟨.app2 (.binop .bor h) A.term B.term, A.defs ++ B.defs, B.next⟩
  | _, _, _, .binop .bxor (p := .uint) h, prev, A, B =>
    match B.term.lit?, A.term.lit? with
    | some r, _ => bxorLit prev A.term r.1 (A.defs ++ B.defs) B.next
    | none, some r => bxorLit prev B.term r.1 (A.defs ++ B.defs) B.next
    | none, none => ⟨.app2 (.binop .bxor h) A.term B.term, A.defs ++ B.defs, B.next⟩
  | _, _, _, .binop .shr h, prev, A, B =>
    match B.term with
    | .app0 (.lit _) =>
      CutTm.atom prev (A.defs ++ B.defs) A.term (.app2 (.binop .shr h) A.term B.term) B.next
    | _ => ⟨.app2 (.binop .shr h) A.term B.term, A.defs ++ B.defs, B.next⟩
  | _, _, _, .binop .shl (p := .uint) h, prev, A, B =>
    match B.term with
    | .app0 (.lit v) => cutShl prev A v (A.defs ++ B.defs) B.next
    | _ => ⟨.app2 (.binop .shl h) A.term B.term, A.defs ++ B.defs, B.next⟩
  | _, _, _, .binop .band (p := .uint) h, prev, A, B => cutBand prev h A B
  | _, _, _, .binop .band (p := .int) h, prev, A, B =>
    match B.term.lit?, A.term.lit? with
    | some r, _ => intBit prev (intBitMk .band prev r.1) A.term (A.defs ++ B.defs) B.next
    | none, some r => intBit prev (intBitMk .band prev r.1) B.term (A.defs ++ B.defs) B.next
    | none, none => ⟨.app2 (.binop .band h) A.term B.term, A.defs ++ B.defs, B.next⟩
  | _, _, _, .binop .bor (p := .int) h, prev, A, B =>
    match B.term.lit?, A.term.lit? with
    | some r, _ => intBit prev (intBitMk .bor prev r.1) A.term (A.defs ++ B.defs) B.next
    | none, some r => intBit prev (intBitMk .bor prev r.1) B.term (A.defs ++ B.defs) B.next
    | none, none => ⟨.app2 (.binop .bor h) A.term B.term, A.defs ++ B.defs, B.next⟩
  | _, _, _, .binop .bxor (p := .int) h, prev, A, B =>
    match B.term.lit?, A.term.lit? with
    | some r, _ => intBit prev (intBitMk .bxor prev r.1) A.term (A.defs ++ B.defs) B.next
    | none, some r => intBit prev (intBitMk .bxor prev r.1) B.term (A.defs ++ B.defs) B.next
    | none, none => ⟨.app2 (.binop .bxor h) A.term B.term, A.defs ++ B.defs, B.next⟩
  | _, _, _, .binop .addW (p := .uint) h, prev, A, B =>
    CutTm.atom prev (A.defs ++ B.defs) (.seq A.term B.term) (.app2 (.binop .addW h) A.term B.term)
      B.next
  | _, _, _, .binop .subW (p := .uint) h, prev, A, B =>
    CutTm.atom prev (A.defs ++ B.defs) (.seq A.term B.term) (.app2 (.binop .subW h) A.term B.term)
      B.next
  | _, _, _, o, _, A, B => ⟨.app2 o A.term B.term, A.defs ++ B.defs, B.next⟩

/-! ## `addmod` and `mulmod` at a literal modulus

Each sum modulo `c` of two operands below `c` is one atom, defined by
cases (`amodDef`): `u + v` where `u < c - v`, `u - (c - v)` where not, under
a guard that both are below `c`; the operands are first reduced by `c`
through their quotients' atoms (`CutTm.rem`), and `mulmod` doubles. -/

/-- `c - v` at `uint`. -/
def LTm.subFrom (c : PrimTy.uint.Denote) (v : LTm C (.val .uint)) : LTm C (.val .uint) :=
  .app2 (.binop .sub rfl) (.app0 (.lit c)) v

/-- `v + 1` at `uint`. -/
def LTm.incr (v : LTm C (.val .uint)) : LTm C (.val .uint) :=
  .app2 (.binop .add rfl) v (.app0 (.lit uintOne))

/-- `u < c - v`. -/
def amodCond (u v : LTm C (.val .uint)) (c : PrimTy.uint.Denote) : LFml C :=
  .eq (.app2 (.binop .lt rfl) u (LTm.subFrom c v)) (.app0 (.lit (p := .bool) true))

/-- `g` returns, then `u < c` and `v < c` (`c - (u + 1)` returns). -/
def amodGuard (g u v : LTm C (.val .uint)) (c : PrimTy.uint.Denote) : LTm C (.val .uint) :=
  .seq g (.seq (LTm.subFrom c (LTm.incr u)) (LTm.subFrom c (LTm.incr v)))

/-- **The atom `k` of `(u + v) mod c`** for `u, v < c`, by cases: `u + v`
where `u < c - v`, `u - (c - v)` where not. -/
def amodDef (g u v : LTm C (.val .uint)) (c : PrimTy.uint.Denote) (k : Nat) : LFml C :=
  .imp (.eq (amodGuard g u v c) (amodGuard g u v c))
    (.and (.imp (amodCond u v c) (.eq (.app2 (.binop .add rfl) u v) (.var k)))
      (.imp (.not (amodCond u v c)) (.eq (.app2 (.binop .sub rfl) u (LTm.subFrom c v)) (.var k))))

/-- `(u + v) mod c` as the atom `m`, sequenced after `g`. -/
def amodAtom (g u v : LTm C (.val .uint)) (c : PrimTy.uint.Denote) (ds : List (LFml C)) (m : Nat) :
    CutTm C (.val .uint) :=
  ⟨.seq g (.var m), ds ++ [amodDef g u v c m], m + 1⟩

/-- **`addmod(a, b, c)` at a nonzero literal `c`**: the operands' remainders
by `c` through their quotients' atoms, and one atom for their sum modulo
`c` (`amodAtom`), sequenced after both operands. -/
def addmodLit (prev : List (LFml C)) (a b : LTm C (.val .uint)) (c : PrimTy.uint.Denote)
    (ds : List (LFml C)) (m : Nat) : CutTm C (.val .uint) :=
  let RA := CutTm.rem prev a c ds m
  let RB := CutTm.rem prev b c RA.defs RA.next
  amodAtom (.seq a b) RA.term RB.term c RB.defs RB.next

/-- `x · k mod c` from `x < c` (the term `a`) for `0 < k < 2^f`: doubling,
each step an atom of `amodAtom` sequenced after `a`. -/
def mulmodGo (a : LTm C (.val .uint)) (c : PrimTy.uint.Denote) :
    Nat → Nat → List (LFml C) → Nat → CutTm C (.val .uint)
  | 0, _, ds, m => ⟨a, ds, m⟩
  | f + 1, k, ds, m =>
    if k / 2 = 0 then ⟨a, ds, m⟩
    else
      let H := mulmodGo a c f (k / 2) ds m
      let D := amodAtom a H.term H.term c H.defs H.next
      if k % 2 = 0 then D else amodAtom a D.term a c D.defs D.next

/-- **`mulmod(a, k, c)` at nonzero literal `c` and a literal `k`**: `a`'s
remainder by `c`, times `k mod c` by doubling (`mulmodGo`); `0` after `a`
where `c` divides `k`. -/
def mulmodLit (prev : List (LFml C)) (a : LTm C (.val .uint)) (k c : PrimTy.uint.Denote)
    (ds : List (LFml C)) (m : Nat) : CutTm C (.val .uint) :=
  if k.val.toNat % c.val.toNat = 0 then ⟨.seq a (.app0 (.lit (PrimTy.dflt .uint))), ds, m⟩
  else
    let R := CutTm.rem prev a c ds m
    mulmodGo R.term c (k.val.toNat % c.val.toNat) (k.val.toNat % c.val.toNat) R.defs R.next

/-- A ternary node, its operands cut: `addmod` at a literal modulus
(`addmodLit`), `mulmod` at a literal modulus and a literal factor on either
side (`mulmodLit`), a zero modulus failing after the operands. -/
def cut3 : {a b c s : Srt} → Op3 C a b c s → List (LFml C) → CutTm C a → CutTm C b → CutTm C c →
    CutTm C s
  | _, _, _, _, .modular .addmod, prev, A, B, K =>
    match K.term.lit? with
    | some r =>
      if r.1.val = 0 then ⟨.seq (.seq A.term B.term) .err, A.defs ++ B.defs ++ K.defs, K.next⟩
      else addmodLit prev A.term B.term r.1 (A.defs ++ B.defs ++ K.defs) K.next
    | none => ⟨.app3 (.modular .addmod) A.term B.term K.term, A.defs ++ B.defs ++ K.defs, K.next⟩
  | _, _, _, _, .modular .mulmod, prev, A, B, K =>
    match K.term.lit?, B.term.lit?, A.term.lit? with
    | some r, some k, _ =>
      if r.1.val = 0 then ⟨.seq A.term .err, A.defs ++ B.defs ++ K.defs, K.next⟩
      else mulmodLit prev A.term k.1 r.1 (A.defs ++ B.defs ++ K.defs) K.next
    | some r, none, some k =>
      if r.1.val = 0 then ⟨.seq B.term .err, A.defs ++ B.defs ++ K.defs, K.next⟩
      else mulmodLit prev B.term k.1 r.1 (A.defs ++ B.defs ++ K.defs) K.next
    | _, _, _ => ⟨.app3 (.modular .mulmod) A.term B.term K.term, A.defs ++ B.defs ++ K.defs, K.next⟩
  | _, _, _, _, o, _, A, B, K => ⟨.app3 o A.term B.term K.term, A.defs ++ B.defs ++ K.defs, K.next⟩

/-- **The cut of a term**, after the definitions `prev`, its fresh atoms from `n`. -/
def LTm.cut : {s : Srt} → LTm C s → List (LFml C) → Nat → CutTm C s
  | _, .var k, _, n => ⟨.var k, [], n⟩
  | _, .app0 o, _, n => ⟨.app0 o, [], n⟩
  | _, .err, _, n => ⟨.err, [], n⟩
  | _, .app1 o a, prev, n => cut1 o prev (a.cut prev n)
  | _, .app2 o a b, prev, n =>
    let A := a.cut prev n
    cut2 o prev A (b.cut (prev ++ A.defs) A.next)
  | _, .app3 o a b c, prev, n =>
    let A := a.cut prev n
    let B := b.cut (prev ++ A.defs) A.next
    let Cc := c.cut (prev ++ A.defs ++ B.defs) B.next
    cut3 o prev A B Cc
  | _, .index it a b, prev, n =>
    let A := a.cut prev n
    let B := b.cut (prev ++ A.defs) A.next
    ⟨.index it A.term B.term, A.defs ++ B.defs, B.next⟩
  | _, .obsW a, prev, n => let A := a.cut prev n; ⟨.obsW A.term, A.defs, A.next⟩
  | _, .obsL a, prev, n => let A := a.cut prev n; ⟨.obsL A.term, A.defs, A.next⟩
  | _, .obsH a, prev, n => let A := a.cut prev n; ⟨.obsH A.term, A.defs, A.next⟩
  | _, .seq a b, prev, n =>
    let A := a.cut prev n
    let B := b.cut (prev ++ A.defs) A.next
    ⟨.seq A.term B.term, A.defs ++ B.defs, B.next⟩
  | _, .orElse a b, prev, n =>
    let A := a.cut prev n
    let B := b.cut (prev ++ A.defs) A.next
    ⟨.orElse A.term B.term, A.defs ++ B.defs, B.next⟩
  | _, .kite a b t e, prev, n =>
    let A := a.cut prev n
    let B := b.cut (prev ++ A.defs) A.next
    let T := t.cut (prev ++ A.defs ++ B.defs) B.next
    let E := e.cut (prev ++ A.defs ++ B.defs ++ T.defs) T.next
    ⟨.kite A.term B.term T.term E.term, A.defs ++ B.defs ++ T.defs ++ E.defs, E.next⟩

/-- A formula with its cut operators replaced by fresh atoms. -/
structure CutFml (C : Contract) where
  formula : LFml C
  defs : List (LFml C)
  next : Nat

/-- **The cut of a formula**, after the definitions `prev`, its fresh atoms
from `n`; a quantifier is kept whole. -/
def LFml.cut : LFml C → List (LFml C) → Nat → CutFml C
  | .tt, _, n => ⟨.tt, [], n⟩
  | .eq a b, prev, n =>
    let A := a.cut prev n
    let B := b.cut (prev ++ A.defs) A.next
    ⟨.eq A.term B.term, A.defs ++ B.defs, B.next⟩
  | .not φ, prev, n => let F := φ.cut prev n; ⟨.not F.formula, F.defs, F.next⟩
  | .and φ ψ, prev, n =>
    let F := φ.cut prev n
    let G := ψ.cut (prev ++ F.defs) F.next
    ⟨.and F.formula G.formula, F.defs ++ G.defs, G.next⟩
  | .imp φ ψ, prev, n =>
    let F := φ.cut prev n
    let G := ψ.cut (prev ++ F.defs) F.next
    ⟨.imp F.formula G.formula, F.defs ++ G.defs, G.next⟩
  | .all k p φ, _, n => ⟨.all k p φ, [], n⟩

/-- **The cut leaf**: the definitions of its fresh atoms (from past every
atom of `φ`) as the antecedent of the cut formula; `φ`'s cut itself when no
operator was cut. -/
def LFml.cutAll (φ : LFml C) : LFml C :=
  match (φ.cut [] φ.atomBound).defs with
  | [] => (φ.cut [] φ.atomBound).formula
  | ds => .imp (LFml.conj ds) (φ.cut [] φ.atomBound).formula

/-! ## Fresh atoms keep the leaf -/

theorem AEnv.AgreesBelow.refl (n : Nat) (ν : AEnv) : ν.AgreesBelow n ν := fun _ _ _ => rfl

theorem AEnv.AgreesBelow.trans {n : Nat} {ν μ ρ : AEnv} (h : ν.AgreesBelow n μ)
    (k : μ.AgreesBelow n ρ) : ν.AgreesBelow n ρ := fun p j hj => (h p j hj).trans (k p j hj)

theorem AEnv.AgreesBelow.set {n : Nat} {ν μ : AEnv} (h : ν.AgreesBelow n μ) (p : PrimTy) (k : Nat)
    (v : p.Denote) : (ν.set p k v).AgreesBelow n (μ.set p k v) := by
  intro q j hj
  have hb := h .bool j hj
  have hu := h .uint j hj
  have hi := h .int j hj
  simp only [AEnv.get] at hb hu hi
  cases p <;> cases q <;> simp only [AEnv.set, AEnv.get, hb, hu, hi]

theorem AEnv.AgreesBelow.set_ge {n : Nat} (ν : AEnv) (p : PrimTy) {k : Nat} (hk : n ≤ k)
    (v : p.Denote) : ν.AgreesBelow n (ν.set p k v) :=
  fun q j hj => (AEnv.get_set_ne ν p q v (by omega)).symm

theorem LFml.holds_agree_below (g : State C []) : ∀ (φ : LFml C) {ν μ : AEnv},
    ν.AgreesBelow φ.atomBound μ → (φ.holds g ν ↔ φ.holds g μ)
  | .tt, _, _, _ => Iff.rfl
  | .eq a b, _, _, h => by
    simp only [LFml.holds, a.eval_agree_below g (h.mono (Nat.le_max_left _ _)),
      b.eval_agree_below g (h.mono (Nat.le_max_right _ _))]
  | .not φ, _, _, h => not_congr (LFml.holds_agree_below g φ h)
  | .and φ ψ, _, _, h => and_congr (LFml.holds_agree_below g φ (h.mono (Nat.le_max_left _ _)))
      (LFml.holds_agree_below g ψ (h.mono (Nat.le_max_right _ _)))
  | .imp φ ψ, _, _, h => imp_congr (LFml.holds_agree_below g φ (h.mono (Nat.le_max_left _ _)))
      (LFml.holds_agree_below g ψ (h.mono (Nat.le_max_right _ _)))
  | .all k p φ, _, _, h => by
    simp only [LFml.holds]
    exact forall_congr' fun v => LFml.holds_agree_below g φ
      ((h.mono (Nat.le_max_right _ _)).set p k v)

theorem LFml.AllHold.append_iff (g : State C []) (ν : AEnv) (a b : List (LFml C)) :
    LFml.AllHold g ν (a ++ b) ↔ LFml.AllHold g ν a ∧ LFml.AllHold g ν b := by
  simp only [LFml.AllHold, List.mem_append]
  exact ⟨fun h => ⟨fun d hd => h d (.inl hd), fun d hd => h d (.inr hd)⟩,
    fun h d hd => hd.elim (h.1 d) (h.2 d)⟩

theorem LFml.holds_conj (g : State C []) (ν : AEnv) :
    ∀ ds : List (LFml C), (LFml.conj ds).holds g ν ↔ LFml.AllHold g ν ds
  | [] => by simp only [LFml.conj, LFml.holds, LFml.AllHold, List.not_mem_nil, false_implies,
      implies_true]
  | [d] => by simp only [LFml.conj, LFml.AllHold, List.mem_singleton, forall_eq]
  | d :: e :: ds => by
    rw [show LFml.conj (d :: e :: ds) = .and d (LFml.conj (e :: ds)) from rfl, LFml.holds,
      LFml.holds_conj g ν (e :: ds)]
    simp only [LFml.AllHold, List.mem_cons, forall_eq_or_imp]

/-- Definitions made from `n` on, below `m`, that some assignment of their
atoms satisfies without changing any atom below `n`. -/
structure Defs.Good (n m : Nat) (ds : List (LFml C)) : Prop where
  le : n ≤ m
  bound : ∀ d ∈ ds, d.atomBound ≤ m
  extend : ∀ (g : State C []) (ν : AEnv), ∃ μ, ν.AgreesBelow n μ ∧ LFml.AllHold g μ ds

theorem Defs.Good.nil (n : Nat) : Defs.Good (C := C) n n [] :=
  ⟨Nat.le_refl _, (fun _ h => nomatch h), (fun _ ν => ⟨ν, .refl _ _, fun _ h => nomatch h⟩)⟩

theorem Defs.Good.mono {n m k : Nat} {ds : List (LFml C)} (h : Defs.Good n m ds) (hk : m ≤ k) :
    Defs.Good n k ds :=
  ⟨Nat.le_trans h.le hk, fun d hd => Nat.le_trans (h.bound d hd) hk, h.extend⟩

theorem Defs.Good.append {n m k : Nat} {ds es : List (LFml C)} (h : Defs.Good n m ds)
    (h' : Defs.Good m k es) : Defs.Good n k (ds ++ es) := by
  refine ⟨Nat.le_trans h.le h'.le, fun d hd => ?_, fun g ν => ?_⟩
  · rcases List.mem_append.mp hd with hd | hd
    · exact Nat.le_trans (h.bound d hd) h'.le
    · exact h'.bound d hd
  · obtain ⟨μ, hμ, hd⟩ := h.extend g ν
    obtain ⟨ρ, hρ, he⟩ := h'.extend g μ
    refine ⟨ρ, hμ.trans (hρ.mono h.le), (LFml.AllHold.append_iff g ρ _ _).mpr ⟨fun d hd' => ?_, he⟩⟩
    exact (LFml.holds_agree_below g d (hρ.mono (h.bound d hd'))).mp (hd d hd')

/-- **A fresh atom is definable**: `m`'s definition, `e`'s value where `g`
returns, is satisfied by setting `m` alone. -/
theorem Defs.Good.defn {n m : Nat} {ds : List (LFml C)} (h : Defs.Good n m ds) {p r : PrimTy}
    {g : LTm C (.val p)} {e : LTm C (.val r)} (hg : g.atomBound ≤ m) (he : e.atomBound ≤ m)
    (ht : ∀ (σ : State C []) ν, (g.eval σ ν).isSome = true → (e.eval σ ν).isSome = true) :
    Defs.Good n (m + 1) (ds ++ [LFml.defn g e m]) := by
  refine ⟨Nat.le_succ_of_le h.le, fun d hd => ?_, fun σ ν => ?_⟩
  · rcases List.mem_append.mp hd with hd | hd
    · exact Nat.le_succ_of_le (h.bound d hd)
    · rw [List.mem_singleton.mp hd]
      show max (max g.atomBound g.atomBound) (max e.atomBound (m + 1)) ≤ m + 1
      omega
  · obtain ⟨μ, hμ, hd⟩ := h.extend σ ν
    let w : r.Denote := ((e.eval σ μ : Option r.Denote)).getD (PrimTy.dflt r)
    have hagree : μ.AgreesBelow m (μ.set r m w) := AEnv.AgreesBelow.set_ge μ r (Nat.le_refl _) w
    refine ⟨μ.set r m w, hμ.trans (hagree.mono h.le), (LFml.AllHold.append_iff σ _ _ _).mpr
      ⟨fun d hd' => (LFml.holds_agree_below σ d (hagree.mono (h.bound d hd'))).mp (hd d hd'), ?_⟩⟩
    intro d hd'
    rw [List.mem_singleton.mp hd']
    have hge : g.eval σ (μ.set r m w) = g.eval σ μ := (g.eval_agree_below σ (hagree.mono hg)).symm
    have hee : e.eval σ (μ.set r m w) = e.eval σ μ := (e.eval_agree_below σ (hagree.mono he)).symm
    intro hgg
    rw [LFml.holds_eq_iff] at hgg ⊢
    obtain ⟨x, hx, -⟩ := hgg
    rw [hge] at hx
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (ht σ μ (by rw [hx]; rfl))
    refine ⟨y, by rw [hee, hy], ?_⟩
    rw [LTm.eval_var, AEnv.get_set_self]
    simp only [w, hy, Option.getD_some]

/-- **What a cut term satisfies**: its definitions are good from `n`, its
atoms are below its next one, and it evaluates as the term wherever the
earlier definitions `prev` and its own hold. -/
structure CutTm.Good {s : Srt} (t : LTm C s) (n : Nat) (prev : List (LFml C)) (A : CutTm C s) : Prop where
  defs : Defs.Good n A.next A.defs
  bound : A.term.atomBound ≤ A.next
  eval : ∀ (g : State C []) (ν : AEnv), LFml.AllHold g ν prev → LFml.AllHold g ν A.defs →
    A.term.eval g ν = t.eval g ν

/-- Definitions below `n`. -/
def Defs.Below (n : Nat) (ds : List (LFml C)) : Prop := ∀ d ∈ ds, d.atomBound ≤ n

theorem Defs.Below.append {n m : Nat} {ds es : List (LFml C)} (h : Defs.Below n ds)
    (hm : n ≤ m) (h' : Defs.Below m es) : Defs.Below m (ds ++ es) := fun d hd =>
  (List.mem_append.mp hd).elim (fun hd => Nat.le_trans (h d hd) hm) (h' d)

theorem LFml.AllHold.append {g : State C []} {ν : AEnv} {a b : List (LFml C)}
    (ha : LFml.AllHold g ν a) (hb : LFml.AllHold g ν b) : LFml.AllHold g ν (a ++ b) :=
  (LFml.AllHold.append_iff g ν a b).mpr ⟨ha, hb⟩

theorem LFml.defnAtom?_eq {p r : PrimTy} {g : LTm C (.val p)} {e : LTm C (.val r)} :
    ∀ {d : LFml C} {m : Nat}, LFml.defnAtom? g e d = some m → d = LFml.defn g e m := by
  intro d m h
  unfold LFml.defnAtom? at h
  split at h
  · rename_i g₁ g₂ e₁ m'
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨h1, h2⟩, h3⟩ := hc
      have s1 := LTm.sigma_eq_of_beqR h1
      have s2 := LTm.sigma_eq_of_beqR h2
      have s3 := LTm.sigma_eq_of_beqR h3
      cases s1
      cases s2
      cases s3
      cases h
      rfl
    · cases h
  · cases h

theorem LFml.findAtom?_mem {p r : PrimTy} {g : LTm C (.val p)} {e : LTm C (.val r)} :
    ∀ {ds : List (LFml C)} {m : Nat}, LFml.findAtom? g e ds = some m → LFml.defn g e m ∈ ds
  | [], _, h => nomatch h
  | d :: ds, m, h => by
    unfold LFml.findAtom? at h
    split at h
    · rename_i hd
      cases h
      exact List.mem_cons.mpr (.inl (LFml.defnAtom?_eq hd).symm)
    · exact List.mem_cons_of_mem _ (LFml.findAtom?_mem h)

/-- **What the atom of a node satisfies.** -/
theorem quotAtom_good {p r : PrimTy} {prev ds : List (LFml C)} {n m : Nat}
    (hds : Defs.Good n m ds) (hprev : Defs.Below n prev) {g : LTm C (.val p)}
    {e : LTm C (.val r)} (hg : g.atomBound ≤ m) (he : e.atomBound ≤ m)
    (ht : ∀ (σ : State C []) ν, (g.eval σ ν).isSome = true → (e.eval σ ν).isSome = true) :
    Defs.Good n (quotAtom prev ds g e m).2.2 (quotAtom prev ds g e m).2.1 ∧
      (quotAtom prev ds g e m).1 < (quotAtom prev ds g e m).2.2 ∧
      m ≤ (quotAtom prev ds g e m).2.2 ∧
      (∀ d ∈ (quotAtom prev ds g e m).2.1, d ∈ ds ∨ d = LFml.defn g e m) ∧
      ∀ (σ : State C []) ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν (quotAtom prev ds g e m).2.1 →
        LFml.AllHold σ ν ds ∧ (LFml.defn g e (quotAtom prev ds g e m).1).holds σ ν := by
  unfold quotAtom
  split
  · rename_i k hk
    have hmem := LFml.findAtom?_mem hk
    have hb : (LFml.defn g e k).atomBound ≤ m := by
      rcases List.mem_append.mp hmem with h | h
      · exact Nat.le_trans (hprev _ h) hds.le
      · exact hds.bound _ h
    have hk' : k < m := by
      have : (LFml.defn g e k).atomBound = max (max g.atomBound g.atomBound) (max e.atomBound (k + 1)) := rfl
      omega
    refine ⟨hds, hk', Nat.le_refl _, fun d hd => .inl hd, fun σ ν h1 h2 => ⟨h2, ?_⟩⟩
    rcases List.mem_append.mp hmem with h | h
    · exact h1 _ h
    · exact h2 _ h
  · refine ⟨hds.defn hg he ht, Nat.lt_succ_self _, Nat.le_succ _, fun d hd => ?_, fun σ ν _ h2 => ?_⟩
    · rcases List.mem_append.mp hd with h | h
      · exact .inl h
      · exact .inr (List.mem_singleton.mp h)
    · obtain ⟨ha, hb⟩ := (LFml.AllHold.append_iff σ ν _ _).mp h2
      exact ⟨ha, hb _ List.mem_cons_self⟩

namespace CutTm.Good

theorem leaf {s : Srt} {t : LTm C s} {n : Nat} {prev : List (LFml C)} (h : t.atomBound ≤ n) :
    CutTm.Good t n prev ⟨t, [], n⟩ :=
  ⟨Defs.Good.nil n, h, fun _ _ _ _ => rfl⟩

theorem node1 {a s : Srt} {x : LTm C a} {n : Nat} {prev : List (LFml C)} {A : CutTm C a}
    (hA : CutTm.Good x n prev A)
    (mk : LTm C a → LTm C s) (hb : ∀ y, (mk y).atomBound = y.atomBound)
    (he : ∀ g ν y, y.eval g ν = x.eval g ν → (mk y).eval g ν = (mk x).eval g ν) :
    CutTm.Good (mk x) n prev ⟨mk A.term, A.defs, A.next⟩ :=
  ⟨hA.defs, by rw [hb]; exact hA.bound, fun g ν hp h => he g ν _ (hA.eval g ν hp h)⟩

theorem node2 {a b s : Srt} {x : LTm C a} {y : LTm C b} {n : Nat} {prev : List (LFml C)}
    {A : CutTm C a} {B : CutTm C b}
    (hA : CutTm.Good x n prev A) (hB : CutTm.Good y A.next (prev ++ A.defs) B)
    (mk : LTm C a → LTm C b → LTm C s)
    (hb : ∀ x' y', (mk x' y').atomBound = max x'.atomBound y'.atomBound)
    (he : ∀ g ν x' y', x'.eval g ν = x.eval g ν → y'.eval g ν = y.eval g ν →
      (mk x' y').eval g ν = (mk x y).eval g ν) :
    CutTm.Good (mk x y) n prev ⟨mk A.term B.term, A.defs ++ B.defs, B.next⟩ := by
  refine ⟨hA.defs.append hB.defs, ?_, fun g ν hp h => ?_⟩
  · show (mk A.term B.term).atomBound ≤ B.next
    rw [hb]
    have := hB.defs.le
    have := hA.bound
    have := hB.bound
    omega
  · obtain ⟨ha, hb'⟩ := (LFml.AllHold.append_iff g ν _ _).mp h
    exact he g ν _ _ (hA.eval g ν hp ha) (hB.eval g ν (hp.append ha) hb')

theorem node3 {a b c s : Srt} {x : LTm C a} {y : LTm C b} {z : LTm C c} {n : Nat}
    {prev : List (LFml C)} {A : CutTm C a} {B : CutTm C b} {Z : CutTm C c}
    (hA : CutTm.Good x n prev A) (hB : CutTm.Good y A.next (prev ++ A.defs) B)
    (hZ : CutTm.Good z B.next (prev ++ A.defs ++ B.defs) Z)
    (mk : LTm C a → LTm C b → LTm C c → LTm C s)
    (hb : ∀ x' y' z', (mk x' y' z').atomBound ≤ max x'.atomBound (max y'.atomBound z'.atomBound))
    (he : ∀ g ν x' y' z', x'.eval g ν = x.eval g ν → y'.eval g ν = y.eval g ν →
      z'.eval g ν = z.eval g ν → (mk x' y' z').eval g ν = (mk x y z).eval g ν) :
    CutTm.Good (mk x y z) n prev ⟨mk A.term B.term Z.term, A.defs ++ B.defs ++ Z.defs, Z.next⟩ := by
  refine ⟨(hA.defs.append hB.defs).append hZ.defs, ?_, fun g ν hp h => ?_⟩
  · show (mk A.term B.term Z.term).atomBound ≤ Z.next
    have := hb A.term B.term Z.term
    have := hB.defs.le
    have := hZ.defs.le
    have := hA.bound
    have := hB.bound
    have := hZ.bound
    omega
  · obtain ⟨hab, hz⟩ := (LFml.AllHold.append_iff g ν _ _).mp h
    obtain ⟨ha, hb'⟩ := (LFml.AllHold.append_iff g ν _ _).mp hab
    exact he g ν _ _ _ (hA.eval g ν hp ha) (hB.eval g ν (hp.append ha) hb')
      (hZ.eval g ν ((hp.append ha).append hb') hz)

theorem node4 {a b c d s : Srt} {x : LTm C a} {y : LTm C b} {z : LTm C c} {w : LTm C d} {n : Nat}
    {prev : List (LFml C)} {A : CutTm C a} {B : CutTm C b} {Z : CutTm C c} {W : CutTm C d}
    (hA : CutTm.Good x n prev A) (hB : CutTm.Good y A.next (prev ++ A.defs) B)
    (hZ : CutTm.Good z B.next (prev ++ A.defs ++ B.defs) Z)
    (hW : CutTm.Good w Z.next (prev ++ A.defs ++ B.defs ++ Z.defs) W)
    (mk : LTm C a → LTm C b → LTm C c → LTm C d → LTm C s)
    (hb : ∀ x' y' z' w', (mk x' y' z' w').atomBound ≤
      max x'.atomBound (max y'.atomBound (max z'.atomBound w'.atomBound)))
    (he : ∀ g ν x' y' z' w', x'.eval g ν = x.eval g ν → y'.eval g ν = y.eval g ν →
      z'.eval g ν = z.eval g ν → w'.eval g ν = w.eval g ν →
      (mk x' y' z' w').eval g ν = (mk x y z w).eval g ν) :
    CutTm.Good (mk x y z w) n prev
      ⟨mk A.term B.term Z.term W.term, A.defs ++ B.defs ++ Z.defs ++ W.defs, W.next⟩ := by
  refine ⟨((hA.defs.append hB.defs).append hZ.defs).append hW.defs, ?_, fun g ν hp h => ?_⟩
  · show (mk A.term B.term Z.term W.term).atomBound ≤ W.next
    have := hb A.term B.term Z.term W.term
    have := hB.defs.le
    have := hZ.defs.le
    have := hW.defs.le
    have := hA.bound
    have := hB.bound
    have := hZ.bound
    have := hW.bound
    omega
  · obtain ⟨habz, hw⟩ := (LFml.AllHold.append_iff g ν _ _).mp h
    obtain ⟨hab, hz⟩ := (LFml.AllHold.append_iff g ν _ _).mp habz
    obtain ⟨ha, hb'⟩ := (LFml.AllHold.append_iff g ν _ _).mp hab
    exact he g ν _ _ _ _ (hA.eval g ν hp ha) (hB.eval g ν (hp.append ha) hb')
      (hZ.eval g ν ((hp.append ha).append hb') hz)
      (hW.eval g ν (((hp.append ha).append hb').append hz) hw)

/-- **A node cut through the atom of `e` after `g`**: wherever the
definitions hold, `R k` evaluates as `t`, `k` the atom. -/
theorem quot {p r r' : PrimTy} {t : LTm C (.val r')} {n m : Nat} {prev ds : List (LFml C)}
    (hds : Defs.Good n m ds) (hprev : Defs.Below n prev) {g : LTm C (.val p)} {e : LTm C (.val r)}
    (R : Nat → LTm C (.val r')) (hg : g.atomBound ≤ m) (he : e.atomBound ≤ m)
    (hR : ∀ k j, k < j → m ≤ j → (R k).atomBound ≤ j)
    (ht : ∀ (σ : State C []) ν, (g.eval σ ν).isSome = true → (e.eval σ ν).isSome = true)
    (heval : ∀ (σ : State C []) ν k, LFml.AllHold σ ν prev → LFml.AllHold σ ν ds →
      (LFml.defn g e k).holds σ ν → (R k).eval σ ν = t.eval σ ν) :
    CutTm.Good t n prev ⟨R (quotAtom prev ds g e m).1, (quotAtom prev ds g e m).2.1,
      (quotAtom prev ds g e m).2.2⟩ := by
  obtain ⟨h1, h2, h3, -, h5⟩ := quotAtom_good hds hprev hg he ht
  refine ⟨h1, hR _ _ h2 h3, fun σ ν hp hd => ?_⟩
  obtain ⟨hds', hdefn⟩ := h5 σ ν hp hd
  exact heval σ ν _ hp hds' hdefn

/-- **A node replaced by its atom**, sequenced after `g`, which returns
exactly where the node does. -/
theorem atom {p r : PrimTy} {t : LTm C (.val r)} {n m : Nat} {prev ds : List (LFml C)}
    (hds : Defs.Good n m ds) (hprev : Defs.Below n prev) {g : LTm C (.val p)} {e : LTm C (.val r)}
    (hg : g.atomBound ≤ m) (he : e.atomBound ≤ m)
    (hdef : ∀ (σ : State C []) ν, (e.eval σ ν).isSome = (g.eval σ ν).isSome)
    (heval : ∀ (σ : State C []) ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν ds →
      e.eval σ ν = t.eval σ ν) :
    CutTm.Good t n prev (CutTm.atom prev ds g e m) := by
  refine quot hds hprev (fun k => .seq g (.var k)) hg he ?_ (fun σ ν h => by rw [hdef]; exact h) ?_
  · intro k j hk hm
    show max g.atomBound (k + 1) ≤ j
    omega
  · intro σ ν k hp hd hdef'
    rw [← heval σ ν hp hd, LTm.eval_seq]
    cases hgv : g.eval σ ν with
    | none =>
      have := hdef σ ν
      rw [hgv] at this
      cases hev : e.eval σ ν with
      | none => rfl
      | some _ => rw [hev] at this; cases this
    | some x =>
      have hgg : (LFml.eq g g).holds σ ν := (LFml.holds_eq_iff σ ν g g).mpr ⟨x, hgv, hgv⟩
      obtain ⟨y, hy, hq⟩ := (LFml.holds_eq_iff σ ν _ _).mp (hdef' hgg)
      rw [hy]
      show (LTm.var k).eval σ ν = some y
      exact hq

end CutTm.Good

/-! ## The cut operators at their values -/

theorem div_isSome (h : BinOp.div.accepts .uint = true) (x v : PrimTy.uint.Denote) (hv : v.val ≠ 0) :
    (BinOp.evalT .div h x v).isSome = true := by
  have hx0 := uint_val_nonneg x
  have hx1 := uint_val_lt x
  have hv0 := uint_val_nonneg v
  show ((if v.val = 0 then none else some (Int.tdiv x.val v.val)).bind PrimTy.uint.ofInt?).isSome = true
  rw [if_neg hv, Option.bind_some]
  apply ofInt?_isSome' rfl
  rw [Int.tdiv_eq_ediv_of_nonneg hx0]
  exact uint_inRange (Int.ediv_nonneg hx0 hv0) (Int.lt_of_le_of_lt (Int.ediv_le_self _ hx0) hx1)

theorem shr_isSome {p : PrimTy} (h : BinOp.shr.accepts p = true) (x v : p.Denote) :
    (BinOp.evalT .shr h x v).isSome = true := by
  cases p with
  | bool => cases h
  | uint =>
    have hx0 := uint_val_nonneg x
    have hx1 := uint_val_lt x
    show ((some (if v.val < 256 then x.val / 2 ^ v.val.toNat
      else if x.val < 0 then -1 else 0)).bind PrimTy.uint.ofInt?).isSome = true
    rw [Option.bind_some]
    apply ofInt?_isSome' rfl
    have hd : (0 : Int) < 2 ^ v.val.toNat := Int.pow_pos (by decide)
    split
    · exact uint_inRange (Int.ediv_nonneg hx0 (Int.le_of_lt hd))
        (Int.lt_of_le_of_lt (Int.ediv_le_self _ hx0) hx1)
    · split
      · omega
      · exact uint_inRange (by decide) (by rw [uintBound_eq]; decide)
  | int =>
    have hx := int_val_bounds x
    show ((some (if v.val < 256 then x.val / 2 ^ v.val.toNat
      else if x.val < 0 then -1 else 0)).bind PrimTy.int.ofInt?).isSome = true
    rw [Option.bind_some]
    apply ofInt?_isSome' rfl
    have hd : (0 : Int) < 2 ^ v.val.toNat := Int.pow_pos (by decide)
    have hB := intBound_eq
    split
    · apply int_inRange
      · rcases Int.lt_or_le x.val 0 with hn | hn
        · refine Int.le_trans hx.1 ((Int.le_ediv_iff_mul_le hd).mpr ?_)
          have h1 := Int.mul_nonpos_of_nonpos_of_nonneg (Int.le_of_lt hn)
            (show (0 : Int) ≤ 2 ^ v.val.toNat - 1 by omega)
          rw [Int.mul_sub, Int.mul_one] at h1
          omega
        · exact Int.le_trans (by omega) (Int.ediv_nonneg hn (Int.le_of_lt hd))
      · rcases Int.lt_or_le x.val 0 with hn | hn
        · have : x.val / 2 ^ v.val.toNat < 0 := (Int.ediv_lt_iff_lt_mul hd).mpr (by omega)
          omega
        · exact Int.lt_of_le_of_lt (Int.ediv_le_self _ hn) hx.2
    · split <;> exact int_inRange (by omega) (by omega)

theorem wrap_inRange (n : Int) : PrimTy.uint.inRange (n % Semantics.uintBound) = true :=
  uint_inRange (Int.emod_nonneg _ (by decide)) (Int.emod_lt_of_pos _ (by decide))

theorem addW_isSome (h : BinOp.addW.accepts .uint = true) (x y : PrimTy.uint.Denote) :
    (BinOp.evalT .addW h x y).isSome = true := by
  show ((some ((x.val + y.val) % Semantics.uintBound)).bind PrimTy.uint.ofInt?).isSome = true
  rw [Option.bind_some]
  exact ofInt?_isSome' rfl (wrap_inRange _)

theorem subW_isSome (h : BinOp.subW.accepts .uint = true) (x y : PrimTy.uint.Denote) :
    (BinOp.evalT .subW h x y).isSome = true := by
  show ((some ((x.val - y.val) % Semantics.uintBound)).bind PrimTy.uint.ofInt?).isSome = true
  rw [Option.bind_some]
  exact ofInt?_isSome' rfl (wrap_inRange _)

theorem toInt_isSome (h : UnOp.toInt.accepts .uint = true) (x : PrimTy.uint.Denote) :
    (UnOp.evalT .toInt h x).isSome = true := by
  have hx0 := uint_val_nonneg x
  have hx1 := uint_val_lt x
  show (PrimTy.int.ofInt? (if x.val < Semantics.intBound then x.val
    else x.val - Semantics.uintBound)).isSome = true
  apply ofInt?_isSome' rfl
  have hM := uintBound_eq
  have hB := intBound_eq
  simp only [Semantics.intBound, Semantics.uintBound]
  split <;> exact int_inRange (by omega) (by omega)

theorem toUint_isSome (h : UnOp.toUint.accepts .int = true) (x : PrimTy.int.Denote) :
    (UnOp.evalT .toUint h x).isSome = true := by
  show (PrimTy.uint.ofInt? (x.val % Semantics.uintBound)).isSome = true
  exact ofInt?_isSome' rfl (wrap_inRange _)

/-- **A remainder through its quotient**: `x - q * v` where `q = x / v`. -/
theorem rem_eval (h : BinOp.mod.accepts .uint = true) (x v q : PrimTy.uint.Denote) (hv : v.val ≠ 0)
    (hq : BinOp.evalT .div rfl x v = some q) :
    (BinOp.evalT .mul rfl q v).bind (BinOp.evalT .sub rfl x) = BinOp.evalT .mod h x v := by
  have hx0 := uint_val_nonneg x
  have hx1 := uint_val_lt x
  have hv0 := uint_val_nonneg v
  have hq' : q.val = x.val / v.val := by
    have : ((if v.val = 0 then none else some (Int.tdiv x.val v.val)).bind PrimTy.uint.ofInt?) = some q := hq
    rw [if_neg hv, Option.bind_some, Int.tdiv_eq_ediv_of_nonneg hx0] at this
    have hin := uint_inRange (Int.ediv_nonneg hx0 hv0) (Int.lt_of_le_of_lt (Int.ediv_le_self _ hx0) hx1)
    simp only [PrimTy.ofInt?, dif_pos hin, Option.some.injEq] at this
    rw [← this]
  have hle : q.val * v.val ≤ x.val := by rw [hq']; exact Int.ediv_mul_le _ hv
  have hm0 : 0 ≤ q.val * v.val := Int.mul_nonneg (uint_val_nonneg q) hv0
  show ((PrimTy.uint.ofInt? (q.val * v.val)).bind fun w =>
      PrimTy.uint.ofInt? (x.val - w.val)) =
    (if v.val = 0 then none else some (Int.tmod x.val v.val)).bind PrimTy.uint.ofInt?
  rw [if_neg hv, Option.bind_some, uint_ofInt?_eq hm0 (by omega), Option.bind_some]
  show PrimTy.uint.ofInt? (x.val - q.val * v.val) = _
  rw [Int.tmod_eq_emod_of_nonneg hx0, Int.emod_def, hq', Int.mul_comm v.val]

theorem pow_cast_mul {k : Nat} (hk : k ≤ 256) :
    ((2 ^ (256 - k) : Nat) : Int) * ((2 ^ k : Nat) : Int) = ((2 ^ 256 : Nat) : Int) := by
  rw [← Int.natCast_mul, ← Nat.pow_add, Nat.sub_add_cancel hk]

/-- **A left shift through its quotient**: `(x - q · 2^(256-k)) · 2^k` where
`q = x / 2^(256-k)`, for `0 < k < 256`. -/
theorem shl_eval (h : BinOp.shl.accepts .uint = true) (x v q : PrimTy.uint.Denote)
    (hk0 : v.val ≠ 0) (hk : v.val < 256) (hd : 256 - v.val.toNat < 256) (he : v.val.toNat < 256)
    (hq : BinOp.evalT .div rfl x (uintPow (256 - v.val.toNat) hd) = some q) :
    ((BinOp.evalT .mul rfl q (uintPow (256 - v.val.toNat) hd)).bind (BinOp.evalT .sub rfl x)).bind
      (fun r => BinOp.evalT .mul rfl r (uintPow v.val.toNat he)) = BinOp.evalT .shl h x v := by
  have hx0 := uint_val_nonneg x
  have hx1 := uint_val_lt x
  have hv0 := uint_val_nonneg v
  have hq0 := uint_val_nonneg q
  have hdk := pow_cast_mul (k := v.val.toNat) (by omega)
  have hdpos : (0 : Int) < ((2 ^ (256 - v.val.toNat) : Nat) : Int) := by
    have := Nat.two_pow_pos (256 - v.val.toNat); omega
  have hepos : (0 : Int) < ((2 ^ v.val.toNat : Nat) : Int) := by
    have := Nat.two_pow_pos v.val.toNat; omega
  have hpow : (2 : Int) ^ v.val.toNat = ((2 ^ v.val.toNat : Nat) : Int) := by
    rw [Int.natCast_pow]; rfl
  have hq' : ((if ((2 ^ (256 - v.val.toNat) : Nat) : Int) = 0 then none
        else some (Int.tdiv x.val ((2 ^ (256 - v.val.toNat) : Nat) : Int))).bind
          PrimTy.uint.ofInt?) = some q := hq
  rw [if_neg (by omega), Option.bind_some, Int.tdiv_eq_ediv_of_nonneg hx0] at hq'
  clear hq
  show (((PrimTy.uint.ofInt? (q.val * ((2 ^ (256 - v.val.toNat) : Nat) : Int))).bind fun w =>
      PrimTy.uint.ofInt? (x.val - w.val)).bind
      fun r => PrimTy.uint.ofInt? (r.val * ((2 ^ v.val.toNat : Nat) : Int))) =
    (some (if v.val < 256 then x.val * 2 ^ v.val.toNat % Semantics.uintBound else 0)).bind
      PrimTy.uint.ofInt?
  rw [if_pos hk, hpow, Option.bind_some]
  revert hq'
  generalize ((2 ^ (256 - v.val.toNat) : Nat) : Int) = d at *
  generalize ((2 ^ v.val.toNat : Nat) : Int) = e at *
  intro hq'
  have hin := uint_inRange (Int.ediv_nonneg hx0 (Int.le_of_lt hdpos))
    (Int.lt_of_le_of_lt (Int.ediv_le_self _ hx0) hx1)
  simp only [PrimTy.ofInt?, dif_pos hin, Option.some.injEq] at hq'
  have hqv : q.val = x.val / d := by rw [← hq']
  have hle : q.val * d ≤ x.val := by rw [hqv]; exact Int.ediv_mul_le _ (by omega)
  have hm0 : 0 ≤ q.val * d := Int.mul_nonneg hq0 (Int.le_of_lt hdpos)
  have hr : x.val - q.val * d = x.val % d := by rw [Int.emod_def, hqv, Int.mul_comm d]
  have hr0 : 0 ≤ x.val % d := Int.emod_nonneg _ (by omega)
  have hrd : x.val % d < d := Int.emod_lt_of_pos _ hdpos
  have hre : x.val % d * e < ((2 ^ 256 : Nat) : Int) := by
    rw [← hdk]; exact Int.mul_lt_mul_of_pos_right hrd hepos
  have hre0 : 0 ≤ x.val % d * e := Int.mul_nonneg hr0 (Int.le_of_lt hepos)
  have hsplit : x.val = d * q.val + x.val % d := by rw [hqv]; exact (Int.ediv_add_emod _ _).symm
  have hmod : x.val * e % Semantics.uintBound = x.val % d * e := by
    have := (Int.ediv_emod_unique (a := x.val * e) (b := Semantics.uintBound) (q := q.val)
      (r := x.val % d * e) (by decide)).mpr ⟨?_, hre0, hre⟩
    · exact this.2
    · show x.val % d * e + ((2 ^ 256 : Nat) : Int) * q.val = x.val * e
      rw [← hdk]
      conv => rhs; rw [hsplit]
      rw [Int.add_mul, Int.mul_comm (d * q.val) e, Int.mul_comm (d * e) q.val,
        Int.mul_comm d q.val, Int.mul_comm e (q.val * d), Int.mul_assoc]
      omega
  rw [uint_ofInt?_eq hm0 (by omega), Option.bind_some]
  show (PrimTy.uint.ofInt? (x.val - q.val * d)).bind (fun r => PrimTy.uint.ofInt? (r.val * e)) = _
  rw [hr, uint_ofInt?_eq hr0 (by omega), Option.bind_some, hmod]

/-! ## The cut is good -/

/-- A binary operator the cut leaves: the node is rebuilt over its cut operands. -/
theorem cut2_default {op : BinOp} {p : PrimTy} (h : op.accepts p = true)
    (hop : op ≠ .div ∧ op ≠ .mod ∧ op ≠ .shr ∧ op ≠ .shl ∧ op ≠ .addW ∧ op ≠ .subW ∧ op ≠ .band ∧
      op ≠ .pow ∧ op ≠ .powW ∧ op ≠ .mulW ∧ op ≠ .bor ∧ op ≠ .bxor)
    (prev : List (LFml C)) (A B : CutTm C (.val p)) :
    cut2 (.binop op h) prev A B = ⟨.app2 (.binop op h) A.term B.term, A.defs ++ B.defs, B.next⟩ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hop
  cases op <;> cases p <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | exact absurd rfl h4 | exact absurd rfl h5 | exact absurd rfl h6 | exact absurd rfl h7 | exact absurd rfl h8 | exact absurd rfl h9 | exact absurd rfl h10 | exact absurd rfl h11 | exact absurd rfl h12

/-- A unary operator the cut leaves. -/
theorem cut1_default {op : UnOp} {p : PrimTy} (h : op.accepts p = true)
    (hop : op ≠ .toInt ∧ op ≠ .toUint) (prev : List (LFml C)) (A : CutTm C (.val p)) :
    cut1 (.unop op h) prev A = ⟨.app1 (.unop op h) A.term, A.defs, A.next⟩ := by
  obtain ⟨h1, h2⟩ := hop
  cases op <;> cases p <;> first | rfl | (exfalso; revert h1 h2; decide)

theorem isSome_binop_lit {op : BinOp} {p : PrimTy} (h : op.accepts p = true)
    (hop : op ≠ .and ∧ op ≠ .or) (a b : LTm C (.val p)) (v : p.Denote)
    (hb : b = .app0 (.lit v)) (ht : ∀ x, (op.evalT h x v).isSome = true) (σ : State C []) (ν : AEnv) :
    ((LTm.app2 (.binop op h) a b).eval σ ν).isSome = (a.eval σ ν).isSome := by
  rw [LTm.eval_binop_of h (shortT_none hop), hb]
  cases a.eval σ ν with
  | none => rfl
  | some x => exact (ht x).trans rfl

theorem isSome_binop2 {op : BinOp} {p : PrimTy} (h : op.accepts p = true)
    (hop : op ≠ .and ∧ op ≠ .or) (a b : LTm C (.val p))
    (ht : ∀ x y, (op.evalT h x y).isSome = true) (σ : State C []) (ν : AEnv) :
    ((LTm.app2 (.binop op h) a b).eval σ ν).isSome = ((LTm.seq a b).eval σ ν).isSome := by
  rw [LTm.eval_binop_of h (shortT_none hop), LTm.eval_seq]
  cases a.eval σ ν with
  | none => rfl
  | some x =>
    cases b.eval σ ν with
    | none => rfl
    | some y => exact (ht x y).trans rfl

/-- Where `defn g e m` holds and `g` returns `x`, `e` returns `m`'s value. -/
theorem LFml.defn_eval {p r : PrimTy} {g : LTm C (.val p)} {e : LTm C (.val r)} {m : Nat}
    {σ : State C []} {ν : AEnv} (hd : (LFml.defn g e m).holds σ ν) {x : p.Denote}
    (hx : g.eval σ ν = some x) : e.eval σ ν = some (ν.get r m) := by
  obtain ⟨y, hy, hq⟩ := (LFml.holds_eq_iff σ ν _ _).mp (hd ((LFml.holds_eq_iff σ ν g g).mpr ⟨x, hx, hx⟩))
  rw [hy]
  exact hq.symm

theorem shl_zero (h : BinOp.shl.accepts .uint = true) (x v : PrimTy.uint.Denote) (hv : v.val = 0) :
    BinOp.evalT .shl h x v = some x := by
  have hx0 := uint_val_nonneg x
  have hx1 := uint_val_lt x
  show (some (if v.val < 256 then x.val * 2 ^ v.val.toNat % Semantics.uintBound else 0)).bind
    PrimTy.uint.ofInt? = some x
  rw [hv, if_pos (by decide), Option.bind_some, show (0 : Int).toNat = 0 from rfl, Int.pow_zero,
    Int.mul_one]
  show PrimTy.uint.ofInt? (x.val % ((2 ^ 256 : Nat) : Int)) = some x
  rw [Int.emod_eq_of_lt hx0 hx1, uint_ofInt?_eq hx0 hx1]
  rfl

theorem shl_big (h : BinOp.shl.accepts .uint = true) (x v : PrimTy.uint.Denote) (hv : ¬ v.val < 256) :
    BinOp.evalT .shl h x v = some (PrimTy.dflt .uint) := by
  show (some (if v.val < 256 then x.val * 2 ^ v.val.toNat % Semantics.uintBound else 0)).bind
    PrimTy.uint.ofInt? = some (PrimTy.dflt .uint)
  rw [if_neg hv, Option.bind_some, uint_ofInt?_eq (Int.le_refl 0) (by decide)]
  rfl

theorem lowMask?_spec {v : PrimTy.uint.Denote} {k : Nat} (h : lowMask? v = some k) :
    v.val = ((2 ^ k : Nat) : Int) - 1 ∧ k ≤ 256 := by
  unfold lowMask? at h
  have h1 := List.find?_some h
  have h2 := List.mem_of_find?_eq_some h
  simp only [decide_eq_true_eq] at h1
  simp only [List.mem_range] at h2
  exact ⟨h1.symm, by omega⟩

theorem cutBand_right {prev : List (LFml C)} {h : BinOp.band.accepts .uint = true}
    {A B : CutTm C (.val .uint)} {k : Nat} (hk : B.term.maskOf? = some k) :
    cutBand prev h A B = maskCut prev A.term k (A.defs ++ B.defs) B.next := by
  unfold cutBand
  rw [hk]

theorem cutBand_left {prev : List (LFml C)} {h : BinOp.band.accepts .uint = true}
    {A B : CutTm C (.val .uint)} {k : Nat} (hb : B.term.maskOf? = none) (hk : A.term.maskOf? = some k) :
    cutBand prev h A B = maskCut prev B.term k (A.defs ++ B.defs) B.next := by
  unfold cutBand
  rw [hb]
  dsimp only
  rw [hk]

theorem LTm.maskOf?_spec {t : LTm C (.val .uint)} {k : Nat} (h : t.maskOf? = some k) :
    ∃ v, t = .app0 (.lit v) ∧ v.val = ((2 ^ k : Nat) : Int) - 1 ∧ k ≤ 256 := by
  unfold LTm.maskOf? at h
  split at h
  · rename_i v
    exact ⟨v, rfl, lowMask?_spec h⟩
  · cases h

/-- **A low mask is a remainder**: `x & (2^k - 1) = x % 2^k`. -/
theorem band_mask (h : BinOp.band.accepts .uint = true) (x v : PrimTy.uint.Denote) (k : Nat)
    (hv : v.val = ((2 ^ k : Nat) : Int) - 1) :
    BinOp.evalT .band h x v = PrimTy.uint.ofInt? (x.val % ((2 ^ k : Nat) : Int)) := by
  have hx0 := uint_val_nonneg x
  have hpos := Nat.two_pow_pos k
  show (some (Semantics.uintBitwise (· &&& ·) x.val v.val)).bind PrimTy.uint.ofInt? = _
  rw [Option.bind_some, hv, ← Int.toNat_of_nonneg hx0,
    show ((2 ^ k : Nat) : Int) - 1 = ((2 ^ k - 1 : Nat) : Int) by omega,
    Semantics.uintBitwise_natCast, Nat.and_two_pow_sub_one_eq_mod, Int.natCast_emod]

theorem band_comm (h : BinOp.band.accepts .uint = true) (x v : PrimTy.uint.Denote) :
    BinOp.evalT .band h v x = BinOp.evalT .band h x v := by
  have hx0 := uint_val_nonneg x
  have hv0 := uint_val_nonneg v
  show (some (Semantics.uintBitwise (· &&& ·) v.val x.val)).bind PrimTy.uint.ofInt? =
    (some (Semantics.uintBitwise (· &&& ·) x.val v.val)).bind PrimTy.uint.ofInt?
  rw [← Int.toNat_of_nonneg hx0, ← Int.toNat_of_nonneg hv0, Semantics.uintBitwise_natCast,
    Semantics.uintBitwise_natCast, Nat.and_comm]

theorem mod_pow_eval (x : PrimTy.uint.Denote) (k : Nat) (hk : k < 256) :
    BinOp.evalT .mod rfl x (uintPow k hk) = PrimTy.uint.ofInt? (x.val % ((2 ^ k : Nat) : Int)) := by
  have hx0 := uint_val_nonneg x
  have hpos := Nat.two_pow_pos k
  show (if ((2 ^ k : Nat) : Int) = 0 then none else some (Int.tmod x.val ((2 ^ k : Nat) : Int))).bind
    PrimTy.uint.ofInt? = _
  rw [if_neg (by omega), Option.bind_some, Int.tmod_eq_emod_of_nonneg hx0]

theorem band_full (h : BinOp.band.accepts .uint = true) (x v : PrimTy.uint.Denote)
    (hv : v.val = ((2 ^ 256 : Nat) : Int) - 1) : BinOp.evalT .band h x v = some x := by
  rw [band_mask h x v 256 hv, Int.emod_eq_of_lt (uint_val_nonneg x) (uint_val_lt x),
    uint_ofInt?_eq (uint_val_nonneg x) (uint_val_lt x)]
  rfl

theorem maskCut_good {n m : Nat} {prev ds : List (LFml C)} (hds : Defs.Good n m ds)
    (hprev : Defs.Below n prev) {a t : LTm C (.val .uint)} (ha : a.atomBound ≤ m) (k : Nat) (hk : k ≤ 256)
    (heval : ∀ (σ : State C []) ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν ds →
      t.eval σ ν = (a.eval σ ν).bind fun x => PrimTy.uint.ofInt? (x.val % ((2 ^ k : Nat) : Int))) :
    CutTm.Good t n prev (maskCut prev a k ds m) := by
  unfold maskCut
  split
  · rename_i hk'
    refine CutTm.Good.quot hds hprev (fun q => a.remOf q (uintPow k hk')) ha
      (by show max a.atomBound 0 ≤ m; omega)
      (fun q j hq hm => by show max a.atomBound (max (q + 1) 0) ≤ j; omega)
      (fun σ ν hg => by
        rw [LTm.divLit, isSome_binop_lit rfl ⟨by decide, by decide⟩ a (.app0 (.lit _)) _ rfl
          (fun x => div_isSome rfl x _ (by
            show ((2 ^ k : Nat) : Int) ≠ 0
            have := Nat.two_pow_pos k; omega))]
        exact hg) ?_
    intro σ ν q hp hd hdefn
    rw [heval σ ν hp hd]
    show (LTm.app2 (.binop .sub rfl) a _).eval σ ν = _
    rw [LTm.eval_binop_of rfl (shortT_none ⟨by decide, by decide⟩)]
    cases hx : a.eval σ ν with
    | none => rfl
    | some xv =>
      have hq := LFml.defn_eval hdefn hx
      rw [LTm.divLit, LTm.eval_binop_of rfl (shortT_none ⟨by decide, by decide⟩), hx] at hq
      simp only [Option.bind_some]
      rw [LTm.eval_binop_of rfl (shortT_none ⟨by decide, by decide⟩)]
      exact (rem_eval rfl xv _ _ (by show ((2 ^ k : Nat) : Int) ≠ 0; have := Nat.two_pow_pos k; omega)
        hq).trans (mod_pow_eval xv k hk')
  · rename_i hk'
    have h256 : k = 256 := by omega
    subst h256
    refine ⟨hds, ha, fun σ ν hp hd => ?_⟩
    rw [heval σ ν hp hd]
    show a.eval σ ν = _
    cases a.eval σ ν with
    | none => rfl
    | some xv =>
      rw [Option.bind_some, Int.emod_eq_of_lt (uint_val_nonneg xv) (uint_val_lt xv),
        uint_ofInt?_eq (uint_val_nonneg xv) (uint_val_lt xv)]
      rfl

/-! ## The literal operators are good -/

theorem ev_bin {op : BinOp} {p : PrimTy} (h : op.accepts p = true) (hop : op ≠ .and ∧ op ≠ .or)
    {a b : LTm C (.val p)} {σ : State C []} {ν : AEnv} {x y : p.Denote}
    (ha : a.eval σ ν = some x) (hb : b.eval σ ν = some y) :
    (LTm.app2 (.binop op h) a b).eval σ ν = op.evalT h x y := by
  rw [LTm.eval_binop_of h (shortT_none hop), ha, hb]; rfl

theorem ev_add {a b : LTm C (.val .uint)} {σ : State C []} {ν : AEnv} {x y : PrimTy.uint.Denote}
    (ha : a.eval σ ν = some x) (hb : b.eval σ ν = some y) (h1 : x.val + y.val < ((2 ^ 256 : Nat) : Int)) :
    ∃ w : PrimTy.uint.Denote, (LTm.app2 (.binop .add rfl) a b).eval σ ν = some w ∧ w.val = x.val + y.val :=
  ⟨_, (ev_bin rfl ⟨by decide, by decide⟩ ha hb).trans
    (uint_ofInt?_eq (by have := uint_val_nonneg x; have := uint_val_nonneg y; omega) h1), rfl⟩

theorem ev_sub {a b : LTm C (.val .uint)} {σ : State C []} {ν : AEnv} {x y : PrimTy.uint.Denote}
    (ha : a.eval σ ν = some x) (hb : b.eval σ ν = some y) (h0 : y.val ≤ x.val) :
    ∃ w : PrimTy.uint.Denote, (LTm.app2 (.binop .sub rfl) a b).eval σ ν = some w ∧ w.val = x.val - y.val :=
  ⟨_, (ev_bin rfl ⟨by decide, by decide⟩ ha hb).trans
    (uint_ofInt?_eq (by omega) (by have := uint_val_lt x; have := uint_val_nonneg y; omega)), rfl⟩

theorem ev_mul {a b : LTm C (.val .uint)} {σ : State C []} {ν : AEnv} {x y : PrimTy.uint.Denote}
    (ha : a.eval σ ν = some x) (hb : b.eval σ ν = some y) (h1 : x.val * y.val < ((2 ^ 256 : Nat) : Int)) :
    ∃ w : PrimTy.uint.Denote, (LTm.app2 (.binop .mul rfl) a b).eval σ ν = some w ∧ w.val = x.val * y.val :=
  ⟨_, (ev_bin rfl ⟨by decide, by decide⟩ ha hb).trans
    (uint_ofInt?_eq (Int.mul_nonneg (uint_val_nonneg x) (uint_val_nonneg y)) h1), rfl⟩

theorem ev_lit {p : PrimTy} (v : p.Denote) (σ : State C []) (ν : AEnv) :
    (LTm.app0 (C := C) (.lit v)).eval σ ν = some v := rfl

/-- The atom of `a / 2` holds `a`'s value halved. -/
theorem half_val {a : LTm C (.val .uint)} {q : Nat} {σ : State C []} {ν : AEnv}
    (hd : (LFml.defn a (a.divLit uintTwo) q).holds σ ν) {x : PrimTy.uint.Denote} (hx : a.eval σ ν = some x) :
    (ν.get .uint q).val = x.val / 2 := by
  have h := LFml.defn_eval hd hx
  rw [LTm.divLit, ev_bin rfl ⟨by decide, by decide⟩ hx (ev_lit _ σ ν)] at h
  have hx0 := uint_val_nonneg x
  have hx1 := uint_val_lt x
  have : ((if (2 : Int) = 0 then none else some (Int.tdiv x.val 2)).bind PrimTy.uint.ofInt?) =
      some (ν.get .uint q) := h
  rw [if_neg (by decide), Option.bind_some, Int.tdiv_eq_ediv_of_nonneg hx0,
    uint_ofInt?_eq (Int.ediv_nonneg hx0 (by decide)) (by omega), Option.some.injEq] at this
  rw [← this]

theorem half_isSome (a : LTm C (.val .uint)) (σ : State C []) (ν : AEnv)
    (hg : (a.eval σ ν).isSome = true) : ((a.divLit uintTwo).eval σ ν).isSome = true := by
  rw [LTm.divLit, isSome_binop_lit rfl ⟨by decide, by decide⟩ a (.app0 (.lit _)) _ rfl
    (fun x => div_isSome rfl x _ (by decide))]
  exact hg

/-- **`x & c` bit by bit**: the definitions good, and the term `x & c`
wherever they hold. -/
theorem bandGo_spec {prev : List (LFml C)} {n : Nat} (hprev : Defs.Below n prev) :
    ∀ (f : Nat) (a : LTm C (.val .uint)) (c : Nat) (ds : List (LFml C)) (m : Nat),
    Defs.Good n m ds → a.atomBound ≤ m → 0 < c → c < 2 ^ f →
    Defs.Good n (bandGo prev f a c ds m).next (bandGo prev f a c ds m).defs ∧
    m ≤ (bandGo prev f a c ds m).next ∧
    (bandGo prev f a c ds m).term.atomBound ≤ (bandGo prev f a c ds m).next ∧
    ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν (bandGo prev f a c ds m).defs →
      LFml.AllHold σ ν ds ∧ ∀ (X : Nat) (x : PrimTy.uint.Denote), a.eval σ ν = some x → x.val = X →
        ∃ w : PrimTy.uint.Denote, (bandGo prev f a c ds m).term.eval σ ν = some w ∧
          w.val = ((X &&& c : Nat) : Int)
  | 0, a, c, ds, m, _, _, hc, hcf => absurd hcf (by simp only [Nat.pow_zero]; omega)
  | f + 1, a, c, ds, m, hds, ha, hc, hcf => by
    obtain ⟨hQg, hQlt, hQm, -, hQh⟩ := quotAtom_good (prev := prev) hds hprev (g := a)
      (e := a.divLit uintTwo) ha (by show max a.atomBound 0 ≤ m; omega) (half_isSome a)
    have hlow : ∀ σ ν, (LFml.defn a (a.divLit uintTwo) (quotAtom prev ds a (a.divLit uintTwo) m).1).holds σ ν →
        ∀ (X : Nat) (x : PrimTy.uint.Denote), a.eval σ ν = some x → x.val = X →
        ∃ w : PrimTy.uint.Denote,
          (a.remOf (quotAtom prev ds a (a.divLit uintTwo) m).1 uintTwo).eval σ ν = some w ∧
          w.val = ((X % 2 : Nat) : Int) := by
      intro σ ν hd X x hx hX
      have hq := half_val hd hx
      have hx1 := uint_val_lt x
      obtain ⟨u, hu, hu'⟩ := ev_mul (a := LTm.var (C := C) (p := .uint) (quotAtom prev ds a (a.divLit uintTwo) m).1)
        (b := .app0 (.lit uintTwo)) (LTm.eval_var σ ν _) (ev_lit _ σ ν)
        (by show (ν.get .uint _).val * 2 < _; rw [hq]; omega)
      obtain ⟨w, hw, hw'⟩ := ev_sub hx hu (by rw [hu']; show (ν.get .uint _).val * 2 ≤ _; rw [hq]; omega)
      refine ⟨w, hw, ?_⟩
      rw [hw', hu']
      show x.val - (ν.get .uint _).val * 2 = _
      rw [hq]; omega
    unfold bandGo
    split
    · rename_i h2
      have hc1 : c = 1 := by omega
      subst hc1
      dsimp only
      refine ⟨hQg, hQm, ?_, fun σ ν hp hd => ?_⟩
      · show max a.atomBound (max (max (_ + 1) 0) 0) ≤ _
        omega
      · obtain ⟨hds', hdefn⟩ := hQh σ ν hp hd
        refine ⟨hds', fun X x hx hX => ?_⟩
        rw [Nat.and_one_is_mod]
        exact hlow σ ν hdefn X x hx hX
    · rename_i h2
      dsimp only
      obtain ⟨hRg, hRm, hRb, hRh⟩ := bandGo_spec hprev f (.var (quotAtom prev ds a (a.divLit uintTwo) m).1)
        (c / 2) _ _ hQg (by show _ + 1 ≤ _; omega) (by omega)
        (by rw [Nat.pow_succ] at hcf; omega)
      have hval : ∀ σ ν, LFml.AllHold σ ν prev →
          LFml.AllHold σ ν (bandGo prev f (.var (quotAtom prev ds a (a.divLit uintTwo) m).1) (c / 2)
            (quotAtom prev ds a (a.divLit uintTwo) m).2.1 (quotAtom prev ds a (a.divLit uintTwo) m).2.2).defs →
          LFml.AllHold σ ν ds ∧ ∀ (X : Nat) (x : PrimTy.uint.Denote), a.eval σ ν = some x → x.val = X →
            (∃ w : PrimTy.uint.Denote, (a.remOf (quotAtom prev ds a (a.divLit uintTwo) m).1 uintTwo).eval σ ν = some w ∧
              w.val = ((X % 2 : Nat) : Int)) ∧
            ∃ w : PrimTy.uint.Denote, (LTm.app2 (.binop .mul rfl) (.app0 (.lit uintTwo))
              (bandGo prev f (.var (quotAtom prev ds a (a.divLit uintTwo) m).1) (c / 2)
                (quotAtom prev ds a (a.divLit uintTwo) m).2.1 (quotAtom prev ds a (a.divLit uintTwo) m).2.2).term).eval σ ν = some w ∧
              w.val = ((2 * ((X / 2) &&& (c / 2)) : Nat) : Int) := by
        intro σ ν hp hd
        obtain ⟨hQd, hrest⟩ := hRh σ ν hp hd
        obtain ⟨hds', hdefn⟩ := hQh σ ν hp hQd
        refine ⟨hds', fun X x hx hX => ⟨hlow σ ν hdefn X x hx hX, ?_⟩⟩
        have hq := half_val hdefn hx
        obtain ⟨r, hr, hr'⟩ := hrest (X / 2) _ (LTm.eval_var σ ν _) (by rw [hq, hX]; omega)
        have hle := Nat.and_le_left (n := X / 2) (m := c / 2)
        have hx1 := uint_val_lt x
        obtain ⟨w, hw, hw'⟩ := ev_mul (ev_lit uintTwo σ ν) hr
          (by rw [hr']; show 2 * _ < _; omega)
        exact ⟨w, hw, by rw [hw', hr']; show 2 * _ = _; omega⟩
      split
      · rename_i h3
        dsimp only
        refine ⟨hRg, by omega, by show max 0 _ ≤ _; omega, fun σ ν hp hd => ?_⟩
        obtain ⟨hds', hv⟩ := hval σ ν hp hd
        refine ⟨hds', fun X x hx hX => ?_⟩
        obtain ⟨-, w, hw, hw'⟩ := hv X x hx hX
        refine ⟨w, hw, ?_⟩
        rw [hw', BitArith.and_split X c, h3]
        simp only [Nat.mul_zero, Nat.zero_add]
      · rename_i h3
        dsimp only
        refine ⟨hRg, by omega, ?_, fun σ ν hp hd => ?_⟩
        · show max (max a.atomBound (max (max (_ + 1) 0) 0)) (max 0 _) ≤ _
          omega
        obtain ⟨hds', hv⟩ := hval σ ν hp hd
        refine ⟨hds', fun X x hx hX => ?_⟩
        obtain ⟨⟨l, hl, hl'⟩, w, hw, hw'⟩ := hv X x hx hX
        have hle := Nat.and_le_left (n := X / 2) (m := c / 2)
        have hx1 := uint_val_lt x
        obtain ⟨u, hu, hu'⟩ := ev_add hl hw (by rw [hl', hw']; omega)
        refine ⟨u, hu, ?_⟩
        rw [hu', hl', hw', BitArith.and_split X c, show c % 2 = 1 by omega, Nat.mul_one]
        omega

theorem ev_addW {a b : LTm C (.val .uint)} {σ : State C []} {ν : AEnv} {x y : PrimTy.uint.Denote}
    (ha : a.eval σ ν = some x) (hb : b.eval σ ν = some y) :
    ∃ w : PrimTy.uint.Denote, (LTm.app2 (.binop .addW rfl) a b).eval σ ν = some w ∧
      w.val = (x.val + y.val) % ((2 ^ 256 : Nat) : Int) :=
  ⟨_, (ev_bin rfl ⟨by decide, by decide⟩ ha hb).trans
    (uint_ofInt?_eq (Int.emod_nonneg _ (by decide)) (Int.emod_lt_of_pos _ (by decide))), rfl⟩

/-- An atom whose definition holds, past a returning `g`, holds the value its node returns. -/
theorem atom_val {p r : PrimTy} {g : LTm C (.val p)} {e : LTm C (.val r)} {q : Nat} {σ : State C []}
    {ν : AEnv} (hd : (LFml.defn g e q).holds σ ν) {x : p.Denote} (hx : g.eval σ ν = some x)
    {w : r.Denote} (hw : e.eval σ ν = some w) : ν.get r q = w := by
  have h := LFml.defn_eval hd hx
  rw [hw] at h
  exact (Option.some.inj h).symm

theorem seq_var_isSome {p r : PrimTy} (a : LTm C (.val p)) (q : Nat) (σ : State C []) (ν : AEnv) :
    ((LTm.seq a (LTm.var (p := r) q)).eval σ ν).isSome = (a.eval σ ν).isSome := by
  rw [LTm.eval_seq]
  cases a.eval σ ν <;> rfl

theorem seq_var_eval {p r : PrimTy} {a : LTm C (.val p)} (q : Nat) {σ : State C []} {ν : AEnv}
    {x : p.Denote} (hx : a.eval σ ν = some x) :
    (LTm.seq a (LTm.var (p := r) q)).eval σ ν = some (ν.get r q) := by
  rw [LTm.eval_seq, hx]; rfl

/-- **`x *% c` by doubling**: the definitions good, the term returning
exactly where `a` does, and `x·c mod 2^256` wherever they hold. -/
theorem mulWGo_spec {prev : List (LFml C)} {n : Nat} (hprev : Defs.Below n prev) (a : LTm C (.val .uint)) :
    ∀ (f c : Nat) (ds : List (LFml C)) (m : Nat), Defs.Good n m ds → a.atomBound ≤ m → 0 < c → c < 2 ^ f →
    Defs.Good n (mulWGo prev a f c ds m).next (mulWGo prev a f c ds m).defs ∧
    m ≤ (mulWGo prev a f c ds m).next ∧
    (mulWGo prev a f c ds m).term.atomBound ≤ (mulWGo prev a f c ds m).next ∧
    (∀ σ ν, ((mulWGo prev a f c ds m).term.eval σ ν).isSome = (a.eval σ ν).isSome) ∧
    ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν (mulWGo prev a f c ds m).defs →
      LFml.AllHold σ ν ds ∧ ∀ x : PrimTy.uint.Denote, a.eval σ ν = some x →
        ∃ w : PrimTy.uint.Denote, (mulWGo prev a f c ds m).term.eval σ ν = some w ∧
          w.val = x.val * (c : Int) % ((2 ^ 256 : Nat) : Int)
  | 0, c, _, _, _, _, hc, hcf => absurd hcf (by simp only [Nat.pow_zero]; omega)
  | f + 1, c, ds, m, hds, ha, hc, hcf => by
    unfold mulWGo
    split
    · rename_i h2
      have hc1 : c = 1 := by omega
      subst hc1
      dsimp only
      refine ⟨hds, Nat.le_refl _, ha, fun _ _ => rfl, fun σ ν _ hd => ⟨hd, fun x hx => ⟨x, hx, ?_⟩⟩⟩
      rw [show ((1 : Nat) : Int) = 1 from rfl, Int.mul_one, Int.emod_eq_of_lt (uint_val_nonneg x) (uint_val_lt x)]
    · rename_i h2
      obtain ⟨hHg, hHm, hHb, hHs, hHh⟩ := mulWGo_spec hprev a f (c / 2) ds m hds ha (by omega)
        (by rw [Nat.pow_succ] at hcf; omega)
      have hHt : ∀ σ ν, (a.eval σ ν).isSome = true →
          ((LTm.app2 (.binop .addW rfl) (mulWGo prev a f (c / 2) ds m).term
            (mulWGo prev a f (c / 2) ds m).term).eval σ ν).isSome = true := by
        intro σ ν hg
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ((hHs σ ν).trans hg)
        obtain ⟨w, hw, -⟩ := ev_addW hx hx
        rw [hw]; rfl
      obtain ⟨hDg, hDlt, hDm, -, hDh⟩ := quotAtom_good (prev := prev) hHg hprev (g := a)
        (e := .app2 (.binop .addW rfl) (mulWGo prev a f (c / 2) ds m).term (mulWGo prev a f (c / 2) ds m).term)
        (by omega) (by show max _ _ ≤ _; omega) hHt
      have hDv : ∀ σ ν, LFml.AllHold σ ν prev →
          LFml.AllHold σ ν (quotAtom prev (mulWGo prev a f (c / 2) ds m).defs a
            (.app2 (.binop .addW rfl) (mulWGo prev a f (c / 2) ds m).term (mulWGo prev a f (c / 2) ds m).term)
            (mulWGo prev a f (c / 2) ds m).next).2.1 →
          LFml.AllHold σ ν ds ∧ ∀ x : PrimTy.uint.Denote, a.eval σ ν = some x →
            (ν.get .uint (quotAtom prev (mulWGo prev a f (c / 2) ds m).defs a
              (.app2 (.binop .addW rfl) (mulWGo prev a f (c / 2) ds m).term (mulWGo prev a f (c / 2) ds m).term)
              (mulWGo prev a f (c / 2) ds m).next).1).val =
              x.val * ((2 * (c / 2) : Nat) : Int) % ((2 ^ 256 : Nat) : Int) := by
        intro σ ν hp hd
        obtain ⟨hHd, hdefn⟩ := hDh σ ν hp hd
        obtain ⟨hds', hH⟩ := hHh σ ν hp hHd
        refine ⟨hds', fun x hx => ?_⟩
        obtain ⟨u, hu, hu'⟩ := hH x hx
        obtain ⟨w, hw, hw'⟩ := ev_addW hu hu
        have hq : ν.get PrimTy.uint _ = w := atom_val hdefn hx hw
        rw [hq, hw', hu', BitArith.mulMod_double]
        congr 2
      split
      · rename_i h3
        dsimp only
        refine ⟨hDg, by omega, by show max a.atomBound (_ + 1) ≤ _; omega, fun σ ν => seq_var_isSome a _ σ ν,
          fun σ ν hp hd => ?_⟩
        obtain ⟨hds', hv⟩ := hDv σ ν hp hd
        refine ⟨hds', fun x hx => ⟨_, seq_var_eval _ hx, ?_⟩⟩
        rw [hv x hx]
        congr 2
        omega
      · rename_i h3
        dsimp only
        have hEt : ∀ σ ν, (a.eval σ ν).isSome = true →
            ((LTm.app2 (.binop .addW rfl) (LTm.seq a (LTm.var (p := .uint) (quotAtom prev
              (mulWGo prev a f (c / 2) ds m).defs a (.app2 (.binop .addW rfl) (mulWGo prev a f (c / 2) ds m).term
                (mulWGo prev a f (c / 2) ds m).term) (mulWGo prev a f (c / 2) ds m).next).1)) a).eval σ ν).isSome = true := by
          intro σ ν hg
          obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hg
          obtain ⟨w, hw, -⟩ := ev_addW (seq_var_eval _ hx) hx
          rw [hw]; rfl
        obtain ⟨hEg, hElt, hEm, -, hEh⟩ := quotAtom_good (prev := prev) hDg hprev (g := a)
          (by omega) (by show max (max a.atomBound (_ + 1)) a.atomBound ≤ _; omega) hEt
        refine ⟨hEg, by omega, by show max a.atomBound (_ + 1) ≤ _; omega, fun σ ν => seq_var_isSome a _ σ ν,
          fun σ ν hp hd => ?_⟩
        obtain ⟨hDd, hdefn⟩ := hEh σ ν hp hd
        obtain ⟨hds', hv⟩ := hDv σ ν hp hDd
        refine ⟨hds', fun x hx => ⟨_, seq_var_eval _ hx, ?_⟩⟩
        obtain ⟨w, hw, hw'⟩ := ev_addW (seq_var_eval _ hx) hx
        have hq : ν.get PrimTy.uint _ = w := atom_val hdefn hx hw
        rw [hq, hw', hv x hx, BitArith.mulMod_succ]
        congr 2
        omega

theorem uint_ofInt?_of_val {w : PrimTy.uint.Denote} {n : Int} (h : w.val = n) :
    PrimTy.uint.ofInt? n = some w := by
  rw [← h, uint_ofInt?_eq (uint_val_nonneg w) (uint_val_lt w)]
  rfl

theorem uint_toNat_cast (x : PrimTy.uint.Denote) : ((x.val.toNat : Nat) : Int) = x.val :=
  Int.toNat_of_nonneg (uint_val_nonneg x)

theorem uint_toNat_lt (x : PrimTy.uint.Denote) : x.val.toNat < 2 ^ 256 := by
  have h := uint_val_lt x
  rw [← uint_toNat_cast x] at h
  exact Int.ofNat_lt.mp h

theorem bitwise_toNat (f : Nat → Nat → Nat) (x v : PrimTy.uint.Denote) :
    Semantics.uintBitwise f x.val v.val = ((f x.val.toNat v.val.toNat : Nat) : Int) := by
  obtain ⟨X, hX⟩ := Int.eq_ofNat_of_zero_le (uint_val_nonneg x)
  obtain ⟨V, hV⟩ := Int.eq_ofNat_of_zero_le (uint_val_nonneg v)
  rw [hX, hV]; rfl

/-- A cut term that evaluates as `t` wherever its definitions hold. -/
theorem good_bind {r p : PrimTy} {t : LTm C (.val r)} {a : LTm C (.val p)} {F : p.Denote → Option r.Denote}
    {R : CutTm C (.val r)} {ds : List (LFml C)} {n : Nat} {prev : List (LFml C)}
    (hR : Defs.Good n R.next R.defs) (hb : R.term.atomBound ≤ R.next)
    (hRe : ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν R.defs →
      LFml.AllHold σ ν ds ∧ R.term.eval σ ν = (a.eval σ ν).bind F)
    (ht : ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν ds → t.eval σ ν = (a.eval σ ν).bind F) :
    CutTm.Good t n prev R :=
  ⟨hR, hb, fun σ ν hp hd => by obtain ⟨h1, h2⟩ := hRe σ ν hp hd; rw [h2, ht σ ν hp h1]⟩

theorem bandGo_top {prev : List (LFml C)} {n m : Nat} {ds : List (LFml C)} (hds : Defs.Good n m ds)
    (hprev : Defs.Below n prev) {a : LTm C (.val .uint)} (ha : a.atomBound ≤ m) {c : Nat} (hc0 : 0 < c)
    (hc : c < 2 ^ 256) (σ : State C []) (ν : AEnv) (hp : LFml.AllHold σ ν prev)
    (hd : LFml.AllHold σ ν (bandGo prev c a c ds m).defs) (x : PrimTy.uint.Denote)
    (hx : a.eval σ ν = some x) :
    (bandGo prev c a c ds m).term.eval σ ν = some ⟨_, uint_inRange (n := ((x.val.toNat &&& c : Nat) : Int))
      (Int.natCast_nonneg _) (Int.ofNat_lt.mpr (Nat.lt_of_le_of_lt Nat.and_le_left (uint_toNat_lt x)))⟩ := by
  obtain ⟨-, -, -, h⟩ := bandGo_spec hprev c a c ds m hds ha hc0 Nat.lt_two_pow_self
  obtain ⟨w, hw, hw'⟩ := (h σ ν hp hd).2 x.val.toNat x hx (uint_toNat_cast x).symm
  rw [hw]
  exact congrArg some (Subtype.ext hw')

theorem bandLit_spec {prev : List (LFml C)} {n m : Nat} {ds : List (LFml C)} (hds : Defs.Good n m ds)
    (hprev : Defs.Below n prev) {a : LTm C (.val .uint)} (ha : a.atomBound ≤ m) {c : Nat}
    (hc : c < 2 ^ 256) :
    Defs.Good n (bandLit prev a c ds m).next (bandLit prev a c ds m).defs ∧
    (bandLit prev a c ds m).term.atomBound ≤ (bandLit prev a c ds m).next ∧
    ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν (bandLit prev a c ds m).defs →
      LFml.AllHold σ ν ds ∧ (bandLit prev a c ds m).term.eval σ ν =
        (a.eval σ ν).bind fun x => PrimTy.uint.ofInt? ((x.val.toNat &&& c : Nat) : Int) := by
  unfold bandLit
  split
  · rename_i h0
    dsimp only
    subst h0
    refine ⟨hds, by show max _ 0 ≤ _; omega, fun σ ν _ hd => ⟨hd, ?_⟩⟩
    show (a.eval σ ν).bind (fun _ => some (PrimTy.dflt .uint)) = _
    cases a.eval σ ν with
    | none => simp only [Option.bind_none]
    | some x =>
      simp only [Option.bind_some, Nat.and_zero]
      exact (uint_ofInt?_of_val (w := PrimTy.dflt .uint) rfl).symm
  · rename_i h0
    dsimp only
    obtain ⟨hg, hm, hb, h⟩ := bandGo_spec hprev c a c ds m hds ha (by omega) Nat.lt_two_pow_self
    refine ⟨hg, by show max _ _ ≤ _; omega, fun σ ν hp hd => ⟨(h σ ν hp hd).1, ?_⟩⟩
    rw [LTm.eval_seq]
    cases hx : a.eval σ ν with
    | none => simp only [Option.bind_none]
    | some x =>
      obtain ⟨w, hw, hw'⟩ := (h σ ν hp hd).2 _ x hx (uint_toNat_cast x).symm
      rw [Option.bind_some, Option.bind_some, hw]
      exact (uint_ofInt?_of_val hw').symm

theorem borLit_spec {prev : List (LFml C)} {n m : Nat} {ds : List (LFml C)} (hds : Defs.Good n m ds)
    (hprev : Defs.Below n prev) {a : LTm C (.val .uint)} (ha : a.atomBound ≤ m) (v : PrimTy.uint.Denote) :
    Defs.Good n (borLit prev a v ds m).next (borLit prev a v ds m).defs ∧
    (borLit prev a v ds m).term.atomBound ≤ (borLit prev a v ds m).next ∧
    ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν (borLit prev a v ds m).defs →
      LFml.AllHold σ ν ds ∧ (borLit prev a v ds m).term.eval σ ν =
        (a.eval σ ν).bind fun x => PrimTy.uint.ofInt? ((x.val.toNat ||| v.val.toNat : Nat) : Int) := by
  unfold borLit
  split
  · rename_i h0
    dsimp only
    refine ⟨hds, ha, fun σ ν _ hd => ⟨hd, ?_⟩⟩
    cases a.eval σ ν with
    | none => simp only [Option.bind_none]
    | some x =>
      rw [Option.bind_some, h0, Nat.or_zero, uint_toNat_cast,
        uint_ofInt?_eq (uint_val_nonneg x) (uint_val_lt x)]
      rfl
  · rename_i h0
    dsimp only
    have hc := uint_toNat_lt v
    obtain ⟨hg, hm, hb, h⟩ := bandGo_spec hprev v.val.toNat a v.val.toNat ds m hds ha (by omega) Nat.lt_two_pow_self
    refine ⟨hg, by show max (max _ _) 0 ≤ _; omega, fun σ ν hp hd => ⟨(h σ ν hp hd).1, ?_⟩⟩
    cases hx : a.eval σ ν with
    | none =>
      rw [LTm.eval_binop_of rfl (shortT_none ⟨by decide, by decide⟩),
        LTm.eval_binop_of rfl (shortT_none ⟨by decide, by decide⟩), hx]
      simp only [Option.bind_none]
    | some x =>
      obtain ⟨t, ht, ht'⟩ := (h σ ν hp hd).2 _ x hx (uint_toNat_cast x).symm
      have hle := Nat.and_le_left (n := x.val.toNat) (m := v.val.toNat)
      have hor := BitArith.and_or_eq x.val.toNat v.val.toNat
      have hlt := Nat.or_lt_two_pow (uint_toNat_lt x) hc
      have hX := uint_toNat_cast x
      have hV := uint_toNat_cast v
      obtain ⟨w1, hw1, hw1'⟩ := ev_sub hx ht (by rw [ht']; omega)
      obtain ⟨w2, hw2, hw2'⟩ := ev_add hw1 (ev_lit v σ ν) (by rw [hw1', ht']; omega)
      rw [hw2, Option.bind_some]
      exact (uint_ofInt?_of_val (by rw [hw2', hw1', ht']; omega)).symm

theorem bxorLit_spec {prev : List (LFml C)} {n m : Nat} {ds : List (LFml C)} (hds : Defs.Good n m ds)
    (hprev : Defs.Below n prev) {a : LTm C (.val .uint)} (ha : a.atomBound ≤ m) (v : PrimTy.uint.Denote) :
    Defs.Good n (bxorLit prev a v ds m).next (bxorLit prev a v ds m).defs ∧
    (bxorLit prev a v ds m).term.atomBound ≤ (bxorLit prev a v ds m).next ∧
    ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν (bxorLit prev a v ds m).defs →
      LFml.AllHold σ ν ds ∧ (bxorLit prev a v ds m).term.eval σ ν =
        (a.eval σ ν).bind fun x => PrimTy.uint.ofInt? ((x.val.toNat ^^^ v.val.toNat : Nat) : Int) := by
  unfold bxorLit
  split
  · rename_i h0
    dsimp only
    refine ⟨hds, ha, fun σ ν _ hd => ⟨hd, ?_⟩⟩
    cases a.eval σ ν with
    | none => simp only [Option.bind_none]
    | some x =>
      rw [Option.bind_some, h0, Nat.xor_zero, uint_toNat_cast,
        uint_ofInt?_eq (uint_val_nonneg x) (uint_val_lt x)]
      rfl
  · rename_i h0
    dsimp only
    have hc := uint_toNat_lt v
    obtain ⟨hg, hm, hb, h⟩ := bandGo_spec hprev v.val.toNat a v.val.toNat ds m hds ha (by omega) Nat.lt_two_pow_self
    refine ⟨hg, by show max (max _ _) (max 0 _) ≤ _; omega, fun σ ν hp hd => ⟨(h σ ν hp hd).1, ?_⟩⟩
    cases hx : a.eval σ ν with
    | none =>
      rw [LTm.eval_binop_of rfl (shortT_none ⟨by decide, by decide⟩),
        LTm.eval_binop_of rfl (shortT_none ⟨by decide, by decide⟩), hx]
      simp only [Option.bind_none]
    | some x =>
      obtain ⟨t, ht, ht'⟩ := (h σ ν hp hd).2 _ x hx (uint_toNat_cast x).symm
      have hle := Nat.and_le_left (n := x.val.toNat) (m := v.val.toNat)
      have hle' := Nat.and_le_right (n := x.val.toNat) (m := v.val.toNat)
      have hxor := BitArith.xor_and_eq x.val.toNat v.val.toNat
      have hlt := Nat.xor_lt_two_pow (uint_toNat_lt x) hc
      have hX := uint_toNat_cast x
      have hV := uint_toNat_cast v
      obtain ⟨w1, hw1, hw1'⟩ := ev_sub hx ht (by rw [ht']; omega)
      obtain ⟨w3, hw3, hw3'⟩ := ev_sub (ev_lit v σ ν) ht (by rw [ht']; omega)
      obtain ⟨w2, hw2, hw2'⟩ := ev_add hw1 hw3 (by rw [hw1', hw3', ht']; omega)
      rw [hw2, Option.bind_some]
      exact (uint_ofInt?_of_val (by rw [hw2', hw1', hw3', ht']; omega)).symm

theorem mulWLit_spec {prev : List (LFml C)} {n m : Nat} {ds : List (LFml C)} (hds : Defs.Good n m ds)
    (hprev : Defs.Below n prev) {a : LTm C (.val .uint)} (ha : a.atomBound ≤ m) (v : PrimTy.uint.Denote) :
    Defs.Good n (mulWLit prev a v.val.toNat ds m).next (mulWLit prev a v.val.toNat ds m).defs ∧
    (mulWLit prev a v.val.toNat ds m).term.atomBound ≤ (mulWLit prev a v.val.toNat ds m).next ∧
    ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν (mulWLit prev a v.val.toNat ds m).defs →
      LFml.AllHold σ ν ds ∧ (mulWLit prev a v.val.toNat ds m).term.eval σ ν =
        (a.eval σ ν).bind fun x => BinOp.evalT .mulW rfl x v := by
  unfold mulWLit
  have hV := uint_toNat_cast v
  split
  · rename_i h0
    dsimp only
    refine ⟨hds, by show max _ 0 ≤ _; omega, fun σ ν _ hd => ⟨hd, ?_⟩⟩
    show (a.eval σ ν).bind (fun _ => some (PrimTy.dflt .uint)) = _
    cases a.eval σ ν with
    | none => simp only [Option.bind_none]
    | some x =>
      simp only [Option.bind_some]
      have hv0 : v.val = 0 := by omega
      show _ = (some (x.val * v.val % Semantics.uintBound)).bind PrimTy.uint.ofInt?
      rw [hv0, Int.mul_zero, Int.zero_emod, Option.bind_some, uint_ofInt?_eq (by decide) (by decide)]
      rfl
  · rename_i h0
    obtain ⟨hg, hm, hb, hs, h⟩ := mulWGo_spec hprev a v.val.toNat v.val.toNat ds m hds ha (by omega) Nat.lt_two_pow_self
    refine ⟨hg, hb, fun σ ν hp hd => ⟨(h σ ν hp hd).1, ?_⟩⟩
    cases hx : a.eval σ ν with
    | none =>
      have := hs σ ν
      rw [hx] at this
      cases hr : (mulWGo prev a v.val.toNat v.val.toNat ds m).term.eval σ ν with
      | none => simp only [Option.bind_none]
      | some _ => rw [hr] at this; cases this
    | some x =>
      obtain ⟨w, hw, hw'⟩ := (h σ ν hp hd).2 x hx
      rw [hw, Option.bind_some]
      show _ = (some (x.val * v.val % Semantics.uintBound)).bind PrimTy.uint.ofInt?
      rw [Option.bind_some, uint_ofInt?_of_val (w := w) (by rw [hw', hV]; rfl)]

/-! ## `addmod` and `mulmod` at a literal modulus are good -/

theorem emod_of_le_lt_two {s c : Int} (h0 : c ≤ s) (h1 : s < c + c) : s % c = s - c := by
  have hc : 0 < c := by omega
  rw [show s = (s - c) + c by omega, Int.add_emod_self, Int.emod_eq_of_lt (by omega) (by omega)]
  omega

theorem uint_ofInt?_isSome_iff (n : Int) :
    (PrimTy.uint.ofInt? n).isSome = true ↔ 0 ≤ n ∧ n < ((2 ^ 256 : Nat) : Int) := by
  simp only [PrimTy.ofInt?]
  split
  · rename_i hin
    simp only [PrimTy.inRange, decide_eq_true_eq] at hin
    simp only [Option.isSome_some, true_iff]
    exact hin
  · rename_i hin
    simp only [PrimTy.inRange, decide_eq_true_eq] at hin
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact hin

theorem subFrom_eval (c : PrimTy.uint.Denote) (w : LTm C (.val .uint)) (σ : State C []) (ν : AEnv) :
    (LTm.subFrom c w).eval σ ν = (w.eval σ ν).bind fun y => PrimTy.uint.ofInt? (c.val - y.val) := by
  unfold LTm.subFrom
  rw [LTm.eval_binop_of _ (shortT_none ⟨by decide, by decide⟩), ev_lit, Option.bind_some]
  rfl

theorem incr_eval (w : LTm C (.val .uint)) (σ : State C []) (ν : AEnv) :
    (LTm.incr w).eval σ ν = (w.eval σ ν).bind fun y => PrimTy.uint.ofInt? (y.val + 1) := by
  unfold LTm.incr
  rw [LTm.eval_binop_of _ (shortT_none ⟨by decide, by decide⟩)]
  cases w.eval σ ν <;> rfl

theorem subFrom_incr_isSome (c : PrimTy.uint.Denote) (w : LTm C (.val .uint)) (σ : State C []) (ν : AEnv) :
    ((LTm.subFrom c (LTm.incr w)).eval σ ν).isSome = true ↔
      ∃ x : PrimTy.uint.Denote, w.eval σ ν = some x ∧ x.val < c.val := by
  rw [subFrom_eval, incr_eval]
  have hc0 := uint_val_nonneg c
  have hc1 := uint_val_lt c
  cases w.eval σ ν with
  | none => simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true, reduceCtorEq, false_and,
      exists_false]
  | some x =>
    have hx0 := uint_val_nonneg x
    have hx1 := uint_val_lt x
    simp only [Option.bind_some, Option.some.injEq, exists_eq_left']
    by_cases hr : x.val + 1 < ((2 ^ 256 : Nat) : Int)
    · rw [uint_ofInt?_eq (by omega) hr, Option.bind_some, uint_ofInt?_isSome_iff]
      dsimp only
      constructor
      · rintro ⟨h, -⟩; show x.val < c.val; omega
      · intro h; constructor <;> omega
    · have : PrimTy.uint.ofInt? (x.val + 1) = none := by
        cases h : PrimTy.uint.ofInt? (x.val + 1) with
        | none => rfl
        | some _ =>
          have := (uint_ofInt?_isSome_iff (x.val + 1)).mp (by rw [h]; rfl)
          omega
      rw [this]
      simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true, false_iff]
      omega

theorem amodGuard_eval_isSome (g u v : LTm C (.val .uint)) (c : PrimTy.uint.Denote) (σ : State C [])
    (ν : AEnv) : ((amodGuard g u v c).eval σ ν).isSome = true ↔ (g.eval σ ν).isSome = true ∧
      (∃ x : PrimTy.uint.Denote, u.eval σ ν = some x ∧ x.val < c.val) ∧
      (∃ y : PrimTy.uint.Denote, v.eval σ ν = some y ∧ y.val < c.val) := by
  rw [← subFrom_incr_isSome c u σ ν, ← subFrom_incr_isSome c v σ ν]
  unfold amodGuard
  rw [LTm.eval_seq, LTm.eval_seq]
  cases g.eval σ ν <;> cases (LTm.subFrom c (LTm.incr u)).eval σ ν <;>
    cases (LTm.subFrom c (LTm.incr v)).eval σ ν <;> simp

theorem amodGuard_isSome {g u v : LTm C (.val .uint)} {c : PrimTy.uint.Denote} {σ : State C []}
    {ν : AEnv} {x y : PrimTy.uint.Denote} (hx : u.eval σ ν = some x) (hy : v.eval σ ν = some y)
    (hxc : x.val < c.val) (hyc : y.val < c.val) :
    ((amodGuard g u v c).eval σ ν).isSome = (g.eval σ ν).isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [amodGuard_eval_isSome]
  exact ⟨fun h => h.1, fun h => ⟨h, ⟨x, hx, hxc⟩, ⟨y, hy, hyc⟩⟩⟩

/-- **The case definition, at returning operands below `c`.** -/
theorem amodDef_iff {g u v : LTm C (.val .uint)} {c : PrimTy.uint.Denote} {k : Nat} {σ : State C []}
    {ν : AEnv} {x y : PrimTy.uint.Denote} (hx : u.eval σ ν = some x) (hy : v.eval σ ν = some y)
    (hxc : x.val < c.val) (hyc : y.val < c.val) :
    (amodDef g u v c k).holds σ ν ↔
      ((g.eval σ ν).isSome = true → (ν.get .uint k).val = (x.val + y.val) % c.val) := by
  have hc1 := uint_val_lt c
  have hx0 := uint_val_nonneg x
  have hy0 := uint_val_nonneg y
  obtain ⟨e, he, he'⟩ : ∃ e : PrimTy.uint.Denote, (LTm.subFrom c v).eval σ ν = some e ∧
      e.val = c.val - y.val := ev_sub (ev_lit c σ ν) hy (Int.le_of_lt hyc)
  have hC : (amodCond u v c).holds σ ν ↔ x.val < e.val := by
    unfold amodCond
    rw [LFml.holds_eq_iff, ev_bin rfl ⟨by decide, by decide⟩ hx he]
    constructor
    · rintro ⟨b, hb, hb'⟩
      have hb1 : b = true := (Option.some.inj hb').symm
      subst hb1
      have : decide (x.val < e.val) = true := Option.some.inj hb
      exact of_decide_eq_true this
    · intro h
      exact ⟨true, by show some (decide (x.val < e.val)) = some true; rw [decide_eq_true h], rfl⟩
  have hG : (LFml.eq (amodGuard g u v c) (amodGuard g u v c)).holds σ ν ↔
      (g.eval σ ν).isSome = true := by
    rw [LFml.holds_rets, ← Option.isSome_iff_exists, amodGuard_isSome hx hy hxc hyc]
  show ((LFml.eq (amodGuard g u v c) (amodGuard g u v c)).holds σ ν →
      ((amodCond u v c).holds σ ν → (LFml.eq (.app2 (.binop .add rfl) u v) (.var k)).holds σ ν) ∧
      (¬ (amodCond u v c).holds σ ν →
        (LFml.eq (.app2 (.binop .sub rfl) u (LTm.subFrom c v)) (.var k)).holds σ ν)) ↔ _
  rw [hG, hC]
  by_cases hc : x.val < e.val
  · obtain ⟨w, hw, hw'⟩ := ev_add hx hy (by omega)
    have hE : (LFml.eq (.app2 (.binop .add rfl) u v) (.var (C := C) (p := .uint) k)).holds σ ν ↔
        ν.get .uint k = w := by
      rw [LFml.holds_eq_iff, hw, LTm.eval_var]
      exact ⟨fun ⟨_, h1, h2⟩ => ((Option.some.inj h1 ▸ Option.some.inj h2).symm).symm,
        fun h => ⟨w, rfl, by rw [h]⟩⟩
    have hmod : (x.val + y.val) % c.val = x.val + y.val := Int.emod_eq_of_lt (by omega) (by omega)
    rw [hE]
    constructor
    · intro h hgs; rw [(h hgs).1 hc, hw', hmod]
    · intro h hgs
      exact ⟨fun _ => Subtype.ext (by rw [h hgs, hw', hmod]), fun hn => absurd hc hn⟩
  · obtain ⟨w, hw, hw'⟩ := ev_sub hx he (by omega)
    have hE : (LFml.eq (.app2 (.binop .sub rfl) u (LTm.subFrom c v)) (.var (C := C) (p := .uint) k)).holds σ ν ↔
        ν.get .uint k = w := by
      rw [LFml.holds_eq_iff, hw, LTm.eval_var]
      exact ⟨fun ⟨_, h1, h2⟩ => ((Option.some.inj h1 ▸ Option.some.inj h2).symm).symm,
        fun h => ⟨w, rfl, by rw [h]⟩⟩
    have hmod : (x.val + y.val) % c.val = x.val + y.val - c.val :=
      emod_of_le_lt_two (by omega) (by omega)
    rw [hE]
    constructor
    · intro h hgs; rw [(h hgs).2 hc, hw', hmod, he']; omega
    · intro h hgs
      exact ⟨fun h' => absurd h' hc, fun _ => Subtype.ext (by rw [h hgs, hw', hmod, he']; omega)⟩

theorem Defs.Good.amod {n m : Nat} {ds : List (LFml C)} (h : Defs.Good n m ds) {g u v : LTm C (.val .uint)}
    (c : PrimTy.uint.Denote) (hg : g.atomBound ≤ m) (hu : u.atomBound ≤ m) (hv : v.atomBound ≤ m) :
    Defs.Good n (m + 1) (ds ++ [amodDef g u v c m]) := by
  refine ⟨Nat.le_succ_of_le h.le, fun d hd => ?_, fun σ ν => ?_⟩
  · rcases List.mem_append.mp hd with hd | hd
    · exact Nat.le_succ_of_le (h.bound d hd)
    · rw [List.mem_singleton.mp hd]
      simp only [amodDef, amodGuard, amodCond, LTm.subFrom, LTm.incr, LFml.atomBound, LTm.atomBound]
      omega
  · obtain ⟨μ, hμ, hd⟩ := h.extend σ ν
    let w : PrimTy.uint.Denote := ((u.eval σ μ).bind fun x => (v.eval σ μ).bind fun y =>
      PrimTy.uint.ofInt? ((x.val + y.val) % c.val)).getD (PrimTy.dflt .uint)
    have hagree : μ.AgreesBelow m (μ.set .uint m w) := AEnv.AgreesBelow.set_ge μ .uint (Nat.le_refl _) w
    refine ⟨μ.set .uint m w, hμ.trans (hagree.mono h.le), (LFml.AllHold.append_iff σ _ _ _).mpr
      ⟨fun d hd' => (LFml.holds_agree_below σ d (hagree.mono (h.bound d hd'))).mp (hd d hd'), ?_⟩⟩
    intro d hd'
    rw [List.mem_singleton.mp hd']
    have hu' : u.eval σ (μ.set .uint m w) = u.eval σ μ := (u.eval_agree_below σ (hagree.mono hu)).symm
    have hv' : v.eval σ (μ.set .uint m w) = v.eval σ μ := (v.eval_agree_below σ (hagree.mono hv)).symm
    intro hG
    have hGs : ((amodGuard g u v c).eval σ (μ.set .uint m w)).isSome = true :=
      Option.isSome_iff_exists.mpr ((LFml.holds_rets σ _ _).mp hG)
    obtain ⟨-, ⟨x, hx, hxc⟩, ⟨y, hy, hyc⟩⟩ := (amodGuard_eval_isSome g u v c σ _).mp hGs
    refine (amodDef_iff (g := g) (k := m) hx hy hxc hyc).mpr (fun _ => ?_) hG
    rw [AEnv.get_set_self]
    have hx0 := uint_val_nonneg x
    have hy0 := uint_val_nonneg y
    have hc1 := uint_val_lt c
    have hr0 : 0 ≤ (x.val + y.val) % c.val := Int.emod_nonneg _ (by omega)
    have hr1 : (x.val + y.val) % c.val < c.val := Int.emod_lt_of_pos _ (by omega)
    show (((u.eval σ μ).bind fun x => (v.eval σ μ).bind fun y =>
      PrimTy.uint.ofInt? ((x.val + y.val) % c.val)).getD (PrimTy.dflt .uint)).val = _
    rw [← hu', ← hv', hx, hy, Option.bind_some, Option.bind_some, uint_ofInt?_eq hr0 (by omega)]
    rfl

/-- **What `amodAtom` satisfies**: its definition good, and `(x + y) mod c`
wherever it holds and the operands return below `c`. -/
theorem amodAtom_spec {n m : Nat} {ds : List (LFml C)} (hds : Defs.Good n m ds)
    {g u v : LTm C (.val .uint)} (c : PrimTy.uint.Denote) (hg : g.atomBound ≤ m) (hu : u.atomBound ≤ m)
    (hv : v.atomBound ≤ m) :
    Defs.Good n (amodAtom g u v c ds m).next (amodAtom g u v c ds m).defs ∧
    m ≤ (amodAtom g u v c ds m).next ∧
    (amodAtom g u v c ds m).term.atomBound ≤ (amodAtom g u v c ds m).next ∧
    (∀ σ ν, ((amodAtom g u v c ds m).term.eval σ ν).isSome = (g.eval σ ν).isSome) ∧
    ∀ σ ν, LFml.AllHold σ ν (amodAtom g u v c ds m).defs → LFml.AllHold σ ν ds ∧
      ∀ x y : PrimTy.uint.Denote, u.eval σ ν = some x → v.eval σ ν = some y → x.val < c.val →
        y.val < c.val → (g.eval σ ν).isSome = true →
        ∃ w : PrimTy.uint.Denote, (amodAtom g u v c ds m).term.eval σ ν = some w ∧
          w.val = (x.val + y.val) % c.val := by
  refine ⟨hds.amod c hg hu hv, Nat.le_succ _, by show max g.atomBound (m + 1) ≤ m + 1; omega,
    fun σ ν => seq_var_isSome g m σ ν, fun σ ν hd => ?_⟩
  obtain ⟨h1, h2⟩ := (LFml.AllHold.append_iff σ ν _ _).mp hd
  refine ⟨h1, fun x y hx hy hxc hyc hgs => ?_⟩
  obtain ⟨gv, hgv⟩ := Option.isSome_iff_exists.mp hgs
  exact ⟨_, seq_var_eval m hgv, (amodDef_iff hx hy hxc hyc).mp (h2 _ List.mem_cons_self) hgs⟩

/-- **A remainder by a nonzero literal**, through its quotient's atom. -/
theorem rem_spec {prev ds : List (LFml C)} {n m : Nat} (hds : Defs.Good n m ds)
    (hprev : Defs.Below n prev) {a : LTm C (.val .uint)} (ha : a.atomBound ≤ m) (c : PrimTy.uint.Denote)
    (hc : c.val ≠ 0) :
    Defs.Good n (CutTm.rem prev a c ds m).next (CutTm.rem prev a c ds m).defs ∧
    m ≤ (CutTm.rem prev a c ds m).next ∧
    (CutTm.rem prev a c ds m).term.atomBound ≤ (CutTm.rem prev a c ds m).next ∧
    ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν (CutTm.rem prev a c ds m).defs →
      LFml.AllHold σ ν ds ∧ (a.eval σ ν = none → (CutTm.rem prev a c ds m).term.eval σ ν = none) ∧
      ∀ x : PrimTy.uint.Denote, a.eval σ ν = some x →
        ∃ w : PrimTy.uint.Denote, (CutTm.rem prev a c ds m).term.eval σ ν = some w ∧
          w.val = x.val % c.val := by
  unfold CutTm.rem
  have hQ := quotAtom_good (prev := prev) hds hprev (g := a) (e := a.divLit c) ha
    (by show max a.atomBound 0 ≤ m; omega) (fun σ ν hg => by
      rw [LTm.divLit, isSome_binop_lit rfl ⟨by decide, by decide⟩ a (.app0 (.lit c)) c rfl
        (fun x => div_isSome rfl x c hc)]
      exact hg)
  generalize quotAtom prev ds a (a.divLit c) m = Q at hQ ⊢
  obtain ⟨hQg, hQlt, hQm, -, hQh⟩ := hQ
  dsimp only
  refine ⟨hQg, hQm, by simp only [LTm.remOf, LTm.atomBound]; omega, fun σ ν hp hd => ?_⟩
  obtain ⟨hds', hdefn⟩ := hQh σ ν hp hd
  refine ⟨hds', fun hx => ?_, fun x hx => ?_⟩
  · show (LTm.app2 (.binop .sub rfl) a _).eval σ ν = none
    rw [LTm.eval_binop_of rfl (shortT_none ⟨by decide, by decide⟩), hx]
    rfl
  · have hq := LFml.defn_eval hdefn hx
    rw [LTm.divLit, ev_bin rfl ⟨by decide, by decide⟩ hx (ev_lit _ σ ν)] at hq
    have hrem := rem_eval rfl x c _ hc hq
    have hx0 := uint_val_nonneg x
    have hx1 := uint_val_lt x
    have hc0 := uint_val_nonneg c
    have hc1 := uint_val_lt c
    have hr0 : 0 ≤ x.val % c.val := Int.emod_nonneg _ hc
    have hr1 : x.val % c.val < c.val := Int.emod_lt_of_pos _ (by omega)
    refine ⟨⟨x.val % c.val, uint_inRange hr0 (by have := uint_val_lt c; omega)⟩, ?_, rfl⟩
    show (LTm.app2 (.binop .sub rfl) a (.app2 (.binop .mul rfl) (.var _) (.app0 (.lit c)))).eval σ ν = _
    rw [LTm.eval_binop_of rfl (shortT_none ⟨by decide, by decide⟩), hx, Option.bind_some,
      ev_bin rfl ⟨by decide, by decide⟩ (LTm.eval_var σ ν _) (ev_lit c σ ν)]
    rw [hrem]
    show (if c.val = 0 then none else some (Int.tmod x.val c.val)).bind PrimTy.uint.ofInt? = _
    rw [if_neg hc, Option.bind_some, Int.tmod_eq_emod_of_nonneg hx0, uint_ofInt?_eq hr0 (by omega)]

theorem addmod_val (x y c : PrimTy.uint.Denote) (hc : c.val ≠ 0) :
    ModOp.evalT .addmod x y c = PrimTy.uint.ofInt? ((x.val + y.val) % c.val) := by
  unfold ModOp.evalT ModOp.wide
  rw [if_neg hc]

theorem mulmod_val (x y c : PrimTy.uint.Denote) (hc : c.val ≠ 0) :
    ModOp.evalT .mulmod x y c = PrimTy.uint.ofInt? (x.val * y.val % c.val) := by
  unfold ModOp.evalT ModOp.wide
  rw [if_neg hc]

theorem addmodLit_spec {prev ds : List (LFml C)} {n m : Nat} (hds : Defs.Good n m ds)
    (hprev : Defs.Below n prev) {a b : LTm C (.val .uint)} (ha : a.atomBound ≤ m) (hb : b.atomBound ≤ m)
    (c : PrimTy.uint.Denote) (hc : c.val ≠ 0) :
    Defs.Good n (addmodLit prev a b c ds m).next (addmodLit prev a b c ds m).defs ∧
    (addmodLit prev a b c ds m).term.atomBound ≤ (addmodLit prev a b c ds m).next ∧
    ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν (addmodLit prev a b c ds m).defs →
      LFml.AllHold σ ν ds ∧ (addmodLit prev a b c ds m).term.eval σ ν =
        (a.eval σ ν).bind fun x => (b.eval σ ν).bind fun y => ModOp.evalT .addmod x y c := by
  unfold addmodLit
  dsimp only
  have hA := rem_spec hds hprev ha c hc
  generalize CutTm.rem prev a c ds m = RA at hA ⊢
  obtain ⟨gA, mA, bA, hA⟩ := hA
  have hB := rem_spec gA hprev (a := b) (by omega) c hc
  generalize CutTm.rem prev b c RA.defs RA.next = RB at hB ⊢
  obtain ⟨gB, mB, bB, hB⟩ := hB
  obtain ⟨gD, -, bD, sD, hD⟩ := amodAtom_spec gB c (g := .seq a b) (u := RA.term) (v := RB.term)
    (by show max a.atomBound b.atomBound ≤ _; omega) (by omega) bB
  refine ⟨gD, bD, fun σ ν hp hd => ?_⟩
  obtain ⟨hdB, hv⟩ := hD σ ν hd
  obtain ⟨hdA, hBn, hBs⟩ := hB σ ν hp hdB
  obtain ⟨hds', hAn, hAs⟩ := hA σ ν hp hdA
  refine ⟨hds', ?_⟩
  have hc0 := uint_val_nonneg c
  have hcpos : 0 < c.val := by omega
  cases hx : a.eval σ ν with
  | none =>
    have := sD σ ν
    rw [LTm.eval_seq, hx] at this
    simp only [Option.bind_none, Option.isSome_none] at this
    cases ht : (amodAtom (LTm.seq a b) RA.term RB.term c RB.defs RB.next).term.eval σ ν with
    | none => rfl
    | some _ => rw [ht] at this; cases this
  | some x =>
    cases hy : b.eval σ ν with
    | none =>
      have := sD σ ν
      rw [LTm.eval_seq, hx, hy] at this
      simp only [Option.bind_some, Option.isSome_none] at this
      cases ht : (amodAtom (LTm.seq a b) RA.term RB.term c RB.defs RB.next).term.eval σ ν with
      | none => rfl
      | some _ => rw [ht] at this; cases this
    | some y =>
      obtain ⟨u, hu, hu'⟩ := hAs x hx
      obtain ⟨v, hv', hv''⟩ := hBs y hy
      obtain ⟨w, hw, hw'⟩ := hv u v hu hv' (by rw [hu']; exact Int.emod_lt_of_pos _ hcpos)
        (by rw [hv'']; exact Int.emod_lt_of_pos _ hcpos) (by rw [LTm.eval_seq, hx, hy]; rfl)
      rw [hw, Option.bind_some, Option.bind_some, addmod_val x y c hc]
      refine (uint_ofInt?_of_val ?_).symm
      rw [hw', hu', hv'', ← Int.add_emod]

theorem mulmodGo_spec {n : Nat} (a : LTm C (.val .uint)) (c : PrimTy.uint.Denote) :
    ∀ (f k : Nat) (ds : List (LFml C)) (m : Nat), Defs.Good n m ds → a.atomBound ≤ m → 0 < k →
    k < 2 ^ f →
    Defs.Good n (mulmodGo a c f k ds m).next (mulmodGo a c f k ds m).defs ∧
    m ≤ (mulmodGo a c f k ds m).next ∧
    (mulmodGo a c f k ds m).term.atomBound ≤ (mulmodGo a c f k ds m).next ∧
    (∀ σ ν, ((mulmodGo a c f k ds m).term.eval σ ν).isSome = (a.eval σ ν).isSome) ∧
    ∀ σ ν, LFml.AllHold σ ν (mulmodGo a c f k ds m).defs → LFml.AllHold σ ν ds ∧
      ∀ x : PrimTy.uint.Denote, a.eval σ ν = some x → x.val < c.val →
        ∃ w : PrimTy.uint.Denote, (mulmodGo a c f k ds m).term.eval σ ν = some w ∧
          w.val = x.val * (k : Int) % c.val
  | 0, k, _, _, _, _, hk, hkf => absurd hkf (by simp only [Nat.pow_zero]; omega)
  | f + 1, k, ds, m, hds, ha, hk, hkf => by
    unfold mulmodGo
    split
    · rename_i h2
      have hk1 : k = 1 := by omega
      subst hk1
      dsimp only
      refine ⟨hds, Nat.le_refl _, ha, fun _ _ => rfl, fun σ ν hd => ⟨hd, fun x hx hxc => ⟨x, hx, ?_⟩⟩⟩
      rw [show ((1 : Nat) : Int) = 1 from rfl, Int.mul_one,
        Int.emod_eq_of_lt (uint_val_nonneg x) hxc]
    · rename_i h2
      obtain ⟨hHg, hHm, hHb, hHs, hHh⟩ := mulmodGo_spec a c f (k / 2) ds m hds ha (by omega)
        (by rw [Nat.pow_succ] at hkf; omega)
      generalize mulmodGo a c f (k / 2) ds m = H at hHg hHm hHb hHs hHh
      dsimp only
      obtain ⟨hDg, hDm, hDb, hDs, hDh⟩ := amodAtom_spec hHg c (g := a) (by omega) hHb hHb
      have hDv : ∀ σ ν, LFml.AllHold σ ν (amodAtom a H.term H.term c H.defs H.next).defs →
          LFml.AllHold σ ν ds ∧ ∀ x : PrimTy.uint.Denote, a.eval σ ν = some x → x.val < c.val →
            ∃ w : PrimTy.uint.Denote, (amodAtom a H.term H.term c H.defs H.next).term.eval σ ν = some w ∧
              w.val = x.val * ((2 * (k / 2) : Nat) : Int) % c.val := by
        intro σ ν hd
        obtain ⟨hHd, hD⟩ := hDh σ ν hd
        obtain ⟨hds', hH⟩ := hHh σ ν hHd
        refine ⟨hds', fun x hx hxc => ?_⟩
        have hcpos : 0 < c.val := by have := uint_val_nonneg x; omega
        obtain ⟨h, hh, hh'⟩ := hH x hx hxc
        have hlt : h.val < c.val := by rw [hh']; exact Int.emod_lt_of_pos _ hcpos
        obtain ⟨w, hw, hw'⟩ := hD h h hh hh hlt hlt (by rw [hx]; rfl)
        refine ⟨w, hw, ?_⟩
        rw [hw', hh', BitArith.mulMod_double]
        congr 2
      split
      · rename_i h3
        refine ⟨hDg, by omega, hDb, fun σ ν => (hDs σ ν), fun σ ν hd => ?_⟩
        obtain ⟨hds', hv⟩ := hDv σ ν hd
        refine ⟨hds', fun x hx hxc => ?_⟩
        obtain ⟨w, hw, hw'⟩ := hv x hx hxc
        refine ⟨w, hw, ?_⟩
        rw [hw']
        congr 2
        omega
      · rename_i h3
        obtain ⟨hEg, hEm, hEb, hEs, hEh⟩ := amodAtom_spec hDg c (g := a) (u := (amodAtom a H.term H.term c H.defs H.next).term)
          (v := a) (by omega) hDb (by omega)
        refine ⟨hEg, by omega, hEb, fun σ ν => hEs σ ν, fun σ ν hd => ?_⟩
        obtain ⟨hDd, hE⟩ := hEh σ ν hd
        obtain ⟨hds', hv⟩ := hDv σ ν hDd
        refine ⟨hds', fun x hx hxc => ?_⟩
        have hcpos : 0 < c.val := by have := uint_val_nonneg x; omega
        obtain ⟨d, hd', hd''⟩ := hv x hx hxc
        have hlt : d.val < c.val := by rw [hd'']; exact Int.emod_lt_of_pos _ hcpos
        obtain ⟨w, hw, hw'⟩ := hE d x hd' hx hlt hxc (by rw [hx]; rfl)
        refine ⟨w, hw, ?_⟩
        rw [hw', hd'', BitArith.mulMod_succ]
        congr 2
        omega

theorem mulmodLit_spec {prev ds : List (LFml C)} {n m : Nat} (hds : Defs.Good n m ds)
    (hprev : Defs.Below n prev) {a : LTm C (.val .uint)} (ha : a.atomBound ≤ m)
    (k c : PrimTy.uint.Denote) (hc : c.val ≠ 0) :
    Defs.Good n (mulmodLit prev a k c ds m).next (mulmodLit prev a k c ds m).defs ∧
    (mulmodLit prev a k c ds m).term.atomBound ≤ (mulmodLit prev a k c ds m).next ∧
    ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν (mulmodLit prev a k c ds m).defs →
      LFml.AllHold σ ν ds ∧ (mulmodLit prev a k c ds m).term.eval σ ν =
        (a.eval σ ν).bind fun x => ModOp.evalT .mulmod x k c := by
  have hc0 := uint_val_nonneg c
  have hc1 := uint_val_lt c
  have hk0 := uint_val_nonneg k
  have hcpos : 0 < c.val := by omega
  have hK : ((k.val.toNat % c.val.toNat : Nat) : Int) = k.val % c.val := by
    rw [Int.natCast_emod, Int.toNat_of_nonneg hk0, Int.toNat_of_nonneg hc0]
  unfold mulmodLit
  split
  · rename_i h0
    refine ⟨hds, by dsimp only; simp only [LTm.atomBound]; omega, fun σ ν _ hd => ⟨hd, ?_⟩⟩
    show (LTm.seq a _).eval σ ν = _
    rw [LTm.eval_seq]
    cases a.eval σ ν with
    | none => rfl
    | some x =>
      rw [Option.bind_some, Option.bind_some, mulmod_val x k c hc]
      refine (uint_ofInt?_of_val (w := PrimTy.dflt .uint) ?_).symm
      have hz : k.val % c.val = 0 := by rw [← hK, h0]; rfl
      rw [Int.mul_emod, hz, Int.mul_zero, Int.zero_emod]
      rfl
  · rename_i h0
    dsimp only
    have hR := rem_spec hds hprev ha c hc
    generalize CutTm.rem prev a c ds m = R at hR ⊢
    obtain ⟨gR, mR, bR, hR⟩ := hR
    have hkc : k.val.toNat % c.val.toNat < 2 ^ (k.val.toNat % c.val.toNat) := Nat.lt_two_pow_self
    obtain ⟨gG, -, bG, sG, hG⟩ := mulmodGo_spec R.term c _ _ R.defs R.next gR bR (by omega) hkc
    refine ⟨gG, bG, fun σ ν hp hd => ?_⟩
    obtain ⟨hdR, hv⟩ := hG σ ν hd
    obtain ⟨hds', hRn, hRs⟩ := hR σ ν hp hdR
    refine ⟨hds', ?_⟩
    cases hx : a.eval σ ν with
    | none =>
      have h1 := sG σ ν
      rw [hRn hx] at h1
      simp only [Option.isSome_none] at h1
      cases ht : (mulmodGo R.term c _ _ R.defs R.next).term.eval σ ν with
      | none => rfl
      | some _ => rw [ht] at h1; cases h1
    | some x =>
      obtain ⟨u, hu, hu'⟩ := hRs x hx
      obtain ⟨w, hw, hw'⟩ := hv u hu (by rw [hu']; exact Int.emod_lt_of_pos _ hcpos)
      rw [hw, Option.bind_some, mulmod_val x k c hc]
      refine (uint_ofInt?_of_val ?_).symm
      rw [hw', hu', hK, ← Int.mul_emod]

/-! ## `&`, `|`, `^` at `int` with a literal, through the words -/

/-- Two `int`s' bitwise operator is the one of their words, read back in two's
complement, for an operator that keeps the nonnegative ones below `2^255`. -/
theorem int_bitwise_eq (f : Nat → Nat → Nat)
    (hf : ∀ a b, a < 2 ^ 255 → b < 2 ^ 255 → f a b < 2 ^ 255) (x y : Int)
    (hx : -((2 ^ 255 : Nat) : Int) ≤ x ∧ x < ((2 ^ 255 : Nat) : Int))
    (hy : -((2 ^ 255 : Nat) : Int) ≤ y ∧ y < ((2 ^ 255 : Nat) : Int)) :
    Semantics.uintBitwise f x y = Semantics.signedOf (f (Semantics.wordOf x) (Semantics.wordOf y)) := by
  cases x with
  | ofNat a =>
    cases y with
    | ofNat b =>
      simp only [Int.ofNat_eq_coe] at hx hy
      have ha : a < 2 ^ 255 := by have := hx.2; omega
      have hb : b < 2 ^ 255 := by have := hy.2; omega
      have hw : ∀ c : Nat, c < 2 ^ 255 → Semantics.wordOf (Int.ofNat c) = c := fun c hc => by
        unfold Semantics.wordOf
        rw [Int.ofNat_eq_coe, Int.emod_eq_of_lt (Int.natCast_nonneg c) (by omega)]
        rfl
      show Int.ofNat (f a b) = _
      rw [hw a ha, hw b hb]
      unfold Semantics.signedOf
      rw [if_pos (hf a b ha hb)]
      rfl
    | negSucc b => rfl
  | negSucc a => cases y <;> rfl

theorem and_lt255 (a b : Nat) (ha : a < 2 ^ 255) (_ : b < 2 ^ 255) : a &&& b < 2 ^ 255 :=
  Nat.lt_of_le_of_lt Nat.and_le_left ha

theorem or_lt255 (a b : Nat) (ha : a < 2 ^ 255) (hb : b < 2 ^ 255) : a ||| b < 2 ^ 255 :=
  Nat.or_lt_two_pow ha hb

theorem xor_lt255 (a b : Nat) (ha : a < 2 ^ 255) (hb : b < 2 ^ 255) : a ^^^ b < 2 ^ 255 :=
  Nat.xor_lt_two_pow ha hb

theorem band_int_val (h : BinOp.band.accepts .int = true) (x v : PrimTy.int.Denote) :
    BinOp.evalT .band h x v = PrimTy.int.ofInt?
      (Semantics.signedOf (Semantics.wordOf x.val &&& (intWord v).val.toNat)) := by
  show (some (Semantics.uintBitwise _ x.val v.val)).bind PrimTy.int.ofInt? = _
  rw [Option.bind_some, int_bitwise_eq _ and_lt255 x.val v.val (int_val_bounds x) (int_val_bounds v)]
  rfl

theorem bor_int_val (h : BinOp.bor.accepts .int = true) (x v : PrimTy.int.Denote) :
    BinOp.evalT .bor h x v = PrimTy.int.ofInt?
      (Semantics.signedOf (Semantics.wordOf x.val ||| (intWord v).val.toNat)) := by
  show (some (Semantics.uintBitwise _ x.val v.val)).bind PrimTy.int.ofInt? = _
  rw [Option.bind_some, int_bitwise_eq _ or_lt255 x.val v.val (int_val_bounds x) (int_val_bounds v)]
  rfl

theorem bxor_int_val (h : BinOp.bxor.accepts .int = true) (x v : PrimTy.int.Denote) :
    BinOp.evalT .bxor h x v = PrimTy.int.ofInt?
      (Semantics.signedOf (Semantics.wordOf x.val ^^^ (intWord v).val.toNat)) := by
  show (some (Semantics.uintBitwise _ x.val v.val)).bind PrimTy.int.ofInt? = _
  rw [Option.bind_some, int_bitwise_eq _ xor_lt255 x.val v.val (int_val_bounds x) (int_val_bounds v)]
  rfl

theorem band_int_valL (h : BinOp.band.accepts .int = true) (v y : PrimTy.int.Denote) :
    BinOp.evalT .band h v y = PrimTy.int.ofInt?
      (Semantics.signedOf (Semantics.wordOf y.val &&& (intWord v).val.toNat)) := by
  rw [band_int_val h v y]
  exact congrArg (fun k => PrimTy.int.ofInt? (Semantics.signedOf k)) (Nat.and_comm _ _)

theorem bor_int_valL (h : BinOp.bor.accepts .int = true) (v y : PrimTy.int.Denote) :
    BinOp.evalT .bor h v y = PrimTy.int.ofInt?
      (Semantics.signedOf (Semantics.wordOf y.val ||| (intWord v).val.toNat)) := by
  rw [bor_int_val h v y]
  exact congrArg (fun k => PrimTy.int.ofInt? (Semantics.signedOf k)) (Nat.or_comm _ _)

theorem bxor_int_valL (h : BinOp.bxor.accepts .int = true) (v y : PrimTy.int.Denote) :
    BinOp.evalT .bxor h v y = PrimTy.int.ofInt?
      (Semantics.signedOf (Semantics.wordOf y.val ^^^ (intWord v).val.toNat)) := by
  rw [bxor_int_val h v y]
  exact congrArg (fun k => PrimTy.int.ofInt? (Semantics.signedOf k)) (Nat.xor_comm _ _)

/-- A word read back as an `int`: `signedOf`. -/
theorem toInt_signed (w : PrimTy.uint.Denote) (r : Nat) (hw : w.val = (r : Int)) :
    UnOp.evalT .toInt rfl w = PrimTy.int.ofInt? (Semantics.signedOf r) := by
  show PrimTy.int.ofInt? (if w.val < Semantics.intBound then w.val else w.val - Semantics.uintBound) = _
  unfold Semantics.signedOf
  rw [hw]
  by_cases hc : r < 2 ^ 255
  · rw [if_pos (show (r : Int) < Semantics.intBound from Int.ofNat_lt.mpr hc), if_pos hc]
  · rw [if_neg (show ¬ (r : Int) < Semantics.intBound from fun h => hc (Int.ofNat_lt.mp h)), if_neg hc]
    rfl

theorem wordOf_lt (x : Int) : Semantics.wordOf x < 2 ^ 256 := by
  unfold Semantics.wordOf
  have h0 := Int.emod_nonneg x (show ((2 ^ 256 : Nat) : Int) ≠ 0 by decide)
  have h1 := Int.emod_lt_of_pos x (show (0 : Int) < ((2 ^ 256 : Nat) : Int) by decide)
  omega

/-- **`a ⊙ v` at `int` through the words**: the definitions good, and the
operator's value wherever they hold. -/
theorem intBit_spec {prev : List (LFml C)} {n m : Nat} {ds : List (LFml C)} (hds : Defs.Good n m ds)
    (hprev : Defs.Below n prev) {a : LTm C (.val .int)} (ha : a.atomBound ≤ m)
    {mk : LTm C (.val .uint) → List (LFml C) → Nat → CutTm C (.val .uint)} {F : Nat → Nat}
    (hF : ∀ k, k < 2 ^ 256 → F k < 2 ^ 256)
    (hmk : ∀ (t : LTm C (.val .uint)) (ds' : List (LFml C)) (m' : Nat), Defs.Good n m' ds' →
      t.atomBound ≤ m' →
      Defs.Good n (mk t ds' m').next (mk t ds' m').defs ∧ (mk t ds' m').term.atomBound ≤ (mk t ds' m').next ∧
      ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν (mk t ds' m').defs →
        LFml.AllHold σ ν ds' ∧ (mk t ds' m').term.eval σ ν =
          (t.eval σ ν).bind fun x => PrimTy.uint.ofInt? ((F x.val.toNat : Nat) : Int)) :
    Defs.Good n (intBit prev mk a ds m).next (intBit prev mk a ds m).defs ∧
    (intBit prev mk a ds m).term.atomBound ≤ (intBit prev mk a ds m).next ∧
    ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν (intBit prev mk a ds m).defs →
      LFml.AllHold σ ν ds ∧ (intBit prev mk a ds m).term.eval σ ν =
        (a.eval σ ν).bind fun x => PrimTy.int.ofInt? (Semantics.signedOf (F (Semantics.wordOf x.val))) := by
  unfold intBit CutTm.atom
  dsimp only
  generalize hQ : quotAtom prev ds a (.app1 (.unop .toUint rfl) a) m = Q
  have hU := quotAtom_good (prev := prev) hds hprev (g := a) (e := .app1 (.unop .toUint rfl) a) ha
    (by show a.atomBound ≤ m; exact ha)
    (fun σ ν hg => by
      rw [LTm.eval_app1, Close.Op1.eval_unop]
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hg
      rw [hx, Option.bind_some]
      exact toUint_isSome rfl x)
  rw [hQ] at hU
  obtain ⟨hUg, hUlt, hUm, -, hUh⟩ := hU
  have hUb : (LTm.seq a (LTm.var (p := .uint) Q.1)).atomBound ≤ Q.2.2 := by
    show max a.atomBound (Q.1 + 1) ≤ Q.2.2; omega
  obtain ⟨hTg, hTb, hTh⟩ := hmk (.seq a (.var Q.1)) Q.2.1 Q.2.2 hUg hUb
  generalize hT : mk (.seq a (.var Q.1)) Q.2.1 Q.2.2 = T at hTg hTb hTh
  have hR := quotAtom_good (prev := prev) hTg hprev (g := T.term)
    (e := .app1 (.unop .toInt rfl) T.term) hTb (by show T.term.atomBound ≤ T.next; exact hTb) (fun σ ν hg => by
      rw [LTm.eval_app1, Close.Op1.eval_unop]
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hg
      rw [hx, Option.bind_some]
      exact toInt_isSome rfl x)
  obtain ⟨hRg, hRlt, hRm, -, hRh⟩ := hR
  refine ⟨hRg, by show max T.term.atomBound (_ + 1) ≤ _; omega, fun σ ν hp hd => ?_⟩
  obtain ⟨hTd, hdR⟩ := hRh σ ν hp hd
  obtain ⟨hUd, hTe⟩ := hTh σ ν hp hTd
  obtain ⟨hds', hdU⟩ := hUh σ ν hp hUd
  refine ⟨hds', ?_⟩
  rw [LTm.eval_seq]
  cases hx : a.eval σ ν with
  | none =>
    rw [hTe, LTm.eval_seq, hx]
    rfl
  | some x =>
    have hu : (LTm.app1 (.unop .toUint rfl) a).eval σ ν = some (ν.get .uint Q.1) := LFml.defn_eval hdU hx
    rw [LTm.eval_app1, Close.Op1.eval_unop, hx, Option.bind_some] at hu
    have hu' : (ν.get .uint Q.1).val = x.val % Semantics.uintBound := by
      have : PrimTy.uint.ofInt? (x.val % Semantics.uintBound) = some (ν.get .uint Q.1) := hu
      rw [uint_ofInt?_eq (n := x.val % Semantics.uintBound) (Int.emod_nonneg _ (by decide))
        (Int.emod_lt_of_pos _ (by decide))] at this
      rw [← Option.some.inj this]
    have hTv : T.term.eval σ ν = PrimTy.uint.ofInt? ((F (Semantics.wordOf x.val) : Nat) : Int) := by
      rw [hTe, seq_var_eval _ hx, Option.bind_some, hu']
      rfl
    have hlt := hF _ (wordOf_lt x.val)
    have hw := uint_ofInt?_eq (n := ((F (Semantics.wordOf x.val) : Nat) : Int)) (Int.natCast_nonneg _)
      (by omega)
    have hTw := hTv.trans hw
    have hr : (LTm.app1 (.unop .toInt rfl) T.term).eval σ ν = some (ν.get .int _) := LFml.defn_eval hdR hTw
    rw [LTm.eval_app1, Close.Op1.eval_unop, hTw, Option.bind_some, toInt_signed _ _ rfl] at hr
    rw [hTw, Option.bind_some, Option.bind_some]
    exact hr.symm

theorem cut1_good {a s : Srt} (o : Op1 C a s) {x : LTm C a} {n : Nat} {prev : List (LFml C)}
    {A : CutTm C a} (hA : CutTm.Good x n prev A) (hprev : Defs.Below n prev) :
    CutTm.Good (.app1 o x) n prev (cut1 o prev A) := by
  have hgen : CutTm.Good (.app1 o x) n prev ⟨.app1 o A.term, A.defs, A.next⟩ :=
    hA.node1 (LTm.app1 o) (fun _ => rfl) (fun g ν y hy => by rw [LTm.eval_app1, LTm.eval_app1, hy])
  have hev : ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν A.defs →
      (LTm.app1 o A.term).eval σ ν = (LTm.app1 o x).eval σ ν := fun σ ν hp hd => hgen.eval σ ν hp hd
  cases o with
  | @unop op p h =>
    cases op <;> cases p <;> first | exact hgen | skip
    · exact CutTm.Good.atom hA.defs hprev hA.bound hA.bound (fun σ ν => by
        rw [LTm.eval_app1, Close.Op1.eval_unop]
        cases A.term.eval σ ν with
        | none => rfl
        | some y => simp only [Option.bind_some, toInt_isSome, Option.isSome_some]) hev
    · exact CutTm.Good.atom hA.defs hprev hA.bound hA.bound (fun σ ν => by
        rw [LTm.eval_app1, Close.Op1.eval_unop]
        cases A.term.eval σ ν with
        | none => rfl
        | some y => simp only [Option.bind_some, toUint_isSome, Option.isSome_some]) hev
  | _ => exact hgen

/-! ## The literal cases of `cut2` -/

theorem good_litR {op : BinOp} {p : PrimTy} (h : op.accepts p = true) (hop : op ≠ .and ∧ op ≠ .or)
    {x y : LTm C (.val p)} {n : Nat} {prev : List (LFml C)} {A B : CutTm C (.val p)} {v : p.Denote}
    (heq : B.term = .app0 (.lit v))
    (hxe : ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν (A.defs ++ B.defs) → A.term.eval σ ν = x.eval σ ν)
    (hye : ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν (A.defs ++ B.defs) → B.term.eval σ ν = y.eval σ ν)
    {R : CutTm C (.val (op.ret p))} (hR : Defs.Good n R.next R.defs) (hb : R.term.atomBound ≤ R.next)
    (hRe : ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν R.defs → LFml.AllHold σ ν (A.defs ++ B.defs) ∧
      R.term.eval σ ν = (A.term.eval σ ν).bind fun xv => op.evalT h xv v) :
    CutTm.Good (.app2 (.binop op h) x y) n prev R :=
  good_bind (a := A.term) (F := fun xv => op.evalT h xv v) hR hb hRe (fun σ ν hp hd => by
    rw [LTm.eval_binop_of h (shortT_none hop), ← hxe σ ν hp hd, ← hye σ ν hp hd, heq]; rfl)

theorem good_litL {op : BinOp} {p : PrimTy} (h : op.accepts p = true) (hop : op ≠ .and ∧ op ≠ .or)
    {x y : LTm C (.val p)} {n : Nat} {prev : List (LFml C)} {A B : CutTm C (.val p)} {v : p.Denote}
    (heq : A.term = .app0 (.lit v))
    (hxe : ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν (A.defs ++ B.defs) → A.term.eval σ ν = x.eval σ ν)
    (hye : ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν (A.defs ++ B.defs) → B.term.eval σ ν = y.eval σ ν)
    {R : CutTm C (.val (op.ret p))} (hR : Defs.Good n R.next R.defs) (hb : R.term.atomBound ≤ R.next)
    (hRe : ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν R.defs → LFml.AllHold σ ν (A.defs ++ B.defs) ∧
      R.term.eval σ ν = (B.term.eval σ ν).bind fun yv => op.evalT h v yv) :
    CutTm.Good (.app2 (.binop op h) x y) n prev R :=
  good_bind (a := B.term) (F := fun yv => op.evalT h v yv) hR hb hRe (fun σ ν hp hd => by
    rw [LTm.eval_binop_of h (shortT_none hop), ← hxe σ ν hp hd, ← hye σ ν hp hd, heq]
    show _ = (B.term.eval σ ν).bind _
    cases B.term.eval σ ν <;> rfl)

/-- `a` then failure: `a / 0`, `a % 0`. -/
theorem seq_err_spec {p : PrimTy} {n m : Nat} {ds prev : List (LFml C)} (hds : Defs.Good n m ds)
    {a : LTm C (.val p)} (ha : a.atomBound ≤ m) {r : PrimTy} {F : p.Denote → Option r.Denote}
    (hF : ∀ x, F x = none) :
    Defs.Good n m ds ∧ (LTm.seq a (LTm.err (s := .val r))).atomBound ≤ m ∧
      ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν ds → LFml.AllHold σ ν ds ∧
        (LTm.seq a (LTm.err (s := .val r))).eval σ ν = (a.eval σ ν).bind F :=
  ⟨hds, by show max _ 0 ≤ _; omega, fun σ ν _ hd => ⟨hd, by
    rw [LTm.eval_seq]; cases a.eval σ ν with
    | none => rfl
    | some x => rw [Option.bind_some, Option.bind_some, hF]; rfl⟩⟩

theorem div_zero {p : PrimTy} (h : BinOp.div.accepts p = true) (x v : p.Denote) (hp : p.isNumeric = true)
    (hv : Linear.ScalarCode.integer p v = 0) : BinOp.evalT .div h x v = none := by
  cases p with
  | bool => cases hp
  | uint => show (if v.val = 0 then none else _).bind _ = none; rw [if_pos (show v.val = 0 from hv)]; rfl
  | int => show (if v.val = 0 then none else _).bind _ = none; rw [if_pos (show v.val = 0 from hv)]; rfl

theorem mod_zero {p : PrimTy} (h : BinOp.mod.accepts p = true) (x v : p.Denote) (hp : p.isNumeric = true)
    (hv : Linear.ScalarCode.integer p v = 0) : BinOp.evalT .mod h x v = none := by
  cases p with
  | bool => cases hp
  | uint => show (if v.val = 0 then none else _).bind _ = none; rw [if_pos (show v.val = 0 from hv)]; rfl
  | int => show (if v.val = 0 then none else _).bind _ = none; rw [if_pos (show v.val = 0 from hv)]; rfl

theorem band_val (h : BinOp.band.accepts .uint = true) (x v : PrimTy.uint.Denote) :
    BinOp.evalT .band h x v = PrimTy.uint.ofInt? ((x.val.toNat &&& v.val.toNat : Nat) : Int) := by
  show (some (Semantics.uintBitwise _ x.val v.val)).bind PrimTy.uint.ofInt? = _
  rw [Option.bind_some, bitwise_toNat]

theorem bor_val (h : BinOp.bor.accepts .uint = true) (x v : PrimTy.uint.Denote) :
    BinOp.evalT .bor h x v = PrimTy.uint.ofInt? ((x.val.toNat ||| v.val.toNat : Nat) : Int) := by
  show (some (Semantics.uintBitwise _ x.val v.val)).bind PrimTy.uint.ofInt? = _
  rw [Option.bind_some, bitwise_toNat]

theorem bxor_val (h : BinOp.bxor.accepts .uint = true) (x v : PrimTy.uint.Denote) :
    BinOp.evalT .bxor h x v = PrimTy.uint.ofInt? ((x.val.toNat ^^^ v.val.toNat : Nat) : Int) := by
  show (some (Semantics.uintBitwise _ x.val v.val)).bind PrimTy.uint.ofInt? = _
  rw [Option.bind_some, bitwise_toNat]

theorem mulW_comm (h : BinOp.mulW.accepts .uint = true) (x v : PrimTy.uint.Denote) :
    BinOp.evalT .mulW h v x = BinOp.evalT .mulW rfl x v := by
  show (some (v.val * x.val % Semantics.uintBound)).bind PrimTy.uint.ofInt? =
    (some (x.val * v.val % Semantics.uintBound)).bind PrimTy.uint.ofInt?
  rw [Int.mul_comm]

/-- `x ** 0 = 1`, `x ** 1 = x`. -/
theorem pow_lit (h : BinOp.pow.accepts .uint = true) (x v : PrimTy.uint.Denote) :
    (v.val = 0 → BinOp.evalT .pow h x v = some uintOne) ∧ (v.val = 1 → BinOp.evalT .pow h x v = some x) := by
  have hx0 := uint_val_nonneg x
  have hx1 := uint_val_lt x
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · show (if v.val < 0 then none else some (x.val ^ v.val.toNat)).bind PrimTy.uint.ofInt? = _
    rw [hv, if_neg (by decide), Option.bind_some, show (0 : Int).toNat = 0 from rfl, Int.pow_zero]
    exact uint_ofInt?_eq (by decide) (by decide)
  · show (if v.val < 0 then none else some (x.val ^ v.val.toNat)).bind PrimTy.uint.ofInt? = _
    rw [hv, if_neg (by decide), Option.bind_some, show (1 : Int).toNat = 1 from rfl, Int.pow_succ, Int.pow_zero, Int.one_mul,
      uint_ofInt?_eq hx0 hx1]
    rfl

/-- `x **% 0 = 1`, `x **% 1 = x`. -/
theorem powW_lit (h : BinOp.powW.accepts .uint = true) (x v : PrimTy.uint.Denote) :
    (v.val = 0 → BinOp.evalT .powW h x v = some uintOne) ∧ (v.val = 1 → BinOp.evalT .powW h x v = some x) := by
  have hx0 := uint_val_nonneg x
  have hx1 := uint_val_lt x
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · show (if v.val < 0 then none else some (x.val ^ v.val.toNat % Semantics.uintBound)).bind
      PrimTy.uint.ofInt? = _
    rw [hv, if_neg (by decide), Option.bind_some, show (0 : Int).toNat = 0 from rfl, Int.pow_zero]
    exact uint_ofInt?_eq (by decide) (by decide)
  · show (if v.val < 0 then none else some (x.val ^ v.val.toNat % Semantics.uintBound)).bind
      PrimTy.uint.ofInt? = _
    rw [hv, if_neg (by decide), Option.bind_some, show (1 : Int).toNat = 1 from rfl, Int.pow_succ, Int.pow_zero, Int.one_mul]
    show PrimTy.uint.ofInt? (x.val % ((2 ^ 256 : Nat) : Int)) = _
    rw [Int.emod_eq_of_lt hx0 hx1, uint_ofInt?_eq hx0 hx1]
    rfl

theorem powLit_spec (h : BinOp.pow.accepts .uint = true)
    {n m : Nat} {ds prev : List (LFml C)} (hds : Defs.Good n m ds) {a : LTm C (.val .uint)}
    (ha : a.atomBound ≤ m) (v : PrimTy.uint.Denote) (hv : v.val = 0 ∨ v.val = 1) :
    Defs.Good n m ds ∧ (powLit (.app2 (.binop .pow h) a (.app0 (.lit v))) a v).atomBound ≤ m ∧
      ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν ds → LFml.AllHold σ ν ds ∧
        (powLit (.app2 (.binop .pow h) a (.app0 (.lit v))) a v).eval σ ν =
          (a.eval σ ν).bind fun xv => BinOp.evalT .pow h xv v := by
  unfold powLit
  rcases hv with hv | hv
  · rw [if_pos hv]
    refine ⟨hds, by show max _ 0 ≤ _; omega, fun σ ν _ hd => ⟨hd, ?_⟩⟩
    rw [LTm.eval_seq]
    cases a.eval σ ν with
    | none => rfl
    | some x => rw [Option.bind_some, Option.bind_some, (pow_lit h x v).1 hv]; rfl
  · rw [if_neg (by omega), if_pos hv]
    refine ⟨hds, ha, fun σ ν _ hd => ⟨hd, ?_⟩⟩
    cases a.eval σ ν with
    | none => rfl
    | some x => rw [Option.bind_some, (pow_lit h x v).2 hv]

theorem powWLit_spec (h : BinOp.powW.accepts .uint = true)
    {n m : Nat} {ds prev : List (LFml C)} (hds : Defs.Good n m ds) {a : LTm C (.val .uint)}
    (ha : a.atomBound ≤ m) (v : PrimTy.uint.Denote) (hv : v.val = 0 ∨ v.val = 1) :
    Defs.Good n m ds ∧ (powLit (.app2 (.binop .powW h) a (.app0 (.lit v))) a v).atomBound ≤ m ∧
      ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν ds → LFml.AllHold σ ν ds ∧
        (powLit (.app2 (.binop .powW h) a (.app0 (.lit v))) a v).eval σ ν =
          (a.eval σ ν).bind fun xv => BinOp.evalT .powW h xv v := by
  unfold powLit
  rcases hv with hv | hv
  · rw [if_pos hv]
    refine ⟨hds, by show max _ 0 ≤ _; omega, fun σ ν _ hd => ⟨hd, ?_⟩⟩
    rw [LTm.eval_seq]
    cases a.eval σ ν with
    | none => rfl
    | some x => rw [Option.bind_some, Option.bind_some, (powW_lit h x v).1 hv]; rfl
  · rw [if_neg (by omega), if_pos hv]
    refine ⟨hds, ha, fun σ ν _ hd => ⟨hd, ?_⟩⟩
    cases a.eval σ ν with
    | none => rfl
    | some x => rw [Option.bind_some, (powW_lit h x v).2 hv]

theorem int_div_neg_one (h : BinOp.div.accepts .int = true) (x v : PrimTy.int.Denote) (hv : v.val = -1) :
    BinOp.evalT .div h x v = UnOp.evalT .neg rfl x := by
  show (if v.val = 0 then none else some (Int.tdiv x.val v.val)).bind PrimTy.int.ofInt? =
    PrimTy.int.ofInt? (-x.val)
  rw [hv, if_neg (by decide), Option.bind_some, BitArith.tdiv_neg_one]

theorem int_mod_neg_one (h : BinOp.mod.accepts .int = true) (x v : PrimTy.int.Denote) (hv : v.val = -1) :
    BinOp.evalT .mod h x v = some (PrimTy.dflt .int) := by
  show (if v.val = 0 then none else some (Int.tmod x.val v.val)).bind PrimTy.int.ofInt? = _
  rw [hv, if_neg (by decide), Option.bind_some, BitArith.tmod_neg_one]
  rfl

theorem int_div_isSome (h : BinOp.div.accepts .int = true) (x v : PrimTy.int.Denote) (hv0 : v.val ≠ 0)
    (hv1 : v.val ≠ -1) : (BinOp.evalT .div h x v).isSome = true := by
  have hx := int_val_bounds x
  show ((if v.val = 0 then none else some (Int.tdiv x.val v.val)).bind PrimTy.int.ofInt?).isSome = true
  rw [if_neg hv0, Option.bind_some]
  have := BitArith.tdiv_bounds x.val v.val _ hx.1 hx.2 hv0 hv1
  exact ofInt?_isSome' rfl (int_inRange this.1 this.2)

theorem int_rem_eval (h : BinOp.mod.accepts .int = true) (x v q : PrimTy.int.Denote) (hv : v.val ≠ 0)
    (hq : BinOp.evalT .div rfl x v = some q) :
    (BinOp.evalT .mul rfl q v).bind (BinOp.evalT .sub rfl x) = BinOp.evalT .mod h x v := by
  have hx := int_val_bounds x
  have hq' : q.val = Int.tdiv x.val v.val := by
    have : ((if v.val = 0 then none else some (Int.tdiv x.val v.val)).bind PrimTy.int.ofInt?) = some q := hq
    rw [if_neg hv, Option.bind_some, PrimTy.ofInt?_eq_some_iff rfl] at this
    exact this
  have hm := Int.tmod_def x.val v.val
  have hb := BitArith.tmod_bounds x.val v.val
  have hqv : q.val * v.val = x.val - Int.tmod x.val v.val := by rw [hm, hq', Int.mul_comm]; omega
  show ((PrimTy.int.ofInt? (q.val * v.val)).bind fun w => PrimTy.int.ofInt? (x.val - w.val)) =
    (if v.val = 0 then none else some (Int.tmod x.val v.val)).bind PrimTy.int.ofInt?
  rw [if_neg hv, Option.bind_some]
  have hin : PrimTy.int.inRange (q.val * v.val) = true := int_inRange (by omega) (by omega)
  rw [show PrimTy.int.ofInt? (q.val * v.val) = some ⟨_, hin⟩ by simp only [PrimTy.ofInt?, dif_pos hin],
    Option.bind_some]
  show PrimTy.int.ofInt? (x.val - q.val * v.val) = _
  rw [hqv]
  congr 1
  omega

theorem cut2_good {a b s : Srt} (o : Op2 C a b s) {x : LTm C a} {y : LTm C b} {n : Nat}
    {prev : List (LFml C)} {A : CutTm C a} {B : CutTm C b} (hA : CutTm.Good x n prev A)
    (hB : CutTm.Good y A.next (prev ++ A.defs) B) (hprev : Defs.Below n prev) :
    CutTm.Good (.app2 o x y) n prev (cut2 o prev A B) := by
  have hgen : CutTm.Good (.app2 o x y) n prev ⟨.app2 o A.term B.term, A.defs ++ B.defs, B.next⟩ :=
    hA.node2 hB (LTm.app2 o) (fun _ _ => rfl)
      (fun g ν x' y' hx hy => by rw [LTm.eval_app2, LTm.eval_app2, hx, hy])
  have hds : Defs.Good n B.next (A.defs ++ B.defs) := hA.defs.append hB.defs
  have hAb : A.term.atomBound ≤ B.next := Nat.le_trans hA.bound hB.defs.le
  have hev : ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν (A.defs ++ B.defs) →
      (LTm.app2 o A.term B.term).eval σ ν = (LTm.app2 o x y).eval σ ν :=
    fun σ ν hp hd => hgen.eval σ ν hp hd
  have hye : ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν (A.defs ++ B.defs) →
      B.term.eval σ ν = y.eval σ ν := fun σ ν hp hd => by
    obtain ⟨ha, hb⟩ := (LFml.AllHold.append_iff σ ν _ _).mp hd
    exact hB.eval σ ν (hp.append ha) hb
  have hxe : ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν (A.defs ++ B.defs) →
      A.term.eval σ ν = x.eval σ ν := fun σ ν hp hd => by
    obtain ⟨ha, -⟩ := (LFml.AllHold.append_iff σ ν _ _).mp hd
    exact hA.eval σ ν hp ha
  have hprev' : Defs.Below n prev := hprev
  cases o with
  | @binop op p h =>
    cases op <;> cases p <;> first | exact hgen | skip
    case div.uint =>
      dsimp only [cut2]
      split
      · rename_i v heq
        split
        · rename_i hv
          obtain ⟨g1, g2, g3⟩ := seq_err_spec (prev := prev) (r := .uint) hds hAb
            (F := fun xv => BinOp.evalT .div h xv v) (fun xv => div_zero h xv v rfl hv)
          exact good_litR h ⟨by decide, by decide⟩ heq hxe hye g1 g2 g3
        · rename_i hv
          exact CutTm.Good.atom hds hprev' hAb
            (by show max A.term.atomBound B.term.atomBound ≤ B.next; have := hB.bound; omega)
            (isSome_binop_lit h ⟨by decide, by decide⟩ A.term B.term v heq (fun x => div_isSome h x v hv))
            hev
      · exact hgen
    case mod.uint =>
      dsimp only [cut2]
      split
      · rename_i v heq
        split
        · rename_i hv
          obtain ⟨g1, g2, g3⟩ := seq_err_spec (prev := prev) (r := .uint) hds hAb
            (F := fun xv => BinOp.evalT .mod h xv v) (fun xv => mod_zero h xv v rfl hv)
          exact good_litR h ⟨by decide, by decide⟩ heq hxe hye g1 g2 g3
        · rename_i hv
          refine CutTm.Good.quot hds hprev' (fun k => A.term.remOf k v) hAb
            (by show max A.term.atomBound 0 ≤ B.next; omega)
            (fun k j hk hm => by
              show max A.term.atomBound (max (k + 1) 0) ≤ j
              omega)
            (fun σ ν hg => by
              rw [LTm.divLit, isSome_binop_lit rfl ⟨by decide, by decide⟩ A.term (.app0 (.lit v)) v rfl
                (fun x => div_isSome rfl x v hv)]
              exact hg) ?_
          intro σ ν k hp hd hdefn
          have hy : y.eval σ ν = some v := by rw [← hye σ ν hp hd, heq]; rfl
          rw [LTm.eval_binop_of h (shortT_none ⟨by decide, by decide⟩) x y, hy, ← hxe σ ν hp hd]
          show (LTm.app2 (.binop .sub rfl) A.term _).eval σ ν = _
          rw [LTm.eval_binop_of rfl (shortT_none ⟨by decide, by decide⟩)]
          cases hx : A.term.eval σ ν with
          | none => rfl
          | some xv =>
            have hq := LFml.defn_eval hdefn hx
            rw [LTm.divLit, LTm.eval_binop_of rfl (shortT_none ⟨by decide, by decide⟩), hx] at hq
            simp only [Option.bind_some]
            rw [LTm.eval_binop_of rfl (shortT_none ⟨by decide, by decide⟩)]
            exact rem_eval h xv v _ hv hq
      · exact hgen
    case shl.uint =>
      dsimp only [cut2]
      split
      · rename_i v heq
        have hy : ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν (A.defs ++ B.defs) →
            y.eval σ ν = some v := fun σ ν hp hd => by rw [← hye σ ν hp hd, heq]; rfl
        unfold cutShl
        split
        · rename_i h0
          refine ⟨hds, hAb, fun σ ν hp hd => ?_⟩
          show A.term.eval σ ν = _
          rw [LTm.eval_binop_of h (shortT_none ⟨by decide, by decide⟩) x y, hy σ ν hp hd,
            hxe σ ν hp hd]
          cases x.eval σ ν with
          | none => rfl
          | some xv => exact (shl_zero h xv v h0).symm
        · split
          · rename_i h0 hk
            have hd : 256 - v.val.toNat < 256 := by have := uint_val_nonneg v; omega
            have he : v.val.toNat < 256 := by have := uint_val_nonneg v; omega
            refine CutTm.Good.quot hds hprev' (fun k => LTm.app2 (.binop .mul rfl)
              (A.term.remOf k (uintPow (256 - v.val.toNat) hd)) (.app0 (.lit (uintPow v.val.toNat he)))) hAb
              (by show max A.term.atomBound 0 ≤ B.next; omega)
              (fun k j hk' hm => by
                show max (max A.term.atomBound (max (k + 1) 0)) 0 ≤ j
                omega)
              (fun σ ν hg => by
                rw [LTm.divLit, isSome_binop_lit rfl ⟨by decide, by decide⟩ A.term _ _ rfl
                  (fun x => div_isSome rfl x _ (by
                    show ((2 ^ (256 - v.val.toNat) : Nat) : Int) ≠ 0
                    have := Nat.two_pow_pos (256 - v.val.toNat); omega))]
                exact hg) ?_
            intro σ ν k hp hd hdefn
            rw [LTm.eval_binop_of h (shortT_none ⟨by decide, by decide⟩) x y, hy σ ν hp hd,
              ← hxe σ ν hp hd]
            rw [LTm.eval_binop_of rfl (shortT_none ⟨by decide, by decide⟩)]
            show ((LTm.remOf A.term k _).eval σ ν).bind _ = _
            rw [LTm.remOf, LTm.eval_binop_of rfl (shortT_none ⟨by decide, by decide⟩)]
            cases hx : A.term.eval σ ν with
            | none => rfl
            | some xv =>
              have hq := LFml.defn_eval hdefn hx
              rw [LTm.divLit, LTm.eval_binop_of rfl (shortT_none ⟨by decide, by decide⟩), hx] at hq
              simp only [Option.bind_some]
              rw [LTm.eval_binop_of rfl (shortT_none ⟨by decide, by decide⟩)]
              exact shl_eval h xv v _ h0 hk _ _ hq
          · rename_i h0 hk
            refine ⟨hds, by show max A.term.atomBound 0 ≤ B.next; omega, fun σ ν hp hd => ?_⟩
            rw [LTm.eval_binop_of h (shortT_none ⟨by decide, by decide⟩) x y, hy σ ν hp hd,
              LTm.eval_seq, hxe σ ν hp hd]
            cases x.eval σ ν with
            | none => rfl
            | some xv => exact (shl_big h xv v hk).symm
      · exact hgen
    case shr.bool => exact absurd h (by decide)
    case shr.uint | shr.int =>
      dsimp only [cut2]
      split
      · rename_i v heq
        exact CutTm.Good.atom hds hprev' hAb
          (by show max A.term.atomBound B.term.atomBound ≤ B.next; have := hB.bound; omega)
          (isSome_binop_lit h ⟨by decide, by decide⟩ A.term B.term v heq (fun x => shr_isSome h x v))
          hev
      · exact hgen
    case band.uint =>
      dsimp only [cut2]
      unfold cutBand
      split
      · rename_i k hk
        obtain ⟨v, heq, hv, hk256⟩ := LTm.maskOf?_spec hk
        refine maskCut_good hds hprev' hAb k hk256 (fun σ ν hp hd => ?_)
        rw [LTm.eval_binop_of h (shortT_none ⟨by decide, by decide⟩) x y, ← hxe σ ν hp hd,
          show y.eval σ ν = some v by rw [← hye σ ν hp hd, heq]; rfl]
        cases A.term.eval σ ν with
        | none => rfl
        | some xv => exact band_mask h xv v k hv
      · split
        · rename_i k hk
          obtain ⟨v, heq, hv, hk256⟩ := LTm.maskOf?_spec hk
          refine maskCut_good hds hprev' hB.bound k hk256 (fun σ ν hp hd => ?_)
          rw [LTm.eval_binop_of h (shortT_none ⟨by decide, by decide⟩) x y, ← hye σ ν hp hd,
            show x.eval σ ν = some v by rw [← hxe σ ν hp hd, heq]; rfl]
          cases B.term.eval σ ν with
          | none => rfl
          | some yv => exact (band_comm h yv v).trans (band_mask h yv v k hv)
        · split
          · rename_i r _
            have heq := r.2
            obtain ⟨g1, g2, g3⟩ := bandLit_spec hds hprev' hAb (uint_toNat_lt r.1)
            exact good_litR h ⟨by decide, by decide⟩ heq hxe hye g1 g2 (fun σ ν hp hd => by
              obtain ⟨r1, r2⟩ := g3 σ ν hp hd
              exact ⟨r1, r2.trans (congrArg _ (funext fun xv => (band_val h xv _).symm))⟩)
          · rename_i r _ _
            have heq := r.2
            obtain ⟨g1, g2, g3⟩ := bandLit_spec hds hprev' hB.bound (uint_toNat_lt r.1)
            exact good_litL h ⟨by decide, by decide⟩ heq hxe hye g1 g2 (fun σ ν hp hd => by
              obtain ⟨r1, r2⟩ := g3 σ ν hp hd
              exact ⟨r1, r2.trans (congrArg _ (funext fun yv => ((band_comm h yv _).trans (band_val h yv _)).symm))⟩)
          · exact hgen
    case addW.uint =>
      exact CutTm.Good.atom hds hprev'
        (by show max A.term.atomBound B.term.atomBound ≤ B.next; have := hB.bound; omega)
        (by show max A.term.atomBound B.term.atomBound ≤ B.next; have := hB.bound; omega)
        (isSome_binop2 h ⟨by decide, by decide⟩ A.term B.term (addW_isSome h)) hev
    case pow.uint =>
      dsimp only [cut2]
      split
      · rename_i v heq
        by_cases hv : v.val = 0 ∨ v.val = 1
        · obtain ⟨g1, g2, g3⟩ := powLit_spec (prev := prev) h hds hAb v hv
          rw [← heq] at g2 g3
          exact good_litR h ⟨by decide, by decide⟩ heq hxe hye g1 g2 g3
        · have : powLit (.app2 (.binop .pow h) A.term B.term) A.term v = .app2 (.binop .pow h) A.term B.term := by
            unfold powLit; rw [if_neg (by omega), if_neg (by omega)]
          rw [this]; exact hgen
      · exact hgen
    case powW.uint =>
      dsimp only [cut2]
      split
      · rename_i v heq
        by_cases hv : v.val = 0 ∨ v.val = 1
        · obtain ⟨g1, g2, g3⟩ := powWLit_spec (prev := prev) h hds hAb v hv
          rw [← heq] at g2 g3
          exact good_litR h ⟨by decide, by decide⟩ heq hxe hye g1 g2 g3
        · have : powLit (.app2 (.binop .powW h) A.term B.term) A.term v = .app2 (.binop .powW h) A.term B.term := by
            unfold powLit; rw [if_neg (by omega), if_neg (by omega)]
          rw [this]; exact hgen
      · exact hgen
    case mulW.uint =>
      dsimp only [cut2]
      split
      · rename_i r _
        have heq := r.2
        obtain ⟨g1, g2, g3⟩ := mulWLit_spec hds hprev' hAb r.1
        exact good_litR h ⟨by decide, by decide⟩ heq hxe hye g1 g2 g3
      · rename_i r _ _
        have heq := r.2
        obtain ⟨g1, g2, g3⟩ := mulWLit_spec hds hprev' hB.bound r.1
        exact good_litL h ⟨by decide, by decide⟩ heq hxe hye g1 g2 (fun σ ν hp hd => by
          obtain ⟨r1, r2⟩ := g3 σ ν hp hd
          exact ⟨r1, r2.trans (congrArg _ (funext fun yv => (mulW_comm h yv _).symm))⟩)
      · exact hgen
    case bor.uint =>
      dsimp only [cut2]
      split
      · rename_i r _
        have heq := r.2
        obtain ⟨g1, g2, g3⟩ := borLit_spec hds hprev' hAb r.1
        exact good_litR h ⟨by decide, by decide⟩ heq hxe hye g1 g2 (fun σ ν hp hd => by
          obtain ⟨r1, r2⟩ := g3 σ ν hp hd
          exact ⟨r1, r2.trans (congrArg _ (funext fun xv => (bor_val h xv _).symm))⟩)
      · rename_i r _ _
        have heq := r.2
        obtain ⟨g1, g2, g3⟩ := borLit_spec hds hprev' hB.bound r.1
        exact good_litL h ⟨by decide, by decide⟩ heq hxe hye g1 g2 (fun σ ν hp hd => by
          obtain ⟨r1, r2⟩ := g3 σ ν hp hd
          exact ⟨r1, r2.trans (congrArg _ (funext fun yv => by rw [Nat.or_comm]; exact (bor_val h _ _).symm))⟩)
      · exact hgen
    case bxor.uint =>
      dsimp only [cut2]
      split
      · rename_i r _
        have heq := r.2
        obtain ⟨g1, g2, g3⟩ := bxorLit_spec hds hprev' hAb r.1
        exact good_litR h ⟨by decide, by decide⟩ heq hxe hye g1 g2 (fun σ ν hp hd => by
          obtain ⟨r1, r2⟩ := g3 σ ν hp hd
          exact ⟨r1, r2.trans (congrArg _ (funext fun xv => (bxor_val h xv _).symm))⟩)
      · rename_i r _ _
        have heq := r.2
        obtain ⟨g1, g2, g3⟩ := bxorLit_spec hds hprev' hB.bound r.1
        exact good_litL h ⟨by decide, by decide⟩ heq hxe hye g1 g2 (fun σ ν hp hd => by
          obtain ⟨r1, r2⟩ := g3 σ ν hp hd
          exact ⟨r1, r2.trans (congrArg _ (funext fun yv => by rw [Nat.xor_comm]; exact (bxor_val h _ _).symm))⟩)
      · exact hgen
    case band.int =>
      dsimp only [cut2]
      split
      · rename_i r _
        have heq := r.2
        obtain ⟨g1, g2, g3⟩ := intBit_spec hds hprev' hAb (mk := intBitMk .band prev r.1)
          (F := fun k => k &&& (intWord r.1).val.toNat) (fun k hk => Nat.lt_of_le_of_lt Nat.and_le_left hk)
          (fun t ds' m' hds' ht => bandLit_spec hds' hprev' ht (uint_toNat_lt _))
        exact good_litR h ⟨by decide, by decide⟩ heq hxe hye g1 g2 (fun σ ν hp hd => by
          obtain ⟨r1, r2⟩ := g3 σ ν hp hd
          exact ⟨r1, r2.trans (congrArg _ (funext fun xv => (band_int_val h xv _).symm))⟩)
      · rename_i r _ _
        have heq := r.2
        obtain ⟨g1, g2, g3⟩ := intBit_spec hds hprev' hB.bound (mk := intBitMk .band prev r.1)
          (F := fun k => k &&& (intWord r.1).val.toNat) (fun k hk => Nat.lt_of_le_of_lt Nat.and_le_left hk)
          (fun t ds' m' hds' ht => bandLit_spec hds' hprev' ht (uint_toNat_lt _))
        exact good_litL h ⟨by decide, by decide⟩ heq hxe hye g1 g2 (fun σ ν hp hd => by
          obtain ⟨r1, r2⟩ := g3 σ ν hp hd
          exact ⟨r1, r2.trans (congrArg _ (funext fun yv => (band_int_valL h _ yv).symm))⟩)
      · exact hgen
    case bor.int =>
      dsimp only [cut2]
      split
      · rename_i r _
        have heq := r.2
        obtain ⟨g1, g2, g3⟩ := intBit_spec hds hprev' hAb (mk := intBitMk .bor prev r.1)
          (F := fun k => k ||| (intWord r.1).val.toNat) (fun k hk => Nat.or_lt_two_pow hk (uint_toNat_lt _))
          (fun t ds' m' hds' ht => borLit_spec hds' hprev' ht _)
        exact good_litR h ⟨by decide, by decide⟩ heq hxe hye g1 g2 (fun σ ν hp hd => by
          obtain ⟨r1, r2⟩ := g3 σ ν hp hd
          exact ⟨r1, r2.trans (congrArg _ (funext fun xv => (bor_int_val h xv _).symm))⟩)
      · rename_i r _ _
        have heq := r.2
        obtain ⟨g1, g2, g3⟩ := intBit_spec hds hprev' hB.bound (mk := intBitMk .bor prev r.1)
          (F := fun k => k ||| (intWord r.1).val.toNat) (fun k hk => Nat.or_lt_two_pow hk (uint_toNat_lt _))
          (fun t ds' m' hds' ht => borLit_spec hds' hprev' ht _)
        exact good_litL h ⟨by decide, by decide⟩ heq hxe hye g1 g2 (fun σ ν hp hd => by
          obtain ⟨r1, r2⟩ := g3 σ ν hp hd
          exact ⟨r1, r2.trans (congrArg _ (funext fun yv => (bor_int_valL h _ yv).symm))⟩)
      · exact hgen
    case bxor.int =>
      dsimp only [cut2]
      split
      · rename_i r _
        have heq := r.2
        obtain ⟨g1, g2, g3⟩ := intBit_spec hds hprev' hAb (mk := intBitMk .bxor prev r.1)
          (F := fun k => k ^^^ (intWord r.1).val.toNat) (fun k hk => Nat.xor_lt_two_pow hk (uint_toNat_lt _))
          (fun t ds' m' hds' ht => bxorLit_spec hds' hprev' ht _)
        exact good_litR h ⟨by decide, by decide⟩ heq hxe hye g1 g2 (fun σ ν hp hd => by
          obtain ⟨r1, r2⟩ := g3 σ ν hp hd
          exact ⟨r1, r2.trans (congrArg _ (funext fun xv => (bxor_int_val h xv _).symm))⟩)
      · rename_i r _ _
        have heq := r.2
        obtain ⟨g1, g2, g3⟩ := intBit_spec hds hprev' hB.bound (mk := intBitMk .bxor prev r.1)
          (F := fun k => k ^^^ (intWord r.1).val.toNat) (fun k hk => Nat.xor_lt_two_pow hk (uint_toNat_lt _))
          (fun t ds' m' hds' ht => bxorLit_spec hds' hprev' ht _)
        exact good_litL h ⟨by decide, by decide⟩ heq hxe hye g1 g2 (fun σ ν hp hd => by
          obtain ⟨r1, r2⟩ := g3 σ ν hp hd
          exact ⟨r1, r2.trans (congrArg _ (funext fun yv => (bxor_int_valL h _ yv).symm))⟩)
      · exact hgen
    case div.int =>
      dsimp only [cut2]
      split
      · rename_i v heq
        split
        · rename_i hv
          obtain ⟨g1, g2, g3⟩ := seq_err_spec (prev := prev) (r := .int) hds hAb
            (F := fun xv => BinOp.evalT .div h xv v) (fun xv => div_zero h xv v rfl hv)
          exact good_litR h ⟨by decide, by decide⟩ heq hxe hye g1 g2 g3
        · split
          · rename_i hv0 hv1
            refine good_litR h ⟨by decide, by decide⟩ heq hxe hye hds hAb (fun σ ν _ hd => ⟨hd, ?_⟩)
            rw [LTm.eval_app1, Close.Op1.eval_unop]
            congr 1; funext xv; rw [int_div_neg_one h xv v hv1]
          · rename_i hv0 hv1
            exact CutTm.Good.atom hds hprev' hAb
              (by show max A.term.atomBound B.term.atomBound ≤ B.next; have := hB.bound; omega)
              (isSome_binop_lit h ⟨by decide, by decide⟩ A.term B.term v heq
                (fun xv => int_div_isSome h xv v hv0 hv1)) hev
      · exact hgen
    case mod.int =>
      dsimp only [cut2]
      split
      · rename_i v heq
        split
        · rename_i hv
          obtain ⟨g1, g2, g3⟩ := seq_err_spec (prev := prev) (r := .int) hds hAb
            (F := fun xv => BinOp.evalT .mod h xv v) (fun xv => mod_zero h xv v rfl hv)
          exact good_litR h ⟨by decide, by decide⟩ heq hxe hye g1 g2 g3
        · split
          · rename_i hv0 hv1
            refine good_litR h ⟨by decide, by decide⟩ heq hxe hye hds
              (by show max A.term.atomBound 0 ≤ B.next; omega) (fun σ ν _ hd => ⟨hd, ?_⟩)
            rw [LTm.eval_seq]
            cases A.term.eval σ ν with
            | none => rfl
            | some xv => rw [Option.bind_some, Option.bind_some, int_mod_neg_one h xv v hv1]; rfl
          · rename_i hv0 hv1
            refine CutTm.Good.quot hds hprev' (fun k => LTm.app2 (.binop .sub rfl) A.term
              (.app2 (.binop .mul rfl) (.var k) (.app0 (.lit v)))) hAb
              (by show max A.term.atomBound B.term.atomBound ≤ B.next; have := hB.bound; omega)
              (fun k j hk hm => by
                show max A.term.atomBound (max (k + 1) 0) ≤ j
                omega)
              (fun σ ν hg => by
                rw [isSome_binop_lit rfl ⟨by decide, by decide⟩ A.term B.term v heq
                  (fun xv => int_div_isSome rfl xv v hv0 hv1)]
                exact hg) ?_
            intro σ ν k hp hd hdefn
            have hy : y.eval σ ν = some v := by rw [← hye σ ν hp hd, heq]; rfl
            rw [LTm.eval_binop_of h (shortT_none ⟨by decide, by decide⟩) x y, hy, ← hxe σ ν hp hd,
              LTm.eval_binop_of rfl (shortT_none ⟨by decide, by decide⟩)]
            cases hx : A.term.eval σ ν with
            | none => rfl
            | some xv =>
              have hq := LFml.defn_eval hdefn hx
              rw [ev_bin rfl ⟨by decide, by decide⟩ hx (by rw [heq]; rfl)] at hq
              simp only [Option.bind_some]
              rw [LTm.eval_binop_of rfl (shortT_none ⟨by decide, by decide⟩)]
              exact int_rem_eval h xv v _ hv0 hq
      · exact hgen
    case subW.uint =>
      exact CutTm.Good.atom hds hprev'
        (by show max A.term.atomBound B.term.atomBound ≤ B.next; have := hB.bound; omega)
        (by show max A.term.atomBound B.term.atomBound ≤ B.next; have := hB.bound; omega)
        (isSome_binop2 h ⟨by decide, by decide⟩ A.term B.term (subW_isSome h)) hev
  | _ => exact hgen

theorem eval_modular (g : State C []) (ν : AEnv) (op : ModOp) (x y z : LTm C (.val .uint)) :
    (LTm.app3 (.modular op) x y z).eval g ν =
      (x.eval g ν).bind fun a => (y.eval g ν).bind fun b => (z.eval g ν).bind fun k => op.evalT a b k := by
  rw [LTm.eval_app3]
  cases x.eval g ν <;> cases y.eval g ν <;> cases z.eval g ν <;> rfl

theorem mulmod_comm (x y c : PrimTy.uint.Denote) : ModOp.evalT .mulmod x y c = ModOp.evalT .mulmod y x c := by
  show (if c.val = 0 then none else PrimTy.uint.ofInt? (x.val * y.val % c.val)) =
    (if c.val = 0 then none else PrimTy.uint.ofInt? (y.val * x.val % c.val))
  rw [Int.mul_comm]

/-- **A ternary node, cut, evaluates as the node.** -/
theorem cut3_good {a b c s : Srt} (o : Op3 C a b c s) {x : LTm C a} {y : LTm C b} {z : LTm C c} {n : Nat}
    {prev : List (LFml C)} {A : CutTm C a} {B : CutTm C b} {K : CutTm C c}
    (hA : CutTm.Good x n prev A) (hB : CutTm.Good y A.next (prev ++ A.defs) B)
    (hK : CutTm.Good z B.next (prev ++ A.defs ++ B.defs) K) (hprev : Defs.Below n prev) :
    CutTm.Good (.app3 o x y z) n prev (cut3 o prev A B K) := by
  have hgen : CutTm.Good (.app3 o x y z) n prev
      ⟨.app3 o A.term B.term K.term, A.defs ++ B.defs ++ K.defs, K.next⟩ :=
    hA.node3 hB hK (LTm.app3 o) (fun _ _ _ => Nat.le_refl _)
      (fun g ν x' y' z' hx hy hz => by rw [LTm.eval_app3, LTm.eval_app3, hx, hy, hz])
  have hds : Defs.Good n K.next (A.defs ++ B.defs ++ K.defs) := (hA.defs.append hB.defs).append hK.defs
  have hAb : A.term.atomBound ≤ K.next := Nat.le_trans hA.bound (Nat.le_trans hB.defs.le hK.defs.le)
  have hBb : B.term.atomBound ≤ K.next := Nat.le_trans hB.bound hK.defs.le
  have hall : ∀ σ ν, LFml.AllHold σ ν prev → LFml.AllHold σ ν (A.defs ++ B.defs ++ K.defs) →
      A.term.eval σ ν = x.eval σ ν ∧ B.term.eval σ ν = y.eval σ ν ∧ K.term.eval σ ν = z.eval σ ν := by
    intro σ ν hp hd
    obtain ⟨hab, hz⟩ := (LFml.AllHold.append_iff σ ν _ _).mp hd
    obtain ⟨ha, hb'⟩ := (LFml.AllHold.append_iff σ ν _ _).mp hab
    exact ⟨hA.eval σ ν hp ha, hB.eval σ ν (hp.append ha) hb',
      hK.eval σ ν ((hp.append ha).append hb') hz⟩
  cases o with
  | modular op =>
    cases op with
    | addmod =>
      dsimp only [cut3]
      split
      · rename_i r _
        obtain ⟨rv, hr⟩ := r
        dsimp only
        split
        · rename_i h0
          refine ⟨hds, by dsimp only; simp only [LTm.atomBound]; omega, fun σ ν hp hd => ?_⟩
          obtain ⟨h1, h2, h3⟩ := hall σ ν hp hd
          rw [eval_modular, ← h1, ← h2, ← h3, hr, LTm.eval_seq, LTm.eval_seq]
          cases A.term.eval σ ν <;> cases B.term.eval σ ν <;>
            simp only [Option.bind_none, Option.bind_some]
          show none = ModOp.evalT .addmod _ _ rv
          unfold ModOp.evalT
          rw [if_pos h0]
        · rename_i h0
          obtain ⟨g1, g2, g3⟩ := addmodLit_spec hds hprev hAb hBb rv h0
          refine ⟨g1, g2, fun σ ν hp hd => ?_⟩
          obtain ⟨hd', he⟩ := g3 σ ν hp hd
          obtain ⟨h1, h2, h3⟩ := hall σ ν hp hd'
          rw [he, eval_modular, ← h1, ← h2, ← h3, hr]
          cases A.term.eval σ ν <;> cases B.term.eval σ ν <;> rfl
      · exact hgen
    | mulmod =>
      dsimp only [cut3]
      split
      · rename_i r k _ _
        obtain ⟨rv, hr⟩ := r
        obtain ⟨kv, hk⟩ := k
        dsimp only
        split
        · rename_i h0
          refine ⟨hds, by dsimp only; simp only [LTm.atomBound]; omega, fun σ ν hp hd => ?_⟩
          obtain ⟨h1, h2, h3⟩ := hall σ ν hp hd
          rw [eval_modular, ← h1, ← h2, ← h3, hr, hk, LTm.eval_seq]
          cases A.term.eval σ ν with
          | none => rfl
          | some _ =>
            show none = ModOp.evalT .mulmod _ kv rv
            unfold ModOp.evalT
            rw [if_pos h0]
        · rename_i h0
          obtain ⟨g1, g2, g3⟩ := mulmodLit_spec hds hprev hAb kv rv h0
          refine ⟨g1, g2, fun σ ν hp hd => ?_⟩
          obtain ⟨hd', he⟩ := g3 σ ν hp hd
          obtain ⟨h1, h2, h3⟩ := hall σ ν hp hd'
          rw [he, eval_modular, ← h1, ← h2, ← h3, hr, hk]
          cases A.term.eval σ ν <;> rfl
      · rename_i r k _ _ _
        obtain ⟨rv, hr⟩ := r
        obtain ⟨kv, hk⟩ := k
        dsimp only
        split
        · rename_i h0
          refine ⟨hds, by dsimp only; simp only [LTm.atomBound]; omega, fun σ ν hp hd => ?_⟩
          obtain ⟨h1, h2, h3⟩ := hall σ ν hp hd
          rw [eval_modular, ← h1, ← h2, ← h3, hr, hk, LTm.eval_seq]
          cases B.term.eval σ ν with
          | none => rfl
          | some _ =>
            show none = ModOp.evalT .mulmod kv _ rv
            unfold ModOp.evalT
            rw [if_pos h0]
        · rename_i h0
          obtain ⟨g1, g2, g3⟩ := mulmodLit_spec hds hprev hBb kv rv h0
          refine ⟨g1, g2, fun σ ν hp hd => ?_⟩
          obtain ⟨hd', he⟩ := g3 σ ν hp hd
          obtain ⟨h1, h2, h3⟩ := hall σ ν hp hd'
          rw [he, eval_modular, ← h1, ← h2, ← h3, hr, hk]
          cases B.term.eval σ ν with
          | none => rfl
          | some yv => exact (mulmod_comm _ _ _).symm
      · exact hgen
  | _ => exact hgen

theorem Defs.Below.ext {n : Nat} {prev ds : List (LFml C)} {m : Nat} (hp : Defs.Below n prev)
    (hd : Defs.Good n m ds) : Defs.Below m (prev ++ ds) :=
  hp.append hd.le hd.bound

/-- **The cut of a term is good.** -/
theorem LTm.cut_good : ∀ {s : Srt} (t : LTm C s) (prev : List (LFml C)) (n : Nat),
    t.atomBound ≤ n → Defs.Below n prev → CutTm.Good t n prev (t.cut prev n)
  | _, .var _, _, _, h, _ => CutTm.Good.leaf h
  | _, .app0 _, _, _, h, _ => CutTm.Good.leaf h
  | _, .err, _, _, h, _ => CutTm.Good.leaf h
  | _, .app1 o a, prev, n, h, hp => cut1_good o (LTm.cut_good a prev n h hp) hp
  | _, .app2 o a b, prev, n, h, hp => by
    have hA := LTm.cut_good a prev n (Nat.le_trans (Nat.le_max_left _ _) h) hp
    exact cut2_good o hA (LTm.cut_good b _ _
      (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) h) hA.defs.le) (hp.ext hA.defs)) hp
  | _, .app3 o a b c, prev, n, h, hp => by
    have h' : max a.atomBound (max b.atomBound c.atomBound) ≤ n := h
    have hA := LTm.cut_good a prev n (by omega) hp
    have hB := LTm.cut_good b (prev ++ (a.cut prev n).defs) (a.cut prev n).next
      (by have := hA.defs.le; omega) (hp.ext hA.defs)
    have hZ := LTm.cut_good c (prev ++ (a.cut prev n).defs ++ (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next).defs)
      (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next).next
      (by have := hA.defs.le; have := hB.defs.le; omega) ((hp.ext hA.defs).ext hB.defs)
    exact cut3_good o hA hB hZ hp
  | _, .index it a b, prev, n, h, hp => by
    have hA := LTm.cut_good a prev n (Nat.le_trans (Nat.le_max_left _ _) h) hp
    have hB := LTm.cut_good b _ _ (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) h) hA.defs.le)
      (hp.ext hA.defs)
    exact hA.node2 hB (LTm.index it) (fun _ _ => rfl)
      (fun g ν x' y' hx hy => by rw [LTm.eval_index, LTm.eval_index, hx, hy])
  | _, .obsW a, prev, n, h, hp =>
    (LTm.cut_good a prev n h hp).node1 LTm.obsW (fun _ => rfl)
      (fun g ν y hy => by rw [LTm.eval_obsW, LTm.eval_obsW, hy])
  | _, .obsL a, prev, n, h, hp =>
    (LTm.cut_good a prev n h hp).node1 LTm.obsL (fun _ => rfl)
      (fun g ν y hy => by rw [LTm.eval_obsL, LTm.eval_obsL, hy])
  | _, .obsH a, prev, n, h, hp =>
    (LTm.cut_good a prev n h hp).node1 LTm.obsH (fun _ => rfl)
      (fun g ν y hy => by rw [LTm.eval_obsH, LTm.eval_obsH, hy])
  | _, .seq a b, prev, n, h, hp => by
    have hA := LTm.cut_good a prev n (Nat.le_trans (Nat.le_max_left _ _) h) hp
    have hB := LTm.cut_good b _ _ (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) h) hA.defs.le)
      (hp.ext hA.defs)
    exact hA.node2 hB LTm.seq (fun _ _ => rfl)
      (fun g ν x' y' hx hy => by rw [LTm.eval_seq, LTm.eval_seq, hx, hy])
  | _, .orElse a b, prev, n, h, hp => by
    have hA := LTm.cut_good a prev n (Nat.le_trans (Nat.le_max_left _ _) h) hp
    have hB := LTm.cut_good b _ _ (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) h) hA.defs.le)
      (hp.ext hA.defs)
    exact hA.node2 hB LTm.orElse (fun _ _ => rfl)
      (fun g ν x' y' hx hy => by rw [LTm.eval_orElse, LTm.eval_orElse, hx, hy])
  | _, .kite a b t e, prev, n, h, hp => by
    have h' : max a.atomBound (max b.atomBound (max t.atomBound e.atomBound)) ≤ n := h
    have hA := LTm.cut_good a prev n (by omega) hp
    have hB := LTm.cut_good b (prev ++ (a.cut prev n).defs) (a.cut prev n).next
      (by have := hA.defs.le; omega) (hp.ext hA.defs)
    have hT := LTm.cut_good t (prev ++ (a.cut prev n).defs ++ (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next).defs)
      (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next).next
      (by have := hA.defs.le; have := hB.defs.le; omega) ((hp.ext hA.defs).ext hB.defs)
    have hE := LTm.cut_good e _ _
      (by have := hA.defs.le; have := hB.defs.le; have := hT.defs.le; omega)
      (((hp.ext hA.defs).ext hB.defs).ext hT.defs)
    exact hA.node4 hB hT hE LTm.kite (fun _ _ _ _ => Nat.le_refl _)
      (fun g ν x' y' z' w' hx hy hz hw => by rw [LTm.eval_kite, LTm.eval_kite, hx, hy, hz, hw])

/-- What a cut formula satisfies. -/
structure CutFml.Good (φ : LFml C) (n : Nat) (prev : List (LFml C)) (F : CutFml C) : Prop where
  defs : Defs.Good n F.next F.defs
  bound : F.formula.atomBound ≤ F.next
  holds : ∀ (g : State C []) (ν : AEnv), LFml.AllHold g ν prev → LFml.AllHold g ν F.defs →
    (F.formula.holds g ν ↔ φ.holds g ν)

theorem CutFml.Good.bin {φ ψ : LFml C} {n : Nat} {prev : List (LFml C)} {F G : CutFml C}
    (hF : CutFml.Good φ n prev F) (hG : CutFml.Good ψ F.next (prev ++ F.defs) G)
    (mk : LFml C → LFml C → LFml C)
    (hb : ∀ a b, (mk a b).atomBound = max a.atomBound b.atomBound)
    (hh : ∀ g ν a b, (a.holds g ν ↔ φ.holds g ν) → (b.holds g ν ↔ ψ.holds g ν) →
      ((mk a b).holds g ν ↔ (mk φ ψ).holds g ν)) :
    CutFml.Good (mk φ ψ) n prev ⟨mk F.formula G.formula, F.defs ++ G.defs, G.next⟩ := by
  refine ⟨hF.defs.append hG.defs, ?_, fun g ν hp h => ?_⟩
  · show (mk F.formula G.formula).atomBound ≤ G.next
    rw [hb]
    have := hG.defs.le
    have := hF.bound
    have := hG.bound
    omega
  · obtain ⟨ha, hb'⟩ := (LFml.AllHold.append_iff g ν _ _).mp h
    exact hh g ν _ _ (hF.holds g ν hp ha) (hG.holds g ν (hp.append ha) hb')

/-- **The cut of a formula is good.** -/
theorem LFml.cut_good : ∀ (φ : LFml C) (prev : List (LFml C)) (n : Nat), φ.atomBound ≤ n →
    Defs.Below n prev → CutFml.Good φ n prev (φ.cut prev n)
  | .tt, _, n, _, _ => ⟨Defs.Good.nil n, Nat.zero_le _, fun _ _ _ _ => Iff.rfl⟩
  | .eq a b, prev, n, h, hp => by
    have hA := LTm.cut_good a prev n (Nat.le_trans (Nat.le_max_left _ _) h) hp
    have hB := LTm.cut_good b _ _ (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) h) hA.defs.le)
      (hp.ext hA.defs)
    refine ⟨hA.defs.append hB.defs, ?_, fun g ν hpv hd => ?_⟩
    · show max (a.cut prev n).term.atomBound (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next).term.atomBound ≤
        (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next).next
      have := hB.defs.le
      have := hA.bound
      have := hB.bound
      omega
    · obtain ⟨ha, hb⟩ := (LFml.AllHold.append_iff g ν _ _).mp hd
      show (LFml.eq (a.cut prev n).term (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next).term).holds g ν ↔
        (LFml.eq a b).holds g ν
      simp only [LFml.holds, hA.eval g ν hpv ha, hB.eval g ν (hpv.append ha) hb]
  | .not φ, prev, n, h, hp => by
    have hF := LFml.cut_good φ prev n h hp
    exact ⟨hF.defs, hF.bound, fun g ν hpv hd => not_congr (hF.holds g ν hpv hd)⟩
  | .and φ ψ, prev, n, h, hp => by
    have hF := LFml.cut_good φ prev n (Nat.le_trans (Nat.le_max_left _ _) h) hp
    have hG := LFml.cut_good ψ _ _ (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) h) hF.defs.le)
      (hp.ext hF.defs)
    exact hF.bin hG LFml.and (fun _ _ => rfl) (fun _ _ _ _ h1 h2 => and_congr h1 h2)
  | .imp φ ψ, prev, n, h, hp => by
    have hF := LFml.cut_good φ prev n (Nat.le_trans (Nat.le_max_left _ _) h) hp
    have hG := LFml.cut_good ψ _ _ (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) h) hF.defs.le)
      (hp.ext hF.defs)
    exact hF.bin hG LFml.imp (fun _ _ => rfl) (fun _ _ _ _ h1 h2 => imp_congr h1 h2)
  | .all _ _ _, _, n, h, _ => ⟨Defs.Good.nil n, h, fun _ _ _ _ => Iff.rfl⟩

theorem LFml.cutAll_holds_iff (φ : LFml C) (g : State C []) (ν : AEnv) :
    φ.cutAll.holds g ν ↔
      (LFml.AllHold g ν (φ.cut [] φ.atomBound).defs → (φ.cut [] φ.atomBound).formula.holds g ν) := by
  unfold LFml.cutAll
  split
  · rename_i heq
    rw [heq]
    exact ⟨fun h _ => h, fun h => h (fun _ hd => nomatch hd)⟩
  · rename_i heq _
    show ((LFml.conj _).holds g ν → _) ↔ _
    rw [LFml.holds_conj]

theorem LFml.cut_good_top (φ : LFml C) : CutFml.Good φ φ.atomBound [] (φ.cut [] φ.atomBound) :=
  LFml.cut_good φ [] φ.atomBound (Nat.le_refl _) (fun _ h => nomatch h)

/-- **A leaf implies its cut**: so a countermodel of the cut leaf refutes
the leaf at the same point. -/
theorem LFml.holds_cutAll (φ : LFml C) (g : State C []) (ν : AEnv) (h : φ.holds g ν) :
    φ.cutAll.holds g ν :=
  (LFml.cutAll_holds_iff φ g ν).mpr fun hd =>
    ((LFml.cut_good_top φ).holds g ν (fun _ h => nomatch h) hd).mpr h

/-- **The cut is exact in a universal reading**: the leaf is valid exactly
when its cut is. -/
theorem LFml.cutAll_valid_iff (φ : LFml C) : φ.cutAll.Valid ↔ φ.Valid := by
  have hF := LFml.cut_good_top φ
  refine ⟨fun hv g ν => ?_, fun hv g ν => LFml.holds_cutAll φ g ν (hv g ν)⟩
  obtain ⟨μ, hμ, hd⟩ := hF.defs.extend g ν
  have h := (LFml.cutAll_holds_iff φ g μ).mp (hv g μ) hd
  exact (LFml.holds_agree_below g φ hμ).mpr ((hF.holds g μ (fun _ h => nomatch h) hd).mp h)

end Solidity.Decide
