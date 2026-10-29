import Solidity.Source.Const

/-!
# Source types and conversions (S01)

The static types of Solidity 0.8.38 expressions (`STy`), their elaboration
from S00's type names, and solc's implicit and explicit conversions
between them, with the fixed-point readings of the second-round decisions
(`docs/solidity-scope.md`, "Second round"):

- implicit fixed-point conversions only between range-contained pairs
  (`FixTy.implicitOK`: solc's test and exactness);
- explicit fixed-point conversions between any two fixed-point types, to and
  from every integer type (by value) and to and from `bytesM` of the same
  width (by bit pattern);
- a constant converts implicitly only exactly and in range, explicitly by
  truncation toward zero, and out of range is a compile error (`Const.lean`).

User-defined types are named by their declaration (`DeclName`: enclosing
contract and name), resolved by `Solidity/Source/Resolve.lean`; reference
types carry their data location.  `implicit_int_range` and
`FixTy.subsumes_inRange` prove the value-level reading of the implicit
conversions: every value of the source type is a value of the target type.
-/

namespace Solidity.Source

/-- A resolved declaration: its enclosing contract (none at file level) and
its name. -/
structure DeclName where
  scope : Option String
  name : String
  deriving DecidableEq, Repr

/-- The static types. -/
inductive STy where
  | int (t : IntTy)
  | bool
  | address (payable : Bool)
  | fixedBytes (n : Nat) (h : 1 ≤ n ∧ n ≤ 32)
  | fixed (t : FixTy)
  | enum (d : DeclName)
  | udvt (d : DeclName)
  | contract (d : DeclName)
  | bytes (loc : DataLoc)
  | string (loc : DataLoc)
  | array (loc : DataLoc) (elem : STy) (len : Option Nat)
  | struct (loc : DataLoc) (d : DeclName)
  | mapping (key value : STy)
  | fn (external : Bool) (params rets : List STy) (mutability : Option Mutability)
  /-- The type of a constant expression: its exact value (`RationalNumberType`). -/
  | rational (q : Q)
  /-- The type of a string literal (`StringLiteralType`). -/
  | stringLit (bytes : List UInt8)
  | tuple (ts : List STy)
  deriving Repr

/-! ## Integer and fixed-point ranges -/

/-- `uint256`. -/
def IntTy.u256 : IntTy := ⟨false, 256, by decide⟩
/-- `uint160`, the integer type of an address. -/
def IntTy.u160 : IntTy := ⟨false, 160, by decide⟩
/-- `uint8`. -/
def IntTy.u8 : IntTy := ⟨false, 8, by decide⟩

/-- solc's implicit integer conversion: the same signedness and no
narrower, or unsigned to strictly wider signed. -/
def IntTy.implicit (t t' : IntTy) : Bool :=
  (t.signed == t'.signed && decide (t.bits ≤ t'.bits)) ||
    (!t.signed && t'.signed && decide (t.bits < t'.bits))

theorem two_pow_le {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) h

theorem two_pow_pos (a : Nat) : 0 < 2 ^ a := Nat.pow_pos (by decide)

/-- **Implicit integer conversions keep every value**: the source range lies
in the target range. -/
theorem implicit_int_range {t t' : IntTy} (h : t.implicit t' = true) : t'.lo ≤ t.lo ∧ t.hi ≤ t'.hi := by
  obtain ⟨s, b, hb⟩ := t
  obtain ⟨s', b', hb'⟩ := t'
  simp only [IntTy.implicit, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    Bool.not_eq_true'] at h
  simp only [IntTy.lo, IntTy.hi]
  rcases h with ⟨rfl, hle⟩ | ⟨⟨rfl, rfl⟩, hlt⟩
  · cases s
    · simp only [Bool.false_eq_true, if_false]
      have := two_pow_le hle
      have := two_pow_pos b
      omega
    · simp only [if_true]
      have := two_pow_le (Nat.sub_le_sub_right hle 1)
      have := two_pow_pos (b - 1)
      omega
  · simp only [Bool.false_eq_true, if_false, if_true]
    have h1 : b ≤ b' - 1 := by omega
    have := two_pow_le h1
    have := two_pow_pos (b' - 1)
    have := two_pow_pos b
    omega

namespace FixTy

/-- solc's greatest integer of the type (`maxIntegerValue`). -/
def maxInt (t : FixTy) : Int := t.hi / t.scale
/-- solc's least integer, the bound divided toward zero (`minIntegerValue`). -/
def minInt (t : FixTy) : Int := -((-t.lo) / t.scale)

/-- Every value of `t` is a value of `t'`: no digit dropped and both scaled
bounds in range. -/
def subsumes (t t' : FixTy) : Bool :=
  decide (t.digits ≤ t'.digits) &&
    decide (t'.lo ≤ t.lo * 10 ^ (t'.digits - t.digits)) && decide (t.lo * 10 ^ (t'.digits - t.digits) ≤ t'.hi) &&
    decide (t'.lo ≤ t.hi * 10 ^ (t'.digits - t.digits)) && decide (t.hi * 10 ^ (t'.digits - t.digits) ≤ t'.hi)

/-- solc's implicit test between fixed-point types
(`FixedPointType::isImplicitlyConvertibleTo`). -/
def solcImplicit (t t' : FixTy) : Bool :=
  decide (t.digits ≤ t'.digits) && decide (t.bits ≤ t'.bits) &&
    decide (t.maxInt ≤ t'.maxInt) && decide (t'.minInt ≤ t.minInt)

/-- **The implicit fixed-point conversion** (second round: only
range-contained pairs): solc's test, restricted to exact conversions. -/
def implicitOK (t t' : FixTy) : Bool := t.solcImplicit t' && t.subsumes t'

/-- solc's implicit integer-to-fixed test, for an integer range. -/
def intImplicit (t : FixTy) (lo hi : Int) : Bool := decide (t.minInt ≤ lo) && decide (hi ≤ t.maxInt)

/-- **Implicit fixed-point conversions keep every value**: a scaled integer
in the range of `t`, rescaled to `t'`'s digits, is in the range of `t'`. -/
theorem subsumes_inRange {t t' : FixTy} (h : t.subsumes t' = true) {v : Int}
    (hv : t.lo ≤ v ∧ v ≤ t.hi) :
    t'.lo ≤ v * 10 ^ (t'.digits - t.digits) ∧ v * 10 ^ (t'.digits - t.digits) ≤ t'.hi := by
  simp only [subsumes, Bool.and_eq_true, decide_eq_true_eq] at h
  have hc : (0 : Int) ≤ 10 ^ (t'.digits - t.digits) := Int.le_of_lt (Int.pow_pos (by decide))
  have h1 := Int.mul_le_mul_of_nonneg_right hv.1 hc
  have h2 := Int.mul_le_mul_of_nonneg_right hv.2 hc
  omega

end FixTy

/-! ## Elementary types -/

/-- The type an elementary type name denotes (`bytes`/`string` in a
location); `fixed`/`ufixed` are `fixed128x18`/`ufixed128x18`. -/
def Elem.ty (loc : DataLoc) : Elem → STy
  | .address => .address false
  | .addressPayable => .address true
  | .bool => .bool
  | .string => .string loc
  | .bytes => .bytes loc
  | .int s b h => .int ⟨s, b, h⟩
  | .fixedBytes n h => .fixedBytes n h
  | .fixed s none => .fixed ⟨s, 128, 18, by decide⟩
  | .fixed s (Option.some d) => .fixed ⟨s, d.bits, d.digits, d.valid⟩

/-- Whether a type is a value type. -/
def STy.isValue : STy → Bool
  | .int _ | .bool | .address _ | .fixedBytes _ _ | .fixed _ | .enum _ | .udvt _ | .contract _
  | .fn _ _ _ _ => true
  | _ => false

/-! ## Conversions -/

/-- solc's location rule for an implicit reference conversion: a copy to
`memory`, or the same location (a pointer). -/
def DataLoc.implicit (l l' : DataLoc) : Bool := l' == .memory || l == l'

/-- **Implicit conversion** between types, given the inheritance relation
on contracts (`isBase d d'`: `d'` is `d` or one of its bases). -/
def STy.implicit (isBase : DeclName → DeclName → Bool) : STy → STy → Bool
  | .int t, .int t' => t.implicit t'
  | .bool, .bool => true
  | .address p, .address p' => p || !p'
  | .fixedBytes n _, .fixedBytes m _ => decide (n ≤ m)
  | .fixed t, .fixed t' => t.implicitOK t'
  | .int t, .fixed f => f.intImplicit t.lo t.hi
  | .enum d, .enum d' | .udvt d, .udvt d' => d == d'
  | .contract d, .contract d' => isBase d d'
  | .bytes l, .bytes l' | .string l, .string l' => l.implicit l'
  | .rational q, .int t => decide (q.FitsInt t)
  | .rational q, .fixed f => (q.toFixed? f).isSome
  | .rational q, .address false => decide (q.FitsInt IntTy.u160) && q.num == 0
  | .stringLit _, .bytes .memory | .stringLit _, .string .memory => true
  | .stringLit s, .fixedBytes n _ => decide (s.length ≤ n)
  | _, _ => false

/-- **Explicit conversion** (`T(e)`), beyond the implicit ones: at most one
change of sign, width or category (solc 0.8); the fixed-point readings of
the second round; addresses, contracts and enums. -/
def STy.explicit (isBase : DeclName → DeclName → Bool) (s t : STy) : Bool :=
  s.implicit isBase t ||
  match s, t with
  | .int a, .int b => a.signed == b.signed || a.bits == b.bits
  | .int a, .fixedBytes n _ | .fixedBytes n _, .int a => !a.signed && a.bits == 8 * n
  | .int a, .address p | .address p, .int a => !p && !a.signed && a.bits == 160
  | .fixedBytes n _, .address false | .address _, .fixedBytes n _ => n == 20
  | .fixedBytes _ _, .fixedBytes _ _ => true
  | .address _, .address false => true
  | .contract _, .address false | .address _, .contract _ => true
  | .int _, .enum _ | .enum _, .int _ => true
  | .fixed _, .fixed _ | .fixed _, .int _ | .int _, .fixed _ => true
  | .fixed f, .fixedBytes n _ | .fixedBytes n _, .fixed f => f.bits == 8 * n
  | .bytes l, .string l' | .string l, .bytes l' => l == l'
  | .bytes l, .fixedBytes _ _ => l != .storage
  | .rational q, .int a => (q.toIntExplicit? a).isSome
  | .rational q, .fixed f => (q.toFixedExplicit? f).isSome
  | .rational q, .address false => decide (q.FitsInt IntTy.u160)
  | .rational q, .enum _ => q.isInt && decide (0 ≤ q.toInt)
  | _, _ => false

theorem STy.explicit_of_implicit {isBase : DeclName → DeclName → Bool} {s t : STy}
    (h : s.implicit isBase t = true) : s.explicit isBase t = true := by
  simp only [STy.explicit, h, Bool.true_or]

/-- **A constant that fits a type fits every type it converts to
implicitly.** -/
theorem Q.FitsInt.implicit {q : Q} {t t' : IntTy} (hq : q.FitsInt t) (h : t.implicit t' = true) :
    q.FitsInt t' := by
  have hr := implicit_int_range h
  exact ⟨hq.1, Int.le_trans hr.1 hq.2.1, Int.le_trans hq.2.2 hr.2⟩

end Solidity.Source
