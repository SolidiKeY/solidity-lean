import Solidity.Semantics.Run
import Solidity.Semantics.AbiEntry

/-!
# Typed intrinsic panic origins

These producers retain the operands of the original W3 sites. They are an
additive interface, independent of Panic/Result: no V1 result or admission
predicate changes. An `Origin` certifies the failed branch of a particular
producer, rather than classifying arbitrary revert bytes or a V1 panic.

Enum membership, storage-byte encoding and internal-function tags have explicit
local guard producers: V1 does not retain these distinctions. Their adoption by
source lowering is a separate association obligation. In particular an invalid
storage encoding is not representable by the canonical V1 array contents.
The allocation link observes AbiEntry.alloc only; it does not change the ABI
verdict or certify any input previously blocked for possible allocation panic.
-/

namespace Solidity.Panic

/-- The nine original W3 sites; no external/oracle payload constructor. -/
inductive Site where
  | assertion | arithmetic | zeroDivisor | enumConversion | storageEncoding
  | emptyPop | bounds | allocation | zeroInternalFunction
  deriving DecidableEq, Repr

def Site.code : Site → Nat
  | .assertion => 0x01
  | .arithmetic => 0x11
  | .zeroDivisor => 0x12
  | .enumConversion => 0x21
  | .storageEncoding => 0x22
  | .emptyPop => 0x31
  | .bounds => 0x32
  | .allocation => 0x41
  | .zeroInternalFunction => 0x51

/-- Checked numeric operators only; wrapping and bitwise operations cannot
be relabelled as checked overflow by this interface. -/
inductive Checked where
  | add | sub | mul | pow | div | mod
  deriving DecidableEq, Repr

def Checked.op : Checked → BinOp
  | .add => .add | .sub => .sub | .mul => .mul
  | .pow => .pow | .div => .div | .mod => .mod

/-- Zero division is distinguished before the range check. V1 also permits
a negative exponent; that failure has no Solidity panic origin here. -/
def Checked.failure (op : Checked) (y : Int) : Option Site :=
  match op with
  | .div => some (if y = 0 then .zeroDivisor else .arithmetic)
  | .mod => if y = 0 then some .zeroDivisor else none
  | .pow => if y < 0 then none else some .arithmetic
  | _ => some .arithmetic

/-- A producer carries typed operands and its successful result type.
Guards are total on their inputs: failure witnesses add no admission condition. -/
inductive Producer : Type → Type where
  | assertion (value : Bool) : Producer Unit
  | binary (op : Checked) (p : PrimTy)
      (accepts : op.op.accepts p = true) (x y : p.Denote) :
      Producer (op.op.ret p).Denote
  | modular (op : ModOp) (x y modulus : PrimTy.uint.Denote) :
      Producer PrimTy.uint.Denote
  | neg (x : PrimTy.int.Denote) : Producer PrimTy.int.Denote
  | enumConversion (members : Nat) (value : PrimTy.uint.Denote) :
      Producer PrimTy.uint.Denote
  | storageEncoding (word : PrimTy.uint.Denote) : Producer Nat
  | pop {C : Contract} {E : Ty} (st : Storage C) (keep : Bool)
      (ref : SRef C (.ref (.array E))) : Producer (Storage C)
  | index {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
      (ref : HRef H R) (array : ArrTy R E) (i : PrimTy.uint.Denote) :
      Producer (MVal H E)
  | storageIndex {C : Contract} {R : RefTy} {E : Ty} (st : Storage C)
      (ref : SRef C (.ref R)) (array : ArrTy R E) (i : PrimTy.uint.Denote) :
      Producer Unit
  | allocation (input : AbiEntry.Input) (used size : Nat) : Producer Nat
  | internalFunction (tag : PrimTy.uint.Denote) : Producer PrimTy.uint.Denote

/-- Solc's storage-byte length check: short encodings have length < 32,
long encodings have length ≥ 32. The low bit selects the representation. -/
def storageLength (word : PrimTy.uint.Denote) : Option Nat :=
  let n := word.val.toNat
  let long := n % 2 = 1
  let len := (if long then n else n % 256) / 2
  if long = (32 ≤ len) then some len else none

/-- Local diagnostic outcome. `none` preserves an unclassified V1 failure
(e.g. a missing storage path), without inventing a panic origin. -/
def checked {α : Type} (site : Option Site) : Option α → Except (Option Site) α
  | some value => .ok value
  | none => .error site

def Producer.run {α : Type} : Producer α → Except (Option Site) α
  | .assertion b => if b then .ok () else .error (some .assertion)
  | .binary op p h x y => checked (op.failure (PrimTy.key y)) (op.op.evalT h x y)
  | .modular op x y modulus =>
      checked (if modulus.val = 0 then some .zeroDivisor else none)
        (op.evalT x y modulus)
  | .neg x => checked (some .arithmetic) (UnOp.neg.evalT rfl x)
  | .enumConversion members value =>
      if value.val.toNat < members then .ok value else .error (some .enumConversion)
  | .storageEncoding word => checked (some .storageEncoding) (storageLength word)
  | .pop st keep ref =>
      match st.find ref with
      | none => .error none
      | some value =>
          if (SVal.view value).elems.toList.isEmpty then .error (some .emptyPop)
          else match st.pop keep ref with
            | none => .error none
            | some next => .ok next
  | .index hp ref array i => checked (some .bounds) (hp.index ref array i)
  | .storageIndex st ref array i =>
      match st.find ref with
      | none => .error none
      | some value => checked (some .bounds) (Storage.inBounds (.arr array) i value)
  | .allocation input used size =>
      match AbiEntry.alloc input used size with
      | .ok n => .ok n
      | .error .panic => .error (some .allocation)
      | .error _ => .error none
  | .internalFunction tag =>
      if tag.val = 0 then .error (some .zeroInternalFunction) else .ok tag

/-- An intrinsically indexed origin is evidence about the producer that
actually raised it, not a freely attached label. -/
def Origin {α : Type} (producer : Producer α) (site : Site) : Prop :=
  producer.run = .error (some site)

theorem assertion_origin : Origin (.assertion false) .assertion := rfl

theorem binary_origin (op : Checked) (p : PrimTy)
    (ha : op.op.accepts p = true) (x y : p.Denote)
    (failed : op.op.evalT ha x y = none) (site : Site)
    (classified : op.failure (PrimTy.key y) = some site) :
    Origin (.binary op p ha x y) site := by
  simp only [Origin, Producer.run, failed, checked, classified]

theorem modular_zero_origin (op : ModOp) (x y modulus : PrimTy.uint.Denote)
    (zero : modulus.val = 0) : Origin (.modular op x y modulus) .zeroDivisor := by
  simp only [Origin, Producer.run, ModOp.evalT, zero, ↓reduceIte, checked]

theorem neg_origin (x : PrimTy.int.Denote)
    (failed : UnOp.neg.evalT rfl x = none) : Origin (.neg x) .arithmetic := by
  simp only [Origin, Producer.run, failed, checked]

theorem enum_origin (members : Nat) (value : PrimTy.uint.Denote)
    (failed : ¬value.val.toNat < members) :
    Origin (.enumConversion members value) .enumConversion := by
  simp only [Origin, Producer.run, if_neg failed]

theorem encoding_origin (word : PrimTy.uint.Denote)
    (failed : storageLength word = none) :
    Origin (.storageEncoding word) .storageEncoding := by
  simp only [Origin, Producer.run, failed, checked]

theorem pop_origin {C : Contract} {E : Ty} (st : Storage C) (keep : Bool)
    (ref : SRef C (.ref (.array E))) (value : SVal (.ref (.array E)))
    (found : st.find ref = some value)
    (empty : (SVal.view value).elems.toList.isEmpty = true) :
    Origin (.pop st keep ref) .emptyPop := by
  simp only [Origin, Producer.run, found, empty, ↓reduceIte]

theorem index_origin {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (ref : HRef H R) (array : ArrTy R E) (i : PrimTy.uint.Denote)
    (failed : hp.index ref array i = none) :
    Origin (.index hp ref array i) .bounds := by
  simp only [Origin, Producer.run, failed, checked]

theorem storage_index_origin {C : Contract} {R : RefTy} {E : Ty} (st : Storage C)
    (ref : SRef C (.ref R)) (array : ArrTy R E) (i : PrimTy.uint.Denote)
    (value : SVal (.ref R)) (found : st.find ref = some value)
    (failed : Storage.inBounds (.arr array) i value = none) :
    Origin (.storageIndex st ref array i) .bounds ∧
      st.checkIndex ref (.arr array) i = none := by
  constructor
  · simp only [Origin, Producer.run, found, failed, checked]
  · change (st.find ref).bind (Storage.inBounds (.arr array) i) = none
    rw [found]
    exact failed

theorem allocation_origin (input : AbiEntry.Input) (used size : Nat)
    (failed : AbiEntry.alloc input used size = .error .panic) :
    Origin (.allocation input used size) .allocation := by
  simp only [Origin, Producer.run, failed]

theorem internal_origin (tag : PrimTy.uint.Denote) (zero : tag.val = 0) :
    Origin (.internalFunction tag) .zeroInternalFunction := by
  simp only [Origin, Producer.run, if_pos zero]

/-- A producer cannot supply two different intrinsic origins. -/
theorem Origin.unique {α : Type} {p : Producer α} {a b : Site}
    (ha : Origin p a) (hb : Origin p b) : a = b := by
  have h := ha.symm.trans hb
  exact Option.some.inj (Except.error.inj h)

/-- Local V1 link: after a successful condition evaluation the failed
assertion is precisely V1's panic. No condition failure is reclassified. -/
theorem assertion_v1 {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (condition : Val C Γ .bool) (failed : condition.evalT σ = .ok false) :
    TRun.assert condition σ = .error .panic := by
  simp only [TRun.assert, failed]
  rfl

/-- The origin API's successful binary result is exactly the old operator's. -/
theorem binary_success (op : Checked) (p : PrimTy)
    (ha : op.op.accepts p = true) (x y : p.Denote) (value : (op.op.ret p).Denote)
    (success : op.op.evalT ha x y = some value) :
    (Producer.binary op p ha x y).run = .ok value := by
  simp only [Producer.run, success, checked]

/-- Both zero-divisor operations use 0x12, including checked signed division. -/
theorem zero_divisor_codes :
    (Checked.div.failure 0).map Site.code = some 0x12 ∧
    (Checked.mod.failure 0).map Site.code = some 0x12 := by decide

/-- Negative exponents remain admitted intrinsic inputs, but their V1 failure
is not misreported as Solidity checked overflow. -/
theorem negative_exponent_unclassified (y : Int) (negative : y < 0) :
    Checked.pow.failure y = none := by
  simp only [Checked.failure, if_pos negative]

/-- Every original site has its prescribed code. -/
theorem original_codes :
    Site.assertion.code = 0x01 ∧ Site.arithmetic.code = 0x11 ∧
    Site.zeroDivisor.code = 0x12 ∧ Site.enumConversion.code = 0x21 ∧
    Site.storageEncoding.code = 0x22 ∧ Site.emptyPop.code = 0x31 ∧
    Site.bounds.code = 0x32 ∧ Site.allocation.code = 0x41 ∧
    Site.zeroInternalFunction.code = 0x51 := by decide

/-- Typed byte-header boundary controls: malformed encodings remain inputs,
not excluded states. Neither odd short lengths nor even long lengths pass. -/
example : storageLength ⟨1, by decide⟩ = none := by decide
example : storageLength ⟨62, by decide⟩ = some 31 := by decide
example : storageLength ⟨63, by decide⟩ = none := by decide
example : storageLength ⟨64, by decide⟩ = none := by decide
example : storageLength ⟨65, by decide⟩ = some 32 := by decide

end Solidity.Panic
