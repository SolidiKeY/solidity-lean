import Solidity.Semantics.Panic.Origins

/-!
# Typed panic-origin regressions

V1 erases the cause of a panic. In particular signed min divided by -1 and division by
zero both fail, while negative powers and missing paths are admitted failures
without a Solidity code. These controls prevent relabelling those failures.
The enum/header/function guards are local producers, not source associations.
No byte decoder, arbitrary revert payload, ABI entry or external EVM is certified.
-/
namespace Solidity.Examples.Panic.Origins
open Solidity.Panic

private def u (n : Nat) : PrimTy.uint.Denote := uintOfNat n
private def im : PrimTy.int.Denote := ⟨-((2^255 : Nat) : Int), by decide⟩
private def minusOne : PrimTy.int.Denote := ⟨-1, by decide⟩
private def umax : PrimTy.uint.Denote := ⟨((2^256 : Nat) : Int) - 1, by decide⟩

/-- `assert(false)` has 0x01; `assert(true)` cannot acquire that origin. -/
theorem assertion_boundary : Origin (.assertion false) .assertion ∧
    (Producer.assertion true).run = .ok () := ⟨assertion_origin, rfl⟩

/-- Once the condition evaluated false, V1 still raises its original panic. -/
theorem assertion_transport {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (v : Val C Γ .bool) (h : v.evalT σ = .ok false) :
    TRun.assert v σ = .error .panic := assertion_v1 σ v h

/-- `uint256.max+1` must fail before assigning the arithmetic code. -/
theorem add_overflow : Origin (.binary .add .uint rfl umax (u 1)) .arithmetic :=
  binary_origin _ _ _ _ _ (by decide +kernel) _ rfl

/-- `0-1` is checked underflow, not wrapping subtraction. -/
theorem sub_underflow : Origin (.binary .sub .uint rfl (u 0) (u 1)) .arithmetic :=
  binary_origin _ _ _ _ _ (by decide +kernel) _ rfl

/-- Multiplication's first overflowing result retains its typed operands. -/
theorem mul_overflow : Origin (.binary .mul .uint rfl umax (u 2)) .arithmetic :=
  binary_origin _ _ _ _ _ (by decide +kernel) _ rfl

/-- `2**256` is outside uint256; a nonnegative exponent gets 0x11. -/
theorem pow_overflow : Origin (.binary .pow .uint rfl (u 2) (u 256)) .arithmetic :=
  binary_origin _ _ _ _ _ (by decide +kernel) _ rfl

/-- Signed min divided by -1 overflows; it is not a zero divisor (0x12). -/
theorem signed_div_overflow : Origin (.binary .div .int rfl im minusOne) .arithmetic :=
  binary_origin _ _ _ _ _ (by decide +kernel) _ (by decide +kernel)

/-- Negating int256.min fails, but negating -1 succeeds with the exact value. -/
theorem neg_boundary : Origin (.neg im) .arithmetic ∧
    (Producer.neg minusOne).run = .ok ⟨1, by decide⟩ :=
  ⟨neg_origin _ (by decide +kernel), rfl⟩

/-- Both binary zero divisors carry 0x12, including signed division. -/
theorem zero_divisors : Origin (.binary .div .int rfl im ⟨0, by decide⟩) .zeroDivisor ∧
    Origin (.binary .mod .uint rfl (u 1) (u 0)) .zeroDivisor := by
  constructor <;> exact binary_origin _ _ _ _ _ (by decide +kernel) _ (by decide +kernel)

/-- addmod/mulmod use the modulus, not the second operand, as divisor. -/
theorem modular_boundary :
    Origin (.modular .addmod umax (u 1) (u 0)) .zeroDivisor ∧
    Origin (.modular .mulmod umax (u 2) (u 0)) .zeroDivisor ∧
    (Producer.modular .addmod umax (u 1) (u 2)).run = .ok (u 0) ∧
    (Producer.modular .mulmod umax (u 2) (u 2)).run = .ok (u 0) :=
  ⟨modular_zero_origin _ _ _ _ rfl, modular_zero_origin _ _ _ _ rfl,
    rfl, rfl⟩

/-- V1 arithmetic admits negative exponents, but typed checked pow accepts
only uint operands. Its classifier must not invent a Solidity overflow code. -/
theorem negative_power : BinOp.arithInt .pow 2 (-1) = none ∧
    Checked.pow.failure (-1) = none :=
  ⟨rfl, negative_exponent_unclassified _ (by decide)⟩

/-- An in-range checked addition returns the original operator's exact result. -/
theorem add_success : (Producer.binary .add .uint rfl (u 1) (u 2)).run = .ok (u 3) :=
  binary_success _ _ _ _ _ _ (by decide +kernel)

/-- E(2) is invalid for two members; E(1) is the last valid member. -/
theorem enum_boundary : Origin (.enumConversion 2 (u 2)) .enumConversion ∧
    (Producer.enumConversion 2 (u 1)).run = .ok (u 1) ∧
    Origin (.enumConversion 0 (u 0)) .enumConversion :=
  ⟨enum_origin _ _ (by decide +kernel), rfl,
    enum_origin _ _ (by decide +kernel)⟩

/-- Byte headers: odd short 1/63 and even long 64 are malformed; 62/65
encode the adjacent valid lengths 31/32. Payload bits above the short header
must not be mistaken for length (318 has the same valid low byte as 62). -/
theorem encoding_boundary : Origin (.storageEncoding (u 1)) .storageEncoding ∧
    Origin (.storageEncoding (u 63)) .storageEncoding ∧
    Origin (.storageEncoding (u 64)) .storageEncoding ∧
    (Producer.storageEncoding (u 62)).run = .ok 31 ∧
    (Producer.storageEncoding (u 65)).run = .ok 32 ∧
    (Producer.storageEncoding (u 318)).run = .ok 31 :=
  ⟨encoding_origin _ (by decide +kernel), encoding_origin _ (by decide +kernel),
    encoding_origin _ (by decide +kernel), rfl, rfl, rfl⟩

private def C : Contract := contract!{ uint[] values; uint[][] nested; }
private def ref : SRef C (.ref (.array (.prim .uint))) := .ofRoot "values" rfl
private def nested : SRef C (.ref (.array (.ref (.array (.prim .uint))))) :=
  .ofRoot "nested" rfl
private def missing : SRef C (.ref (.array (.prim .uint))) :=
  nested.index (.arr .dyn) (u 0)

/-- Empty pop has 0x31 for either keep mode, using a real stored empty array. -/
theorem empty_pop (keep : Bool) : Origin (.pop (Storage.init C) keep ref) .emptyPop :=
  pop_origin _ _ _ _ rfl (by decide +kernel)

/-- A missing nested storage path is not an empty array and has no 0x31/0x32. -/
theorem missing_path : (Producer.pop (Storage.init C) false missing).run = .error none ∧
    (Producer.storageIndex (Storage.init C) missing .dyn (u 0)).run = .error none :=
by
  have h : (Storage.init C).find missing = none := by
    apply Option.isNone_iff_eq_none.mp
    decide +kernel
  simp only [Producer.run, h, and_self]

/-- Index zero of an actual empty storage array is 0x32; V1 checkIndex fails too. -/
theorem storage_bounds : Origin (.storageIndex (Storage.init C) ref .dyn (u 0)) .bounds ∧
    (Storage.init C).checkIndex ref (.arr .dyn) (u 0) = none :=
  storage_index_origin _ _ _ _ _ rfl rfl

private def singleton : SVal (.ref (.array (.prim .uint))) :=
  .array (SVec.ofList [.prim (u 7)]) (.ofList []) (by decide)
private def one : Storage C := (Storage.init C).set ref.hroot singleton

/-- Index zero of a singleton succeeds, index one fails. Unlike a missing
path, this is a bounds origin with an existing storage value. -/
theorem storage_singleton :
    (Producer.storageIndex one ref .dyn (u 0)).run = .ok () ∧
    Origin (.storageIndex one ref .dyn (u 1)) .bounds := by
  constructor
  · rfl
  · exact (storage_index_origin _ _ _ _ _ rfl rfl).1

/-- Pop of a singleton succeeds in both modes; its resulting live length is
zero. The shadow-retention choice cannot spuriously introduce an empty-pop panic. -/
theorem pop_success (keep : Bool) :
    ((Producer.pop one keep ref).run.toOption.bind (Storage.len · ref)) = some (u 0) := by
  have found : one.find ref = some singleton := rfl
  cases keep <;>
    simp only [Producer.run, Storage.pop, found, singleton, SVal.view_array,
      Option.bind_eq_bind, Option.bind_some, SVec.ofList, SList.ofList,
      SVec.toList, SList.toList]
    <;> rfl


private abbrev A : RefTy := .array (.prim .uint)
private def obj : MObj [] A := ⟨[u 7], by decide⟩
private def hp : Heap [A] := (Heap.empty.alloc obj).1
private def hr : HRef [A] A := ⟨0, rfl⟩

/-- Last valid heap index succeeds with its value; index == length fails with
0x32. This prevents an off-by-one change or an unconditional bounds label. -/
theorem heap_bounds : Origin (.index hp hr .dyn (u 1)) .bounds ∧
    (Producer.index hp hr .dyn (u 0)).run = .ok (u 7) :=
by
  constructor
  · apply index_origin
    simp only [Heap.index, MObj.elems_dyn, hp, hr, Heap.get, Heap.alloc,
      Objs.get, Objs.snoc, MObj.wk, obj]
    rfl
  · have h : hp.index hr .dyn (u 0) = some (u 7) := by
      simp only [Heap.index, MObj.elems_dyn, hp, hr, Heap.get, Heap.alloc,
        Objs.get, Objs.snoc, MObj.wk, obj]
      rfl
    simp only [Producer.run, h, checked]

/-- Allocation at the limit succeeds; rounding one requested byte to32 crosses
it. No decoder admission verdict is changed by observing this producer. -/
theorem allocation_boundary :
    (Producer.allocation ⟨[], AbiEntry.lim - 32⟩ 0 32).run = .ok 32 ∧
    Origin (.allocation ⟨[], AbiEntry.lim - 31⟩ 0 1) .allocation ∧
    Origin (.allocation ⟨[], AbiEntry.lim⟩ 1 0) .allocation :=
  ⟨rfl, allocation_origin _ _ _ rfl, allocation_origin _ _ _ rfl⟩

/-- Zero internal tag fails; a nonzero tag retains its value without any claim
that the source importer associates it with a particular function. -/
theorem internal_boundary : Origin (.internalFunction (u 0)) .zeroInternalFunction ∧
    (Producer.internalFunction (u 1)).run = .ok (u 1) :=
  ⟨internal_origin _ rfl, rfl⟩

/-- An observed failed assertion cannot be relabelled as arithmetic even
though both are failures; origin evidence is tied to the producer. -/
theorem wrong_origin : ¬ Origin (.assertion false) .arithmetic := by
  intro h
  have bad := Origin.unique assertion_origin h
  cases bad

/-- Preserve every original code, rather than equating arbitrary revert data
with a typed origin. Binary zero-divisor classification also agrees. -/
theorem code_boundary :
    Site.assertion.code = 0x01 ∧ Site.arithmetic.code = 0x11 ∧
    Site.zeroDivisor.code = 0x12 ∧ Site.enumConversion.code = 0x21 ∧
    Site.storageEncoding.code = 0x22 ∧ Site.emptyPop.code = 0x31 ∧
    Site.bounds.code = 0x32 ∧ Site.allocation.code = 0x41 ∧
    Site.zeroInternalFunction.code = 0x51 := original_codes

/-- Both binary zero-divisor classifiers retain code 0x12. -/
theorem division_codes : (Checked.div.failure 0).map Site.code = some 0x12 ∧
    (Checked.mod.failure 0).map Site.code = some 0x12 := zero_divisor_codes

/-- Observe only a local producer's code, never ABI bytes or external payloads. -/
private def observedCode {α : Type} (p : Producer α) : Option Nat :=
  match p.run with
  | .error (some site) => some site.code
  | _ => none

private theorem observed_origin {α : Type} {p : Producer α} {site : Site}
    (h : Origin p site) : observedCode p = some site.code := by
  unfold observedCode
  rw [h]

/-- Real failed producers reach all nine code observations. This couples the
code-table contract to typed failure witnesses rather than merely aliasing it. -/
theorem observed_codes :
    observedCode (.assertion false) = some 0x01 ∧
    observedCode (.binary .add .uint rfl umax (u 1)) = some 0x11 ∧
    observedCode (.binary .div .int rfl im ⟨0, by decide⟩) = some 0x12 ∧
    observedCode (.enumConversion 2 (u 2)) = some 0x21 ∧
    observedCode (.storageEncoding (u 63)) = some 0x22 ∧
    observedCode (.pop (Storage.init C) false ref) = some 0x31 ∧
    observedCode (.storageIndex (Storage.init C) ref .dyn (u 0)) = some 0x32 ∧
    observedCode (.allocation ⟨[], AbiEntry.lim - 31⟩ 0 1) = some 0x41 ∧
    observedCode (.internalFunction (u 0)) = some 0x51 := by
  rcases code_boundary with ⟨a, b, _, d, e, f, g, h, i⟩
  have z : some Site.zeroDivisor.code = some 0x12 := by
    simpa only [Checked.failure, ↓reduceIte, Option.map_some] using division_codes.1
  exact ⟨(observed_origin assertion_origin).trans (congrArg some a),
    (observed_origin add_overflow).trans (congrArg some b),
    (observed_origin zero_divisors.1).trans z,
    (observed_origin enum_boundary.1).trans (congrArg some d),
    (observed_origin encoding_boundary.2.1).trans (congrArg some e),
    (observed_origin (empty_pop false)).trans (congrArg some f),
    (observed_origin storage_bounds.1).trans (congrArg some g),
    (observed_origin allocation_boundary.2.1).trans (congrArg some h),
    (observed_origin internal_boundary.1).trans (congrArg some i)⟩

/-- Neither successful assertion nor missing-path failure invents a code. -/
theorem no_spurious_code : observedCode (.assertion true) = none ∧
    observedCode (.pop (Storage.init C) false missing) = none := by
  simp only [observedCode, missing_path.1]
  exact ⟨rfl, trivial⟩

end Solidity.Examples.Panic.Origins
