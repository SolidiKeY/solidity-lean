import Solidity.Backend.PrimitivePackets.CheckedMul.Agreement
import Solidity.Backend.PrimitivePackets.CheckedMul.Populated
import Solidity.Backend.PrimitivePackets.PanicBytes
import Solidity.Source.SemanticsExamples

/-! Populated caller heap/aliases/frame, arbitrary saved stack, both pipelines,
uint256 boundary execution and refusal controls through public selected code. -/
namespace Solidity.Backend.PrimitivePackets.CheckedMul.Controls
open Evm Evm.Memory Solidity.Lowering.V07
open Source.SemanticsExamples (E0 G0 F0 s0)
namespace Fixture
open Populated (C)
abbrev Γ : Ctx := .val .uint :: .val .uint :: Populated.Γ
abbrev F := Frag.init Γ
abbrev srcΓ : Source.RCtx := [.int U,.int U]

theorem nat_range (n : Nat) (h : n < W) : U.lo ≤ (n:Int) ∧ (n:Int) ≤ U.hi := by
  change 0 ≤ (n:Int) ∧ (n:Int) ≤ (W:Int)-1
  omega

def u (n : Nat) (h : n<W) : PrimTy.uint.Denote := integerValue U n (nat_range n h)
def source (x y : Nat) (hx : x<W) (hy : y<W) : Source.EMState E0 srcΓ :=
  (.cons (.int x (nat_range x hx)) (.cons (.int y (nat_range y hy)) .nil),s0)
def target (x y : Nat) (hx : x<W) (hy : y<W) : State C Γ :=
  (Populated.σ.push (t:=.val .uint) (u y hy)).push (t:=.val .uint) (u x hx)
def machine (x y : Nat) (hx : x<W) (hy : y<W) : Machine :=
  writeMachine (writeMachine Populated.machine 4 (.val ⟨y,hy⟩)) 5 (.val ⟨x,hx⟩)
def si (k : Bool) : Source.Idx srcΓ (.int U) := if k then .there .here else .here
def ti (k : Bool) : Idx Γ (.val .uint) := if k then .there .here else .here

theorem family (x y : Nat) (hx : x<W) (hy : y<W) :
    IntegerLocalFamily U si ti (source x y hx hy).1 (target x y hx hy).env := by
  constructor
  · intro k; cases k <;> exact integer_related _ _ _
  · intro i j; cases i <;> cases j <;> decide

theorem represented (x y : Nat) (hx : x<W) (hy : y<W) :
    StateRepr 1 0 8 F (target x y hx hy) Populated.base (machine x y hx hy) := by
  have start : StateRepr 1 0 8 (Frag.init Populated.Γ) Populated.σ
      Populated.base Populated.machine :=
    ⟨Populated.fixture_repr.core,
      ⟨Populated.heap_repr.arrays,(by intro p r; dsimp only [Populated.base];split <;> decide),
        Populated.heap_repr.separated⟩,
      Populated.fixture_repr.pointers,(by decide),
      ⟨Populated.fixture_repr.structs.objects,
        (by intro name r; dsimp only [Populated.base];split <;> decide),
        Populated.fixture_repr.structs.separated⟩,
      Populated.fixture_repr.separated,Populated.fixture_repr.refs⟩
  have ry : ReprV .uint (u y hy) (.val ⟨y,hy⟩) := ReprV.uint_of (by rfl)
  have rx : ReprV .uint (u x hx) (.val ⟨x,hx⟩) := ReprV.uint_of (by rfl)
  exact (start.consVal (u y hy) (.val ⟨y,hy⟩) ry (by decide)).consVal
    (u x hx) (.val ⟨x,hx⟩) rx (by decide)

def productCode : List Instr := (selected (C:=C) 0 F (.here) (.there .here)).code

theorem result (x y : Nat) (hx : x<W) (hy : y<W) (small : x*y<W) (tail : List Word) :
    run productCode {machine x y hx hy with stack := tail} =
      .ok ({machine x y hx hy with stack := tail}.push (.val ⟨x*y,small⟩)) 0 := by
  obtain ⟨word,repr,ran⟩ := target_success (target x y hx hy) .here (.there .here) x y
    (nat_range x hx) (nat_range y hy) rfl rfl (nat_range (x*y) small)
    (represented x y hx hy) tail
  rcases repr with ⟨actual,rfl,content⟩
  have same : actual = (⟨x*y,small⟩ : Fin W) := by
    apply Fin.ext
    change actual.val = x*y
    change ((x*y : Nat) : Int) = actual.val at content
    omega
  rw [same] at ran
  exact ran

theorem minimum (tail : List Word) :
    run productCode {machine 0 0 (by decide) (by decide) with stack := tail} =
      .ok ({machine 0 0 (by decide) (by decide) with stack := tail}.push w[0]) 0 := by
  exact result 0 0 (by decide) (by decide) (by decide) tail

/-- The zero operand disjunct in the selected multiplication guard is live. -/
theorem zero_left (tail : List Word) :
    run productCode {machine 0 (W-1) (by decide) (by decide) with stack:=tail} =
      .ok ({machine 0 (W-1) (by decide) (by decide) with stack:=tail}.push w[0]) 0 :=
  result 0 (W-1) (by decide) (by decide) (by decide) tail

theorem zero_right (tail : List Word) :
    run productCode {machine (W-1) 0 (by decide) (by decide) with stack:=tail} =
      .ok ({machine (W-1) 0 (by decide) (by decide) with stack:=tail}.push w[0]) 0 :=
  result (W-1) 0 (by decide) (by decide) (by decide) tail

theorem maximum (tail : List Word) :
    run productCode {machine (W-1) 1 (by decide) (by decide) with stack := tail} =
      .ok ({machine (W-1) 1 (by decide) (by decide) with stack := tail}.push (.val ⟨W-1,by decide⟩)) 0 := by
  exact result (W-1) 1 (by decide) (by decide) (by decide) tail

theorem overflow (tail : List Word) :
    run productCode {machine (W-1) 2 (by decide) (by decide) with stack := tail} = .revert := by
  exact target_overflow (target (W-1) 2 (by decide) (by decide)) .here (.there .here)
    (W-1) 2 (nat_range _ (by decide)) (nat_range _ (by decide)) rfl rfl
    (by decide) (represented _ _ (by decide) (by decide)) tail

theorem regular (tail : List Word) :
    run productCode {machine 7 9 (by decide) (by decide) with stack := tail} =
      .ok ({machine 7 9 (by decide) (by decide) with stack := tail}.push w[63]) 0 := by
  exact result 7 9 (by decide) (by decide) (by decide) tail


def jointSuccess (p : Roadmap.Pipeline) (tail : List Word) :=
  CheckedMul.success (G0 p) F0 0 (source 7 9 (by decide) (by decide))
    (target 7 9 (by decide) (by decide)) si ti (family 7 9 (by decide) (by decide)) false true
    7 9 (nat_range 7 (by decide)) (nat_range 9 (by decide)) rfl rfl
    (nat_range 63 (by decide)) (represented 7 9 (by decide) (by decide)) tail

def jointMaximum (p : Roadmap.Pipeline) (tail : List Word) :=
  CheckedMul.success (G0 p) F0 0 (source (W-1) 1 (by decide) (by decide))
    (target (W-1) 1 (by decide) (by decide)) si ti
    (family (W-1) 1 (by decide) (by decide)) false true
    (W-1) 1 (nat_range (W-1) (by decide)) (nat_range 1 (by decide)) rfl rfl
    (by decide) (represented (W-1) 1 (by decide) (by decide)) tail

def jointZeroLeft (p : Roadmap.Pipeline) (tail : List Word) :=
  CheckedMul.success (G0 p) F0 0 (source 0 (W-1) (by decide) (by decide))
    (target 0 (W-1) (by decide) (by decide)) si ti
    (family 0 (W-1) (by decide) (by decide)) false true
    0 (W-1) (nat_range 0 (by decide)) (nat_range (W-1) (by decide)) rfl rfl
    (by decide) (represented 0 (W-1) (by decide) (by decide)) tail

def jointZeroRight (p : Roadmap.Pipeline) (tail : List Word) :=
  CheckedMul.success (G0 p) F0 0 (source (W-1) 0 (by decide) (by decide))
    (target (W-1) 0 (by decide) (by decide)) si ti
    (family (W-1) 0 (by decide) (by decide)) false true
    (W-1) 0 (nat_range (W-1) (by decide)) (nat_range 0 (by decide)) rfl rfl
    (by decide) (represented (W-1) 0 (by decide) (by decide)) tail

def jointOverflow (p : Roadmap.Pipeline) (tail : List Word) :=
  CheckedMul.overflow (G0 p) F0 0 (source (W-1) 2 (by decide) (by decide))
    (target (W-1) 2 (by decide) (by decide)) si ti
    (family (W-1) 2 (by decide) (by decide)) false true
    (W-1) 2 (nat_range (W-1) (by decide)) (nat_range 2 (by decide)) rfl rfl
    (by decide) (represented (W-1) 2 (by decide) (by decide)) tail

theorem double_overflow (tail : List Word) :
    run productCode {machine (W-1) (W-1) (by decide) (by decide) with stack := tail} = .revert := by
  exact target_overflow (target (W-1) (W-1) (by decide) (by decide)) .here (.there .here)
    (W-1) (W-1) (nat_range _ (by decide)) (nat_range _ (by decide)) rfl rfl
    (by decide) (represented _ _ (by decide) (by decide)) tail

theorem wrong_value_refused :
    ¬ IntegerLocalFamily U si ti (source 7 9 (by decide) (by decide)).1
      (target 7 8 (by decide) (by decide)).env := by
  intro h
  have same := h.read true 9 (nat_range 9 (by decide)) rfl
  have numeric : (8:Int) = 9 := congrArg Subtype.val same
  omega

theorem wrong_index_refused :
    ¬ IntegerLocalFamily U si (fun _ => (.here : Idx Γ (.val .uint)))
      (source 7 9 (by decide) (by decide)).1 (target 7 9 (by decide) (by decide)).env := by
  intro h
  have same := (h.aliases false true).mpr rfl
  have different : (si false).toNat ≠ (si true).toNat := by decide
  exact different same

def protectedCells : List Nat := [0,1,2,3,16,17,18,20,21]
theorem protected_frame :
    protectedCells.map (machine 7 9 (by decide) (by decide)).mem =
      [w[20],w[16],w[16],w[0],w[2],w[7],w[9],w[1],w[4]] := by
  first | rfl | decide | omega

def sourceSuccess (p : Roadmap.Pipeline) :=
  source_success (G0 p) F0 0 (source 7 9 (by decide) (by decide)) .here (.there .here)
    7 9 (by decide) (by decide) rfl rfl (by decide)
def sourceOverflow (p : Roadmap.Pipeline) :=
  source_overflow (G0 p) F0 0 (source (W-1) 2 (by decide) (by decide)) .here (.there .here)
    (W-1) 2 (nat_range (W-1) (by decide)) (nat_range 2 (by decide)) rfl rfl (by decide)

theorem low_fuel (p : Roadmap.Pipeline) :
    (Source.evalE (G0 p) {F0 with checked := true} 0
      (.binary .mul (.local .here) (.local (.there .here)))).run (source 7 9 (by decide) (by decide)) =
      (.error .timeout,source 7 9 (by decide) (by decide)) := by
  first | rfl | decide | omega
end Fixture

theorem exact_panic_bytes : Source.panicData .arithmetic =
    [0x4e,0x48,0x7b,0x71] ++ List.replicate 31 0 ++ [0x11] := by
  exact PanicBytes.exact_panic_bytes

theorem panic_not_truncated : Source.panicData .arithmetic ≠
    [0x4e,0x48,0x7b,0x71,0x11] := by
  exact PanicBytes.panic_not_truncated

theorem panic_not_empty : Source.panicData .arithmetic ≠ [] := by
  exact PanicBytes.panic_not_empty

#print axioms Fixture.nat_range
#print axioms Fixture.u
#print axioms Fixture.source
#print axioms Fixture.target
#print axioms Fixture.machine
#print axioms Fixture.si
#print axioms Fixture.ti
#print axioms Fixture.family
#print axioms Fixture.represented
#print axioms Fixture.productCode
#print axioms Fixture.result
#print axioms Fixture.zero_left
#print axioms Fixture.zero_right
#print axioms Fixture.minimum
#print axioms Fixture.maximum
#print axioms Fixture.overflow
#print axioms Fixture.regular
#print axioms Fixture.jointSuccess
#print axioms Fixture.jointMaximum
#print axioms Fixture.jointZeroLeft
#print axioms Fixture.jointZeroRight
#print axioms Fixture.jointOverflow
#print axioms Fixture.double_overflow
#print axioms Fixture.wrong_value_refused
#print axioms Fixture.wrong_index_refused
#print axioms Fixture.protectedCells
#print axioms Fixture.protected_frame
#print axioms Fixture.sourceSuccess
#print axioms Fixture.sourceOverflow
#print axioms Fixture.low_fuel
#print axioms exact_panic_bytes
#print axioms panic_not_truncated
#print axioms panic_not_empty
end Solidity.Backend.PrimitivePackets.CheckedMul.Controls
