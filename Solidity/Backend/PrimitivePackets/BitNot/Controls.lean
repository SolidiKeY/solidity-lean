import Solidity.Backend.PrimitivePackets.BitNot.Agreement
import Solidity.Evm.MemoryCompileExamples
import Solidity.Source.SemanticsExamples

/-! Populated heap/alias/caller-frame controls for actual selected NOT code.
The generic result covers every valid unsigned width; concrete narrow/full
boundaries, both pipelines/check modes, masking and refusal cases are retained. -/
namespace Solidity.Backend.PrimitivePackets.BitNot.Controls
open Evm Evm.Memory Solidity.Lowering.V07
open UnsignedNarrowing (ty)
open Source.SemanticsExamples (E0 G0 F0 s0)
namespace Fixture
open CompileExamples (C)
abbrev Γ : Ctx := .val .uint :: .val .uint :: CompileExamples.Γ
abbrev F := Frag.init Γ
abbrev srcΓ (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) : Source.RCtx :=
 [.int (ty bits valid),.int (ty bits valid)]

theorem nat_range (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
 (x : Nat) (bound : x < 2^bits) : (ty bits valid).lo ≤ (x:Int) ∧ (x:Int) ≤ (ty bits valid).hi := by
 have positive := Source.two_pow_pos bits
 simp only [ty,Source.IntTy.lo,Source.IntTy.hi,Bool.false_eq_true,if_false]
 omega

theorem wide_bound (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
 (x : Nat) (bound : x < 2^bits) : x < W :=
 Nat.lt_of_lt_of_le bound (Source.two_pow_le valid.2.2)

def u (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (x : Nat) (bound : x < 2^bits) :
 PrimTy.uint.Denote := integerValue (ty bits valid) x (nat_range bits valid x bound)
def source (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
 (x y : Nat) (hx : x < 2^bits) (hy : y < 2^bits) : Source.EMState E0 (srcΓ bits valid) :=
 (.cons (.int x (nat_range bits valid x hx)) (.cons (.int y (nat_range bits valid y hy)) .nil),s0)
def target (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
 (x y : Nat) (hx : x < 2^bits) (hy : y < 2^bits) : State C Γ :=
 (CompileExamples.σ.push (t:=.val .uint) (u bits valid y hy)).push (t:=.val .uint) (u bits valid x hx)
def machine (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
 (x y : Nat) (hx : x < 2^bits) (hy : y < 2^bits) : Machine :=
 writeMachine (writeMachine CompileExamples.machine 4 (.val ⟨y,wide_bound bits valid y hy⟩))
   5 (.val ⟨x,wide_bound bits valid x hx⟩)
def si (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (k : Bool) :
 Source.Idx (srcΓ bits valid) (.int (ty bits valid)) := if k then .there .here else .here
def ti (k : Bool) : Idx Γ (.val .uint) := if k then .there .here else .here

theorem family (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
 (x y : Nat) (hx : x < 2^bits) (hy : y < 2^bits) :
 IntegerLocalFamily (ty bits valid) (si bits valid) ti (source bits valid x y hx hy).1 (target bits valid x y hx hy).env := by
 constructor
 · intro k; cases k <;> exact integer_related _ _ _
 · intro i j; cases i <;> cases j <;> rfl

theorem represented (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
 (x y : Nat) (hx : x < 2^bits) (hy : y < 2^bits) :
 StateRepr 1 0 8 F (target bits valid x y hx hy) CompileExamples.base (machine bits valid x y hx hy) := by
 have start : StateRepr 1 0 8 (Frag.init CompileExamples.Γ) CompileExamples.σ CompileExamples.base CompileExamples.machine :=
   Backend.Passes.memory_frame CompileExamples.fixture_repr (by decide)
     (by intro p r; dsimp only [CompileExamples.base]; split <;> decide)
     (by intro name r; dsimp only [CompileExamples.base]; split <;> decide)
 have rx : ReprV .uint (u bits valid x hx) (.val ⟨x,wide_bound bits valid x hx⟩) := ReprV.uint_of (by rfl)
 have ry : ReprV .uint (u bits valid y hy) (.val ⟨y,wide_bound bits valid y hy⟩) := ReprV.uint_of (by rfl)
 exact (start.consVal (u bits valid y hy) (.val ⟨y,wide_bound bits valid y hy⟩) ry (by decide)).consVal
   (u bits valid x hx) (.val ⟨x,wide_bound bits valid x hx⟩) rx (by decide)

def resultNat (bits x : Nat) := 2^bits-1-x

theorem result_range (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (x : Nat) :
 resultNat bits x < W := by
 have positive := Source.two_pow_pos bits
 have wide := Source.two_pow_le valid.2.2
 unfold resultNat
 change 2^bits-1-x < 2^256
 omega

theorem computed (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
 (x : Nat) (hx : x < 2^bits) :
 (ty bits valid).wrap (-(x:Int)-1) = (resultNat bits x : Int) := by
 rw [BitNot.masked_value bits valid x (nat_range bits valid x hx)]
 have positive := Source.two_pow_pos bits
 unfold resultNat
 omega

def code (bits : Nat) := (selected (C:=C) bits 0 F (.here)).code

theorem result (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
 (x y : Nat) (hx : x < 2^bits) (hy : y < 2^bits) (tail : List Word) :
 run (code bits) {machine bits valid x y hx hy with stack := tail} =
 .ok ({machine bits valid x y hx hy with stack := tail}.push (.val ⟨resultNat bits x,result_range bits valid x⟩)) 0 := by
 obtain ⟨word,repr,ran⟩ := target_success (target bits valid x y hx hy) bits valid .here x
   (nat_range bits valid x hx) rfl (represented bits valid x y hx hy) tail
 rcases repr with ⟨actual,rfl,content⟩
 have same : actual = (⟨resultNat bits x,result_range bits valid x⟩ : Fin W) := by
   apply Fin.ext
   change actual.val = resultNat bits x
   change (ty bits valid).wrap (-(x:Int)-1) = (actual.val:Int) at content
   rw [computed bits valid x hx] at content
   omega
 rw [same] at ran
 exact ran

theorem uint8_zero (tail : List Word) :
 run (code 8) {machine 8 (by decide) 0 7 (by decide) (by decide) with stack := tail} =
 .ok ({machine 8 (by decide) 0 7 (by decide) (by decide) with stack := tail}.push w[255]) 0 :=
 result 8 (by decide) 0 7 (by decide) (by decide) tail

theorem uint8_max (tail : List Word) :
 run (code 8) {machine 8 (by decide) 255 7 (by decide) (by decide) with stack := tail} =
 .ok ({machine 8 (by decide) 255 7 (by decide) (by decide) with stack := tail}.push w[0]) 0 :=
 result 8 (by decide) 255 7 (by decide) (by decide) tail

theorem uint8_regular (tail : List Word) :
 run (code 8) {machine 8 (by decide) 5 7 (by decide) (by decide) with stack := tail} =
 .ok ({machine 8 (by decide) 5 7 (by decide) (by decide) with stack := tail}.push w[250]) 0 :=
 result 8 (by decide) 5 7 (by decide) (by decide) tail

theorem uint16_regular (tail : List Word) :
 run (code 16) {machine 16 (by decide) 0x1234 7 (by decide) (by decide) with stack := tail} =
 .ok ({machine 16 (by decide) 0x1234 7 (by decide) (by decide) with stack := tail}.push w[0xedcb]) 0 :=
 result 16 (by decide) 0x1234 7 (by decide) (by decide) tail

theorem uint256_zero (tail : List Word) :
 run (code 256) {machine 256 (by decide) 0 7 (by decide) (by decide) with stack := tail} =
 .ok ({machine 256 (by decide) 0 7 (by decide) (by decide) with stack := tail}.push (.val ⟨W-1,by decide⟩)) 0 :=
 result 256 (by decide) 0 7 (by decide) (by decide) tail

theorem uint256_max (tail : List Word) :
 run (code 256) {machine 256 (by decide) (W-1) 7 (by decide) (by decide) with stack := tail} =
 .ok ({machine 256 (by decide) (W-1) 7 (by decide) (by decide) with stack := tail}.push w[0]) 0 :=
 result 256 (by decide) (W-1) 7 (by decide) (by decide) tail

def joint8 (p : Roadmap.Pipeline) (checked : Bool) (tail : List Word) :=
 BitNot.success 8 (by decide) (G0 p) {F0 with checked := checked} 0
   (source 8 (by decide) 5 7 (by decide) (by decide)) (target 8 (by decide) 5 7 (by decide) (by decide))
   (si 8 (by decide)) ti (family 8 (by decide) 5 7 (by decide) (by decide)) false 5
   (nat_range 8 (by decide) 5 (by decide)) rfl (represented 8 (by decide) 5 7 (by decide) (by decide)) tail

theorem wrong_value_refused :
 ¬ IntegerLocalFamily (ty 8 (by decide)) (si 8 (by decide)) ti
   (source 8 (by decide) 5 7 (by decide) (by decide)).1
   (target 8 (by decide) 5 8 (by decide) (by decide)).env := by
 intro h
 have same := h.read true 7 (nat_range 8 (by decide) 7 (by decide)) rfl
 have numeric : (8:Int) = 7 := congrArg Subtype.val same
 omega

theorem wrong_index_refused :
 ¬ IntegerLocalFamily (ty 8 (by decide)) (si 8 (by decide)) (fun _ => (.here : Idx Γ (.val .uint)))
   (source 8 (by decide) 5 7 (by decide) (by decide)).1
   (target 8 (by decide) 5 7 (by decide) (by decide)).env := by
 intro h
 have same := (h.aliases false true).mpr rfl
 have different : (si 8 (by decide) false).toNat ≠ (si 8 (by decide) true).toNat := by decide
 exact different same

theorem mask_present : code 8 ≠ (rawSelected (C:=C) 0 F .here).code := by
 intro same
 have lengths := congrArg List.length same
 have different : (code 8).length ≠ (rawSelected (C:=C) 0 F .here).code.length := by decide
 exact different lengths

theorem unmasked_result (tail : List Word) :
 run (rawSelected (C:=C) 0 F .here).code {machine 8 (by decide) 5 7 (by decide) (by decide) with stack := tail} =
 .ok ({machine 8 (by decide) 5 7 (by decide) (by decide) with stack := tail}.push (.val ⟨W-6,by decide⟩)) 0 :=
 result 256 (by decide) 5 7 (by decide) (by decide) tail

theorem missing_mask_refused (tail : List Word) :
 run (rawSelected (C:=C) 0 F .here).code {machine 8 (by decide) 5 7 (by decide) (by decide) with stack := tail} ≠
 .ok ({machine 8 (by decide) 5 7 (by decide) (by decide) with stack := tail}.push w[250]) 0 := by
 intro bad
 have same := (unmasked_result tail).symm.trans bad
 have stacks := congrArg Machine.stack (Out.ok.inj same).1
 have different : (Word.val ⟨W-6,by decide⟩ : Word) ≠ w[250] := by decide
 exact different (List.cons.inj stacks).1

def protectedCells : List Nat := [0,1,2,3,16,17,18,20,21]
theorem protected_frame :
 protectedCells.map (machine 8 (by decide) 5 7 (by decide) (by decide)).mem =
 [w[20],w[16],w[16],w[0],w[2],w[7],w[9],w[1],w[4]] := by rfl

theorem low_fuel (p : Roadmap.Pipeline) (checked : Bool) :
 (Source.evalE (G0 p) {F0 with checked := checked} 1
   (.unary .bitNot (.local .here))).run (source 8 (by decide) 5 7 (by decide) (by decide)) =
 (.error .timeout,source 8 (by decide) 5 7 (by decide) (by decide)) := by rfl
end Fixture

example : ¬ (7 % 8 = 0 ∧ 8 ≤ 7 ∧ 7 ≤ 256) := by decide
example : ¬ (264 % 8 = 0 ∧ 8 ≤ 264 ∧ 264 ≤ 256) := by decide
example : ¬ ((ty 8 (by decide)).lo ≤ (257:Int) ∧ (257:Int) ≤ (ty 8 (by decide)).hi) := by decide
end Solidity.Backend.PrimitivePackets.BitNot.Controls

/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.nat_range' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.nat_range
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.wide_bound' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.wide_bound
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.family
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.represented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.represented
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.result_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.result_range
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.computed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.computed
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.result
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.uint8_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.uint8_zero
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.uint8_max' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.uint8_max
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.uint8_regular' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.uint8_regular
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.uint16_regular' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.uint16_regular
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.uint256_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.uint256_zero
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.uint256_max' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.uint256_max
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.wrong_value_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.wrong_value_refused
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.wrong_index_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.wrong_index_refused
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.mask_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.mask_present
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.unmasked_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.unmasked_result
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.missing_mask_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.missing_mask_refused
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.protected_frame' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.protected_frame
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.low_fuel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.low_fuel
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.joint8' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.joint8
