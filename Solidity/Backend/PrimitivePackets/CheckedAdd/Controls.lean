import Solidity.Backend.PrimitivePackets.CheckedAdd.Agreement
import Solidity.Evm.MemoryCompileExamples
import Solidity.Source.SemanticsExamples

/-! Populated caller heap/aliases/frame, arbitrary saved stack, both pipelines,
uint256 boundary execution and refusal controls through public selected code. -/
namespace Solidity.Backend.PrimitivePackets.CheckedAdd.Controls
open Evm Evm.Memory Solidity.Lowering.V07
open Source.SemanticsExamples (E0 G0 F0 s0)
namespace Fixture
open CompileExamples (C)
abbrev Γ : Ctx := .val .uint :: .val .uint :: CompileExamples.Γ
abbrev F := Frag.init Γ
abbrev srcΓ : Source.RCtx := [.int U,.int U]

theorem nat_range (n : Nat) (h : n < W) : U.lo ≤ (n:Int) ∧ (n:Int) ≤ U.hi := by
  change 0 ≤ (n:Int) ∧ (n:Int) ≤ (W:Int)-1
  omega

def u (n : Nat) (h : n<W) : PrimTy.uint.Denote := integerValue U n (nat_range n h)
def source (x y : Nat) (hx : x<W) (hy : y<W) : Source.EMState E0 srcΓ :=
  (.cons (.int x (nat_range x hx)) (.cons (.int y (nat_range y hy)) .nil),s0)
def target (x y : Nat) (hx : x<W) (hy : y<W) : State C Γ :=
  (CompileExamples.σ.push (t:=.val .uint) (u y hy)).push (t:=.val .uint) (u x hx)
def machine (x y : Nat) (hx : x<W) (hy : y<W) : Machine :=
  writeMachine (writeMachine CompileExamples.machine 4 (.val ⟨y,hy⟩)) 5 (.val ⟨x,hx⟩)
def si (k : Bool) : Source.Idx srcΓ (.int U) := if k then .there .here else .here
def ti (k : Bool) : Idx Γ (.val .uint) := if k then .there .here else .here

theorem family (x y : Nat) (hx : x<W) (hy : y<W) :
    IntegerLocalFamily U si ti (source x y hx hy).1 (target x y hx hy).env := by
  constructor
  · intro k; cases k <;> exact integer_related _ _ _
  · intro i j; cases i <;> cases j <;> decide

theorem represented (x y : Nat) (hx : x<W) (hy : y<W) :
    StateRepr 1 0 8 F (target x y hx hy) CompileExamples.base (machine x y hx hy) := by
  have start : StateRepr 1 0 8 (Frag.init CompileExamples.Γ) CompileExamples.σ
      CompileExamples.base CompileExamples.machine :=
    Backend.Passes.memory_frame CompileExamples.fixture_repr (by decide)
      (by intro p r; dsimp only [CompileExamples.base]; split <;> decide)
      (by intro name r; dsimp only [CompileExamples.base]; split <;> decide)
  have ry : ReprV .uint (u y hy) (.val ⟨y,hy⟩) := ReprV.uint_of (by rfl)
  have rx : ReprV .uint (u x hx) (.val ⟨x,hx⟩) := ReprV.uint_of (by rfl)
  exact (start.consVal (u y hy) (.val ⟨y,hy⟩) ry (by decide)).consVal
    (u x hx) (.val ⟨x,hx⟩) rx (by decide)

def sumCode : List Instr := (selected (C:=C) 0 F (.here) (.there .here)).code

theorem result (x y : Nat) (hx : x<W) (hy : y<W) (small : x+y<W) (tail : List Word) :
    run sumCode {machine x y hx hy with stack := tail} =
      .ok ({machine x y hx hy with stack := tail}.push (.val ⟨x+y,small⟩)) 0 := by
  obtain ⟨word,repr,ran⟩ := target_success (target x y hx hy) .here (.there .here) x y
    (nat_range x hx) (nat_range y hy) rfl rfl (nat_range (x+y) small)
    (represented x y hx hy) tail
  rcases repr with ⟨actual,rfl,content⟩
  have same : actual = (⟨x+y,small⟩ : Fin W) := by
    apply Fin.ext
    change actual.val = x+y
    change ((x+y : Nat) : Int) = actual.val at content
    omega
  rw [same] at ran
  exact ran

theorem minimum (tail : List Word) :
    run sumCode {machine 0 0 (by decide) (by decide) with stack := tail} =
      .ok ({machine 0 0 (by decide) (by decide) with stack := tail}.push w[0]) 0 := by
  exact result 0 0 (by decide) (by decide) (by decide) tail

theorem maximum (tail : List Word) :
    run sumCode {machine (W-1) 0 (by decide) (by decide) with stack := tail} =
      .ok ({machine (W-1) 0 (by decide) (by decide) with stack := tail}.push (.val ⟨W-1,by decide⟩)) 0 := by
  exact result (W-1) 0 (by decide) (by decide) (by decide) tail

theorem overflow (tail : List Word) :
    run sumCode {machine (W-1) 1 (by decide) (by decide) with stack := tail} = .revert := by
  exact target_overflow (target (W-1) 1 (by decide) (by decide)) .here (.there .here)
    (W-1) 1 (nat_range _ (by decide)) (nat_range _ (by decide)) rfl rfl
    (by decide) (represented _ _ (by decide) (by decide)) tail

theorem regular (tail : List Word) :
    run sumCode {machine 7 9 (by decide) (by decide) with stack := tail} =
      .ok ({machine 7 9 (by decide) (by decide) with stack := tail}.push w[16]) 0 := by
  exact result 7 9 (by decide) (by decide) (by decide) tail


def jointSuccess (p : Roadmap.Pipeline) (tail : List Word) :=
  CheckedAdd.success (G0 p) F0 0 (source 7 9 (by decide) (by decide))
    (target 7 9 (by decide) (by decide)) si ti (family 7 9 (by decide) (by decide)) false true
    7 9 (nat_range 7 (by decide)) (nat_range 9 (by decide)) rfl rfl
    (nat_range 16 (by decide)) (represented 7 9 (by decide) (by decide)) tail

def jointOverflow (p : Roadmap.Pipeline) (tail : List Word) :=
  CheckedAdd.overflow (G0 p) F0 0 (source (W-1) 1 (by decide) (by decide))
    (target (W-1) 1 (by decide) (by decide)) si ti
    (family (W-1) 1 (by decide) (by decide)) false true
    (W-1) 1 (nat_range (W-1) (by decide)) (nat_range 1 (by decide)) rfl rfl
    (by decide) (represented (W-1) 1 (by decide) (by decide)) tail

theorem double_overflow (tail : List Word) :
    run sumCode {machine (W-1) (W-1) (by decide) (by decide) with stack := tail} = .revert := by
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
  source_overflow (G0 p) F0 0 (source (W-1) 1 (by decide) (by decide)) .here (.there .here)
    (W-1) 1 (nat_range (W-1) (by decide)) (nat_range 1 (by decide)) rfl rfl (by decide)

theorem low_fuel (p : Roadmap.Pipeline) :
    (Source.evalE (G0 p) {F0 with checked := true} 0
      (.binary .add (.local .here) (.local (.there .here)))).run (source 7 9 (by decide) (by decide)) =
      (.error .timeout,source 7 9 (by decide) (by decide)) := by
  first | rfl | decide | omega
end Fixture

theorem exact_panic_bytes : Source.panicData .arithmetic =
    [0x4e,0x48,0x7b,0x71] ++ List.replicate 31 0 ++ [0x11] := by
  first | decide | rfl | omega

theorem panic_not_truncated : Source.panicData .arithmetic ≠
    [0x4e,0x48,0x7b,0x71,0x11] := by
  first | decide | rfl | omega

theorem panic_not_empty : Source.panicData .arithmetic ≠ [] := by
  first | decide | rfl | omega
end Solidity.Backend.PrimitivePackets.CheckedAdd.Controls
