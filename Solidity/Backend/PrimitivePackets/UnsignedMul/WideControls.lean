import Solidity.Backend.PrimitivePackets.UnsignedMul.Execution
import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRefArrayControls
import Solidity.Source.SemanticsExamples

/-! Inhabited independent-local executions, with an old allocated array,
reserved memory, allocator cursor and a nonempty saved caller stack. -/
namespace Solidity.Backend.PrimitivePackets.UnsignedMul.WideControls
open Evm Evm.Memory Solidity.Lowering.V07 Backend.Passes
open Solidity.Lowering.V07.UnsignedNarrowing
open Solidity.Backend.InternalFlow.RuntimeFrame
open Source.SemanticsExamples
namespace Seed
abbrev C := V3CallProducerRef.ArrayControls.C
abbrev A := V3CallProducerRef.ArrayControls.A
abbrev caller := V3CallProducerRef.ArrayControls.caller
abbrev machine := V3CallProducerRef.ArrayControls.machine
abbrev bases := V3CallProducerRef.ArrayControls.bases
abbrev initial := V3CallProducerRef.ArrayControls.initial
abbrev F := V3CallProducerRef.ArrayControls.F
end Seed
abbrev Γ : Ctx := [.val .uint,.val .uint,.val .uint,.mem Seed.A]
def F : Frag Γ := (Seed.F.push (.val .uint) .ok).push (.val .uint) .ok

def inRange (x : Fin W) : Source.IntTy.u256.lo ≤ (x.val : Int) ∧
    (x.val : Int) ≤ Source.IntTy.u256.hi := by
  have h := x.isLt
  change 0 ≤ (x.val : Int) ∧ (x.val : Int) ≤ ((W : Nat) : Int)-1
  omega

def value (x : Fin W) := integerValue .u256 (x.val : Int) (inRange x)
def word (x : Fin W) : Word := .val x
def target (x y : Fin W) : State Seed.C Γ :=
  ((Seed.caller (wmod 7)).push (t := .val .uint) (value y)).push (t := .val .uint) (value x)
def machine (x y : Fin W) : Machine :=
  writeMachine (writeMachine (Seed.machine (wmod 7)) 3 (word y)) 4 (word x)

theorem represented (x y : Fin W) : StateRepr 1 1 64 F (target x y) Seed.bases (machine x y) :=
  (((Seed.initial (wmod 7)).1.consVal (value y) (word y) (ReprV.uint_of rfl) (by decide)).consVal
    (value x) (word x) (ReprV.uint_of rfl) (by decide))

def source (x y : Fin W) : Source.EMState E0 [.int .u256,.int .u256] :=
  (.cons (.int x.val (inRange x)) (.cons (.int y.val (inRange y)) .nil),s0)
def si : Bool → Source.Idx [.int .u256,.int .u256] (.int .u256)
  | false => .here | true => .there .here
def ti : Bool → Idx Γ (.val .uint)
  | false => .here | true => .there .here

theorem independent : (si false).toNat ≠ (si true).toNat ∧
    (ti false).toNat ≠ (ti true).toNat := by decide

theorem family (x y : Fin W) : IntegerLocalFamily .u256 si ti (source x y).1 (target x y).env := by
  constructor
  · intro k
    cases k
    · exact integer_related .u256 x.val (inRange x)
    · exact integer_related .u256 y.val (inRange y)
  · intro k l
    cases k <;> cases l <;> rfl

def application (p : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) (x y : Fin W) :=
  execution (G0 p) {F0 with checked := checked} fuel (source x y) (target x y) 256
    (by decide) si ti (family x y) false true x.val y.val (inRange x) (inRange y) rfl rfl (represented x y)

def code := (selected (C := Seed.C) 1 F 256 (ti false) (ti true)).code

theorem maximum_wrap (p : Roadmap.Pipeline) (tail : List Word) :
    run code {machine ⟨W-1,by unfold W; decide⟩ (wmod 2) with stack := tail} =
      .ok ({machine ⟨W-1,by unfold W; decide⟩ (wmod 2) with stack := tail}.push w[W-2]) 0 := by
  obtain ⟨actual,hr,runs⟩ := (application p 0 false ⟨W-1,by unfold W; decide⟩ (wmod 2)).2.2.2.2
  have same : actual = w[W-2] := Restored.value_unique hr (ReprV.uint_of rfl)
  subst actual
  exact (runs tail).1

end Solidity.Backend.PrimitivePackets.UnsignedMul.WideControls
