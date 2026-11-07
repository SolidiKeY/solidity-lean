import Solidity.Backend.PrimitivePackets.UnsignedMul.Execution
import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRefArrayControls
import Solidity.Source.SemanticsExamples

/-! Inhabited independent-local executions, with an old allocated array,
reserved memory, allocator cursor and a nonempty saved caller stack. -/
namespace Solidity.Backend.PrimitivePackets.UnsignedMul.Controls
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

def inRange (x : Fin 256) : Source.IntTy.u8.lo ≤ (x.val : Int) ∧
    (x.val : Int) ≤ Source.IntTy.u8.hi := by
  have h := x.isLt
  change 0 ≤ (x.val : Int) ∧ (x.val : Int) ≤ 255
  omega

def value (x : Fin 256) := integerValue .u8 (x.val : Int) (inRange x)
def word (x : Fin 256) : Word := .val ⟨x.val,Nat.lt_trans x.isLt (by decide)⟩
def target (x y : Fin 256) : State Seed.C Γ :=
  ((Seed.caller (wmod 7)).push (t := .val .uint) (value y)).push (t := .val .uint) (value x)
def machine (x y : Fin 256) : Machine :=
  writeMachine (writeMachine (Seed.machine (wmod 7)) 3 (word y)) 4 (word x)

theorem represented (x y : Fin 256) : StateRepr 1 1 64 F (target x y) Seed.bases (machine x y) :=
  (((Seed.initial (wmod 7)).1.consVal (value y) (word y) (ReprV.uint_of rfl) (by decide)).consVal
    (value x) (word x) (ReprV.uint_of rfl) (by decide))

def source (x y : Fin 256) : Source.EMState E0 [.int .u8,.int .u8] :=
  (.cons (.int x.val (inRange x)) (.cons (.int y.val (inRange y)) .nil),s0)
def si : Bool → Source.Idx [.int .u8,.int .u8] (.int .u8)
  | false => .here | true => .there .here
def ti : Bool → Idx Γ (.val .uint)
  | false => .here | true => .there .here

theorem independent : (si false).toNat ≠ (si true).toNat ∧
    (ti false).toNat ≠ (ti true).toNat := by decide

theorem family (x y : Fin 256) : IntegerLocalFamily .u8 si ti (source x y).1 (target x y).env := by
  constructor
  · intro k
    cases k
    · exact integer_related .u8 x.val (inRange x)
    · exact integer_related .u8 y.val (inRange y)
  · intro k l
    cases k <;> cases l <;> rfl

def application (p : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) (x y : Fin 256) :=
  execution (G0 p) {F0 with checked := checked} fuel (source x y) (target x y) 8
    (by decide) si ti (family x y) false true x.val y.val (inRange x) (inRange y) rfl rfl (represented x y)

def code := (selected (C := Seed.C) 1 F 8 (ti false) (ti true)).code

theorem source_execution (p : Roadmap.Pipeline) (fuel : Nat) (checked : Bool) (x y : Fin 256) :
    (Source.evalE (G0 p) {F0 with checked := false} (fuel+3)
      (.binary .mul (.local (si false)) (.local (si true)))).run (source x y) =
      (.ok (.val (Source.intWrap .u8 ((x.val : Int)*y.val))),source x y) :=
  (application p fuel checked x y).1

/-- The concrete result premise only pins a test's expected literal; compilation,
Source evaluation, execution and physical preservation all come from execution. -/
theorem emitted (p : Roadmap.Pipeline) (x y : Fin 256) (expected : Word)
    (he : ReprV .uint (integerValue .u8 (Source.IntTy.u8.wrap ((x.val : Int)*y.val))
      (Source.IntTy.u8.wrap_mem ((x.val : Int)*y.val))) expected) (tail : List Word) :
    run code {machine x y with stack := tail} = .ok ({machine x y with stack := tail}.push expected) 0 ∧
      StateRepr 1 1 64 F (target x y) Seed.bases ({machine x y with stack := tail}.push expected) := by
  obtain ⟨actual,hr,runs⟩ := (application p 0 false x y).2.2.2.2
  have same := Restored.value_unique hr he
  subst actual
  exact runs tail

theorem zero (p : Roadmap.Pipeline) (tail : List Word) :
    run code {machine 0 255 with stack := tail} = .ok ({machine 0 255 with stack := tail}.push w[0]) 0 :=
  (emitted p 0 255 w[0] (ReprV.uint_of rfl) tail).1

theorem maximum (p : Roadmap.Pipeline) (tail : List Word) :
    run code {machine 255 255 with stack := tail} = .ok ({machine 255 255 with stack := tail}.push w[1]) 0 :=
  (emitted p 255 255 w[1] (ReprV.uint_of rfl) tail).1

theorem wrap (p : Roadmap.Pipeline) (tail : List Word) :
    run code {machine 200 2 with stack := tail} = .ok ({machine 200 2 with stack := tail}.push w[144]) 0 :=
  (emitted p 200 2 w[144] (ReprV.uint_of rfl) tail).1

def observe : Evm.Out → Option (List Nat)
  | .ok m 0 => m.stack.mapM (fun w => match w with | .val n => some n.val | .slot _ => none)
  | _ => none

theorem observed_wrap : observe (run code {machine 200 2 with stack := [w[77],w[88]]}) =
    some [144,77,88] := by
  rw [wrap .legacy]
  rfl

def wrongCode := (selected (C := Seed.C) 1 F 256 (ti false) (ti true)).code

theorem wrong_run (tail : List Word) :
    run wrongCode {machine 200 2 with stack := tail} =
      .ok ({machine 200 2 with stack := tail}.push w[400]) 0 := by
  have eval : (expression (C := Seed.C) 256 (ti false) (ti true)).evalT (target 200 2) =
      .ok (integerValue .u256 400 (by decide)) := by rfl
  obtain ⟨actual,hr,hrun⟩ := value_success_tail
    (selected (C := Seed.C) 1 F 256 (ti false) (ti true)) (represented 200 2) eval tail
  have same : actual = w[400] := Restored.value_unique hr (ReprV.uint_of rfl)
  subst actual
  exact hrun

theorem wrong_cleaning : observe (run wrongCode {machine 200 2 with stack := [w[77],w[88]]}) =
    some [400,77,88] := by
  rw [wrong_run]
  rfl

theorem wrong_cleaning_refused : observe (run wrongCode {machine 200 2 with stack := [w[77],w[88]]}) ≠
    observe (run code {machine 200 2 with stack := [w[77],w[88]]}) := by
  rw [wrong_cleaning,observed_wrap]
  decide

theorem caller_observations : (machine 200 2).stack = [w[77]] ∧
    ([0,1,2,3,4,16,63,128,129].map (machine 200 2).mem) =
      [w[130],w[128],w[7],w[2],w[200],w[20],w[99],w[1],w[0]] := by decide +kernel

/-- The success theorem does not erase the Source horizon boundary. -/
theorem insufficient_horizon (p : Roadmap.Pipeline) :
    (Source.evalE (G0 p) {F0 with checked := false} 2
      (.binary .mul (.local (si false)) (.local (si true)))).run (source 200 2) =
        (.error .timeout,source 200 2) := by
  cases p <;> first | rfl | decide | omega | simp only | with_unfolding_all rfl

theorem corrupted_tail_refused (tail : List Word) :
    run code {machine 200 2 with stack := w[77] :: tail} ≠
      .ok ({machine 200 2 with stack := w[88] :: tail}.push w[144]) 0 := by
  intro h
  rw [wrap .legacy] at h
  have stack := congrArg Machine.stack (Evm.Out.ok.inj h).1
  have wrong : w[77] = w[88] := (List.cons.inj (List.cons.inj stack).2).1
  exact (by decide : w[77] ≠ w[88]) wrong

end Solidity.Backend.PrimitivePackets.UnsignedMul.Controls
