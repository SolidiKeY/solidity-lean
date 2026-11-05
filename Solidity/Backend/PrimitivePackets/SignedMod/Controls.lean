import Solidity.Backend.PrimitivePackets.SignedMod.Selection
import Solidity.Evm.MemoryCompileExamples
import Solidity.Source.Semantics

/-! Inhabited controls use the published populated aliasing heap. The Source
world's fixed functions are irrelevant to pure local evaluation; no crypto or
external-call agreement is inferred. All controls use selected public code. -/
namespace Solidity.Backend.PrimitivePackets.SignedMod.Controls
open Solidity.Evm Solidity.Evm.Memory
namespace HeapFixture
export Solidity.Evm.Memory.CompileExamples (C Γ σ base machine fixture_repr)
end HeapFixture
abbrev C := HeapFixture.C
abbrev Γ : Ctx := .val .int :: .val .int :: HeapFixture.Γ

def fragment : Frag Γ := ((Frag.init HeapFixture.Γ).push (.val .int) .ok).push (.val .int) .ok

def target (x y : Int) (hx : Range x) (hy : Range y) : State C Γ :=
  (HeapFixture.σ.push (t := .val .int) (lower y hy)).push (t := .val .int) (lower x hx)

def machine (x y : Int) (_hx : Range x) (_hy : Range y) : Machine :=
  writeMachine (writeMachine HeapFixture.machine (cell 4) (.val (sword y)))
    (cell 5) (.val (sword x))

theorem initial8 : StateRepr 1 0 8 (Frag.init HeapFixture.Γ)
    HeapFixture.σ HeapFixture.base HeapFixture.machine := by
  have h := HeapFixture.fixture_repr
  refine ⟨h.core, ⟨h.heap.arrays, ?_, h.heap.separated⟩, h.pointers, by decide,
    ⟨h.structs.objects, ?_, h.structs.separated⟩, h.separated, h.refs⟩
  · intro p r
    change 8 ≤ (HeapFixture.base r.id).val
    unfold HeapFixture.base
    split <;> decide
  · intro s r
    change 8 ≤ (HeapFixture.base r.id).val
    unfold HeapFixture.base
    split <;> decide

theorem initial (x y : Int) (hx : Range x) (hy : Range y) :
    StateRepr 1 0 8 fragment (target x y hx hy) HeapFixture.base (machine x y hx hy) :=
  (initial8.consVal (lower y hy) (.val (sword y)) (ReprV.int_word _) (by decide)).consVal
    (lower x hx) (.val (sword x)) (ReprV.int_word _) (by decide)

def E : Source.Env := ⟨[]⟩
def program : Source.Program E where
  body _ := none
  consts _ := none
  inits _ := []
  ctor _ := none
  ctorLocals _ := []
  baseArgs _ := []
  contracts := []
def fixed : Roadmap.Fixed where
  evm := { keccak := fun _ => 0, keccak_lt := fun _ => by decide,
           precompile := fun _ _ => none, precompileGas := fun _ _ => 0 }
  ledger := fun bal _ a => bal a
  regionLen := 1
  rootSlots := 1
def globals (p : Roadmap.Pipeline) : Source.Glob E :=
  ⟨program, p, fixed, fun _ => ⟨0, by decide⟩, fun _ _ => false,
    fun _ => .answer (.success []), ⟨0, by decide⟩⟩
def frame (checked : Bool) : Source.Fr :=
  {this := ⟨1, by decide⟩, sender := ⟨2, by decide⟩, value := ⟨0, by decide⟩,
    static := false, contract := "SignedMod", checked := checked}
def source (x y : Int) (hx : Range x) (hy : Range y) :
    Source.EMState E [.int ty, .int ty] :=
  (.cons (.int x hx) (.cons (.int y hy) .nil), Source.St.init E)

def code : List Evm.Instr := (selected (C := C) 0 fragment .here (.there .here)).code

/-- Exact public-code run for arbitrary inhabited operands and saved tail,
including the min divided by -1 case and negative operands. All non-stack fields survive. -/
theorem target_success (x y : Int) (hx : Range x) (hy : Range y) (nonzero : y ≠ 0)
    (tail : List Word) :
    run code {machine x y hx hy with stack := w[77] :: tail} =
      .ok {machine x y hx hy with stack := .val (sword (x.tmod y)) :: w[77] :: tail} 0 := by
  obtain ⟨w, repr, runs⟩ := selected_success (target x y hx hy) .here (.there .here)
    x y hx hy nonzero rfl rfl 0 1 8 fragment HeapFixture.base (machine x y hx hy)
    (initial x y hx hy) (w[77] :: tail)
  have unique : w = .val (sword (x.tmod y)) :=
    int_repr_unique repr (ReprV.int_word _)
  rw [unique] at runs
  exact runs

theorem target_failure (x : Int) (hx : Range x) (tail : List Word) :
    run code {machine x 0 hx (by decide) with stack := w[77] :: tail} = .revert :=
  selected_zero (target x 0 hx (by decide)) .here (.there .here) x hx (by decide)
    rfl rfl 0 1 8 fragment HeapFixture.base (machine x 0 hx (by decide))
    (initial x 0 hx (by decide)) (w[77] :: tail)

theorem source_success (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat)
    (x y : Int) (hx : Range x) (hy : Range y) (nonzero : y ≠ 0) :
    (Source.evalE (globals p) (frame checked) (fuel + 3)
      (.binary .mod (.local .here) (.local (.there .here)))).run (source x y hx hy) =
      (.ok (.val (.int (x.tmod y) (remainder_range x y hy nonzero))), source x y hx hy) :=
  source_locals_nonzero (globals p) (frame checked) fuel (source x y hx hy)
    .here (.there .here) x y hx hy rfl rfl nonzero

theorem source_failure (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat)
    (x : Int) (hx : Range x) :
    (Source.evalE (globals p) (frame checked) (fuel + 3)
      (.binary .mod (.local .here) (.local (.there .here)))).run (source x 0 hx (by decide)) =
      (.error (.revert (Source.panicData .divZero)), source x 0 hx (by decide)) :=
  source_locals_zero (globals p) (frame checked) fuel (source x 0 hx (by decide))
    .here (.there .here) x hx (by decide) rfl rfl

/-- Numeric zero guard is required: raw SMOD with zero divisor returns zero. -/
theorem raw_zero_differs :
    Backend.Scalar.run [.op .SMOD] [7, 0, 77] = some [0, 77] ∧
    Backend.Scalar.guarded (Backend.Scalar.zeroTest ⟨1, by decide⟩) [.op .SMOD]
      Backend.Scalar.divisionFailure [7, 0, 77] =
      some (.error Backend.Scalar.divisionFailure) := by
  constructor
  · rfl
  · rw [Backend.Scalar.guarded_zero ⟨1, by decide⟩ _ (0 : Backend.Scalar.Word) _ _ rfl]
    rfl

theorem nonempty_tail : ([w[77]] : List Word) ≠ [] := by decide

theorem ordinary (tail : List Word) :
    run code {machine 7 3 (by decide) (by decide) with stack := w[77] :: tail} =
      .ok {machine 7 3 (by decide) (by decide) with stack := w[1] :: w[77] :: tail} 0 :=
  target_success 7 3 (by decide) (by decide) (by decide) tail

theorem negative (tail : List Word) :
    run code {machine (-7) 3 (by decide) (by decide) with stack := w[77] :: tail} =
      .ok {machine (-7) 3 (by decide) (by decide) with stack := .val (sword (-1)) :: w[77] :: tail} 0 :=
  target_success (-7) 3 (by decide) (by decide) (by decide) tail

theorem minimum (tail : List Word) :
    run code {machine (-(Evm.H : Int)) (-1) (by decide) (by decide) with stack := w[77] :: tail} =
      .ok {machine (-(Evm.H : Int)) (-1) (by decide) (by decide) with stack := w[0] :: w[77] :: tail} 0 := by
  simpa only [minimum_remainder_neg_one] using
    target_success (-(Evm.H : Int)) (-1) (by decide) (by decide) (by decide) tail

theorem negative_divisor_run (tail : List Word) :
    run code {machine 7 (-3) (by decide) (by decide) with stack := w[77] :: tail} =
      .ok {machine 7 (-3) (by decide) (by decide) with stack := w[1] :: w[77] :: tail} 0 :=
  target_success 7 (-3) (by decide) (by decide) (by decide) tail

theorem both_negative (tail : List Word) :
    run code {machine (-7) (-3) (by decide) (by decide) with stack := w[77] :: tail} =
      .ok {machine (-7) (-3) (by decide) (by decide) with stack := .val (sword (-1)) :: w[77] :: tail} 0 :=
  target_success (-7) (-3) (by decide) (by decide) (by decide) tail

theorem too_short_horizon (p : Roadmap.Pipeline) (checked : Bool) :
    (Source.evalE (globals p) (frame checked) 0
      (.binary .mod (.local .here) (.local (.there .here)))).run
      (source 7 3 (by decide) (by decide)) =
      (.error .timeout, source 7 3 (by decide) (by decide)) := rfl

theorem horizon_two_timeout (p : Roadmap.Pipeline) (checked : Bool) :
    (Source.evalE (globals p) (frame checked) 2
      (.binary .mod (.local .here) (.local (.there .here)))).run
      (source 7 3 (by decide) (by decide)) =
      (.error .timeout, source 7 3 (by decide) (by decide)) := by
  cases p <;> rfl

theorem corrupted_saved_tail (tail : List Word) :
    run code {machine 7 3 (by decide) (by decide) with stack := w[77] :: tail} ≠
      .ok {machine 7 3 (by decide) (by decide) with stack := w[1] :: w[88] :: tail} 0 := by
  intro wrong
  rw [ordinary] at wrong
  have stacks := congrArg Machine.stack (Evm.Out.ok.inj wrong).1
  have bad : (w[77] : Word) = w[88] := (List.cons.inj (List.cons.inj stacks).2).1
  exact (by decide : (w[77] : Word) ≠ w[88]) bad

theorem short_frame_refused (x y : Int) (hx : Range x) (hy : Range y) :
    ¬ StateRepr 1 0 5 fragment (target x y hx hy) HeapFixture.base (machine x y hx hy) := by
  intro representation
  have bound := representation.locals
  change 6 ≤ 5 at bound
  omega

theorem observed_heap (x y : Int) (hx : Range x) (hy : Range y) :
    [16, 17, 18, 20, 21].map (machine x y hx hy).mem = [w[2], w[7], w[9], w[1], w[4]] := by
  rfl

end Solidity.Backend.PrimitivePackets.SignedMod.Controls
