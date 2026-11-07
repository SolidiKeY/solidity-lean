import Solidity.Backend.InternalFlow.RuntimeFrameP1LangV2
import Solidity.Evm.Repr

/-! H68 family 3 (`p1_frame_bridge`), version 2: a guarded revert with data.

A non-degenerate family over the version-2 languages of `P1LangV2`: its
outcome depends on the caller and one of its outcomes carries revert data.

* Source: in a frame with one `bool` local `ok`, the statement
  `if (ok) {} else { revert(0x08c379a0) }` (`guard`): success when `ok`,
  otherwise `revertWith data` with the four bytes `data` (the `Error(string)`
  selector, used here only as a fixed payload). The family is constant in the
  depth (no recursion).
* Target: a hand-written version-2 image (`image cell`), not compiler output:
  `MLOAD cell; JUMPI +5; PUSH word; MSTORE cell; PUSH 4; PUSH cell; REVERT`,
  whose `REVERT` reads the four bytes back from memory.
* Domain (`admitted cell`): the machine's cell `cell` represents the caller's
  `ok` (`ReprV .bool`, as `Sim` lays out a `bool` local), with `cell < W`.
  Nothing else about the caller, machine or start is restricted; the
  environment map is the identity.

`Local` is the per-input frame conclusion: for every admitted input, either
the flag is set, the source class is `success` and the target stops with the
journal unchanged, or it is clear, the source class is `revertWith data` and
the target run is exactly `.revert calls data`. That both classes are
inhabited by admitted inputs is shown separately (`Controls.admitted_true`,
`Controls.admitted_false`, cell `3`). The domain fixes one absolute cell per
context; `L`, `frame`, `base` and `start` do not occur in it. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.P1BridgeV2
open Evm P1LangV2
open Solidity.Roadmap (Event Outcome Prefix Lang Prefixes)
open Solidity.Roadmap.G49Final (BridgeGoal PassCorrect Behaviour)

/-- The frame: one `bool` local. -/
abbrev Γ : Ctx := [.val .bool]

/-- The payload. -/
def data : List UInt8 := [0x08, 0xc3, 0x79, 0xa0]

/-- The payload laid out as a memory word. -/
def dataWord : Fin W := ⟨0x08c379a0 * 2 ^ 224, by unfold W; decide⟩

theorem dataWord_bytes : (wordBytes dataWord).take 4 = data := by decide

/-- `if (ok) {} else { revert(data) }`. -/
def guard (C : Contract) : Stmt C Γ Γ :=
  .ite (.simple (.local .here)) .nil (.cons (.revertData [.bytes data]) .nil)

/-- The family: the same statement at every depth. -/
def source (C : Contract) : Nat → Stmt C Γ Γ := fun _ => guard C

/-- The caller's flag. -/
def flag {C : Contract} (σ : State C Γ) : Bool := TEnv.get .here σ.env

/-- The emitted image for a flag held in memory cell `cell`. -/
def image (cell : Nat) : List InstrV2 :=
  [.base (.mload cell), .base (.jumpi 5),
   .base (.push (.val dataWord)), .base (.mstore cell),
   .base (.push (.val ⟨4, by unfold W; decide⟩)), .base (.push (.val (wmod cell))), .revertData]

/-- The admitted inputs: cell `cell` represents the caller's flag. -/
def admitted (C : Contract) (cell : Nat) : Admission C Γ := fun e =>
  cell < W ∧ ReprV .bool (TEnv.get .here e.caller.env) (e.machine.base.mem cell)

/-! ## Source runs -/

theorem source_true {C : Contract} (σ : State C Γ) (h : flag σ = true) :
    sourcePrefix ((guard C).run σ) = ⟨[], some (.success [])⟩ := by
  simp only [flag] at h
  show sourcePrefix (TRun.ite _ _ _ _ _ σ) = _
  simp only [TRun.ite, Val.evalT, Simple.evalT, h, boolT, bind, Except.bind, pure, Except.pure,
    if_true]
  rfl

theorem source_false {C : Contract} (σ : State C Γ) (h : flag σ = false) :
    sourcePrefix ((guard C).run σ) = ⟨[], some (.revert data)⟩ := by
  simp only [flag] at h
  show sourcePrefix (TRun.ite _ _ _ _ _ σ) = _
  simp only [TRun.ite, Val.evalT, Simple.evalT, h, boolT, bind, Except.bind, pure, Except.pure,
    Bool.false_eq_true, if_false]
  rfl

theorem source_class_false {C : Contract} (σ : State C Γ) (h : flag σ = false) :
    sourceClass ((guard C).run σ) = .revertWith data := by
  simp only [flag] at h
  show sourceClass (TRun.ite _ _ _ _ _ σ) = _
  simp only [TRun.ite, Val.evalT, Simple.evalT, h, boolT, bind, Except.bind, pure, Except.pure,
    Bool.false_eq_true, if_false]
  rfl

theorem source_class_true {C : Contract} (σ : State C Γ) (h : flag σ = true) :
    sourceClass ((guard C).run σ) = .success := by
  simp only [flag] at h
  show sourceClass (TRun.ite _ _ _ _ _ σ) = _
  simp only [TRun.ite, Val.evalT, Simple.evalT, h, boolT, bind, Except.bind, pure, Except.pure,
    if_true]
  rfl

/-! ## Target runs -/

theorem image_true (cell : Nat) (m : MachineV2) (h : m.base.mem cell = .val (bword true)) :
    ∃ m', runV2 (image cell) m = .ok m' 0 ∧ m'.calls = m.calls := by
  refine ⟨_, ?_, rfl⟩
  simp only [runV2, image, execV2_cons_zero, execV2_cons_succ, InstrV2.step, Instr.step,
    Machine.next, OutV2.ofOut, OutV2.ok_bind, MachineV2.withBase_base, h]
  rfl

theorem image_false (cell : Nat) (hcell : cell < W) (m : MachineV2)
    (h : m.base.mem cell = .val (bword false)) :
    runV2 (image cell) m = .revert m.calls data := by
  have hr : readBytes (upd m.base.mem cell (.val dataWord)) cell 4 = some data := by
    simp only [readBytes, cellsOf, readCells, upd_same, Option.map_some]
    rw [List.append_nil, dataWord_bytes]
  have hw : (wmod cell).1 = cell := by simp only [wmod_def, Nat.mod_eq_of_lt hcell]
  simp only [runV2, image, execV2_cons_zero, InstrV2.step, Instr.step,
    Machine.next, OutV2.ofOut, OutV2.ok_bind, MachineV2.withBase_base, h]
  simp only [bword, Bool.false_eq_true, if_false, if_true, execV2_cons_zero, InstrV2.step,
    Instr.step, Machine.next, OutV2.ofOut, OutV2.ok_bind, MachineV2.withBase_base, hw, hr,
    OutV2.revert_bind]
  simp only [upd_same, MachineV2.withBase, hw, hr]

theorem target_true {C : Contract} {cell : Nat} (e : Input C Γ) (h : admitted C cell e)
    (hf : flag e.caller = true) : targetSem (image cell) e = ⟨[], some (.success [])⟩ := by
  have hm : e.machine.base.mem cell = .val (bword true) := by
    have := h.2; simp only [ReprV] at this; rw [this]; simp only [flag] at hf; rw [hf]
  obtain ⟨m', run, calls⟩ := image_true cell e.machine hm
  simp only [targetSem, run, targetPrefix, eventsAfter, calls, List.drop_length, List.filter_nil, List.map_nil,
    List.flatten_nil]

theorem target_false {C : Contract} {cell : Nat} (e : Input C Γ) (h : admitted C cell e)
    (hf : flag e.caller = false) : targetSem (image cell) e = ⟨[], some (.revert data)⟩ := by
  have hm : e.machine.base.mem cell = .val (bword false) := by
    have := h.2; simp only [ReprV] at this; rw [this]; simp only [flag] at hf; rw [hf]
  simp only [targetSem, image_false cell h.1 e.machine hm, targetPrefix, eventsAfter, List.filter_nil,
    List.drop_length, List.map_nil, List.flatten_nil]

/-- **Frame agreement**: on every admitted input both sides show the same
prefix. -/
theorem agree {C : Contract} {cell : Nat} (e : Input C Γ) (h : admitted C cell e) :
    targetSem (image cell) e = sourcePrefix ((guard C).run e.caller) := by
  cases hf : flag e.caller
  · rw [target_false e h hf, source_false _ hf]
  · rw [target_true e h hf, source_true _ hf]

/-! ## Languages and the bridge -/

theorem consistent {C : Contract} (e : Input C Γ) : Prefixes.Consistent (sourceSem (source C) e) :=
  fun _ _ _ => Prefix.Le.refl _

/-- The canonical version-2 source language of the family. -/
def A (C : Contract) (cell : Nat) : Lang Event Outcome :=
  sourceLang (source C) (admitted C cell) consistent

/-- The canonical version-2 target language of the image. -/
noncomputable def B (C : Contract) (cell : Nat) : Lang Event Outcome :=
  targetLang (C := C) (image cell) (admitted C cell)

/-- The entire local frame conclusion. -/
def Local (C : Contract) (cell : Nat) : Prop :=
  (∀ e : Input C Γ, admitted C cell e →
    (flag e.caller = true ∧ sourceClass ((guard C).run e.caller) = .success ∧
        ∃ m', runV2 (image cell) e.machine = .ok m' 0 ∧ m'.calls = e.machine.calls) ∨
    (flag e.caller = false ∧ sourceClass ((guard C).run e.caller) = .revertWith data ∧
        runV2 (image cell) e.machine = .revert e.machine.calls data))

theorem local_holds (C : Contract) (cell : Nat) : Local C cell := by
  intro e h
  cases hf : flag e.caller
  · have hm : e.machine.base.mem cell = .val (bword false) := by
      have := h.2; simp only [ReprV] at this; rw [this]; simp only [flag] at hf; rw [hf]
    exact .inr ⟨rfl, source_class_false _ hf, image_false cell h.1 e.machine hm⟩
  · have hm : e.machine.base.mem cell = .val (bword true) := by
      have := h.2; simp only [ReprV] at this; rw [this]; simp only [flag] at hf; rw [hf]
    exact .inl ⟨rfl, source_class_true _ hf, image_true cell e.machine hm⟩

/-- The full refinement between the canonical version-2 languages. -/
noncomputable def pass (C : Contract) (cell : Nat) :
    PassCorrect (Behaviour.ofLang (A C cell) ()) (Behaviour.ofLang (B C cell) ()) where
  envAbs := id
  envSound := fun _ h => h
  envOnto := fun e h => ⟨e, h, rfl⟩
  need := fun _ _ => ()
  need_ok e r h _ := by
    refine ⟨⟨trivial, trivial, trivial⟩, ?_⟩
    change (sourcePrefix ((guard C).run e.caller)).Le (targetSem (image cell) e)
    rw [agree e h]
    exact Prefix.Le.refl _
  back e _ h _ _ := by
    refine ⟨(0 : Nat), trivial, trivial, ?_⟩
    change (targetSem (image cell) e).Le (sourcePrefix ((guard C).run e.caller))
    rw [agree e h]
    exact Prefix.Le.refl _

/-- **`p1_frame_bridge`, version 2**, for the guarded revert-with-data
family. -/
noncomputable def p1_frame_bridge (C : Contract) (cell : Nat) :
    BridgeGoal (A C cell) (B C cell) () () id (fun _ _ => ()) (Local C cell) :=
  ⟨pass C cell, rfl, rfl, local_holds C cell⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.P1BridgeV2
