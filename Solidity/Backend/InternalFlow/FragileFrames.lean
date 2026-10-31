import Solidity.Backend.InternalFlow.StorageFrames

/-! Fragile storage aliases from actual reached path/liveness evidence.
The existing plain selector and storeDrop/dropFragile semantics stay unchanged. -/
namespace Solidity.Backend.InternalFlow.FragileFrames
open Evm Evm.Memory
variable {C : Contract}

theorem pushFragile {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {R : RefTy}
    {r : SRef C (.ref R)} {s : Slot} (path : PathSlot C false r s)
    (live : ∃ sv, σ.storage.findLive r = some sv)
    (room : b + (Γ.length + 1) ≤ frame) :
    StateRepr L b frame (F.push (.alias R) .fragile)
      (σ.push (t := .alias R) (some r)) base
      (writeMachine m (cell (b + Γ.length)) (.slot s)) := by
  have hl : b + Γ.length < frame := by omega
  refine ⟨h.core.pushFragile path live, h.heap.localWrite _ hl _, ?_, room,
    h.structs.localWrite _ hl _, h.separated, RefFieldsRepr.localWrite h.refs h.structs _ hl _⟩
  intro T i
  cases i with
  | there j =>
    obtain ⟨ref,hr,hm⟩ := h.pointers j
    refine ⟨ref,hr,?_⟩
    change upd m.mem (b + Γ.length) (.slot s) (lvl b (.there j)) = _
    rw [lvl_there, upd_other _ _ (Nat.ne_of_lt (lvl_lt b j))]
    exact hm

theorem setFragile {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {R : RefTy}
    (dst : Idx Γ (.alias R)) {r : SRef C (.ref R)} {s : Slot}
    (path : PathSlot C false r s)
    (live : ∃ sv, σ.storage.findLive r = some sv) :
    StateRepr L b frame (F.set dst .fragile) (σ.setLocal dst (some r)) base
      (writeMachine m (cellOf b dst) (.slot s)) := by
  have hl : lvl b dst < frame := Nat.lt_of_lt_of_le (lvl_lt b dst) h.locals
  refine ⟨h.core.setFragileE dst path live, h.heap.localWrite _ hl _, ?_, h.locals,
    h.structs.localWrite _ hl _, h.separated, RefFieldsRepr.localWrite h.refs h.structs _ hl _⟩
  intro T i
  have hn : dst.toNat ≠ i.toNat := fun he => by cases Idx.ty_eq dst i he
  obtain ⟨ref,hr,hm⟩ := h.pointers i
  refine ⟨ref,(TEnv.get_set_ne dst i (some r) σ.env hn).trans hr,?_⟩
  change upd m.mem (cellOf b dst) (.slot s) (cellOf b i) = _
  rw [upd_other _ _ (fun he => hn ((lvl_eq_iff b dst i).mp he.symm))]
  exact hm

def bindPathFragile (b : Nat) {Γ : Ctx} (F : Frag Γ) {R : RefTy}
    (dst : Idx Γ (.alias R)) (q : SPath C Γ (.ref R))
    (free : spathIn F false q = true) : Calls.Statement b F (.rebind dst (.path q)) where
  frag := F.set dst .fragile
  code := compileSPath b q ++ [.mstore (cellOf b dst)]
  need := Γ.length
  cost := fun _ => 0
  allocates := false
  zeroCost := fun _ _ => rfl
  sound := by
    intro L frame σ base m h room capacity
    apply ResultRepr.growing
    rcases spath_sim q h.core free with ⟨r,s,sv,hr,hlive,hpath,hrepr,hcode⟩ | ⟨hr,hcode⟩
    · refine .inl ⟨⟨σ.setLocal dst (some r), List.prefix_refl _⟩,
        writeMachine m (cellOf b dst) (.slot s),?_,?_,setFragile h dst hpath ⟨sv,hlive⟩,rfl,?_⟩
      · simp only [Stmt.run, Stmt.runR, TRun.rebind, ARhs.evalT, hr, bind, Except.bind,
          pure, Except.pure]
        rfl
      · rw [run_append_ok hcode]
        rfl
      · intro cursor hb ha
        exact ha.localWrite _ (Nat.lt_of_lt_of_le hb (le_lvl b dst))
          (Nat.lt_of_lt_of_le (lvl_lt b dst) h.locals) _
    · refine .inr ⟨?_,run_append_revert hcode⟩
      simp only [Stmt.run, Stmt.runR, TRun.rebind, ARhs.evalT, hr, bind, Except.bind]

/-- Fragile storage declaration with its actual core-evaluated live reference. -/
def declarePathFragile (b : Nat) {Γ : Ctx} (F : Frag Γ) {R : RefTy} (name : Var)
    (q : SPath C Γ (.ref R)) (free : spathIn F false q = true) :
    Calls.Statement b F (.declStorage R name (some (.path q))) where
  frag := F.push (.alias R) .fragile
  code := compileSPath b q ++ [.mstore (cell (b + Γ.length))]
  need := Γ.length + 1
  cost := fun _ => 0
  allocates := false
  zeroCost := fun _ _ => rfl
  sound := by
    intro L frame σ base m h room capacity
    apply ResultRepr.growing
    rcases spath_sim q h.core free with ⟨r,s,sv,hr,hlive,hpath,hrepr,hcode⟩ | ⟨hr,hcode⟩
    · refine .inl ⟨⟨σ.push (t := .alias R) (some r), List.prefix_refl _⟩,
        writeMachine m (cell (b + Γ.length)) (.slot s),?_,?_,pushFragile h hpath ⟨sv,hlive⟩ room,rfl,?_⟩
      · simp only [Stmt.run, Stmt.runR, TRun.declStorage, ARhs.evalT, hr, bind, Except.bind,
          pure, Except.pure]
        rfl
      · rw [run_append_ok hcode]
        rfl
      · intro cursor hb ha
        exact ha.localWrite _ (by dsimp [cell]; omega) (by dsimp [cell]; omega) _
    · refine .inr ⟨?_,run_append_revert hcode⟩
      simp only [Stmt.run, Stmt.runR, TRun.declStorage, ARhs.evalT, hr, bind, Except.bind]

def statement (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (s : Stmt C Γ Δ) :
    Option (Calls.Statement b F s) :=
  match StorageFrames.statement b F s with
  | some out => some out
  | none => match s with
    | .declStorage _ name (some (.path q)) =>
      if accepted : spathIn F false q = true then some (declarePathFragile b F name q accepted) else none
    | .rebind dst (.path q) =>
      if accepted : spathIn F false q = true then some (bindPathFragile b F dst q accepted) else none
    | _ => none

end Solidity.Backend.InternalFlow.FragileFrames
