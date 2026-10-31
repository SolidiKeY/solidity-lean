import Solidity.Backend.InternalFlow.TuplePrograms
import Solidity.Evm.Stmt

/-! Storage aliases over the published represented heap. Plain paths only;
no storage semantics, fragile lifetime predicate or producer is changed. -/
namespace Solidity.Backend.InternalFlow.StorageFrames
open Evm Evm.Memory
variable {C : Contract}

theorem pushDead {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) (R : RefTy)
    (room : b + (Γ.length + 1) ≤ frame) :
    StateRepr L b frame (F.push (.alias R) .dead)
      (σ.push (t := .alias R) none) base m := by
  refine ⟨h.core.pushDead R none, h.heap, ?_, room, h.structs, h.separated, h.refs⟩
  intro T i
  cases i with
  | there j =>
    obtain ⟨ref,hr,hm⟩ := h.pointers j
    refine ⟨ref,hr,?_⟩
    simpa only [cellOf,lvl_there] using hm

theorem pushAlias {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {R : RefTy}
    {r : SRef C (.ref R)} {s : Slot} (path : PathSlot C true r s)
    (room : b + (Γ.length + 1) ≤ frame) :
    StateRepr L b frame (F.push (.alias R) .ok)
      (σ.push (t := .alias R) (some r)) base
      (writeMachine m (cell (b + Γ.length)) (.slot s)) := by
  have hl : b + Γ.length < frame := by omega
  refine ⟨h.core.pushAlias path, h.heap.localWrite _ hl _, ?_, room,
    h.structs.localWrite _ hl _, h.separated, RefFieldsRepr.localWrite h.refs h.structs _ hl _⟩
  intro T i
  cases i with
  | there j =>
    obtain ⟨ref,hr,hm⟩ := h.pointers j
    refine ⟨ref,hr,?_⟩
    change upd m.mem (b + Γ.length) (.slot s) (lvl b (.there j)) = _
    rw [lvl_there, upd_other _ _ (Nat.ne_of_lt (lvl_lt b j))]
    exact hm

theorem setAlias {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {R : RefTy}
    (dst : Idx Γ (.alias R)) {r : SRef C (.ref R)} {s : Slot}
    (path : PathSlot C true r s) :
    StateRepr L b frame (F.set dst .ok) (σ.setLocal dst (some r)) base
      (writeMachine m (cellOf b dst) (.slot s)) := by
  have hl : lvl b dst < frame := Nat.lt_of_lt_of_le (lvl_lt b dst) h.locals
  refine ⟨h.core.setAliasE dst path, h.heap.localWrite _ hl _, ?_, h.locals,
    h.structs.localWrite _ hl _, h.separated, RefFieldsRepr.localWrite h.refs h.structs _ hl _⟩
  intro T i
  have hn : dst.toNat ≠ i.toNat := fun he => by cases Idx.ty_eq dst i he
  obtain ⟨ref,hr,hm⟩ := h.pointers i
  refine ⟨ref,(TEnv.get_set_ne dst i (some r) σ.env hn).trans hr,?_⟩
  change upd m.mem (cellOf b dst) (.slot s) (cellOf b i) = _
  rw [upd_other _ _ (fun he => hn ((lvl_eq_iff b dst i).mp he.symm))]
  exact hm

def declareUnset (b : Nat) {Γ : Ctx} (F : Frag Γ) (R : RefTy) (name : Var) :
    Calls.Statement (C := C) b F (.declStorage R name none) where
  frag := F.push (.alias R) .dead
  code := []
  need := Γ.length + 1
  cost := fun _ => 0
  allocates := false
  zeroCost := fun _ _ => rfl
  sound := by
    intro L frame σ base m h room capacity
    apply ResultRepr.growing
    refine .inl ⟨⟨σ.push (t := .alias R) none, List.prefix_refl _⟩,m,rfl,rfl,
      pushDead h R room,rfl,?_⟩
    intro cursor hb ha
    exact ha

/-- A resolved plain storage path, evaluated by the existing core proof, then
stored in its actual local cell. Heap and allocator cells are framed. -/
def bindPath (b : Nat) {Γ : Ctx} (F : Frag Γ) {R : RefTy}
    (dst : Idx Γ (.alias R)) (q : SPath C Γ (.ref R))
    (free : spathIn F true q = true) : Calls.Statement b F (.rebind dst (.path q)) where
  frag := F.set dst .ok
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
        writeMachine m (cellOf b dst) (.slot s),?_,?_,setAlias h dst hpath,rfl,?_⟩
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

/-- Plain storage declaration with its actual core-evaluated reference. -/
def declarePath (b : Nat) {Γ : Ctx} (F : Frag Γ) {R : RefTy} (name : Var)
    (q : SPath C Γ (.ref R)) (free : spathIn F true q = true) :
    Calls.Statement b F (.declStorage R name (some (.path q))) where
  frag := F.push (.alias R) .ok
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
        writeMachine m (cell (b + Γ.length)) (.slot s),?_,?_,pushAlias h hpath room,rfl,?_⟩
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
  match s with
  | .declStorage R name none => some (declareUnset b F R name)
  | .declStorage _ name (some (.path q)) =>
    if free : spathIn F true q = true then some (declarePath b F name q free) else none
  | .rebind dst (.path q) =>
    if free : spathIn F true q = true then some (bindPath b F dst q free) else none
  | _ => none

end Solidity.Backend.InternalFlow.StorageFrames
