import Solidity.Semantics.Transient
import Solidity.Semantics.CallbackFrame

/-!
# A read-only body commits nothing (S3.1, view)

`docs/feature-work/semantics-extensions.md`, S3.1: a body a `view` (or
`pure`) function may run leaves the storage, the transient storage and the
balances as they were, in every outcome.

"A body a `view` function may run" is `Prog.within .view` (`Calculus/Blocks.lean`),
the classifier solc's mutability check corresponds to on the intrinsic
syntax: no storage write, no `delete`, no push or pop, no payment, no
`try` (its callee may write), every callee within `view` too.  Every
`Prog C Γ Γ'` is well typed by construction, so the theorems below carry no
typing hypothesis.

What a run commits is `committed` (the `Globals` of the state it ends in, or
the entry's on a halt, which rolls back).  Transient storage is not a
separate component here: a contract's transient roots are roots of its one
typed `Storage` (`Storage.RegionRoot`, `Semantics/Storage.lean`), so "the
storage is kept" covers both regions.  The explicit transient layer of
`Semantics/Transient.lean` (`Transient.Program`, typed transient cells beside
an ordinary state) gets its own theorem, `Program.readOnly_preserves`.

The proofs reuse the frame theorems already in the tree: `Prog.run_frame`
(`Semantics/RunFrame.lean`) for the plain run and `ExecP.frame`
(`Semantics/CallbackFrame.lean`) for the run with callbacks.
-/

namespace Solidity.Theory.Mutability

open Solidity

variable {C : Contract}

/-- What a transaction commits of a state: the typed storage (persistent and
transient roots), the ledger and the contract's own balance. -/
structure Globals (C : Contract) where
  storage : Storage C
  net : Ledger
  selfBalance : PrimTy.uint.Denote

/-- The committed part of `σ`. -/
def globals {Γ : Ctx} (σ : State C Γ) : Globals C := ⟨σ.storage, σ.net, σ.selfBalance⟩

/-- **What a run from `σ` commits**: the end state's globals, or, on any halt
(revert, panic, divergence, exhaustion), `σ`'s, since a halt rolls back. -/
def committed {Γ Γ' : Ctx} (σ : State C Γ) : TRes (Out C σ.H Γ') → Globals C
  | .ok o => globals o.st
  | .error _ => globals σ

/-- Read-only mutabilities: `pure` and `view`. -/
theorem readOnly_view : (Mutability.view) ≠ .nonpayable := by decide
theorem readOnly_pure : (Mutability.pure) ≠ .nonpayable := by decide

/-- A frame of a read-only mutability keeps the globals. -/
theorem frame_globals {μ : Mutability} {Γ Δ : Ctx} {σ : State C Γ} {τ : State C Δ}
    (h : TGFrame μ σ τ) (hμ : μ ≠ .nonpayable) : globals τ = globals σ := by
  have hk := h.keeps hμ
  have hb := h.selfBalance hμ
  simp only [globals, hk.1, hk.2, hb]

/-- **A read-only body leaves the globals in every outcome.**  For instance
`function get() view returns (uint) { return x + 1; }`: whatever `x` holds,
whether the addition overflows (a panic) or not, the run commits the entry's
storage, ledger and balance. -/
theorem Prog.committed_readOnly {μ : Mutability} {Γ Γ' : Ctx} (P : Prog C Γ Γ')
    (hw : Prog.within μ P = true) (hμ : μ ≠ .nonpayable) (σ : State C Γ) :
    committed σ (Prog.run σ P) = globals σ := by
  cases h : Prog.run σ P with
  | error e => rfl
  | ok o => exact frame_globals (Prog.run_frame P hw 0 h).1 hμ

/-- **S3.1 (view)**: a `view` body keeps storage, transient storage and
balances in every outcome (`uint x; function get() view returns (uint) {
return x; }`). -/
theorem Prog.committed_view {Γ Γ' : Ctx} (P : Prog C Γ Γ') (hw : Prog.within .view P = true)
    (σ : State C Γ) : committed σ (Prog.run σ P) = globals σ :=
  Prog.committed_readOnly P hw readOnly_view σ

/-- A successful read-only run, field by field: the storage (both regions), the
ledger and the balance are the entry's. -/
theorem Prog.run_readOnly {μ : Mutability} {Γ Γ' : Ctx} {P : Prog C Γ Γ'}
    (hw : Prog.within μ P = true) (hμ : μ ≠ .nonpayable) {σ : State C Γ} {o : Out C σ.H Γ'}
    (h : Prog.run σ P = .ok o) :
    o.st.storage = σ.storage ∧ o.st.net = σ.net ∧ o.st.selfBalance = σ.selfBalance := by
  have hg := (Prog.run_frame P hw 0 h).1
  exact ⟨(hg.keeps hμ).1, (hg.keeps hμ).2, hg.selfBalance hμ⟩

/-- What a callback run commits: the end state's globals on success; on a
halt or a violated invariant, the entry's. -/
def committedC {Γ Γ' : Ctx} (σ : State C Γ) : COut C σ.H Γ' → Globals C
  | .ok o => globals o.st
  | .halt _ | .violated => globals σ

/-- **S3.1 (view), with callbacks**: under any callback strategy `J` a
read-only body's run commits the entry's globals (a `view` body makes no
call that may call back: `try` and payments are outside `view`). -/
theorem ExecP.committed_readOnly {J : StateInv C} {μ : Mutability} {Γ Γ' : Ctx}
    {σ : State C Γ} {P : Prog C Γ Γ'} {o : COut C σ.H Γ'} (h : ExecP J σ P o)
    (hw : Prog.within μ P = true) (hμ : μ ≠ .nonpayable) : committedC σ o = globals σ := by
  cases o with
  | ok o' => exact frame_globals (ExecP.frame h hw 0 o' rfl).1 hμ
  | halt e => rfl
  | violated => rfl

/-! ## The explicit transient layer -/

namespace Transient

open Solidity.Transient

/-- Only a `nonpayable` caller may call a `nonpayable` callee. -/
theorem permits_readOnly {m μ : Mutability} (h : Program.permits m μ = true)
    (hm : m ≠ .nonpayable) : μ ≠ .nonpayable := by
  cases m <;> cases μ <;> simp only [Program.permits] at h <;> first
    | exact absurd rfl hm | decide | exact absurd h (by decide)

/-- **A read-only frame of the transient layer keeps both stores.**  In a
`view` context (`Context.mutability` `pure` or `view`), a successful run of
any effect tree (transient reads and writes, ordinary fragments, nested
self-calls, caught failures) ends with the entry's transient cells and the
entry's persistent globals: `function peek() view returns (uint) { return
count; }` over `uint transient count`. -/
theorem Program.readOnly_preserves {L : Layout} {α : Type} (body : Program C L α)
    {ctx : Context} {s t : FrameState C L} {v : α} (hμ : ctx.mutability ≠ .nonpayable)
    (success : Program.run body ctx s = .ok (v, t)) :
    t.cells = s.cells ∧ globals t.base = globals s.base := by
  induction body generalizing ctx s t with
  | pure x =>
    change Except.ok (x, s) = Except.ok (v, t) at success
    cases success
    exact ⟨rfl, rfl⟩
  | bind body next ih ihNext =>
    change (do let (x, u) ← Program.run body ctx s; Program.run (next x) ctx u) = .ok (v, t)
      at success
    cases first : Program.run body ctx s with
    | error e => rw [first] at success; cases success
    | ok result =>
      obtain ⟨x, u⟩ := result
      rw [first] at success
      obtain ⟨h₁, h₂⟩ := ih hμ first
      obtain ⟨h₃, h₄⟩ := ihNext x hμ success
      exact ⟨h₃.trans h₁, h₄.trans h₂⟩
  | halt e =>
    change Except.error e = Except.ok (v, t) at success
    cases success
  | read i =>
    change (if ctx.mutability == .pure then Except.error THalt.revert
      else Except.ok (Store.get i s.cells, s)) = .ok (v, t) at success
    split at success
    · cases success
    · cases success; exact ⟨rfl, rfl⟩
  | write i value =>
    change (if ctx.mutability != .nonpayable || ctx.static then Except.error THalt.revert
      else Except.ok ((), { s with cells := Store.set i value s.cells })) = .ok (v, t) at success
    have hne : (ctx.mutability != .nonpayable) = true := by
      simpa only [bne_iff_ne, ne_eq] using hμ
    simp only [hne, Bool.true_or, if_true] at success
    cases success
  | ordinary μ P within =>
    change (if Program.ordinaryAllowed ctx μ P then
      (do let o ← P.run s.base; Except.ok ((), { s with base := o.st }))
      else Except.error THalt.revert) = .ok (v, t) at success
    split at success
    · rename_i allowed
      have hp : Program.permits ctx.mutability μ = true := by
        simp only [Program.ordinaryAllowed, Bool.and_eq_true] at allowed
        exact allowed.1
      cases ran : P.run s.base with
      | error e => rw [ran] at success; cases success
      | ok o =>
        rw [ran] at success
        cases success
        exact ⟨rfl, frame_globals (Prog.run_frame P within 0 ran).1 (permits_readOnly hp hμ)⟩
    · cases success
  | selfCall μ forced body ih =>
    change (if Program.permits ctx.mutability μ then
      (do let (x, child) ← Program.run body (Program.calleeContext ctx μ forced) s.enterSelf
          Except.ok (x, s.resume child)) else Except.error THalt.revert) = .ok (v, t) at success
    split at success
    · rename_i hp
      cases ran : Program.run body (Program.calleeContext ctx μ forced) s.enterSelf with
      | error e => rw [ran] at success; cases success
      | ok result =>
        obtain ⟨x, child⟩ := result
        rw [ran] at success
        cases success
        obtain ⟨h₁, h₂⟩ := ih (ctx := Program.calleeContext ctx μ forced) (s := s.enterSelf)
          (t := child) (v := v) (permits_readOnly hp hμ) ran
        refine ⟨h₁, ?_⟩
        have e : globals (s.resume child).base = globals child.base := rfl
        rw [e, h₂]
        rfl
    · cases success
  | attempt body ih =>
    change (match Program.run body ctx s with
      | .ok (x, u) => Except.ok (Except.ok x, u)
      | .error e => if Program.catchable e then Except.ok (Except.error e, s)
        else Except.error e) = .ok (v, t) at success
    cases ran : Program.run body ctx s with
    | error e =>
      simp only [ran] at success
      split at success
      · cases success; exact ⟨rfl, rfl⟩
      · cases success
    | ok result =>
      obtain ⟨x, u⟩ := result
      rw [ran] at success
      cases success
      exact ih hμ ran

/-- A transient write in a read-only context reverts, whatever the cell and
value (`function f() view { count = 1; }` is rejected at run time here as
solc rejects it statically). -/
theorem Program.write_readOnly {L : Layout} {p : PrimTy} (i : Slot L p) (value : p.Denote)
    {ctx : Context} (hμ : ctx.mutability ≠ .nonpayable) (s : FrameState C L) :
    Program.run (Program.write i value) ctx s = .error .revert := by
  change (if ctx.mutability != .nonpayable || ctx.static then Except.error THalt.revert
    else Except.ok ((), { s with cells := Store.set i value s.cells })) = _
  have hne : (ctx.mutability != .nonpayable) = true := by
    simpa only [bne_iff_ne, ne_eq] using hμ
  simp only [hne, Bool.true_or, if_true]

/-- A transient write in a static context reverts. -/
theorem Program.write_static {L : Layout} {p : PrimTy} (i : Slot L p) (value : p.Denote)
    {ctx : Context} (hs : ctx.static = true) (s : FrameState C L) :
    Program.run (Program.write i value) ctx s = .error .revert := by
  change (if ctx.mutability != .nonpayable || ctx.static then Except.error THalt.revert
    else Except.ok ((), { s with cells := Store.set i value s.cells })) = _
  simp only [hs, Bool.or_true, if_true]

/-- A transient read in a `pure` context reverts. -/
theorem Program.read_pure {L : Layout} {p : PrimTy} (i : Slot L p) {ctx : Context}
    (hμ : ctx.mutability = .pure) (s : FrameState C L) :
    Program.run (Program.read i) ctx s = .error .revert := by
  change (if ctx.mutability == .pure then Except.error THalt.revert
    else Except.ok (Store.get i s.cells, s)) = _
  simp only [hμ, BEq.rfl, if_true]

/-- A read-only context cannot call a `nonpayable` callee. -/
theorem Program.selfCall_nonpayable_readOnly {L : Layout} {α : Type} (body : Program C L α)
    (forced : Bool) {ctx : Context} (hμ : ctx.mutability ≠ .nonpayable) (s : FrameState C L) :
    Program.run (Program.selfCall .nonpayable forced body) ctx s = .error .revert := by
  change (if Program.permits ctx.mutability .nonpayable then
    (do let (x, child) ← Program.run body (Program.calleeContext ctx .nonpayable forced)
          s.enterSelf
        Except.ok (x, s.resume child)) else Except.error THalt.revert) = _
  have hp : Program.permits ctx.mutability .nonpayable = false := by
    cases h : ctx.mutability with
    | nonpayable => exact absurd h hμ
    | pure => rfl
    | view => rfl
  rw [hp]
  rfl

end Transient

end Solidity.Theory.Mutability
