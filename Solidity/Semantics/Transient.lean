import Solidity.Semantics.Lifetime
import Solidity.Semantics.RunFrame

/-!
# Transient effects composed with the ordinary interpreter

This supplement composes closed ordinary programs with typed transient reads
and writes. Zero-value self-calls share the owning contract's persistent and
transient cells, enter with fresh memory, and restore the caller's memory and
transaction on return. A caught failure restores both stores. Transaction
entry uses `Lifetime.World.enter`; transaction exit discards transient cells.

This is an explicit model-building API, not elaboration of `T transient x`.
It does not change `State`, callback havoc, scoped terms or their taclets.
The ordinary fragments carry the existing `Prog.within` certificate; this
currently restricts them to its heap-neutral fragment. The new effect tree
cannot hide an arbitrary transient-state transformer in an ordinary fragment.
-/

namespace Solidity.Transient

/-- Labels are documentation only; declaration positions identify cells. -/
abbrev Layout := List (Name × PrimTy)

/-- Only value-type cells can be declared, at their actual Solidity types. -/
inductive Slot : Layout → PrimTy → Type where
  | here {n : Name} {p : PrimTy} {L : Layout} : Slot ((n, p) :: L) p
  | there {n : Name} {p q : PrimTy} {L : Layout} (i : Slot L p) :
      Slot ((n, q) :: L) p

/-- One value at each declared type; no raw words, physical slots or casts. -/
def Store : Layout → Type
  | [] => Unit
  | (_, p) :: L => p.Denote × Store L

namespace Store

def empty : (L : Layout) → Store L
  | [] => ()
  | (_, p) :: L => (PrimTy.dflt p, empty L)

def get : {L : Layout} → {p : PrimTy} → Slot L p → Store L → p.Denote
  | _, _, i => Slot.casesOn (motive := fun L p _ => Store L → p.Denote) i
      (fun s => s.1) (fun j s => get j s.2)
  termination_by structural _ _ i => i

def set : {L : Layout} → {p : PrimTy} → Slot L p → p.Denote → Store L → Store L
  | _, _, i => Slot.casesOn (motive := fun L p _ => p.Denote → Store L → Store L) i
      (fun v s => (v, s.2)) (fun j v s => (s.1, set j v s.2))
  termination_by structural _ _ i => i

theorem get_empty : {L : Layout} → {p : PrimTy} → (i : Slot L p) →
    get i (empty L) = PrimTy.dflt p
  | _, _, .here => rfl
  | _, _, .there i => get_empty i

theorem get_set : {L : Layout} → {p : PrimTy} → (i : Slot L p) →
    (v : p.Denote) → (s : Store L) → get i (set i v s) = v
  | _, _, .here, _, _ => rfl
  | _, _, .there i, v, s => get_set i v s.2

end Store

/-- Source mutability and inherited static execution are distinct. -/
structure Context where
  mutability : Mutability := .nonpayable
  static : Bool := false
  deriving Repr

/-- Ordinary state and transient cells have disjoint representations. -/
structure FrameState (C : Contract) (L : Layout) where
  base : State C []
  cells : Store L

namespace FrameState

/-- A zero-value selfCALL does not book the outer payment twice. -/
def enterSelf (s : FrameState C L) : FrameState C L :=
  { base := {
      storage := s.base.storage
      H := []
      heap := Heap.empty
      env := ()
      net := s.base.net
      selfBalance := s.base.selfBalance
      tx := { s.base.tx with
        msgSender := s.base.tx.selfAddress
        msgValue := PrimTy.dflt .uint } }
    cells := s.cells }

/-- Keep the caller's heap, locals and transaction, adopt the child's globals. -/
def resume (caller child : FrameState C L) : FrameState C L :=
  { base := { caller.base with
      storage := child.base.storage
      net := child.base.net
      selfBalance := child.base.selfBalance }
    cells := child.cells }

theorem enterSelf_cells (s : FrameState C L) : s.enterSelf.cells = s.cells := rfl
theorem enterSelf_sender (s : FrameState C L) :
    s.enterSelf.base.tx.msgSender = s.base.tx.selfAddress := rfl
theorem enterSelf_value (s : FrameState C L) :
    s.enterSelf.base.tx.msgValue = PrimTy.dflt .uint := rfl
theorem resume_cells (s t : FrameState C L) : (s.resume t).cells = t.cells := rfl
theorem resume_tx (s t : FrameState C L) : (s.resume t).base.tx = s.base.tx := rfl
theorem resume_heap (s t : FrameState C L) : (s.resume t).base.heap = s.base.heap := rfl

end FrameState

/-- Explicit sequencing of transient effects and existing scoped programs.
Only zero-value calls to this same owning contract are represented here. -/
inductive Program (C : Contract) (L : Layout) : Type → Type 1 where
  | pure {α : Type} (value : α) : Program C L α
  | bind {α β : Type} (body : Program C L α) (next : α → Program C L β) : Program C L β
  | halt {α : Type} (reason : THalt) : Program C L α
  | read {p : PrimTy} (slot : Slot L p) : Program C L p.Denote
  | write {p : PrimTy} (slot : Slot L p) (value : p.Denote) : Program C L Unit
  | ordinary (mutability : Mutability) (body : Prog C [] [])
      (within : Prog.within mutability body = true) : Program C L Unit
  | selfCall {α : Type} (mutability : Mutability) (static : Bool)
      (body : Program C L α) : Program C L α
  | attempt {α : Type} (body : Program C L α) : Program C L (Except THalt α)

namespace Program

variable {C : Contract} {L : Layout} {α β : Type}

instance : Monad (Program C L) where
  pure := Program.pure
  bind := Program.bind

def permits (caller callee : Mutability) : Bool :=
  if caller == .pure then callee == .pure
  else if caller == .view then callee != .nonpayable else true

def catchable : THalt → Bool
  | .revert | .revertWith _ | .panic => true
  | .diverge | .exhausted => false

def calleeContext (ctx : Context) (μ : Mutability) (static : Bool) : Context :=
  { mutability := μ, static := ctx.static || static ||
      (ctx.mutability != .nonpayable) || (μ != .nonpayable) }

/-- The ordinary fragment must satisfy both its source mode and inherited
static execution. The second check uses the existing frame classifier. -/
def ordinaryAllowed (ctx : Context) (μ : Mutability) (body : Prog C [] []) : Bool :=
  permits ctx.mutability μ && (!ctx.static || Prog.within .view body)

/-- All effects are interpreted by this recursor; there is no arbitrary
state-transformer constructor. Failed runs expose no partially changed state. -/
def run : {α : Type} → (body : Program C L α) → Context → FrameState C L → TRes (α × FrameState C L)
  | _, .pure v, _, s => .ok (v, s)
  | _, .bind body next, ctx, s => do
    let (v, s') ← run body ctx s
    run (next v) ctx s'
  | _, .halt e, _, _ => .error e
  | _, .read i, ctx, s => if ctx.mutability == .pure then .error .revert
    else .ok (Store.get i s.cells, s)
  | _, .write i v, ctx, s => if ctx.mutability != .nonpayable || ctx.static then .error .revert
    else .ok ((), { s with cells := Store.set i v s.cells })
  | _, .ordinary μ P _, ctx, s => if ordinaryAllowed ctx μ P then do
    let o ← P.run s.base
    Except.ok ((), { s with base := o.st })
    else .error .revert
  | _, .selfCall μ static body, ctx, s => if permits ctx.mutability μ then do
    let (v, child) ← run body (calleeContext ctx μ static) s.enterSelf
    Except.ok (v, s.resume child)
    else .error .revert
  | _, .attempt body, ctx, s => match run body ctx s with
    | .ok (v, s') => .ok (.ok v, s')
    | .error e => if catchable e then Except.ok (Except.error e, s) else Except.error e
termination_by structural _ body => body

theorem run_ordinary (P : Prog C [] []) (within : Prog.within .nonpayable P = true)
    (s : FrameState C L) :
    run (.ordinary .nonpayable P within) {} s =
      (do let o ← P.run s.base; Except.ok ((), { s with base := o.st })) := rfl

theorem ordinary_success (P : Prog C [] []) (within : Prog.within .nonpayable P = true)
    {s : FrameState C L} {o : Out C s.base.H []} (success : P.run s.base = .ok o) :
    run (.ordinary .nonpayable P within) {} s = .ok ((), { s with base := o.st }) := by
  rw [run_ordinary, success] <;> rfl

/-- Read-only ordinary fragments keep globals by the current upstream frame
theorem, rather than an independently restated effect analysis. -/
theorem ordinary_frame {μ : Mutability} (P : Prog C [] [])
    (within : Prog.within μ P = true) {s : FrameState C L} {o : Out C s.base.H []}
    (success : P.run s.base = .ok o) : TGFrame μ s.base o.st :=
  (Prog.run_frame P within 0 success).1

/-- Reentrant success adopts both child stores without retaining its memory
or replacing the caller's transaction metadata. -/
theorem selfCall_success (body : Program C L α) {ctx : Context} {s child : FrameState C L}
    {μ : Mutability} {static : Bool} {v : α} (allowed : permits ctx.mutability μ = true)
    (success : run body (calleeContext ctx μ static) s.enterSelf = .ok (v, child)) :
    run (.selfCall μ static body) ctx s = .ok (v, s.resume child) := by
  change (if permits ctx.mutability μ then
    (do let (v, child) ← run body (calleeContext ctx μ static) s.enterSelf
        Except.ok (v, s.resume child)) else .error .revert) = _
  rw [allowed, success] <;> rfl

/-- A completed caught failure restores persistent state, heap, transaction
and every transient cell, including writes made by successful descendants. -/
theorem attempt_rollback (body : Program C L α) {ctx : Context} {s : FrameState C L}
    {e : THalt} (failure : run body ctx s = .error e) (caught : catchable e = true) :
    run (.attempt body) ctx s = .ok (.error e, s) := by
  change (match run body ctx s with
    | .ok (v, t) => Except.ok (Except.ok v, t)
    | .error e => if catchable e then Except.ok (Except.error e, s) else Except.error e) = _
  simp only [failure, caught, if_true]

theorem attempt_success (body : Program C L α) {ctx : Context} {s t : FrameState C L}
    {v : α} (success : run body ctx s = .ok (v, t)) :
    run (.attempt body) ctx s = .ok (.ok v, t) := by
  change (match run body ctx s with
    | .ok (v, t) => Except.ok (Except.ok v, t)
    | .error e => if catchable e then Except.ok (Except.error e, s) else Except.error e) = _
  rw [success]

/-- A successful static frame cannot alter transient cells, even through
ordinary fragments, nested calls or caught failures. -/
theorem static_preserves (body : Program C L α) {ctx : Context}
    {s t : FrameState C L} {v : α} (static : ctx.static = true)
    (success : run body ctx s = .ok (v, t)) : t.cells = s.cells := by
  induction body generalizing ctx s t with
  | pure x =>
    change Except.ok (x, s) = Except.ok (v, t) at success
    cases success
    rfl
  | bind body next ih ihNext =>
    change (do let (x, u) ← run body ctx s; run (next x) ctx u) = .ok (v, t) at success
    cases first : run body ctx s with
    | error e => rw [first] at success; cases success
    | ok result =>
      obtain ⟨x, u⟩ := result
      rw [first] at success
      exact (ihNext x static success).trans (ih static first)
  | halt e =>
    change Except.error e = Except.ok (v, t) at success
    cases success
  | read i =>
    change (if ctx.mutability == .pure then Except.error THalt.revert
      else Except.ok (Store.get i s.cells, s)) = .ok (v, t) at success
    split at success
    · cases success
    · cases success; rfl
  | write i value =>
    change (if ctx.mutability != .nonpayable || ctx.static then Except.error THalt.revert
      else Except.ok ((), { s with cells := Store.set i value s.cells })) = .ok (v, t) at success
    simp only [static, Bool.or_true, if_true] at success
    cases success
  | ordinary μ P within =>
    change (if ordinaryAllowed ctx μ P then
      (do let o ← P.run s.base; Except.ok ((), { s with base := o.st }))
      else Except.error THalt.revert) = .ok (v, t) at success
    split at success
    · cases ran : P.run s.base with
      | error e => rw [ran] at success; cases success
      | ok o => rw [ran] at success; cases success; rfl
    · cases success
  | selfCall μ forced body ih =>
    change (if permits ctx.mutability μ then
      (do let (x, child) ← run body (calleeContext ctx μ forced) s.enterSelf
          Except.ok (x, s.resume child)) else Except.error THalt.revert) = .ok (v, t) at success
    split at success
    · cases ran : run body (calleeContext ctx μ forced) s.enterSelf with
      | error e => rw [ran] at success; cases success
      | ok result =>
        obtain ⟨x, child⟩ := result
        rw [ran] at success
        cases success
        exact ih (ctx := calleeContext ctx μ forced) (s := s.enterSelf) (t := child) (v := v) (by change (ctx.static || forced || (ctx.mutability != .nonpayable) || (μ != .nonpayable)) = true; rw [static]; rfl) ran
    · cases success
  | attempt body ih =>
    change (match run body ctx s with
      | .ok (x, u) => Except.ok (Except.ok x, u)
      | .error e => if catchable e then Except.ok (Except.error e, s) else Except.error e) = .ok (v, t) at success
    cases ran : run body ctx s with
    | error e =>
      simp only [ran] at success
      split at success
      · cases success; rfl
      · cases success
    | ok result =>
      obtain ⟨x, u⟩ := result
      rw [ran] at success
      cases success
      exact ih static ran

/-- One top-level transaction. The persistent world cannot contain transient
cells. Each entry starts from defaults, and successful exit drops the store.
Callers still owe the ordinary lifetime interface's address/time/allow checks. -/
def transact (body : Program C L α) (world : Lifetime.World C) (tx : TTx)
    (payable : Bool := false) (ctx : Context := {}) : TRes (α × Lifetime.World C) := do
  if !payable && tx.msgValue.1 != 0 then .error .revert else do
    let σ ← world.enter tx
    let (v, out) ← run body ctx ⟨σ, Store.empty L⟩
    Except.ok (v, Lifetime.World.ofState out.base)

/-- A commit requires actual successful entry and execution, not exhaustion. -/
theorem transact_ok {body : Program C L α} {world final : Lifetime.World C} {tx : TTx}
    {payable : Bool} {ctx : Context} {v : α}
    (success : transact body world tx payable ctx = .ok (v, final)) :
    ∃ σ out, world.enter tx = .ok σ ∧
      run body ctx ⟨σ, Store.empty L⟩ = .ok (v, out) ∧
      Lifetime.World.ofState out.base = final := by
  unfold transact at success
  split at success
  · cases success
  · cases entered : world.enter tx with
    | error e => rw [entered] at success; cases success
    | ok σ =>
      simp only [entered, Bind.bind, Except.bind] at success
      cases ran : run body ctx ⟨σ, Store.empty L⟩ with
      | error e => rw [ran] at success; cases success
      | ok result =>
        obtain ⟨x, out⟩ := result
        rw [ran] at success
        cases success
        exact ⟨σ, out, rfl, ran, rfl⟩

/-- With no transient effects the adapter is the existing lifetime runner,
including its payment guard, entry semantics and all halt outcomes. -/
theorem transact_ordinary {D A : Type} (model : Lifetime.System C D A) (action : A)
    (within : Prog.within .nonpayable (model.call action) = true)
    (world : Lifetime.World C) (tx : TTx) :
    (transact (L := L) (.ordinary .nonpayable (model.call action) within)
      world tx (model.payable action)).map Prod.snd = model.run world action tx := by
  unfold transact Lifetime.System.run
  by_cases guard : (!model.payable action && tx.msgValue.1 != 0) = true
  · simp only [if_pos guard, Except.map]
  · simp only [if_neg guard]
    cases entered : world.enter tx with
    | error e => rfl
    | ok σ =>
      simp only [Bind.bind, Except.bind]
      rw [run_ordinary]
      cases ran : (model.call action).run σ <;> rfl

end Program
end Solidity.Transient
