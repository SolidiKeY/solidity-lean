import Solidity.Source.State

/-!
# World, transactions and frames (S04.03)

The state of the compiled system's own instances around an execution,
independently of the EVM:

- `Account D L`: an instance's balance, nonce, code (the contract's
  position in the compilation input, as G01's `Event.create` names it) and
  storage over its layout `L`;
- `World D L`: the instances by address.  External accounts are not here:
  their balances are G01's ledger over the session environment
  (`SessionEnv.balance`, `Fixed.ledger`) and their code `SessionEnv.hasCode`,
  moved only by events, so the two never disagree;
- `Transient D T`: each instance's transient storage (EIP-1153), over its
  own layout, cleared when a transaction ends (`endTx`);
- `TxConfig`: a transaction's configuration, G01's `Request`, with
  `tx.origin` its sender;
- `CallFrame`: one call — `this`, the caller, the value, the input, the
  static flag — and its journal mark.

**Journal and rollback.**  Every state change is an `Op` (an update of one
instance's account, or of its transient storage), and `ExecState.apply`
records the old account or transient storage in the journal before
changing it, as the EVM's journal does.  Entering a call marks the
journal's length (`ExecState.enter`); a revert undoes the journal back to
the mark (`CallFrame.rollback`), a success keeps it (`commit`).  The
headline is `rollback_run`: after *any* sequence of operations since the
entry, the rollback is the state at the entry, world, transient storage and
journal.  Nested calls follow (`rollback_inner`: an inner revert keeps the
outer call's earlier operations; `rollback_outer_after_commit`: a committed
inner call is still undone by the outer revert).  Value transfers between
instances are two balance updates (`transfer`), refused without change
when unaffordable or overflowing (`transfer_none_iff`).

Nothing here reads the compiler or the intrinsic semantics.
-/

namespace Solidity.Source

open Solidity.Roadmap (Address Word Bytes Request)

variable {D : Layout}

/-- An instance's account. -/
structure Account (D : Layout) (L : SPath → STy) where
  balance : Word
  nonce : Nat
  /-- The contract the instance runs, by its position in the compilation
  input. -/
  code : Option Nat
  storage : Storage D L

/-- An account with nothing. -/
def Account.empty (L : SPath → STy) : Account D L := ⟨⟨0, by decide⟩, 0, none, Storage.empty⟩

/-- The instances, each over its storage layout. -/
structure World (D : Layout) (L : Address → SPath → STy) where
  accounts : (a : Address) → Account D (L a)

/-- Transient storage, per instance, over its transient layout. -/
structure Transient (D : Layout) (T : Address → SPath → STy) where
  cells : (a : Address) → Storage D (T a)

/-- Cleared transient storage. -/
def Transient.empty {T : Address → SPath → STy} : Transient D T := ⟨fun _ => Storage.empty⟩

variable {L T : Address → SPath → STy}

/-- One account replaced. -/
def World.set (w : World D L) (a : Address) (x : Account D (L a)) : World D L :=
  ⟨fun b => if h : b = a then h ▸ x else w.accounts b⟩

/-- One transient storage replaced. -/
def Transient.set (t : Transient D T) (a : Address) (x : Storage D (T a)) : Transient D T :=
  ⟨fun b => if h : b = a then h ▸ x else t.cells b⟩

theorem World.set_get (w : World D L) (a : Address) (x : Account D (L a)) :
    (w.set a x).accounts a = x := by
  simp only [World.set, dif_pos]

theorem World.set_other (w : World D L) {a b : Address} (h : b ≠ a) (x : Account D (L a)) :
    (w.set a x).accounts b = w.accounts b := by
  simp only [World.set, h, dif_neg, not_false_eq_true]

/-- Restoring the old account undoes a replacement. -/
theorem World.set_restore (w : World D L) (a : Address) (x : Account D (L a)) :
    (w.set a x).set a (w.accounts a) = w := by
  cases w with
  | mk f =>
    simp only [World.set, World.mk.injEq]
    funext b
    by_cases h : b = a
    · subst h; simp only [dif_pos]
    · simp only [h, dif_neg, not_false_eq_true]

theorem Transient.set_restore (t : Transient D T) (a : Address) (x : Storage D (T a)) :
    (t.set a x).set a (t.cells a) = t := by
  cases t with
  | mk f =>
    simp only [Transient.set, Transient.mk.injEq]
    funext b
    by_cases h : b = a
    · subst h; simp only [dif_pos]
    · simp only [h, dif_neg, not_false_eq_true]

/-- A journal entry: what an operation overwrote. -/
inductive Entry (D : Layout) (L T : Address → SPath → STy) where
  | account (a : Address) (old : Account D (L a))
  | transient (a : Address) (old : Storage D (T a))

/-- The state an execution changes, with its journal (newest first). -/
structure ExecState (D : Layout) (L T : Address → SPath → STy) where
  world : World D L
  transient : Transient D T
  journal : List (Entry D L T)

/-- A state change. -/
inductive Op (D : Layout) (L T : Address → SPath → STy) where
  /-- An update of one instance's account (its storage, balance or nonce). -/
  | account (a : Address) (f : Account D (L a) → Account D (L a))
  /-- An update of one instance's transient storage. -/
  | transient (a : Address) (f : Storage D (T a) → Storage D (T a))

namespace ExecState

/-- **An operation**, journaled. -/
def apply (s : ExecState D L T) : Op D L T → ExecState D L T
  | .account a f => ⟨s.world.set a (f (s.world.accounts a)), s.transient,
      .account a (s.world.accounts a) :: s.journal⟩
  | .transient a f => ⟨s.world, s.transient.set a (f (s.transient.cells a)),
      .transient a (s.transient.cells a) :: s.journal⟩

/-- Operations in order of execution. -/
def run (s : ExecState D L T) : List (Op D L T) → ExecState D L T
  | [] => s
  | o :: os => (s.apply o).run os

/-- Undoing the newest journal entry. -/
def undo (s : ExecState D L T) : ExecState D L T :=
  match s.journal with
  | [] => s
  | .account a old :: j => ⟨s.world.set a old, s.transient, j⟩
  | .transient a old :: j => ⟨s.world, s.transient.set a old, j⟩

/-- Undoing `k` entries. -/
def undoN : Nat → ExecState D L T → ExecState D L T
  | 0, s => s
  | k + 1, s => undoN k s.undo

/-- Undoing an operation's entry gives the state before it. -/
theorem undo_apply (s : ExecState D L T) (o : Op D L T) : (s.apply o).undo = s := by
  cases s with
  | mk w t j =>
    cases o with
    | account a f => simp only [apply, undo, World.set_restore]
    | transient a f => simp only [apply, undo, Transient.set_restore]

theorem journal_apply (s : ExecState D L T) (o : Op D L T) :
    (s.apply o).journal.length = s.journal.length + 1 := by
  cases o <;> simp only [apply, List.length_cons]

theorem journal_run (s : ExecState D L T) (os : List (Op D L T)) :
    (s.run os).journal.length = s.journal.length + os.length := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih =>
    simp only [run, ih, journal_apply, List.length_cons]
    omega

/-- **Undoing every entry since the start restores the start.** -/
theorem undoN_run (s : ExecState D L T) (os : List (Op D L T)) : undoN os.length (s.run os) = s := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih =>
    -- `run (o :: os) s = run os (apply o s)`; undo the `os` entries, then `o`'s.
    have key : ∀ (k : Nat) (x : ExecState D L T), undoN (k + 1) x = (undoN k x).undo := by
      intro k
      induction k with
      | zero => intro x; rfl
      | succ k ihk => intro x; simp only [undoN] at ihk ⊢; exact ihk x.undo
    simp only [run, List.length_cons, key, ih, undo_apply]

end ExecState

/-! ## Frames -/

/-- A transaction's configuration: G01's request; `tx.origin` is its
sender. -/
structure TxConfig where
  request : Request

/-- `tx.origin`. -/
def TxConfig.origin (c : TxConfig) : Address := c.request.sender

/-- A call frame and its journal mark. -/
structure CallFrame where
  this : Address
  caller : Address
  value : Word
  input : Bytes
  static : Bool
  /-- The journal's length on entry. -/
  mark : Nat

/-- **Entering a call** marks the journal. -/
def ExecState.enter (s : ExecState D L T) (this caller : Address) (value : Word) (input : Bytes)
    (static : Bool) : CallFrame :=
  ⟨this, caller, value, input, static, s.journal.length⟩

/-- The frame of a transaction's top-level call. -/
def TxConfig.frame (c : TxConfig) (s : ExecState D L T) : CallFrame :=
  s.enter c.request.target c.request.sender c.request.value c.request.input false

/-- A revert: undo the journal back to the mark. -/
def CallFrame.rollback (f : CallFrame) (s : ExecState D L T) : ExecState D L T :=
  s.undoN (s.journal.length - f.mark)

/-- A success: keep the state and the journal (an enclosing revert still
undoes it). -/
def CallFrame.commit (_ : CallFrame) (s : ExecState D L T) : ExecState D L T := s

/-- **A revert undoes the call**: after any operations since the entry,
the rollback is the state at the entry. -/
theorem rollback_run (s : ExecState D L T) (os : List (Op D L T)) (this caller : Address) (value : Word)
    (input : Bytes) (static : Bool) :
    (s.enter this caller value input static).rollback (s.run os) = s := by
  simp only [CallFrame.rollback, ExecState.enter, ExecState.journal_run]
  rw [show s.journal.length + os.length - s.journal.length = os.length by omega]
  exact ExecState.undoN_run s os

/-- **Nested calls**: the outer call runs `os₁`, enters an inner call that
runs `os₂` and reverts; the state is the outer one after `os₁`, and an
outer revert then returns to the outer entry. -/
theorem rollback_inner (s : ExecState D L T) (os₁ os₂ : List (Op D L T)) (f g : Address → Address →
    Word → Bytes → Bool → CallFrame) (hf : f = s.enter) (hg : g = (s.run os₁).enter)
    (a c : Address) (v : Word) (i : Bytes) (st : Bool) :
    (g a c v i st).rollback ((s.run os₁).run os₂) = s.run os₁ ∧
      (f a c v i st).rollback ((g a c v i st).rollback ((s.run os₁).run os₂)) = s := by
  subst hf hg
  refine ⟨rollback_run _ _ _ _ _ _ _, ?_⟩
  rw [rollback_run]
  exact rollback_run _ _ _ _ _ _ _

theorem run_append (s : ExecState D L T) (os₁ os₂ : List (Op D L T)) :
    s.run (os₁ ++ os₂) = (s.run os₁).run os₂ := by
  induction os₁ generalizing s with
  | nil => rfl
  | cons o os ih => simp only [List.cons_append, ExecState.run, ih]

/-- **A committed inner call is undone by the outer revert.** -/
theorem rollback_outer_after_commit (s : ExecState D L T) (os₁ os₂ os₃ : List (Op D L T))
    (a c : Address) (v : Word) (i : Bytes) (st : Bool) :
    let inner := (s.run os₁).enter a c v i st
    (s.enter a c v i st).rollback ((inner.commit ((s.run os₁).run os₂)).run os₃) = s := by
  simp only [CallFrame.commit, ← run_append]
  exact rollback_run _ _ _ _ _ _ _

/-- A success keeps the call's writes. -/
theorem commit_keeps (f : CallFrame) (s : ExecState D L T) : f.commit s = s := rfl

/-! ## Transfers and the end of a transaction -/

/-- A balance replaced. -/
def Account.withBalance {L : SPath → STy} (x : Account D L) (b : Word) : Account D L :=
  { x with balance := b }

/-- **A value transfer between instances**: `none` when the sender cannot
afford it or the recipient would overflow; otherwise two journaled balance
updates. -/
def ExecState.transfer (s : ExecState D L T) (src dst : Address) (v : Word) : Option (ExecState D L T) :=
  let bs := (s.world.accounts src).balance.val
  let bd := (s.world.accounts dst).balance.val
  if src = dst then (if v.val ≤ bs then some s else none)
  else if h : v.val ≤ bs ∧ bd + v.val < 2 ^ 256 then
    some ((s.apply (.account src fun x => x.withBalance ⟨bs - v.val, by omega⟩)).apply
      (.account dst fun x => x.withBalance ⟨bd + v.val, h.2⟩))
  else none

/-- A transfer between two instances fails exactly when it is unaffordable
or would overflow. -/
theorem transfer_none_iff (s : ExecState D L T) {src dst : Address} (hne : src ≠ dst) (v : Word) :
    s.transfer src dst v = none ↔
      ¬ (v.val ≤ (s.world.accounts src).balance.val ∧
        (s.world.accounts dst).balance.val + v.val < 2 ^ 256) := by
  simp only [ExecState.transfer, hne, if_false]
  constructor
  · intro h hc
    simp only [hc, and_self, dif_pos, reduceCtorEq] at h
  · intro h
    simp only [h, dif_neg, not_false_eq_true]

/-- **A reverted call undoes its transfers.** -/
theorem rollback_transfer (s s' : ExecState D L T) {src dst : Address} (hne : src ≠ dst) (v : Word)
    (h : s.transfer src dst v = some s') (a c : Address) (i : Bytes) (st : Bool) :
    (s.enter a c v i st).rollback s' = s := by
  simp only [ExecState.transfer, hne, if_false] at h
  split at h
  · cases h
    exact rollback_run s [_, _] a c v i st
  · cases h

/-- **The end of a transaction** clears transient storage and the journal,
and keeps the world. -/
def ExecState.endTx (s : ExecState D L T) : ExecState D L T := ⟨s.world, Transient.empty, []⟩

theorem endTx_world (s : ExecState D L T) : s.endTx.world = s.world := rfl

theorem endTx_transient (s : ExecState D L T) (a : Address) (p : SPath) :
    (s.endTx.transient.cells a).read p = Val.default D (T a p) := rfl

end Solidity.Source
