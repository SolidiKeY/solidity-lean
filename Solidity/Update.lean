import Solidity.Wp.Terminal.Table

/-!
# Symbolic updates

The calculus never writes a derivation as a chain of programs alone.  Every
line of every chain is an *updated* judgment,

    {acc := alice·account} {storage := save(storage, acc·balance, 10)} φ

and the last line of a derivation is usually not a rule application at all
but the *composition* of the accumulated updates into one parallel update,

    {acc := alice·account ‖ storage := save(storage, alice·account·balance, 10)} φ

`Wp/Terminal/Table.lean` already has the content of those updates — one
`State -> Res State` function per terminal rule family, written in the
interpreter's state vocabulary.  What it does not have is an *algebra*: the
updates are Lean functions, so `{u}{v}` is `Function.comp` and there is
nothing to write on the page.  This module gives the same functions a
first-order spelling, so a derivation can carry them line by line.

## The design

An **elementary update** `Elem` names one of the four things a Solidity
state holds and gives a *pre-state reader* for its new value:

| `Elem` | update | `State` fields |
|---|---|---|
| `.env n rhs` | `x := t`, `sp := alice·account`, `mv := …` | `env` |
| `.storage rhs` | `storage := save(…)` / `store(…)` / `push` / `pop` / `delete` | `storage` |
| `.heap rhs` | `memory := write(…)` / `new(T)` | `heap`, `nextId` |
| `.net rhs` | `net := …` | `net`, `selfBalance` |

The reader takes the state the update is *applied in*, which is what makes
a list of them **parallel**: `Par.apply` evaluates every reader in the
incoming state and only then writes, left to right, so a later element
overwrites an earlier one but never *reads* it.  That is KeY's parallel
update, and it is why the merge law below has to re-read the right-hand
side in the composed state.

`heap` and `net` are written as a pair each because their two `State`
fields move together: an allocation bumps `nextId`, and a `transfer`
debits `selfBalance` alongside the ledger (`Wp.transferUpd`).

## What is proved here

The algebra, and nothing about any particular rule:

* `Par.apply_nil`, `Upd.seq_assoc`, `Upd.id_seq`, `Upd.seq_id` — a monoid;
* `Par.seq_single` — **the merge law**, `{u}{x := t} = {u ‖ x := {u}t}`,
  the step every derivation upstream ends with;
* `UpdJudgment.Holds` and `UpdJudgment.holds_id`, which tie an updated
  judgment back to `SolidityJudgment.Holds`.

The per-rule bridges (`Par.toUpd [...] = <family> args`) live in
`Update/Bridges.lean`.  The *derivation* layer these updates are written in is
`Update/Step.lean` -- sequents, frontiers and the rule-indexed step relation --
with its surface notation in `Update/SequentSyntax.lean` (`seq!`) and the
reader lemmas that make a merge line provable in `Update/Merge.lean`.
-/

namespace Solidity
namespace Upd

open Semantics

/-- One elementary update: a component of the state, and a reader that
computes its new value **in the state the update is applied in**. -/
inductive Elem where
  /-- `x := t`: rebind one name.  Covers a stack value (`Binding.val`), a
  storage alias (`Binding.spath`) and a memory identity (`Binding.mref`) --
  the calculus writes all three the same way. -/
  | env (n : Name) (rhs : State -> Res Binding)
  /-- `storage := …`: the whole storage tree, as `save`/`store`/`push`/
  `pop`/`delete` produce it. -/
  | storage (rhs : State -> Res (List (Name × SVal)))
  /-- `memory := …`: the heap and the allocation counter, which move
  together. -/
  | heap (rhs : State -> Res (List (Nat × MObj) × Nat))
  /-- `net := …`: the ledger and the contract's own balance, which
  `transfer` moves together. -/
  | net (rhs : State -> Res (List (Int × Int) × Int))

/-- A parallel update: elementary updates that all read the same
pre-state.  Written `{a ‖ b ‖ c}` in the calculus. -/
abbrev Par := List Elem

namespace Elem

/-- Evaluate an elementary update's reader in `s`, yielding the writer it
will apply.  Splitting evaluation from writing is what makes a `Par`
parallel. -/
def eval (e : Elem) (s : State) : Res (State -> State) :=
  match e with
  | .env n rhs => (rhs s).map fun b => fun t => t.setEnv n b
  | .storage rhs => (rhs s).map fun g => fun t => { t with storage := g }
  | .heap rhs => (rhs s).map fun x => fun t => { t with heap := x.1, nextId := x.2 }
  | .net rhs => (rhs s).map fun x => fun t => { t with net := x.1, selfBalance := x.2 }

end Elem

namespace Par

/-- Every element's writer, all read in the same state, in list order
(so the *first* faulting element is the one that halts). -/
def writers : Par -> State -> Res (List (State -> State))
  | [], _ => .ok []
  | e :: rest, s => do
      let w <- e.eval s
      let ws <- writers rest s
      return w :: ws

/-- Apply a parallel update: read everything in `s`, then write left to
right, so the last element writing a component wins. -/
def apply (p : Par) (s : State) : Res State :=
  (p.writers s).map fun ws => ws.foldl (fun t w => w t) s

@[simp] theorem writers_nil (s : State) : writers [] s = .ok [] := rfl

@[simp] theorem apply_nil (s : State) : apply [] s = .ok s := rfl

theorem writers_append (p q : Par) (s : State) :
    writers (p ++ q) s =
      (writers p s) >>= fun ws => (writers q s).map fun vs => ws ++ vs := by
  induction p with
  | nil =>
      show writers q s = _
      simp only [writers, bind, Except.bind, Except.map, List.nil_append]
      cases writers q s <;> rfl
  | cons e rest ih =>
      show (do let w <- e.eval s; let ws <- writers (rest ++ q) s; pure (w :: ws)) = _
      cases he : e.eval s with
      | error h => simp [writers, he, bind, Except.bind]
      | ok w =>
          simp only [writers, he, bind, Except.bind, ih]
          cases writers rest s with
          | error h => rfl
          | ok ws => cases writers q s <;> rfl

theorem apply_eq_of_writers {p : Par} {s : State} {ws : List (State -> State)}
    (h : writers p s = .ok ws) :
    apply p s = .ok (ws.foldl (fun t w => w t) s) := by
  simp [apply, h, Except.map]

/-- Appending one element: the writers of `p` fold onto `s` first, then
the new writer applies to the result. -/
theorem apply_append_single (p : Par) (e : Elem) (s : State) :
    apply (p ++ [e]) s =
      (writers p s) >>= fun ws =>
        (e.eval s).map fun w => w (ws.foldl (fun t v => v t) s) := by
  simp only [apply, writers_append, writers, bind, Except.bind, Except.map,
    pure, Except.pure]
  cases writers p s with
  | error h => rfl
  | ok ws =>
      cases e.eval s with
      | error h => rfl
      | ok w => simp [List.foldl_append]

end Par

/-- An update, as the calculus's `{u}` acts: a state transformer that may
halt.  Sequential composition is Kleisli composition, which is exactly
what `{u}{v}` means. -/
abbrev _root_.Solidity.Upd := State -> Res State

/-- The empty update, KeY's `skip`. -/
def id : Upd := fun s => .ok s

/-- `{u}{v}`: run `u`, then `v` in the result. -/
def seq (u v : Upd) : Upd := fun s => u s >>= v

@[inherit_doc] scoped infixr:65 " ⨟ " => seq

theorem seq_assoc (u v w : Upd) : seq (seq u v) w = seq u (seq v w) := by
  funext s
  simp only [seq, bind, Except.bind]
  cases u s <;> rfl

@[simp] theorem id_seq (u : Upd) : seq id u = u := by
  funext s; rfl

@[simp] theorem seq_id (u : Upd) : seq u id = u := by
  funext s
  simp only [seq, id, bind, Except.bind]
  cases u s <;> rfl

namespace Par

/-- A parallel update as an `Upd`. -/
def toUpd (p : Par) : Upd := p.apply

@[simp] theorem toUpd_nil : toUpd [] = Upd.id := by funext s; rfl

end Par

namespace Elem

/-- Re-read an elementary update's right-hand side *after* `p`: the
calculus's `{u}t`.  This is what turns `{u}{x := t}` into a single parallel
update. -/
def after (e : Elem) (p : Par) : Elem :=
  match e with
  | .env n rhs => .env n (fun s => p.apply s >>= rhs)
  | .storage rhs => .storage (fun s => p.apply s >>= rhs)
  | .heap rhs => .heap (fun s => p.apply s >>= rhs)
  | .net rhs => .net (fun s => p.apply s >>= rhs)

theorem eval_after {e : Elem} {p : Par} {s s' : State}
    (h : p.apply s = .ok s') : (e.after p).eval s = e.eval s' := by
  cases e <;> simp [after, eval, h, bind, Except.bind, Except.map]

theorem eval_after_error {e : Elem} {p : Par} {s : State} {halt : Halt}
    (h : p.apply s = .error halt) : (e.after p).eval s = .error halt := by
  cases e <;> simp [after, eval, h, bind, Except.bind, Except.map]

end Elem

/-- **The merge law**, `{u}{x := t} = {u ‖ x := {u}t}`.

This is the step the calculus draws at the end of almost every derivation:
two stacked updates collapse into one parallel update, at the price of
re-reading the second one's right-hand side in the first one's result.
Both directions of the KeY update calculus that have real content
(`applyOnPV`, `applyOnDifferentPV`) are instances of it once the readers
are unfolded; see `Update/Bridges.lean`. -/
theorem Par.seq_single (p : Par) (e : Elem) :
    Upd.seq (Par.toUpd p) (Par.toUpd [e]) = Par.toUpd (p ++ [e.after p]) := by
  funext s
  show (Par.apply p s >>= fun s1 => Par.apply [e] s1) =
    Par.apply (p ++ [e.after p]) s
  rw [Par.apply_append_single]
  cases hw : Par.writers p s with
  | error halt =>
      have hap : Par.apply p s = .error halt := by simp [Par.apply, hw, Except.map]
      simp only [hap, hw, bind, Except.bind]
  | ok ws =>
      have hap : Par.apply p s = .ok (ws.foldl (fun t w => w t) s) :=
        Par.apply_eq_of_writers hw
      simp only [hap, hw, bind, Except.bind, Elem.eval_after hap]
      show Par.apply [e] (ws.foldl (fun t w => w t) s) = _
      simp only [Par.apply, Par.writers, bind, Except.bind, Except.map,
        pure, Except.pure]
      cases Elem.eval e (ws.foldl (fun t w => w t) s) <;> rfl

end Upd

/-- A dynamic-logic judgment under an accumulated update: the calculus's
`{u} ⟨[ program ]⟩ φ`.  The update runs first, then the program, then the
postcondition is read in the final state. -/
structure UpdJudgment where
  upd : Upd
  j : SolidityJudgment

namespace UpdJudgment

open Semantics

/-- Run an updated judgment.  The verdict shape is
`SolidityJudgment.check`'s: a `revert` makes a box judgment hold and a
diamond judgment fail, a stuck run validates nothing. -/
def check (uj : UpdJudgment) (s0 : State := State.exampleStore) : Bool :=
  match uj.upd s0 with
  | .ok s => uj.j.check s
  | .error .revert => uj.j.block.modality = SolidityModality.box
  | .error .stuck => false

/-- Validity of an updated judgment. -/
def Holds (uj : UpdJudgment) (s0 : State := State.exampleStore) : Prop :=
  uj.check s0 = true

instance (uj : UpdJudgment) (s0 : State) : Decidable (uj.Holds s0) :=
  inferInstanceAs (Decidable (uj.check s0 = true))

/-- With no update accumulated yet, an updated judgment is the plain
judgment: the base case of every derivation. -/
@[simp] theorem check_id (j : SolidityJudgment) (s0 : State) :
    (UpdJudgment.mk Upd.id j).check s0 = j.check s0 := rfl

@[simp] theorem holds_id (j : SolidityJudgment) (s0 : State) :
    (UpdJudgment.mk Upd.id j).Holds s0 ↔ j.Holds s0 := Iff.rfl

/-- An update-only rewriting step preserves validity: this is what makes
the merge line of a derivation upstream a legitimate step. -/
theorem check_congr {u v : Upd} (h : u = v) (j : SolidityJudgment)
    (s0 : State) :
    (UpdJudgment.mk u j).check s0 = (UpdJudgment.mk v j).check s0 := by
  rw [h]

end UpdJudgment

end Solidity
