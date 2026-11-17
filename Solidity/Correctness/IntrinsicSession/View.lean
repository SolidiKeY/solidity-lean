import Solidity.Correctness.IntrinsicSession.Spec

/-!
# The intrinsic session: its worlds as typed worlds

The `Solidity.Goals.IntrinsicSession.View` of the concrete `spec` (plan step
`is0e-session-spec`); nothing here is a goal.

* `typed`: a start that resumes a boundary world is that typed world; a fresh
  start is its code with nothing deployed (`ContractWorld.World.empty`, no
  funds: the opening balances belong to the environment, which a world does
  not carry).
* `initial` is the fresh start of a code, `resume` the start at a typed world.
* `stored` is `IntrinsicStorage.stored` of the typed world: the list
  `slotHashed` opens with when a run resumes there (`stored_resume`).
* `Boundary F x e h n t` reads `run` at the bound without failure whose
  horizon is `n`: every one of the `n` actions completed (the boundary worlds,
  counting the one resumed, are `n + 1`), the history is exactly `h`, and the
  last boundary world is `t`'s, in the code of `x`. A session whose deployment
  stopped, or one that ended or stopped before `n` actions, lists fewer worlds
  and has no such boundary; so `h` and `t` are functions of `x`, `e` and `n`
  (`Boundary.unique`).
-/

namespace Solidity.Semantics.IntrinsicSession

open Solidity.Roadmap
open Solidity.Goals.IntrinsicSession (Code TypedWorld View)
open Solidity.ContractWorld (World)

/-- The typed world of a session start. -/
def Start.typed : Start → TypedWorld
  | ⟨code, .boundary w⟩ => ⟨code, w⟩
  | ⟨code, .fresh⟩ => ⟨code, World.empty code.catalog (fun _ => PrimTy.dflt .uint) code.roles⟩

/-- The start of a compilation: nothing deployed. -/
def Start.initial (code : Code) : Start := ⟨code, .fresh⟩

/-- The start that resumes a typed world. -/
def Start.resume (t : TypedWorld) : Start := ⟨t.code, .boundary t.world⟩

theorem Start.typed_resume (t : TypedWorld) : (Start.resume t).typed = t := rfl

theorem Start.typed_code (x : Start) : x.typed.code = x.code := by
  obtain ⟨code, _ | w⟩ := x <;> rfl

/-- The boundary worlds of a run in order, the resumed one first. -/
def Start.boundaries (x : Start) (ws : List (World (catalog x.code.contracts))) :
    List (World (catalog x.code.contracts)) :=
  match x.world with
  | .fresh => ws
  | .boundary w => w :: ws

/-- The session of `x` in `e` stands at a transaction boundary after exactly
the history `h`, with `n` actions issued, in the world `w`: at the horizon
`n` without failure all `n` actions completed, with that history, and `w` is
the last boundary world. -/
def Stands (F : Fixed) (x : Start) (e : SessionEnv) (h : List Event) (n : Nat)
    (w : World (catalog x.code.contracts)) : Prop :=
  let ρ := runOf F x e { horizon := n }
  ρ.pfx.events = h ∧ (x.boundaries ρ.worlds).length = n + 1 ∧
    (x.boundaries ρ.worlds).getLast? = some w

/-- **The transaction boundaries of a session**, in typed worlds of its code. -/
def Boundary (F : Fixed) (x : Start) (e : SessionEnv) (h : List Event) (n : Nat)
    (t : TypedWorld) : Prop :=
  ∃ w, t = ⟨x.code, w⟩ ∧ Stands F x e h n w

/-- The history and world of a boundary are determined by the actions issued. -/
theorem Boundary.unique {F : Fixed} {x : Start} {e : SessionEnv} {h h' : List Event} {n : Nat}
    {t t' : TypedWorld} (a : Boundary F x e h n t) (b : Boundary F x e h' n t') :
    h = h' ∧ t = t' := by
  obtain ⟨w, rfl, events, _, last⟩ := a
  obtain ⟨w', rfl, events', _, last'⟩ := b
  cases last.symm.trans last'
  exact ⟨events.symm.trans events', rfl⟩

/-- A boundary's world has the session's code. -/
theorem Boundary.code {F : Fixed} {x : Start} {e : SessionEnv} {h : List Event} {n : Nat}
    {t : TypedWorld} (a : Boundary F x e h n t) : t.code = x.typed.code := by
  obtain ⟨w, rfl, _⟩ := a
  exact x.typed_code.symm

/-- A session resumed at a typed world starts at that world. -/
theorem Boundary.resume (F : Fixed) (t : TypedWorld) (e : SessionEnv) :
    Boundary F (Start.resume t) e [] 0 t :=
  ⟨t.world, rfl, rfl, rfl, rfl⟩

/-- **The view of the concrete intrinsic session semantics.** -/
noncomputable def view (F : Fixed) : View (spec F) where
  typed := Start.typed
  initial := Start.initial
  resume := Start.resume
  stored t := IntrinsicStorage.stored t.world
  Boundary := Boundary F

/-- A start resuming a typed world stores that world's keys. -/
theorem Start.stored_resume (t : TypedWorld) :
    (Start.resume t).stored = IntrinsicStorage.stored t.world := by
  simp only [Start.stored, Start.resume]

/-- The view's stored keys, by rewriting: unifying through `stored` would
unfold its preimage universe. -/
theorem view_stored (F : Fixed) (t : TypedWorld) :
    (view F).stored t = IntrinsicStorage.stored t.world := by
  simp only [view]

/-- The stored keys of a typed world open the slot preimages of every run
resumed there. -/
theorem stored_resume (F : Fixed) (t : TypedWorld) (e : SessionEnv) (r : Bound) {b : Bytes}
    (mem : b ∈ (view F).stored t) : b ∈ (spec F).slotHashed ((view F).resume t) e r := by
  rw [view_stored, ← Start.stored_resume t] at mem
  exact stored_slotHashed mem

end Solidity.Semantics.IntrinsicSession
