import Solidity.Backend.Failure.Slice

/-!
# Component-local typed checkpoint rules

The two store types are independent parameters. These records are local
snapshot data, not another source state or term IR. No world/call/catch
semantics is introduced. A failed local frame returns its already copied
outcome while restoring the explicit caller snapshot, including its machine.
-/
namespace Solidity.Backend.Failure.Local

structure Journal (Persistent Transient : Type) where
  persistent : Persistent
  transient : Transient
  machine : Slice.Machine

structure Checkpoint (Persistent Transient : Type) where
  savedPersistent : Persistent
  savedTransient : Transient
  caller : Slice.Machine

variable {P T : Type}

def save (s : Journal P T) : Checkpoint P T :=
  ⟨s.persistent, s.transient, s.machine⟩

def restore (c : Checkpoint P T) : Journal P T :=
  ⟨c.savedPersistent, c.savedTransient, c.caller⟩

def finish (c : Checkpoint P T) (o : Roadmap.Outcome) (live : Journal P T) : Journal P T :=
  match o with
  | .success _ => live
  | .revert _ => restore c

/-- Independent checkpoint rules: success commits the live local state;
failure restores both named snapshots, and never conflates them. -/
inductive CheckpointRel (c : Checkpoint P T) :
    Roadmap.Outcome → Journal P T → Journal P T → Prop
  | success (d : List UInt8) (live : Journal P T) : CheckpointRel c (.success d) live live
  | revert (d : List UInt8) (live : Journal P T) :
      CheckpointRel c (.revert d) live (restore c)

theorem finish_rel (c : Checkpoint P T) (o : Roadmap.Outcome) (live : Journal P T) :
    CheckpointRel c o live (finish c o live) := by
  cases o with
  | success d => exact .success d live
  | revert d => exact .revert d live

theorem CheckpointRel.functional {c : Checkpoint P T} {o : Roadmap.Outcome}
    {live left right : Journal P T} (h₁ : CheckpointRel c o live left)
    (h₂ : CheckpointRel c o live right) : left = right := by
  cases h₁ <;> cases h₂ <;> rfl

theorem restore_save (s : Journal P T) : restore (save s) = s := rfl

theorem snapshot_projections (c : Checkpoint P T) :
    (restore c).persistent = c.savedPersistent ∧
    (restore c).transient = c.savedTransient ∧
    (restore c).machine = c.caller := ⟨rfl, rfl, rfl⟩

theorem rollback_idempotent (c : Checkpoint P T) (s : Journal P T) (d₁ d₂ : List UInt8) :
    finish c (.revert d₂) (finish c (.revert d₁) s) = restore c := rfl

/-- A later outer failure restores the outer checkpoint, regardless of the
inner checkpoint. This does not claim that either checkpoint is a world. -/
theorem outer_rollback (outer inner : Checkpoint P T) (s : Journal P T)
    (innerData outerData : List UInt8) :
    finish outer (.revert outerData) (finish inner (.revert innerData) s) = restore outer := rfl

theorem success_keeps_inner_rollback (outer inner : Checkpoint P T) (s : Journal P T)
    (innerData returnData : List UInt8) :
    finish outer (.success returnData) (finish inner (.revert innerData) s) = restore inner := rfl

end Solidity.Backend.Failure.Local
