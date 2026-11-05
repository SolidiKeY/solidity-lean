import Solidity.Evm.Machine
import Solidity.Source.World

/-! G39 numeric transient target state. Persistent/memory state remains the
existing Evm.Machine; the separate bank is owner-indexed, never its WordStore.
Journal snapshots are target writes, not a substitute for Source's journal. -/
namespace Solidity.Backend.Transient
open Solidity.Roadmap (Address)
abbrev Word := Roadmap.Word
abbrev Bank := Address → Word → Word

def empty : Bank := fun _ _ => ⟨0,by decide⟩
def put (bank : Bank) (owner : Address) (key value : Word) : Bank :=
  fun a k => if a=owner ∧ k=key then value else bank a k

theorem put_same (bank : Bank) (a : Address) (k v : Word) : put bank a k v a k=v :=
  if_pos ⟨rfl,rfl⟩
theorem put_other (bank : Bank) (a b : Address) (k j v : Word)
    (other : b≠a ∨ j≠k) : put bank a k v b j=bank b j := by
  apply if_neg
  intro h
  rcases other with h'|h'
  · exact h' h.1
  · exact h' h.2

theorem put_restore (bank : Bank) (a : Address) (k v : Word) :
    put (put bank a k v) a k (bank a k)=bank := by
  funext b j
  by_cases h : b=a ∧ j=k
  · rcases h with ⟨rfl,rfl⟩; exact put_same _ _ _ _
  · simp only [put,if_neg h]

structure Entry where
  owner : Address
  key : Word
  old : Word
structure State where
  machine : Evm.Machine
  bank : Bank
  journal : List Entry

def write (s : State) (a : Address) (k v : Word) : State :=
  ⟨s.machine,put s.bank a k v,⟨a,k,s.bank a k⟩::s.journal⟩
def undo (s : State) : State :=
  match s.journal with
  | [] => s
  | e::tail => ⟨s.machine,put s.bank e.owner e.key e.old,tail⟩
def undoN : Nat → State → State
  | 0,s => s
  | n+1,s => undoN n (undo s)
def rollback (mark : Nat) (s : State) : State := undoN (s.journal.length-mark) s

theorem undo_write (s : State) (a : Address) (k v : Word) : undo (write s a k v)=s := by
  cases s
  simp only [write,undo,put_restore]

def endTx (s : State) : State := ⟨s.machine,empty,[]⟩
theorem endTx_fields (s : State) :
    (endTx s).machine=s.machine ∧ (endTx s).bank=empty ∧ (endTx s).journal=[] := ⟨rfl,rfl,rfl⟩
theorem endTx_idempotent (s : State) : endTx (endTx s)=endTx s := rfl

theorem rollback_write (s : State) (a : Address) (k v : Word) :
    rollback s.journal.length (write s a k v)=s := by
  have length : (write s a k v).journal.length-s.journal.length=1 := by
    change s.journal.length+1-s.journal.length=1
    omega
  change undoN _ _=s
  rw [length]
  exact undo_write s a k v

theorem write_machine (s : State) (a : Address) (k v : Word) :
    (write s a k v).machine=s.machine := rfl
end Solidity.Backend.Transient
