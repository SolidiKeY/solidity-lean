import Solidity.Theorems

/-! Arbitrary in-range stored values with separate source and target executions. -/
namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics

def cellContract : Contract := { vars := [("x", .prim .uint)] }
def cellRef : SRef cellContract (.prim .uint) := ⟨"x", rfl, .nil⟩
def writeProgram (n : Int) (hn : PrimTy.uint.inRange n = true) : Prog cellContract [] [] :=
  .cons (.assign (.root "x" rfl) (.val (.simple (.lit n hn)))) .nil

def cellSource : State cellContract [] := Evm.freshT cellContract 0 (by decide) ⟨0, by decide⟩
def cellMachine : Evm.Machine := Evm.Machine.init (fun _ => 0) ⟨0, by decide⟩
def writtenMachine (n : Int) : Evm.Machine :=
  { cellMachine with
    store := Evm.WordStore.write cellMachine.store (.root 0)
      (Evm.wmod (Evm.toWord n)).1 }

theorem write_fragment (n : Int) (hn : PrimTy.uint.inRange n = true) :
    Evm.inFragP (Evm.Frag.init []) (writeProgram n hn) = some (Evm.Frag.init []) := rfl

theorem write_source (n : Int) (hn : PrimTy.uint.inRange n = true) :
    ∃ o, Prog.run cellSource (writeProgram n hn) = .ok o ∧
      o.st.storage.findLive cellRef = some (.prim (⟨n, hn⟩ : PrimTy.uint.Denote)) :=
  ⟨_, rfl, rfl⟩

theorem write_target (n : Int) (hn : PrimTy.uint.inRange n = true) :
    Evm.run (Evm.compileProg 0 (writeProgram n hn)) cellMachine = .ok (writtenMachine n) 0 := rfl

theorem changed_observation : cellMachine.store (.root 0) = 0 ∧
    (writtenMachine 1).store (.root 0) = 1 := ⟨rfl, rfl⟩

theorem storage_observation_erasure_rejected :
    (writtenMachine 1).store (.root 0) ≠ cellMachine.store (.root 0) := by
  change (1 : Nat) ≠ 0
  decide +kernel

theorem write_compiler_application (n : Int) (hn : PrimTy.uint.inRange n = true) :
    ∃ o mc', Prog.run cellSource (writeProgram n hn) = .ok o ∧
      Evm.run (Evm.compileProg 0 (writeProgram n hn)) cellMachine = .ok mc' 0 ∧
      Evm.Sim cellContract (1 + Evm.Prog.pushes (writeProgram n hn)) 0
        (Evm.Frag.init []) o.st mc' := by
  obtain ⟨o, ho, _⟩ := write_source n hn
  unfold cellSource at ho
  rcases Main.compiler_correct (write_fragment n hn)
    (Evm.Sim.init cellContract 0 (by decide) (fun _ => 0) ⟨0, by decide⟩ rfl)
    (by change 1 ≤ Evm.Lmax; decide) with
    h | ⟨hsrc, _⟩ | ⟨hp, _⟩ | ⟨hd, _⟩
  · exact h
  · rcases hsrc with hr | ⟨_, hp⟩
    · rw [ho] at hr
      cases hr
    · rw [ho] at hp
      cases hp
  · cases hp
  · rw [ho] at hd
    cases hd

end Solidity.Assurance.NonVacuityH28
