import Solidity.Backend.Executable.CreationFreshness

namespace Solidity.Backend.Executable.CreationFreshness.Controls
open Solidity ContractWorld

def numberContract : Contract := {vars := [("number",.uint)]}
def flagContract : Contract := {vars := [("flag",.bool)]}
def contracts (kind : Bool) : Contract := if kind then flagContract else numberContract

def sender : Address := ⟨⟨10, by decide +kernel⟩, by decide +kernel⟩
def firstAddress : Address := ⟨⟨20, by decide +kernel⟩, by decide +kernel⟩
def secondAddress : Address := ⟨⟨30, by decide +kernel⟩, by decide +kernel⟩
def oldAddress : Address := ⟨⟨40, by decide +kernel⟩, by decide +kernel⟩
def first : Handle false := ⟨firstAddress⟩
def second : Handle true := ⟨secondAddress⟩
def context : Context := {sender}
def initial : World contracts :=
  { World.empty contracts (fun _ => PrimTy.dflt .uint) with
    accounts := fun a => if a = oldAddress then some ⟨true,Storage.init (contracts true)⟩ else none }

def numberCtor : Prog (contracts false) [] [] :=
  .cons (.assign (.root "number" rfl) (.val (.simple (.lit 42 (by decide))))) .nil
def flagCtor : Prog (contracts true) [] [] :=
  .cons (.assign (.root "flag" rfl) (.val (.simple (.bool true)))) .nil

def middle : World contracts :=
  match initial.create false firstAddress numberCtor context with
  | .ok pair => pair.1
  | .error _ => initial
def finalWorld : World contracts :=
  match middle.create true secondAddress flagCtor context with
  | .ok pair => pair.1
  | .error _ => middle

theorem first_run : initial.create false firstAddress numberCtor context = .ok (middle,first) := rfl
theorem second_run : middle.create true secondAddress flagCtor context = .ok (finalWorld,second) := rfl

theorem derived_identity :
    firstAddress ≠ secondAddress ∧ first.address = firstAddress ∧ second.address = secondAddress ∧
    finalWorld.accounts firstAddress = middle.accounts firstAddress ∧
    (∃ st : Storage (contracts false), finalWorld.accounts firstAddress = some ⟨false,st⟩) ∧
    (∃ st : Storage (contracts true), finalWorld.accounts secondAddress = some ⟨true,st⟩) :=
  two first_run second_run

theorem storage_observations :
    (finalWorld.storage? first).map (fun st => st.get (f := "number") rfl) =
      some (.prim (PrimTy.ofLit .uint 42 (by decide))) ∧
    (finalWorld.storage? second).map (fun st => st.get (f := "flag") rfl) =
      some (.prim true) ∧
    finalWorld.accounts oldAddress = initial.accounts oldAddress := by
  exact ⟨rfl,rfl,rfl⟩

/-- A handle alone does not install code into an earlier world. -/
theorem wrong_world : initial.storage? first = none ∧ (finalWorld.storage? first).isSome = true := by
  exact ⟨rfl,rfl⟩

/-- The second typed handle cannot be used to reinterpret the first instance. -/
theorem wrong_kind : finalWorld.storage? (⟨firstAddress⟩ : Handle true) = none := rfl

/-- Retrying the occupied target refuses even a constructor with different code. -/
theorem collision : finalWorld.create false firstAddress .nil context = .error .revert := rfl

/-- Empty and nonempty halts are not conflated with collision refusal. -/
theorem wrong_halt : finalWorld.create false firstAddress .nil context ≠ .error (.revertWith [202,254]) := by
  rw [collision]
  intro h
  cases h

end Solidity.Backend.Executable.CreationFreshness.Controls
