import Solidity.Source.Eval

namespace Solidity.Source.SemanticsExamples
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Event Outcome)

/-- A toy hash: the selector is a positional checksum of the bytes. -/
def toyKeccak (bs : Bytes) : Nat := ((bs.foldl (fun a b => a * 257 + b.toNat) 0 % 2 ^ 32) * 2 ^ 224) % 2 ^ 256

def toyFixed : Solidity.Roadmap.Fixed where
  evm := { keccak := toyKeccak, keccak_lt := fun _ => Nat.mod_lt _ (by decide),
           precompile := fun _ _ => none, precompileGas := fun _ _ => 0 }
  ledger := fun bal _ a => bal a
  regionLen := 1
  rootSlots := 1

def E0 : Env := ⟨[]⟩

def P0 : Program E0 where
  body _ := none
  consts _ := none
  inits _ := []
  ctor _ := none
  ctorLocals _ := []
  baseArgs _ := []
  contracts := []

def G0 (p : Solidity.Roadmap.Pipeline) : Glob E0 :=
  ⟨P0, p, toyFixed, fun _ => ⟨0, by decide⟩, fun _ _ => false, fun _ => .answer (.success []), ⟨0, by decide⟩⟩

def s0 : St E0 := ⟨⟨⟨fun _ => Account.empty _⟩, Transient.empty, []⟩, Heap.empty, [], [], ⟨[], .nil⟩⟩

def F0 : Fr := { this := ⟨1, by decide⟩, sender := ⟨2, by decide⟩, value := ⟨0, by decide⟩, static := false, contract := "C" }

def u8 : STy := .int IntTy.u8

/-- `x + 1` at `uint8`. -/
def incX : RExpr E0 [u8] u8 := .binary .add (.local .here) (.conv (.const (Q.ofInt 1)) (.inl (by decide)))

def l255 : Locals E0.layout [u8] := .cons (.int 255 (by decide)) .nil

def res {Γ : RCtx} {τ : STy} (r : Except Halt (RVal E0.layout τ) × (Locals E0.layout Γ × St E0)) : Option Bytes :=
  match r.1 with
  | .error (.revert d) => some d
  | _ => none

example : res ((evalE (G0 .legacy) F0 10 incX).run (l255, s0)) = some (panicData .arithmetic) := by decide

end Solidity.Source.SemanticsExamples
