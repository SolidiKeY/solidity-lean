import Solidity.Backend.CompilerTotal

/-! # `compilerTotal` at the array bound `L = 0`: the check passes, yet no world is accepted

**Claim.** `Solidity/Goals/Total.lean` (module docstring): every `ProgOk []` program compiles and
"the result passes the production static refusal check for every array bound `L ≤ Lmax` and every
frame, so success cannot come from refusing every input".

**Culprit.** `Solidity/Goals/Total.lean:21` (`∀ (b L frame : Nat), L ≤ Lmax → …`, with no `0 < L`
and no conjunct that an accepted world exists) together with `Solidity/Evm/Repr.lean:79`
(`ReprAt.array` demands `k < L`) and `Solidity/Backend/Passes/WholeProgram/Refusal.lean:39`
(the core check is only `Lmax < L + pushes P`).

**Witness.** For the contract `C` with one dynamic storage array, every `ProgOk []` program (the
empty one included) at `L = 0` gets a result with `staticRefused r 0 frame = false`, while
`r.Input 0 frame base σ m` is false for every base map, state and machine: the conclusion of
`compilerTotal` holds exactly where every input is refused. The goal therefore does not deliver
"cannot come from refusing every input"; it only says the static check does not fire.

**Suggested fix.** Quantify over `0 < L` (as `initStorage_repr` does), or add the missing
conjunct `∃ base σ m, r.Input L frame base σ m`, or weaken the docstring to "the static check
does not fire" and let `staticRefused` refuse `L = 0` for contracts with dynamic arrays. -/

namespace Solidity.Examples.RedTeam.Statements.BackendTotalZeroBound

open Solidity Solidity.Evm Solidity.Backend Solidity.Backend.AbiWorld.PublicCompilerTotal

/-- One dynamic storage array `uint[] a`. -/
def C : Contract := { vars := [("a", .ref (.array (.prim .uint)))] }

/-- No dynamic array is represented under the bound `0`. -/
theorem array_unrepresented {st : WordStore} {E : Ty} {s : Slot} {v : SVal (.ref (.array E))} :
    ¬ ReprAt st 0 (.ref (.array E)) s v := by
  intro h
  cases h with
  | array _ hk _ => exact Nat.not_lt_zero _ hk

/-- The conclusion of `compilerTotal` at `L = 0`, and every input refused. -/
theorem passes_yet_no_input {Γ Δ : Ctx} (P : Prog C Γ Δ) (hP : ProgOk [] P) (b frame : Nat) :
    ∃ r : Compiler.Compilation b (Frag.init Γ) P,
      Compiler.compile b (Frag.init Γ) P = some r ∧
      Passes.WholeProgram.staticRefused r 0 frame = false ∧
      ∀ (base : Nat → Fin W) (σ : State C Γ) (m : Machine), ¬ r.Input 0 frame base σ m := by
  obtain ⟨r, hr, hs⟩ := compiler_total C Γ Δ P hP b 0 frame (Nat.zero_le _)
  obtain ⟨G, h, eq⟩ := compile_core b (Matches.init Γ) hP
  obtain rfl : Compiler.Compilation.core G h = r := Option.some.inj (eq.symm.trans hr)
  exact ⟨_, hr, hs, fun _ _ _ hi => array_unrepresented (hi.1.store "a" _ rfl)⟩

/-- The premise is inhabited: the empty program is in the domain. -/
example := passes_yet_no_input (Γ := []) .nil .nil 0 0

-- Reject any dependency outside Lean's three standard logical axioms.
open Lean Elab Command in
run_elab do
  for target in [``passes_yet_no_input] do
    let dependencies ← collectAxioms target
    unless dependencies.all (fun name =>
        [``propext, ``Classical.choice, ``Quot.sound].contains name) do
      throwError "unexpected logical dependencies for {target}: {dependencies}"

end Solidity.Examples.RedTeam.Statements.BackendTotalZeroBound
