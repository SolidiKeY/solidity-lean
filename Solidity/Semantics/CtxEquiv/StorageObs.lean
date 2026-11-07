import Solidity.Semantics.CtxEquiv.Basic
import Solidity.Semantics.RecursiveStorage.Observations

/-!
# Storage observational equivalence as contextual equivalence (S1.2)

`Value.ObsEq` (`Solidity/Semantics/RecursiveStorage/Arrays.lean`, laws in
`Solidity/Semantics/RecursiveStorage/Observations.lean`) equates two
recursive storage values that agree on every path observation (failed reads,
words, live lengths and retained extents).  It is restated here as
contextual equivalence for one language, by construction: the stored value
is the program, the adversary chooses one path (a single read, no writes),
and the run completes with the observation there (`obsEq_iff_ctxEquiv`).
This places the storage relation in the same order as the ABI-boundary
relation (`Solidity/Semantics/CtxEquiv/Basic.lean`), but it is not a G50
statement: ObsEq storages giving `CtxEquiv` sessions needs a source
semantics over these values, which no Source module reads yet (open).
-/

namespace Solidity.CtxEquiv

open Solidity.Roadmap (Prefix Lang)
open Solidity.TypeGraph

variable {n : Nat}

/-- What one path read shows: the observation, tagged with its type. -/
abbrev PathObs (n : Nat) := Option (Σ U : TypeGraph.Ty n, U.Head)

/-- The adversary of a stored value: a path out of its type. -/
abbrev PathAdv {n : Nat} (G : TypeGraph.Schema n) (T : TypeGraph.Ty n) := Σ U : TypeGraph.Ty n, Path G T U

/-- Reading a stored value along a path, as a G01 language with one bound
and no events. -/
def storageLang (G : TypeGraph.Schema n) (T : TypeGraph.Ty n) : Lang Unit (PathObs n) where
  Prog := Value G T
  Env := PathAdv G T
  Res := Unit
  resLE := ⟨fun _ _ => True⟩
  Allowed := fun _ => True
  Admissible := fun _ => True
  sem := fun v a _ => ⟨[], some ((v.observe a.2).map fun x => ⟨a.1, x⟩)⟩
  consistent := fun _ _ _ _ _ => Prefix.Le.refl _

/-- A stored value deployed against path adversaries. -/
def storageContract {G : TypeGraph.Schema n} {T : TypeGraph.Ty n} (v : Value G T) :
    Deployed (PathAdv G T) Unit (PathObs n) :=
  Deployed.mk' (storageLang G T) v id

theorem tag_injective {U : TypeGraph.Ty n} {x y : Option U.Head}
    (h : x.map (fun z => (⟨U, z⟩ : Σ U : TypeGraph.Ty n, U.Head)) = y.map fun z => ⟨U, z⟩) : x = y := by
  cases x <;> cases y
  · rfl
  · cases h
  · cases h
  · simp only [Option.map_some, Option.some.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at h
    rw [h]

/-- **Storage observational equivalence, restated** as contextual equivalence
against single-read path adversaries. -/
theorem obsEq_iff_ctxEquiv {G : TypeGraph.Schema n} {T : TypeGraph.Ty n} (v w : Value G T) :
    v.ObsEq w ↔ CtxEquivOn (fun _ => True) (storageContract v) (storageContract w) := by
  constructor
  · intro h
    have hb : ∀ a : PathAdv G T, (storageContract v).behav a = (storageContract w).behav a := by
      intro a
      funext π
      simp only [Deployed.behav, Behav.ofPrefixes, storageContract, Deployed.mk', storageLang, id,
        h a.2]
    exact ⟨fun a _ => by rw [hb a]; exact Behav.Below.refl _,
      fun a _ => by rw [hb a]; exact Behav.Below.refl _⟩
  · intro h U p
    have hd : ((storageContract v).behav ⟨U, p⟩).Done []
        ((v.observe p).map fun x => ⟨U, x⟩) := ⟨(), trivial, rfl⟩
    obtain ⟨_, _, he⟩ := (h.1 ⟨U, p⟩ trivial).done hd
    simp only [storageContract, Deployed.mk', storageLang, id, Prefix.mk.injEq, Option.some.injEq,
      true_and] at he
    exact (tag_injective he).symm

end Solidity.CtxEquiv
