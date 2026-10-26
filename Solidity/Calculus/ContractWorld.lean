import Solidity.Calculus.Correct
import Solidity.Semantics.ContractWorld

/-!
# Existing correctness proofs at actual contract-world outcomes

The entry premise is checked after payment. A successful frame witnesses the
typed run, so neither exhaustion nor an assumed external response creates a
world outcome. The caller supplies the meaning of a postcondition for global
funds and the world invariant; settlement remains explicit in the witness.
-/

namespace Solidity.ContractWorld

variable {K : Type} [DecidableEq K] {contracts : K → Contract}

/-- A per-function box proof holds at every successful world call's result.
The actual paid entry must satisfy its precondition. -/
theorem World.callFrame_post_of_spec {w next : World contracts} {k : K} {α : Type}
    {r : Handle k} {entry : Entry (contracts k) α} {ctx : Context}
    {result : State (contracts k) entry.locals}
    (pre : Spec (contracts k) []) (post : Spec (contracts k) entry.locals)
    (proved : Spec.Valid (.imp pre (.box entry.body post)))
    (entered : ∀ st σ, w.storage? r = some st →
      w.enter r.address ctx st entry.payable = .ok σ → Spec.sat σ pre)
    (run : w.callFrame r entry ctx = .ok (next, result)) : Spec.sat result post := by
  obtain ⟨st, σ, o, stored, enter, ran, _, eq⟩ := World.callFrame_ok run
  have box : Spec.sat σ (.box entry.body post) := proved σ (entered st σ stored enter)
  simp only [Spec.sat, ran] at box
  exact eq ▸ box

/-- A constructor proof applies to the real constructor outcome, with fresh
storage, funded entry and the exact committed world retained as premises. -/
theorem World.create_post_of_spec {w next : World contracts} {k : K} {self : Address}
    {ctor : Prog (contracts k) [] []} {ctx : Context} {reference : Handle k}
    (pre post : Spec (contracts k) [])
    (proved : Spec.Valid (.imp pre (.box ctor post)))
    (entered : ∀ σ, w.enter self ctx (Storage.init (contracts k))
      (((contracts k).ctor.map (·.payable)).getD false) = .ok σ → Spec.sat σ pre)
    (run : w.create k self ctor ctx = .ok (next, reference)) :
    ∃ σ : State (contracts k) [], Spec.sat σ post ∧
      w.finish self σ = .ok next ∧ reference.address = self := by
  obtain ⟨σ, o, enter, ran, finish, address⟩ := World.create_ok run
  have box : Spec.sat σ (.box ctor post) := proved σ (entered σ enter)
  simp only [Spec.sat, ran] at box
  exact ⟨o.st, box, finish, address⟩

/-- Read a formula box at a successful typed outcome with any result context. -/
private theorem fml_post_of_run {C : Contract} {Γ : Ctx} {P : Prog C [] Γ}
    {post : Fml C Γ} {σ : State C []} {o : Out C σ.H Γ}
    (box : holds σ (.modal .box P .nil post)) (run : P.run σ = .ok o) :
    holds o.st post := by
  change Modality.afterRunTR .box (holds · post) (Prog.runFrames σ P .nil) at box
  have hr : Prog.runFrames σ P .nil = .ok o.st := by
    unfold Prog.runFrames
    rw [run]
    rfl
  rw [hr] at box
  exact box.1

/-- Existing dynamic-logic proofs also establish actual world call results. -/
theorem World.callFrame_post_of_fml {w next : World contracts} {k : K} {α : Type}
    {r : Handle k} {entry : Entry (contracts k) α} {ctx : Context}
    {result : State (contracts k) entry.locals}
    (pre : Fml (contracts k) []) (post : Fml (contracts k) entry.locals)
    (proved : Fml.Valid (.imp pre (.modal .box entry.body .nil post)))
    (entered : ∀ st σ, w.storage? r = some st →
      w.enter r.address ctx st entry.payable = .ok σ → holds σ pre)
    (run : w.callFrame r entry ctx = .ok (next, result)) : holds result post := by
  obtain ⟨st, σ, o, stored, enter, ran, _, eq⟩ := World.callFrame_ok run
  exact eq ▸ fml_post_of_run (proved σ (entered st σ stored enter)) ran

/-- A constructor formula proof is read only at a real successful creation,
with its exact global settlement retained for a world invariant proof. -/
theorem World.create_post_of_fml {w next : World contracts} {k : K} {self : Address}
    {ctor : Prog (contracts k) [] []} {ctx : Context} {reference : Handle k}
    (pre post : Fml (contracts k) [])
    (proved : Fml.Valid (.imp pre (.modal .box ctor .nil post)))
    (entered : ∀ σ, w.enter self ctx (Storage.init (contracts k))
      (((contracts k).ctor.map (·.payable)).getD false) = .ok σ → holds σ pre)
    (run : w.create k self ctor ctx = .ok (next, reference)) :
    ∃ σ : State (contracts k) [], holds σ post ∧
      w.finish self σ = .ok next ∧ reference.address = self := by
  obtain ⟨σ, o, enter, ran, finish, address⟩ := World.create_ok run
  exact ⟨o.st, fml_post_of_run (proved σ (entered σ enter)) ran, finish, address⟩

end Solidity.ContractWorld
