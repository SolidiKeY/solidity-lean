import Solidity.Lowering.P8b.Domain
import Solidity.Roadmap.Controls

/-! Contract-only controls reuse G07's published model READ ONLY. They do not
instantiate production SourceSpec, intrinsic world, compiler or full profile. -/
namespace Solidity.Lowering.P8b.Controls
open Roadmap Roadmap.Controls

/-- Closed positive certificate on the EXISTING G07 identity model. The
resource function is literally identity, not selected by classical choice. -/
def identityCert : Cert (pass toySource toyIntrinsic id) where
  envSound := envSound toySource toyIntrinsic
  envOnto := envOnto toySource toyIntrinsic
  need := fun _ _ _ r => r
  need_ok := fun _ _ _ _ _ _ hf hg => ⟨trivial,hf,hg,Prefix.Le.refl _⟩
  back := fun _ _ _ r _ _ hg => ⟨r,trivial,hg,Prefix.Le.refl _⟩

def resolved (p : Toy) : ToyRes := ⟨p,.legacy,.v2⟩
def artifact : Artifact := ⟨[],0⟩

theorem success : ∃ rt, toyIntrinsic.lang.Admissible rt ∧
    (toyIntrinsic.lang.sem (.quiet [1]) quietEnv rt).final=some (.success [1]) ∧
    (toyIntrinsic.lang.sem (.quiet [1]) quietEnv rt).events=[] := by
  exact (identityCert.refines (.quiet [1])
    (dom toySource toyIntrinsic id (resolved (.quiet [1])) trivial trivial artifact)
    quietEnv quietEnv_allowed).completes trivial
      (toy_forward (.quiet [1]) quietEnv 0).1 (toy_forward (.quiet [1]) quietEnv 0).2 rfl

theorem failure : ∃ rt, toyIntrinsic.lang.Admissible rt ∧
    (toyIntrinsic.lang.sem (.fail [7]) quietEnv rt).final=some (.revert [7]) ∧
    (toyIntrinsic.lang.sem (.fail [7]) quietEnv rt).events=[] := by
  exact (identityCert.refines (.fail [7])
    (dom toySource toyIntrinsic id (resolved (.fail [7])) trivial trivial artifact)
    quietEnv quietEnv_allowed).completes trivial
      (toy_forward (.fail [7]) quietEnv 0).1 (toy_forward (.fail [7]) quietEnv 0).2 rfl

/-- All structural laws also hold for a WRONG emitter. Therefore they are
not sufficient evidence for the semantic Cert field of G01 Lowering. -/
def badEmit : toySource.lang.Prog → toyIntrinsic.World := fun _ => .fail []

theorem bad_agrees :
    (pass toySource toyIntrinsic badEmit).run (.quiet [1])
      (dom toySource toyIntrinsic badEmit (resolved (.quiet [1])) trivial trivial artifact)=
      toyIntrinsic.ofWorld (lower toySource toyIntrinsic badEmit
        (resolved (.quiet [1])) trivial trivial artifact) := rfl

theorem bad_no_certificate : ¬ Nonempty (Cert (pass toySource toyIntrinsic badEmit)) := by
  apply no_certificate_of_wrong_completion toySource toyIntrinsic badEmit
    (resolved (.quiet [1])) trivial trivial artifact quietEnv ⟨0,false⟩ quietEnv_allowed trivial
    (toy_forward (.quiet [1]) quietEnv 0).1 (toy_forward (.quiet [1]) quietEnv 0).2
    (.success [1]) rfl
  intro rt _
  rcases rt with ⟨n,b⟩
  cases b <;> intro h <;> cases h

/-- Genuine G07 divergence is no-failure-admissibility divergence only.
An exhausted loop remains a revert and is not silently included. -/
theorem loop_no_failure :
    (toyIntrinsic.lang.sem .loop quietEnv).Diverges
      (fun r => toyIntrinsic.lang.Admissible r ∧ toyIntrinsic.NoFail r) := by
  intro r hr
  have hx : r.exhausted=false := hr.2
  change (Toy.run .loop r.exhausted).final=none
  rw [hx]
  rfl

theorem loop_exhausted :
    (toyIntrinsic.lang.sem .loop quietEnv ⟨0,true⟩).final=some (.revert []) := rfl

/-- Inhabited conditional assembly on the existing contract-only model;
not a production Lowering or a certificate for badEmit. -/
def identityLowering : Lowering toySource toyIntrinsic :=
  assemble toySource toyIntrinsic id identityCert

theorem identity_bound (p : toySource.lang.Prog) (h : MeaningDomain toySource p)
    (e : toyIntrinsic.lang.Env) (r : toySource.lang.Res) :
    identityLowering.cert.need p h e r=r := rfl

end Solidity.Lowering.P8b.Controls
