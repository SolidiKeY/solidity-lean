import Solidity.Correctness.IntrinsicSession.Laws.Structure
import Solidity.Examples.IntrinsicSession.Spec

/-! The structural session laws on the one-contract session of `Spec.lean`, resumed at `w`. -/
namespace Solidity.Examples.IntrinsicSession.Laws.Structure

open Solidity.Roadmap Solidity.Semantics.IntrinsicSession Solidity.Examples.IntrinsicSession.Spec
open Solidity.Goals.IntrinsicSession (Code Good Moved outcomes)

variable {C : Contract} {code : Code} {w : ContractWorld.World code.catalog} {F : Fixed}
  {r : Bound} {e : SessionEnv} (s : OneRequest C code w F r e)

/-- The session's events at any bound: no call to a precompile, every deployed address the
computed one, and a call's successor the strategy's move; the parameters are `F`. -/
example (r' : Bound) (allowed : e.Allowed) (good : Good (spec F) r') {c v i st sd a o x h ev} :
    (spec F).fixed = F ∧
    (Event.call c v i st ∈ ((spec F).lang.sem s.start e r').events → ¬ c.Precompile) ∧
    (Event.deploy sd v a o (some x) ∈ ((spec F).lang.sem s.start e r').events →
      x = F.createAddress e.deployer e.deployNonce) ∧
    (h ++ [Event.call c v i st, ev] <+: ((spec F).lang.sem s.start e r').events →
      Moved (e.callee (h ++ [Event.call c v i st])) ev) :=
  ⟨Laws.fixed F, Laws.precompiles F s.start e r' c v i st, Laws.this F s.start e r' sd v a o x,
    Laws.answered F s.start e r' h c v i st ev allowed good⟩

/-- A final observation of the session is its last outcome: with an outcome shown, the
history's last one. -/
example {o} (final : ((spec F).lang.sem s.start e r).final = some o)
    (shown : outcomes ((spec F).lang.sem s.start e r).events ≠ []) :
    (outcomes ((spec F).lang.sem s.start e r).events).getLast? = some o :=
  (Laws.final_last F s.start e r o final).resolve_left shown

/-- Two good bounds of the session have a common one, which extends the listed worlds and
the preimages of both; the stored keys of `w` are slot preimages, hence preimages, there. -/
example {r' : Bound} (good : Good (spec F) r) (good' : Good (spec F) r') :
    ∃ r'', Good (spec F) r'' ∧
      (spec F).worlds s.start e r <+: (spec F).worlds s.start e r'' ∧
      (spec F).worlds s.start e r' <+: (spec F).worlds s.start e r'' ∧
      (spec F).hashed s.start e r <+: (spec F).hashed s.start e r'' ∧
      (spec F).hashed s.start e r' <+: (spec F).hashed s.start e r'' ∧
      ∀ b ∈ (view F).stored ⟨code, w⟩, b ∈ (spec F).hashed s.start e r'' :=
  have ⟨r'', good'', le, le'⟩ := Laws.directed F r r' good good'
  ⟨r'', good'', Laws.worlds_consistent F s.start e r r'' le,
    Laws.worlds_consistent F s.start e r' r'' le', Laws.hashed_consistent F s.start e r r'' le,
    Laws.hashed_consistent F s.start e r' r'' le', fun b mem =>
      Laws.slotHashed_sub F s.start e r'' b (Laws.stored_hashed F ⟨code, w⟩ e r'' b mem)⟩

/-- The session's start is the world resumed at `w`, the initial world has the code, and a
listed world keeps the code and runs as the world resumed at its typed world. -/
example {ω} (mem : ω ∈ (spec F).worlds s.start e r) :
    (view F).typed ((view F).resume ⟨code, w⟩) = ⟨code, w⟩ ∧
    ((view F).typed ((view F).initial code)).code = code ∧ ((view F).typed ω).code = code ∧
    (spec F).lang.sem ω = (spec F).lang.sem ((view F).resume ((view F).typed ω)) ∧
    (spec F).slotHashed ω = (spec F).slotHashed ((view F).resume ((view F).typed ω)) :=
  have resumes := Laws.listed_resumes F s.start e r ω mem
  ⟨Laws.typed_resume F ⟨code, w⟩, Laws.initial_code F code, Laws.worlds_code F s.start e r ω mem,
    resumes.1, resumes.2.2.2⟩

end Solidity.Examples.IntrinsicSession.Laws.Structure
