import Solidity.Semantics.ContractWorld

/-! Account-map consequences of actual checked creation. No balances, address
allocator/nonce implementation, source lowering or executable-byte correspondence
is asserted. Freshness is extracted from the existing collision guard. -/
namespace Solidity.Backend.Executable.CreationFreshness
open Solidity ContractWorld
variable {K : Type} [DecidableEq K] {contracts : K → Contract}

omit [DecidableEq K] in
/-- A successful creation necessarily entered at an absent account. -/
theorem fresh {w next : World contracts} {k : K} {target : Address}
    {ctor : Prog (contracts k) [] []} {ctx : Context} {reference : Handle k}
    (run : w.create k target ctor ctx = .ok (next, reference)) :
    w.accounts target = none := by
  unfold World.create at run
  split at run
  · cases run
  · change (if (w.accounts target).isSome || decide (target = ctx.sender) || ctx.isStatic
      then (Except.error THalt.revert : TRes (World contracts × Handle k)) else _) = _ at run
    split at run
    · cases run
    · rename_i guard
      cases ha : w.accounts target with
      | none => rfl
      | some account => simp only [ha, Option.isSome_some, Bool.true_or, not_true_eq_false] at guard

/-- Creation preserves every other actual code/storage account. -/
theorem other {w next : World contracts} {k : K} {target a : Address}
    {ctor : Prog (contracts k) [] []} {ctx : Context} {reference : Handle k}
    (run : w.create k target ctor ctx = .ok (next, reference)) (different : a ≠ target) :
    next.accounts a = w.accounts a := by
  obtain ⟨_, _, _, _, finish, _⟩ := World.create_ok run
  exact World.finish_other finish different

/-- Two successful creates derive distinct targets and retain both typed
instances. Neither disjointness nor the desired preserved account is a premise. -/
theorem two {before middle after : World contracts} {k j : K} {a b : Address}
    {firstCtor : Prog (contracts k) [] []} {secondCtor : Prog (contracts j) [] []}
    {firstCtx secondCtx : Context} {first : Handle k} {second : Handle j}
    (one : before.create k a firstCtor firstCtx = .ok (middle, first))
    (two : middle.create j b secondCtor secondCtx = .ok (after, second)) :
    a ≠ b ∧ first.address = a ∧ second.address = b ∧
      after.accounts a = middle.accounts a ∧
      (∃ st : Storage (contracts k), after.accounts a = some ⟨k,st⟩) ∧
      (∃ st : Storage (contracts j), after.accounts b = some ⟨j,st⟩) := by
  obtain ⟨_, _, _, _, _, hfirst⟩ := World.create_ok one
  obtain ⟨_, _, _, _, _, hsecond⟩ := World.create_ok two
  obtain ⟨st, installed⟩ := World.create_installs one
  rw [hfirst] at installed
  have empty : middle.accounts b = none := fresh two
  have different : a ≠ b := by
    intro eq
    rw [eq, empty] at installed
    cases installed
  have kept : after.accounts a = middle.accounts a := other two different
  refine ⟨different,hfirst,hsecond,kept,⟨st,kept.trans installed⟩,?_⟩
  obtain ⟨st2, installed2⟩ := World.create_installs two
  exact ⟨st2, by simpa only [hsecond] using installed2⟩

end Solidity.Backend.Executable.CreationFreshness
