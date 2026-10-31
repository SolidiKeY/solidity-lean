import Solidity.Semantics.ContractWorld

/-! Creation-try conditions reuse the existing typed world interface. Only
actual creation-frame catchable failures are caught at the original world;
arguments, static callers, divergence/exhaustion and handler failures retain
their original boundaries. No world implementation or callback policy changes. -/
namespace Solidity.ContractWorld
variable {K : Type} {contracts : K → Contract}

/-- Necessary and sufficient conditions on actual argument, creation and
continuation outcomes, indexed by the full typed world/result pair. -/
def creationTryCondition {α β : Type} (w : World contracts) (args : TRes α) (k : K)
    (target : α → Address) (ctor : α → Prog (contracts k) [] []) (context : α → Context)
    (success : World contracts → Handle k → TRes (World contracts × β))
    (caught : World contracts → THalt → TRes (World contracts × β))
    (result : TRes (World contracts × β)) : Prop :=
  match args with
  | .error e => result = .error e
  | .ok a => if (context a).isStatic then result = .error .revert else
    match w.create k (target a) (ctor a) (context a) with
    | .ok (next, handle) => result = success next handle
    | .error e => if catchable e then result = caught w e else result = .error e

/-- Exact for both normal and halting handler results. An ordinary constructor
failure need not produce normal completion of its catch handler. -/
theorem creationTry_eq_iff {α β : Type} (w : World contracts) (args : TRes α) (k : K)
    (target : α → Address) (ctor : α → Prog (contracts k) [] []) (context : α → Context)
    (success : World contracts → Handle k → TRes (World contracts × β))
    (caught : World contracts → THalt → TRes (World contracts × β))
    (result : TRes (World contracts × β)) :
    w.tryCreate args k target ctor context success caught = result ↔
      creationTryCondition w args k target ctor context success caught result := by
  unfold World.tryCreate creationTryCondition
  simp only [bind, Except.bind]
  repeat' first
    | exact ⟨Eq.symm, Eq.symm⟩
    | (split <;> try simp only [*])

/-- info: 'Solidity.ContractWorld.creationTry_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms creationTry_eq_iff

end Solidity.ContractWorld
