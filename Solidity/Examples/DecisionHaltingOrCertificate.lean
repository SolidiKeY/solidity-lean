import Solidity.Calculus.DecisionHaltingOrCertificate
import Solidity.Calculus.Decision
import Solidity.Calculus.Surface
import Solidity.Calculus.CloseFrame

/-! # Positive-key certificate clients and the zero-key boundary
No closer is registered and original partial-OR verdict observations are preserved.
-/
namespace Solidity.Examples.DecisionHaltingOrCertificate
open Solidity.Decide Solidity.Decide.ResidueReason

def Probe : Contract := contract!{ mapping(uint => uint) balances; uint value; }
def roots : PartialOrRoots Probe := ⟨"value", "balances", rfl, rfl⟩
def claim (key : PrimTy.uint.Denote) : Fml Probe [] :=
  roots.sourceClaim (.user "i") (.user "j") (uintOfNat 0) key (uintOfNat 0)
def member (key : PrimTy.uint.Denote) :
    PartialOrBlockAt roots (uintOfNat 0) key (uintOfNat 0) (claim key) :=
  ⟨.user "i", .user "j", rfl⟩

theorem positive_valid (key : PrimTy.uint.Denote) (hk : 0 < key.1) :
    Fml.Valid (claim key) := (member key).valid_positive hk

theorem positive_validH (key : PrimTy.uint.Denote) (hk : 0 < key.1) :
    Fml.ValidH (claim key) := (member key).validH_positive hk

theorem one_valid : Fml.ValidH (claim (uintOfNat 1)) :=
  positive_validH _ (by decide +kernel)
theorem two_valid : Fml.ValidH (claim (uintOfNat 2)) :=
  positive_validH _ (by decide +kernel)

private theorem initial_read {Γ : Ctx} (σ : State Probe Γ)
    (hs : σ.storage = Storage.init Probe) (key : Tm Probe Γ (.val .uint))
    (value : PrimTy.uint.Denote) (hk : key.eval σ = some value) :
    (roots.mapRead key).eval σ = some (uintOfNat 0) := by
  simp only [PartialOrRoots.mapRead, Tm.eval_app2, Tm.eval_app0, Op0.eval_eq_evalM,
    Op0.evalM, Op2.eval_eq_evalM, Op2.evalM, hk, Option.bind_eq_bind,
    Option.bind_some, Storage.atT]
  change (σ.storage.find ((SRef.ofRoot "balances" (by rfl) :
    SRef Probe (.ref (.mapping .uint (.prim .uint)))).index .map value)).bind
      (fun v => some v.view) = some (uintOfNat 0)
  rw [hs]
  rw [Storage.find_init_total _ (by simp only [CloseS.index_append, CloseS.path_append,
    CloseS.path_ofRoot, Path.append_nil, Path.index_map, Path.total])]
  rfl

/-- The antecedent is inhabited, independently of the partial guard. -/
theorem initial_block : holds (State.init Probe)
    (roots.sourceBlock (.user "i") (.user "j") (uintOfNat 0)) := by
  intro i j _hg
  exact (holds_eq_of_eval (x := uintOfNat 0) (y := uintOfNat 0)
    (initial_read _ rfl _ i rfl) (by rfl)).mpr rfl

/-- The same shortcut is unavailable at zero in an actual initial state. -/
theorem zero_guard_halts : roots.sourceGuard.denote
    (((State.init Probe).push (t := .val .uint) (uintOfNat 0)).push
      (t := .val .uint) (uintOfNat 0)) = none := by rfl

theorem zero_not_positive : ¬ (0 < (uintOfNat 0).1) := by decide +kernel

theorem one_target : (claim (uintOfNat 1)).inTarget {} = true := by rfl
/-- info: false -/
#guard_msgs in #eval (claim (uintOfNat 1)).Covered
/-- info: "unknown" -/
#guard_msgs in #eval (match decideGoal (claim (uintOfNat 1)) with
  | .proved => "proved" | .refuted _ => "refuted" | .unknown => "unknown")
/-- info: "unknown" -/
#guard_msgs in #eval (match decideGoal (claim (uintOfNat 0)) with
  | .proved => "proved" | .refuted _ => "refuted" | .unknown => "unknown")

end Solidity.Examples.DecisionHaltingOrCertificate
