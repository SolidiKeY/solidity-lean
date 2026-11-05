import Solidity.Theory.Reachable.CallerModel
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# A witness contract for the `reachable` mode, and its controls

`Bag` keeps `Token[] tokens`. Through the interface `safeM` (`add`, `drop`,
`clear`), every entry exposes nothing, so every reachable world has clean
tails, and `tokens.push()` followed by a read of the new element proves the
default under `.reachable safeM` (`pushRead_reachable`, from `.clean`).

Controls:
* the claim is false under `.any` (`pushRead_not_any`), refuted at a
  dirty-tail state no transaction of `safeM` starts in
  (`danglingState_not_entry`);
* the interface matters: `dirtyM` adds `dirty()`, which writes through an
  alias left dangling by a `pop`; one call of it reaches the dirty tail, and
  the claim fails under `.reachable dirtyM` (`dirty_refutes`);
* the mode is not vacuous: the deployment and a committed `add()` are
  reachable worlds with entry states (`entry_after_add`).

`Counter` shows the persistent-invariant route: `x <= 10` proved once, a
constructor box and one box per entry, gives `x != 11` under `.reachable`
(`never11`), false under `.any` (`never11_not_any`).
-/

namespace Solidity.Examples.Tactics.Reachable

open Solidity.Lifetime Solidity.Reachable
open scoped Scoped

/-- `contract Bag { Token[] tokens; … }`. -/
def Bag : Contract := contract!{
  Token[] tokens;
  function add() public { Token storage r = tokens.push(); r.value = 3; }
  function drop() public { tokens.pop(); }
  function clear() public { delete tokens; }
  function dirty() public { Token storage r = tokens.push(); tokens.pop(); r.value = 7; }
}

/-- The entries that expose nothing. -/
inductive Act where
  | add | drop | clear

/-- `add();`, `drop();`, `clear();`. -/
def safeCall : Act → Prog Bag [] []
  | .add => sol[Bag]{ add(); }
  | .drop => sol[Bag]{ drop(); }
  | .clear => sol[Bag]{ clear(); }

/-- The interface without `dirty()`; no constructor. -/
def safeM : System Bag Unit Act where
  deploy := fun _ => .nil
  call := safeCall

/-- The interface with `dirty()`. -/
def dirtyM : System Bag Unit (Option Act) where
  deploy := fun _ => .nil
  call
    | some a => safeCall a
    | none => sol[Bag]{ dirty(); }

/-- `add`, `drop` and `clear` expose nothing. -/
theorem safeM_exposesNone : ExposesNone safeM :=
  ⟨fun _ => rfl, fun a => by cases a <;> decide⟩

/-- `dirty()` shrinks `tokens` while `r` is held. -/
example : (dirtyM.call none).exposesNone = false := by decide

/-- `tokens.push(); assert(tokens[tokens.length - 1].value == 0);` -/
abbrev pushRead : Fml Bag [] :=
  dl[Bag]{ [ tokens.push(); assert(tokens[tokens.length - 1].value == 0); ] true }

/-- **Under `.clean`**: the recycled slot reads the default. -/
theorem pushRead_clean : ValidTail .clean pushRead := by
  show ⊨ᶠ dl[Bag]{ cleanTail(storage) = true →
    [ tokens.push(); assert(tokens[tokens.length - 1].value == 0); ] true }
  sol_prove

/-- **Under `.reachable safeM`**: `TailMode.clean` discharged by the
interface. -/
theorem pushRead_reachable : ValidStart (.reachable safeM) pushRead :=
  pushRead_clean.validStart_reachable safeM_exposesNone

/-! ## Negative controls -/

/-- `tokens` empty, a `Token{value: 7}` past its end. -/
def dangling : Storage Bag :=
  .cons (.array .nil (.cons (.struct (.cons (.prim (PrimTy.ofLit .uint 7 rfl)) .nil)) .nil)
    SVal.zero_lt_bound) .nil

/-- A state with a dirty tail. -/
def danglingState : State Bag [] := { State.init Bag with storage := dangling }

/-- From `dangling` the `push` recycles the `7` and the `assert` fails. -/
theorem pushRead_fails_dangling : ¬ holds danglingState pushRead :=
  fun h => Modality.afterRunTR_not_panic h (by decide +kernel)

/-- **The claim is false under `.any`.** -/
theorem pushRead_not_any : ¬ ValidStart (.any : StartMode Bag Unit Act) pushRead :=
  fun h => pushRead_fails_dangling (h danglingState)

/-- **The dirty-tail state is no entry state of `safeM`.** -/
theorem danglingState_not_entry : ¬ EntryState safeM danglingState :=
  fun h => pushRead_fails_dangling (pushRead_reachable _ h)

/-- The deployment, from an empty transaction. -/
def tx0 : TTx := {}

/-- A zero-value call from address `1`. -/
def tx1 : TTx := { msgSender := PrimTy.ofLit .uint 1 rfl }

/-- The world after deployment. -/
def s0 : World Bag := World.ofState (State.deploy Bag tx0)

theorem s0_init {D : Type} (M : System Bag Unit D) (hA : M.allowDeploy () tx0)
    (hM : M.deploy () = .nil) : M.Init s0 :=
  ⟨(), tx0, State.deploy Bag tx0, hA, by rw [hM]; rfl, rfl⟩

/-- `tx1` is accepted by a world at address `0` and time `0`. -/
theorem accepts_tx1 {C : Contract} {s : World C} (ha : s.address = PrimTy.dflt .uint)
    (ht : s.timestamp = PrimTy.dflt .uint) : s.accepts tx1 := by
  refine ⟨ha.symm ▸ rfl, ?_, ?_⟩
  · rw [ht]; exact Int.le_refl _
  · rw [ha]; decide

theorem s0_accepts : s0.accepts tx1 := accepts_tx1 rfl rfl

/-- The world `dirty()` leaves: `dangling`, nothing else changed. -/
def s1 : World Bag := { s0 with storage := dangling }

private theorem run_of_fields {r : TRes (World Bag)} {t : World Bag}
    (h : r.toOption.map (fun u => (u.storage, u.net, u.balance, u.address, u.timestamp)) =
      some (t.storage, t.net, t.balance, t.address, t.timestamp)) : r = .ok t := by
  cases r with
  | error e => cases h
  | ok u =>
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    cases u
    cases t
    simp only at h1 h2 h3 h4 h5
    subst h1 h2 h3 h4 h5
    rfl

/-- **`dirty()` commits and reaches the dirty tail.** -/
theorem dirty_run : dirtyM.run s0 none tx1 = .ok s1 :=
  run_of_fields (by decide +kernel)

/-- An entry state over `s1`. -/
def σ1 : State Bag [] := { s1.observe with tx := tx1 }

theorem s1_entry : EntryState dirtyM σ1 :=
  ⟨s1, tx1, .step (.init (s0_init dirtyM trivial rfl)) (.commit s0_accepts trivial dirty_run),
    accepts_tx1 rfl rfl, World.enter_zero s1 tx1 rfl⟩

/-- **The interface matters**: with `dirty()` admitted, the claim fails at a
reachable entry state. -/
theorem dirty_refutes : ¬ ValidStart (.reachable dirtyM) pushRead :=
  fun h => Modality.afterRunTR_not_panic (h σ1 s1_entry) (by decide +kernel)

/-! ## Inhabited -/

/-- The world after `add()`. -/
def s2 : World Bag :=
  { s0 with storage := .cons (.array (.cons (.struct (.cons (.prim (PrimTy.ofLit .uint 3 rfl))
      .nil)) .nil) .nil (by decide)) .nil }

theorem add_run : safeM.run s0 .add tx1 = .ok s2 :=
  run_of_fields (by decide +kernel)

/-- **Not vacuous**: a transaction starts after a committed `add()`. -/
theorem entry_after_add : EntryState safeM { s2.observe with tx := tx1 } :=
  ⟨s2, tx1, .step (.init (s0_init safeM trivial rfl)) (.commit s0_accepts trivial add_run),
    accepts_tx1 rfl rfl, World.enter_zero s2 tx1 rfl⟩

/-- So the claim holds there. -/
example : holds { s2.observe with tx := tx1 } pushRead := pushRead_reachable _ entry_after_add

/-- The same under the caller-model stub: `noCallback` is the `Lifetime`
reading. -/
example : ValidStartE (CallerStub.noCallback (C := Bag)).exec safeM pushRead :=
  validStartE_noCallback_iff.2 pushRead_reachable

/-- **A violating run admits any world**: under an execution relation that
always violates, a safe entry reaches the dirty tail, and the claim fails.
An invariant under a caller model owes the absence of violations. -/
theorem violating_refutes :
    ¬ ValidStartE (fun _ _ r => r = .violated) safeM pushRead := by
  intro h
  refine Modality.afterRunTR_not_panic (h σ1 ⟨s1, tx1, ?_, accepts_tx1 rfl rfl,
    World.enter_zero s1 tx1 rfl⟩) (by decide +kernel)
  exact .step (.init (s0_init safeM trivial rfl))
    (.commit (a := .add) s0_accepts trivial (.violated rfl (World.enter_zero s0 tx1 rfl) rfl _))

end Solidity.Examples.Tactics.Reachable

namespace Solidity.Examples.Tactics.Reachable.Counter

open Solidity.Lifetime Solidity.Reachable
open scoped Scoped

/-! ## A persistent invariant, by one box per entry

`contract Counter { uint x; constructor() { x = 0; } function inc() { require(x < 10); x = x + 1; } function zero() { x = 0; } }`:
`x <= 10` is proved once over the entry points (`PersistentFml.invariant`),
and `x != 11` follows under `.reachable` (`ValidStart.of_persistent`). -/

/-- The counter. -/
def Counter : Contract := contract!{
  uint x;
  constructor() { x = 0; }
  function inc() public { require(x < 10); x = x + 1; }
  function zero() public { x = 0; }
}

/-- `inc()` or `zero()`. -/
inductive Act where
  | inc | zero

/-- The interface: `constructor();`, then `inc();` or `zero();`. -/
def counterM : System Counter Unit Act where
  deploy := fun _ => sol[Counter]{ constructor(); }
  call
    | .inc => sol[Counter]{ inc(); }
    | .zero => sol[Counter]{ zero(); }

/-- `x <= 10`, a formula of the storage. -/
def bound : PersistentFml Counter :=
  .ofStorage dl[Counter]{ x <= 10 } rfl (fun _ => Iff.rfl)

/-- `[ constructor(); ] x <= 10`. -/
theorem bound_deploy : Fml.Valid (.modal .box (counterM.deploy ()) .nil bound.fml) := by
  show ⊨ᶠ dl[Counter]{ [ constructor(); ] x <= 10 }
  sol_prove

/-- `x <= 10 → [ inc(); ] x <= 10` and the same for `zero();`. -/
theorem bound_calls (a : Act) :
    Fml.Valid (.imp bound.fml (.modal .box (counterM.call a) .nil bound.fml)) := by
  cases a
  · show ⊨ᶠ dl[Counter]{ x <= 10 → [ inc(); ] x <= 10 }
    sol_prove
  · show ⊨ᶠ dl[Counter]{ x <= 10 → [ zero(); ] x <= 10 }
    sol_prove

/-- **`x != 11` at every reachable starting state.** -/
theorem never11 : ValidStart (.reachable counterM) dl[Counter]{ x != 11 } :=
  .of_persistent bound (fun d _ _ => bound_deploy (State.deploy Counter _))
    bound_calls (by show ⊨ᶠ dl[Counter]{ x <= 10 → x != 11 }; sol_prove)

/-- A state with `x == 11`: no starting state of `counterM`. -/
def at11 : State Counter [] :=
  { State.init Counter with storage := .cons (.prim (PrimTy.ofLit .uint 11 rfl)) .nil }

/-- **Control**: `x != 11` is not valid under `.any`. -/
theorem never11_not_any :
    ¬ ValidStart (.any : StartMode Counter Unit Act) dl[Counter]{ x != 11 } :=
  fun h => h at11 rfl

/-- So `at11` is no entry state of `counterM`. -/
theorem at11_not_entry : ¬ EntryState counterM at11 :=
  fun h => never11 at11 h rfl

/-- The constructor commits, at address `0` and time `0`. -/
private theorem deploy_fields :
    (Counter.deployT (counterM.deploy ()) tx0).toOption.map
      (fun σ => (σ.tx.selfAddress, σ.tx.timestamp)) = some (PrimTy.dflt .uint, PrimTy.dflt .uint) := by
  decide +kernel

/-- **Not vacuous**: `counterM` has an entry state. -/
theorem counter_entry : ∃ σ, EntryState counterM σ := by
  have hf := deploy_fields
  cases hd : Counter.deployT (counterM.deploy ()) tx0 with
  | error e => rw [hd] at hf; cases hf
  | ok σ =>
    rw [hd] at hf
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
    exact ⟨_, World.ofState σ, tx1, .init ⟨(), tx0, σ, trivial, hd, rfl⟩,
      accepts_tx1 hf.1 hf.2, World.enter_zero _ tx1 rfl⟩

end Solidity.Examples.Tactics.Reachable.Counter
