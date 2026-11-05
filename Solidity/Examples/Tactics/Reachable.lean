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
default under `.reachable safeM` (`pushRead_validStart`, from `.clean`). `pushRead` is
`Examples/Tactics/TailMode.lean`'s program, over a contract that has entry
points (`Tokens` there has none).

Controls:
* the claim is false under `.any` (`pushRead_not_any`), refuted at a
  dirty-tail state no transaction of `safeM` starts in
  (`danglingState_not_entry`);
* the interface matters: `dirtyM` adds `dirty()`, which writes through an
  alias left dangling by a `pop`; one call of it reaches the dirty tail, and
  the claim fails under `.reachable dirtyM` (`dirty_refutes`);
* a violating caller model admits any world (`top_refutes`), so the order
  of `ValidStartE.weaken` cannot be reversed;
* the mode is not vacuous: the deployment, a committed `add()` and a
  rolled-back `add()` sent value are reachable worlds with entry states
  (`entry_after_add`, `entry_after_rollback`).

`Counter` shows the persistent-invariant route: `x <= 10` proved once, a
constructor box and one box per entry, gives `x != 11` under `.reachable`
(`never11`), false under `.any` (`never11_not_any`) and under an interface
with an entry that breaks the invariant (`eleven_refutes`).
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

/-- The interface with `dirty()` (`none`). -/
def dirtyM : System Bag Unit (Option Act) where
  deploy := fun _ => .nil
  call
    | some a => safeCall a
    | none => sol[Bag]{ dirty(); }

/-- `add();`, `drop();` and `clear();` expose nothing. -/
theorem safeM_exposesNone : ExposesNone safeM :=
  ⟨fun _ => rfl, fun a => by cases a <;> decide⟩

/-- `dirty();` shrinks `tokens` while `r` is held. -/
example : (dirtyM.call none).exposesNone = false := by decide

/-- `tokens.push(); assert(tokens[tokens.length - 1].value == 0);` -/
abbrev pushRead : Fml Bag [] :=
  dl[Bag]{ [ tokens.push(); assert(tokens[tokens.length - 1].value == 0); ] true }

/-- **Under `.clean`**: `cleanTail(storage) = true → [ tokens.push();
assert(tokens[tokens.length - 1].value == 0); ] true`. -/
theorem pushRead_clean : ValidTail .clean pushRead := by
  show ⊨ᶠ dl[Bag]{ cleanTail(storage) = true →
    [ tokens.push(); assert(tokens[tokens.length - 1].value == 0); ] true }
  sol_prove

/-- **Under `.reachable safeM`**: `[ tokens.push(); assert(tokens[tokens.length
- 1].value == 0); ] true` at every starting state of `add()`, `drop()`,
`clear()`; `TailMode.clean` discharged by the interface. -/
theorem pushRead_validStart : ValidStart (.reachable safeM) pushRead :=
  pushRead_clean.validStart_reachable safeM_exposesNone

/-! ## Negative controls -/

/-- `tokens` empty, a `Token{value: 7}` past its end. -/
def dangling : Storage Bag :=
  .cons (.array .nil (.cons (.struct (.cons (.prim (PrimTy.ofLit .uint 7 rfl)) .nil)) .nil)
    SVal.zero_lt_bound) .nil

/-- A state with a dirty tail. -/
def danglingState : State Bag [] := { State.init Bag with storage := dangling }

/-- From `dangling`, `tokens.push()` recycles the `7` and
`assert(tokens[tokens.length - 1].value == 0)` fails. -/
theorem pushRead_fails_dangling : ¬ holds danglingState pushRead :=
  fun h => Modality.afterRunTR_not_panic h (by decide +kernel)

/-- **Under `.any`, `[ tokens.push(); assert(tokens[tokens.length - 1].value
== 0); ] true` is false.** -/
theorem pushRead_not_any : ¬ ValidStart (.any : StartMode Bag Unit Act) pushRead :=
  fun h => pushRead_fails_dangling (h danglingState)

/-- **The dirty-tail state is no starting state of `add()`, `drop()`,
`clear()`.** -/
theorem danglingState_not_entry : ¬ EntryState safeM danglingState :=
  fun h => pushRead_fails_dangling (pushRead_validStart _ h)

/-- The deployment, from an empty transaction. -/
def tx0 : TTx := {}

/-- A zero-value call from address `1`. -/
def tx1 : TTx := { msgSender := PrimTy.ofLit .uint 1 rfl }

/-- The world after deployment. -/
def s0 : World Bag := World.ofState (State.deploy Bag tx0)

/-- Deploying `Bag` (no constructor) from `tx0` gives `s0`. -/
theorem s0_init {D : Type} (M : System Bag Unit D) (hA : M.allowDeploy () tx0)
    (hM : M.deploy () = .nil) : M.Init s0 :=
  ⟨(), tx0, State.deploy Bag tx0, hA, by rw [hM]; rfl, rfl⟩

/-- `tx1` is accepted by a world at address `0` and time `0`. -/
theorem accepts_tx1 {C : Contract} {s : World C} (ha : s.address = PrimTy.dflt .uint)
    (ht : s.timestamp = PrimTy.dflt .uint) : s.accepts tx1 := by
  refine ⟨ha.symm ▸ rfl, ?_, ?_⟩
  · rw [ht]; exact Int.le_refl _
  · rw [ha]; decide

/-- The deployed `Bag` accepts `tx1`. -/
theorem s0_accepts : s0.accepts tx1 := accepts_tx1 rfl rfl

/-- The world `dirty()` leaves: `dangling`, nothing else changed. -/
def s1 : World Bag := { s0 with storage := dangling }

/-- A run's world, read off its fields (each decided by the kernel). -/
theorem run_of_fields {C : Contract} {r : TRes (World C)} {t : World C}
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

/-- **`dirty();` commits from `s0` and reaches the dirty tail.** -/
theorem dirty_run : dirtyM.run s0 none tx1 = .ok s1 :=
  run_of_fields (by decide +kernel)

/-- An entry state over `s1`. -/
def σ1 : State Bag [] := { s1.observe with tx := tx1 }

/-- After `dirty();`, `tx1` starts a transaction at `σ1`. -/
theorem s1_entry : EntryState dirtyM σ1 :=
  ⟨s1, tx1, some .add, .step (.init (s0_init dirtyM trivial rfl))
    (.commit s0_accepts trivial dirty_run), accepts_tx1 rfl rfl, rfl, trivial,
    World.enter_zero s1 tx1 rfl⟩

/-- **The interface matters**: with `dirty()` admitted, `[ tokens.push();
assert(tokens[tokens.length - 1].value == 0); ] true` fails at a reachable
starting state. -/
theorem dirty_refutes : ¬ ValidStart (.reachable dirtyM) pushRead :=
  fun h => Modality.afterRunTR_not_panic (h σ1 s1_entry) (by decide +kernel)

/-! ## Inhabited -/

/-- The world after `add()`. -/
def s2 : World Bag :=
  { s0 with storage := .cons (.array (.cons (.struct (.cons (.prim (PrimTy.ofLit .uint 3 rfl))
      .nil)) .nil) .nil (by decide)) .nil }

/-- `add();` commits from `s0`: `tokens` holds `Token{value: 3}`. -/
theorem add_run : safeM.run s0 .add tx1 = .ok s2 :=
  run_of_fields (by decide +kernel)

/-- **Not vacuous**: a transaction starts after a committed `add()`. -/
theorem entry_after_add : EntryState safeM { s2.observe with tx := tx1 } :=
  ⟨s2, tx1, .add, .step (.init (s0_init safeM trivial rfl)) (.commit s0_accepts trivial add_run),
    accepts_tx1 rfl rfl, rfl, trivial, World.enter_zero s2 tx1 rfl⟩

/-- So the claim holds there. -/
example : holds { s2.observe with tx := tx1 } pushRead := pushRead_validStart _ entry_after_add

/-- A call of `add()` sending one wei. -/
def txValue : TTx := { msgSender := PrimTy.ofLit .uint 1 rfl, msgValue := PrimTy.ofLit .uint 1 rfl }

/-- `add()` is not payable: `add();` sent one wei reverts. -/
theorem add_refuses_value : safeM.run s0 .add txValue = .error .revert := rfl

/-- **A rollback in the sequence**: the revert is rolled back, the world
keeps its storage and ledger, and a transaction starts after it. -/
theorem entry_after_rollback :
    EntryState safeM { (s0.atTime txValue.timestamp).observe with tx := tx1 } :=
  ⟨_, tx1, .add, .step (.init (s0_init safeM trivial rfl))
      (.rollback (tx := txValue) (accepts_tx1 rfl rfl) trivial add_refuses_value (Or.inl rfl)),
    accepts_tx1 rfl rfl, rfl, trivial, World.enter_zero _ tx1 rfl⟩

/-- The rolled-back world is the deployed one: the payment and any write are
undone. -/
example : s0.atTime txValue.timestamp = s0 := rfl

/-- A value transaction is no starting state of a non-payable interface:
`txValue` is refused by every entry. -/
example (a : Act) : safeM.refuses a txValue = true := rfl

/-! ## Under the caller-model stub -/

/-- `noCallback` is the `Lifetime` reading. -/
example : ValidStartE (CallerStub.noCallback (C := Bag)).exec safeM pushRead :=
  validStartE_noCallback_iff.2 pushRead_validStart

/-- `add();`, `drop();` and `clear();` call nobody back. -/
theorem safeM_callsBack (a : Act) : Prog.callsBack true (safeM.call a) = false := by
  cases a <;> decide

/-- Under callbacks too: they keep clean tails (`KeepsCleanC.of_run`). -/
theorem safeM_keepsClean (a : Act) : KeepsCleanC (safeM.call a) :=
  .of_run (safeM_callsBack a) (safeM_exposesNone.2 a)

/-- **`.clean` gives `.reachable` under the `withCallback` stub.** -/
theorem pushRead_withCallback :
    ValidStartE (CallerStub.withCallback (StateInv.cleanTail Bag)).exec safeM pushRead :=
  pushRead_clean.validStartE_withCallback (fun _ => rfl) safeM_keepsClean

/-- The same by weakening: on entries that call nobody back the two stub
readings are ordered (`leOn_of_callsBack`), here for any callback invariant. -/
example (J : StateInv Bag) (hJ : J.pay = true) :
    ValidStartE (CallerStub.withCallback J).exec safeM pushRead :=
  ValidStartE.weaken (leOn_of_callsBack (fun a => hJ ▸ safeM_callsBack a)).2
    (validStartE_noCallback_iff.2 pushRead_validStart)

/-- **A violating caller model admits any world**: under `Exec.top` a safe
entry reaches the dirty tail, and the claim fails. So `ValidStartE.weaken`
does not reverse: the claim holds under `noCallback ≤ Exec.top`, not under
`Exec.top`. -/
theorem top_refutes : ¬ ValidStartE Exec.top safeM pushRead := by
  intro h
  refine Modality.afterRunTR_not_panic (h σ1 ⟨s1, tx1, .add, ?_, accepts_tx1 rfl rfl, rfl,
    trivial, World.enter_zero s1 tx1 rfl⟩) (by decide +kernel)
  exact .step (.init (s0_init safeM trivial rfl))
    (.commit (a := .add) s0_accepts trivial
      (.violated rfl (World.enter_zero s0 tx1 rfl) trivial _))

end Solidity.Examples.Tactics.Reachable

namespace Solidity.Examples.Tactics.Reachable.Counter

open Solidity.Lifetime Solidity.Reachable
open Solidity.Examples.Tactics.Reachable (tx0 tx1 accepts_tx1 run_of_fields)
open scoped Scoped

/-! ## A persistent invariant, by one box per entry

`x <= 10` is proved once over the entry points `inc()` and `zero()`
(`PersistentFml.invariant`), and `x != 11` follows under `.reachable`
(`ValidStart.of_persistent`). An interface that adds `eleven()` breaks it. -/

/-- `contract Counter { uint x; constructor() { x = 0; }
function inc() public { require(x < 10); x = x + 1; }
function zero() public { x = 0; } function eleven() public { x = 11; } }` -/
def Counter : Contract := contract!{
  uint x;
  constructor() { x = 0; }
  function inc() public { require(x < 10); x = x + 1; }
  function zero() public { x = 0; }
  function eleven() public { x = 11; }
}

/-- `inc()` or `zero()`. -/
inductive Act where
  | inc | zero

/-- `inc();`, `zero();`. -/
def counterCall : Act → Prog Counter [] []
  | .inc => sol[Counter]{ inc(); }
  | .zero => sol[Counter]{ zero(); }

/-- The interface: `constructor();`, then `inc();` or `zero();`. -/
def counterM : System Counter Unit Act where
  deploy := fun _ => sol[Counter]{ constructor(); }
  call := counterCall

/-- `x <= 10`, a formula of the storage. -/
def bound : PersistentFml Counter :=
  .ofStorage dl[Counter]{ x <= 10 } rfl (fun _ => Iff.rfl)

/-- `[ constructor(); ] x <= 10`. -/
theorem bound_deploy : ⊨ᶠ dl[Counter]{ [ constructor(); ] x <= 10 } := by sol_prove

/-- `x <= 10 → [ inc(); ] x <= 10`. -/
theorem bound_inc : ⊨ᶠ dl[Counter]{ x <= 10 → [ inc(); ] x <= 10 } := by sol_prove

/-- `x <= 10 → [ zero(); ] x <= 10`. -/
theorem bound_zero : ⊨ᶠ dl[Counter]{ x <= 10 → [ zero(); ] x <= 10 } := by sol_prove

/-- `x <= 10 → x != 11`. -/
theorem bound_never11 : ⊨ᶠ dl[Counter]{ x <= 10 → x != 11 } := by sol_prove

/-- **`x != 11` at every starting state of `inc()`, `zero()`.** -/
theorem never11 : ValidStart (.reachable counterM) dl[Counter]{ x != 11 } :=
  .of_persistent bound (fun _ _ _ => bound_deploy _)
    (fun | .inc => bound_inc | .zero => bound_zero) bound_never11

/-- A state with `x == 11`. -/
def at11 : State Counter [] :=
  { State.init Counter with storage := .cons (.prim (PrimTy.ofLit .uint 11 rfl)) .nil }

/-- **Control**: `x != 11` is not valid under `.any`. -/
theorem never11_not_any :
    ¬ ValidStart (.any : StartMode Counter Unit Act) dl[Counter]{ x != 11 } :=
  fun h => h at11 rfl

/-- So `x == 11` is no starting state of `inc()`, `zero()`. -/
theorem at11_not_entry : ¬ EntryState counterM at11 :=
  fun h => never11 at11 h rfl

/-- The constructor commits, at address `0` and time `0`. -/
private theorem deploy_fields :
    (Counter.deployT (counterM.deploy ()) tx0).toOption.map
      (fun σ => (σ.tx.selfAddress, σ.tx.timestamp)) = some (PrimTy.dflt .uint, PrimTy.dflt .uint) := by
  decide +kernel

/-- **Not vacuous**: `inc()`, `zero()` have a starting state. -/
theorem counter_entry : ∃ σ, EntryState counterM σ := by
  have hf := deploy_fields
  cases hd : Counter.deployT (counterM.deploy ()) tx0 with
  | error e => rw [hd] at hf; cases hf
  | ok σ =>
    rw [hd] at hf
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
    exact ⟨_, World.ofState σ, tx1, .zero, .init ⟨(), tx0, σ, trivial, hd, rfl⟩,
      accepts_tx1 hf.1 hf.2, rfl, trivial, World.enter_zero _ tx1 rfl⟩

/-! ## Control: an entry that breaks the invariant -/

/-- `inc()`, `zero()` and `eleven()` (`none`), no constructor (`x` starts `0`,
where `x <= 10` holds). -/
def elevenM : System Counter Unit (Option Act) where
  deploy := fun _ => .nil
  call
    | some a => counterCall a
    | none => sol[Counter]{ eleven(); }

/-- The deployed world. -/
def c0 : World Counter := World.ofState (State.deploy Counter tx0)

/-- The world `eleven()` leaves. -/
def c1 : World Counter := { c0 with storage := .cons (.prim (PrimTy.ofLit .uint 11 rfl)) .nil }

/-- `eleven();` commits from `c0`. -/
theorem eleven_run : elevenM.run c0 none tx1 = .ok c1 :=
  run_of_fields (by decide +kernel)

/-- **The per-entry obligation is needed**: `x <= 10` holds after deployment
but `eleven()` breaks it, and `x != 11` fails at a reachable starting
state. -/
theorem eleven_refutes : ¬ ValidStart (.reachable elevenM) dl[Counter]{ x != 11 } :=
  fun h => h { c1.observe with tx := tx1 }
    ⟨c1, tx1, none, .step (.init ⟨(), tx0, _, trivial, rfl, rfl⟩)
      (.commit (accepts_tx1 rfl rfl) trivial eleven_run), accepts_tx1 rfl rfl, rfl, trivial,
      World.enter_zero c1 tx1 rfl⟩ rfl

end Solidity.Examples.Tactics.Reachable.Counter
