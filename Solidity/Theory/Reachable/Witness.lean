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
-/

namespace Solidity.Reachable.Witness

open Solidity.Lifetime
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

theorem s0_init {D : Type} (M : System Bag Unit D) (hM : M.deploy () = .nil) : M.Init s0 :=
  ⟨(), tx0, State.deploy Bag tx0, trivial, by rw [hM]; rfl, rfl⟩

theorem s0_accepts : s0.accepts tx1 := by decide

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
  ⟨s1, tx1, .step (.init (s0_init dirtyM rfl)) (.commit s0_accepts trivial dirty_run),
    by decide, World.enter_zero s1 tx1 rfl⟩

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
  ⟨s2, tx1, .step (.init (s0_init safeM rfl)) (.commit s0_accepts trivial add_run),
    by decide, World.enter_zero s2 tx1 rfl⟩

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
  refine Modality.afterRunTR_not_panic (h σ1 ⟨s1, tx1, ?_, by decide,
    World.enter_zero s1 tx1 rfl⟩) (by decide +kernel)
  exact .step (.init (s0_init safeM rfl))
    (.commit (a := .add) s0_accepts trivial (.violated rfl (World.enter_zero s0 tx1 rfl) rfl _))

end Solidity.Reachable.Witness
