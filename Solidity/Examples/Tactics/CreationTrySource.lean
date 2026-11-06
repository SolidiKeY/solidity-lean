import Solidity.Tools.CreationTryReplay

/-! The complete unchanged original create.sol source, imported through its
pinned compiler AST. These are concrete typed world/caller executions, not
universal source validity or a CREATE nonce-model equivalence claim. -/
namespace Solidity.Examples.Tactics.CreationTrySource
open Solidity.Frontend.CreationTry Solidity.ContractWorld Semantics
solc_creation_try "../../../tests/solc/CreationTry.ast.json" hash 0xd3643a80701c47bf
  from_contract "C" as Original

def sender : Address := ⟨⟨103164821458651970696730694074090566093359944210, by decide +kernel⟩, by decide +kernel⟩
def factory : Address := ⟨⟨457415396813334496268612927368880745799219276745, by decide +kernel⟩, by decide +kernel⟩
def first : Address := ⟨⟨428238858683769988117249899297947241168592284849, by decide +kernel⟩, by decide +kernel⟩
def second : Address := ⟨⟨765865378857594171345198072072138302409814020804, by decide +kernel⟩, by decide +kernel⟩
def initial := World.empty Original.contracts (fun a => if a = sender then (⟨1000000000000000000000000000000, by decide +kernel⟩ : ContractWorld.Word) else ⟨0, by decide +kernel⟩)

def expected (b : Nat) (text : List UInt8) : List Nat :=
  (wordBytes b ++ wordBytes 64 ++ wordBytes text.length ++ pad32 text).map UInt8.toNat

def both : TRes (List Nat × List Nat) := do
  let (w, self) ← Original.deploy initial factory { sender }
  let (w, caught) ← Original.run w self { sender } first "f()"
  let (_, succeeded) ← Original.run w self { sender } second "g()"
  pure (caught, succeeded)

/-- Both complete original source observations, checked in order by the kernel.
The explicit address/funding contexts are independent of output bytes. -/
theorem original_outputs : both.toOption = some
    (expected 0 [116,101,115,116,32,109,101,115,115,97,103,101,46],
     expected 1 [115,117,99,99,101,115,115]) := by decide +kernel
/-- The same whole caller sequence in ordinary, unbounded model semantics. -/
def bothOrdinary : TRes (List Nat × List Nat) := do
  let (w, self) ← Original.deploy initial factory { sender }
  let (w, caught) ← Original.m0.runOrdinary w self { sender } first
  let (_, succeeded) ← Original.m1.runOrdinary w self { sender } second
  pure (caught, succeeded)

/-- Composition of the generated universal per-method correspondence laws. -/
theorem both_approx : TRes.Approx both bothOrdinary := by
  unfold both bothOrdinary
  apply (TRes.Approx.refl _).bind
  rintro ⟨w, self⟩
  apply (Original.m0.run_approx w self { sender } first).bind
  rintro ⟨next, caught⟩
  exact (Original.m1.run_approx next self { sender } second).map (fun pair => (caught, pair.2))

/-- Actual completed observations exclude bounded exhaustion/divergence. -/
theorem both_normal : both.halt? = none := by
  cases executed : both with
  | error e =>
    have h := original_outputs
    simp only [executed, Except.toOption] at h
    cases h
  | ok out => rfl

/-- The proved finite witness gives the exact ordinary result. -/
theorem ordinary_execution : bothOrdinary = both := by
  apply Eq.symm
  apply both_approx.eq
  intro divergent
  have h := both_normal
  rw [divergent] at h
  cases h

/-- A wrong caught byte sequence cannot satisfy the actual source witness. -/
theorem wrong_reason_refused : both.toOption ≠ some
    (expected 0 [116,101,115,116,32,109,101,115,115,97,103,101,47],
     expected 1 [115,117,99,99,101,115,115]) := by
  rw [original_outputs]
  decide +kernel

/-- Collision/wrong creation target is an actual uncaught bare halt, not
silently an Error(string) reason or a created handle. -/
def collision : TRes (List Nat) := do
  let (w, self) ← Original.deploy initial factory { sender }
  let (_, bytes) ← Original.run w self { sender } factory "g()"
  pure bytes

theorem collision_uncaught : collision.halt? = some .revert := by decide +kernel

/-- Source-level creation rollback and installation are actual world facts. -/
def installations : TRes (Bool × Bool) := do
  let (w, self) ← Original.deploy initial factory { sender }
  let (w, _) ← Original.run w self { sender } first "f()"
  let failedAbsent := (w.accounts first).isNone
  let (w, _) ← Original.run w self { sender } second "g()"
  pure (failedAbsent, (w.storage? (⟨second⟩ : Handle Original.Code.c1)).isSome)

theorem actual_rollback_and_installation : installations.toOption = some (true, true) := by decide +kernel

/-- Read the exact evaluated source argument words, independently of the
constructors' unused parameters and their eventual return observations. -/
def argumentValues : TRes (Int × Int) := do
  let (w, self) ← Original.deploy initial factory { sender }
  let st ← TRes.ofOpt (w.storage? self)
  let entry ← w.enter (k := .c2) self.address { sender } st false
  let f ← Original.m0.before.runF 1000 entry
  let g ← Original.m1.before.runF 1000 entry
  pure ((TEnv.get .here f.st.env).1, (TEnv.get .here g.st.env).1)

theorem actual_arguments : argumentValues.toOption = some (3, 8) := by decide +kernel

/- Runtime frontend/host controls below are distinct from the kernel witnesses.
No malformed job or wrong expected bytes may certify a completed fixture. -/
def host (selfText := "457415396813334496268612927368880745799219276745")
    (senderText := "103164821458651970696730694074090566093359944210") : Lean.Json :=
  Lean.Json.mkObj [("kind", Lean.toJson "creation-try-source"),
    ("selfAddress", Lean.toJson selfText), ("sender", Lean.toJson senderText),
    ("value", Lean.toJson "0"), ("ownerFunds", Lean.toJson "0"), ("timestamp", Lean.toJson "0"),
    ("senderFunds", Lean.toJson "1000000000000000000000000000000"), ("firstCreationNonce", Lean.toJson (1 : Nat))]

def vector (signature : String) (bytes : List Nat) : Lean.Json := Lean.Json.mkObj [
  ("signature", Lean.toJson signature), ("calldata", Lean.toJson ([] : List Nat)),
  ("expectedBytes", Lean.toJson bytes), ("failure", Lean.toJson false)]

def replayStatus (context : Lean.Json) (vectors : List Lean.Json) : Option String :=
  let job := Lean.Json.mkObj [("hostContext", context), ("vectors", Lean.toJson vectors)]
  ((Tools.CreationTryReplay.replay Original.contracts Original.deploy Original.run job).getObjValAs? String "status").toOption

#guard replayStatus (host) [] == some "blocked"
#guard replayStatus (host "0") [vector "f()" []] == some "blocked"
#guard replayStatus (host (senderText := "0")) [vector "f()" []] == some "blocked"
#guard replayStatus (host) [vector "absent()" []] == some "blocked"
#guard replayStatus (host) [vector "f()" [1]] == some "broken"
#guard replayStatus (host) [vector "f()" (expected 0 [116,101,115,116,32,109,101,115,115,97,103,101,46]),
  vector "g()" (expected 1 [115,117,99,99,101,115,115])] == some "working"

end Solidity.Examples.Tactics.CreationTrySource
