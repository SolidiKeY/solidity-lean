import Solidity.Evm.MachineV2
import Solidity.Semantics.Run
import Solidity.Roadmap.G49Final.BridgeGoal

/-! Canonical P1 languages, version 2: revert data, call events and frame
classes (H115 item 3).

The versioned pair of V12's coarse `RuntimeFrame.P1Lang` (which observes no
data and no events, because the frozen `Evm.Out` carries none). Here the
target is the version-2 machine of `Evm/MachineV2.lean`, so both sides can
show the data a frame exits with.

A context fixes a source family `source : Nat → Stmt C Γ Δ`, an emitted
version-2 code image and an admitted input domain. Both languages range over
the same inputs `Input C Γ` (the `L frame caller base machine start` of
`InterfaceV1.Entry`, with a version-2 machine), so the environment map is the
identity.

* **Source.** Resource: the quotation depth `n`. Observation of
  `Stmt.run` of `source n` from the caller (`sourcePrefix`): success is
  `Outcome.success []` (an internal frame returns typed values, not bytes);
  `revertWith d` is `Outcome.revert d`; a bare `revert` is
  `Outcome.revert []`; the code-less `panic` (a failing `assert`) is
  `Outcome.revert (encodePanic 1)`, solc's `Panic(0x01)`, the data the
  source itself gives it when a caller reads it (`TRun.catchBytes`,
  `selfPanicCode`'s default); exhaustion and divergence are unfinished. No
  events: the source run has no journal of external calls. Outside a
  self-call the source keeps some data-less reverts that solc gives data
  (`require(c, "m")`, `docs/solc-alignment.md`), and a successful frame's
  typed results are not bytes. So this language is canonical only for
  families whose bodies make no external call or payment, return no data,
  and whose reverts carry their data in the source (as `revertData` does).
* **Target.** Resource `Unit`. Observation of `runV2 code machine`
  (`targetPrefix`): the calls journaled during the run to an account other
  than the machine's own are events (`Event.call callee value input false`,
  then `Event.answer` with the callee's outcome and data); a call of the
  contract itself is internal to the system and is no event. `ok _ 0` is
  success with no data, `ret _ d` success with `d`, `revert _ d` revert
  with `d`; a pending jump or a fault is unfinished. A revert keeps its
  events (the calls happened); a fault carries no journal, so its events
  are dropped (`⟨[], none⟩`).
* **Frame classes** (`SourceClass`, `TargetClass`) keep what the shared
  `Outcome` merges (bare revert vs. panic vs. revert with data; return vs.
  end of code; fault vs. pending jump) for a bridge's `Local` conclusion.

Typed states, representation and frame words are not observed. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.P1LangV2
open Evm
open Solidity.Roadmap (Event Outcome Prefix Lang Prefixes)

/-- One P1 input: the arguments of `InterfaceV1.Entry`, with a version-2
machine. -/
structure Input (C : Contract) (Γ : Ctx) where
  L : Nat
  frame : Nat
  caller : State C Γ
  base : Nat → Fin W
  machine : MachineV2
  start : Nat

/-- An admission predicate over version-2 inputs. -/
abbrev Admission (C : Contract) (Γ : Ctx) := Input C Γ → Prop

/-! ## Observations -/

/-- A core word as an address: its low 160 bits. -/
def toAddress (a : Fin W) : Solidity.Roadmap.Address := ⟨a.1 % 2 ^ 160, Nat.mod_lt _ (by decide)⟩

/-- A core word as a roadmap word. -/
def toWord (v : Fin W) : Solidity.Roadmap.Word := ⟨v.1, v.2⟩

/-- The events of one journaled call: the request, then the answer. -/
def callEvents (r : CallRec) : List Event :=
  [.call (toAddress r.callee) (toWord r.value) r.input false,
   .answer (if r.success then .success r.output else .revert r.output) none]

/-- The events of the calls journaled after the first `k`, other than
calls of the contract `self` itself. -/
def eventsAfter (self : Fin W) (k : Nat) (calls : List CallRec) : List Event :=
  (((calls.drop k).filter fun r => r.callee != self).map callEvents).flatten

/-- Frame-boundary observation of a source run. -/
def sourcePrefix {C : Contract} {Δ : Ctx} {H : HTy}
    (r : TRes (Solidity.Out C H Δ)) : Prefix Event Outcome :=
  match r with
  | .ok _ => ⟨[], some (.success [])⟩
  | .error (.revertWith d) => ⟨[], some (.revert d)⟩
  | .error .revert => ⟨[], some (.revert [])⟩
  | .error .panic => ⟨[], some (.revert (Semantics.encodePanic 1))⟩
  | .error .exhausted | .error .diverge => ⟨[], none⟩

/-- Frame-boundary observation of a version-2 target run of the contract
`self` from a machine whose journal already holds `k` calls. -/
def targetPrefix (self : Fin W) (k : Nat) (r : OutV2) : Prefix Event Outcome :=
  match r with
  | .ok m 0 => ⟨eventsAfter self k m.calls, some (.success [])⟩
  | .ok m (_ + 1) => ⟨eventsAfter self k m.calls, none⟩
  | .ret m d => ⟨eventsAfter self k m.calls, some (.success d)⟩
  | .revert cs d => ⟨eventsAfter self k cs, some (.revert d)⟩
  | .fault => ⟨[], none⟩

/-! ## Frame classes -/

/-- How a source frame ends, before the shared `Outcome` merges classes. -/
inductive SourceClass where
  | success
  | bareRevert
  | panic
  | revertWith (d : List UInt8)
  | exhausted
  | diverge
  deriving DecidableEq, Repr

def sourceClass {C : Contract} {Δ : Ctx} {H : HTy} (r : TRes (Solidity.Out C H Δ)) :
    SourceClass :=
  match r with
  | .ok _ => .success
  | .error .revert => .bareRevert
  | .error .panic => .panic
  | .error (.revertWith d) => .revertWith d
  | .error .exhausted => .exhausted
  | .error .diverge => .diverge

/-- How a version-2 target frame ends. -/
inductive TargetClass where
  | stop
  | ret (d : List UInt8)
  | revert (d : List UInt8)
  | pending
  | fault
  deriving DecidableEq, Repr

def targetClass : OutV2 → TargetClass
  | .ok _ 0 => .stop
  | .ok _ (_ + 1) => .pending
  | .ret _ d => .ret d
  | .revert _ d => .revert d
  | .fault => .fault

/-- The target observation's final outcome is a function of its class. -/
def TargetClass.final : TargetClass → Option Outcome
  | .stop => some (.success [])
  | .ret d => some (.success d)
  | .revert d => some (.revert d)
  | .pending | .fault => none

theorem targetPrefix_final (self : Fin W) (k : Nat) (r : OutV2) :
    (targetPrefix self k r).final = (targetClass r).final := by
  cases r with
  | ok m s => cases s <;> rfl
  | ret m d => rfl
  | revert cs d => rfl
  | fault => rfl

/-- The source observation's final outcome is a function of its class. -/
def SourceClass.final : SourceClass → Option Outcome
  | .success => some (.success [])
  | .bareRevert => some (.revert [])
  | .panic => some (.revert (Semantics.encodePanic 1))
  | .revertWith d => some (.revert d)
  | .exhausted | .diverge => none

theorem sourcePrefix_final {C : Contract} {Δ : Ctx} {H : HTy} (r : TRes (Solidity.Out C H Δ)) :
    (sourcePrefix r).final = (sourceClass r).final := by
  rcases r with e | o
  · cases e <;> rfl
  · rfl

/-- The source observation shows no events. -/
theorem sourcePrefix_events {C : Contract} {Δ : Ctx} {H : HTy} (r : TRes (Solidity.Out C H Δ)) :
    (sourcePrefix r).events = [] := by
  rcases r with e | o
  · cases e <;> rfl
  · rfl

/-! ## Languages -/

/-- The source observation family of a context. -/
def sourceSem {C : Contract} {Γ Δ : Ctx} (source : Nat → Stmt C Γ Δ) (e : Input C Γ) :
    Prefixes Nat Event Outcome :=
  fun n => sourcePrefix ((source n).run e.caller)

/-- The canonical version-2 source language of one P1 context. -/
def sourceLang {C : Contract} {Γ Δ : Ctx} (source : Nat → Stmt C Γ Δ)
    (allowed : Admission C Γ)
    (consistent : ∀ e : Input C Γ, Prefixes.Consistent (sourceSem source e)) :
    Lang Event Outcome where
  Prog := Unit
  Env := Input C Γ
  Res := Nat
  resLE := inferInstanceAs (LE Nat)
  Allowed := allowed
  Admissible := fun _ => True
  sem := fun _ e => sourceSem source e
  consistent := fun _ e => consistent e

/-- The target observation of one emitted image. -/
noncomputable def targetSem {C : Contract} {Γ : Ctx} (code : List InstrV2) (e : Input C Γ) : Prefix Event Outcome :=
  targetPrefix e.machine.base.self e.machine.calls.length (runV2 code e.machine)

/-- The canonical version-2 target language of one emitted image. -/
noncomputable def targetLang {C : Contract} {Γ : Ctx} (code : List InstrV2)
    (allowed : Admission C Γ) : Lang Event Outcome where
  Prog := Unit
  Env := Input C Γ
  Res := Unit
  resLE := ⟨fun _ _ => True⟩
  Allowed := allowed
  Admissible := fun _ => True
  sem := fun _ e _ => targetSem code e
  consistent := fun _ _ _ _ _ => Prefix.Le.refl _

end Solidity.Backend.InternalFlow.RuntimeFrame.P1LangV2
