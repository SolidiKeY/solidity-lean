import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV4
import Solidity.Roadmap.G49Final.BridgeGoal

/-! Canonical G01 languages for one P1 runtime-frame context (H68 family 3).

A context fixes a source family `source : Nat → Stmt C Γ Δ` (for a recursive
family, `InterfaceV1.recursiveSource … n`), an emitted code image and the
admitted P1 input domain. Both languages range over the SAME inputs
`Input C Γ` (the `L frame caller base machine start` of `InterfaceV1.Entry`),
with `Allowed` the admitted domain, so the prescribed environment map is the
identity.

* Source: the resource is the quotation depth `n` (the only bound the
  intrinsic recursion has); the prefix at `n` is the actual `Stmt.run` of
  `source n` from the input's caller.
* Target: `Evm.run` has no resource index, so the resource is `Unit`; the
  prefix is the actual run of the code image from the input's machine.

Observations use the shared `Event`/`Outcome` types at the frame boundary,
deliberately coarsened to what the target model `Evm.Out` can show (it carries
no return or revert data):

* `events = []`. This is canonical only for families without external calls
  or payments (`transfer`, `send`, `tryCall` produce session events); for
  other families this language is not their canonical one.
* Source success is `Outcome.success []`; every source revert class (bare
  revert, panic, revert with data) is `Outcome.revert []`, as the compiler's
  own agreement maps a panic to a bare target `REVERT`. Revert data is not
  observed (G38).
* Depth exhaustion (a resource failure at that horizon) and divergence are
  unfinished prefixes.
* Target `.ok _ 0` is success and `.revert` is revert; `.fault` (including a
  non-terminating loop) and `.ok _ (k+1)` (a pending jump, not a frame exit)
  are unfinished.

The typed states, `StateRepr`, stack, allocator and frame words are NOT
observed; they are retained only in a bridge's `Local` conclusion.
The source language needs depth consistency, a real per-family fact, so it
takes that proof as an argument. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.P1Lang
open Evm Evm.Memory
open Solidity.Roadmap (Event Outcome Prefix Lang Prefixes)

/-- One P1 input: exactly the arguments of `InterfaceV1.Entry`. -/
structure Input (C : Contract) (Γ : Ctx) where
  L : Nat
  frame : Nat
  caller : State C Γ
  base : Nat → Fin W
  machine : Machine
  start : Nat

/-- Membership of an input in an admission predicate. -/
def Input.In {C : Contract} {Γ : Ctx} (admitted : InterfaceV3.Admission C Γ) (e : Input C Γ) :
    Prop :=
  admitted e.L e.frame e.caller e.base e.machine e.start

/-- Frame-boundary observation of a source run. -/
def sourcePrefix {C : Contract} {Δ : Ctx} {H : HTy}
    (r : TRes (Solidity.Out C H Δ)) : Prefix Event Outcome :=
  match r with
  | .ok _ => ⟨[], some (.success [])⟩
  | .error .revert | .error .panic | .error (.revertWith _) => ⟨[], some (.revert [])⟩
  | .error .exhausted | .error .diverge => ⟨[], none⟩

/-- Frame-boundary observation of a target run. -/
def targetPrefix (r : Evm.Out) : Prefix Event Outcome :=
  match r with
  | .ok _ 0 => ⟨[], some (.success [])⟩
  | .ok _ (_ + 1) => ⟨[], none⟩
  | .revert => ⟨[], some (.revert [])⟩
  | .fault => ⟨[], none⟩

/-- The source observation family of a context. -/
def sourceSem {C : Contract} {Γ Δ : Ctx} (source : Nat → Stmt C Γ Δ) (e : Input C Γ) :
    Prefixes Nat Event Outcome :=
  fun n => sourcePrefix ((source n).run e.caller)

/-- The canonical source language of one P1 context. -/
def sourceLang {C : Contract} {Γ Δ : Ctx} (source : Nat → Stmt C Γ Δ)
    (allowed : InterfaceV3.Admission C Γ)
    (consistent : ∀ e : Input C Γ, Prefixes.Consistent (sourceSem source e)) :
    Lang Event Outcome where
  Prog := Unit
  Env := Input C Γ
  Res := Nat
  resLE := inferInstanceAs (LE Nat)
  Allowed := Input.In allowed
  Admissible := fun _ => True
  sem := fun _ e => sourceSem source e
  consistent := fun _ e => consistent e

/-- The canonical target language of one emitted code image. -/
def targetLang {C : Contract} {Γ : Ctx} (code : List Instr) (allowed : InterfaceV3.Admission C Γ) :
    Lang Event Outcome where
  Prog := Unit
  Env := Input C Γ
  Res := Unit
  resLE := ⟨fun _ _ => True⟩
  Allowed := Input.In allowed
  Admissible := fun _ => True
  sem := fun _ e _ => targetPrefix (Evm.run code e.machine)
  consistent := fun _ _ _ _ _ => Prefix.Le.refl _

end Solidity.Backend.InternalFlow.RuntimeFrame.P1Lang
