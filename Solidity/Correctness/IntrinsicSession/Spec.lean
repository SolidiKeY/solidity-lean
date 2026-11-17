import Solidity.Correctness.IntrinsicSession.Run
import Solidity.Goals.IntrinsicSession
import Solidity.Semantics.IntrinsicStorage.Preimages.Calls

/-!
# The intrinsic session: hash accounting and the concrete `IntrinsicSpec`

Definitions for the concrete intrinsic session semantics (H556 option A, plan
step `is0e-session-spec`); nothing here is a goal. The path is under
`Solidity/Correctness` for the reason `Step.lean` states.

* **A session start** (`Start`) is the code of a compilation
  (`Solidity.Goals.IntrinsicSession.Code`) with the world its sessions start
  from: `fresh`, or a typed world at a transaction boundary. `runOf` is `run`
  of `Run.lean` at that code's catalog.
* **The response table is empty** (`wire`): the laws read a typed world as its
  code and world alone, so the ABI reading cannot vary with the world, and no
  finite reading lists every key. Every frame therefore runs with `ext := []`;
  a body that leaves its contract reads no answer (H720).
* **The inputs of a frame** (`Frame.inputs`) are those of
  `IntrinsicStorage.Frame.call` / `Frame.create` at the frame's recorded
  arguments, at a fuel that completes the observation (`Frame.CompletesAt`:
  the observed result is not `diverge`, so it is the actual frame result,
  `Frame.inputs_call` / `Frame.inputs_create`). A reverting frame, caught or
  not, completes and keeps its inputs. A frame no fuel completes diverges: it
  shows no event, stops the session, and contributes no input.
* **The preimages of a session prefix**: `slotHashed` is the slot preimages
  `IntrinsicStorage.stored` of the world the run resumes from (none for a
  fresh start: nothing is deployed), then the `slots` of every executed frame
  in order; `hashed` is the same with each frame's `hashed` (its slots, then
  its ordinary preimages). Both are concrete encoded preimages; no ideal slot
  term occurs. `slotHashed_sub` and prefix monotonicity in the bound
  (`hashed_mono`, `slotHashed_mono`, from `frames_mono`) hold by construction.
* **`lang`** and **`spec`**: the language of session starts over `SessionEnv`
  and `Bound`, with `Forward` and `Guard` pinned as `Roadmap.IntrinsicSpec`
  asks; the listed worlds are the boundary worlds of `run`, each as the start
  that resumes there.
-/

namespace Solidity.Semantics.IntrinsicSession

open Solidity.Roadmap
open Solidity.Goals.IntrinsicSession (Code)
open Solidity.ContractWorld (World Handle Entry Context)

/-! ## Frame inputs -/

section FrameInputs

variable {K : Type} [DecidableEq K] {contracts : K → Contract}

/-- The inputs the frame's observer shows at the fuel `n`. -/
noncomputable def Frame.inputsAt (f : Frame contracts) (n : Nat) : IntrinsicStorage.Inputs :=
  match f.body with
  | .call r entry => (IntrinsicStorage.Frame.call n f.world r entry f.ctx).inputs
  | .create k self ctor => (IntrinsicStorage.Frame.create n f.world k self ctor f.ctx).inputs

/-- The fuel `n` completes the frame: its observation is not cut short. -/
def Frame.CompletesAt (f : Frame contracts) (n : Nat) : Prop :=
  match f.body with
  | .call r entry =>
    (IntrinsicStorage.Frame.call n f.world r entry f.ctx).result ≠ .error .diverge
  | .create k self ctor =>
    (IntrinsicStorage.Frame.create n f.world k self ctor f.ctx).result ≠ .error .diverge

open Classical in
/-- **The inputs of an executed frame**: those its observer shows at a fuel
that completes it; none when no fuel does (the frame diverges). -/
noncomputable def Frame.inputs (f : Frame contracts) : IntrinsicStorage.Inputs :=
  if done : ∃ n, f.CompletesAt n then f.inputsAt (Classical.choose done) else {}

/-- A frame some fuel completes has the inputs of a completing fuel. -/
theorem Frame.inputs_of {f : Frame contracts} (done : ∃ n, f.CompletesAt n) :
    ∃ n, f.CompletesAt n ∧ f.inputs = f.inputsAt n :=
  ⟨Classical.choose done, Classical.choose_spec done, by simp only [Frame.inputs, done, dite_true]⟩

/-- A call frame some fuel completes has the inputs of an observation whose
result is the actual `World.call`. -/
theorem Frame.inputs_call {w : World contracts} {k : K} {r : Handle k}
    {entry : Entry (contracts k) Bytes} {ctx : Context}
    (done : ∃ n, (IntrinsicStorage.Frame.call n w r entry ctx).result ≠ .error .diverge) :
    ∃ n, (IntrinsicStorage.Frame.call n w r entry ctx).result = w.call r entry ctx ∧
      (⟨w, .call r entry, ctx⟩ : Frame contracts).inputs =
        (IntrinsicStorage.Frame.call n w r entry ctx).inputs :=
  let ⟨n, completes, eq⟩ := Frame.inputs_of (f := ⟨w, .call r entry, ctx⟩) done
  ⟨n, (IntrinsicStorage.Frame.call_approx n w r entry ctx).eq completes, eq⟩

/-- A create frame some fuel completes has the inputs of an observation whose
result is the actual `World.create`. -/
theorem Frame.inputs_create {w : World contracts} {k : K} {self : ContractWorld.Address}
    {ctor : Prog (contracts k) [] []} {ctx : Context}
    (done : ∃ n, (IntrinsicStorage.Frame.create n w k self ctor ctx).result ≠ .error .diverge) :
    ∃ n, (IntrinsicStorage.Frame.create n w k self ctor ctx).result = w.create k self ctor ctx ∧
      (⟨w, .create k self ctor, ctx⟩ : Frame contracts).inputs =
        (IntrinsicStorage.Frame.create n w k self ctor ctx).inputs :=
  let ⟨n, completes, eq⟩ := Frame.inputs_of (f := ⟨w, .create k self ctor, ctx⟩) done
  ⟨n, (IntrinsicStorage.Frame.create_approx n w k self ctor ctx).eq completes, eq⟩

end FrameInputs

/-! ## Session starts and their runs -/

/-- Where the sessions of a compilation start: its code, and nothing deployed
or a typed world at a transaction boundary. -/
structure Start where
  code : Code
  world : SessionWorld code.contracts

/-- The empty ABI reading: no key, so every frame's response table is empty.
The two readings are never applied. -/
def wire : Wire := ⟨[], fun _ => .reentered (.revert []), fun _ => .other []⟩

/-- No answer reaches a frame. -/
theorem responses_wire (e : SessionEnv) (h : List Event) : responses wire e h = [] := rfl

/-- **The run of a session start**: `run` at its code's catalog. -/
noncomputable def runOf (F : Fixed) (x : Start) (e : SessionEnv) (r : Bound) :
    Run x.code.contracts :=
  run x.code.main x.code.roles x.code.ctor x.code.entry F wire x.world e r

/-! ## Hash accounting -/

/-- The slot preimages of the keys the resumed world stores; a fresh start
resumes nothing. -/
noncomputable def Start.stored (x : Start) : List Bytes :=
  match x.world with
  | .fresh => []
  | .boundary w => IntrinsicStorage.stored w

/-- **The slot preimages of a session prefix**: those of the resumed world,
then the slots of every executed frame, in order. -/
noncomputable def slotHashed (F : Fixed) (x : Start) (e : SessionEnv) (r : Bound) : List Bytes :=
  x.stored ++ (runOf F x e r).frames.flatMap fun f => f.inputs.slots

/-- **The preimages of a session prefix**: the slot preimages of the resumed
world, then everything every executed frame hashed, in order. -/
noncomputable def hashed (F : Fixed) (x : Start) (e : SessionEnv) (r : Bound) : List Bytes :=
  x.stored ++ (runOf F x e r).frames.flatMap fun f => f.inputs.hashed

variable {F : Fixed} {x : Start} {e : SessionEnv} {r r' : Bound}

/-- The resumed world's keys are accounted for at every bound. -/
theorem stored_slotHashed {b : Bytes} (mem : b ∈ x.stored) : b ∈ slotHashed F x e r :=
  List.mem_append_left _ mem

/-- An executed frame's slots are slot preimages of the session. -/
theorem frame_slotHashed {f : Frame (catalog x.code.contracts)} {b : Bytes}
    (ran : f ∈ (runOf F x e r).frames) (mem : b ∈ f.inputs.slots) : b ∈ slotHashed F x e r :=
  List.mem_append_right _ (List.mem_flatMap.2 ⟨f, ran, mem⟩)

/-- Everything an executed frame hashed is a preimage of the session. -/
theorem frame_hashed {f : Frame (catalog x.code.contracts)} {b : Bytes}
    (ran : f ∈ (runOf F x e r).frames) (mem : b ∈ f.inputs.hashed) : b ∈ hashed F x e r :=
  List.mem_append_right _ (List.mem_flatMap.2 ⟨f, ran, mem⟩)

/-- **The slot preimages are among the preimages.** -/
theorem slotHashed_sub {b : Bytes} (mem : b ∈ slotHashed F x e r) : b ∈ hashed F x e r := by
  rcases List.mem_append.1 mem with stored | framed
  · exact List.mem_append_left _ stored
  · obtain ⟨f, ran, slot⟩ := List.mem_flatMap.1 framed
    exact frame_hashed ran (f.inputs.slot_hashed slot)

/-- Longer frame lists extend what the frames account for. -/
theorem flatMap_prefix {α β : Type} {xs ys : List α} (g : α → List β) (le : xs <+: ys) :
    xs.flatMap g <+: ys.flatMap g := by
  obtain ⟨zs, rfl⟩ := le
  rw [List.flatMap_append]
  exact List.prefix_append _ _

/-- **A larger bound extends the slot preimages.** -/
theorem slotHashed_mono (le : r ≤ r') : slotHashed F x e r <+: slotHashed F x e r' :=
  (List.prefix_append_right_inj _).2 (flatMap_prefix _ (frames_mono _ _ _ _ F wire x.world e le))

/-- **A larger bound extends the preimages.** -/
theorem hashed_mono (le : r ≤ r') : hashed F x e r <+: hashed F x e r' :=
  (List.prefix_append_right_inj _).2 (flatMap_prefix _ (frames_mono _ _ _ _ F wire x.world e le))

/-! ## The language and the spec -/

/-- **The intrinsic session language**: session starts in session
environments at bounds; the prefix of `run`. `Forward` is the runs without
resource failure hashing fewer than `hashBound` distinct preimages, `Guard`
the hash premise on the run's own preimages. -/
noncomputable def lang (F : Fixed) : Lang Event Outcome where
  Prog := Start
  Env := SessionEnv
  Res := Bound
  resLE := inferInstance
  Allowed := SessionEnv.Allowed
  Admissible := Bound.Admissible
  sem x e r := (runOf F x e r).pfx
  consistent x e := run_consistent x.code.main x.code.roles x.code.ctor x.code.entry F wire x.world e
  Forward x e r := r.NoFail ∧ distinctCount (hashed F x e r) < hashBound
  Guard x e r := HashPremise F (hashed F x e r) (slotHashed F x e r)

/-- **The concrete intrinsic session semantics** over the fixed parameters
`F`. Its worlds are session starts; a prefix lists the boundary worlds of its
run, each as the start resuming there. -/
noncomputable def spec (F : Fixed) : IntrinsicSpec where
  World := Start
  lang := lang F
  ofWorld x := x
  worlds x e r := (runOf F x e r).worlds.map fun w => ⟨x.code, .boundary w⟩
  fixed := F
  session e := e
  ofSession e := e
  session_of _ := rfl
  of_session _ := rfl
  allowed_iff _ := Iff.rfl
  NoFail := Bound.NoFail
  hashed := hashed F
  slotHashed := slotHashed F
  forward_iff _ _ _ := Iff.rfl
  guard_iff _ _ _ := Iff.rfl

/-- A larger bound extends the listed worlds. -/
theorem worlds_consistent (le : r ≤ r') : (spec F).worlds x e r <+: (spec F).worlds x e r' :=
  (worlds_mono _ _ _ _ F wire x.world e le).map _

end Solidity.Semantics.IntrinsicSession
