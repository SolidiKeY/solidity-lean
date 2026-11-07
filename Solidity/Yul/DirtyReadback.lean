import Solidity.Yul.RawBoundary
import Solidity.Yul.CleanFunctions

/-! **Readback of dirty LOCAL words** (user decision H109, 2026-11-06).

An assembly block may leave a dirty word (high bits set) in a narrow integer
or `bool` Solidity local. Every Solidity-level read of the local afterwards
sees it cleaned, the same way in both pinned pipelines (solc 0.8.38,
optimizer off; `tests/evm-reference/dirty-locals.json`, produced by
`scripts/evm-reference/dirty-locals.mjs`, 33 probes):

- `uintN`: the low `N` bits (`u8_eq`, `u8_checked_add` (`0x1fe + 1` is
  `255`), `u8_div`, `u8_lt`, `u8_shr`, `u8_store`, `u16_widen`, `u32_widen`);
- `intN`: the low `N` bits sign-extended (`i8_widen_neg` (`0x80` is `-128`),
  `i8_widen_pos` (`0x17f` is `127`), `i8_eq_neg1` (`0x1ff == -1`), `i8_lt`,
  `i8_div`, `i16_widen` (`0x18000` is `-32768`));
- `bool`: true exactly when the word is not zero (`b_eq_true`, `b_eq_b`,
  `b_ne_false`, `b_and`, `b_if`, `b_store` stores `1`).

**Limit.** solc cleans lazily, at each use; the stack slot keeps the dirty
word. A later assembly read of the local, or of a Solidity copy of it
(`uint8 y = x;`), sees the raw word (`u8_asm_direct`, `b_asm_direct`,
`u8_asm_reread`). This readback drops the raw bits, so it agrees with solc
exactly when no later assembly block reads the local (or a copy) before it
is rewritten; the raw frame (`RawFrame.State`) keeps every bit for that
case. The explicit `evalLocal` boundary below invokes actual Source local
read evaluation on a prepared view and retains the original raw frame. The
ordinary Source evaluator does not automatically consult raw frames; arbitrary
Source code and raw-word propagation through copies are not integrated here. (Unchecked narrow arithmetic results are a separate, recorded pipeline
difference, H3: `u8_unchecked_add_widen`.)

Source values stay intrinsic and no assembly write cleans. Any other type a
raw word can hold (addresses, `bytesN`, enums, user-defined value types,
contracts, fixed point, external function values) is not cleaned here: a
dirty local of such a type is refused (`none`), as `LocalValues.clean?`
refuses. `RawCoherent.coherent` keeps reporting a dirty frame as
incoherent: coherence is about reusing the clean backup without decoding,
and this readback is the explicit cleaning boundary. -/
namespace Solidity.Yul.DirtyReadback

open Solidity.Source (STy Locals)

abbrev Pipeline := LocalOperations.Pipeline

/-- **solc's cleanup of a dirty word read as type `ty`**: an integer wrapped
into its width (mask, or sign extension from bit `N-1`), a `bool` true when
the word is not zero; any other type is refused. Both pipelines clean the
same way (evidence above). -/
def cleanWord {D : Solidity.Source.Layout} : Pipeline → (ty : STy) → Word → Option (Solidity.Source.Val D ty)
  | .legacy, .int t, w | .viaIR, .int t, w => some (Solidity.Source.intWrap t (w.val : Int))
  | .legacy, .bool, w | .viaIR, .bool, w => some (.bool (w.val != 0))
  | _, _, _ => none

/-- A local read back: a clean value as it is, a raw scalar word cleaned by
`cleanWord`, anything else refused. -/
def readValue {env : Solidity.Source.Env} {ty : STy} (pipeline : Pipeline)
    (value : LocalValue env ty) : Option (Solidity.Source.Val env.layout ty) :=
  match value.clean? with
  | some v => some v
  | none =>
    match value.scalar? with
    | some w => cleanWord pipeline ty w
    | none => none

/-- **The readback of LOCAL values into Source locals**: every local read
back (`readValue`), or `none` when one is refused. -/
def readback {env : Solidity.Source.Env} (pipeline : Pipeline) :
    (ctx : Solidity.Source.RCtx) → LocalValues env ctx → Option (Locals env.layout ctx)
  | [], _ => some .nil
  | _ :: ctx, locals => do
      let value ← readValue pipeline locals.1
      let rest ← readback pipeline ctx locals.2
      pure (.cons value rest)

/-- The raw fields of an external function local holding raw ones. -/
def functionFields? {env : Solidity.Source.Env} {ty : STy} (value : LocalValue env ty) :
    Option (Word × Word) := by
  apply LocalValue.casesOn (motive := fun _ _ => Option (Word × Word)) value
  case clean => intro ty clean; exact none
  case scalar => intro ty encoding shape raw; exact none
  case externalFunction => intro params rets mutability address selector; exact some (address, selector)

/-- Whether a raw local holds exactly the words of a clean value: a local the
assembly block left untouched (or rewrote with the same words). -/
def unchanged {env : Solidity.Source.Env} {ty : STy} (value : LocalValue env ty)
    (backup : Solidity.Source.Val env.layout ty) : Bool :=
  match value.scalar? with
  | some w => decide (backup.word = some w)
  | none =>
    match functionFields? value with
    | some fields => decide (cleanFunctionFields backup = some fields)
    | none => false

/-- A local of a raw frame read back against its clean backup: read back
(`readValue`) when it can be; otherwise the backup when the local is
unchanged; otherwise refused (a dirty word of a type solc's cleanup here
does not cover). -/
def readLocal {env : Solidity.Source.Env} {ty : STy} (pipeline : Pipeline) (value : LocalValue env ty)
    (backup : Solidity.Source.Val env.layout ty) : Option (Solidity.Source.Val env.layout ty) :=
  match readValue pipeline value with
  | some v => some v
  | none => if unchanged value backup then some backup else none

/-- `readLocal` for every local, against the clean backup. -/
def readbackFrom {env : Solidity.Source.Env} (pipeline : Pipeline) :
    (ctx : Solidity.Source.RCtx) → LocalValues env ctx → Locals env.layout ctx →
      Option (Locals env.layout ctx)
  | [], _, _ => some .nil
  | _ :: ctx, values, .cons backup rest => do
      let value ← readLocal pipeline values.1 backup
      let tail ← readbackFrom pipeline ctx values.2 rest
      pure (.cons value tail)

/-- A clean local reads back as it is, against any backup. -/
theorem readLocal_clean {env : Solidity.Source.Env} {ty : STy} (pipeline : Pipeline)
    (v backup : Solidity.Source.Val env.layout ty) :
    readLocal pipeline (LocalValue.clean (env := env) v) backup = some v := rfl

/-- **Clean locals read back unchanged against any backup.** -/
theorem readbackFrom_ofClean {env : Solidity.Source.Env} (pipeline : Pipeline) :
    ∀ {ctx : Solidity.Source.RCtx} (locals backup : Locals env.layout ctx),
      readbackFrom pipeline ctx (LocalValues.ofClean locals) backup = some locals
  | [], .nil, .nil => rfl
  | _ :: _, .cons v rest, .cons b brest => by
    show (do let x ← readLocal pipeline (LocalValue.clean v) b
             let t ← readbackFrom pipeline _ (LocalValues.ofClean rest) brest
             pure (Locals.cons x t)) = _
    rw [readLocal_clean, readbackFrom_ofClean pipeline rest brest]
    rfl

/-- **The readback of a raw LOCAL frame** after an assembly block: its
authoritative words (`RawFrame.materialize`) read back into Source locals
against the frame's clean backup, with the frame's world. A dirty narrow
integer or `bool` local is cleaned as solc cleans it; an untouched local
keeps its clean value; a dirty local of any other type refuses the frame. -/
def frame {ctx : Solidity.Source.Ctx} (pipeline : Pipeline) (state : RawFrame.State ctx) :
    Option (Locals ctx.env.layout ctx.tys × Solidity.Source.St ctx.env) :=
  (readbackFrom pipeline ctx.tys (RawFrame.materialize state).1 state.clean).map (·, state.world)

/-- Clean only the selected intrinsic local against its existing backup.
An unrelated dirty unsupported local cannot refuse this selected read. -/
def readAt {ctx : Solidity.Source.Ctx} {ty : STy} (pipeline : Pipeline)
    (state : RawFrame.State ctx) (index : Solidity.Source.Idx ctx.tys ty) :
    Option (Solidity.Source.Val ctx.env.layout ty) :=
  readLocal pipeline (LocalValues.get (RawFrame.materialize state).1 index)
    (state.clean.get index)

/-- Explicit Source local-read integration. The decoder follows the actual
Source global pipeline. A successful decode invokes the real evaluator with the
same global/frame/fuel/resource plan on a selected-local clean view. The full
Source result/state and the original authoritative raw frame are both returned.
None is an unsupported readback, distinct from a Source timeout. This is not an
integration of arbitrary Source expressions/statements or raw-copy propagation. -/
def evalLocal {ctx : Solidity.Source.Ctx} {ty : STy}
    (G : Solidity.Source.Glob ctx.env) (F : Solidity.Source.Fr) (fuel : Nat)
    (state : RawFrame.State ctx) (index : Solidity.Source.Idx ctx.tys ty)
    (plan : Solidity.Source.FailureExecution.RuntimePlan := none) :
    Option ((Solidity.Source.R (Solidity.Source.RVal ctx.env.layout ty) ×
      Solidity.Source.EMState ctx.env ctx.tys) × RawFrame.State ctx) :=
  (readAt G.pipeline state index).map fun value =>
    ((Solidity.Source.evalE G F fuel (.local index) plan).run
      (state.clean.set index value, state.world), state)

/-! ## Laws -/

/-- An integer word reads back wrapped into its type. -/
theorem cleanWord_int {D : Solidity.Source.Layout} (pipeline : Pipeline) (t : Solidity.Source.IntTy)
    (w : Word) : cleanWord (D := D) pipeline (.int t) w =
      some (Solidity.Source.intWrap t (w.val : Int)) := by
  cases pipeline <;> rfl

/-- A `bool` word reads back true exactly when it is not zero. -/
theorem cleanWord_bool {D : Solidity.Source.Layout} (pipeline : Pipeline) (w : Word) :
    cleanWord (D := D) pipeline .bool w = some (.bool (w.val != 0)) := by
  cases pipeline <;> rfl

/-- The two pipelines read back alike. -/
theorem cleanWord_pipelines {D : Solidity.Source.Layout} (ty : STy) (w : Word) :
    cleanWord (D := D) .legacy ty w = cleanWord (D := D) .viaIR ty w := by
  cases ty <;> rfl

/-- A clean value reads back as it is. -/
theorem readValue_clean {env : Solidity.Source.Env} {ty : STy} (pipeline : Pipeline)
    (v : Solidity.Source.Val env.layout ty) : readValue pipeline (LocalValue.clean (env := env) v) = some v := rfl

/-- **Clean locals read back unchanged** (the readback extends
`LocalValues.clean?`). -/
theorem readback_ofClean {env : Solidity.Source.Env} (pipeline : Pipeline) {ctx : Solidity.Source.RCtx}
    (locals : Locals env.layout ctx) :
    readback pipeline ctx (LocalValues.ofClean locals) = some locals := by
  induction locals with
  | nil => rfl
  | cons value rest ih =>
    show (do let v ← readValue pipeline (LocalValue.clean value)
             let r ← readback pipeline _ (LocalValues.ofClean rest); pure (Locals.cons v r)) = _
    rw [ih]
    rfl

/-- **Wherever the old projection succeeds, the readback agrees**: an
all-clean frame is not decoded differently. -/
theorem readback_of_clean? {env : Solidity.Source.Env} (pipeline : Pipeline) :
    ∀ (ctx : Solidity.Source.RCtx) (values : LocalValues env ctx) (locals : Locals env.layout ctx),
      LocalValues.clean? ctx values = some locals → readback pipeline ctx values = some locals
  | [], _, locals, h => by cases locals; rfl
  | ty :: ctx, values, locals, h => by
    simp only [LocalValues.clean?, Option.bind_eq_bind] at h
    cases hv : values.1.clean? with
    | none => rw [hv] at h; cases h
    | some v =>
      rw [hv] at h
      cases hr : LocalValues.clean? ctx values.2 with
      | none => rw [hr] at h; cases h
      | some rest =>
        rw [hr] at h
        cases h
        simp only [readback, readValue, hv, readback_of_clean? pipeline ctx values.2 rest hr]
        rfl

/-- The `uint8` readback is the existing canonical return projection
(`RawFrame.returnU8`'s numeric reading, `RawFrame.U8ReturnD`). -/
theorem cleanWord_u8_key {D : Solidity.Source.Layout} (pipeline : Pipeline) (w : Word) :
    ((cleanWord (D := D) pipeline (.int Solidity.Source.IntTy.u8) w).map Solidity.Source.Val.key) =
      some (some (Solidity.Source.IntTy.u8.wrap (w.val : Int))) := by
  cases pipeline <;> rfl

/-- The actual intrinsic Source local selected by a typed index reads back
the value prepared at that index, for every local type and position. -/
theorem locals_get_set :
 ∀ (D : Solidity.Source.Layout) (types : Solidity.Source.RCtx) (ty : Solidity.Source.STy)
 (index : Solidity.Source.Idx types ty) (locals : Solidity.Source.Locals D types)
 (value : Solidity.Source.Val D ty), (locals.set index value).get index = value := by
  intro D types ty index
  induction index with
  | here => intro locals value; cases locals; rfl
  | there previous ih =>
    intro locals value
    cases locals with
    | cons head tail => exact ih tail value


/-- An unsupported selected readback remains none, rather than a fabricated Source halt. -/
theorem evalLocal_refused :
 ∀ (ctx : Solidity.Source.Ctx) (ty : Solidity.Source.STy)
 (G : Solidity.Source.Glob ctx.env) (F : Solidity.Source.Fr) (fuel : Nat)
 (state : Solidity.Yul.RawFrame.State ctx) (index : Solidity.Source.Idx ctx.tys ty)
 (plan : Solidity.Source.FailureExecution.RuntimePlan), Solidity.Yul.DirtyReadback.readAt G.pipeline state index = none → Solidity.Yul.DirtyReadback.evalLocal G F fuel state index plan = none := by
  intros ctx ty G F fuel state index plan refused
  unfold Solidity.Yul.DirtyReadback.evalLocal
  rw [refused]
  rfl

/-- Zero fuel preserves the actual Source timeout and prepared Source state, distinct from unsupported readback. -/
theorem evalLocal_zero :
 ∀ (ctx : Solidity.Source.Ctx) (ty : Solidity.Source.STy)
 (G : Solidity.Source.Glob ctx.env) (F : Solidity.Source.Fr)
 (state : Solidity.Yul.RawFrame.State ctx) (index : Solidity.Source.Idx ctx.tys ty)
 (plan : Solidity.Source.FailureExecution.RuntimePlan), Solidity.Yul.DirtyReadback.evalLocal G F 0 state index plan =
 (Solidity.Yul.DirtyReadback.readAt G.pipeline state index).map (fun value =>
 ((.error .timeout, (state.clean.set index value, state.world)), state)) := by
  intros; rfl

/-- A decoded selected local is read by actual Source evaluation at every positive horizon, with the full Source state and original raw frame. -/
theorem evalLocal_success :
 ∀ (ctx : Solidity.Source.Ctx) (ty : Solidity.Source.STy)
 (G : Solidity.Source.Glob ctx.env) (F : Solidity.Source.Fr) (fuel : Nat)
 (state : Solidity.Yul.RawFrame.State ctx) (index : Solidity.Source.Idx ctx.tys ty)
 (plan : Solidity.Source.FailureExecution.RuntimePlan), ∀ (value : Solidity.Source.Val ctx.env.layout ty),
 Solidity.Yul.DirtyReadback.readAt G.pipeline state index = some value → Solidity.Yul.DirtyReadback.evalLocal G F (fuel+1) state index plan =
 some ((.ok (.val value), (state.clean.set index value, state.world)), state) := by
  intros ctx ty G F fuel state index plan value decoded
  unfold Solidity.Yul.DirtyReadback.evalLocal
  rw [decoded]
  change some (((Except.ok (Solidity.Source.RVal.val ((state.clean.set index value).get index)) :
      Solidity.Source.R (Solidity.Source.RVal ctx.env.layout ty)),
    (state.clean.set index value, state.world)), state) = _
  rw [Solidity.Yul.DirtyReadback.locals_get_set]

/-- The explicit Source read never rewrites the authoritative raw frame, including dirty bits and overlay metadata. -/
theorem evalLocal_raw :
 ∀ (ctx : Solidity.Source.Ctx) (ty : Solidity.Source.STy)
 (G : Solidity.Source.Glob ctx.env) (F : Solidity.Source.Fr) (fuel : Nat)
 (state : Solidity.Yul.RawFrame.State ctx) (index : Solidity.Source.Idx ctx.tys ty)
 (plan : Solidity.Source.FailureExecution.RuntimePlan), (Solidity.Yul.DirtyReadback.evalLocal G F fuel state index plan).map Prod.snd = (Solidity.Yul.DirtyReadback.readAt G.pipeline state index).map (fun _ => state) := by
  intros ctx ty G F fuel state index plan
  unfold Solidity.Yul.DirtyReadback.evalLocal
  rw [Option.map_map]
  rfl

/-- Preparing a typed local with its existing value preserves the entire Source local environment. -/
theorem locals_set_get :
 ∀ (D : Solidity.Source.Layout) (types : Solidity.Source.RCtx) (ty : Solidity.Source.STy)
(index : Solidity.Source.Idx types ty) (locals : Solidity.Source.Locals D types),
locals.set index (locals.get index) = locals := by
  intro D types ty index
  induction index with
  | here => intro locals; cases locals; rfl
  | there previous ih =>
    intro locals
    cases locals with
    | cons head tail => exact congrArg (Solidity.Source.Locals.cons head) (ih tail)

/-- Readback admission depends only on the selected decoder, not Source fuel or runtime plan. A Source timeout is still an admitted result. -/
theorem evalLocal_readable :
 ∀ (ctx : Solidity.Source.Ctx) (ty : Solidity.Source.STy)
(G : Solidity.Source.Glob ctx.env) (F : Solidity.Source.Fr) (fuel : Nat)
(state : Solidity.Yul.RawFrame.State ctx) (index : Solidity.Source.Idx ctx.tys ty)
(plan : Solidity.Source.FailureExecution.RuntimePlan),
(Solidity.Yul.DirtyReadback.evalLocal G F fuel state index plan).isSome =
(Solidity.Yul.DirtyReadback.readAt G.pipeline state index).isSome := by
  intros
  unfold Solidity.Yul.DirtyReadback.evalLocal
  cases Solidity.Yul.DirtyReadback.readAt _ _ _ <;> rfl

/-- Whenever selected decoding equals the existing backup, the explicit boundary
agrees with ordinary Source local evaluation on the original complete Source state,
at every fuel and runtime plan. This is a conditional compatibility theorem, not
an assertion that all dirty values decode to their backups. -/
theorem evalLocal_compatible :
 ∀ (ctx : Solidity.Source.Ctx) (ty : Solidity.Source.STy)
(G : Solidity.Source.Glob ctx.env) (F : Solidity.Source.Fr) (fuel : Nat)
(state : Solidity.Yul.RawFrame.State ctx) (index : Solidity.Source.Idx ctx.tys ty)
(plan : Solidity.Source.FailureExecution.RuntimePlan),
Solidity.Yul.DirtyReadback.readAt G.pipeline state index = some (state.clean.get index) →
Solidity.Yul.DirtyReadback.evalLocal G F fuel state index plan =
some (((Solidity.Source.evalE G F fuel (.local index) plan).run
(state.clean, state.world)), state) := by
  intros ctx ty G F fuel state index plan decoded
  unfold Solidity.Yul.DirtyReadback.evalLocal
  rw [decoded]
  change some (((Solidity.Source.evalE G F fuel (.local index) plan).run
    (state.clean.set index (state.clean.get index), state.world)), state) = _
  rw [Solidity.Yul.DirtyReadback.locals_set_get]

/-- Both pinned pipelines agree on this complete optional readback, including refusal. No Source execution agreement is inferred. -/
theorem readValue_pipelines :
 ∀ (env : Solidity.Source.Env) (ty : Solidity.Source.STy) (value : Solidity.Yul.LocalValue env ty),
Solidity.Yul.DirtyReadback.readValue .legacy value = Solidity.Yul.DirtyReadback.readValue .viaIR value := by
  intros
  simp only [Solidity.Yul.DirtyReadback.readValue, Solidity.Yul.DirtyReadback.cleanWord_pipelines]

/-- Both pinned pipelines agree on this complete optional readback, including refusal. No Source execution agreement is inferred. -/
theorem readLocal_pipelines :
 ∀ (env : Solidity.Source.Env) (ty : Solidity.Source.STy) (value : Solidity.Yul.LocalValue env ty)
(backup : Solidity.Source.Val env.layout ty),
Solidity.Yul.DirtyReadback.readLocal .legacy value backup = Solidity.Yul.DirtyReadback.readLocal .viaIR value backup := by
  intros
  simp only [Solidity.Yul.DirtyReadback.readLocal, Solidity.Yul.DirtyReadback.readValue_pipelines]

/-- Both pinned pipelines agree on this complete optional readback, including refusal. No Source execution agreement is inferred. -/
theorem readback_pipelines :
 ∀ (env : Solidity.Source.Env) (types : Solidity.Source.RCtx) (values : Solidity.Yul.LocalValues env types),
Solidity.Yul.DirtyReadback.readback .legacy types values = Solidity.Yul.DirtyReadback.readback .viaIR types values := by
  intro env types
  induction types with
  | nil => intro values; rfl
  | cons ty types ih =>
    intro values
    simp only [Solidity.Yul.DirtyReadback.readback, Solidity.Yul.DirtyReadback.readValue_pipelines, ih]

/-- Both pinned pipelines agree on this complete optional readback, including refusal. No Source execution agreement is inferred. -/
theorem readbackFrom_pipelines :
 ∀ (env : Solidity.Source.Env) (types : Solidity.Source.RCtx)
(backup : Solidity.Source.Locals env.layout types) (values : Solidity.Yul.LocalValues env types),
Solidity.Yul.DirtyReadback.readbackFrom .legacy types values backup =
Solidity.Yul.DirtyReadback.readbackFrom .viaIR types values backup := by
  intro env types backup
  induction backup with
  | nil => intro values; rfl
  | cons value rest ih =>
    intro values
    simp only [Solidity.Yul.DirtyReadback.readbackFrom, Solidity.Yul.DirtyReadback.readLocal_pipelines, ih]

/-- Both pinned pipelines agree on this complete optional readback, including refusal. No Source execution agreement is inferred. -/
theorem readAt_pipelines :
 ∀ (ctx : Solidity.Source.Ctx) (ty : Solidity.Source.STy)
(state : Solidity.Yul.RawFrame.State ctx) (index : Solidity.Source.Idx ctx.tys ty),
Solidity.Yul.DirtyReadback.readAt .legacy state index = Solidity.Yul.DirtyReadback.readAt .viaIR state index := by
  intros
  exact Solidity.Yul.DirtyReadback.readLocal_pipelines _ _ _ _

/-- Changing only the global pipeline preserves the full explicit selected-local
Source read, at every fuel and runtime plan. This is local-read agreement only;
it does not assert pipeline agreement for arbitrary Source expressions. -/
theorem evalLocal_pipelines :
 ∀ (ctx : Solidity.Source.Ctx) (ty : Solidity.Source.STy)
(G : Solidity.Source.Glob ctx.env) (F : Solidity.Source.Fr) (fuel : Nat)
(state : Solidity.Yul.RawFrame.State ctx) (index : Solidity.Source.Idx ctx.tys ty)
(plan : Solidity.Source.FailureExecution.RuntimePlan),
Solidity.Yul.DirtyReadback.evalLocal {G with pipeline := .legacy} F fuel state index plan =
Solidity.Yul.DirtyReadback.evalLocal {G with pipeline := .viaIR} F fuel state index plan := by
  intro ctx ty G F fuel state index plan
  cases fuel <;> unfold Solidity.Yul.DirtyReadback.evalLocal <;>
    rw [Solidity.Yul.DirtyReadback.readAt_pipelines] <;> rfl

/-- Selected readback depends on the authoritative word view and clean backup,
not the optional overlay's sparsity or world. The clean-backup premise matters
for unsupported locals and is retained explicitly. -/
theorem readAt_agrees :
 ∀ (ctx : Solidity.Source.Ctx) (ty : Solidity.Source.STy) (pipeline : Solidity.Yul.DirtyReadback.Pipeline)
(first second : Solidity.Yul.RawFrame.State ctx),
first.clean = second.clean → Solidity.Yul.RawFrame.view first = Solidity.Yul.RawFrame.view second →
∀ (index : Solidity.Source.Idx ctx.tys ty),
Solidity.Yul.DirtyReadback.readAt pipeline first index = Solidity.Yul.DirtyReadback.readAt pipeline second index := by
  intro ctx ty pipeline first second clean words index
  unfold Solidity.Yul.DirtyReadback.readAt Solidity.Yul.RawFrame.materialize
  rw [clean, words]

/-- Equal clean backups, worlds and authoritative word views produce identical full Source observations. Only the original raw-frame component is projected away; its metadata need not be equal. -/
theorem evalLocal_source_agrees :
 ∀ (ctx : Solidity.Source.Ctx) (ty : Solidity.Source.STy)
(G : Solidity.Source.Glob ctx.env) (F : Solidity.Source.Fr) (fuel : Nat)
(first second : Solidity.Yul.RawFrame.State ctx),
first.clean = second.clean → first.world = second.world →
Solidity.Yul.RawFrame.view first = Solidity.Yul.RawFrame.view second →
∀ (index : Solidity.Source.Idx ctx.tys ty) (plan : Solidity.Source.FailureExecution.RuntimePlan),
(Solidity.Yul.DirtyReadback.evalLocal G F fuel first index plan).map Prod.fst =
(Solidity.Yul.DirtyReadback.evalLocal G F fuel second index plan).map Prod.fst := by
  intro ctx ty G F fuel first second clean world words index plan
  unfold Solidity.Yul.DirtyReadback.evalLocal
  rw [Solidity.Yul.DirtyReadback.readAt_agrees ctx ty G.pipeline first second clean words, clean, world]
  cases Solidity.Yul.DirtyReadback.readAt G.pipeline second index <;> rfl

/-- Capturing the same complete word view preserves selected decoding, including refusal and clean-backup fallback. -/
theorem readAt_capture :
 ∀ (ctx : Solidity.Source.Ctx) (ty : Solidity.Source.STy) (pipeline : Solidity.Yul.DirtyReadback.Pipeline)
(state : Solidity.Yul.RawFrame.State ctx) (index : Solidity.Source.Idx ctx.tys ty),
Solidity.Yul.DirtyReadback.readAt pipeline (Solidity.Yul.RawFrame.capture state (Solidity.Yul.RawFrame.view state)) index =
Solidity.Yul.DirtyReadback.readAt pipeline state index := by
  intro ctx ty pipeline state index
  exact Solidity.Yul.DirtyReadback.readAt_agrees ctx ty pipeline _ state rfl
    (Solidity.Yul.RawFrame.view_capture state _) index

/-- Snapshot capture preserves the complete optional Source result/state at the selected-read boundary. The returned original raw frame is deliberately not equated. -/
theorem evalLocal_source_capture :
 ∀ (ctx : Solidity.Source.Ctx) (ty : Solidity.Source.STy)
(G : Solidity.Source.Glob ctx.env) (F : Solidity.Source.Fr) (fuel : Nat)
(state : Solidity.Yul.RawFrame.State ctx) (index : Solidity.Source.Idx ctx.tys ty)
(plan : Solidity.Source.FailureExecution.RuntimePlan),
(Solidity.Yul.DirtyReadback.evalLocal G F fuel
(Solidity.Yul.RawFrame.capture state (Solidity.Yul.RawFrame.view state)) index plan).map Prod.fst =
(Solidity.Yul.DirtyReadback.evalLocal G F fuel state index plan).map Prod.fst := by
  intro ctx ty G F fuel state index plan
  exact Solidity.Yul.DirtyReadback.evalLocal_source_agrees ctx ty G F fuel
    (Solidity.Yul.RawFrame.capture state (Solidity.Yul.RawFrame.view state)) state rfl rfl
    (Solidity.Yul.RawFrame.view_capture state _) index plan

/-- Generic residue law for the existing Source integer cleanup at every width and signedness. No new cleanup operation is defined. -/
theorem wrapBits_emod :
 ∀ (signed : Bool) (bits : Nat) (value : Int),
Solidity.Source.wrapBits signed bits value % ((2 ^ bits : Nat) : Int) =
value % ((2 ^ bits : Nat) : Int) := by
  intro signed bits value
  unfold Solidity.Source.wrapBits
  dsimp only
  split
  · rw [Int.sub_emod_right, Int.emod_emod]
  · rw [Int.emod_emod]

/-- Equal low-bit residues produce the same Source cleanup at every width and signedness. -/
theorem wrapBits_congr :
 ∀ (signed : Bool) (bits : Nat) (first second : Int),
first % ((2 ^ bits : Nat) : Int) = second % ((2 ^ bits : Nat) : Int) →
Solidity.Source.wrapBits signed bits first = Solidity.Source.wrapBits signed bits second := by
  intro signed bits first second residue
  unfold Solidity.Source.wrapBits
  dsimp only
  rw [residue]

/-- The existing Source integer cleanup is idempotent. No new cleanup operation is defined. -/
theorem wrapBits_idempotent :
 ∀ (signed : Bool) (bits : Nat) (value : Int),
Solidity.Source.wrapBits signed bits (Solidity.Source.wrapBits signed bits value) =
Solidity.Source.wrapBits signed bits value := by
  intro signed bits value
  exact Solidity.Yul.DirtyReadback.wrapBits_congr signed bits _ value
    (Solidity.Yul.DirtyReadback.wrapBits_emod signed bits value)

/-- Repeated integer wrapping preserves the full intrinsic Source value, not just its numeric key. -/
theorem intWrap_idempotent :
 ∀ (D : Solidity.Source.Layout) (ty : Solidity.Source.IntTy) (value : Int),
Solidity.Source.intWrap (D := D) ty (ty.wrap value) =
Solidity.Source.intWrap (D := D) ty value := by
  intro D ty value
  simp only [Solidity.Source.intWrap, Solidity.Source.IntTy.wrap,
    Solidity.Yul.DirtyReadback.wrapBits_idempotent]

/-- Changing only bits above the declared integer width preserves readback in both pipelines, comparing the complete optional intrinsic value. -/
theorem cleanWord_int_lowBits :
 ∀ (D : Solidity.Source.Layout) (pipeline : Solidity.Yul.DirtyReadback.Pipeline)
(ty : Solidity.Source.IntTy) (first second : Solidity.Yul.Word),
first.val % 2 ^ ty.bits = second.val % 2 ^ ty.bits →
Solidity.Yul.DirtyReadback.cleanWord (D := D) pipeline (.int ty) first =
Solidity.Yul.DirtyReadback.cleanWord (D := D) pipeline (.int ty) second := by
  intro D pipeline ty first second residue
  rw [Solidity.Yul.DirtyReadback.cleanWord_int, Solidity.Yul.DirtyReadback.cleanWord_int]
  have residues := congrArg (fun n : Nat => (n : Int)) residue
  simp only [Int.natCast_emod] at residues
  have wrapped := Solidity.Yul.DirtyReadback.wrapBits_congr ty.signed ty.bits
    (first.val : Int) (second.val : Int) residues
  simp only [Solidity.Source.intWrap, Solidity.Source.IntTy.wrap, wrapped]

/-- The existing integer word encoder carries exactly the nonnegative 256-bit residue. -/
theorem intWord_value :
 ∀ (value : Int), ((Solidity.Source.intWord value).val : Int) =
value % ((2 ^ 256 : Nat) : Int) := by
  intro value
  have positive : (0 : Int) < ((2 ^ 256 : Nat) : Int) := by decide
  have nonnegative := Int.emod_nonneg value (by omega : ((2 ^ 256 : Nat) : Int) ≠ 0)
  have bounded := Int.emod_lt_of_pos value positive
  have narrow : (value % ((2 ^ 256 : Nat) : Int)).toNat < 2 ^ 256 := by omega
  unfold Solidity.Source.intWord Solidity.Source.toWord
  dsimp only
  rw [Nat.mod_eq_of_lt narrow, Int.toNat_of_nonneg nonnegative]

/-- The existing 256-bit encoder preserves every valid integer cleanup, including signed negative values. -/
theorem wrap_intWord :
 ∀ (ty : Solidity.Source.IntTy) (value : Int),
ty.wrap ((Solidity.Source.intWord value).val : Int) = ty.wrap value := by
  intro ty value
  obtain ⟨factor, equation⟩ := Nat.pow_dvd_pow 2 ty.valid.2.2
  have divides : ((2 ^ ty.bits : Nat) : Int) ∣ ((2 ^ 256 : Nat) : Int) := by
    refine ⟨(factor : Int), ?_⟩
    rw [equation, Int.natCast_mul]
  apply Solidity.Yul.DirtyReadback.wrapBits_congr
  rw [Solidity.Yul.DirtyReadback.intWord_value]
  exact Int.emod_emod_of_dvd value divides

/-- Encoding any integer and reading it back yields exactly the existing intrinsic wrapped value in either pipeline. This states no general Source execution agreement. -/
theorem cleanWord_int_encode :
 ∀ (D : Solidity.Source.Layout) (pipeline : Solidity.Yul.DirtyReadback.Pipeline)
(ty : Solidity.Source.IntTy) (value : Int),
Solidity.Yul.DirtyReadback.cleanWord (D := D) pipeline (.int ty) (Solidity.Source.intWord value) =
some (Solidity.Source.intWrap ty value) := by
  intro D pipeline ty value
  rw [Solidity.Yul.DirtyReadback.cleanWord_int]
  simp only [Solidity.Source.intWrap, Solidity.Yul.DirtyReadback.wrap_intWord]

/-- Cleanup preserves every already bounded Source integer, unsigned or signed. -/
theorem intWrap_of_range :
 ∀ (ty : Solidity.Source.IntTy) (value : Int),
ty.lo ≤ value ∧ value ≤ ty.hi → ty.wrap value = value := by
  intro ty value bound
  rcases ty with ⟨signed, bits, valid⟩
  cases signed
  · have positive := Solidity.Source.two_pow_pos bits
    simp only [Solidity.Source.IntTy.lo, Solidity.Source.IntTy.hi,
      Bool.false_eq_true, if_false] at bound
    simp only [Solidity.Source.IntTy.wrap, Solidity.Source.wrapBits,
      Bool.false_eq_true, false_and, if_false]
    exact Int.emod_eq_of_lt bound.1 (by omega)
  · let half : Int := ((2 ^ (bits - 1) : Nat) : Int)
    let modulus : Int := ((2 ^ bits : Nat) : Int)
    have positive : 0 < half := Int.ofNat_lt.mpr (Solidity.Source.two_pow_pos (bits - 1))
    have relation : modulus = 2 * half := by
      change ((2 ^ bits : Nat) : Int) = 2 * ((2 ^ (bits - 1) : Nat) : Int)
      rw [Solidity.Source.two_pow_succ_pred (by omega), Int.natCast_mul]
      rfl
    have high : ((2 ^ (bits - 1) - 1 : Nat) : Int) = half - 1 := by
      dsimp [half]
      have pos := Solidity.Source.two_pow_pos (bits - 1)
      omega
    change -half ≤ value ∧ value ≤ ((2 ^ (bits - 1) - 1 : Nat) : Int) at bound
    rw [high] at bound
    simp only [Solidity.Source.IntTy.wrap, Solidity.Source.wrapBits, true_and]
    change (if ((2 ^ (bits - 1) - 1 : Nat) : Int) < value % modulus
      then value % modulus - modulus else value % modulus) = value
    rw [high]
    by_cases nonnegative : 0 ≤ value
    · have residue : value % modulus = value := Int.emod_eq_of_lt nonnegative (by omega)
      rw [residue]
      split <;> omega
    · have residue : value % modulus = value + modulus := by
        rw [← Int.add_emod_right]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      rw [residue]
      split <;> omega

/-- Every bounded intrinsic Source integer survives its actual ABI word encoder and published cleanup in either pipeline. This is a value roundtrip, not a general Source execution theorem. -/
theorem cleanWord_int_roundtrip :
 ∀ (D : Solidity.Source.Layout) (pipeline : Solidity.Yul.DirtyReadback.Pipeline)
(ty : Solidity.Source.IntTy) (value : Int) (bound : ty.lo ≤ value ∧ value ≤ ty.hi),
(Solidity.Source.Val.int (D := D) (t := ty) value bound).word.bind
(Solidity.Yul.DirtyReadback.cleanWord (D := D) pipeline (.int ty)) =
some (Solidity.Source.Val.int value bound) := by
  intro D pipeline ty value bound
  simp only [Solidity.Source.Val.word, Option.bind_some,
    Solidity.Yul.DirtyReadback.cleanWord_int_encode, Solidity.Source.intWrap,
    Solidity.Yul.DirtyReadback.intWrap_of_range ty value bound]

/-- The intrinsic Boolean ABI encoder and published nonzero cleanup roundtrip exactly; no integer-width modulo rule is used. -/
theorem cleanWord_bool_roundtrip :
 ∀ (D : Solidity.Source.Layout) (pipeline : Solidity.Yul.DirtyReadback.Pipeline) (value : Bool),
(Solidity.Source.Val.bool (D := D) value).word.bind
(Solidity.Yul.DirtyReadback.cleanWord (D := D) pipeline .bool) =
some (Solidity.Source.Val.bool value) := by
  intro D pipeline value
  cases pipeline <;> cases value <;> rfl

end Solidity.Yul.DirtyReadback
