import Solidity.Yul.RawBoundary
import Solidity.Yul.CleanFunctions

/-! **Readback of dirty LOCAL words** (user decision H109, 2026-11-06).

An assembly block may leave a dirty word (high bits set) in a narrow integer
or `bool` Solidity local. Solidity code reading the local afterwards sees it
cleaned, the same way in both pinned pipelines (solc 0.8.38, optimizer off;
`tests/evm-reference/dirty-locals.json`, produced by
`scripts/evm-reference/dirty-locals.mjs`):

- `uintN`: the low `N` bits (`uint8` `0x1ff` reads `255`, `uint16`
  `0xabcd1234` reads `0x1234`);
- `intN`: the low `N` bits sign-extended (`int8` `0x80` reads `-128`,
  `0x17f` reads `127`, `0x1ff` reads `-1`);
- `bool`: true exactly when the word is not zero (`2` reads true, `!x` is
  false, `x == true` is true).

The cleaning happens here, at the readback into Source locals: Source values
stay intrinsic, the raw frame keeps every bit, and no assembly write cleans.
Any other type a raw word can hold (addresses, `bytesN`, enums, external
function values, …) is not read back: the refusal (`none`) stays, as
`LocalValues.clean?` refuses. `RawCoherent.coherent` keeps reporting a dirty
frame as incoherent: coherence is about reusing the clean backup without
decoding, and this readback is the explicit cleaning boundary. -/
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

/-- **The readback of a raw LOCAL frame** after an assembly block: its
authoritative words (`RawFrame.materialize`) read back into Source locals
against the frame's clean backup, with the frame's world. A dirty narrow
integer or `bool` local is cleaned as solc cleans it; an untouched local
keeps its clean value; a dirty local of any other type refuses the frame. -/
def frame {ctx : Solidity.Source.Ctx} (pipeline : Pipeline) (state : RawFrame.State ctx) :
    Option (Locals ctx.env.layout ctx.tys × Solidity.Source.St ctx.env) :=
  (readbackFrom pipeline ctx.tys (RawFrame.materialize state).1 state.clean).map (·, state.world)

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

end Solidity.Yul.DirtyReadback
