import Solidity.Lowering.Readonly.StaticJournal
import Solidity.Backend.Passes.SourceTypedCall
import Solidity.Semantics.State

/-! Conditional P2 consumer interface for P1 runtime histories and P3 raw
source outcomes. Both are indexed by one actual typed source capture and its
post-argument state. No P1/P3 producer theorem is asserted here. In particular,
this does not prove a general source execution produces `History`.
The representation relation is explicit and storage-only, with uniqueness;
no memory/ledger/balance/transaction representation is inferred. -/
namespace Solidity.Lowering.Readonly.InvocationFrame
open Solidity.Source
open Solidity.Roadmap (Outcome)
open Solidity.Backend.Passes.SourceTypedCall
variable {E : Env} {Γ : RCtx} {dn : DeclName} {ps rs : List STy}

/-- A source-local invocation: declaration identity is checked in the source
environment, arguments have their declared types, and capture actually runs.
Embedding this local invocation in a whole body remains a lowering obligation. -/
structure Invocation (E : Env) (Γ : RCtx) (dn : DeclName) (ps rs : List STy) where
  global : Glob E
  frame : Fr
  horizon : Nat
  declaration : Decl
  declared : E.declOf .function ⟨declaration.scope, declaration.name⟩ = some declaration
  signature : declaration.fnSig E = some (ps, rs)
  target : RExpr E Γ (.contract dn)
  value : RExpr E Γ (.int IntTy.u256)
  arguments : RConvArgs E Γ ps
  before : Locals E.layout Γ × St E
  after : Locals E.layout Γ × St E
  captured : Captured E ps
  execution : CapturedAt global frame horizon target declaration signature value arguments
    before after captured

namespace Invocation

def requested (i : Invocation E Γ dn ps rs) : Bool :=
  i.declaration.fnMut == some .view || i.declaration.fnMut == some .pure

def mode (i : Invocation E Γ dn ps rs) : Bool := i.requested || i.frame.static

/-- Exact pre-caller-decoder source outcome at this capture, not a label,
receiver-self equality, or an unrelated supplied byte array. P3 must produce it. -/
def RawAt (i : Invocation E Γ dn ps rs) (result : Except Halt Outcome) (final : St E) : Prop :=
  (callAddr i.global i.frame i.horizon i.captured.receiver i.captured.value
    i.captured.input i.requested).run (L0 E, i.after.2) = (result, (L0 E, final))

/-- P1's required structural journal fact for the same live entry/final state.
This is an explicit producer premise, NOT a proved consequence of mode alone. -/
structure RuntimeFrames (i : Invocation E Γ dn ps rs) (final : St E) : Prop where
  static : i.mode = true
  history : StaticJournal.History i.after.2.ex i.mode final.ex

/-- Inherited static mode cannot be downgraded by the selected declaration. -/
theorem inherited (i : Invocation E Γ dn ps rs) (h : i.frame.static = true) : i.mode = true := by
  simp only [mode, h, Bool.or_true]

/-- Same-invocation raw outcome plus P1's structural execution history yields
source caller-storage preservation; arbitrary bytes/reverts/halts remain allowed. -/
theorem storage (i : Invocation E Γ dn ps rs) (result : Except Halt Outcome) (final : St E)
    (_raw : i.RawAt result final) (frames : i.RuntimeFrames final) :
    (final.ex.world.accounts i.frame.this).storage =
      (i.after.2.ex.world.accounts i.frame.this).storage :=
  frames.history.storage frames.static i.frame.this

/-- The actual pre-decoder source result is deterministic for this invocation. -/
theorem raw_unique (i : Invocation E Γ dn ps rs)
    (one two : Except Halt Outcome) (first second : St E)
    (h₁ : i.RawAt one first) (h₂ : i.RawAt two second) : one = two ∧ first = second := by
  have equal : (one, (L0 E, first)) = (two, (L0 E, second)) := h₁.symm.trans h₂
  exact ⟨congrArg Prod.fst equal, congrArg (fun x => x.2.2) equal⟩

/-- View metadata is read from this exact checked declaration. -/
theorem view_mode (i : Invocation E Γ dn ps rs)
    (view : i.declaration.fnMut = some .view) : i.mode = true := by
  simp only [mode, requested, view, beq_self_eq_true, Bool.true_or]

/-- Pure metadata is likewise insufficient as a detached label: it must be
an equality about the declaration already bound by this invocation. -/
theorem pure_mode (i : Invocation E Γ dn ps rs)
    (pure : i.declaration.fnMut = some .pure) : i.mode = true := by
  simp only [mode, requested, pure, beq_self_eq_true, Bool.or_true, Bool.true_or]

end Invocation

/-- A typed source/intrinsic storage relation, explicit rather than guessed
from labels. Uniqueness states functionality only; it does not prove representation
faithfulness, source path/layout correctness, or compiler adequacy. -/
structure StorageRepresentation (E : Env) (C : Contract) (caller : Solidity.Roadmap.Address) where
  relates : Solidity.Source.Storage E.layout (E.lay caller) → Solidity.Storage C → Prop
  unique : ∀ source left right, relates source left → relates source right → left = right

/-- Transport a real source storage frame through an explicit functional
representation. All other typed state components/frames remain independent. -/
theorem typed_storage {C : Contract} (i : Invocation E Γ dn ps rs)
    (result : Except Halt Outcome) (final : St E) (raw : i.RawAt result final)
    (frames : i.RuntimeFrames final) (representation : StorageRepresentation E C i.frame.this)
    (before after : Solidity.Storage C)
    (entry : representation.relates (i.after.2.ex.world.accounts i.frame.this).storage before)
    (exit : representation.relates (final.ex.world.accounts i.frame.this).storage after) :
    after = before := by
  rw [i.storage result final raw frames] at exit
  exact representation.unique _ _ _ exit entry

/-- Resume with the same explicitly supplied typed context, heap, ledger,
balance, transaction and scoped locals. Continuation/tail correspondence remains separate. Their preservation is not inferred
from a storage-only source restriction. -/
theorem typed_resume {C : Contract} {Ξ : Ctx} (i : Invocation E Γ dn ps rs)
    (result : Except Halt Outcome) (final : St E) (raw : i.RawAt result final)
    (frames : i.RuntimeFrames final) (representation : StorageRepresentation E C i.frame.this)
    (before after : Solidity.Storage C)
    (entry : representation.relates (i.after.2.ex.world.accounts i.frame.this).storage before)
    (exit : representation.relates (final.ex.world.accounts i.frame.this).storage after)
    (template : Solidity.State C Ξ) : template.withStorage after = template.withStorage before :=
  congrArg template.withStorage (typed_storage i result final raw frames representation before after entry exit)

end Solidity.Lowering.Readonly.InvocationFrame
