import Solidity.Lowering.Readonly.InvocationFrame
import Solidity.Backend.Passes.SourceCallControls

/-! Inhabited P2 controls. The concrete source runs below discharge their own
P1/P3 inputs. No general P1/P3 producer or native adequacy is asserted. -/
namespace Solidity.Lowering.Readonly.Controls
open Solidity.Source Solidity.Source.SemanticsExamples
open Solidity.Backend.Passes.SourceCallControls
open Solidity.Roadmap (Event Outcome)
open InvocationFrame

/-- A permitted static environment credit, followed by arbitrary raw bytes. -/
def creditAnswer : Solidity.Roadmap.Strategy := fun events =>
  if events.any (fun e => match e with | .credit _ _ => true | _ => false)
  then .answer (.success [7]) else .credit thisC (word 5)

def origin : Invocation EB [.address false] ⟨none, "I"⟩ [] [] where
  global := GB creditAnswer
  frame := { FC with static := true }
  horizon := 8
  declaration := dPing
  declared := by rfl
  signature := dPing_sig
  target := target
  value := lit 0
  arguments := .nil
  before := before
  after := before
  captured := captured
  execution := by rfl

def final : St EB := { sB with
  ex := sB.ex.apply (.account thisC fun old => old.withBalance (word 5))
  events := [.call ext (word 0) (selOf "ping()") true,
    .credit thisC (word 5), .answer (.success [7]) none] }

/-- Actual unknown/nonself source call, pre-caller-decoder, same invocation. -/
theorem raw : origin.RawAt (.ok (.success [7])) final := by rfl

theorem runtime : origin.RuntimeFrames final :=
  ⟨by rfl, .balance (.start _ _) thisC (word 5)⟩

/-- Storage is preserved despite a real permitted balance change. -/
theorem source_frame :
    (final.ex.world.accounts thisC).storage = (sB.ex.world.accounts thisC).storage :=
  origin.storage _ _ raw runtime

theorem balance_changes : (final.ex.world.accounts thisC).balance.val = 5 ∧
    (sB.ex.world.accounts thisC).balance.val = 0 := by decide +kernel

/-- A nonempty typed primitive storage projection using the actual range
checker. This selected-field representation is explicit, not inferred ABI or
whole-contract representation. -/
def Cell : Contract := contract!{ uint x; }

def sourceNumber (source : Solidity.Source.Storage EB.layout (EB.lay thisC)) : Option Int :=
  match source.read dX.path with
  | some (.int value _) => some value
  | _ => none

def project (source : Solidity.Source.Storage EB.layout (EB.lay thisC)) :
    Option (Solidity.Storage Cell) := do
  let n ← sourceNumber source
  let typed ← Solidity.PrimTy.ofInt? .uint n
  return .cons (.prim typed) .nil

def representation : StorageRepresentation EB Cell thisC where
  relates source typed := project source = some typed
  unique _ _ _ left right := Option.some.inj (left.symm.trans right)

def typedThree : Solidity.Storage Cell := .cons (.prim ⟨3, by decide⟩) .nil

theorem entry_representation :
    representation.relates (sB.ex.world.accounts thisC).storage typedThree := by rfl

theorem exit_representation :
    representation.relates (final.ex.world.accounts thisC).storage typedThree := by
  rw [source_frame]
  exact entry_representation

/-- Nonvacuous typed P2 client; the source raw result and history above are
kernel witnesses, rather than assumed endpoint frame facts. -/
theorem typed_client (after : Solidity.Storage Cell)
    (exit : representation.relates (final.ex.world.accounts thisC).storage after) : after = typedThree :=
  typed_storage origin _ _ raw runtime representation typedThree after entry_representation exit

/-- Ordinary write histories remain inhabited and can change caller storage. -/
def writeOp : Op EB.layout EB.lay EB.lay :=
  .account thisC fun old => { old with storage := old.storage.write dX.path (show Solidity.Source.Val EB.layout uint from .int 4 (by decide)) }

theorem ordinary_write : StaticJournal.History sB.ex false (sB.ex.apply writeOp) :=
  .write (.start _ _) rfl writeOp

theorem ordinary_not_preserved :
    readX { sB with ex := sB.ex.apply writeOp } ≠ readX sB := by decide +kernel

theorem static_cannot_write :
    ¬ StaticJournal.History sB.ex true (sB.ex.apply writeOp) := by
  intro history
  have same := history.storage rfl thisC
  have readSame := congrArg (fun cells => sourceNumber cells) same
  have wrong : sourceNumber ((sB.ex.apply writeOp).world.accounts thisC).storage ≠
      sourceNumber (sB.ex.world.accounts thisC).storage := by decide +kernel
  exact wrong readSame

/-- An outer rollback cannot accidentally erase argument effects already
included in its live entry. The rollback uses this exact entry's own mark. -/
theorem rollback_live_checkpoint :
    ((sB.ex.apply writeOp).enter thisC user (word 0) [] true).rollback
      ((sB.ex.apply writeOp).run [writeOp]) = sB.ex.apply writeOp := by
  exact rollback_run _ _ _ _ _ _ _

/-- The callback's actual typed body reads storage and returns normally. -/
def readProgram : Program EB := { PB with
  body := fun d => if d.name = "cb" then
    some (body0 [] (.stmt (.expr (.state dX dX_ty)) .nil)) else PB.body d }

def readOrigin : Invocation EB [.address false] ⟨none, "I"⟩ [] [] :=
  { origin with
    global := { GB reenterOnce with prog := readProgram }
    horizon := 30
    execution := by rfl }

def readFinal : St EB := { sB with
  ex := sB.ex.apply (.account thisC fun old => old.withBalance (word 0))
  events := [.call ext (word 0) (selOf "ping()") true,
    .reenter thisC ext (word 0) (selOf "cb()") false,
    .reentered (.success []), .answer (.success []) none] }

/-- Actual successful read-only callback: static mode does not suppress it. -/
theorem read_reentry_raw : readOrigin.RawAt (.ok (.success [])) readFinal := by rfl

theorem read_reentry_frames : readOrigin.RuntimeFrames readFinal :=
  ⟨by rfl, .child (.start _ _) false (.balance (.start _ _) thisC (word 0))⟩

theorem read_reentry_kept :
    (readFinal.ex.world.accounts thisC).storage = (sB.ex.world.accounts thisC).storage :=
  readOrigin.storage _ _ read_reentry_raw read_reentry_frames

theorem callback_not_suppressed : readFinal.events.contains (.reentered (.success [])) = true := by
  decide +kernel

/-- A view label cannot replace the actual ordinary source declaration. -/
def spoof : Decl := ⟨.function, "ping", some "I", false,
  .function (.ident "ping") .nil (some .external) (some .view) .nil false none .nil .none⟩

theorem spoof_rejected : EB.declOf .function ⟨some "I", "ping"⟩ ≠ some spoof := by
  intro same
  have equal : dPing = spoof := Option.some.inj (origin.declared.symm.trans same)
  have observed := congrArg Solidity.Source.Decl.fnMut equal
  simp only [Solidity.Source.Decl.fnMut, Solidity.Source.SemanticsExamples.dPing, spoof] at observed
  cases observed

/-- A different byte result cannot be attached to this actual invocation. -/
theorem wrong_raw_rejected : ¬ origin.RawAt (.ok (.success [9])) final := by
  intro wrong
  have equal := (origin.raw_unique _ _ _ _ raw wrong).1
  cases equal

end Solidity.Lowering.Readonly.Controls
