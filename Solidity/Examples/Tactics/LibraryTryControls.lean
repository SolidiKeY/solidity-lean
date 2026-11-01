import Solidity.Examples.Tactics.LibraryTrySource
import Solidity.Tools.LibraryTryReplay

/-! Negative controls for the actual linked source interface, not fabricated
observations or changes to its original expected outputs. -/
namespace Solidity.Examples.Tactics.LibraryTryControls
open ContractWorld Semantics
open Solidity.Examples.Tactics.LibraryTrySource

def prepared : TRes (World Original.contracts × Handle Original.Code.caller) := do
  let (w,_) ← Original.deployLibrary initial libraryAddress { sender }
  Original.deployCaller w callerAddress { sender }

def absent : Address := ⟨⟨999, by decide +kernel⟩, by decide +kernel⟩

/-- Wrong role, caller frame, linked identity and absent code are distinct
actual world failures, not normal library values or decoded Error reasons. -/
def refused (which : Nat) : TRes (List Nat) := do
  let (w,self) ← prepared
  let w := if which == 0 then { w with roles := fun _ => .contractCode } else w
  let self := if which == 1 then (⟨libraryAddress⟩ : Handle Original.Code.caller) else self
  let linked := if which == 2 then callerAddress else if which == 3 then absent else libraryAddress
  let (_,bytes) ← Original.m0.run w self { sender } linked true
  pure bytes

/-- A world with ordinary code in the library role is refused. -/
theorem wrong_role : (refused 0).halt? = some .revert := by decide +kernel

/-- A library account cannot substitute for the caller frame. -/
theorem wrong_caller_frame : (refused 1).halt? = some .revert := by decide +kernel

/-- The linked address must contain the exact library catalog identity. -/
theorem wrong_installed_identity : (refused 2).halt? = some .revert := by decide +kernel

/-- An uninstalled library is not a successful empty return. -/
theorem uninstalled_library : (refused 3).halt? = some .revert := by decide +kernel

/-- A deliberately wrong raw shape still has total extraction. Its successful
library body runs, then explicit decoding fails outside both caller clauses. -/
def malformedReturn : TRes (List Nat) := do
  let (w,self) ← prepared
  let correct := (Original.m0.linked libraryAddress ((⟨8, by decide +kernel⟩ : ContractWorld.Word),true)).target
  let entry := { correct.entry with result := fun _ => .ok [] }
  let raw : LibraryTryFrame.RawLibrary Original.contracts .caller :=
    ⟨{ correct with entry }, fun _ => ⟨[],rfl⟩⟩
  LibraryTryFrame.run w self (.ok ()) (fun _ => raw) { sender } Original.m0.decode
    (fun _ _ => .ok [777]) (fun _ _ => .ok [18])

/-- A missing raw result is decoded outside the catch boundary. -/
theorem malformed_return_uncaught : malformedReturn.halt? = some .revert := by decide +kernel

/- The actual caught bytes exclude an invented replacement reason. -/
/-- The actual Error payload cannot become an invented byte sequence. -/
theorem wrong_catch_bytes : (f false).toOption ≠ some
    (expected 18 [102,97,105,108,117,114,102]) := by
  rw [f_caught]
  decide +kernel

/- Actual typed uint decoding refuses missing result words. -/
/-- The existing uint binder refuses an absent return word. -/
theorem missing_result_shape : (Original.m0.decode []).halt? = some .revert := by decide +kernel

/- Original argument words are decoded before source prefix execution. -/
/-- A noncanonical Boolean cannot execute the source prefix. -/
theorem malformed_bool_input : Tools.LibraryTryReplay.input ((wordBytes 2).map UInt8.toNat) =
    .error "invalid bool word" := by rfl

/-- An out-of-range byte cannot enter the source interface. -/
theorem malformed_byte_input : Tools.LibraryTryReplay.input [256] =
    .error "canonical bool word required" := by rfl

/-- The current static restriction is retained, not weakened to execute a view body. -/
def staticCall : TRes (List Nat) := do
  let (w,self) ← prepared
  let (_,bytes) ← Original.m0.run w self { sender, mode := .readOnly } libraryAddress true
  pure bytes

/-- The existing nonempty-body static restriction remains in force. -/
theorem static_refused : staticCall.halt? = some .revert := by decide +kernel

/-- The source storage root/member really has the admitted intrinsic type. -/
theorem caller_storage_type : Original.Source.C.rootType "t" =
    some (.ref (.struct "S{x:uint}")) := rfl

/-- Storage parameter mapping is exactly a caller-root alias, with unchanged
heap and caller environment; it is not a copied library-state object. -/
theorem caller_storage_alias {Γ : Ctx} (σ : State Original.Source.C Γ) :
    TRun.declStorage (.struct "S{x:uint}")
      (some (.path (.loc (.root "t" caller_storage_type)))) σ =
      .ok ⟨σ.push (t := .alias (.struct "S{x:uint}"))
        (some (SRef.ofRoot "t" caller_storage_type)), List.prefix_refl _⟩ :=
  LibraryTryFrame.storage_alias_root σ "t" (.struct "S{x:uint}") caller_storage_type

/-- An uncaught failed library boundary rolls back the earlier caller
prefix with the existing outer atomic operation; no new outcome modality. -/
def rolledBackPrefix : TRes (Int × Option THalt) := do
  let (w,self) ← prepared
  let (after,outcome) := atomic w (Original.m1.run w self { sender } absent false)
  let value ← Original.readStorage after self
  pure (value,outcome.halt?)

/-- Missing linked code cannot leak g's candidate prefix write. -/
theorem atomic_prefix_rollback : rolledBackPrefix.toOption = some (0,some .revert) := by decide +kernel

end Solidity.Examples.Tactics.LibraryTryControls
