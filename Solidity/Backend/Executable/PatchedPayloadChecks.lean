import Solidity.Backend.Executable.PatchedPayload
import Solidity.Backend.Executable.ScalarSequenceChecks

/-! Actual emitted PUSH regions, complete selected-code execution and
constructor return coexist without identifying numeric/creation/pinned runs. -/
namespace Solidity.Backend.Executable.PatchedPayloadChecks
open Scalar Creation ScalarSequence PatchedPayload
open ScalarSequenceChecks (caller)
def five : PrimTy.uint.Denote := ⟨5, by decide⟩
def thirtySeven : PrimTy.uint.Denote := ⟨37, by decide⟩
def signed : PrimTy.int.Denote := ⟨37, by decide⟩

theorem actual_selected :
    (resultExpr libraryWord five).evalT caller = .ok true ∧
    Scalar.run (code libraryWord five) (frameTail caller []) =
      some (1 :: 37 :: frameTail caller []) ∧
    stackBound (code libraryWord five) ((frameTail caller []).length : Int) = true :=
  typed_result caller [] (by decide) libraryWord five thirtySeven signed false rfl rfl rfl rfl rfl

theorem actual_install :
    Exec (deployed [0xaa,0xbb] five).payload (deployed [0xaa,0xbb] five).payload [] []
      (.returned (Backend.encode (code libraryWord five))) := installs_selected _ _

example : (deployed [0xaa,0xbb] five).args = [0xaa,0xbb] := args_unchanged _ _
example : Backend.decode (deployed [0xaa,0xbb] five).runtime = some (code libraryWord five) := decode_selected _ _
example : ((deployed [] five).runtime.drop 1).take 32 = (toBytesBE 32 5).toList := immutable_read _ _
example : (deployed [] five).runtime[0]? = some 0x7f ∧
    (deployed [] five).runtime[33]? = some 0x7f ∧
    (deployed [] five).runtime[66]? = some 0x03 := by decide +kernel

/-- The actual immutable and library locations commute and retain exact bytes. -/
example : patchAt (patchAt (template []).runtime 1 (immutable [] five).value.toList) 46 (addressBytes ()).toList =
    patchAt (patchAt (template []).runtime 46 (addressBytes ()).toList) 1 (immutable [] five).value.toList :=
  immutable_link_commute (template []).runtime (immutable [] five) (site []) (addressBytes ()) (by decide +kernel)

def overlap : ImmutableTable (template []).runtime.length Unit where
  patches := [⟨(), ⟨50, by change 50+32 ≤ (Backend.encode (code zeroWord zeroWord)).length; rw [bytes_length]; decide⟩,
    (immutable [] five).value⟩]
  disjoint := by simp only [List.pairwise_singleton]

/-- Individually bounded regions still cannot overlap across component kinds. -/
example : compatible overlap (links []).sites = false := by decide +kernel
example : (immutablePatch? 104 () 90 (immutable [] five).value).isNone = true := by decide +kernel
example : resolve [site []] (fun _ => none) = none :=
  resolve_missing [site []] (fun _ => none) (site []) List.mem_cons_self rfl
example : deployable (template []) = none := unresolved_refused _ (by decide +kernel)
example : deployable (deployed [] five) = some (deployed [] five).payload := rfl
example : ¬ Exec (deployed [0xaa,0xbb] five).payload (deployed [0xaa,0xbb] five).payload [] []
    (.returned (Backend.encode (code libraryWord five) ++ [0xaa,0xbb])) :=
  excludes_arguments _ _ (by decide)
/-- info: 'Solidity.Backend.Executable.PatchedPayloadChecks.actual_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_selected
/-- info: 'Solidity.Backend.Executable.PatchedPayloadChecks.actual_install' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_install
end Solidity.Backend.Executable.PatchedPayloadChecks
