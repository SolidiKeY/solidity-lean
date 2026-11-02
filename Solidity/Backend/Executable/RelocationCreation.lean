import Solidity.Backend.Executable.RelocationChecks
import Solidity.Backend.Creation.Linking

/-! Constructor consumer of the actual linked enclosing runtime. The section
was assembled at3 inside this runtime; its actual library site is5. The
standalone constructor header is a different origin and is never added to
runtime operands. This proves copy/return bytes, not account CREATE or JUMP. -/
namespace Solidity.Backend.Executable.RelocationCreation
open Creation RelocationChecks

def runtime : List UInt8 := encode pre ++ encode linked.code ++ suffix
def program : Program := pre ++ linked.code ++ [.op .JUMPDEST, .push 1 #v[0x5b]]
theorem runtime_encoding : runtime = encode program := by
  rw [program, encode_append, encode_append]
  rfl

def template (args : List UInt8) : Artifact Unit where
  runtime := encode pre ++ encode unresolved.code ++ suffix
  args := args
  runtimeFits := by change 36 < 256 ^ 32; decide +kernel
  linkBase := 0
  runtimeLinks := unresolved.linkRefs

def site (args : List UInt8) : LinkSite (template args).runtime.length Unit where
  location := ⟨5, by change 5+20 ≤ 36; decide⟩
  library := ()
def table (args : List UInt8) : LinkTable (template args) where
  sites := [site args]
  origin := rfl
  disjoint := by simp only [List.pairwise_singleton]
def deployed (args : List UInt8) : Artifact Unit := linkedArtifact (template args) (table args) address

/-- Actual section linker equality, not an assumed desired installed runtime. -/
theorem runtime_eq (args : List UInt8) : (deployed args).runtime = runtime := by
  change linkBytes (encode pre ++ encode unresolved.code ++ suffix) unresolved.linkRefs address = _
  exact client.1

theorem installs (args : List UInt8) : Exec (deployed args).payload (deployed args).payload [] []
    (.returned runtime) := by
  have ran := installs_runtime (deployed args)
  rw [runtime_eq] at ran
  exact ran

theorem coordinates (args : List UInt8) :
    (deployed args).runtimeStart = 10 ∧ (deployed args).argsStart = 46 ∧
    (deployed args).runtime.length = 36 := by
  have len : (deployed args).runtime.length = 36 := by rw [runtime_eq]; rfl
  have start : (deployed args).runtimeStart = 10 := by
    change 2 * byteWidth (deployed args).runtime.length + 8 = 10
    rw [len, byteWidth_small 36 (by decide) (by decide)]
  refine ⟨start, ?_, len⟩
  change (deployed args).runtimeStart + (deployed args).runtime.length = 46
  rw [start,len]

theorem slices (args : List UInt8) :
    ((deployed args).payload.drop 10).take 36 = runtime ∧
    (deployed args).payload.drop 46 = args := by
  have rt := (deployed args).runtime_slice
  rw [(coordinates args).1,(coordinates args).2.2,runtime_eq] at rt
  have arg := (deployed args).args_slice
  rw [(coordinates args).2.1] at arg
  exact ⟨rt,arg⟩

/-- Coordinate13 is valid in initcode but not in the installed runtime. The
original backward operand3 remains valid in runtime, not header-adjusted. -/
theorem destination_coordinates (args : List UInt8) :
    validJumpdest (deployed args).runtime 3 = true ∧
    validJumpdest (deployed args).payload 13 = true ∧
    validJumpdest (deployed args).runtime 13 = false := by
  have runtimeTarget : validJumpdest runtime 3 = true := client.2.2.1
  have appended : validJumpdest (runtime ++ args) 3 = true := by
    rw [runtime_encoding]
    exact validJumpdest_encode_append program args (k := 2) rfl
  have image : validJumpdest (deployed args).payload ((deployed args).runtimeStart+3) = true := by
    change validJumpdest ((encode (wrapper (deployed args).lengthWord) ++ (deployed args).runtime) ++ args)
      (runtimeOffset (deployed args).lengthWord+3) = true
    rw [List.append_assoc, ← wrapper_size, validJumpdest_encode_prefix, runtime_eq]
    exact appended
  rw [(coordinates args).1] at image
  refine ⟨?_, image, ?_⟩
  · rw [runtime_eq]
    exact runtimeTarget
  · rw [runtime_eq]
    exact (address_payload 8 (by decide)).2

/-- Dropping the enclosing pre changes a real backward operand into PUSH20
data. Correct linker completion alone cannot justify that wrong copy range. -/
theorem omitted_prefix_invalid : validJumpdest (encode linked.code ++ suffix) 3 = false := by
  apply Bool.eq_false_iff.mpr
  intro valid
  exact ((validJumpdest_iff _ _).mp valid).2 (address_payload 1 (by decide)).1

theorem unresolved_refused (args : List UInt8) : deployable (template args) = none :=
  Creation.unresolved_refused _ (by change [(5,())] ≠ []; decide +kernel)
theorem resolved_ready (args : List UInt8) : deployable (deployed args) = some (deployed args).payload :=
  linked_deployable _ _ _
theorem missing_address (args : List UInt8) : resolve (table args).sites (fun _ => none) = none := rfl

/-- Typed link metadata must retain the real assembler's site5. A site8
cannot be substituted while claiming the same certified origin. -/
theorem wrong_site_refused (args : List UInt8) :
    ¬ ∃ t : LinkTable (template args), localRefs t.sites = [(8,())] := by
  rintro ⟨t,wrong⟩
  have origin : [(5,())] = localRefs t.sites := by
    simpa only [template, localRefs, Nat.zero_add] using t.origin
  rw [wrong] at origin
  cases origin

/-- Nonempty original runtime cannot be replaced by a fragment-only or empty
result of the same actual constructor. -/
theorem no_truncated_return (args : List UInt8) :
    ¬ Exec (deployed args).payload (deployed args).payload [] [] (.returned (encode linked.code ++ suffix)) ∧
    ¬ Exec (deployed args).payload (deployed args).payload [] [] (.returned []) := by
  constructor
  · intro wrong
    have lengths := congrArg List.length (Outcome.returned.inj ((installs args).deterministic wrong))
    change 36 = 33 at lengths
    cases lengths
  · intro wrong
    have lengths := congrArg List.length (Outcome.returned.inj ((installs args).deterministic wrong))
    change 36 = 0 at lengths
    cases lengths

/-- Nonempty constructor arguments stay beyond the returned36-byte interval. -/
theorem no_argument_return (args : List UInt8) (nonempty : 0 < args.length) :
    ¬ Exec (deployed args).payload (deployed args).payload [] [] (.returned (runtime ++ args)) := by
  intro wrong
  have equal := Outcome.returned.inj ((installs args).deterministic wrong)
  have lengths := congrArg List.length equal
  simp only [List.length_append] at lengths
  omega

theorem inhabited : (template [0xaa,0xbb]).runtimeLinks = [(5,())] ∧
    (deployed [0xaa,0xbb]).args = [0xaa,0xbb] ∧
    ((deployed [0xaa,0xbb]).payload.drop 10).take 36 = runtime ∧
    (deployed [0xaa,0xbb]).payload.drop 46 = [0xaa,0xbb] :=
  ⟨rfl,rfl,(slices _).1,(slices _).2⟩
/-- info: 'Solidity.Backend.Executable.RelocationCreation.runtime_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runtime_eq
/-- info: 'Solidity.Backend.Executable.RelocationCreation.installs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms installs
/-- info: 'Solidity.Backend.Executable.RelocationCreation.coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms coordinates
/-- info: 'Solidity.Backend.Executable.RelocationCreation.slices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms slices
/-- info: 'Solidity.Backend.Executable.RelocationCreation.destination_coordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms destination_coordinates
/-- info: 'Solidity.Backend.Executable.RelocationCreation.omitted_prefix_invalid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms omitted_prefix_invalid
/-- info: 'Solidity.Backend.Executable.RelocationCreation.unresolved_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unresolved_refused
/-- info: 'Solidity.Backend.Executable.RelocationCreation.resolved_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_ready
/-- info: 'Solidity.Backend.Executable.RelocationCreation.missing_address' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms missing_address
/-- info: 'Solidity.Backend.Executable.RelocationCreation.wrong_site_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_site_refused
/-- info: 'Solidity.Backend.Executable.RelocationCreation.no_truncated_return' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_truncated_return
/-- info: 'Solidity.Backend.Executable.RelocationCreation.no_argument_return' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_argument_return
/-- info: 'Solidity.Backend.Executable.RelocationCreation.inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inhabited
end Solidity.Backend.Executable.RelocationCreation
