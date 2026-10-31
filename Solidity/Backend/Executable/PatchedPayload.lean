import Solidity.Backend.Executable.ScalarArtifact
import Solidity.Backend.Creation.Immutables

/-! Real library and immutable regions inside the owned selected scalar
payload. Patching is tied to emitted PUSH data and exact selected code, not
just length preservation. LinkTable origin is lane-authored template metadata
inside PUSH32 data, not assembler-generated PUSH20/reference provenance. The
fixed42 fixture resolver does not prove session-deployed library identity. Source declaration/value identity and fetched EVM
execution remain separate producer obligations. -/
namespace Solidity.Backend.Executable.PatchedPayload
open Scalar Creation ScalarSequence

def zeroWord : PrimTy.uint.Denote := ⟨0, by decide⟩
def libraryWord : PrimTy.uint.Denote := ⟨42, by decide⟩
def addressBytes (_ : Unit) : Vector UInt8 20 := toBytesBE 20 42

def template (args : List UInt8) : Artifact Unit where
  runtime := Backend.encode (code zeroWord zeroWord)
  args := args
  runtimeFits := by rw [bytes_length]; decide
  linkBase := 0
  runtimeLinks := [(46,())]

def site (args : List UInt8) : LinkSite (template args).runtime.length Unit where
  location := ⟨46, by change 46+20 ≤ (Backend.encode (code zeroWord zeroWord)).length; rw [bytes_length]; decide⟩
  library := ()
def links (args : List UInt8) : LinkTable (template args) where
  sites := [site args]
  origin := rfl
  disjoint := by simp only [List.pairwise_singleton]

def immutable (args : List UInt8) (b : PrimTy.uint.Denote) : ImmutablePatch (template args).runtime.length Unit where
  key := ()
  location := ⟨1, by change 1+32 ≤ (Backend.encode (code zeroWord zeroWord)).length; rw [bytes_length]; decide⟩
  value := toBytesBE 32 (encodeValue .uint b).toNat

def table (args : List UInt8) (b : PrimTy.uint.Denote) : ImmutableTable (template args).runtime.length Unit where
  patches := [immutable args b]
  disjoint := by simp only [List.pairwise_singleton]

theorem compatible_regions (args : List UInt8) (b : PrimTy.uint.Denote) :
    compatible (table args b) (links args).sites = true := by
  apply (compatible_iff (table args b) (links args).sites).mpr
  intro p hp s hs
  have sameP : p = immutable args b := List.mem_singleton.mp hp
  have sameS : s = site args := List.mem_singleton.mp hs
  subst p s
  left
  change 1+32 ≤ 46
  decide

/-- The library's20 bytes replace the low20 bytes of the second actual PUSH32;
the high12 padding bytes and the complete remaining runtime are retained. -/
theorem linked_runtime (args : List UInt8) :
    linkBytes (template args).runtime (localRefs (links args).sites) addressBytes =
      Backend.encode (code libraryWord zeroWord) := by
  change linkBytes (template []).runtime (localRefs (links []).sites) addressBytes = _
  decide +kernel

def tailBytes : List UInt8 :=
  (pushWord (encodeValue .uint libraryWord)).encode ++ [0x03,0x80] ++
    (pushWord (encodeValue .int ScalarSequence.zero)).encode ++ [0x90,0x12,0x15]

theorem runtime_parts (b : PrimTy.uint.Denote) :
    Backend.encode (code libraryWord b) =
      (0x7f :: (toBytesBE 32 (encodeValue .uint b).toNat).toList) ++ tailBytes := by
  rw [emitted_bytes, encode_pushWord]
  simp only [tailBytes, List.append_assoc]

/-- The immutable patch is the entire first PUSH32's operand, so the resulting
bytes equal the actual selected program for b, not arbitrary patched data. -/
theorem immutable_runtime (args : List UInt8) (b : PrimTy.uint.Denote) :
    patchImmutables (linkBytes (template args).runtime (localRefs (links args).sites) addressBytes)
      (table args b).patches = Backend.encode (code libraryWord b) := by
  rw [linked_runtime]
  change patchAt (Backend.encode (code libraryWord zeroWord)) 1
    (toBytesBE 32 (encodeValue .uint b).toNat).toList = _
  rw [runtime_parts, runtime_parts]
  exact patchAt_middle [] tailBytes 0x7f _ _ (by simp only [Vector.length_toList])

def deployed (args : List UInt8) (b : PrimTy.uint.Denote) : Artifact Unit :=
  combinedArtifact (template args) (links args) (table args b) addressBytes (compatible_regions args b)

theorem runtime_eq (args : List UInt8) (b : PrimTy.uint.Denote) :
    (deployed args b).runtime = Backend.encode (code libraryWord b) := immutable_runtime args b

theorem installs_selected (args : List UInt8) (b : PrimTy.uint.Denote) :
    Exec (deployed args b).payload (deployed args b).payload [] []
      (.returned (Backend.encode (code libraryWord b))) := by
  have actual := combined_installs (template args) (links args) (table args b) addressBytes (compatible_regions args b)
  change Exec (deployed args b).payload (deployed args b).payload [] [] (.returned (deployed args b).runtime) at actual
  rw [runtime_eq] at actual
  exact actual

theorem args_unchanged (args : List UInt8) (b : PrimTy.uint.Denote) : (deployed args b).args = args := rfl

theorem decode_selected (args : List UInt8) (b : PrimTy.uint.Denote) :
    Backend.decode (deployed args b).runtime = some (code libraryWord b) := by
  rw [runtime_eq]
  exact Backend.decode_encode _

/-- The selected literal's exact32-byte value is read from the patched runtime. -/
theorem immutable_read (args : List UInt8) (b : PrimTy.uint.Denote) :
    ((deployed args b).runtime.drop 1).take 32 = (immutable args b).value.toList := by
  apply ImmutableTable.read (table args b)
    (linkBytes (template args).runtime (localRefs (links args).sites) addressBytes)
    (linkSites_length _ _ rfl _) (immutable args b)
  exact List.mem_cons_self

/-- Actual constructor execution cannot return trailing argument bytes. -/
theorem excludes_arguments (args : List UInt8) (b : PrimTy.uint.Denote)
    (nonempty : 0 < args.length) :
    ¬ Exec (deployed args b).payload (deployed args b).payload [] []
      (.returned (Backend.encode (code libraryWord b) ++ args)) := by
  intro bad
  have equal := Outcome.returned.inj ((installs_selected args b).deterministic bad)
  have lengths := congrArg List.length equal
  simp only [List.length_append] at lengths
  omega

/-- info: 'Solidity.Backend.Executable.PatchedPayload.immutable_runtime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms immutable_runtime
/-- info: 'Solidity.Backend.Executable.PatchedPayload.installs_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms installs_selected
/-- info: 'Solidity.Backend.Executable.PatchedPayload.immutable_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms immutable_read
/-- info: 'Solidity.Backend.Executable.PatchedPayload.excludes_arguments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms excludes_arguments
end Solidity.Backend.Executable.PatchedPayload
