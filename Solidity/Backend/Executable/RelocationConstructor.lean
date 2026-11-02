import Solidity.Backend.Executable.Relocation
import Solidity.Backend.Creation.Linking

/-! General assembly-to-constructor consumers. An enclosing runtime already
contains its encoded prefix, so assembler references are whole-runtime offsets
and the Artifact link origin is zero. Typed LinkTable bounds/origin/disjointness
remain required. All runtime equalities below are derived from actual assembly
and linking, not supplied as simulation premises. Exec is only the published
constructor copy/return slice; contained jumps, accounts and gas stay outside. -/
namespace Solidity.Backend.Executable.RelocationConstructor
open Creation
variable {Lib : Type}

def enclosing (pre : Program) (out : Assembled Lib) (suffix args : List UInt8)
    (fits : (encode pre ++ encode out.code ++ suffix).length < 256 ^ 32) : Artifact Lib where
  runtime := encode pre ++ encode out.code ++ suffix
  args := args
  runtimeFits := fits
  linkBase := 0
  runtimeLinks := out.linkRefs

variable (pre : Program) (out : Assembled Lib) (suffix args : List UInt8)
variable (fits : (encode pre ++ encode out.code ++ suffix).length < 256 ^ 32)

theorem enclosing_length : (enclosing pre out suffix args fits).runtime.length =
    size pre + size out.code + suffix.length := by
  simp only [enclosing, List.length_append, length_encode]

theorem local_origin (table : LinkTable (enclosing pre out suffix args fits)) :
    localRefs table.sites = out.linkRefs := by
  simpa only [enclosing, localRefs, Nat.zero_add] using table.origin.symm

theorem completed_length (table : LinkTable (enclosing pre out suffix args fits))
    (addr : Lib → Vector UInt8 20) :
    (linkedArtifact (enclosing pre out suffix args fits) table addr).runtime.length =
      size pre + size out.code + suffix.length := by
  have preserved := linkSites_length table.sites (enclosing pre out suffix args fits).runtime rfl addr
  exact preserved.trans (enclosing_length pre out suffix args fits)

/-- Minimal-width constructor and argument boundaries are derived from the
actual bounded whole-runtime length; no fixed header size is assumed. -/
theorem constructor_layout (table : LinkTable (enclosing pre out suffix args fits))
    (addr : Lib → Vector UInt8 20) :
    let n := size pre + size out.code + suffix.length
    let a := linkedArtifact (enclosing pre out suffix args fits) table addr
    a.runtime.length = n ∧ a.runtimeStart = 2 * byteWidth n + 8 ∧
      a.argsStart = (2 * byteWidth n + 8) + n ∧
      (a.payload.drop (2 * byteWidth n + 8)).take n = a.runtime ∧
      a.payload.drop ((2 * byteWidth n + 8) + n) = args := by
  dsimp only
  let a := linkedArtifact (enclosing pre out suffix args fits) table addr
  have len := completed_length pre out suffix args fits table addr
  have start : a.runtimeStart = 2 * byteWidth (size pre + size out.code + suffix.length) + 8 := by
    change 2 * byteWidth a.runtime.length + 8 = _
    rw [len]
  have finish : a.argsStart = (2 * byteWidth (size pre + size out.code + suffix.length) + 8) +
      (size pre + size out.code + suffix.length) := by
    change a.runtimeStart + a.runtime.length = _
    rw [start,len]
  have rt := a.runtime_slice
  rw [start,len] at rt
  have ar := a.args_slice
  rw [finish] at ar
  exact ⟨len,start,finish,rt,ar⟩

/-- The typed origin identifies the exact actual assembler patch list. -/
theorem linked_runtime {L : Type} [DecidableEq L]
    {link : Lib → Option (Vector UInt8 20)} {items : List (Item L Lib)}
    (assembled : assemble (size pre) link items = some out)
    (table : LinkTable (enclosing pre out suffix args fits)) (addr : Lib → Vector UInt8 20) :
    ∃ linked, assemble (size pre) (fillLink link addr) items = some linked ∧
      linked.linkRefs = [] ∧
      (linkedArtifact (enclosing pre out suffix args fits) table addr).runtime =
        encode pre ++ encode linked.code ++ suffix := by
  obtain ⟨linked, ran, resolved, patch, _, _⟩ := link_patch addr assembled
  refine ⟨linked,ran,resolved,?_⟩
  change linkBytes _ (localRefs table.sites) addr = _
  rw [local_origin pre out suffix args fits table]
  exact patch pre suffix rfl

/-- Full generic backward-reference consumer: actual assembly/linking determines
the returned runtime, slices, minimal header and runtime/initcode destinations.
It does not run the reference's contained JUMP or identify target state models. -/
theorem relocated_constructor {L : Type} [DecidableEq L]
    {link : Lib → Option (Vector UInt8 20)} {items : List (Item L Lib)}
    (assembled : assemble (size pre) link items = some out)
    (table : LinkTable (enclosing pre out suffix args fits)) (addr : Lib → Vector UInt8 20)
    {j k : Nat} {label : L} (tag : tagIndex items label = some j)
    (reference : items[k]? = some (.pushTag label)) (earlier : j < k) :
    let n := size pre + size out.code + suffix.length
    let a := linkedArtifact (enclosing pre out suffix args fits) table addr
    ∃ linked imm,
      assemble (size pre) (fillLink link addr) items = some linked ∧ linked.linkRefs = [] ∧
      a.runtime = encode pre ++ encode linked.code ++ suffix ∧
      a.runtimeStart = 2 * byteWidth n + 8 ∧ a.argsStart = (2 * byteWidth n + 8) + n ∧
      Exec a.payload a.payload [] [] (.returned (encode pre ++ encode linked.code ++ suffix)) ∧
      (a.payload.drop (2 * byteWidth n + 8)).take n = encode pre ++ encode linked.code ++ suffix ∧
      a.payload.drop ((2 * byteWidth n + 8) + n) = args ∧
      linked.code[k]? = some (.push (asmWidths (size pre) items label) imm) ∧
      ofBytesBE imm.toList = size pre + itemOffset (asmWidths (size pre) items) items j ∧
      ofBytesBE imm.toList < 256 ^ (asmWidths (size pre) items label).val ∧
      ofBytesBE imm.toList < size pre + offset linked.code k ∧
      validJumpdest a.runtime (ofBytesBE imm.toList) = true ∧
      validJumpdest a.payload ((2 * byteWidth n + 8) + ofBytesBE imm.toList) = true := by
  dsimp only
  let a := linkedArtifact (enclosing pre out suffix args fits) table addr
  obtain ⟨linked,imm,ran,resolved,patch,_,_,_,dest,push,_,value,wordFit,back,valid,_⟩ :=
    Relocation.linked_backedge pre suffix addr assembled tag reference earlier
  have runtime : a.runtime = encode pre ++ encode linked.code ++ suffix := by
    change linkBytes _ (localRefs table.sites) addr = _
    rw [local_origin pre out suffix args fits table]
    exact patch
  obtain ⟨_,start,finish,rt,ar⟩ := constructor_layout pre out suffix args fits table addr
  have installed := installs_runtime a
  rw [runtime] at installed rt
  have inside : validJumpdest (a.runtime ++ args) (ofBytesBE imm.toList) = true := by
    rw [runtime, List.append_assoc, List.append_assoc, value,
      ← (assemble_layout ran).2.1 j, validJumpdest_encode_prefix]
    exact validJumpdest_encode_append linked.code (suffix ++ args) dest
  have image : validJumpdest a.payload (a.runtimeStart + ofBytesBE imm.toList) = true := by
    change validJumpdest ((encode (wrapper a.lengthWord) ++ a.runtime) ++ args)
      (runtimeOffset a.lengthWord + ofBytesBE imm.toList) = true
    rw [List.append_assoc, ← wrapper_size, validJumpdest_encode_prefix]
    exact inside
  rw [start] at image
  exact ⟨linked,imm,ran,resolved,runtime,start,finish,installed,rt,ar,push,value,wordFit,back,
    by rw [runtime]; exact valid,image⟩

/-- Exact return observations follow from real constructor execution, not from
an assumed byte equality. This also rules out changed bytes of the same size. -/
theorem return_iff (table : LinkTable (enclosing pre out suffix args fits))
    (addr : Lib → Vector UInt8 20) (bytes : List UInt8) :
    let a := linkedArtifact (enclosing pre out suffix args fits) table addr
    Exec a.payload a.payload [] [] (.returned bytes) ↔ bytes = a.runtime := by
  dsimp only
  constructor
  · intro wrong
    exact (Outcome.returned.inj ((installs_runtime _).deterministic wrong)).symm
  · intro equal
    rw [equal]
    exact installs_runtime _

theorem no_short_return (table : LinkTable (enclosing pre out suffix args fits))
    (addr : Lib → Vector UInt8 20) (bytes : List UInt8)
    (short : bytes.length < size pre + size out.code + suffix.length) :
    let a := linkedArtifact (enclosing pre out suffix args fits) table addr
    ¬ Exec a.payload a.payload [] [] (.returned bytes) := by
  dsimp only
  intro wrong
  have same := (return_iff pre out suffix args fits table addr bytes).mp wrong
  have len := congrArg List.length same
  rw [completed_length pre out suffix args fits table addr] at len
  omega

theorem no_argument_return (table : LinkTable (enclosing pre out suffix args fits))
    (addr : Lib → Vector UInt8 20) (nonempty : 0 < args.length) :
    let a := linkedArtifact (enclosing pre out suffix args fits) table addr
    ¬ Exec a.payload a.payload [] [] (.returned (a.runtime ++ args)) := by
  dsimp only
  intro wrong
  have same := (return_iff pre out suffix args fits table addr _).mp wrong
  have len := congrArg List.length same
  simp only [List.length_append] at len
  omega

/-- Omitting a nonempty enclosing prefix is genuinely shorter even after
linking, because both actual assemblies share the same checked section size. -/
theorem no_omitted_prefix {L : Type} [DecidableEq L]
    {link : Lib → Option (Vector UInt8 20)} {items : List (Item L Lib)}
    (assembled : assemble (size pre) link items = some out)
    (table : LinkTable (enclosing pre out suffix args fits)) (addr : Lib → Vector UInt8 20)
    {linked : Assembled Lib} (filled : assemble (size pre) (fillLink link addr) items = some linked)
    (nonempty : 0 < size pre) :
    let a := linkedArtifact (enclosing pre out suffix args fits) table addr
    ¬ Exec a.payload a.payload [] [] (.returned (encode linked.code ++ suffix)) := by
  have sameSize : size linked.code = size out.code :=
    (assemble_layout filled).2.2.trans (assemble_layout assembled).2.2.symm
  apply no_short_return pre out suffix args fits table addr
  simp only [List.length_append, length_encode]
  rw [sameSize]
  omega

theorem wrong_sites (bad : List (Nat × Lib)) (different : bad ≠ out.linkRefs) :
    ¬ ∃ table : LinkTable (enclosing pre out suffix args fits), localRefs table.sites = bad := by
  rintro ⟨table,wrong⟩
  exact different (wrong.symm.trans (local_origin pre out suffix args fits table))
/-- info: 'Solidity.Backend.Executable.RelocationConstructor.enclosing_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms enclosing_length
/-- info: 'Solidity.Backend.Executable.RelocationConstructor.local_origin' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms local_origin
/-- info: 'Solidity.Backend.Executable.RelocationConstructor.completed_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms completed_length
/-- info: 'Solidity.Backend.Executable.RelocationConstructor.constructor_layout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms constructor_layout
/-- info: 'Solidity.Backend.Executable.RelocationConstructor.linked_runtime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms linked_runtime
/-- info: 'Solidity.Backend.Executable.RelocationConstructor.relocated_constructor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms relocated_constructor
/-- info: 'Solidity.Backend.Executable.RelocationConstructor.return_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms return_iff
/-- info: 'Solidity.Backend.Executable.RelocationConstructor.no_short_return' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_short_return
/-- info: 'Solidity.Backend.Executable.RelocationConstructor.no_argument_return' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_argument_return
/-- info: 'Solidity.Backend.Executable.RelocationConstructor.no_omitted_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_omitted_prefix
/-- info: 'Solidity.Backend.Executable.RelocationConstructor.wrong_sites' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_sites
end Solidity.Backend.Executable.RelocationConstructor
