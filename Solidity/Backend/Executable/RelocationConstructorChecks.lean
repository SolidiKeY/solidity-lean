import Solidity.Backend.Executable.RelocationConstructor
import Solidity.Backend.Executable.RelocationCreation

/-! Inhabited clients of the general consumer, not new linking/creation
semantics. Reuse the actual base3/backedge/PUSH20 client, including a255→256
runtime-length boundary. Empty runtime is a separate assembly with no backward
reference; it does not pretend to inhabit the nonempty-backedge premises. -/
namespace Solidity.Backend.Executable.RelocationConstructorChecks
open Creation RelocationChecks RelocationConstructor

def paddedSuffix (padding : Nat) : List UInt8 := suffix ++ List.replicate padding 0
theorem whole_length (padding : Nat) :
    (encode pre ++ encode unresolved.code ++ paddedSuffix padding).length = 36+padding := by
  simp only [paddedSuffix, List.length_append, List.length_replicate, length_encode]
  change 3+30+(3+padding) = _
  omega

theorem section_length (padding : Nat) :
    size pre + size unresolved.code + (paddedSuffix padding).length = 36+padding := by
  rw [← whole_length padding]
  simp only [List.length_append, length_encode]

def representable (padding : Nat) (room : 36+padding < 256 ^ 32) :
    (encode pre ++ encode unresolved.code ++ paddedSuffix padding).length < 256 ^ 32 := by
  rw [whole_length]
  exact room

def artifact (padding : Nat) (args : List UInt8) (room : 36+padding < 256 ^ 32) : Artifact Unit :=
  enclosing pre unresolved (paddedSuffix padding) args (representable padding room)
def site (padding : Nat) (args : List UInt8) (room : 36+padding < 256 ^ 32) :
    LinkSite (artifact padding args room).runtime.length Unit where
  location := ⟨5, by
    change 5+20 ≤ (encode pre ++ encode unresolved.code ++ paddedSuffix padding).length
    rw [whole_length]
    omega⟩
  library := ()
def table (padding : Nat) (args : List UInt8) (room : 36+padding < 256 ^ 32) :
    LinkTable (artifact padding args room) where
  sites := [site padding args room]
  origin := rfl
  disjoint := by simp only [List.pairwise_singleton]
def completed (padding : Nat) (args : List UInt8) (room : 36+padding < 256 ^ 32) : Artifact Unit :=
  linkedArtifact (artifact padding args room) (table padding args room) address
def linkedBytes (padding : Nat) : List UInt8 := encode pre ++ encode linked.code ++ paddedSuffix padding

/-- The general theorem supplies actual execution and both destinations for
arbitrary bounded padding and arguments. There is no supplied patch equality. -/
theorem generic_client (padding : Nat) (args : List UInt8) (room : 36+padding < 256 ^ 32) :
    let a := completed padding args room
    a.runtime = linkedBytes padding ∧
      Exec a.payload a.payload [] [] (.returned (linkedBytes padding)) ∧
      validJumpdest a.runtime 3 = true ∧
      validJumpdest a.payload ((2 * byteWidth (36+padding)+8)+3) = true ∧
      (a.payload.drop (2 * byteWidth (36+padding)+8)).take (36+padding) = linkedBytes padding ∧
      a.payload.drop ((2 * byteWidth (36+padding)+8)+(36+padding)) = args := by
  obtain ⟨out,imm,ran,_,runtime,_,_,exec,rt,ar,_,value,_,_,valid,image⟩ :=
    relocated_constructor pre unresolved (paddedSuffix padding) args (representable padding room)
      actual_unresolved (table padding args room) address (j := 0) (k := 5) (label := 0) rfl rfl (by decide)
  have same : out = linked := Option.some.inj (ran.symm.trans actual_linked)
  subst out
  change ofBytesBE imm.toList = 3 at value
  rw [value] at valid image
  rw [section_length] at image rt ar
  exact ⟨runtime,exec,valid,image,rt,ar⟩

def low (args : List UInt8) : Artifact Unit := completed 219 args (by decide +kernel)
def high (args : List UInt8) : Artifact Unit := completed 220 args (by decide +kernel)
private theorem width256 : byteWidth 256 = 2 := by
  rw [byteWidth]
  change byteWidth 1 + 1 = 2
  rw [byteWidth_small 1 (by decide) (by decide)]

theorem low_coordinates (args : List UInt8) :
    (low args).runtime.length = 255 ∧ (low args).runtimeStart = 10 ∧ (low args).argsStart = 265 := by
  obtain ⟨len,start,finish,_,_⟩ := constructor_layout pre unresolved (paddedSuffix 219) args
    (representable 219 (by decide +kernel)) (table 219 args (by decide +kernel)) address
  rw [section_length] at len start finish
  change (low args).runtimeStart = 2 * byteWidth 255+8 at start
  change (low args).argsStart = (2 * byteWidth 255+8)+255 at finish
  rw [byteWidth_small 255 (by decide) (by decide)] at start finish
  exact ⟨len,start,finish⟩
theorem high_coordinates (args : List UInt8) :
    (high args).runtime.length = 256 ∧ (high args).runtimeStart = 12 ∧ (high args).argsStart = 268 := by
  obtain ⟨len,start,finish,_,_⟩ := constructor_layout pre unresolved (paddedSuffix 220) args
    (representable 220 (by decide +kernel)) (table 220 args (by decide +kernel)) address
  rw [section_length] at len start finish
  change (high args).runtimeStart = 2 * byteWidth 256+8 at start
  change (high args).argsStart = (2 * byteWidth 256+8)+256 at finish
  rw [width256] at start finish
  exact ⟨len,start,finish⟩

/-- Both actual constructor executions cross the minimal-width boundary; the
backward runtime operand stays3 while its image coordinate changes13→15. -/
theorem width_boundary :
    Exec (low []).payload (low []).payload [] [] (.returned (linkedBytes 219)) ∧
    Exec (high [0xaa,0xbb]).payload (high [0xaa,0xbb]).payload [] [] (.returned (linkedBytes 220)) ∧
    validJumpdest (low []).payload 13 = true ∧
    validJumpdest (high [0xaa,0xbb]).payload 15 = true ∧
    (low []).runtimeStart ≠ (high [0xaa,0xbb]).runtimeStart := by
  have lo := generic_client 219 [] (by decide +kernel)
  have hi := generic_client 220 [0xaa,0xbb] (by decide +kernel)
  have lv := lo.2.2.2.1
  have hv := hi.2.2.2.1
  change validJumpdest (low []).payload ((2*byteWidth 255+8)+3) = true at lv
  change validJumpdest (high [0xaa,0xbb]).payload ((2*byteWidth 256+8)+3) = true at hv
  rw [byteWidth_small 255 (by decide) (by decide)] at lv
  rw [width256] at hv
  refine ⟨lo.2.1,hi.2.1,lv,hv,?_⟩
  rw [(low_coordinates []).2.1,(high_coordinates [0xaa,0xbb]).2.1]
  decide

theorem omitted_prefix (padding : Nat) (args : List UInt8) (room : 36+padding < 256^32) :
    ¬ Exec (completed padding args room).payload (completed padding args room).payload [] []
      (.returned (encode linked.code ++ paddedSuffix padding)) :=
  no_omitted_prefix pre unresolved (paddedSuffix padding) args (representable padding room)
    actual_unresolved (table padding args room) address actual_linked (by decide)
theorem wrong_site (padding : Nat) (args : List UInt8) (room : 36+padding < 256^32) :
    ¬ ∃ t : LinkTable (artifact padding args room), localRefs t.sites = [(8,())] :=
  wrong_sites pre unresolved (paddedSuffix padding) args (representable padding room) [(8,())]
    (by change [(8,())] ≠ [(5,())]; decide)
theorem argument_leak :
    ¬ Exec (high [0xaa,0xbb]).payload (high [0xaa,0xbb]).payload [] []
      (.returned ((high [0xaa,0xbb]).runtime ++ [0xaa,0xbb])) :=
  no_argument_return pre unresolved (paddedSuffix 220) [0xaa,0xbb] (representable 220 (by decide +kernel))
    (table 220 [0xaa,0xbb] (by decide +kernel)) address (by decide)

def empty : Assembled Unit := ⟨[],[]⟩
theorem empty_assembled (link : Unit → Option (Vector UInt8 20)) :
    assemble 0 link ([] : List (Item Nat Unit)) = some empty := by
  unfold assemble asmWidths
  rw [fixWidths]
  simp only [refs,List.filterMap_nil,List.all_nil,dite_true]
  rfl
def emptyArtifact (args : List UInt8) : Artifact Unit := enclosing [] empty [] args (by decide +kernel)
def emptyTable (args : List UInt8) : LinkTable (emptyArtifact args) where
  sites := []
  origin := rfl
  disjoint := by constructor
def emptyCompleted (args : List UInt8) : Artifact Unit := linkedArtifact (emptyArtifact args) (emptyTable args) address

/-- Empty runtime is an actual independently assembled case with no reference.
Arbitrary arguments remain separate, including nonempty arguments. -/
theorem empty_constructor (args : List UInt8) :
    (emptyCompleted args).runtime = [] ∧ (emptyCompleted args).runtimeStart = 8 ∧
    (emptyCompleted args).argsStart = 8 ∧
    Exec (emptyCompleted args).payload (emptyCompleted args).payload [] [] (.returned []) ∧
    (emptyCompleted args).payload.drop 8 = args := by
  obtain ⟨linked,ran,_,runtime⟩ := linked_runtime [] empty [] args (by decide +kernel)
    (empty_assembled (fun _ => none)) (emptyTable args) address
  have same : linked = empty := Option.some.inj (ran.symm.trans (empty_assembled _))
  subst linked
  obtain ⟨_,start,finish,_,ar⟩ := constructor_layout [] empty [] args (by decide +kernel) (emptyTable args) address
  change (emptyCompleted args).runtime = [] at runtime
  change (emptyCompleted args).runtimeStart = 2*byteWidth 0+8 at start
  change (emptyCompleted args).argsStart = (2*byteWidth 0+8)+0 at finish
  change (emptyCompleted args).payload.drop ((2*byteWidth 0+8)+0) = args at ar
  rw [byteWidth_zero] at start finish ar
  have ran := installs_runtime (emptyCompleted args)
  rw [runtime] at ran
  exact ⟨runtime,start,finish,ran,ar⟩

theorem empty_nonempty_arguments :
    Exec (emptyCompleted []).payload (emptyCompleted []).payload [] [] (.returned []) ∧
    Exec (emptyCompleted [0xaa,0xbb]).payload (emptyCompleted [0xaa,0xbb]).payload [] [] (.returned []) ∧
    ¬ Exec (emptyCompleted [0xaa,0xbb]).payload (emptyCompleted [0xaa,0xbb]).payload [] [] (.returned [0xaa,0xbb]) := by
  refine ⟨(empty_constructor []).2.2.2.1,(empty_constructor [0xaa,0xbb]).2.2.2.1,?_⟩
  intro wrong
  have same := (return_iff [] empty [] [0xaa,0xbb] (by decide +kernel) (emptyTable [0xaa,0xbb]) address [0xaa,0xbb]).mp wrong
  change [0xaa,0xbb] = (emptyCompleted [0xaa,0xbb]).runtime at same
  rw [(empty_constructor [0xaa,0xbb]).1] at same
  cases same
/-- Taking255 bytes from the actual256-byte result is not another possible
return observation of this same constructor. -/
theorem truncated_high (args : List UInt8) :
    ¬ Exec (high args).payload (high args).payload [] [] (.returned ((high args).runtime.take 255)) := by
  apply no_short_return pre unresolved (paddedSuffix 220) args (representable 220 (by decide +kernel))
    (table 220 args (by decide +kernel)) address
  rw [section_length, List.length_take, (high_coordinates args).1]
  decide

/-- Reusing the old10-byte header to compute the argument boundary of the
256-byte case leaves two runtime bytes. No argument contents can hide it. -/
theorem high_wrong_arguments (args : List UInt8) : (high args).payload.drop 266 ≠ args := by
  have total : (high args).payload.length = 268+args.length := by
    change ((high args).initcode ++ args).length = _
    rw [List.length_append, (high args).initcode_length, (high_coordinates args).2.2]
  intro wrong
  have lengths := congrArg List.length wrong
  rw [List.length_drop,total] at lengths
  omega

/-- info: 'Solidity.Backend.Executable.RelocationConstructorChecks.generic_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms generic_client
/-- info: 'Solidity.Backend.Executable.RelocationConstructorChecks.low_coordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms low_coordinates
/-- info: 'Solidity.Backend.Executable.RelocationConstructorChecks.high_coordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms high_coordinates
/-- info: 'Solidity.Backend.Executable.RelocationConstructorChecks.width_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms width_boundary
/-- info: 'Solidity.Backend.Executable.RelocationConstructorChecks.omitted_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms omitted_prefix
/-- info: 'Solidity.Backend.Executable.RelocationConstructorChecks.wrong_site' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_site
/-- info: 'Solidity.Backend.Executable.RelocationConstructorChecks.argument_leak' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms argument_leak
/-- info: 'Solidity.Backend.Executable.RelocationConstructorChecks.empty_assembled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_assembled
/-- info: 'Solidity.Backend.Executable.RelocationConstructorChecks.empty_constructor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_constructor
/-- info: 'Solidity.Backend.Executable.RelocationConstructorChecks.empty_nonempty_arguments' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_nonempty_arguments
/-- info: 'Solidity.Backend.Executable.RelocationConstructorChecks.truncated_high' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms truncated_high
/-- info: 'Solidity.Backend.Executable.RelocationConstructorChecks.high_wrong_arguments' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms high_wrong_arguments
end Solidity.Backend.Executable.RelocationConstructorChecks
