import Solidity.Backend.Executable.ScalarSequenceResources
import Solidity.Backend.Executable.PrefixChecks

/-!
# Constructor consumer for the selected scalar byte payload

The layout is derived from actual complete scalar encodings and the existing
nonempty CODECOPY prefix. Creation.Exec returns those bytes; Scalar.run gives
separate numeric behavior of the returned instruction program. The runners,
stack types and observations are never identified. Account installation,
fetched runtime execution, source constructors and Osaka agreement remain open.
-/
namespace Solidity.Backend.Executable.ScalarArtifact
open Creation

def runtimeCode (checked : Bool) (a b : PrimTy.uint.Denote) : Program :=
  if checked then ScalarSequence.checkedCode a b else ScalarSequence.code a b

def runtimeBytes (checked : Bool) (a b : PrimTy.uint.Denote) : List UInt8 :=
  Backend.encode (runtimeCode checked a b)

theorem runtime_length (checked : Bool) (a b : PrimTy.uint.Denote) :
    (runtimeBytes checked a b).length = if checked then 175 else 104 := by
  cases checked
  · exact ScalarSequence.bytes_length a b
  · exact ScalarSequence.checked_bytes_length a b

/-- The two actual payloads both use PUSH1 lengths. The nonempty prefix is
six bytes and the exit wrapper ten, so the derived runtime entry is sixteen. -/
def placement (checked : Bool) (a b : PrimTy.uint.Denote) :
    Placement (Backend.encode copyPrefix) (runtimeBytes checked a b) where
  lengthWord := ⟨if checked then 175 else 104, by cases checked <;> decide⟩
  length_eq := (runtime_length checked a b).symm
  offsetWord := ⟨16, by decide⟩
  aligned := by
    rw [placed_size, length_encode]
    cases checked
    · change 16 = 6 + (2 * byteWidth 104 + byteWidth 16 + 7)
      rw [byteWidth_small 104 (by decide) (by decide), byteWidth_small 16 (by decide) (by decide)]
    · change 16 = 6 + (2 * byteWidth 175 + byteWidth 16 + 7)
      rw [byteWidth_small 175 (by decide) (by decide), byteWidth_small 16 (by decide) (by decide)]

def front (checked success : Bool) (a b : PrimTy.uint.Denote) : List UInt8 :=
  Backend.encode copyPrefix ++
    Backend.encode (exitWrapper success (placement checked a b).lengthWord (placement checked a b).offsetWord)

def image (checked success : Bool) (a b : PrimTy.uint.Denote) (args : List UInt8) : List UInt8 :=
  front checked success a b ++ runtimeBytes checked a b ++ args

/-- Executed nonempty constructor prefix plus exact exit, with an independent
creation-stack suffix. No scalar-stack coercion or runner agreement is used. -/
theorem constructor_exec (checked success : Bool) (a b : PrimTy.uint.Denote)
    (args : List UInt8) (creationTail : List StackWord) :
    Exec (image checked success a b args) (image checked success a b args) creationTail []
      (exitOutcome success (runtimeBytes checked a b)) :=
  PrefixChecks.segmented (placement checked a b) success args creationTail

theorem front_length (checked success : Bool) (a b : PrimTy.uint.Denote) :
    (front checked success a b).length = 16 := by
  simp only [front, List.length_append, length_encode, exitWrapper_size]
  exact (placement checked a b).aligned.symm

theorem image_length (checked success : Bool) (a b : PrimTy.uint.Denote) (args : List UInt8) :
    (image checked success a b args).length = 16 + (if checked then 175 else 104) + args.length := by
  simp only [image, List.length_append, front_length, runtime_length]

/-- The complete scalar encoding is the exact runtime-data interval. -/
theorem runtime_slice (checked success : Bool) (a b : PrimTy.uint.Denote) (args : List UInt8) :
    ((image checked success a b args).drop 16).take (runtimeBytes checked a b).length =
      runtimeBytes checked a b := by
  rw [image, List.append_assoc, ← front_length checked success a b, List.drop_left, List.take_left]

/-- Constructor arguments stay outside that interval and have an exact suffix. -/
theorem arguments_slice (checked success : Bool) (a b : PrimTy.uint.Denote) (args : List UInt8) :
    (image checked success a b args).drop (16 + (runtimeBytes checked a b).length) = args := by
  rw [image, ← front_length checked success a b, ← List.length_append, List.drop_left]

theorem decode_runtime (checked : Bool) (a b : PrimTy.uint.Denote) :
    Backend.decode (runtimeBytes checked a b) = some (runtimeCode checked a b) := decode_encode _

/-- Independent source/numeric execution and constructor-return observations
share the actual selected bytes, without asserting fetched-runtime execution. -/
theorem typed_payload {C : Contract} (σ : State C [.val .int, .val .uint])
    (spill : Scalar.Stack) (room : spill.length ≤ 1019)
    (a b u : PrimTy.uint.Denote) (s : PrimTy.int.Denote) (cmp : Bool)
    (subResult : BinOp.evalT .subW rfl a b = some u) (subShort : BinOp.shortT .subW a = none)
    (castResult : UnOp.evalT .toInt rfl u = some s)
    (cmpResult : BinOp.evalT .lt rfl s ScalarSequence.zero = some cmp)
    (cmpShort : BinOp.shortT .lt s = none) (args : List UInt8)
    (creationTail : List StackWord) :
    (ScalarSequence.resultExpr a b).evalT σ = .ok (!cmp) ∧
    Scalar.run (runtimeCode false a b) (ScalarSequence.frameTail σ spill) =
      some (Scalar.encodeValue .bool (!cmp) :: Scalar.encodeValue .int s :: ScalarSequence.frameTail σ spill) ∧
    Scalar.stackBound (runtimeCode false a b) ((ScalarSequence.frameTail σ spill).length : Int) = true ∧
    Exec (image false true a b args) (image false true a b args) creationTail []
      (.returned (runtimeBytes false a b)) ∧
    Backend.decode (runtimeBytes false a b) = some (runtimeCode false a b) := by
  obtain ⟨source, numeric, capacity⟩ := ScalarSequence.typed_result σ spill room a b u s cmp
    subResult subShort castResult cmpResult cmpShort
  exact ⟨source, numeric, capacity, constructor_exec false true a b args creationTail, decode_runtime false a b⟩

/-- A nonempty argument suffix cannot contaminate a successful runtime result. -/
theorem excludes_argument_bytes (checked : Bool) (a b : PrimTy.uint.Denote)
    (args : List UInt8) (nonempty : 0 < args.length) (creationTail : List StackWord) :
    ¬ Exec (image checked true a b args) (image checked true a b args) creationTail []
      (.returned (runtimeBytes checked a b ++ args)) := by
  intro bad
  have equal := Outcome.returned.inj ((constructor_exec checked true a b args creationTail).deterministic bad)
  have lengths := congrArg List.length equal
  simp only [List.length_append] at lengths
  omega

/-- Failed constructor bytes also exclude all trailing argument bytes. -/
theorem excludes_revert_arguments (checked : Bool) (a b : PrimTy.uint.Denote)
    (args : List UInt8) (nonempty : 0 < args.length) (creationTail : List StackWord) :
    ¬ Exec (image checked false a b args) (image checked false a b args) creationTail []
      (.reverted (runtimeBytes checked a b ++ args)) := by
  intro bad
  have equal := reverted_bytes_unique (constructor_exec checked false a b args creationTail) bad
  have lengths := congrArg List.length equal
  simp only [List.length_append] at lengths
  omega

/-- Changing only the expected result tag cannot convert return into revert. -/
theorem excludes_wrong_tag (checked : Bool) (a b : PrimTy.uint.Denote)
    (args : List UInt8) (creationTail : List StackWord) :
    ¬ Exec (image checked true a b args) (image checked true a b args) creationTail []
      (.reverted (runtimeBytes checked a b)) :=
  returned_excludes_reverted (constructor_exec checked true a b args creationTail)

/-- info: 'Solidity.Backend.Executable.ScalarArtifact.excludes_revert_arguments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms excludes_revert_arguments

/-- info: 'Solidity.Backend.Executable.ScalarArtifact.constructor_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms constructor_exec
/-- info: 'Solidity.Backend.Executable.ScalarArtifact.typed_payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typed_payload
/-- info: 'Solidity.Backend.Executable.ScalarArtifact.runtime_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runtime_slice
/-- info: 'Solidity.Backend.Executable.ScalarArtifact.arguments_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms arguments_slice
/-- info: 'Solidity.Backend.Executable.ScalarArtifact.excludes_argument_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms excludes_argument_bytes
end Solidity.Backend.Executable.ScalarArtifact
