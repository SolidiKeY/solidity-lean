import Solidity.Solkey.ComputedRevert
import Solidity.Semantics.RevertMemory

/-!
# Computed reasons and raw rethrows

The pinned solc source computes a reason in memory, catches and rethrows its
ABI bytes, then decodes the outer reason. Kernel certificates cover computed
reasons and eager evaluation; the complete nested catch has executable guards.
Bounded certificates are lifted to the unbounded typed run by its proved
approximation theorem.
-/

namespace Solidity.Examples.Tactics.ComputedRevert

local instance : InContract := ⟨Solc.ComputedRevert⟩

/-- Every source function elaborates, including the internal reason producer. -/
example : Solc.ComputedRevert.report.all (·.status == .elaborated) = true := by decide +kernel

-- The importer accepts only a byte buffer's canonical whole-buffer rethrow.
example : Solc.RevertAssemblyRejected.report.map (fun r => (r.name, r.status)) =
    [("wrongOffset", .unsupported), ("differentLength", .unsupported),
     ("extraStatement", .unsupported), ("wordArray", .unsupported),
     ("renamed", .elaborated)] := by decide +kernel

private def σ₇ : State Solc.ComputedRevert [] :=
  { State.init Solc.ComputedRevert with tx := { selfAddress := ⟨7, rfl⟩ } }

/-- The finite witness computes the complete ABI payload in the kernel. -/
theorem computed_fuel : (Solc.ComputedRevert.computed.runF 8 σ₇).halt? =
    some (.revertWith (Semantics.encodeError [98, 111, 111, 109, 33])) := by
  decide +kernel

/-- The computed ABI data is also the actual unbounded execution outcome. -/
theorem computed_exact : (Prog.run σ₇ Solc.ComputedRevert.computed).halt? =
    some (.revertWith (Semantics.encodeError [98, 111, 111, 109, 33])) :=
  Prog.run_halt_of_runF _ σ₇ 8 (by decide +kernel) computed_fuel

private def bounce := sol{ bounce(); }
private def observe := sol{ observe(); }

-- The compiled nested catch rethrows the full ABI buffer unchanged.
#guard (bounce.runF 8 σ₇).halt? ==
  some (.revertWith (Semantics.encodeError [98, 111, 111, 109, 33]))
#guard (observe.runF 8 σ₇).toOption.isSome

/-- Solidity evaluates the reason producer even when require's condition is true. -/
theorem eager_fuel : (Solc.ComputedRevert.eager.runF 8 σ₇).toOption.isSome = true := by
  decide +kernel

theorem eager_exact : (Prog.run σ₇ Solc.ComputedRevert.eager).toOption.isSome = true :=
  (Prog.runF_approx 8 _ σ₇).returned eager_fuel

private def changedAlias := sol{
  bytes memory data = hex"1234";
  bytes memory aliasData = data;
  data[1] = bytes1(uint8(254));
  assembly { revert(add(aliasData, 32), mload(aliasData)) }
}

theorem raw_alias_exact : (Prog.run σ₇ changedAlias).halt? =
    some (.revertWith [0x12, 0xfe]) := by
  decide +kernel

private def emptyRaw := sol{
  bytes memory data = new bytes(0);
  assembly { revert(add(data, 32), mload(data)) }
}

theorem empty_raw_exact : (Prog.run σ₇ emptyRaw).halt? = some .revert := by
  decide +kernel

private def emptyReason := sol{
  string memory reason = "";
  revert(reason);
}

theorem empty_reason_exact : (Prog.run σ₇ emptyReason).halt? =
    some (.revertWith (Semantics.encodeError [])) := by
  decide +kernel

private def conditionBeforeReason := sol{
  require(result == 0, makeReason());
  assert(result == 1);
}

theorem condition_captured : (Prog.run σ₇ conditionBeforeReason).toOption.isSome = true := by
  decide +kernel

/-- The assembly operand follows the importer's renaming of Lean keywords. -/
theorem renamed_buffer_exact :
    (Prog.run (State.init Solc.RevertAssemblyRejected)
      Solc.RevertAssemblyRejected.renamed).halt? = some (.revertWith [9]) := by
  decide +kernel

/-- error: Solidity elaboration failed: a revert reason is a string; convert bytes with string(data) -/
#guard_msgs in
#check sol{ bytes memory data = hex"12"; revert(data); }

/-- error: Solidity elaboration failed: a revert reason is a string; convert bytes with string(data) -/
#guard_msgs in
#check sol{ bytes memory data = hex"12"; require(true, data); }

/-- error: Solidity elaboration failed: a revert reason is a string; convert bytes with string(data) -/
#guard_msgs in
#check sol{ revert(hex"ff"); }

/-- error: Solidity elaboration failed: a revert reason is a string; convert bytes with string(data) -/
#guard_msgs in
#check sol{ require(true, hex"ff"); }

/-- error: Solidity elaboration failed: a revert reason is a string; convert bytes with string(data) -/
#guard_msgs in
#check sol{ revert(string(hex"ff")); }

/-- error: Solidity elaboration failed: a revert reason is a string; convert bytes with string(data) -/
#guard_msgs in
#check sol{ revert(string.concat(hex"ff")); }

/-- error: Solidity elaboration failed: a revert reason is a string; convert bytes with string(data) -/
#guard_msgs in
#check sol{ revert(string(string(hex"ff"))); }

/-- error: Solidity elaboration failed: a revert reason is a string; convert bytes with string(data) -/
#guard_msgs in
#check sol{ revert(string(bytes(string(hex"ff")))); }

private def castReason := sol{
  bytes memory data = hex"12";
  require(false, string(data));
}

theorem cast_reason_exact : (Prog.run σ₇ castReason).halt? =
    some (.revertWith (Semantics.encodeError [0x12])) := by
  decide +kernel

theorem failed_concat_exact : (Prog.run σ₇ Solc.ComputedRevert.failedConcat).halt? =
    some (.revertWith (Semantics.encodeError [98, 33])) := by
  decide +kernel

theorem eager_failure_exact : (Prog.run σ₇ Solc.ComputedRevert.eagerFailure).halt? =
    some .revert := by
  decide +kernel

private def runtimeBytesReason := sol{
  bytes memory data = hex"ff";
  require(false, string(bytes(string(data))));
}

-- Runtime strings may contain bytes that are not valid UTF-8; the literal's
-- implicit conversion, unlike an explicit conversion of a bytes object, is checked.
theorem runtime_bytes_reason_exact : (Prog.run σ₇ runtimeBytesReason).halt? =
    some (.revertWith (Semantics.encodeError [0xff])) := by
  decide +kernel

private def unicodeHexReason := sol{ require(false, hex"c3a9"); }

theorem unicode_hex_reason_exact : (Prog.run σ₇ unicodeHexReason).halt? =
    some (.revertWith (Semantics.encodeError [0xc3, 0xa9])) := by
  decide +kernel

end Solidity.Examples.Tactics.ComputedRevert
