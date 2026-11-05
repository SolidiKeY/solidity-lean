import Solidity.Frontend.QualifiedUnits.SignatureResolution
import Solidity.Frontend.QualifiedUnits.SignatureMemberControls
import Solidity.Frontend.QualifiedUnits.CheckedControls

/-! Kernel observations for the actual signature-aware resolver. Each main
compiler query has a paired theorem; external compiler graph comparisons
remain separate from these intrinsic fixture transcriptions. -/
namespace Solidity.Frontend.QualifiedUnits.SignatureResolutionControls
open Solidity.Source Controls

theorem multi_hop_0 : SignatureResolution.resolve DifferentialControls.hopsInput [] "A.sol" none [] ⟨"N", ["M", "T"]⟩ = .ok [.decl ⟨"C.sol", 0⟩] := by
  rfl

theorem missing_symbol_0 : SignatureResolution.resolve DifferentialControls.missingInput [] "A.sol" none [] ⟨"N", ["M", "Missing"]⟩ = .error .missing := by
  rfl

theorem ambiguous_namespace_0 : SignatureResolution.resolve DifferentialControls.ambiguousInput [] "A.sol" none [] ⟨"N", ["T"]⟩ = .error .ambiguous := by
  rfl

theorem same_spelling_units_0 : SignatureResolution.resolve DifferentialControls.spellingInput [] "A.sol" none [] ⟨"L", ["T"]⟩ = .ok [.decl ⟨"B.sol", 0⟩] := by
  rfl

theorem same_spelling_units_1 : SignatureResolution.resolve DifferentialControls.spellingInput [] "A.sol" none [] ⟨"R", ["T"]⟩ = .ok [.decl ⟨"C.sol", 0⟩] := by
  rfl

theorem symbol_namespace_alias_0 : SignatureResolution.resolve DifferentialControls.aliasInput [] "A.sol" none [] ⟨"N", ["T"]⟩ = .ok [.decl ⟨"C.sol", 0⟩] := by
  rfl

theorem transitive_all_0 : SignatureResolution.resolve DifferentialControls.allInput [] "A.sol" none [] ⟨"N", ["T"]⟩ = .ok [.decl ⟨"C.sol", 0⟩] := by
  rfl

theorem diamond_identity_0 : SignatureResolution.resolve DifferentialControls.diamondInput [] "A.sol" none [] ⟨"T", []⟩ = .ok [.decl ⟨"C.sol", 0⟩] := by
  rfl

theorem cyclic_namespace_0 : SignatureResolution.resolve DifferentialControls.cycleInput [] "A.sol" none [] ⟨"N", ["Back", "N", "T"]⟩ = .ok [.decl ⟨"B.sol", 0⟩] := by
  rfl

theorem private_base_fallback_0 : SignatureResolution.resolve (DifferentialControls.shadowInput .priv) [] "A.sol" (some ⟨"A.sol", 2⟩) [] ⟨"N", ["T"]⟩ = .ok [.decl ⟨"C.sol", 0⟩] := by
  rfl

theorem visible_base_shadow_0 : SignatureResolution.resolve (DifferentialControls.shadowInput .internal) [] "A.sol" (some ⟨"A.sol", 2⟩) [] ⟨"N", ["T"]⟩ = .error .missing := by
  rfl

theorem local_shadow_0 : SignatureResolution.resolve DifferentialControls.localInput [] "A.sol" (some ⟨"A.sol", 0⟩) ["N"] ⟨"N", ["T"]⟩ = .error (.localShadow 0) := by
  rfl

theorem inherited_type_0 : SignatureResolution.resolve DifferentialControls.inheritedInput [] "A.sol" none [] ⟨"N", ["Base"]⟩ = .ok [.decl ⟨"B.sol", 0⟩] := by
  rfl

theorem inherited_type_1 : SignatureResolution.resolve DifferentialControls.inheritedInput [] "A.sol" none [] ⟨"D", ["S"]⟩ = .ok [.decl ⟨"B.sol", 1⟩] := by
  rfl

theorem ambiguous_base_0 : SignatureResolution.resolve DifferentialControls.ambiguousBaseInput [] "A.sol" none [] ⟨"D", ["S"]⟩ = .error .missing := by
  rfl

theorem inherited_overload_gap_0 : SignatureResolution.resolve DifferentialControls.inheritedOverloadInput [] "A.sol" (some ⟨"A.sol", 0⟩) [] ⟨"f", []⟩ = .ok [.decl ⟨"A.sol", 1⟩, .decl ⟨"B.sol", 1⟩] := by
  rfl

theorem qualified_parameter_overload_gap_0 : SignatureResolution.resolve DifferentialControls.qualifiedOverloadInput [] "A.sol" (some ⟨"A.sol", 0⟩) [] ⟨"f", []⟩ = .ok [.decl ⟨"A.sol", 1⟩, .decl ⟨"B.sol", 2⟩] := by
  rfl

def failedSignatureGlobal : UnitSet := ⟨[("A",unitOf [.topPart (.enum "f" "a" []),
  .contract false "D" .none .nil (.cons (SignatureGap.functionOf (.userType ⟨"Absent",[]⟩) 1) .nil)])]⟩

theorem failed_signature_no_global_fallback : SignatureResolution.resolve failedSignatureGlobal [] "A"
    (some ⟨"A",1⟩) [] ⟨"f",[]⟩ = .error .missing := by rfl

theorem own_private_still_shadows : SignatureResolution.resolve CheckedControls.privateBase [] "A"
    (some ⟨"A",0⟩) [] ⟨"N",["T"]⟩ = .error .missing := by rfl

theorem visible_nonoverload_still_shadows : SignatureResolution.resolve CheckedControls.visibleBase [] "A"
    (some ⟨"A",2⟩) [] ⟨"N",["T"]⟩ = .error .missing := by rfl

theorem private_base_global_fallback : SignatureResolution.resolve CheckedControls.privateBase [] "A"
    (some ⟨"A",2⟩) [] ⟨"N",["T"]⟩ = .ok [.decl ⟨"C",0⟩] := by rfl

theorem diamond_override_identity : SignatureResolution.resolve SignatureMemberControls.overrideDiamond [] "A"
    (some ⟨"A",5⟩) [] ⟨"f",[]⟩ = .ok [.decl ⟨"A",4⟩] := by rfl

theorem external_location_override : SignatureResolution.resolve
    (NormalizationControls.locations .calldata .memory .external .pub) [] "A"
    (some ⟨"A",2⟩) [] ⟨"f",[]⟩ = .ok [.decl ⟨"A",3⟩] := by rfl

theorem foreign_scope_refused : SignatureResolution.resolve Controls.hops [] "A"
    (some ⟨"C",0⟩) [] ⟨"N",["M","T"]⟩ = .error .invalidScope := by rfl

def visibleBarrier : UnitSet := ⟨[("A",unitOf [
  .contract false "A" .none .nil (.cons (SignatureGap.functionOf SignatureGap.uintTy 1) .nil),
  .contract false "B" .none (.cons (.inherit ⟨"A",[]⟩ .none) .nil)
    (.cons (.stateVar (.elem .bool) (some .internal) none none false "f" .none) .nil),
  .contract false "D" .none (.cons (.inherit ⟨"B",[]⟩ .none) .nil)
    (.cons (SignatureGap.functionOf (.elem .bool) 2) .nil)])]⟩

theorem visible_intermediate_barrier_refused : SignatureResolution.resolve visibleBarrier [] "A"
    (some ⟨"A",4⟩) [] ⟨"f",[]⟩ = .error .missing := by rfl

theorem qualified_barrier_refused : SignatureResolution.resolve visibleBarrier [] "A"
    none [] ⟨"D",["f"]⟩ = .error .missing := by rfl

def getterOverride : UnitSet := ⟨[("A",unitOf [
  .contract true "A" .none .nil (.cons
    (.function (.ident "f") .nil (some .external) (some .view) .nil true none
      (.cons (.param (.elem .bool) none none) .nil) .none) .nil),
  .contract false "B" .none (.cons (.inherit ⟨"A",[]⟩ .none) .nil)
    (.cons (.stateVar (.elem .bool) (some .pub) none none false "f" .none) .nil)])]⟩

theorem getter_override_identity : SignatureResolution.resolve getterOverride [] "A"
    (some ⟨"A",2⟩) [] ⟨"f",[]⟩ = .ok [.decl ⟨"A",3⟩] := by rfl

end Solidity.Frontend.QualifiedUnits.SignatureResolutionControls
