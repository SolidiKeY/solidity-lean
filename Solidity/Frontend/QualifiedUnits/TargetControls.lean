import Solidity.Frontend.QualifiedUnits.Target
import Solidity.Frontend.QualifiedUnits.NormalizationAdequacy
import Solidity.Frontend.QualifiedUnits.SignatureResolutionControls

/-! Kernel controls for the independent C3 judgment, the final target relation
and normalization adequacy. Positive controls derive the declarative judgment
from an executed run through the proved equivalences; negative controls show
that no derivation exists. These are intrinsic fixture transcriptions, not
external compiler evidence. -/
namespace Solidity.Frontend.QualifiedUnits.TargetControls
open Solidity.Source Controls SignatureGap SignatureMembers Linearization

/-- Nontrivial diamond D is L, R; L is B; R is B: one shared base identity. -/
theorem diamond_linear : Linear SignatureMemberControls.overrideDiamond [] ⟨"A",5⟩
    [⟨"A",5⟩,⟨"A",3⟩,⟨"A",2⟩,⟨"A",0⟩] :=
  order_iff.mp SignatureMemberControls.diamond_owner_order

/-- The shared base B occurs once and after both of its derived contracts. -/
theorem diamond_shared_base_once : ([⟨"A",5⟩,⟨"A",3⟩,⟨"A",2⟩,⟨"A",0⟩] : List DeclId).Nodup :=
  diamond_linear.bounded.1

theorem diamond_local_precedence :
    ([⟨"A",3⟩,⟨"A",2⟩] : List DeclId).Sublist [⟨"A",3⟩,⟨"A",2⟩,⟨"A",0⟩] := by
  have hb : Bases SignatureMemberControls.overrideDiamond [] ⟨"A",5⟩ [⟨"A",2⟩,⟨"A",3⟩] :=
    bases_iff.mp (by decide +kernel)
  exact (diamond_linear.precedence hb).1

/-- A self-inheriting contract has no linearization at all. -/
theorem cycle_no_linear : ¬ ∃ out, Linear SignatureMemberControls.cyclicBase [] ⟨"A",0⟩ out := by
  intro ⟨out, h⟩
  have ho := order_iff.mpr h
  have hn : order SignatureMemberControls.cyclicBase [] ⟨"A",0⟩ = none := by decide +kernel
  rw [hn] at ho
  cases ho

/-- A missing written base refuses the hierarchy rather than vanishing. -/
theorem missing_base_no_linear : ¬ ∃ out, Linear SignatureMemberControls.missingBase [] ⟨"A",0⟩ out := by
  intro ⟨out, h⟩
  have ho := order_iff.mpr h
  have hn : order SignatureMemberControls.missingBase [] ⟨"A",0⟩ = none := by decide +kernel
  rw [hn] at ho
  cases ho

/-- Inherited overload: the base B.f(uint) is a target answer beside D.f(bool). -/
theorem inherited_overload_target :
    Target.Target DifferentialControls.inheritedOverloadInput [] "A.sol" (some ⟨"A.sol",0⟩) [] ⟨"f",[]⟩
      (.decl ⟨"B.sol",1⟩) :=
  Target.target_iff.mp ⟨_, SignatureResolutionControls.inherited_overload_gap_0, by decide⟩

/-- Cross-unit same-spelled parameter types keep the base overload distinct. -/
theorem qualified_parameter_overload_target :
    Target.Target DifferentialControls.qualifiedOverloadInput [] "A.sol" (some ⟨"A.sol",0⟩) [] ⟨"f",[]⟩
      (.decl ⟨"B.sol",2⟩) :=
  Target.target_iff.mp ⟨_, SignatureResolutionControls.qualified_parameter_overload_gap_0, by decide⟩

/-- Successful multi-hop qualified reference N.M.T. -/
theorem multi_hop_target :
    Target.Target DifferentialControls.hopsInput [] "A.sol" none [] ⟨"N",["M","T"]⟩ (.decl ⟨"C.sol",0⟩) :=
  Target.target_iff.mp ⟨_, SignatureResolutionControls.multi_hop_0, by decide⟩

theorem missing_symbol_no_target :
    ∀ s, ¬ Target.Target DifferentialControls.missingInput [] "A.sol" none [] ⟨"N",["M","Missing"]⟩ s :=
  Target.refused_no_target SignatureResolutionControls.missing_symbol_0

theorem ambiguous_no_target :
    ∀ s, ¬ Target.Target DifferentialControls.ambiguousInput [] "A.sol" none [] ⟨"N",["T"]⟩ s :=
  Target.refused_no_target SignatureResolutionControls.ambiguous_namespace_0

theorem local_shadow_no_target :
    ∀ s, ¬ Target.Target DifferentialControls.localInput [] "A.sol" (some ⟨"A.sol",0⟩) ["N"] ⟨"N",["T"]⟩ s :=
  Target.refused_no_target SignatureResolutionControls.local_shadow_0

theorem failed_signature_no_target :
    ∀ s, ¬ Target.Target SignatureResolutionControls.failedSignatureGlobal [] "A" (some ⟨"A",1⟩) [] ⟨"f",[]⟩ s :=
  Target.refused_no_target SignatureResolutionControls.failed_signature_no_global_fallback

theorem visible_barrier_no_target :
    ∀ s, ¬ Target.Target SignatureResolutionControls.visibleBarrier [] "A" (some ⟨"A",4⟩) [] ⟨"f",[]⟩ s :=
  Target.refused_no_target SignatureResolutionControls.visible_intermediate_barrier_refused

/-- A nested function type normalizes; its erasure is the Source elaboration. -/
theorem callable_erases :
    (SignatureNormalization.types DifferentialControls.hopsInput [] "A.sol" none .memory
      (.fnType (.cons (.param (.elem .bool) none none) .nil) (some .external) none .nil)).map
        (·.map NormalizationAdequacy.erase) =
      some [.fn true [.bool] [] none] := rfl

/-- Struct members are not signature syntax and are refused, not guessed. -/
theorem struct_member_refused :
    SignatureNormalization.types DifferentialControls.hopsInput [] "A.sol" none .memory
      (.structMember (.elem .bool) "x") = none :=
  (NormalizationAdequacy.fields_refused .memory (.elem .bool) "x" none).1

end Solidity.Frontend.QualifiedUnits.TargetControls
