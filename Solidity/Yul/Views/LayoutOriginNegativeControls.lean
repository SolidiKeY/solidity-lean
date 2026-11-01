import Solidity.Yul.Views.LayoutOriginControls

namespace Solidity.Yul.Views.Controls

def originFraction : Source.Syn .expr := .lit (.num (.dec 5 1 0))
def originTooLarge : Source.Syn .expr := .lit (.num (.dec (2^256) 0 0))
def originMax : Source.Syn .expr := .lit (.num (.dec (2^256-1) 0 0))
def originArithmetic : Source.Syn .expr := .addSub .add (.lit (.num (.dec 40 0 0))) (.lit (.num (.dec 2 0 0)))

theorem origin_fraction_not_truncated : prepareLiteralOrigin originFraction = .error .outOfRange := rfl
theorem origin_large_not_wrapped : prepareLiteralOrigin originTooLarge = .error .outOfRange := rfl
theorem origin_max_exact : (prepareLiteralOrigin originMax).toOption.map ExactLiteralOrigin.value = some ⟨2^256-1,by decide⟩ := rfl

theorem origin_arithmetic_owner_value : originArithmetic.const = some (Source.Q.ofInt 42) := rfl
theorem origin_arithmetic_profile_unchanged : prepareLiteralOrigin originArithmetic = .error .outsideProfile := rfl

theorem origin_arithmetic_owner_exclusion :
    (Source.Syn.contract false "Expr" (.some originArithmetic) .nil .nil).excl = some .storageLayout := rfl

theorem origin_negative_owner_range : ¬ (Source.Q.ofInt (-1)).FitsInt .u256 := by decide

def originMissingActive : Source.Env := ⟨originEnv.decls.filter (fun d => d.name != "D")⟩
theorem origin_missing_active_diagnosed : prepareActiveOrigin originMissingActive "D" = .error (.hierarchy .malformedLineage) := rfl

def originDuplicateActive : Source.Env := ⟨originEnv.decls ++ [⟨.contract,"D",none,true,.contract false "D" .none .nil .nil⟩]⟩
theorem origin_duplicate_active_diagnosed : prepareActiveOrigin originDuplicateActive "D" = .error (.hierarchy .duplicateContracts) := rfl

def originMalformedActive : Source.Env := ⟨originEnv.decls.map (fun d => if d.name = "D" then
  ⟨.contract,"D",none,true,.contract false "Wrong" .none .nil .nil⟩ else d)⟩
theorem origin_mismatched_active_diagnosed : prepareActiveOrigin originMalformedActive "D" = .error .malformedActive := rfl

theorem origin_base_deployed_independently :
    (prepareActiveOrigin originEnv "A").toOption.map ActiveLayoutOrigin.persistent = some 0 := rfl

def originWithBase (base : Source.Syn .expr) : Source.Env := ⟨originEnv.decls.map (fun d => if d.name = "D" then
  ⟨.contract,"D",none,true,.contract false "D" (.some base)
    (.cons (.inherit ⟨"B",[]⟩ .none) (.cons (.inherit ⟨"C",[]⟩ .none) .nil)) .nil⟩ else d)⟩

theorem origin_fraction_active_diagnosed : prepareActiveOrigin (originWithBase originFraction) "D" = .error .outOfRange := rfl

theorem origin_source_profile_not_silently_expanded :
    prepareActiveOrigin (originWithBase originArithmetic) "D" = .error .outsideProfile := rfl

/-- The numeric origin is representable, but the existing whole declaration
span cannot fit; this is distinct from modulo wrapping or numeric conversion. -/
theorem origin_span_nonwrapping_failure :
    (originDeclarations.pack account ((2^256-1)*32)).toOption.isNone := by decide

end Solidity.Yul.Views.Controls

namespace Solidity.Yul.Views.Controls

def originDeclarationsAt (base : Source.Syn .expr) : RootDeclarations (originWithBase base) originDeclTypes :=
  .cons (.scalar (.int originU8) (by rfl)) (.cons (.scalar (.int originU248) (by rfl))
    (.cons (.scalar .bool (by rfl))
      (.cons (.array 2 (by decide) (.strct ⟨none,"DiamondInner"⟩ [("flag",.bool),("small",.int unsigned16)] rfl
        (.cons (.scalar .bool (by rfl)) (.cons (.scalar (.int unsigned16) (by rfl)) .nil))))
        (.cons (.scalar (.int originU248) (by rfl))
          (.cons (.scalar (.int unsigned16) (by rfl)) (.cons (.scalar (.int .u256) (by rfl)) .nil))))))

theorem origin_full_entry_span_failure :
    (prepareComputedLayout (originDeclarationsAt originMax) "D" false account).toOption.isNone := by decide

theorem origin_integral_decimal :
    (prepareLiteralOrigin (.lit (.num (.dec 420 1 0)))).toOption.map ExactLiteralOrigin.value = some 42 := rfl

theorem origin_integral_exponent :
    (prepareLiteralOrigin (.lit (.num (.dec 42 2 2)))).toOption.map ExactLiteralOrigin.value = some 42 := rfl

/-- Exact preservation of success at a representable numeric origin is not
success of an overflowing physical declaration span. -/
theorem origin_max_numeric_but_not_layout :
    (prepareActiveOrigin (originWithBase originMax) "D").toOption.isSome ∧
    (prepareComputedLayout (originDeclarationsAt originMax) "D" false account).toOption.isNone := by decide

end Solidity.Yul.Views.Controls
