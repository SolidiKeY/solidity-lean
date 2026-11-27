import Solidity.Correctness.Lowering.Total.Decode.Callee.Metadata

/-! Refusal-boundary regressions for the frozen decoder. These checks expose
obstructions that the additive full-domain decoder must overcome; they do not
claim full-domain coverage or certify a new semantic boundary. -/
namespace Solidity.Examples.Lowering.Total.FullDomain

open Solidity.Correctness.Lowering.Total

/-- Every callee body is refused by the frozen request guard, independently
of its statement family, declaration, caller settings or recursive scope. -/
theorem callee_refused (T : Decode.Tables)
    (spell : RawExpr → Option (Source.Syn .expr)) (r : Request) (c : CalleeRequest)
    (h : r.callee = some c) : Decode.WithExpr.decode T spell r = none := by
  simp [Decode.WithExpr.decode, Decode.plain, h]

/-- Explicit caller return slots are outside the frozen request decoder. -/
theorem returnSlots_refused (T : Decode.Tables)
    (spell : RawExpr → Option (Source.Syn .expr)) (r : Request) (slots : List String)
    (h : r.input.returnSlots = some slots) : Decode.WithExpr.decode T spell r = none := by
  simp [Decode.WithExpr.decode, Decode.plain, h]

/-- Caller unchecked mode is outside the frozen request decoder. -/
theorem unchecked_refused (T : Decode.Tables)
    (spell : RawExpr → Option (Source.Syn .expr)) (r : Request)
    (h : r.input.scope.unchecked = true) : Decode.WithExpr.decode T spell r = none := by
  simp [Decode.WithExpr.decode, Decode.plain, h]

/-- Explicit overflow policy is outside the frozen request decoder. -/
theorem overflow_refused (T : Decode.Tables)
    (spell : RawExpr → Option (Source.Syn .expr)) (r : Request) (mode : OFMode)
    (h : r.input.scope.overflow = some mode) : Decode.WithExpr.decode T spell r = none := by
  simp [Decode.WithExpr.decode, Decode.plain, h]

/-- A checked block is refused by the shared statement traversal, even with
an arbitrary expression spelling and type table. -/
theorem checked_refused (T : Decode.Tables)
    (spell : RawExpr → Option (Source.Syn .expr)) (k : Source.SCtx) (mode : OFMode) (b : List RawStmt) :
    Decode.Tables.WithExpr.stmt T spell k (.checked mode b) = none := rfl

/-- Retained source metadata is required by the landed ordinary-function
assembler; absent metadata cannot silently become a fabricated header. -/
theorem missingMetadata_refused (T : Decode.Tables) (R : CallSpellExt.Registry)
    (scope : String) (d : FunDecl) (h : d.sourceDecl = none) :
    Decode.Callee.fromMetadata T R scope d = none := by
  simp [Decode.Callee.fromMetadata, h]

end Solidity.Examples.Lowering.Total.FullDomain
