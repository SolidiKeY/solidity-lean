import Solidity.Correctness.Lowering.Unchecked.SourceSpelling

/-!
# Typed Source association controls

Guards losing original Source widths, replacing the actual StmtD.toR result,
accepting a different local or operation direction, and confusing initial
prefix/postfix or compound spellings. Positive controls
supply real production typing derivations at every legal integer type; they
are structural checks, not sampled semantic runs or a Source/model bridge.
-/
namespace Solidity.Correctness.Lowering.Unchecked.SourceOneControls

private def context (E : Source.Env) : Source.Ctx :=
  { env := E, scope := none, locals := [] }

private def locals (t : Source.IntTy) : List (String × Source.STy) := [("x", .int t)]

private def raw : RawOneInput (.incDec .postInc (.name "x")) :=
  ⟨true, "x", .inr ⟨.postInc, rfl, rfl⟩⟩

private def decrement : RawOneInput (.incDec .postDec (.name "x")) :=
  ⟨false, "x", .inr ⟨.postDec, rfl, rfl⟩⟩

private def postfixDerivation (E : Source.Env) (t : Source.IntTy) :
    Source.StmtD (context E) (k := ⟨false, true⟩) (locals t)
      (.simpleStmt (.exprStmt (.unarySuffix .inc (.ident "x")))) (locals t) :=
  .expr (.incDecSuffix (.loc rfl rfl) rfl) rfl

private def compound (E : Source.Env) (t : Source.IntTy)
    (fits : Source.AssignOp.add.fits E.isBase E.mapFree
      (.rational (Source.Q.ofInt 1)) (.int t) = true) :
    Source.StmtD (context E) (k := ⟨false, true⟩) (locals t)
      (.simpleStmt (.exprStmt (.assign .add (.ident "x") (.lit (.num (.dec 1 0 0)))))) (locals t) :=
  .expr (.compound (.loc rfl rfl) (.const rfl rfl rfl) fits) rfl

/-- Actual postfix typing reaches an accepted resolved statement. -/
theorem typed_postfix_accepted (E : Source.Env) (t : Source.IntTy) :
    (checkTypedSourceOne raw (postfixDerivation E t)).isSome = true := by
  rfl

/-- The recognized type is the original Source type, including its width. -/
theorem original_width_retained (E : Source.Env) (t : Source.IntTy) :
    (checkTypedSourceOne raw (postfixDerivation E t)).map (·.type) = some t := by
  rfl

/-- A real compound typing derivation uses the same normalization family.
The fits argument is precisely the production typing constructor's premise. -/
theorem typed_compound_accepted (E : Source.Env) (t : Source.IntTy)
    (fits : Source.AssignOp.add.fits E.isBase E.mapFree
      (.rational (Source.Q.ofInt 1)) (.int t) = true) :
    (checkTypedSourceOne raw (compound E t fits)).isSome = true := by
  rfl

/-- An actual increment must not certify the opposite raw update direction. -/
theorem wrong_direction_rejected (E : Source.Env) (t : Source.IntTy) :
    (checkTypedSourceOne decrement (postfixDerivation E t)).isNone = true := by
  rfl

private def twoLocals (t : Source.IntTy) : List (String × Source.STy) :=
  [("x", .int t), ("y", .int t)]

private def otherLocal (E : Source.Env) (t : Source.IntTy) :
    Source.StmtD (context E) (k := ⟨false, true⟩) (twoLocals t)
      (.simpleStmt (.exprStmt (.unarySuffix .inc (.ident "y")))) (twoLocals t) :=
  .expr (.incDecSuffix (.loc rfl rfl) rfl) rfl

/-- Direction/type alone cannot associate a different actual Source local. -/
theorem wrong_source_local_rejected (E : Source.Env) (t : Source.IntTy) :
    (checkTypedSourceOne raw (otherLocal E t)).isNone = true := by
  rfl

/-- Exact initial raw and Source postfix spellings associate. -/
theorem typed_spelling_accepted (E : Source.Env) (t : Source.IntTy) :
    (checkTypedSourceSpelling (.incDec .postInc (.name "x")) (postfixDerivation E t)).isSome = true := by
  rfl

/-- Discarded-result equivalence does not justify changing the input spelling. -/
theorem prefix_suffix_mismatch_rejected (E : Source.Env) (t : Source.IntTy) :
    (checkTypedSourceSpelling (.incDec .preInc (.name "x")) (postfixDerivation E t)).isNone = true := by
  rfl

/-- The raw name must be the actual initial Source identifier. -/
theorem typed_raw_name_rejected (E : Source.Env) (t : Source.IntTy) :
    (checkTypedSourceSpelling (.incDec .postInc (.name "y")) (postfixDerivation E t)).isNone = true := by
  rfl

/-- Canonical compound syntax passes the combined initial/typed boundary. -/
theorem typed_compound_spelling_accepted (E : Source.Env) (t : Source.IntTy)
    (fits : Source.AssignOp.add.fits E.isBase E.mapFree
      (.rational (Source.Q.ofInt 1)) (.int t) = true) :
    (checkTypedSourceSpelling (.opAssign .add (.name "x") (.num 1)) (compound E t fits)).isSome = true := by
  rfl

/-- A normalization-related compound is not the spelling of an initial ++. -/
theorem cross_family_spelling_rejected (E : Source.Env) (t : Source.IntTy)
    (fits : Source.AssignOp.add.fits E.isBase E.mapFree
      (.rational (Source.Q.ofInt 1)) (.int t) = true) :
    (checkTypedSourceSpelling (.incDec .postInc (.name "x")) (compound E t fits)).isNone = true := by
  rfl

#print axioms typed_postfix_accepted
#print axioms original_width_retained
#print axioms typed_compound_accepted
#print axioms wrong_direction_rejected
#print axioms wrong_source_local_rejected
#print axioms typed_spelling_accepted
#print axioms prefix_suffix_mismatch_rejected
#print axioms typed_raw_name_rejected
#print axioms typed_compound_spelling_accepted
#print axioms cross_family_spelling_rejected

end Solidity.Correctness.Lowering.Unchecked.SourceOneControls
