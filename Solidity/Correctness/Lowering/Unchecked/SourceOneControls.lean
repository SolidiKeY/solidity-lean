import Solidity.Correctness.Lowering.Unchecked.SourceSpelling
import Solidity.Syntax.Splice

/-!
# Typed Source association controls

Guards losing original Source widths, replacing the actual StmtD.toR result,
accepting a different local or operation direction, and confusing initial
prefix/postfix or compound spellings. Positive controls
supply real production typing derivations at every legal integer type; they
are structural checks, not sampled semantic runs. V4 controls also check the
combined typed Source/raw/model boundary; the full producer pass remains open.
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

private def byteType : Source.IntTy := ⟨false, 8, by decide⟩

private def byteValues {D : Source.Layout} : Source.Locals D [.int byteType] :=
  .cons (.int 255 (by decide)) .nil

private def byteStep (E : Source.Env) (unchecked : Bool) :
    Source.RStmt E [] false ⟨false, unchecked⟩ [.int byteType] [.int byteType] :=
  .expr (.incDec true true (.local .here))

/-- Guard losing checked panic bytes or the complete failure poststate in a
production bridge. The checked frame panics at uint8 maximum; the unchecked
frame wraps to zero. Both preserve the same complete interpreter state, and
the static statement contexts agree with their runtime checkedness modes. -/
theorem checked_panic_and_wrapping_poststate {E : Source.Env}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (plan : Source.FailureExecution.RuntimePlan) (known : Bool) (st : Source.St E) :
    (Source.execS G { F with checked := true } (fuel + 3) 0 none (byteStep E false)
      byteValues (plan := plan) (calldataKnown := known)).run (.nil, st) =
        (.error (.revert (Source.panicData .arithmetic)), (.nil, st)) ∧
    (Source.execS G { F with checked := false } (fuel + 3) 0 none (byteStep E true)
      byteValues (plan := plan) (calldataKnown := known)).run (.nil, st) =
        (.ok (.normal (.cons (Source.intWrap byteType 0) .nil)), (.nil, st)) := by
  cases known <;> exact ⟨rfl, rfl⟩

private theorem production_x_parses_as_user : FreshNames.parse "x" = none := by
  have scan : Substring.takeWhileAux "x" ⟨1⟩ (!·.isDigit) ⟨0⟩ = ⟨1⟩ := by
    rw [Substring.takeWhileAux]
    change Substring.takeWhileAux "x" ⟨1⟩ (!·.isDigit) ⟨1⟩ = ⟨1⟩
    rw [Substring.takeWhileAux]
    rfl
  have scannedStem : "x".takeWhile (!·.isDigit) = "x" := by
    change String.extract "x" ⟨0⟩ (Substring.takeWhileAux "x" ⟨1⟩ (!·.isDigit) ⟨0⟩) = "x"
    rw [scan]
    rfl
  change (FreshNames.ofPrefixes "se" "sp" "ie" "mv").parse "x" = none
  dsimp only [FreshNames.ofPrefixes]
  rw [scannedStem]
  rfl

private theorem production_x_name : Var.ofName "x" = .user "x" := by
  unfold Var.ofName
  rw [production_x_parses_as_user]

private theorem named_fixture {C : Contract} (ctx : NCtx) (input output : RawStmt)
    (program : Prog C ctx.ctx ctx.ctx) (raw : RawOneAssociation input output)
    (word : WordOneAssociation raw.source.inc program)
    (rawCheck : checkRawOne input output = some raw)
    (wordCheck : checkWordOne raw.source.inc program = some word)
    (binding : ((ctx.find (Var.ofName raw.source.name) (.val .uint)).toOption.map Subtype.val) =
      some word.target.slot) :
    checkNamedOne ctx input output program = some ⟨raw, word, binding⟩ := by
  unfold checkNamedOne
  simp only [rawCheck, wordCheck, bind, Option.bind, dif_pos binding]

private def ModelExample : Contract := contract!{}
private def emittedIncrement := sol[ModelExample]{ uint x = 0; unchecked { x++; }; }
private def emittedCompound := sol[ModelExample]{ uint x = 0; unchecked { x += 1; }; }
private def emittedChecked := sol[ModelExample]{ uint x = 0; x += 1; }

private def emittedBody (program : Prog ModelExample [] [.val .uint]) :
    Prog ModelExample [.val .uint] [.val .uint] :=
  match program with
  | .cons (.declLocal .uint _ _) rest => rest
  | _ => .nil

private def modelContext : NCtx := [(.user "x", .val .uint)]
private def rawInput : RawStmt := .incDec .postInc (.name "x")
private def rawOutput : RawStmt := .opAssign .addW (.name "x") (.num 1)

/-- Guards a vacuous typed boundary: a real Source typing derivation, actual
raw rewrite shape and actual quotation output all pass with the default
production FreshNames instance. This is a supplied-output control, not a
proof of the opaque producer pipeline. -/
theorem typed_pair_v4_increment_accepted (E : Source.Env) :
    (checkTypedPairV4 [] [] modelContext rawInput rawOutput
      (postfixDerivation E Source.IntTy.u256) (emittedBody emittedIncrement)).isSome = true := by
  let raw := (checkRawOne rawInput rawOutput).get (by rfl)
  let word := (checkWordOne raw.source.inc (emittedBody emittedIncrement)).get (by rfl)
  have binding : ((modelContext.find (Var.ofName raw.source.name) (.val .uint)).toOption.map Subtype.val) =
      some word.target.slot := by
    change ((modelContext.find (Var.ofName "x") (.val .uint)).toOption.map Subtype.val) = some .here
    rw [production_x_name]
    rfl
  have checked := named_fixture modelContext rawInput rawOutput
    (emittedBody emittedIncrement) raw word rfl rfl binding
  dsimp only [checkTypedPairV4]
  rw [checked]
  rfl

/-- Guards losing the compound arm while composing typed spelling and model
output. Both Source and target are the actual supplied objects. -/
theorem typed_pair_v4_compound_accepted (E : Source.Env) :
    (checkTypedPairV4 [] [] modelContext (.opAssign .add (.name "x") (.num 1)) rawOutput
      (compound E Source.IntTy.u256 rfl) (emittedBody emittedCompound)).isSome = true := by
  let raw := (checkRawOne (.opAssign .add (.name "x") (.num 1)) rawOutput).get (by rfl)
  let word := (checkWordOne raw.source.inc (emittedBody emittedCompound)).get (by rfl)
  have binding : ((modelContext.find (Var.ofName raw.source.name) (.val .uint)).toOption.map Subtype.val) =
      some word.target.slot := by
    change ((modelContext.find (Var.ofName "x") (.val .uint)).toOption.map Subtype.val) = some .here
    rw [production_x_name]
    rfl
  have checked := named_fixture modelContext (.opAssign .add (.name "x") (.num 1)) rawOutput
    (emittedBody emittedCompound) raw word rfl rfl binding
  dsimp only [checkTypedPairV4]
  rw [checked]
  rfl

/-- Guards accepting a narrow Source integer after erasing its original width. -/
theorem typed_pair_v4_width_rejected (E : Source.Env) :
    (checkTypedPairV4 [] [] modelContext rawInput rawOutput
      (postfixDerivation E byteType) (emittedBody emittedIncrement)).isNone = true := by
  rfl

/-- Guards associating the input name with a different actual Source identifier. -/
theorem typed_pair_v4_source_name_rejected (E : Source.Env) :
    (checkTypedPairV4 [] [] modelContext (.incDec .postInc (.name "y")) rawOutput
      (postfixDerivation E Source.IntTy.u256) (emittedBody emittedIncrement)).isNone = true := by
  rfl

/-- Guards accepting a model context where the actual input name is absent. -/
theorem typed_pair_v4_model_name_rejected (E : Source.Env) :
    (checkTypedPairV4 [] [] [(.user "y", .val .uint)] rawInput rawOutput
      (postfixDerivation E Source.IntTy.u256) (emittedBody emittedIncrement)).isNone = true := by
  let raw := (checkRawOne rawInput rawOutput).get (by rfl)
  let word := (checkWordOne raw.source.inc (emittedBody emittedIncrement)).get (by rfl)
  have missing : ¬((NCtx.find (Var.ofName raw.source.name) (.val .uint)
      [(.user "y", .val .uint)]).toOption.map Subtype.val) = some word.target.slot := by
    change ¬((NCtx.find (Var.ofName "x") (.val .uint)
      [(.user "y", .val .uint)]).toOption.map Subtype.val) = some .here
    rw [production_x_name]
    decide
  have rejected : checkNamedOne [(.user "y", .val .uint)] rawInput rawOutput
      (emittedBody emittedIncrement) = none := by
    unfold checkNamedOne
    have rawCheck : checkRawOne rawInput rawOutput = some raw := rfl
    have wordCheck : checkWordOne raw.source.inc (emittedBody emittedIncrement) = some word := rfl
    simp only [rawCheck, wordCheck, bind, Option.bind, dif_neg missing]
  dsimp only [checkTypedPairV4]
  rw [rejected]
  rfl

/-- Guards dropping the raw output's wrapping operation during composition. -/
theorem typed_pair_v4_rewrite_rejected (E : Source.Env) :
    (checkTypedPairV4 [] [] modelContext rawInput (.opAssign .add (.name "x") (.num 1))
      (postfixDerivation E Source.IntTy.u256) (emittedBody emittedIncrement)).isNone = true := by
  rfl

/-- Guards certifying a checked actual target despite a valid wrapping raw output. -/
theorem typed_pair_v4_checked_target_rejected (E : Source.Env) :
    (checkTypedPairV4 [] [] modelContext rawInput rawOutput
      (postfixDerivation E Source.IntTy.u256) (emittedBody emittedChecked)).isNone = true := by
  rfl

private def emittedExtra := sol[ModelExample]{ bool flag = false; uint x = 0; unchecked { x++; }; }
private def extraContext : NCtx := [(.user "x", .val .uint), (.user "flag", .val .bool)]

private def extraBody (program : Prog ModelExample [] [.val .uint, .val .bool]) :
    Prog ModelExample [.val .uint, .val .bool] [.val .uint, .val .bool] :=
  match program with
  | .cons (.declLocal .bool _ _) (.cons (.declLocal .uint _ _) rest) => rest
  | _ => .nil

/-- Guards ignoring model context alignment: the actual larger-context output
passes the named update check, but cannot pair with a one-local Source input. -/
theorem typed_pair_v4_context_alignment (E : Source.Env) :
    (checkNamedOne extraContext rawInput rawOutput (extraBody emittedExtra)).isSome = true ∧
    (checkTypedPairV4 [] [] extraContext rawInput rawOutput
      (postfixDerivation E Source.IntTy.u256) (extraBody emittedExtra)).isNone = true := by
  constructor
  · let raw := (checkRawOne rawInput rawOutput).get (by rfl)
    let word := (checkWordOne raw.source.inc (extraBody emittedExtra)).get (by rfl)
    have binding : ((extraContext.find (Var.ofName raw.source.name) (.val .uint)).toOption.map Subtype.val) =
        some word.target.slot := by
      change ((extraContext.find (Var.ofName "x") (.val .uint)).toOption.map Subtype.val) = some .here
      rw [production_x_name]
      rfl
    rw [named_fixture extraContext rawInput rawOutput (extraBody emittedExtra) raw word rfl rfl binding]
    rfl
  · rfl

#print axioms typed_pair_v4_context_alignment

#print axioms typed_pair_v4_increment_accepted
#print axioms typed_pair_v4_compound_accepted
#print axioms typed_pair_v4_width_rejected
#print axioms typed_pair_v4_source_name_rejected
#print axioms typed_pair_v4_model_name_rejected
#print axioms typed_pair_v4_rewrite_rejected
#print axioms typed_pair_v4_checked_target_rejected

#print axioms checked_panic_and_wrapping_poststate

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
