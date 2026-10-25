import Solidity.Semantics.Ops
import Solidity.Calculus.Step
import Solidity.Calculus.Lands
import Solidity.Semantics.RunFuel
import Plausible

/-!
Executable local-rule tests. These run the emitted update and the typed
statement separately and compare observations, including failures. An
unsupported premise is `none`, never a passing test. This initial corpus
covers numeric local assignment, compound assignment and increment rules;
it is deliberately separate from universal kernel-checked soundness proofs.
-/
namespace Solidity.Bridge.PropertyChecks

/-- Compare a candidate update with execution. Ordinary failure must revert;
panic and fuel exhaustion cannot silently match a failed update. -/
def checkUpdateWith {C : Contract} {Γ Δ : Ctx} {β : Type} [DecidableEq β]
    (σ : State C Γ) (s : Stmt C Γ Δ) (U : Upd C Γ Δ)
    (observe : State C [] → LocsV C Δ → β) : Bool :=
  let expected := TRes.ofOpt ((U.applyV σ).map (fun q => observe q.1.1 q.2))
  let actual := (s.runF 4 σ).map (fun o => observe o.st.glob o.st.locV)
  match actual, expected with
  | .ok a, .ok b => decide (a = b)
  | .error a, .error b => decide (a = b)
  | _, _ => false

/-- Test the update emitted by the rule table. `none` reports an unsupported
premise shape, rather than quietly accepting it. -/
def checkUpdate {C : Contract} {Γ Δ : Ctx} {β : Type} [DecidableEq β]
    (σ : State C Γ) (s : Stmt C Γ Δ)
    (observe : State C [] → LocsV C Δ → β) : Option Bool :=
  match s.step 0 .diamond with
  | .update U => some (checkUpdateWith σ s U observe)
  | _ => none

structure WordSample where
  word : BitVec 256
  deriving Repr

instance : Plausible.Shrinkable WordSample where
  shrink x := (Plausible.Nat.shrink x.word.toNat).map (fun n => ⟨BitVec.ofNat 256 n⟩)

/-- Uniform full-word samples mixed with the arithmetic boundaries. Plausible's
default BitVec generator only samples small naturals at its default size. -/
instance : Plausible.SampleableExt WordSample :=
  Plausible.SampleableExt.mkSelfContained do
    let tag ← Plausible.Gen.chooseNatLt 0 6 (by decide)
    let n ← Plausible.Gen.chooseNatLt 0 (2^256) (by decide)
    return ⟨BitVec.ofNat 256 (match tag.val with
      | 0 => 0 | 1 => 1 | 2 => 2^256 - 1 | 3 => 2^255 | 4 => 2^255 - 1 | _ => n.val)⟩

private abbrev context (p : PrimTy) : Ctx := [.val p, .val p]

private def state (p : PrimTy) (x y : p.Denote) : State StandardExample (context p) :=
  ((State.init StandardExample).push (t := .val p) y).push (t := .val p) x

private def observe (p : PrimTy) (v : LocsV StandardExample (context p)) :
    p.Denote × p.Denote := (v _ .here, v _ (.there .here))

private def numericCases (p : PrimTy) (hp : p.isNumeric = true) :
    List (String × Stmt StandardExample (context p) (context p)) :=
  let rhs : Val StandardExample (context p) p := .simple (.local (.there .here))
  let lhs : Val StandardExample (context p) p := .simple (.local .here)
  let ops : List {op : BinOp // op.hasCompoundAssign = true} :=
    [⟨.add, rfl⟩, ⟨.sub, rfl⟩, ⟨.mul, rfl⟩, ⟨.div, rfl⟩, ⟨.mod, rfl⟩]
  let assignments := ops.flatMap fun ⟨op, hop⟩ =>
    let v := Val.binop op (BinOp.compound_accepts hop hp) (BinOp.compound_ret hop p) lhs rhs
    [(s!"binopAssignment/{op.sym}", .assignLocal .here v),
      (s!"localOpAssign/{op.sym}", .opAssign op hop hp (.local .here) rhs)]
  assignments ++ [IncDec.preInc, IncDec.preDec, IncDec.postInc, IncDec.postDec].flatMap (fun op =>
    [(s!"localIncrement/{repr op}", .incDec op hp (.local .here)),
      (s!"localAssignIncrement/{repr op}",
        .assignIncDec (.there .here) op hp (.local .here) rfl)])

private def uintSample (x : WordSample) : PrimTy.uint.Denote :=
  ⟨x.word.toNat, by
    simp only [PrimTy.inRange, decide_eq_true_eq]
    exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr x.word.isLt⟩⟩

set_option maxRecDepth 2048 in
private def intSample (x : WordSample) : PrimTy.int.Denote :=
  ⟨x.word.toInt, by
    simp only [PrimTy.inRange, decide_eq_true_eq]
    exact ⟨BitVec.le_toInt x.word, BitVec.toInt_lt⟩⟩

private def checkGroup (p : PrimTy) (hp : p.isNumeric = true)
    (decode : WordSample → p.Denote) (cfg : Plausible.Configuration) : IO Nat := do
  let cases := numericCases p hp
  let seed := cfg.randomSeed.map toString |>.getD "random"
  for (name, s) in cases do
    let property := Plausible.NamedBinder "x" (∀ x : WordSample,
      Plausible.NamedBinder "y" (∀ y : WordSample,
        checkUpdate (state p (decode x) (decode y)) s (fun _ => observe p) = some true))
    match ← Plausible.Testable.checkIO property cfg with
    | .success _ => pure ()
    | .gaveUp n => throw (IO.userError s!"{repr p}/{name} (seed {seed}): gave up after {n} samples")
    | .failure _ values shrinks =>
      throw (IO.userError (Plausible.Testable.formatFailure
        s!"{repr p}/{name} (seed {seed})" values shrinks))
  return cases.length

/-- A missing assignment must be detected and shrunk, using the same
sampling/checking path as real rule tests. This is an expected failure. -/
private def rejectBrokenRule : IO Unit := do
  let s : Stmt StandardExample (context .uint) (context .uint) :=
    .assignLocal .here (.simple (.local (.there .here)))
  let property := Plausible.NamedBinder "x" (∀ x : WordSample,
    Plausible.NamedBinder "y" (∀ y : WordSample,
      checkUpdateWith (state .uint (uintSample x) (uintSample y)) s .nil
        (fun _ => observe .uint) = true))
  match ← Plausible.Testable.checkIO property
      {numInst := 100, randomSeed := some 20261025} with
  | .failure .. => pure ()
  | _ => throw (IO.userError "Plausible failed to detect the deliberately broken assignment rule")

/-- Run all named rule cases; failures include the type, rule, operands and
shrinking report. Supplying the printed seed reproduces the same run. -/
def runChecks (cfg : Plausible.Configuration :=
    { numInst := 200, randomSeed := some 20261025 }) : IO Unit := do
  if cfg.numInst == 0 then throw (IO.userError "--samples must be positive")
  rejectBrokenRule
  let u ← checkGroup .uint rfl uintSample cfg
  let i ← checkGroup .int rfl intSample cfg
  let seed := cfg.randomSeed.map toString |>.getD "random"
  IO.println s!"Plausible: {u + i} rule cases × {cfg.numInst} samples passed (seed {seed})."

-- Imported by the bridge root, so CI runs the same reproducible checks.
#eval runChecks

end Solidity.Bridge.PropertyChecks
