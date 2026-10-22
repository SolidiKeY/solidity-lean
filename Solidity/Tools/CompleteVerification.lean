import Solidity.Calculus.DeclarationStaticReduction
import Solidity.Tools.Counterexample

/-!
# Complete decisions after exact source recognition

The compiler first removes independently certified declaration facts. Its
successful result preserves the original formula in every starting state.
Compiled arithmetic exploration chooses a verdict; the kernel then checks
the positive computation or only the extracted finite false assignment.
Unsupported syntax and timeouts leave the ordinary verifier available.
-/

namespace Solidity.Tools

open Lean Elab Term Meta Decide Linear

variable {C : Contract}

/-- The original parameter binders, in the reducer's atom order. -/
def inputNames : {Γ : Ctx} → Nat → Fml C Γ → List (Var × Parameter)
  | _, k, .all x p φ | _, k, .bind _ x (.val p) φ =>
    (x, ⟨p, k⟩) :: inputNames (k + 1) φ
  | _, _, _ => []

/-- Project an exact original-state countermodel into the existing report
format. Names come from the original binders, not from declaration order. -/
def exactCandidate {φ : Fml C []} (r : InputReduction φ) (xs : List Nat)
    (h : r.arithmetic.guarded.check (fun k => xs[k]?.getD 0) = false) : Cand C :=
  let cm := r.countermodelOfCodes xs h
  { st := cm.state.storage
    args := (inputNames 0 φ).map fun (x, p) => (toString x, Semantics.CallValue.ofTyped (p.read cm.atoms))
    tx := cm.state.tx
    net := cm.state.net
    bal := cm.state.selfBalance }

/-- A report of the actual exact model, independent of the legacy
interpreter-based renderer. Atom positions identify universal instances. -/
def exactModelLines {φ : Fml C []} (r : InputReduction φ) (xs : List Nat)
    (h : r.arithmetic.guarded.check (fun k => xs[k]?.getD 0) = false) : List String :=
  let cm := r.countermodelOfCodes xs h
  (r.parameters.map fun p => s!"parameter #{p.index} = {CallValue.fmt (.ofTyped (p.read cm.atoms))}") ++
    [", ".intercalate (fmtTx cm.state ++ [s!"address(this) = {cm.state.tx.selfAddress.val}"]),
      "before: " ++ fmtStorageLine C cm.state.storage]

def dependentCandidate {φ : Fml C []} (r : DependentReduction φ) (xs : List Nat)
    (h : r.checkCodes xs = false) : Cand C :=
  let cm := r.countermodelOfCodes xs h
  { st := cm.state.storage
    args := (inputNames 0 φ).map fun (x, p) => (toString x, Semantics.CallValue.ofTyped (p.read cm.atoms))
    tx := cm.state.tx
    net := cm.state.net
    bal := cm.state.selfBalance }

def dependentModelLines {φ : Fml C []} (r : DependentReduction φ) (xs : List Nat)
    (h : r.checkCodes xs = false) : List String :=
  let cm := r.countermodelOfCodes xs h
  (r.sentence.parameters.map fun p => s!"parameter #{p.index} = {CallValue.fmt (.ofTyped (p.read cm.atoms))}") ++
    [", ".intercalate (fmtTx cm.state ++ [s!"address(this) = {cm.state.tx.selfAddress.val}"]),
      "before: " ++ fmtStorageLine C cm.state.storage]

/-- Closed proof terms are retained for both verdicts. A refutation also
retains the reduction and finite assignment for witness display. -/
inductive ExactVerdict where
  | proved (proof : Expr)
  | refuted (proof reduction : Expr) (codes : List Nat)
  | refutedDependent (proof reduction : Expr) (codes : List Nat)

/-- Explore once and export only finite data. The caller independently
checks the verdict after quoting this untrusted computation back to Lean. -/
def arithmeticData (F : AFml) : Option (List Nat) :=
  match F.verify with
  | .inl _ => none
  | .inr cm => some (List.ofFn (fun i : Fin F.width => cm.val i))

/-- A bounded probe checks nodes as they are discovered, before completing
the graph. Its output is untrusted finite data, checked by each caller. -/
private def earlyCounterdata (root : AFml) (width : Nat) : Nat → List (AFml.Node root) →
    List (AFml.Node root) → Option (List Nat)
  | 0, _, _ => none
  | fuel + 1, seen, frontier =>
    match frontier.find? (fun node => !node.formula.atZero) with
    | some node => some (List.ofFn (fun i : Fin width => node.embed (fun _ => 0) i))
    | none =>
      if frontier.isEmpty then none else
      let new := AFml.Node.addNew (seen.map AFml.Node.formula) [] (frontier.flatMap AFml.Node.children)
      earlyCounterdata root width fuel (new ++ seen) new

/-- Early negative discovery keeps the complete decision as fallback;
probe exhaustion is never interpreted as validity or absence of a model. -/
def arithmeticDataEarly (F : AFml) : Option (List Nat) :=
  let root := F.simp
  (earlyCounterdata root F.width (min 512 (root.count + 1))
    [AFml.Node.initial root] [AFml.Node.initial root]).orElse (fun _ => arithmeticData F)

/-- Independently check a closed generated certificate before a tool uses
its verdict or reconstructed witness. -/
def checkCertificate (type proof : Expr) : MetaM Expr := do
  let proof ← instantiateMVars proof
  if proof.hasSorry || proof.hasMVar || proof.hasFVar then
    throwError "exact verification: certificate is not a closed proof"
  let decl := Declaration.thmDecl {
    name := `_exact_verification_certificate, levelParams := [], type, value := proof }
  match Kernel.Environment.addDecl (← getEnv).toKernelEnv (← getOptions) decl with
  | .ok _ => return proof
  | .error _ => throwError "exact verification: kernel rejected certificate"

/-- Decide a successfully recognized formula, and independently check the
chosen verdict. Each caller can catch a resource failure and keep it open. -/
private def verifyReduction (φ r : Expr) (arithmeticName validName checkName refuteName : Lean.Name)
    (dependent : Bool) : MetaM ExactVerdict := withCurrHeartbeats do
  let arithmetic ← mkAppM arithmeticName #[r]
  let guarded ← mkAppM ``TypedFormula.guarded #[arithmetic]
  let data ← mkAppM (if dependent then ``arithmeticDataEarly else ``arithmeticData) #[guarded]
  let result ← unsafe evalExpr (Option (List Nat)) (← inferType data) data
  match result with
  | none =>
    let decision ← mkAppM ``AFml.decide #[guarded]
    let hDecision := mkExpectedPropHint (← mkEqRefl (mkConst ``Bool.true))
      (← mkEq decision (mkConst ``Bool.true))
    let proof ← mkAppM validName #[r, hDecision]
    return .proved (← checkCertificate (← mkAppM ``Solidity.Fml.Valid #[φ]) proof)
  | some xs =>
    let check ← mkAppM checkName #[r, toExpr xs]
    let h := mkExpectedPropHint (← mkEqRefl (mkConst ``Bool.false))
      (← mkEq check (mkConst ``Bool.false))
    let proof ← mkAppM refuteName #[r, toExpr xs, h]
    let checked ← checkCertificate (mkNot (← mkAppM ``Solidity.Fml.Valid #[φ])) proof
    return if dependent then .refutedDependent checked r xs else .refuted checked r xs

/-- Keep the existing static-input route first; dependent reads use the
same kernel gate after automatic occurrence and alias compilation. -/
def exactVerify (φ : Expr) : MetaM ExactVerdict :=
  tryCatchRuntimeEx
    (do
      let r ← DeclarationReduction.compileInput φ
      verifyReduction φ r ``InputReduction.arithmetic ``InputReduction.valid_of_decide
        ``InputReduction.checkCodes ``InputReduction.not_valid_of_codes false)
    (fun _ => do
      let r ← DeclarationReduction.compileDependent φ
      verifyReduction φ r ``DependentReduction.arithmetic ``DependentReduction.valid_of_decide
        ``DependentReduction.checkCodes ``DependentReduction.not_valid_of_codes true)

/-- Display the exact model through the existing witness renderer. Check
the displayed call independently, including its original entry premises. -/
private def detailedExactRefutation (n : Lean.Name) (C : Contract) (f : String)
    (φ candidate : Expr) : MetaM Refutation := do
  let P ← match SpecProblem.of C f with
    | .ok p => pure p
    | .error e => throwError "{e}"
  let c ← unsafe evalExpr (Cand C) (← inferType candidate) candidate
  let lits := P.domLits c
  let certified ← if Fml.eval3Peel (poolDom lits) c.vals (c.tstate C) P.fml = .ff then
      certifyRefl (mkConst n) φ lits c.vals c
    else certifyDeclarations (mkConst n) φ lits c.vals c
  unless certified do throwError "exact verification: displayed witness did not certify"
  let ⟨_, σ, ψ⟩ := Fml.peel c.vals (c.tstate C) P.fml
  let body := match ψ with | .imp _ body => body | _ => ψ
  let dom := poolDom lits
  let failing := (Fml.postFails dom P.posts.length σ body).elim [] (·.2)
  let w : Witness C := ⟨c, Fml.outcome dom σ body, failing⟩
  return {
    witness := w.lines C ++
      (if c.tx.selfAddress.val = 0 then [] else [s!"address(this) = {c.tx.selfAddress.val}"])
    certified := true
    fails := failing.map fun i => postLabel C P.decl (mkConst n) i (P.posts.getD i NRead.tt) }

/-- A checked negative verdict survives failure of the detailed renderer.
The fallback still displays its actual typed initial state and parameters. -/
private def renderRefutation (n : Lean.Name) (C : Contract) (f : String)
    (φ r : Expr) (xs : List Nat) (checkName refuteName reportName candidateName : Lean.Name) : MetaM Refutation := do
  let check ← mkAppM checkName #[r, toExpr xs]
  let h := mkExpectedPropHint (← mkEqRefl (mkConst ``Bool.false))
    (← mkEq check (mkConst ``Bool.false))
  let proof ← mkAppM refuteName #[r, toExpr xs, h]
  let _ ← checkCertificate (mkNot (← mkAppM ``Solidity.Fml.Valid #[φ])) proof
  let report ← mkAppM reportName #[r, toExpr xs, h]
  let candidate ← mkAppM candidateName #[r, toExpr xs, h]
  let minimal ← unsafe evalExpr (List String) (← inferType report) report
  let saved ← saveState
  let result ← tryCatchRuntimeEx (withCurrHeartbeats (detailedExactRefutation n C f φ candidate))
    (fun _ => pure { witness := minimal, certified := true, fails := [] })
  saved.restore
  return result

def exactRefutation (n : Lean.Name) (C : Contract) (f : String)
    (φ r : Expr) (xs : List Nat) : MetaM Refutation :=
  renderRefutation n C f φ r xs ``InputReduction.checkCodes ``InputReduction.not_valid_of_codes
    ``exactModelLines ``exactCandidate

def dependentRefutation (n : Lean.Name) (C : Contract) (f : String)
    (φ r : Expr) (xs : List Nat) : MetaM Refutation :=
  renderRefutation n C f φ r xs ``DependentReduction.checkCodes ``DependentReduction.not_valid_of_codes
    ``dependentModelLines ``dependentCandidate

private def exactTactic (ref : Syntax) (suggest : Bool) : Tactic.TacticM Unit :=
  Tactic.withMainContext do
    let goal ← Tactic.getMainGoal
    let ty ← goal.getType
    unless ty.isAppOfArity ``Solidity.Fml.Valid 2 do
      throwError "sol_exact: expected validity of a closed scoped formula"
    match ← exactVerify ty.appArg! with
    | .proved proof =>
      if suggest then Lean.Meta.Tactic.TryThis.addExactSuggestion ref proof
      goal.assign proof
      Tactic.replaceMainGoal []
    | .refuted _ _ _ | .refutedDependent _ _ _ => throwError "sol_exact: the original formula has a countermodel"

/-- Complete decision on the recognized typed-input fragment. -/
elab stx:"sol_exact" : tactic => exactTactic stx false

/-- Offer the explicit checked proof for replay. -/
elab stx:"sol_exact?" : tactic => exactTactic stx true

end Solidity.Tools
