import Solidity.Correctness.Lowering.Checker.Contract
import Solidity.Lowering.V08.IntegerCallable

/-! Actual Source typed-to-resolved spelling and explicit identity-conversion
horizon transport. These are generic expression/control adapters, not copied
raw-spelling `correct` proofs. No Source producer or interface is modified. -/
namespace Solidity.Correctness.Lowering.Checker.SourceAssociation

/-- Exact Source names corresponding to the raw/intrinsic caller context. -/
def names : List (String × Source.STy) := [("i", .bool), ("a", .bool)]

def typingContext (E : Source.Env) : Source.Ctx :=
  { env := E, scope := none, locals := names }

/-- Unbraced source syntax: a block body has a separate horizon obligation. -/
def sourceSyntax : Source.Syn (.stmt Source.SCtx.body) :=
  .whileStmt (.assign .assign (.ident "i") (.ident "a")) .breakStmt

/-- A genuine typing derivation; name resolution and implicit conversion are
checked against the actual Source interfaces, not assumed as proof fields. -/
def conditionTyping (E : Source.Env) :
    Source.Typed (typingContext E) (.assign .assign (.ident "i") (.ident "a")) .bool :=
  .assign (.loc (i := 0) rfl rfl) (.loc (i := 1) rfl rfl) rfl rfl

def typing (E : Source.Env) : Source.StmtD (typingContext E) names sourceSyntax names :=
  .whileLoop (conditionTyping E) rfl .brk

/-- The actual toR result of the checked Source derivation. -/
def resolved (E : Source.Env) :
    Source.RStmt E [] false .body [.bool, .bool] [.bool, .bool] := (typing E).toR

/-- G19's hand-built source has no identity conversion around the RHS. -/
def bare (E : Source.Env) :
    Source.RStmt E [] false .body [.bool, .bool] [.bool, .bool] :=
  .whileLoop (.assign (.local .here) (.local (.there .here))) .brk

/-- Identity conversion is retained by actual Source resolution. -/
theorem resolved_eq (E : Source.Env) : resolved E =
    .whileLoop (.assign (.local .here) (.conv (.local (.there .here)) (.inl rfl))) .brk := by
  rfl

/-- A generic identity conversion consumes one expression horizon while
preserving the full action. No same-horizon equality is asserted. -/
theorem identity_eval {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (e : Source.RExpr E Γ τ)
    (h : Source.Conv E.isBase E.mapFree τ τ) :
    Source.evalE G F (fuel + 1) (.conv e h) = Source.evalE G F fuel e := by
  change (Source.evalE G F fuel e >>= fun value => Source.convRV F fuel τ value) = _
  simp only [Solidity.Lowering.V08.IntegerCallable.conversion_identity, bind_pure]

/-- Generic local-assignment transport. Only local lvalues are covered;
effectful/nonlocal lvalue evaluation is not silently reordered or erased. -/
theorem local_assignment_identity {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (i a : Source.Idx Γ τ)
    (h : Source.Conv E.isBase E.mapFree τ τ) :
    Source.evalE G F (fuel + 3) (.assign (.local i) (.conv (.local a) h)) =
      Source.evalE G F (fuel + 2) (.assign (.local i) (.local a)) := by
  conv => lhs; rw [Source.evalE]
  rw [identity_eval]
  rfl

/-- A generic immediate-break control adapter transports a proved condition
horizon equation. The equation is derived by the expression adapter above,
not supplied as semantic evidence in a certificate. Other loop bodies are
outside this lemma. No general loop termination theorem follows. -/
theorem immediate_break_transport {E : Source.Env} {Γ : Source.RCtx}
    {returns : List Source.STy} {modifier l u : Bool}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (c d : Source.RExpr E Γ .bool)
    (condition : Source.evalE G F (fuel + 3) d = Source.evalE G F (fuel + 2) c)
    (ls : Source.Locals E.layout Γ) :
    Source.execS G F (fuel + 4) nps ph (R := returns) (M := modifier)
      (.whileLoop (l := l) (u := u) d .brk) ls =
    Source.execS G F (fuel + 3) nps ph (R := returns) (M := modifier)
      (.whileLoop (l := l) (u := u) c .brk) ls := by
  conv => lhs; rw [Source.execS]
  conv => rhs; rw [Source.execS]
  rw [condition]
  have breakStep (n : Nat) (xs : Source.Locals E.layout Γ) :
      Source.execS G F (n + 1) nps ph
        (Source.RStmt.brk : Source.RStmt E returns modifier ⟨true, u⟩ Γ Γ) xs =
        pure (Source.Out.brk xs) := by rfl
  simp only [breakStep, pure_bind]

/-- The actual resolved leaf reaches G19 at the explicitly derived horizons:
converted Source at fuel+4, hand-built G19 Source at fuel+3. -/
theorem resolved_run_eq_bare {E : Source.Env} (G : Source.Glob E) (F : Source.Fr)
    (fuel nps : Nat) (ph : Option (Source.Ph E))
    (ls : Source.Locals E.layout [.bool, .bool]) :
    Source.execS G F (fuel + 4) nps ph (resolved E) ls =
      Source.execS G F (fuel + 3) nps ph (bare E) ls := by
  rw [resolved_eq]
  exact immediate_break_transport G F fuel nps ph _ _
    (local_assignment_identity G F fuel .here (.there .here) (.inl rfl)) ls

/-- Negative horizon control: erasing the conversion at horizon three would
lose a real timeout. State remains unchanged before the assignment writes. -/
theorem resolved_three_timeout {E : Source.Env} (G : Source.Glob E) (F : Source.Fr)
    (nps : Nat) (ph : Option (Source.Ph E)) (ls : Source.Locals E.layout [.bool, .bool])
    (st : Source.St E) :
    (Source.execS G F 3 nps ph (resolved E) ls).run (.nil, st) =
      (.error .timeout, (.nil, st)) := by
  rw [resolved_eq]
  rfl

#print axioms resolved_eq
#print axioms identity_eval
#print axioms local_assignment_identity
#print axioms immediate_break_transport
#print axioms resolved_run_eq_bare
#print axioms resolved_three_timeout

end Solidity.Correctness.Lowering.Checker.SourceAssociation
