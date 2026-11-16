import Solidity.Backend.Passes.SourceCallBoundary

/-! G22.01: a typed factorisation of the actual resolved external-call
interpreter. Capture runs target, value and arguments once, in source order;
its final state is the invocation checkpoint. This is not yet a compiler or
intrinsic-world simulation. Arbitrary `Captured` values are not provenance:
`CapturedAt` requires the actual capture execution. -/
namespace Solidity.Backend.Passes.SourceTypedCall
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes)
open EM
variable {E : Env} {Γ : RCtx} {dn : DeclName} {ps rs : List STy}

structure Captured (E : Env) (ps : List STy) where
  receiver : Address
  value : Word
  arguments : Vals E.layout ps
  input : Bytes

def capture (G : Glob E) (F : Fr) (n : Nat)
    (target : RExpr E Γ (.contract dn)) (d : Decl)
    (value : RExpr E Γ (.int IntTy.u256)) (args : RConvArgs E Γ ps) :
    EM E Γ (Captured E ps) := do
  let a ← match ← getV (← evalE G F n target) with
    | .contract x => pure x
  let v ← match ← getV (← evalE G F n value) with
    | .int x _ => pure x
  let vs ← evalConvArgs G F n args
  let sig := match d.fnSig E with | some (ts, _) => ts | none => []
  let input := G.selector (sigOf E.layout d.name sig) ++ (← encodeVals F n false vs.toR)
  if (← instanceAt G a).isNone && !G.hasCode (← st).events a then halt (.revert [])
  return ⟨a, ⟨v.toNat % 2 ^ 256, Nat.mod_lt _ (by decide)⟩, vs, input⟩

def resume (G : Glob E) (F : Fr) (n : Nat) (d : Decl)
    (rs : List STy) (captured : Captured E ps) : EM E Γ (RVal E.layout (STy.ret rs)) := do
  let (out, _) ← sub (L0 E) (callAddr G F n captured.receiver captured.value captured.input
    (d.fnMut == some .view || d.fnMut == some .pure))
  extReturn rs out

/-- Declaration identity/signature and the execution position are retained
as parameters; the post-capture state is produced by source execution. -/
def CapturedAt (G : Glob E) (F : Fr) (n : Nat)
    (target : RExpr E Γ (.contract dn)) (d : Decl)
    (_signature : d.fnSig E = some (ps, rs))
    (value : RExpr E Γ (.int IntTy.u256)) (args : RConvArgs E Γ ps)
    (before after : Locals E.layout Γ × St E) (captured : Captured E ps) : Prop :=
  (capture G F n target d value args).run before = (.ok captured, after)

/-- Exact factorisation, including all failures and post-capture effects.
The return decoder remains after the real call, with declared return types. -/
theorem eval_external (G : Glob E) (F : Fr) (n : Nat)
    (target : RExpr E Γ (.contract dn)) (d : Decl)
    (signature : d.fnSig E = some (ps, rs))
    (value : RExpr E Γ (.int IntTy.u256)) (args : RConvArgs E Γ ps) :
    evalE G F (n + 1) (.extCall target d signature value args) =
      (capture G F n target d value args >>= resume G F n d rs) := by
  simp only [evalE, withLibraryCalldata, capture, bind_assoc, pure_bind]
  congr 1
  funext raw
  congr 1
  funext a
  cases a with
  | contract a =>
    try simp only [bind_assoc]
    congr 1
    funext raw
    congr 1
    funext v
    cases v with
    | int v hv =>
      try simp only [bind_assoc]
      congr 1
      funext vs
      try simp only [bind_assoc]
      congr 1
      funext encoded
      try simp only [bind_assoc]
      congr 1
      funext inst
      try simp only [bind_assoc]
      congr 1
      funext state
      split <;> rfl
    | memRef h _ => cases h
    | storRef h _ => cases h
    | cdRef h _ => cases h
  | memRef h _ => cases h
  | storRef h _ => cases h
  | cdRef h _ => cases h

private theorem run_bind {α β : Type} (m : EM E Γ α) (k : α → EM E Γ β)
    (x : Locals E.layout Γ × St E) :
    (m >>= k).run x = match m.run x with
      | (.ok a, y) => (k a).run y
      | (.error e, y) => (.error e, y) := by
  rw [ExceptT.run_bind]
  show StateT.bind (ExceptT.run m) _ x = _
  simp only [StateT.bind]
  rcases m.run x with ⟨r, y⟩
  cases r <;> rfl

/-- A genuine capture run supplies the exact live state to the real callee. -/
theorem external_captured (G : Glob E) (F : Fr) (n : Nat)
    (target : RExpr E Γ (.contract dn)) (d : Decl)
    (signature : d.fnSig E = some (ps, rs))
    (value : RExpr E Γ (.int IntTy.u256)) (args : RConvArgs E Γ ps)
    (before after : Locals E.layout Γ × St E) (captured : Captured E ps)
    (execution : CapturedAt G F n target d signature value args before after captured) :
    (evalE G F (n + 1) (.extCall target d signature value args)).run before =
      (resume G F n d rs captured).run after := by
  rw [eval_external, run_bind, execution]

/-- Capture failure preserves its actual failure state and never invokes a callee. -/
theorem external_capture_failure (G : Glob E) (F : Fr) (n : Nat)
    (target : RExpr E Γ (.contract dn)) (d : Decl)
    (signature : d.fnSig E = some (ps, rs))
    (value : RExpr E Γ (.int IntTy.u256)) (args : RConvArgs E Γ ps)
    (before after : Locals E.layout Γ × St E) (h : Halt)
    (execution : (capture G F n target d value args).run before = (.error h, after)) :
    (evalE G F (n + 1) (.extCall target d signature value args)).run before =
      (.error h, after) := by
  rw [eval_external, run_bind, execution]

end Solidity.Backend.Passes.SourceTypedCall
