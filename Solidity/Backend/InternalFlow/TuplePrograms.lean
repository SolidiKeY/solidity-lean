import Solidity.Backend.InternalFlow.TupleCalls

/-! Owned compositional direct-call consumer. Public certificate constructors
perform all simulation/composition proofs. The traversal consumes the exact
finite embedded call height, never a user-chosen recursion admission budget.
Global Compiler.compile and all unsupported intrinsic cases remain unchanged. -/
namespace Solidity.Backend.InternalFlow.TuplePrograms
open Evm Evm.Memory
variable {C : Contract}

mutual
private def statementWith (b : Nat) (call : Calls.Expander C b)
    {Γ Δ : Ctx} (F : Frag Γ) : (s : Stmt C Γ Δ) → Option (Calls.Statement b F s)
  | .block body => do
    let out ← programWith b call F body
    pure (Calls.block out)
  | .ite c thn els => do
    let cond ← Memory.compileVal b F c
    let left ← programWith b call F thn
    let right ← programWith b call F els
    pure (Calls.branch c cond left right)
  | s => match Memory.compileStmt b F s with
    | some out => some (Calls.plainStmt out)
    | none => call F s

private def programWith (b : Nat) (call : Calls.Expander C b)
    {Γ Δ : Ctx} (F : Frag Γ) : (P : Prog C Γ Δ) → Option (Calls.Program b F P)
  | .nil => some (Calls.nil b F)
  | .cons s P => do
    let head ← statementWith b call F s
    let tail ← programWith b call head.frag P
    pure (Calls.cons head tail)
end

private def directCall (b : Nat)
    (bodyCompiler : {Γ Δ : Ctx} → (F : Frag Γ) → (P : Prog C Γ Δ) →
      Option (Calls.Program b F P)) {Γ Δ : Ctx} (F : Frag Γ)
    (s : Stmt C Γ Δ) : Option (Calls.Statement b F s) :=
  match s with
  | @Stmt.call _ _ _ ps _ Γf f args ret body =>
    CallRet.casesOn (motive := fun rs _ ret => (body : Prog C (rs ++ ps) Γf) →
      Option (Calls.Statement b F (.call f args ret body))) ret
      (fun body => do
        let out ← bodyCompiler F (Calls.expandNone args body)
        pure (Calls.equivalent out (Calls.expandNone_run f args body)))
      (fun p r res body => do
        let out ← bodyCompiler F (Calls.expandVal args p r res body)
        pure (Calls.equivalent out (Calls.expandVal_run f args p r res body)))
      (fun bs body => do
        let out ← bodyCompiler F (TupleCalls.expand args bs body)
        pure (TupleCalls.tupleReturn f args bs body out))
      (fun R r hd hm body => do
        let out ← bodyCompiler F (Calls.expandMem args R r hd hm body)
        pure (Calls.memoryReturn f args R r hd hm body out))
      (fun _ _ _ => none) body
  | _ => none

private def layers (b : Nat) : Nat → {Γ Δ : Ctx} →
    (F : Frag Γ) → (P : Prog C Γ Δ) → Option (Calls.Program b F P)
  | 0, _, _, F, P => Calls.compile b F P
  | n + 1, _, _, F, P => programWith b (directCall b (layers b n)) F P

mutual
/-- Finite embedded syntax only: callRec is not a direct-call body. -/
def statementHeight {Γ Δ : Ctx} : Stmt C Γ Δ → Nat
  | .call _ _ _ body => height body + 1
  | .block body => height body
  | .ite _ thn els => max (height thn) (height els)
  | _ => 0

def height {Γ Δ : Ctx} : Prog C Γ Δ → Nat
  | .nil => 0
  | .cons s P => max (statementHeight s) (height P)
end

/-- Checked tuple-aware program entrypoint, with depth derived from syntax.
Returned certificates carry exact reached costs and expanded frame needs, and
require the public representation/capacity/allocator premises at execution.
This is not public compiler admission or unbounded recursive compilation. -/
def compile (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) :
    Option (Calls.Program b F P) :=
  match Calls.compile b F P with
  | some out => some out
  | none => layers b (height P) F P

/-- Actual finite selector construction for a tuple call followed by nil.
The premises are compiler results and finite syntax height, not simulation. -/
theorem compile_tuple_nil_success {b : Nat} {Γ ps rs Γf : Ctx}
    (F : Frag Γ) (f : Name) (args : Args C Γ ps) (bs : Binders rs)
    (body : Prog C (rs ++ ps) Γf)
    (out : Calls.Program b F (TupleCalls.expand args bs body))
    (outerRefused : Calls.compile b F (.cons (.call f args (.rets bs) body) .nil) = none)
    (expandedRefused : Calls.compile b F (TupleCalls.expand args bs body) = none)
    (sameHeight : height (TupleCalls.expand args bs body) = height body)
    (compiled : compile b F (TupleCalls.expand args bs body) = some out) :
    compile b F (.cons (.call f args (.rets bs) body) .nil) =
      some (Calls.cons (TupleCalls.tupleReturn f args bs body out)
        (Calls.nil b (TupleCalls.tupleReturn f args bs body out).frag)) := by
  have entered : layers b (height body) F (TupleCalls.expand args bs body) = some out := by
    rw [compile,expandedRefused] at compiled
    simpa only [sameHeight] using compiled
  rw [compile,outerRefused]
  have outerHeight : height (.cons (.call f args (.rets bs) body) .nil) = height body + 1 := by
    change max (height body + 1) 0 = height body + 1
    exact Nat.max_zero _
  rw [outerHeight]
  change Option.bind
    (Option.bind (layers b (height body) F (TupleCalls.expand args bs body))
      (fun selected => some (TupleCalls.tupleReturn f args bs body selected)))
    (fun head => some (Calls.cons head (Calls.nil b head.frag))) = _
  rw [entered]
  rfl


/-- The actual structural traversal used at the enclosing program's finite
syntax height. This exposes construction equations, not a new evaluator or
user-selected call-depth admission bound. -/
def construction (b : Nat) {Ω Ω' : Ctx} (enclosing : Prog C Ω Ω')
    {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) : Option (Calls.Program b F P) :=
  programWith b (directCall b (layers b (height enclosing - 1))) F P

def constructionStmt (b : Nat) {Ω Ω' : Ctx} (enclosing : Prog C Ω Ω')
    {Γ Δ : Ctx} (F : Frag Γ) (s : Stmt C Γ Δ) : Option (Calls.Statement b F s) :=
  statementWith b (directCall b (layers b (height enclosing - 1))) F s

theorem construction_nil {b : Nat} {Ω Ω' Γ : Ctx} (enclosing : Prog C Ω Ω') (F : Frag Γ) :
    construction b enclosing F .nil = some (Calls.nil b F) := rfl

theorem construction_cons {b : Nat} {Ω Ω' Γ Δ Ξ : Ctx}
    (enclosing : Prog C Ω Ω') (F : Frag Γ) (s : Stmt C Γ Δ) (P : Prog C Δ Ξ)
    (head : Calls.Statement b F s) (tail : Calls.Program b head.frag P)
    (hs : constructionStmt b enclosing F s = some head)
    (hp : construction b enclosing head.frag P = some tail) :
    construction b enclosing F (.cons s P) = some (Calls.cons head tail) := by
  change Option.bind (constructionStmt b enclosing F s) (fun selected =>
    Option.bind (construction b enclosing selected.frag P)
      (fun rest => some (Calls.cons selected rest))) = _
  rw [hs]
  change Option.bind (construction b enclosing head.frag P) (fun rest => some (Calls.cons head rest)) = _
  rw [hp]
  rfl

theorem construction_block {b : Nat} {Ω Ω' Γ Δ : Ctx}
    (enclosing : Prog C Ω Ω') (F : Frag Γ) (P : Prog C Γ Δ)
    (body : Calls.Program b F P) (hp : construction b enclosing F P = some body) :
    constructionStmt b enclosing F (.block P) = some (Calls.block body) := by
  change Option.bind (construction b enclosing F P) (fun q => some (Calls.block q)) = _
  rw [hp]
  rfl

theorem construction_branch {b : Nat} {Ω Ω' Γ Δ Ξ : Ctx}
    (enclosing : Prog C Ω Ω') (F : Frag Γ) (c : Val C Γ .bool)
    (thn : Prog C Γ Δ) (els : Prog C Γ Ξ) (cond : CompiledVal b F c)
    (left : Calls.Program b F thn) (right : Calls.Program b F els)
    (hc : Memory.compileVal b F c = some cond)
    (ht : construction b enclosing F thn = some left)
    (he : construction b enclosing F els = some right) :
    constructionStmt b enclosing F (.ite c thn els) = some (Calls.branch c cond left right) := by
  change Option.bind (Memory.compileVal b F c) (fun v =>
    Option.bind (construction b enclosing F thn) (fun l =>
      Option.bind (construction b enclosing F els) (fun r => some (Calls.branch c v l r)))) = _
  rw [hc,ht,he]
  rfl

/-- Identify the actual fallback selector at positive syntax height. The
ordinary compiler refusal is retained as a real premise, not changed admission. -/
theorem compile_construction {b : Nat} {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ)
    (positive : 0 < height P) (refused : Calls.compile b F P = none) :
    compile b F P = construction b P F P := by
  rw [compile,refused]
  cases h : height P with
  | zero => omega
  | succ n =>
    simp only [construction,h,Nat.add_sub_cancel,layers]

/-- Tuple argument/result expansion at the real enclosing height. Every
premise names actual compiler output or syntax, not target simulation. -/
theorem construction_tuple {b : Nat} {Ω Ω' Γ ps rs Γf : Ctx}
    (enclosing : Prog C Ω Ω') (F : Frag Γ) (f : Name)
    (args : Args C Γ ps) (bs : Binders rs) (body : Prog C (rs ++ ps) Γf)
    (out : Calls.Program b F (TupleCalls.expand args bs body))
    (enclosingHeight : height enclosing = height body + 1)
    (expandedHeight : height (TupleCalls.expand args bs body) = height body)
    (refused : Calls.compile b F (TupleCalls.expand args bs body) = none)
    (selected : compile b F (TupleCalls.expand args bs body) = some out) :
    constructionStmt b enclosing F (.call f args (.rets bs) body) =
      some (TupleCalls.tupleReturn f args bs body out) := by
  have entered : layers b (height body) F (TupleCalls.expand args bs body) = some out := by
    rw [compile,refused] at selected
    simpa only [expandedHeight] using selected
  change Option.bind (layers b (height enclosing - 1) F (TupleCalls.expand args bs body))
    (fun q => some (TupleCalls.tupleReturn f args bs body q)) = _
  rw [enclosingHeight,Nat.add_sub_cancel,entered]
  rfl

/-- Eliminate a known bare failure through the public program certificate.
Keeping the certificate generic avoids unfolding a large concrete get-proof
merely to select its soundness field. No successful failed state is recovered. -/
theorem program_revert {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ}
    {P : Prog C Γ Δ} (p : Calls.Program b F P) {σ : State C Γ}
    {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m) (room : b + p.need ≤ frame)
    (capacity : AllocationInput b frame (p.cost σ) σ base m)
    (failed : P.run σ = .error .revert) : Evm.run p.code m = .revert := by
  rcases p.sound repr room capacity with
      ⟨o,m',base',hs,ht,hrepr,hstack,hext,halloc⟩ | ⟨hs,ht⟩
  · rw [failed] at hs
    contradiction
  · exact ht

/-- info: 'Solidity.Backend.InternalFlow.TuplePrograms.compile_tuple_nil_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms compile_tuple_nil_success

/-- info: 'Solidity.Backend.InternalFlow.TuplePrograms.construction_nil' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms construction_nil

/-- info: 'Solidity.Backend.InternalFlow.TuplePrograms.construction_cons' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms construction_cons

/-- info: 'Solidity.Backend.InternalFlow.TuplePrograms.construction_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms construction_block

/-- info: 'Solidity.Backend.InternalFlow.TuplePrograms.construction_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms construction_branch

/-- info: 'Solidity.Backend.InternalFlow.TuplePrograms.compile_construction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms compile_construction

/-- info: 'Solidity.Backend.InternalFlow.TuplePrograms.construction_tuple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms construction_tuple

end Solidity.Backend.InternalFlow.TuplePrograms
