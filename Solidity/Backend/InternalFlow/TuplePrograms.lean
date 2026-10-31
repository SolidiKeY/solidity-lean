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

end Solidity.Backend.InternalFlow.TuplePrograms
