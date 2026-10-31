import Solidity.Backend.InternalFlow.StorageCalls

/-! Owned plain-storage direct-call consumer. Public certificate constructors
perform all simulation/composition proofs. The traversal consumes the exact
finite embedded call height, never a user-chosen recursion admission budget.
Global Compiler.compile and existing selectors remain unchanged. Plain storage paths only; fragile/unset storage returns and recursive calls refuse. -/
namespace Solidity.Backend.InternalFlow.StoragePrograms
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
    | none => match StorageFrames.statement b F s with
      | some out => some out
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
      (fun R name body => do
        let out ← bodyCompiler F (StorageCalls.expand args R name body)
        if plain : out.frag.get .here = .ok then
          pure (StorageCalls.storageReturn f args R name body out plain)
        else none) body
  | _ => none

private def layers (b : Nat) : Nat → {Γ Δ : Ctx} →
    (F : Frag Γ) → (P : Prog C Γ Δ) → Option (Calls.Program b F P)
  | 0, _, _, F, P => programWith b (fun _ _ => none) F P
  | n + 1, _, _, F, P => programWith b (directCall b (layers b n)) F P

/-- Checked plain-storage and tuple-aware finite program entrypoint, with depth derived from syntax.
Returned certificates carry exact reached costs and expanded frame needs, and
require the public representation/capacity/allocator premises at execution.
This is not public compiler admission or unbounded recursive compilation. -/
def compile (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) :
    Option (Calls.Program b F P) :=
  match Calls.compile b F P with
  | some out => some out
  | none => layers b (TuplePrograms.height P) F P

end Solidity.Backend.InternalFlow.StoragePrograms
