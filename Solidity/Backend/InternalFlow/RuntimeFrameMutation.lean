import Solidity.Backend.InternalFlow.RuntimeFrameComposition

/-! Derived scratch transport for dynamic writes through actual caller aliases.
The old selector is unchanged. This extension handles real value/index failures
and bounds reversion; no failed State, Heap.Keeps or liveness oracle is used. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.Mutation
open Evm Evm.Memory
variable {C : Contract}

/-- The existing typed write certificate is strengthened for ALL represented
inputs and successful executions. Liveness is derived from the actual bounds
check, rather than required as an extra source-profile premise. -/
def write {b : Nat} {Γ : Ctx} (F : Frag Γ) {p : PrimTy}
    (destination : Idx Γ (.mem (.array (.prim p))))
    (index : Val C Γ .uint) (value : Val C Γ p)
    (indexCode : CompiledVal b F index) (valueCode : CompiledVal b F value) :
    Composition.Statement b F (.assignMem (.index .dyn (.var destination rfl) index) (.val value)) where
  checked := Calls.plainStmt ⟨F,_,.write F destination rfl index value
    indexCode.code valueCode.code indexCode.cert valueCode.cert⟩
  safe := by
    intro L frame lo σ base m target repr room boundary capacity actual
    obtain ⟨ref,binding,pointer⟩ := repr.pointers destination
    rcases valueCode.cert.correct repr with ⟨v,w,evaluated,represented,valueRun⟩ | ⟨evaluated,valueRun⟩
    · have pointerRun : run [.mload (cellOf b destination)] (m.push w) =
          .ok ((m.push w).push (.val (base ref.id))) 0 := by
        change Out.ok ((m.push w).push (m.mem (cellOf b destination))) 0 = _
        rw [pointer]
      change run (writeLocalValueCode b destination indexCode.code valueCode.code) m = _ at actual
      rw [writeLocalValueCode,List.append_assoc,List.append_assoc,
        run_append_ok valueRun,run_append_ok pointerRun] at actual
      rcases indexCode.cert.correct ((repr.push w).push (.val (base ref.id))) with
        ⟨iv,iw,indexValue,indexRepr,indexRun⟩ | ⟨indexValue,indexRun⟩
      · rw [run_append_ok indexRun] at actual
        obtain ⟨a,ha,numeric,rfl⟩ := indexRepr.uint_inv
        rw [writeArrayStackCode,arrayStack_append_eq (m.push w) (base ref.id) ⟨a,ha⟩ _
          (σ.heap.len_dyn_lt ref) (repr.heap.arrays ref).length,← writeArrayCode] at actual
        by_cases live : a < σ.heap.len ref .dyn
        · obtain ⟨source,code,represented,words⟩ := Footprint.array_write repr ref ⟨a,ha⟩ live v w represented lo
          have same := (Evm.Out.ok.inj (actual.symm.trans code)).1
          exact same.symm ▸ words
        · have guard := arrayAddr_run (m.push w) (base ref.id) ⟨a,ha⟩ _
            (σ.heap.len_dyn_lt ref) (repr.heap.arrays ref).length
          rw [if_neg live] at guard
          have failure : run (writeArrayCode (base ref.id)) ((m.push w).push (.val ⟨a,ha⟩)) = .revert :=
            run_append_revert guard
          rw [failure] at actual
          contradiction
      · rw [run_append_revert indexRun] at actual
        contradiction
    · change run (writeLocalValueCode b destination indexCode.code valueCode.code) m = _ at actual
      rw [writeLocalValueCode,List.append_assoc,List.append_assoc,run_append_revert valueRun] at actual
      contradiction

mutual
/-- Extend only the footprint capability; existing public admission and the
previous selector's refused cases/controls are preserved. -/
def compileStatement (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) :
    (s : Stmt C Γ Δ) → Option (Composition.Statement b F s)
  | .block body => do
    let selected ← compileProgram b F body
    pure (Composition.block selected)
  | .ite condition thn els => do
    let cond ← Memory.compileVal b F condition
    let left ← compileProgram b F thn
    let right ← compileProgram b F els
    pure (Composition.branch condition cond left right)
  | .assignMem (.index .dyn (.var destination _) index) (.val value) => do
    let indexCode ← Memory.compileVal b F index
    let valueCode ← Memory.compileVal b F value
    pure (write F destination index value indexCode valueCode)
  | statement => Composition.compileStatement b F statement

def compileProgram (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) :
    (P : Prog C Γ Δ) → Option (Composition.Program b F P)
  | .nil => some (Composition.nil b F)
  | .cons head tail => do
    let first ← compileStatement b F head
    let rest ← compileProgram b first.checked.frag tail
    pure (Composition.cons first rest)
end

/-- One call level: the callee body is compiled by `compileProgram`, which
refuses an inner `.call`; nested calls go through `RuntimeFrameNested`. -/
def compileCall (b : Nat) {Γ ps rs Δ Γf : Ctx} (F : Frag Γ) (name : Name)
    (args : Args C Γ ps) (ret : CallRet Γ rs Δ) (body : Prog C (rs ++ ps) Γf) :
    Option (Composition.Statement b F (.call name args ret body)) :=
  CallRet.casesOn (motive := fun rs _ ret => (body : Prog C (rs ++ ps) Γf) →
      Option (Composition.Statement b F (.call name args ret body))) ret
    (fun body => do
      let selected ← compileProgram b F (Calls.expandNone args body)
      pure (Composition.equivalent selected (Calls.expandNone_run name args body)))
    (fun p result destination body => do
      let selected ← compileProgram b F (Calls.expandVal args p result destination body)
      pure (Composition.equivalent selected (Calls.expandVal_run name args p result destination body)))
    (fun _ _ => none)
    (fun R result hd hm body => do
      let selected ← compileProgram b F (Calls.expandMem args R result hd hm body)
      if bound : (.mem R :: (ps ++ Γ)).length ≤ selected.checked.need then
        pure (Composition.memoryReturn name args R result hd hm body selected bound)
      else none)
    (fun _ _ _ => none) body
/-- Every elaborated recursive unrolling ends in `Prog.recBase` (`assumeFalse`),
which no selector compiles, so this returns `none` for it today.
Preserve actual callRec semantics through the existing exact normalizer;
this selector still handles only finite supplied bodies, not recursive source
execution without an unrolling premise. -/
def compileRecursive (b : Nat) {Γ ps rs Δ : Ctx} (F : Frag Γ) (name : Name) (depth : Nat)
    (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
    (body : Unit → Prog C (rs ++ ps) (rs ++ ps)) :
    Option (Composition.Statement b F (.callRec name depth args ret body)) :=
  (compileCall b F name args ret (RuntimeFrame.program (body ()))).map
    (Composition.normalizeStatement (.callRec name depth args ret body))
end Solidity.Backend.InternalFlow.RuntimeFrame.Mutation
