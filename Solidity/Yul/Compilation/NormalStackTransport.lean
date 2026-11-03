import Solidity.Yul.Compilation.NormalControl
/-! Concrete whole-block execution of compiled normal control when every leaf
is selected by the existing stack-only MachineAdapter. No word selector is
silently widened: arithmetic and loops refuse in this model consumer.
This is the existing Evm.Machine model, not native/charged/Source/G24 adequacy. -/
namespace Solidity.Yul.Compilation.NormalStackTransport
open Solidity.Yul Solidity.Yul.Closed
open Backend Scalar MachineAdapter

def blockCode : Backend.Block → Option (List Evm.Instr)
  | .code p => MachineAdapter.stackCode p
  | .seq a b => (blockCode a).bind (fun x => (blockCode b).map (fun y => x ++ y))
  | .ite c a b => (MachineAdapter.stackCode c).bind (fun x =>
      (blockCode a).bind (fun y => (blockCode b).map (fun z => MachineControl.branchCode x y z)))
  | .loop _ _ => none

/-- Actual emitted blocks and concrete model selection derive all operands,
intermediate states and arm executions; no desired execution is a premise. -/
theorem machine {c n fuel} {stmt : Stmt [] [] c n}
    (compiled : NormalControl.Derivation fuel stmt) (depth : Nat)
    (block : Backend.Block) (code : List Evm.Instr)
    (emitted : compiled.emit depth = some block)
    (translated : blockCode block = some code)
    (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
    (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run code {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} =
      .ok {m with stack := (newer.toList ++ (compiled.update locals).toList).map coreWord ++ caller} 0 := by
  induction compiled generalizing block code locals with
  | scalar leaf =>
    change (leaf.lowered.code depth).map Backend.Block.code = some block at emitted
    cases hp : leaf.lowered.code depth with
    | none => simp only [hp,Option.map_none,reduceCtorEq] at emitted
    | some p =>
      simp only [hp,Option.map_some,Option.some.injEq] at emitted
      subst block
      exact MachineAdapter.loweredStmt_machine leaf.lowered depth p code hp translated locals newer m caller
  | seq first second ihFirst ihSecond =>
    change (do
      let a ← first.emit depth
      let b ← second.emit depth
      pure (Backend.Block.seq a b)) = some block at emitted
    cases ha : first.emit depth with
    | none => simp only [ha] at emitted; cases emitted
    | some a =>
      cases hb : second.emit depth with
      | none => simp only [ha,hb] at emitted; cases emitted
      | some b =>
        simp only [ha,hb] at emitted
        have same : Backend.Block.seq a b = block := Option.some.inj emitted
        subst block
        change ((blockCode a).bind (fun qa =>
          (blockCode b).map (fun qb => qa ++ qb))) = some code at translated
        cases sa : blockCode a with
        | none => simp only [sa,Option.bind_none,reduceCtorEq] at translated
        | some qa =>
          cases sb : blockCode b with
          | none => simp only [sa,sb,Option.bind_some,Option.map_none,reduceCtorEq] at translated
          | some qb =>
            simp only [sa,sb,Option.bind_some,Option.map_some,Option.some.injEq] at translated
            subst code
            rw [Evm.run_append_ok (ihFirst a qa ha sa locals)]
            exact ihSecond b qb hb sb (first.update locals)
  | branch condition arm ih =>
    change (do
      let cc ← condition.lowered.code depth
      let bb ← arm.emit depth
      pure (Backend.Block.ite cc bb (.code []))) = some block at emitted
    cases hc : condition.lowered.code depth with
    | none => simp only [hc] at emitted; cases emitted
    | some cc =>
      cases hb : arm.emit depth with
      | none => simp only [hc,hb] at emitted; cases emitted
      | some bb =>
        simp only [hc,hb] at emitted
        have same : Backend.Block.ite cc bb (.code []) = block := Option.some.inj emitted
        subst block
        change ((MachineAdapter.stackCode cc).bind (fun qc =>
          (blockCode bb).bind (fun qb =>
            (MachineAdapter.stackCode []).map (fun qn => MachineControl.branchCode qc qb qn)))) = some code at translated
        have empty : MachineAdapter.stackCode [] = some [] := rfl
        rw [empty] at translated
        cases sc : MachineAdapter.stackCode cc with
        | none => simp only [sc,Option.bind_none,reduceCtorEq] at translated
        | some qc =>
          cases sb : blockCode bb with
          | none => simp only [sc,sb,Option.bind_some,Option.bind_none,reduceCtorEq] at translated
          | some qb =>
            simp only [sc,sb,Option.bind_some,Option.map_some,Option.some.injEq] at translated
            subst code
            have law := MachineControl.branchCode_run
              ⟨(condition.value locals).toNat,(condition.value locals).isLt⟩ qc qb []
              {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller}
              {m with stack := (newer.toList ++ (arm.update locals).toList).map coreWord ++ caller}
              {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller}
              (MachineAdapter.loweredExpr_machine condition.lowered depth cc qc hc sc locals newer m caller)
              (ih bb qb hb sb locals) (by rfl)
            have truth : (condition.value locals).toNat = 0 ↔ condition.value locals = 0 :=
              ⟨fun h => BitVec.eq_of_toNat_eq h,fun h => congrArg BitVec.toNat h⟩
            change _ = Evm.Out.ok {m with stack := (newer.toList ++
              (if condition.value locals = 0 then locals else arm.update locals).toList).map coreWord ++ caller} 0
            by_cases zero : condition.value locals = 0
            · simpa only [truth,zero,ite_true] using law
            · simpa only [truth,zero,ite_false] using law

#print axioms machine
end Solidity.Yul.Compilation.NormalStackTransport
