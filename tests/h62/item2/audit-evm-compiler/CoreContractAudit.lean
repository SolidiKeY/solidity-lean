import Solidity.Backend.Payments.EntrySuccess
import tests.h62.item2.«audit-evm-compiler».HeadlineAudit

/-! A success contract over candidate code compilers. The premises are the
existing core-fragment, simulation, room and source-success conditions.
The actual checked entry satisfies it. Closed supported inputs refute four
trivial candidates; no Source adequacy or external gas/fork claim is made. -/
namespace Solidity.H62.EvmCompilerAudit.CoreContract
open Evm Evm.Examples

abbrev CodeCompiler := {C : Solidity.Contract} → (b : Nat) → {Γ Δ : Ctx} →
  (F : Frag Γ) → Solidity.Prog C Γ Δ → Option (List Instr)

def Succeeds (candidate : CodeCompiler) : Prop :=
  ∀ {C : Solidity.Contract} {Γ Δ : Ctx} {b L : Nat} {F : Frag Γ} {F' : Frag Δ}
    {P : Solidity.Prog C Γ Δ} {σ : State C Γ} {m : Machine}
    {o : Solidity.Out C σ.H Δ},
    inFragP F P = some F' → Sim C L b F σ m →
    L + Evm.Prog.pushes P ≤ Lmax → Solidity.Prog.run σ P = .ok o →
    ∃ code, candidate b F P = some code ∧ ∃ final,
      run code m = .ok final 0 ∧ final.stack = m.stack ∧
      Sim C (L + Evm.Prog.pushes P) b F' o.st final

def Admits (candidate : CodeCompiler) : Prop :=
  ∀ {C : Solidity.Contract} {Γ Δ : Ctx} {b : Nat} {F : Frag Γ} {F' : Frag Δ}
    {P : Solidity.Prog C Γ Δ}, inFragP F P = some F' →
    ∃ code, candidate b F P = some code

def Contract (candidate : CodeCompiler) : Prop := Admits candidate ∧ Succeeds candidate

def actual : CodeCompiler := fun {C} b {Γ Δ} F P =>
  (Compiler.compile (C := C) (Γ := Γ) (Δ := Δ) b F P).map Compiler.Compilation.code
def rejectAll : CodeCompiler := fun {_C} _b {_Γ _Δ} _F _P => none
def revertAll : CodeCompiler := fun {_C} _b {_Γ _Δ} _F _P => some [.revert]
def empty : CodeCompiler := fun {_C} _b {_Γ _Δ} _F _P => some []
def pendingJump : CodeCompiler := fun {C} b {Γ Δ} F P => (actual (C := C) (Γ := Γ) (Δ := Δ) b F P).map (· ++ [.jump 1])

/-- Admission and success, not just conditional agreement for returned results. -/
theorem actual_satisfies_contract : Contract actual := by
  constructor
  · intro C Γ Δ b F F' P fragment
    exact ⟨compileProg b P, by
      simp only [actual, Compiler.compile_core_some fragment, Option.map_some,
        Compiler.Compilation.code]⟩
  · intro C Γ Δ b L F F' P σ m o fragment represented room source
    obtain ⟨result, admitted, final, executed, stack, related⟩ :=
      Compiler.compile_core_success fragment represented room source
    exact ⟨result.code, by simp only [actual, admitted, Option.map_some], final,
      executed, stack, related⟩

theorem reject_all_fails_contract : ¬ Contract rejectAll := by
  intro contract
  obtain ⟨F, o, fragment, represented, room, _, source⟩ := source_success_joint
  obtain ⟨code, admitted, _⟩ := contract.2 fragment represented room source
  cases admitted

theorem revert_all_fails_contract : ¬ Contract revertAll := by
  intro contract
  obtain ⟨F, o, fragment, represented, room, _, source⟩ := source_success_joint
  obtain ⟨code, admitted, final, executed, _⟩ := contract.2 fragment represented room source
  cases Option.some.inj admitted
  cases executed

private theorem uint_cell {st : WordStore} {L : Nat} {s : Slot}
    {v : PrimTy.uint.Denote} (h : ReprAt st L (.prim .uint) s (.prim v)) :
    st s = v.1.toNat := by
  cases h with
  | prim h =>
    obtain ⟨a, ha, hv⟩ := h
    cases ha
    change (st.cells s).val = v.1.toNat
    rw [hv, Int.toNat_natCast]

private theorem uint_slot_same {C : Solidity.Contract} {L L' : Nat} {st st' : WordStore}
    {storage : Storage C} {r : SRef C (.prim .uint)} {s : Slot}
    (left : ReprStore C L st storage) (right : ReprStore C L' st' storage)
    (path : PathSlot C true r s) : st s = st' s := by
  rcases find_repr left path with ⟨v, found, represented⟩ | ⟨impossible, _⟩
  · rcases find_repr right path with ⟨v', found', represented'⟩ | ⟨impossible, _⟩
    · have same : v = v' := Option.some.inj (found.symm.trans found')
      cases same
      cases v with
      | prim value => exact (uint_cell represented).trans (uint_cell represented').symm
    · cases impossible
  · cases impossible

private def ageRef : SRef StandardExample (.prim .uint) :=
  ⟨"alice", rfl, .field (f := "age") rfl .nil⟩

theorem empty_fails_contract : ¬ Contract empty := by
  intro contract
  obtain ⟨F, o, fragment, represented, room, _, source⟩ := source_success_joint
  obtain ⟨code, admitted, final, executed, _, related⟩ :=
    contract.2 fragment represented room source
  cases Option.some.inj admitted
  change Out.ok fresh 0 = Out.ok final 0 at executed
  cases executed
  obtain ⟨code, admitted, actualFinal, actualRun, actualStore⟩ := compiled_setAge_writes
  cases Option.some.inj admitted
  obtain ⟨o', source', actualRelated⟩ := compile_box fragment represented room actualRun
  have same : o' = o := Except.ok.inj (source'.symm.trans source)
  cases same
  have path : PathSlot StandardExample true ageRef (.root 13) := PathAt.field PathAt.nil
  have unchanged : fresh.store (.root 13) = actualFinal.store (.root 13) :=
    uint_slot_same related.store actualRelated.store path
  change (0 : Nat) = actualFinal.store (.root 13) at unchanged
  rw [actualStore] at unchanged
  cases unchanged

theorem pending_jump_fails_contract : ¬ Contract pendingJump := by
  intro contract
  obtain ⟨F, o, fragment, represented, room, _, source⟩ := source_success_joint
  obtain ⟨code, admitted, final, executed, _⟩ := contract.2 fragment represented room source
  have actualAdmitted : actual 0 (Frag.init []) setAge = some (compileProg 0 setAge) := by
    simp only [actual, Compiler.compile_core_some fragment, Option.map_some,
      Compiler.Compilation.code]
  change (actual 0 (Frag.init []) setAge).map (· ++ [.jump 1]) = some code at admitted
  rw [actualAdmitted] at admitted
  cases Option.some.inj admitted
  obtain ⟨code, accepted, actualFinal, actualRun, _⟩ := compiled_setAge_writes
  cases Option.some.inj accepted
  have jumped : run (compileProg 0 setAge ++ [.jump 1]) fresh = .ok actualFinal 1 := by
    rw [run_append_ok actualRun]
    rfl
  rw [jumped] at executed
  cases executed

#print axioms actual_satisfies_contract
#print axioms reject_all_fails_contract
#print axioms revert_all_fails_contract
#print axioms uint_cell
#print axioms uint_slot_same
#print axioms empty_fails_contract
#print axioms pending_jump_fails_contract
end Solidity.H62.EvmCompilerAudit.CoreContract
