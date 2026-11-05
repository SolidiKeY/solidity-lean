import Solidity.Backend.Passes.ReturnedStorageCapture
import Solidity.Lowering.V07.P12NextInterface

/-! Exact published P12 storage-capture fields, conditional on their producer.
Physical readback is symbolic PathSlot, not numeric layout/hash adequacy. -/
namespace Solidity.Backend.Passes.P12StorageCapture
open Evm Evm.Compiler Solidity.Lowering.V07
open P12NextInterface
variable {E : Source.Env} {C : Contract} {srcΓ : Source.RCtx} {Γ : Ctx}
  {G : Source.Glob E} {SF : Source.Fr} {m : ContextMap srcΓ Γ}
  {values : ValueRelation E C} {worlds : WorldRelation E C}
  {τ : Source.STy} {location : τ.loc? = some .storage} {R : RefTy}
  {expr : Source.RExpr E srcΓ τ} {b L frame : Nat} {F : Frag Γ}

theorem execution (request : StorageCapture G SF m values worlds τ location R expr)
    (compiled : Compilation b F request.code)
    (accepted : Compiler.compile b F request.code = some compiled)
    (source after : Source.EMState E srcΓ) (target : State C Γ)
    (machine : Machine) (base : Nat → Fin W) (fuel : Nat) (path : Source.SPath)
    (aligned : Aligned m values worlds source target)
    (sourceRun : (Source.evalE G SF fuel expr).run source =
      (.ok (.val (.storRef location path)),after))
    (input : compiled.Input L frame base target machine)
    (free : Evm.Prog.pays request.code = false) (plain : compiled.frag.get .here = .ok) :
    ∃ (out : Solidity.Out C target.H (.alias R :: Γ)) (ref : SRef C (.ref R)),
      request.code.run target = .ok out ∧ TEnv.get .here out.st.env = some ref ∧
      (SPath.alias .here : SPath C (.alias R :: Γ) (.ref R)).resolveT out.st = .ok ref ∧
      (m.cons τ (.alias R)).Related (values after.2 out.st.glob)
        (.cons (.storRef location path) after.1) out.st.env ∧
      worlds after.2 out.st.glob ∧
      (∀ (σ : Source.STy) (oldLocation : σ.loc? = some .storage)
        (i : Source.Idx srcΓ σ) (j : Idx Γ (.alias R)) (oldPath : Source.SPath) (oldRef : SRef C (.ref R)),
        m.slot i = ⟨.alias R,j⟩ → after.1.get i = .storRef oldLocation oldPath →
        TEnv.get (.there j) out.st.env = some oldRef → (path = oldPath ↔ ref = oldRef)) ∧
      ∃ (canonical : Machine) (selected : Nat → Fin W) (slot : Slot),
        PathSlot C true ref slot ∧ canonical.stack = [] ∧ ∀ tail,
        compiled.Input L frame base target {machine with stack := tail} ∧
        run compiled.code {machine with stack := tail} = .ok {canonical with stack := tail} 0 ∧
        MappedOutput compiled (L + Evm.Prog.pushes request.code) frame base target {machine with stack := tail}
          out.st {canonical with stack := tail} selected ∧
        canonical.mem (cell (b+Γ.length)) = .slot slot ∧
        run (compiled.code ++ [.mload (cell (b+Γ.length))]) {machine with stack := tail} =
          .ok ({canonical with stack := tail}.push (.slot slot)) 0 := by
  obtain ⟨out,ref,sourceTarget,bound,resolved,contexts,world,aliases⟩ :=
    request.success fuel source after target path aligned sourceRun
  obtain ⟨_,canonical,selected,slot,pathSlot,empty,runs⟩ :=
    ReturnedStorageCapture.readback compiled accepted input free sourceTarget ref bound plain
  exact ⟨out,ref,sourceTarget,bound,resolved,contexts,world,aliases,canonical,selected,slot,pathSlot,empty,runs⟩

theorem empty_revert (request : StorageCapture G SF m values worlds τ location R expr)
    (compiled : Compilation b F request.code)
    (source after : Source.EMState E srcΓ) (target : State C Γ)
    (machine : Machine) (base : Nat → Fin W) (fuel : Nat)
    (aligned : Aligned m values worlds source target)
    (sourceRun : (Source.evalE G SF fuel expr).run source = (.error (.revert []),after))
    (input : compiled.Input L frame base target machine) (free : Evm.Prog.pays request.code = false) :
    ∀ tail, run compiled.code {machine with stack := tail} = .revert := by
  have failed := request.revert fuel source after target [] aligned sourceRun
  change request.code.run target = .error .revert at failed
  intro tail
  exact (compilation_revert_iff compiled (compilation_input_stack compiled input tail) free).mpr (.inl failed)

/-- Current internal compilation cannot silently erase nonempty failure data. -/
theorem nonempty_revert_incompatible
    (request : StorageCapture G SF m values worlds τ location R expr)
    (compiled : Compilation b F request.code)
    (source after : Source.EMState E srcΓ) (target : State C Γ)
    (machine : Machine) (base : Nat → Fin W) (fuel : Nat) (data : Roadmap.Bytes)
    (aligned : Aligned m values worlds source target)
    (sourceRun : (Source.evalE G SF fuel expr).run source = (.error (.revert data),after))
    (nonempty : data ≠ []) (input : compiled.Input L frame base target machine)
    (free : Evm.Prog.pays request.code = false) : False := by
  have failed := request.revert fuel source after target data aligned sourceRun
  have exactData : THalt.ofData data = .revertWith data := by
    cases data with
    | nil => exact False.elim (nonempty rfl)
    | cons x xs => rfl
  rw [exactData] at failed
  rcases compilation_exact compiled input free with
    ⟨out,final,actual,rest⟩ | ⟨actual,rest⟩ | ⟨actual,rest⟩
  · rw [failed] at actual
    cases actual
  · rcases actual with actual | ⟨_,actual⟩
    · rw [failed] at actual
      cases actual
    · rw [failed] at actual
      cases actual
  · rw [failed] at actual
    cases actual

/-- info: 'Solidity.Backend.Passes.P12StorageCapture.execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms execution
/-- info: 'Solidity.Backend.Passes.P12StorageCapture.empty_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms empty_revert
/-- info: 'Solidity.Backend.Passes.P12StorageCapture.nonempty_revert_incompatible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nonempty_revert_incompatible
end Solidity.Backend.Passes.P12StorageCapture
