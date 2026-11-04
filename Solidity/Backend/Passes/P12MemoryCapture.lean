import Solidity.Backend.Passes.ReturnedMemoryCapture
import Solidity.Lowering.V07.P12NextInterface

/-! Conditional consumer of the exact published P12 request. Source lowering
fields remain explicit owner obligations; the physical compiler Input is
separate. This constructs no P8 admission or P12 producer instance. -/
namespace Solidity.Backend.Passes.P12MemoryCapture
open Evm Evm.Memory Evm.Compiler Solidity.Lowering.V07
open P12NextInterface

variable {E : Source.Env} {C : Contract} {srcΓ : Source.RCtx} {Γ : Ctx}
  {G : Source.Glob E} {SF : Source.Fr} {m : ContextMap srcΓ Γ}
  {values : ValueRelation E C} {worlds : WorldRelation E C}
  {τ : Source.STy} {location : τ.loc? = some .memory} {R : RefTy}
  {mapFree : (Ty.ref R).mapFree = true} {expr : Source.RExpr E srcΓ τ}
  {b L frame : Nat} {F : Frag Γ}

theorem execution (request : MemoryCapture G SF m values worlds τ location R mapFree expr)
    (compiled : CompiledProg b F request.code)
    (accepted : Memory.compileProg b F request.code = some compiled)
    (source after : Source.EMState E srcΓ) (target : State C Γ)
    (machine : Machine) (base : Nat → Fin W) (fuel address : Nat)
    (aligned : Aligned m values worlds source target)
    (sourceRun : (Source.evalE G SF fuel expr).run source =
      (.ok (.val (.memRef location address)),after))
    (input : (Compilation.memory compiled).Input L frame base target machine)
    (free : Evm.Prog.pays request.code = false) :
    ∃ (out : Solidity.Out C target.H (.mem R :: Γ)) (ref : HRef out.st.H R),
      request.code.run target = .ok out ∧ TEnv.get .here out.st.env = some ref ∧
      (MPath.var .here mapFree : MPath C (.mem R :: Γ) (.ref R)).mvalT out.st = .ok ref ∧
      (m.cons τ (.mem R)).Related (values after.2 out.st.glob)
        (.cons (.memRef location address) after.1) out.st.env ∧
      worlds after.2 out.st.glob ∧
      (∀ (σ : Source.STy) (oldLocation : σ.loc? = some .memory)
        (i : Source.Idx srcΓ σ) (oldR : RefTy) (j : Idx Γ (.mem oldR))
        (oldAddress : Nat) (oldRef : HRef out.st.H oldR),
        m.slot i = ⟨.mem oldR,j⟩ → after.1.get i = .memRef oldLocation oldAddress →
        TEnv.get (.there j) out.st.env = some oldRef →
        (address = oldAddress ↔ ref.id = oldRef.id)) ∧
      ∃ (canonical : Machine) (selected : Nat → Fin W), canonical.stack = [] ∧ ∀ tail,
        (Compilation.memory compiled).Input L frame base target {machine with stack := tail} ∧
        run compiled.code {machine with stack := tail} = .ok {canonical with stack := tail} 0 ∧
        MappedOutput (.memory compiled) L frame base target {machine with stack := tail}
          out.st {canonical with stack := tail} selected ∧
        canonical.mem (cell (b+Γ.length)) = .val (selected ref.id) ∧
        run (compiled.code ++ [.mload (cell (b+Γ.length))]) {machine with stack := tail} =
          .ok ({canonical with stack := tail}.push (.val (selected ref.id))) 0 := by
  obtain ⟨out,ref,sourceTarget,bound,path,contexts,world,aliases⟩ :=
    request.success fuel source after target address aligned sourceRun
  obtain ⟨_,canonical,selected,empty,runs⟩ := ReturnedMemoryCapture.readback
    compiled accepted input free sourceTarget ref bound
  exact ⟨out,ref,sourceTarget,bound,path,contexts,world,aliases,canonical,selected,empty,runs⟩

/-- The empty-data branch uses the original coarse revert law, with no
post-failure state/map and no execution required beyond the actual failure. -/
theorem empty_revert
    (request : MemoryCapture G SF m values worlds τ location R mapFree expr)
    (compiled : CompiledProg b F request.code)
    (source after : Source.EMState E srcΓ) (target : State C Γ)
    (machine : Machine) (base : Nat → Fin W) (fuel : Nat)
    (aligned : Aligned m values worlds source target)
    (sourceRun : (Source.evalE G SF fuel expr).run source = (.error (.revert []),after))
    (input : (Compilation.memory compiled).Input L frame base target machine)
    (free : Evm.Prog.pays request.code = false) :
    ∀ tail, run compiled.code {machine with stack := tail} = .revert := by
  have failed := request.revert fuel source after target [] aligned sourceRun
  change request.code.run target = .error .revert at failed
  intro tail
  exact (compilation_revert_iff (.memory compiled)
    (compilation_input_stack (.memory compiled) input tail) free).mpr (.inl failed)

/-- Nonempty Source revert data cannot silently be collapsed to the coarse
terminal compiler boundary. The present request/compilation combination is
incompatible with that actual reached Source failure under these premises. -/
theorem nonempty_revert_incompatible
    (request : MemoryCapture G SF m values worlds τ location R mapFree expr)
    (compiled : CompiledProg b F request.code)
    (source after : Source.EMState E srcΓ) (target : State C Γ)
    (machine : Machine) (base : Nat → Fin W) (fuel : Nat) (data : Roadmap.Bytes)
    (aligned : Aligned m values worlds source target)
    (sourceRun : (Source.evalE G SF fuel expr).run source = (.error (.revert data),after))
    (nonempty : data ≠ [])
    (input : (Compilation.memory compiled).Input L frame base target machine)
    (free : Evm.Prog.pays request.code = false) : False := by
  have failed := request.revert fuel source after target data aligned sourceRun
  have exactData : THalt.ofData data = .revertWith data := by
    cases data with
    | nil => exact False.elim (nonempty rfl)
    | cons x xs => rfl
  rw [exactData] at failed
  exact ReturnedMemoryCapture.excludes_revert_with compiled input free data failed

/-- info: 'Solidity.Backend.Passes.P12MemoryCapture.execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms execution
/-- info: 'Solidity.Backend.Passes.P12MemoryCapture.empty_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms empty_revert
/-- info: 'Solidity.Backend.Passes.P12MemoryCapture.nonempty_revert_incompatible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nonempty_revert_incompatible
end Solidity.Backend.Passes.P12MemoryCapture
