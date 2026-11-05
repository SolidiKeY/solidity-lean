import Solidity.Evm.MemoryRecursiveComposition

namespace Solidity.Evm.Memory.Recursive.Dispatch
variable {C : Contract} {Γ : Ctx}

/-- Every compiler result is constructed with derived frame bounds and
allocation metadata. These are conclusions, not output-law inputs. -/
theorem compile_every_depth_budget {b : Nat} {F : Frag Γ} {c : Val C Γ .bool} {body : Prog C Γ Γ}
    (condition : Memory.CompiledVal b F c) (out : CompiledProg b F body)
    (stable : out.frag.restrict Γ=F) (hc : Memory.compileVal b F c=some condition)
    (hp : compileProg b body F=some out) :
    ∀ n, ∃ result : CompiledProg b F (nest c body n),
      compileProg b (nest c body n) F=some result ∧ result.frag.restrict Γ=F ∧
      result.cert.need≤max Γ.length out.cert.need ∧ result.cert.allocates=out.cert.allocates := by
  intro n
  induction n with
  | zero=>exact ⟨out,hp,stable,Nat.le_max_right _ _,rfl⟩
  | succ n ih=>
    obtain ⟨inner,found,stableInner,need,allocation⟩:=ih
    refine ⟨wrap condition inner stableInner,wrap_found condition inner stableInner hc found,restrict_self F,?_,?_⟩
    · change max (max Γ.length inner.cert.need) Γ.length≤max Γ.length out.cert.need
      omega
    · change (inner.cert.allocates || false)=out.cert.allocates
      rw [Bool.or_false,allocation]

/-- Actual compiler result and COMPLETE runtime agreement at every finite
nesting depth, from initial StateRepr and the derived shared frame bound.
Nonallocation is a sufficient real metadata fact, not an admission guard. -/
theorem execution_every_depth {b L frame : Nat} {F : Frag Γ} {c : Val C Γ .bool} {body : Prog C Γ Γ}
    (condition : Memory.CompiledVal b F c) (out : CompiledProg b F body)
    (stable : out.frag.restrict Γ=F) (hc : Memory.compileVal b F c=some condition)
    (hp : compileProg b body F=some out) (nonallocating : out.cert.allocates=false)
    (σ : State C Γ) (base : Nat → Fin W) (m : Machine)
    (repr : StateRepr L b frame F σ base m) (capacity : b+max Γ.length out.cert.need≤frame) :
    ∀ n, ∃ result : CompiledProg b F (nest c body n), compileProg b (nest c body n) F=some result ∧
      LoopScopes.Result L b frame result.frag σ base m (fun o amount=>Cost result.cert σ o amount)
        ((nest c body n).run σ) (run result.code m) := by
  intro n
  obtain ⟨result,found,stableResult,need,allocation⟩:=compile_every_depth_budget condition out stable hc hp n
  have cap : b+result.cert.need≤frame := by omega
  have none : result.cert.allocates=false := allocation.trans nonallocating
  exact ⟨result,found,result.correct ⟨repr,cap,room_nonallocating result.cert none frame σ base m⟩⟩

end Solidity.Evm.Memory.Recursive.Dispatch
