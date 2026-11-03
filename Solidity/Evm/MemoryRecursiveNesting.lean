import Solidity.Evm.MemoryRecursiveDispatch

namespace Solidity.Evm.Memory.Recursive.Dispatch
variable {C : Contract} {Γ : Ctx}

theorem restrict_self (F : Frag Γ) : F.restrict Γ=F := by
  cases F
  simp only [Frag.restrict,Nat.sub_self,List.drop_zero]

def loopProgram (c : Val C Γ .bool) (body : Prog C Γ Γ) : Prog C Γ Γ :=
  .cons (.loop .auto c body) .nil

def wrap {b : Nat} {F : Frag Γ} {c : Val C Γ .bool} {body : Prog C Γ Γ} (condition : Memory.CompiledVal b F c)
    (out : CompiledProg b F body) (stable : out.frag.restrict Γ=F) :
    CompiledProg b F (loopProgram c body) :=
  ⟨F,[.loop condition.code out.code],.cons (.loop .auto condition.cert out.cert stable) (.nil F)⟩

/-- Constructor closure uses actual compiler outcomes, not a supplied inverse
or final soundness law. -/
theorem wrap_found {b : Nat} {F : Frag Γ} {c : Val C Γ .bool} {body : Prog C Γ Γ} (condition : Memory.CompiledVal b F c)
    (out : CompiledProg b F body) (stable : out.frag.restrict Γ=F)
    (hc : Memory.compileVal b F c=some condition) (hp : Recursive.compileProg b body F=some out) :
    Recursive.compileProg b (loopProgram c body) F=some (wrap condition out stable) := by
  change (do
    let first ← Recursive.compileStmt b (.loop .auto c body) F
    let last ← Recursive.compileProg b Prog.nil first.frag
    pure (⟨last.frag,first.code++last.code,.cons first.cert last.cert⟩ : CompiledProg b F (loopProgram c body)))=_
  change (do
    let first ← (do
      let condition ← Memory.compileVal b F c
      let inner ← Recursive.compileProg b body F
      if stable : inner.frag.restrict Γ=F then
        pure (⟨F,[.loop condition.code inner.code],.loop .auto condition.cert inner.cert stable⟩ : CompiledStmt b F (.loop .auto c body))
      else none)
    let last ← Recursive.compileProg b Prog.nil first.frag
    pure (⟨last.frag,first.code++last.code,.cons first.cert last.cert⟩ : CompiledProg b F (loopProgram c body)))=_
  rw [hc]
  rw [hp]
  simp only [bind,Option.bind,dif_pos stable]
  rfl

/-- Actual nested programs, with no recursion-depth cap. -/
def nest (c : Val C Γ .bool) (body : Prog C Γ Γ) : Nat → Prog C Γ Γ
  | 0=>body
  | n+1=>loopProgram c (nest c body n)

/-- Every finite depth has an actual successful recursive compiler result.
Stability is only the genuine initial body's layout fact; each new wrapper
constructively returns F. -/
theorem compile_every_depth {b : Nat} {F : Frag Γ} {c : Val C Γ .bool} {body : Prog C Γ Γ} (condition : Memory.CompiledVal b F c)
    (out : CompiledProg b F body) (stable : out.frag.restrict Γ=F)
    (hc : Memory.compileVal b F c=some condition) (hp : Recursive.compileProg b body F=some out) :
    ∀ n, ∃ result : CompiledProg b F (nest c body n),
      Recursive.compileProg b (nest c body n) F=some result ∧ result.frag.restrict Γ=F := by
  intro n
  induction n with
  | zero=>exact ⟨out,hp,stable⟩
  | succ n ih=>
    obtain ⟨inner,found,stable⟩:=ih
    exact ⟨wrap condition inner stable,wrap_found condition inner stable hc found,restrict_self F⟩

/-- Old acceptance or recursive acceptance yields actual checked-entry
acceptance; existing priority is retained at EVERY depth. -/
theorem entry_every_depth {b : Nat} {F : Frag Γ} {c : Val C Γ .bool} {body : Prog C Γ Γ} (condition : Memory.CompiledVal b F c)
    (out : CompiledProg b F body) (stable : out.frag.restrict Γ=F)
    (hc : Memory.compileVal b F c=some condition) (hp : Recursive.compileProg b body F=some out)
    (n : Nat) : ∃ choice : Choice b F (nest c body n),compile b F (nest c body n)=some choice := by
  obtain ⟨result,found,stable⟩:=compile_every_depth condition out stable hc hp n
  cases old : Compiler.compile b F (nest c body n) with
  | some oldResult=>exact ⟨.inl oldResult,preserves_existing old⟩
  | none=>exact ⟨.inr result,selects_recursive old found⟩

end Solidity.Evm.Memory.Recursive.Dispatch
