import Solidity.Evm.Compiler
import Solidity.Evm.MemoryRecursiveRoom

/-! Additive checked entry preserving every existing compiler choice verbatim.
Only an existing refusal selects the closed recursive-loop compiler. No owner
compiler, AST, source state or target semantics is replaced. -/
namespace Solidity.Evm.Memory.Recursive
variable {C : Contract}

theorem StmtCert.pushes_zero {b Γ Δ F G s code}
    (hs : StmtCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G s code) : Evm.Stmt.pushes s=0 := by
  induction hs using StmtCert.rec (motive_2:=fun F G P code hp=>Evm.Prog.pushes P=0) with
  | base cert=>exact cert.pushes_zero
  | block hp ih=>exact ih
  | ite hc ht he iht ihe=>change Evm.Prog.pushes _+Evm.Prog.pushes _=0;rw [iht,ihe]
  | loop a hc hp stable ih=>rfl
  | nil F=>rfl
  | cons hs hp ihs ihp=>change Evm.Stmt.pushes _+Evm.Prog.pushes _=0;rw [ihs,ihp]

theorem ProgCert.pushes_zero {b Γ Δ F G P code}
    (hp : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G P code) : Evm.Prog.pushes P=0 := by
  induction hp using ProgCert.rec (motive_1:=fun F G s code hs=>Evm.Stmt.pushes s=0) with
  | base cert=>exact cert.pushes_zero
  | block hp ih=>exact ih
  | ite hc ht he iht ihe=>change Evm.Prog.pushes _+Evm.Prog.pushes _=0;rw [iht,ihe]
  | loop a hc hp stable ih=>rfl
  | nil F=>rfl
  | cons hs hp ihs ihp=>change Evm.Stmt.pushes _+Evm.Prog.pushes _=0;rw [ihs,ihp]

namespace Dispatch
/-- Both choices retain the SAME actual intrinsic program and input fragment. -/
abbrev Choice (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) :=
  Sum (Compiler.Compilation b F P) (CompiledProg b F P)

def compile (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) : Option (Choice b F P) :=
  match Compiler.compile b F P with
  | some old=>some (.inl old)
  | none=>(Recursive.compileProg b P F).map Sum.inr

def code {b Γ Δ F P} : Choice (C:=C) b (Γ:=Γ) (Δ:=Δ) F P → List Instr
  | .inl old=>old.code
  | .inr out=>out.code

def Input {b Γ Δ F P} (choice : Choice (C:=C) b (Γ:=Γ) (Δ:=Δ) F P)
    (L frame : Nat) (base : Nat → Fin W) (σ : State C Γ) (m : Machine) : Prop :=
  match choice with
  | .inl old=>old.Input L frame base σ m
  | .inr out=>out.Input L frame σ base m

def Rep {b Γ Δ F P} (choice : Choice (C:=C) b (Γ:=Γ) (Δ:=Δ) F P)
    (L frame : Nat) (base : Nat → Fin W) (entry : State C Γ) (initial : Machine)
    (σ : State C Δ) (m : Machine) : Prop :=
  match choice with
  | .inl old=>old.Rep L frame base entry initial σ m
  | .inr out=>∃ base' amount, ∃ ext : entry.H <+: σ.H,
      Cost out.cert entry ⟨σ,ext⟩ amount ∧ StateRepr L b frame out.frag σ base' m ∧
      BaseExtends entry.H base base' ∧ GrowsAllocator b frame amount entry base initial σ base' m

/-- EXACT existing observation shape, including existing panic/pay cases.
Recursive fallback derives the applicable success/revert/divergence cases. -/
def Agrees {b Γ Δ F P} (choice : Choice (C:=C) b (Γ:=Γ) (Δ:=Δ) F P)
    (L frame : Nat) (base : Nat → Fin W) (σ : State C Γ) (m : Machine) : Prop :=
  (∃ o m', P.run σ=.ok o ∧ run (code choice) m=.ok m' 0 ∧ m'.stack=m.stack ∧
    Rep choice (L+Evm.Prog.pushes P) frame base σ m o.st m') ∨
  ((P.run σ=.error .revert ∨ (P.asserts=true ∧ P.run σ=.error .panic)) ∧ run (code choice) m=.revert) ∨
  (Evm.Prog.pays P=true ∧ run (code choice) m=.revert ∧ ∃ o m', P.run σ=.ok o ∧
    Rep choice (L+Evm.Prog.pushes P) frame base σ m o.st m') ∨
  (P.run σ=.error .diverge ∧ (run (code choice) m=.fault ∨ (Evm.Prog.pays P=true ∧ run (code choice) m=.revert)))

theorem existing_exact {b Γ Δ F P} (old : Compiler.Compilation (C:=C) b (Γ:=Γ) (Δ:=Δ) F P)
    (L frame : Nat) (base : Nat → Fin W) (σ : State C Γ) (m : Machine) :
    Agrees (.inl old) L frame base σ m ↔ old.Agrees L frame base σ m := Iff.rfl

theorem correct {b Γ Δ F P L frame} (choice : Choice (C:=C) b (Γ:=Γ) (Δ:=Δ) F P)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine} (input : Input choice L frame base σ m) :
    Agrees choice L frame base σ m := by
  cases choice with
  | inl old=>exact old.correct input
  | inr out=>
    simp only [Agrees,code,Rep,out.cert.pushes_zero,Nat.add_zero]
    rcases out.correct input with
      ⟨o,next,newBase,amount,source,target,cost,repr,stack,bases,growth⟩ | ⟨source,target⟩ | ⟨source,target⟩
    · exact .inl ⟨o,next,source,target,stack,newBase,amount,o.ext,cost,repr,bases,growth⟩
    · exact .inr (.inl ⟨.inl source,target⟩)
    · exact .inr (.inr (.inr ⟨source,.inl target⟩))

theorem preserves_existing {b Γ Δ F P} {old : Compiler.Compilation (C:=C) b (Γ:=Γ) (Δ:=Δ) F P}
    (found : Compiler.compile b F P=some old) : compile b F P=some (.inl old) := by
  simp only [compile,found]

theorem selects_recursive {b Γ Δ F P} (refused : Compiler.compile (C:=C) b (Γ:=Γ) (Δ:=Δ) F P=none)
    {out : CompiledProg b F P} (found : Recursive.compileProg b P F=some out) :
    compile b F P=some (.inr out) := by simp only [compile,refused,found,Option.map_some]

theorem refusal_exact {b Γ Δ F P} : compile (C:=C) b (Γ:=Γ) (Δ:=Δ) F P=none ↔
    Compiler.compile b F P=none ∧ Recursive.compileProg b P F=none := by
  unfold compile
  cases old : Compiler.compile b F P with
  | some out=>simp only [reduceCtorEq,false_and]
  | none=>simp only [true_and,Option.map_eq_none_iff]

end Dispatch
end Solidity.Evm.Memory.Recursive
