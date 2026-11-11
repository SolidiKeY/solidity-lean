import Solidity.Examples.Roadmap.V16.FiniteHeapConsumer
import Solidity.Examples.Roadmap.V16.ConstructionCompilation

/-! Actual compilation-function algebra. These statements do not assume a
simulation and do not supply frontend/full-profile compilation coverage. -/
namespace Solidity.Roadmap.V16
open Solidity.Evm

def finiteMemoryCertificate {C : Contract} {b : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemory = true) : Memory.CompiledProg b F P := by
  cases compiled with
  | memoryCopy _ => cases path
  | fixedMemory _ => cases path
  | copyConstruction _ => cases path
  | core _ _ => cases path
  | construction _ => cases path
  | referenceArrays _ => cases path
  | objects _ => cases path
  | memoryLoops _ => cases path
  | memoryLoopScopes _ => cases path
  | memoryCalls _ _ => cases path
  | memory out => exact out

theorem finite_memory_reconstruct {C : Contract} {b : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemory = true) : Compiler.Compilation.memory (finiteMemoryCertificate compiled path) = compiled := by
  cases compiled with
  | memoryCopy _ => cases path
  | fixedMemory _ => cases path
  | copyConstruction _ => cases path
  | core _ _ => cases path
  | construction _ => cases path
  | referenceArrays _ => cases path
  | objects _ => cases path
  | memoryLoops _ => cases path
  | memoryLoopScopes _ => cases path
  | memoryCalls _ _ => cases path
  | memory out => rfl

theorem finite_memory_compile_inversion {C : Contract} {b : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemory = true)
    (accepted : Compiler.compile b F P = some compiled) :
    Memory.compileProg b F P = some (finiteMemoryCertificate compiled path) := by
  cases compiled with
  | memoryCopy _ => cases path
  | fixedMemory _ => cases path
  | copyConstruction _ => cases path
  | core _ _ => cases path
  | construction _ => cases path
  | referenceArrays _ => cases path
  | objects _ => cases path
  | memoryLoops _ => cases path
  | memoryLoopScopes _ => cases path
  | memoryCalls _ _ => cases path
  | memory out =>
    change Memory.compileProg b F P = some out
    simp only [Compiler.compile,Option.map] at accepted
    repeat' (first | split at accepted | cases accepted)
    all_goals first
      | assumption
      | (change (match Memory.StorageCopy.compileProg b F P with
          | some copied => some (Compiler.Compilation.memoryCopy copied)
          | none => match Memory.Fixed.compileProg b F P with
            | some fixed => some (Compiler.Compilation.fixedMemory fixed)
            | none => (Memory.CopyConstruction.compileProg b F P).map
                Compiler.Compilation.copyConstruction) = some (.memory out) at accepted
         simp only [Option.map] at accepted
         repeat' (first | split at accepted | cases accepted))

theorem finite_memory_compile_append {C : Contract} {b : Nat} {Γ Ξ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Ξ} {Q : Prog C Ξ Δ}
    (head : Memory.CompiledProg b F P)
    (tail : Memory.CompiledProg b head.frag Q)
    (compiledHead : Memory.compileProg b F P = some head)
    (compiledTail : Memory.compileProg b head.frag Q = some tail) :
    ∃ out : Memory.CompiledProg b F (constructionAppend P Q),
      Memory.compileProg b F (constructionAppend P Q) = some out ∧
      out.frag = tail.frag ∧ out.code = head.code ++ tail.code := by
  revert head
  cases hSource : P with
  | nil =>
    intro head tail compiledHead compiledTail
    simp only [Memory.compileProg,Option.some.injEq] at compiledHead
    cases compiledHead
    exact ⟨tail,compiledTail,rfl,by simp only [List.nil_append]⟩
  | cons stmt rest =>
    intro head tail compiledHead compiledTail
    cases hs : Memory.compileStmt b F stmt with
    | none =>
      simp only [Memory.compileProg,hs,bind,Option.bind] at compiledHead
      cases compiledHead
    | some first =>
      cases hp : Memory.compileProg b first.frag rest with
      | none =>
        simp only [Memory.compileProg,hs,hp,bind,Option.bind] at compiledHead
        cases compiledHead
      | some second =>
        simp only [Memory.compileProg,hs,hp,bind,Option.bind,pure,
          Option.some.injEq] at compiledHead
        cases compiledHead
        obtain ⟨joined,hjoined,frag,code⟩ :=
          finite_memory_compile_append (P := rest) second tail hp compiledTail
        let out : Memory.CompiledProg b F (constructionAppend (.cons stmt rest) Q) :=
          ⟨joined.frag,first.code ++ joined.code,.cons first.cert joined.cert⟩
        refine ⟨out,?_,frag,?_⟩
        · simp only [constructionAppend,Memory.compileProg,hs,hjoined,
            bind,Option.bind,pure,out]
        · simp only [out,code,List.append_assoc]

termination_by sizeOf P
decreasing_by
  all_goals subst P
  all_goals simp_wf
  all_goals omega

/-- Preserve source typing while observing only the actual output fragment/code;
this is an output projection, not another IR or execution semantics. -/
def finiteMemoryShape {C : Contract} (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) :
    Option (Frag Δ × List Instr) :=
  (Memory.compileProg b F P).map (fun out => (out.frag,out.code))

theorem finite_memory_compile_append_link {C : Contract} {b : Nat} {Γ Ξ Δ : Ctx}
    {F : Frag Γ} {G : Frag Ξ} {P : Prog C Γ Ξ} {Q : Prog C Ξ Δ}
    (head : Memory.CompiledProg b F P)
    (tail : Memory.CompiledProg b G Q) (link : head.frag = G)
    (compiledHead : Memory.compileProg b F P = some head)
    (compiledTail : Memory.compileProg b G Q = some tail) :
    finiteMemoryShape b F (constructionAppend P Q) = some (tail.frag,head.code ++ tail.code) := by
  cases link
  obtain ⟨out,compiled,frag,code⟩ := finite_memory_compile_append head tail compiledHead compiledTail
  simp only [finiteMemoryShape,compiled,Option.map_some,frag,code]

theorem finite_memory_certificate_code {C : Contract} {b : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemory = true) :
    (finiteMemoryCertificate compiled path).code = compiled.code :=
  congrArg Compiler.Compilation.code (finite_memory_reconstruct compiled path)

theorem finite_memory_certificate_fragment {C : Contract} {b : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemory = true) :
    (finiteMemoryCertificate compiled path).frag = compiled.frag :=
  congrArg Compiler.Compilation.frag (finite_memory_reconstruct compiled path)

/-- Canonical public-code composition follows from the ACTUAL compiler function
and actual success equations, not certificate uniqueness or assumed simulation. -/
theorem finite_memory_public_append_code {C : Contract} {b : Nat} {Γ Ξ Δ : Ctx}
    {F : Frag Γ} {G : Frag Ξ} {P : Prog C Γ Ξ} {Q : Prog C Ξ Δ} {R : Prog C Γ Δ}
    (whole : Compiler.Compilation b F R) (wholePath : whole.isMemory = true)
    (head : Compiler.Compilation b F P) (headPath : head.isMemory = true)
    (tail : Compiler.Compilation b G Q) (tailPath : tail.isMemory = true)
    (link : head.frag = G) (source : constructionAppend P Q = R)
    (compiledWhole : Compiler.compile b F R = some whole)
    (compiledHead : Compiler.compile b F P = some head)
    (compiledTail : Compiler.compile b G Q = some tail) :
    whole.code = head.code ++ tail.code ∧ whole.frag = tail.frag := by
  have lowHead := finite_memory_compile_inversion head headPath compiledHead
  have lowTail := finite_memory_compile_inversion tail tailPath compiledTail
  have lowWhole := finite_memory_compile_inversion whole wholePath compiledWhole
  have fragment : (finiteMemoryCertificate head headPath).frag = G :=
    (finite_memory_certificate_fragment head headPath).trans link
  have joined := finite_memory_compile_append_link
    (finiteMemoryCertificate head headPath) (finiteMemoryCertificate tail tailPath)
    fragment lowHead lowTail
  rw [source] at joined
  have actual : finiteMemoryShape b F R = some
      ((finiteMemoryCertificate whole wholePath).frag,(finiteMemoryCertificate whole wholePath).code) := by
    simp only [finiteMemoryShape,lowWhole,Option.map_some]
  have eq := Option.some.inj (actual.symm.trans joined)
  constructor
  · simpa only [finite_memory_certificate_code] using congrArg Prod.snd eq
  · simpa only [finite_memory_certificate_fragment] using congrArg Prod.fst eq

private theorem intrinsic_cons_error {C : Contract} {Γ Ξ Δ : Ctx} {σ : State C Γ}
    {s : Stmt C Γ Ξ} (P : Prog C Ξ Δ) {e : THalt} (h : s.run σ = .error e) :
    (Prog.cons s P).run σ = .error e := by
  show TRun.seq s.runR P.runR σ = _
  simp only [TRun.seq,Solidity.Stmt.run] at h ⊢
  rw [h]

/-- Exact intrinsic source composition, including every existing halt class. -/
theorem intrinsic_append_run {C : Contract} {Γ Ξ Δ : Ctx}
    (P : Prog C Γ Ξ) (Q : Prog C Ξ Δ) (σ : State C Γ) :
    (constructionAppend P Q).run σ = (P.run σ).bind fun o =>
      (Q.run o.st).map fun u => ⟨u.st,o.ext.trans u.ext⟩ := by
  cases hSource : P with
  | nil =>
    simp only [constructionAppend,Solidity.Prog.run_nil,Except.bind]
    cases Q.run σ <;> rfl
  | cons stmt rest =>
    cases hs : stmt.run σ with
    | error e =>
      simp only [constructionAppend,intrinsic_cons_error _ hs,Except.bind]
    | ok o =>
      simp only [constructionAppend]
      rw [Solidity.Prog.run_cons_ok hs,Solidity.Prog.run_cons_ok hs,
        intrinsic_append_run rest Q o.st]
      cases rest.run o.st with
      | error e => rfl
      | ok u =>
        simp only [Except.bind,Except.map]
        cases Q.run u.st <;> rfl
termination_by sizeOf P
decreasing_by
  all_goals subst P
  all_goals simp_wf
  all_goals omega

/-- Keep approved panic/failure/exhaustion observations of BOTH source stages. -/
theorem intrinsic_append_box_iff {C : Contract} {Γ Ξ Δ : Ctx}
    (P : Prog C Γ Ξ) (Q : Prog C Ξ Δ) (σ : State C Γ) (φ : Spec C Δ) :
    Spec.sat σ (.box (constructionAppend P Q) φ) ↔ Spec.sat σ (.box P (.box Q φ)) := by
  simp only [Spec.sat,intrinsic_append_run]
  cases P.run σ with
  | error e => rfl
  | ok o =>
    simp only [Except.bind,Except.map]
    cases Q.run o.st <;> rfl

/-- This preserves the genuine exhausted diamond, rather than calling it success. -/
theorem intrinsic_append_diamond_iff {C : Contract} {Γ Ξ Δ : Ctx}
    (P : Prog C Γ Ξ) (Q : Prog C Ξ Δ) (σ : State C Γ) (φ : Spec C Δ) :
    Spec.sat σ (.diamond (constructionAppend P Q) φ) ↔ Spec.sat σ (.diamond P (.diamond Q φ)) := by
  simp only [Spec.sat,intrinsic_append_run]
  cases P.run σ with
  | error e => rfl
  | ok o =>
    simp only [Except.bind,Except.map]
    cases Q.run o.st <;> rfl

end Solidity.Roadmap.V16
