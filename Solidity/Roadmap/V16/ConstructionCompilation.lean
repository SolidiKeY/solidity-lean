import Solidity.Roadmap.V16.ConstructionConsumer

/-! Actual compilation-function algebra. These statements do not assume a
simulation and do not supply frontend/full-profile compilation coverage. -/
namespace Solidity.Roadmap.V16
open Solidity.Evm

theorem construction_compile_inversion {C : Contract} {b : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isConstruction = true)
    (accepted : Compiler.compile b F P = some compiled) :
    Memory.Construction.compileProg b F P = some (constructionCertificate compiled path) := by
  cases compiled with
  | core _ _ => cases path
  | memory _ => cases path
  | referenceArrays _ => cases path
  | objects _ => cases path
  | memoryLoops _ => cases path
  | memoryLoopScopes _ => cases path
  | memoryCalls _ _ => cases path
  | construction out =>
    change Memory.Construction.compileProg b F P = some out
    simp only [Compiler.compile,Option.map] at accepted
    repeat' (first | split at accepted | cases accepted)
    all_goals assumption

theorem construction_compile_append {C : Contract} {b : Nat} {Γ Ξ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Ξ} {Q : Prog C Ξ Δ}
    (head : Memory.Construction.CompiledProg b F P)
    (tail : Memory.Construction.CompiledProg b head.frag Q)
    (compiledHead : Memory.Construction.compileProg b F P = some head)
    (compiledTail : Memory.Construction.compileProg b head.frag Q = some tail) :
    ∃ out : Memory.Construction.CompiledProg b F (constructionAppend P Q),
      Memory.Construction.compileProg b F (constructionAppend P Q) = some out ∧
      out.frag = tail.frag ∧ out.code = head.code ++ tail.code := by
  revert head
  cases hSource : P with
  | nil =>
    intro head tail compiledHead compiledTail
    simp only [Memory.Construction.compileProg,Option.some.injEq] at compiledHead
    cases compiledHead
    exact ⟨tail,compiledTail,rfl,by simp only [List.nil_append]⟩
  | cons stmt rest =>
    intro head tail compiledHead compiledTail
    cases hs : Memory.Construction.compileStmt b F stmt with
    | none =>
      simp only [Memory.Construction.compileProg,hs,bind,Option.bind] at compiledHead
      cases compiledHead
    | some first =>
      cases hp : Memory.Construction.compileProg b first.frag rest with
      | none =>
        simp only [Memory.Construction.compileProg,hs,hp,bind,Option.bind] at compiledHead
        cases compiledHead
      | some second =>
        simp only [Memory.Construction.compileProg,hs,hp,bind,Option.bind,pure,
          Option.some.injEq] at compiledHead
        cases compiledHead
        obtain ⟨joined,hjoined,frag,code⟩ :=
          construction_compile_append (P := rest) second tail hp compiledTail
        let out : Memory.Construction.CompiledProg b F (constructionAppend (.cons stmt rest) Q) :=
          ⟨joined.frag,first.code ++ joined.code,.cons first.cert joined.cert⟩
        refine ⟨out,?_,frag,?_⟩
        · simp only [constructionAppend,Memory.Construction.compileProg,hs,hjoined,
            bind,Option.bind,pure,out]
        · simp only [out,code,List.append_assoc]

termination_by sizeOf P
decreasing_by
  all_goals subst P
  all_goals simp_wf
  all_goals omega

/-- Preserve source typing while observing only the actual output fragment/code;
this is an output projection, not another IR or execution semantics. -/
def constructionShape {C : Contract} (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) :
    Option (Frag Δ × List Instr) :=
  (Memory.Construction.compileProg b F P).map (fun out => (out.frag,out.code))

theorem construction_compile_append_link {C : Contract} {b : Nat} {Γ Ξ Δ : Ctx}
    {F : Frag Γ} {G : Frag Ξ} {P : Prog C Γ Ξ} {Q : Prog C Ξ Δ}
    (head : Memory.Construction.CompiledProg b F P)
    (tail : Memory.Construction.CompiledProg b G Q) (link : head.frag = G)
    (compiledHead : Memory.Construction.compileProg b F P = some head)
    (compiledTail : Memory.Construction.compileProg b G Q = some tail) :
    constructionShape b F (constructionAppend P Q) = some (tail.frag,head.code ++ tail.code) := by
  cases link
  obtain ⟨out,compiled,frag,code⟩ := construction_compile_append head tail compiledHead compiledTail
  simp only [constructionShape,compiled,Option.map_some,frag,code]

theorem construction_certificate_code {C : Contract} {b : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isConstruction = true) :
    (constructionCertificate compiled path).code = compiled.code :=
  congrArg Compiler.Compilation.code (construction_reconstruct compiled path)

theorem construction_certificate_fragment {C : Contract} {b : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isConstruction = true) :
    (constructionCertificate compiled path).frag = compiled.frag :=
  congrArg Compiler.Compilation.frag (construction_reconstruct compiled path)

/-- Canonical public-code composition follows from the ACTUAL compiler function
and actual success equations, not certificate uniqueness or assumed simulation. -/
theorem construction_public_append_code {C : Contract} {b : Nat} {Γ Ξ Δ : Ctx}
    {F : Frag Γ} {G : Frag Ξ} {P : Prog C Γ Ξ} {Q : Prog C Ξ Δ} {R : Prog C Γ Δ}
    (whole : Compiler.Compilation b F R) (wholePath : whole.isConstruction = true)
    (head : Compiler.Compilation b F P) (headPath : head.isConstruction = true)
    (tail : Compiler.Compilation b G Q) (tailPath : tail.isConstruction = true)
    (link : head.frag = G) (source : constructionAppend P Q = R)
    (compiledWhole : Compiler.compile b F R = some whole)
    (compiledHead : Compiler.compile b F P = some head)
    (compiledTail : Compiler.compile b G Q = some tail) :
    whole.code = head.code ++ tail.code ∧ whole.frag = tail.frag := by
  have lowHead := construction_compile_inversion head headPath compiledHead
  have lowTail := construction_compile_inversion tail tailPath compiledTail
  have lowWhole := construction_compile_inversion whole wholePath compiledWhole
  have fragment : (constructionCertificate head headPath).frag = G :=
    (construction_certificate_fragment head headPath).trans link
  have joined := construction_compile_append_link
    (constructionCertificate head headPath) (constructionCertificate tail tailPath)
    fragment lowHead lowTail
  rw [source] at joined
  have actual : constructionShape b F R = some
      ((constructionCertificate whole wholePath).frag,(constructionCertificate whole wholePath).code) := by
    simp only [constructionShape,lowWhole,Option.map_some]
  have eq := Option.some.inj (actual.symm.trans joined)
  constructor
  · simpa only [construction_certificate_code] using congrArg Prod.snd eq
  · simpa only [construction_certificate_fragment] using congrArg Prod.fst eq

end Solidity.Roadmap.V16
