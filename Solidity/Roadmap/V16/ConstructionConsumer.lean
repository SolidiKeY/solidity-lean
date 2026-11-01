import Solidity.Evm.Compiler
import Solidity.Roadmap.V16.Specifications

/-!
Scoped consumers of the published object/reference-array-construction compiler certificate.
The actual Input retains state/frame/reached allocation obligations. ProgFrag.correct
has only represented success or exact empty revert; the public Agrees union is
not narrowed by assuming a desired target run. No byte-EVM/source-profile claim.
-/
namespace Solidity.Roadmap.V16
open Solidity.Evm

/-- The public resource selector keeps the actual construction cost. -/
theorem construction_allocation_cost {C : Contract} {b : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isConstruction = true) (σ : State C Γ) :
    compiled.allocationCost σ = Memory.Construction.allocationCostProg P σ := by
  cases compiled with
  | core _ _ => cases path
  | memory _ => cases path
  | referenceArrays _ => cases path
  | objects _ => cases path
  | construction _ => rfl
  | memoryLoops _ => cases path
  | memoryLoopScopes _ => cases path
  | memoryCalls _ _ => cases path

/-- The actual construction constructor supplies the stronger published relation. -/
theorem construction_result {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isConstruction = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} (input : compiled.Input L frame base σ m) :
    Memory.Objects.GrowingResult L b frame (compiled.allocationCost σ) compiled.frag σ base m
      (P.run σ) (run compiled.code m) := by
  cases compiled with
  | core _ _ => cases path
  | memory _ => cases path
  | referenceArrays _ => cases path
  | objects _ => cases path
  | construction out => exact out.cert.correct input.1 input.2.1 input.2.2
  | memoryLoops _ => cases path
  | memoryLoopScopes _ => cases path
  | memoryCalls _ _ => cases path

/-- Unpack the successful public representation without losing base extension
or the exact reached allocator cost. -/
theorem construction_rep_iff {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isConstruction = true) {σ : State C Γ} {τ : State C Δ}
    {base : Nat → Fin W} {m m' : Machine} :
    compiled.Rep L frame base σ m τ m' ↔
      ∃ base', Memory.Objects.StateRepr L b frame compiled.frag τ base' m' ∧
        Memory.BaseExtends σ.H base base' ∧
        Memory.Objects.GrowsAllocator b frame (compiled.allocationCost σ) σ base m τ base' m' := by
  cases compiled with
  | core _ _ => cases path
  | memory _ => cases path
  | referenceArrays _ => cases path
  | objects _ => cases path
  | construction _ => rfl
  | memoryLoops _ => cases path
  | memoryLoopScopes _ => cases path
  | memoryCalls _ _ => cases path

/-- Actual source success selects represented target success using soundness,
not the broader public Agrees payment/panic/divergence alternatives. -/
theorem construction_success {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isConstruction = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} {o : Solidity.Out C σ.H Δ}
    (input : compiled.Input L frame base σ m) (source : P.run σ = .ok o) :
    ∃ m' base', run compiled.code m = .ok m' 0 ∧ m'.stack = m.stack ∧
      Memory.Objects.StateRepr L b frame compiled.frag o.st base' m' ∧
      Memory.BaseExtends σ.H base base' ∧
      Memory.Objects.GrowsAllocator b frame (compiled.allocationCost σ) σ base m o.st base' m' := by
  rcases construction_result compiled path input with
    ⟨u, m', base', hs, ht, repr, stack, baseExtension, grows⟩ | ⟨hs, _⟩
  · have eq : u = o := Except.ok.inj (hs.symm.trans source)
    subst u
    exact ⟨m', base', ht, stack, repr, baseExtension, grows⟩
  · rw [source] at hs
    cases hs

/-- A source box at a real successful compiled construction gives a machine-side
represented specification witness, retaining its entire evaluation-stack tail. -/
theorem construction_spec {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isConstruction = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} {o : Solidity.Out C σ.H Δ} {φ : Spec C Δ}
    (input : compiled.Input L frame base σ m) (source : P.run σ = .ok o)
    (box : Spec.sat σ (.box P φ)) :
    ∃ m', run compiled.code m = .ok m' 0 ∧ m'.stack = m.stack ∧
      compiled.Rep L frame base σ m o.st m' ∧ Spec.sat o.st φ := by
  obtain ⟨m', base', ht, stack, repr, baseExtension, grows⟩ :=
    construction_success compiled path input source
  exact ⟨m', ht, stack, (construction_rep_iff compiled path).2
    ⟨base', repr, baseExtension, grows⟩, spec_box_post box source⟩

/-- On this actual certificate path, a source failure is precisely empty revert.
No panic, payload-bearing revert or divergence is silently collapsed into it. -/
theorem construction_failure {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isConstruction = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} {e : THalt} (input : compiled.Input L frame base σ m)
    (source : P.run σ = .error e) : e = .revert ∧ run compiled.code m = .revert := by
  rcases construction_result compiled path input with
    ⟨_, _, _, hs, _⟩ | ⟨hs, ht⟩
  · rw [source] at hs
    cases hs
  · rw [source] at hs
    exact ⟨Except.error.inj hs, ht⟩

/-- Source alias identity yields equality of actual complete-object pointer cells. -/
theorem construction_alias {C : Contract} {L b frame : Nat} {Γ : Ctx}
    {F : Frag Γ} {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : Memory.Objects.StateRepr L b frame F σ base m) {R : RefTy}
    (i j : Idx Γ (.mem R)) (r : HRef σ.H R)
    (left : TEnv.get i σ.env = some r) (right : TEnv.get j σ.env = some r) :
    m.mem (cellOf b i) = m.mem (cellOf b j) := by
  obtain ⟨ri, hi, mi⟩ := repr.pointers i
  obtain ⟨rj, hj, mj⟩ := repr.pointers j
  have ei : ri = r := Option.some.inj (hi.symm.trans left)
  have ej : rj = r := Option.some.inj (hj.symm.trans right)
  subst ri
  subst rj
  exact mi.trans mj.symm

/-- Required program frame size remains an actual admission obligation. -/
theorem construction_small_frame {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isConstruction = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} (small : frame < b + Memory.frameNeedProg P) :
    ¬ compiled.Input L frame base σ m := by
  intro input
  have bound := ((compiled.construction_input path L frame base σ m).1 input).2.1
  exact Nat.not_lt_of_ge bound small

/-- Actual reached allocator capacity yields its exact post-run cursor cell. -/
theorem construction_cursor {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isConstruction = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} {o : Solidity.Out C σ.H Δ}
    (input : compiled.Input L frame base σ m) (source : P.run σ = .ok o)
    (cursor : Fin W) (positive : 0 < b)
    (allocator : Memory.Objects.AllocatorRepr σ.heap base frame cursor m)
    (space : cursor.val + compiled.allocationCost σ < W) :
    ∃ m' base', run compiled.code m = .ok m' 0 ∧ m'.stack = m.stack ∧
      Memory.Objects.StateRepr L b frame compiled.frag o.st base' m' ∧
      Memory.BaseExtends σ.H base base' ∧
      Memory.Objects.AllocatorRepr o.st.heap base' frame
        ⟨cursor.val + compiled.allocationCost σ, space⟩ m' ∧
      m'.mem 0 = .val ⟨cursor.val + compiled.allocationCost σ, space⟩ := by
  obtain ⟨m', base', ht, stack, repr, baseExtension, grows⟩ :=
    construction_success compiled path input source
  have next := grows cursor positive allocator space
  exact ⟨m', base', ht, stack, repr, baseExtension, next, next.free.cell⟩

/-- The actual checked construction certificate excludes the existing exhausted
outcome. This is not an assumption about all source executions or diamonds. -/
theorem construction_not_exhausted {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isConstruction = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} (input : compiled.Input L frame base σ m) :
    P.run σ ≠ .error .exhausted := by
  intro exhausted
  have impossible := (construction_failure compiled path input exhausted).1
  cases impossible

/-- Reached AllocationInput supplies capacity at any actual represented entry
cursor. Cursor equality is obtained from its machine cell, not assumed. -/
theorem construction_capacity {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isConstruction = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} (input : compiled.Input L frame base σ m) (cursor : Fin W)
    (allocator : Memory.Objects.AllocatorRepr σ.heap base frame cursor m) :
    cursor.val + compiled.allocationCost σ < W := by
  rw [construction_allocation_cost compiled path]
  have capacity := ((compiled.construction_input path L frame base σ m).1 input).2.2
  rcases capacity with zero | ⟨_, other, represented, space⟩
  · rw [zero, Nat.add_zero]
    exact cursor.isLt
  · have eq : cursor = other := Evm.Word.val.inj
      (allocator.free.cell.symm.trans represented.free.cell)
    subst other
    exact space

/-- The unchanged approved diamond becomes genuine source AND target success on
this actual finite certificate path. No source-success/notExhausted/target-run
premise is supplied; the certificate discharges exhaustion. -/
theorem construction_diamond {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isConstruction = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} {φ : Spec C Δ} (input : compiled.Input L frame base σ m)
    (diamond : Spec.sat σ (.diamond P φ)) :
    ∃ o m' base', P.run σ = .ok o ∧ run compiled.code m = .ok m' 0 ∧
      m'.stack = m.stack ∧ Memory.Objects.StateRepr L b frame compiled.frag o.st base' m' ∧
      Memory.BaseExtends σ.H base base' ∧
      Memory.Objects.GrowsAllocator b frame (compiled.allocationCost σ) σ base m o.st base' m' ∧
      Spec.sat o.st φ := by
  obtain ⟨o, source, post⟩ := spec_diamond_success diamond
    (construction_not_exhausted compiled path input)
  obtain ⟨m', base', target, stack, repr, baseExtension, grows⟩ :=
    construction_success compiled path input source
  exact ⟨o, m', base', source, target, stack, repr, baseExtension, grows, post⟩

/-- Scoped equivalence with the full actual source/target/post witness. The
reverse direction uses only the existing successful diamond reading. -/
theorem construction_diamond_iff {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isConstruction = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} {φ : Spec C Δ} (input : compiled.Input L frame base σ m) :
    Spec.sat σ (.diamond P φ) ↔
    ∃ o m' base', P.run σ = .ok o ∧ run compiled.code m = .ok m' 0 ∧
      m'.stack = m.stack ∧ Memory.Objects.StateRepr L b frame compiled.frag o.st base' m' ∧
      Memory.BaseExtends σ.H base base' ∧
      Memory.Objects.GrowsAllocator b frame (compiled.allocationCost σ) σ base m o.st base' m' ∧
      Spec.sat o.st φ := by
  constructor
  · exact construction_diamond compiled path input
  · rintro ⟨o, _, _, source, _, _, _, _, _, post⟩
    simpa only [Spec.sat, source] using post

/-- Diamond transport also retains exact reached allocator observations. Capacity
is DERIVED from Input; only the actual entry allocator and positive frame base
are requested, with no desired source/target run premise. -/
theorem construction_diamond_cursor {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isConstruction = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} {φ : Spec C Δ} (input : compiled.Input L frame base σ m)
    (diamond : Spec.sat σ (.diamond P φ)) (cursor : Fin W) (positive : 0 < b)
    (allocator : Memory.Objects.AllocatorRepr σ.heap base frame cursor m) :
    ∃ o m' base', ∃ space : cursor.val + compiled.allocationCost σ < W,
      P.run σ = .ok o ∧ run compiled.code m = .ok m' 0 ∧ m'.stack = m.stack ∧
      Memory.Objects.StateRepr L b frame compiled.frag o.st base' m' ∧
      Memory.BaseExtends σ.H base base' ∧
      Memory.Objects.GrowsAllocator b frame (compiled.allocationCost σ) σ base m o.st base' m' ∧
      Spec.sat o.st φ ∧ Memory.Objects.AllocatorRepr o.st.heap base' frame
        ⟨cursor.val + compiled.allocationCost σ, space⟩ m' ∧
      m'.mem 0 = .val ⟨cursor.val + compiled.allocationCost σ, space⟩ := by
  obtain ⟨o, m', base', source, target, stack, repr, baseExtension, grows, post⟩ :=
    construction_diamond compiled path input diamond
  have space := construction_capacity compiled path input cursor allocator
  have next := grows cursor positive allocator space
  exact ⟨o, m', base', space, source, target, stack, repr, baseExtension, grows,
    post, next, next.free.cell⟩

/-- A box on this actual checked path supplies successful represented output
with its postcondition OR the exact genuine empty-revert alternative. Source
success is not a premise, and a reverting box does not supply a false post. -/
theorem construction_box {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isConstruction = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} {φ : Spec C Δ} (input : compiled.Input L frame base σ m)
    (box : Spec.sat σ (.box P φ)) :
    (∃ o m' base', P.run σ = .ok o ∧ run compiled.code m = .ok m' 0 ∧
      m'.stack = m.stack ∧ Memory.Objects.StateRepr L b frame compiled.frag o.st base' m' ∧
      Memory.BaseExtends σ.H base base' ∧
      Memory.Objects.GrowsAllocator b frame (compiled.allocationCost σ) σ base m o.st base' m' ∧
      Spec.sat o.st φ) ∨ (P.run σ = .error .revert ∧ run compiled.code m = .revert) := by
  rcases construction_result compiled path input with
    ⟨o, m', base', source, target, repr, stack, baseExtension, grows⟩ | ⟨source, target⟩
  · exact .inl ⟨o, m', base', source, target, stack, repr, baseExtension, grows,
      spec_box_post box source⟩
  · exact .inr ⟨source, target⟩

/-- Exact scoped box equivalence preserves both success/post and failure; it is
not a total-success assertion or a change to the approved box reading. -/
theorem construction_box_iff {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isConstruction = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} {φ : Spec C Δ} (input : compiled.Input L frame base σ m) :
    Spec.sat σ (.box P φ) ↔
    (∃ o m' base', P.run σ = .ok o ∧ run compiled.code m = .ok m' 0 ∧
      m'.stack = m.stack ∧ Memory.Objects.StateRepr L b frame compiled.frag o.st base' m' ∧
      Memory.BaseExtends σ.H base base' ∧
      Memory.Objects.GrowsAllocator b frame (compiled.allocationCost σ) σ base m o.st base' m' ∧
      Spec.sat o.st φ) ∨ (P.run σ = .error .revert ∧ run compiled.code m = .revert) := by
  constructor
  · exact construction_box compiled path input
  · rintro (⟨o, _, _, source, _, _, _, _, _, post⟩ | ⟨source, _⟩)
    · simpa only [Spec.sat, source] using post
    · simp only [Spec.sat, source, ne_eq, reduceCtorEq, not_false_eq_true]

/-- Box/diamond duality is valid on this actual two-outcome certificate path.
It is deliberately not asserted for arbitrary source execution (exhaustion and
panic in the approved general semantics would invalidate that inference). -/
theorem construction_box_diamond_dual {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isConstruction = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} {φ : Spec C Δ} (input : compiled.Input L frame base σ m) :
    Spec.sat σ (.box P φ) ↔ ¬ Spec.sat σ (.diamond P (.not φ)) := by
  classical
  rcases construction_result compiled path input with ⟨o, _, _, source, _⟩ | ⟨source, _⟩
  · simpa only [Spec.sat, source] using (Classical.not_not : ¬ ¬ Spec.sat o.st φ ↔ Spec.sat o.st φ).symm
  · simp only [Spec.sat, source, ne_eq, reduceCtorEq, not_false_eq_true, iff_self]

/-- Concatenate existing intrinsic typed programs; no new syntax or semantics. -/
def constructionAppend {C : Contract} {Γ Ξ Δ : Ctx} : Prog C Γ Ξ → Prog C Ξ Δ → Prog C Γ Δ
  | .nil,Q => Q
  | .cons stmt tail,Q => .cons stmt (constructionAppend tail Q)

/-- Compose actual published backend certificates, retaining their exact code.
This does not assert the public compiler's canonical output equals this code. -/
theorem construction_append_cert {C : Contract} {b : Nat} {Γ Ξ Δ : Ctx}
    {F : Frag Γ} {G : Frag Ξ} {K : Frag Δ} {P : Prog C Γ Ξ} {Q : Prog C Ξ Δ}
    {first second : List Instr} (head : Memory.Construction.ProgFrag b F G P first)
    (tail : Memory.Construction.ProgFrag b G K Q second) :
    Memory.Construction.ProgFrag b F K (constructionAppend P Q) (first ++ second) := by
  induction head with
  | nil F => simpa only [constructionAppend,List.nil_append] using tail
  | cons hs hp ih =>
    simpa only [constructionAppend,List.append_assoc] using
      (Memory.Construction.ProgFrag.cons hs (ih tail))

/-- An actual composition adapter over the producer's intrinsic CompiledProg. -/
def constructionAppendCompiled {C : Contract} {b : Nat} {Γ Ξ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Ξ} {Q : Prog C Ξ Δ}
    (head : Memory.Construction.CompiledProg b F P)
    (tail : Memory.Construction.CompiledProg b head.frag Q) :
    Memory.Construction.CompiledProg b F (constructionAppend P Q) :=
  ⟨tail.frag,head.code ++ tail.code,construction_append_cert head.cert tail.cert⟩

/-- Recover the actual construction certificate without evaluating code lists. -/
def constructionCertificate {C : Contract} {b : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isConstruction = true) : Memory.Construction.CompiledProg b F P :=
  match compiled with
  | .construction out => out
  | .core _ _ => False.elim (Bool.noConfusion path)
  | .memory _ => False.elim (Bool.noConfusion path)
  | .referenceArrays _ => False.elim (Bool.noConfusion path)
  | .objects _ => False.elim (Bool.noConfusion path)
  | .memoryLoops _ => False.elim (Bool.noConfusion path)
  | .memoryLoopScopes _ => False.elim (Bool.noConfusion path)
  | .memoryCalls _ _ => False.elim (Bool.noConfusion path)

theorem construction_reconstruct {C : Contract} {b : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isConstruction = true) :
    Compiler.Compilation.construction (constructionCertificate compiled path) = compiled := by
  cases compiled with
  | core _ _ => cases path
  | memory _ => cases path
  | referenceArrays _ => cases path
  | objects _ => cases path
  | construction _ => rfl
  | memoryLoops _ => cases path
  | memoryLoopScopes _ => cases path
  | memoryCalls _ _ => cases path

/-- The actual public constructor carries a certificate over its exact code. -/
theorem construction_public_cert {C : Contract} {b : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isConstruction = true) :
    Memory.Construction.ProgFrag b F compiled.frag P compiled.code := by
  cases compiled with
  | core _ _ => cases path
  | memory _ => cases path
  | referenceArrays _ => cases path
  | objects _ => cases path
  | construction out => exact out.cert
  | memoryLoops _ => cases path
  | memoryLoopScopes _ => cases path
  | memoryCalls _ _ => cases path

/-- Compose actual public compiler certificates with a checked fragment link.
No equality to the public compiler's canonical whole output is asserted. -/
def constructionCompose {C : Contract} {b : Nat} {Γ Ξ Δ : Ctx}
    {F : Frag Γ} {G : Frag Ξ} {P : Prog C Γ Ξ} {Q : Prog C Ξ Δ}
    (head : Compiler.Compilation b F P) (headPath : head.isConstruction = true)
    (tail : Compiler.Compilation b G Q) (tailPath : tail.isConstruction = true)
    (link : head.frag = G) : Memory.Construction.CompiledProg b F (constructionAppend P Q) where
  frag := tail.frag
  code := head.code ++ tail.code
  cert := by
    have first := construction_public_cert head headPath
    rw [link] at first
    exact construction_append_cert first (construction_public_cert tail tailPath)

end Solidity.Roadmap.V16
