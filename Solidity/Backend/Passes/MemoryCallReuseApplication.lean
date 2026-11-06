import Solidity.Backend.Passes.MemoryCallReuse

/-! Reached budgets through two actual memory calls and a subsequent allocation.
No selected map is replaced between the independent physical links. -/
namespace Solidity.Backend.Passes.MemoryCallReuseApplication
open Evm Evm.Memory Evm.Compiler MemoryCallControls MemoryCallReuse

def beginning : Compilation 1 (Frag.init []) prefixProgram := .memoryCalls leading prefix_free

theorem budget : AllocationInput 1 128 12 initial base machine :=
  .inr ⟨by decide,wmod 256,initial_repr.2,by decide +kernel⟩

theorem input : beginning.Input 1 128 base initial machine :=
  ⟨initial_repr.1,frames.1,budget.of_le (by rw [MemoryCallReuse.costs.1]; decide)⟩

/-- Concrete nonallocating right CALL producer, not merely a legacy memory pass. -/
theorem scalar_entry : MappedBoundaryLink beginning (.memoryCalls scalar free.1)
    1 128 base initial machine :=
  memoryCalls_nonallocating_link leading prefix_free scalar free.1
    frames.2.1 MemoryCallReuse.costs.2.2.2.2

/-- The initial capacity12 supplies8+the ACTUAL reached right call cost. -/
theorem entry {Ξ : Ctx} {Q : Prog C After Ξ}
    (right : Calls.Program 1 leading.frag Q) (rightFree : Evm.Prog.pushes Q = 0)
    (capacity : 1 + right.need ≤ 128) (bound : right.cost before.st ≤ 2) :
    MappedBoundaryLink beginning (.memoryCalls right rightFree) 1 128 base initial machine := by
  apply memoryCalls_budgeted_link leading prefix_free right rightFree capacity
  intro o hs
  have same : before = o := Except.ok.inj (prefix_source.symm.trans hs)
  subst o
  exact budget.of_le (by rw [MemoryCallReuse.costs.1]; omega)

/-- Prefix growth transports the remaining call+allocation budget to its actual
map; the right call's own growth then supplies the final allocating Input. -/
theorem following {Ξ Ω : Ctx} {Q : Prog C After Ξ} {R : Prog C Ξ Ω}
    (right : Calls.Program 1 leading.frag Q) (rightFree : Evm.Prog.pushes Q = 0)
    (last : CompiledProg 1 right.frag R) (capacity : 1 + frameNeedProg R ≤ 128)
    (bound : right.cost before.st ≤ 2) (lastCost : ∀ σ, last.cert.cost σ = 2) :
    ReachedMappedLink beginning (.memoryCalls right rightFree) (.memory last)
      1 128 base initial machine := by
  intro o mid selected hs _ output
  apply memoryCalls_budgeted_memory_link right rightFree last capacity
  intro u hu
  have same : before = o := Except.ok.inj (prefix_source.symm.trans hs)
  subst o
  exact output.2.2.nextInput (budget.of_le (by rw [MemoryCallReuse.costs.1,lastCost]; omega))

/-- All four already allocated objects, including the escaped returned object,
keep identity across the second call and final allocation. Total growth is8+k+2. -/
theorem resources {Ξ Ω : Ctx} {Q : Prog C After Ξ} {R : Prog C Ξ Ω}
    (right : Calls.Program 1 leading.frag Q) (rightFree : Evm.Prog.pushes Q = 0)
    (last : CompiledProg 1 right.frag R) {tail : List Word}
    {mb nb ob : Nat → Fin W} {mid next out : Machine}
    {u : Solidity.Out C before.st.H Ξ} {v : Solidity.Out C u.st.H Ω}
    (ha : MappedOutput beginning 1 128 base initial {machine with stack := tail} before.st mid mb)
    (hb : MappedOutput (.memoryCalls right rightFree) 1 128 mb before.st mid u.st next nb)
    (hc : MappedOutput (.memory last) 1 128 nb u.st next v.st out ob)
    (lastCost : ∀ σ, last.cert.cost σ = 2) :
    BaseExtends before.st.H mb nb ∧ BaseExtends before.st.H mb ob ∧
    GrowsAllocator 1 128 (8 + right.cost before.st + 2) initial base
      {machine with stack := tail} v.st ob out := by
  refine ⟨hb.2.1,Memory.BaseExtends.trans u.ext hb.2.1 hc.2.1,?_⟩
  have h := ha.2.2.comp (hb.2.2.comp hc.2.2)
  simpa only [MemoryCallReuse.costs.1,lastCost,Nat.add_assoc] using h

theorem scalar_joined :
    ((prefixProgram.join scalarCall).join (fresh After)).run initial =
      .ok ⟨scalarFinal.st,(before.ext.trans scalarOut.ext).trans scalarFinal.ext⟩ ∧
    (prefixProgram.join (scalarCall.join (fresh After))).run initial =
      .ok ⟨scalarFinal.st,before.ext.trans (scalarOut.ext.trans scalarFinal.ext)⟩ :=
  triple_source_success initial prefix_source scalar_source scalar_final

theorem scalar_shared : ∃ (mb nb ob : Nat → Fin W) (mid next out : Machine),
    mid.stack = [] ∧ next.stack = [] ∧ out.stack = [] ∧ ∀ tail,
    run leading.code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
    run scalar.code {mid with stack := tail} = .ok {next with stack := tail} 0 ∧
    run scalarFresh.code {next with stack := tail} = .ok {out with stack := tail} 0 ∧
    run ((leading.code ++ scalar.code) ++ scalarFresh.code) {machine with stack := tail} =
      .ok {out with stack := tail} 0 ∧
    run (leading.code ++ (scalar.code ++ scalarFresh.code)) {machine with stack := tail} =
      .ok {out with stack := tail} 0 ∧
    MappedOutput beginning 1 128 base initial {machine with stack := tail}
      before.st {mid with stack := tail} mb ∧
    MappedOutput (.memoryCalls scalar free.1) 1 128 mb before.st {mid with stack := tail}
      scalarOut.st {next with stack := tail} nb ∧
    MappedOutput (.memory scalarFresh) 1 128 nb scalarOut.st {next with stack := tail}
      scalarFinal.st {out with stack := tail} ob := by
  have rightEntry := scalar_entry
  have rightFollowing := following scalar free.1 scalarFresh frames.2.2.2.2.2.1
    (by decide +kernel) scalar_fresh_cost
  simpa only [prefix_free,free.1,show Evm.Prog.pushes (fresh After) = 0 by decide +kernel,
    Nat.add_zero] using
    compilation_triple_shared beginning (.memoryCalls scalar free.1) (.memory scalarFresh)
      input rfl rightEntry rightFollowing (by decide +kernel) (by decide +kernel) (by decide +kernel)
      prefix_source scalar_source scalar_final

theorem alias_joined :
    ((prefixProgram.join aliasCall).join (fresh AliasContext)).run initial =
      .ok ⟨aliasFinal.st,(before.ext.trans aliasOut.ext).trans aliasFinal.ext⟩ ∧
    (prefixProgram.join (aliasCall.join (fresh AliasContext))).run initial =
      .ok ⟨aliasFinal.st,before.ext.trans (aliasOut.ext.trans aliasFinal.ext)⟩ :=
  triple_source_success initial prefix_source alias_source alias_final

theorem alias_shared : ∃ (mb nb ob : Nat → Fin W) (mid next out : Machine),
    mid.stack = [] ∧ next.stack = [] ∧ out.stack = [] ∧ ∀ tail,
    run leading.code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
    run alias.code {mid with stack := tail} = .ok {next with stack := tail} 0 ∧
    run aliasFresh.code {next with stack := tail} = .ok {out with stack := tail} 0 ∧
    run ((leading.code ++ alias.code) ++ aliasFresh.code) {machine with stack := tail} =
      .ok {out with stack := tail} 0 ∧
    run (leading.code ++ (alias.code ++ aliasFresh.code)) {machine with stack := tail} =
      .ok {out with stack := tail} 0 ∧
    MappedOutput beginning 1 128 base initial {machine with stack := tail}
      before.st {mid with stack := tail} mb ∧
    MappedOutput (.memoryCalls alias free.2.1) 1 128 mb before.st {mid with stack := tail}
      aliasOut.st {next with stack := tail} nb ∧
    MappedOutput (.memory aliasFresh) 1 128 nb aliasOut.st {next with stack := tail}
      aliasFinal.st {out with stack := tail} ob := by
  have rightEntry := entry alias free.2.1 frames.2.2.1 (by decide +kernel)
  have rightFollowing := following alias free.2.1 aliasFresh frames.2.2.2.2.2.2
    (by decide +kernel) alias_fresh_cost
  simpa only [prefix_free,free.2.1,show Evm.Prog.pushes (fresh AliasContext) = 0 by decide +kernel,
    Nat.add_zero] using
    compilation_triple_shared beginning (.memoryCalls alias free.2.1) (.memory aliasFresh)
      input rfl rightEntry rightFollowing (by decide +kernel) (by decide +kernel) (by decide +kernel)
      prefix_source alias_source alias_final

theorem void_joined :
    ((prefixProgram.join voidCall).join (fresh After)).run initial =
      .ok ⟨voidFinal.st,(before.ext.trans voidOut.ext).trans voidFinal.ext⟩ ∧
    (prefixProgram.join (voidCall.join (fresh After))).run initial =
      .ok ⟨voidFinal.st,before.ext.trans (voidOut.ext.trans voidFinal.ext)⟩ :=
  triple_source_success initial prefix_source void_source void_final

theorem void_shared : ∃ (mb nb ob : Nat → Fin W) (mid next out : Machine),
    mid.stack = [] ∧ next.stack = [] ∧ out.stack = [] ∧ ∀ tail,
    run leading.code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
    run void.code {mid with stack := tail} = .ok {next with stack := tail} 0 ∧
    run voidFresh.code {next with stack := tail} = .ok {out with stack := tail} 0 ∧
    run ((leading.code ++ void.code) ++ voidFresh.code) {machine with stack := tail} =
      .ok {out with stack := tail} 0 ∧
    run (leading.code ++ (void.code ++ voidFresh.code)) {machine with stack := tail} =
      .ok {out with stack := tail} 0 ∧
    MappedOutput beginning 1 128 base initial {machine with stack := tail}
      before.st {mid with stack := tail} mb ∧
    MappedOutput (.memoryCalls void free.2.2.1) 1 128 mb before.st {mid with stack := tail}
      voidOut.st {next with stack := tail} nb ∧
    MappedOutput (.memory voidFresh) 1 128 nb voidOut.st {next with stack := tail}
      voidFinal.st {out with stack := tail} ob := by
  have rightEntry := entry void free.2.2.1 frames.2.2.2.1 (by decide +kernel)
  have rightFollowing := following void free.2.2.1 voidFresh frames.2.2.2.2.2.1
    (by decide +kernel) void_fresh_cost
  simpa only [prefix_free,free.2.2.1,show Evm.Prog.pushes (fresh After) = 0 by decide +kernel,
    Nat.add_zero] using
    compilation_triple_shared beginning (.memoryCalls void free.2.2.1) (.memory voidFresh)
      input rfl rightEntry rightFollowing (by decide +kernel) (by decide +kernel) (by decide +kernel)
      prefix_source void_source void_final

theorem scalar_resources {tail : List Word} {mb nb ob : Nat → Fin W} {mid next out : Machine}
    (ha : MappedOutput beginning 1 128 base initial {machine with stack := tail} before.st mid mb)
    (hb : MappedOutput (.memoryCalls scalar free.1) 1 128 mb before.st mid scalarOut.st next nb)
    (hc : MappedOutput (.memory scalarFresh) 1 128 nb scalarOut.st next scalarFinal.st out ob) :
    BaseExtends before.st.H mb nb ∧ BaseExtends before.st.H mb ob ∧
    GrowsAllocator 1 128 10 initial base {machine with stack := tail} scalarFinal.st ob out := by
  simpa only [MemoryCallReuse.costs.2.1] using resources scalar free.1 scalarFresh ha hb hc scalar_fresh_cost

theorem alias_resources {tail : List Word} {mb nb ob : Nat → Fin W} {mid next out : Machine}
    (ha : MappedOutput beginning 1 128 base initial {machine with stack := tail} before.st mid mb)
    (hb : MappedOutput (.memoryCalls alias free.2.1) 1 128 mb before.st mid aliasOut.st next nb)
    (hc : MappedOutput (.memory aliasFresh) 1 128 nb aliasOut.st next aliasFinal.st out ob) :
    BaseExtends before.st.H mb nb ∧ BaseExtends before.st.H mb ob ∧
    GrowsAllocator 1 128 11 initial base {machine with stack := tail} aliasFinal.st ob out := by
  simpa only [MemoryCallReuse.costs.2.2.1] using resources alias free.2.1 aliasFresh ha hb hc alias_fresh_cost

theorem void_resources {tail : List Word} {mb nb ob : Nat → Fin W} {mid next out : Machine}
    (ha : MappedOutput beginning 1 128 base initial {machine with stack := tail} before.st mid mb)
    (hb : MappedOutput (.memoryCalls void free.2.2.1) 1 128 mb before.st mid voidOut.st next nb)
    (hc : MappedOutput (.memory voidFresh) 1 128 nb voidOut.st next voidFinal.st out ob) :
    BaseExtends before.st.H mb nb ∧ BaseExtends before.st.H mb ob ∧
    GrowsAllocator 1 128 12 initial base {machine with stack := tail} voidFinal.st ob out := by
  simpa only [MemoryCallReuse.costs.2.2.2.1] using resources void free.2.2.1 voidFresh ha hb hc void_fresh_cost

end Solidity.Backend.Passes.MemoryCallReuseApplication
