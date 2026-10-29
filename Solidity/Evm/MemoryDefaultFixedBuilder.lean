import Solidity.Evm.MemoryDefaultParent

/-! Fixed reference defaults are built from typed child certificates. This is
structural on the finite type tree; no source type or heap representation changes. -/
namespace Solidity.Evm.Memory.Objects

def fixedDefaultPrefix (n : Nat) : List Instr :=
  allocateStructCode (max 1 n) ++ [.push (.val (wmod n)), .push (.val (wmod 0))]
def fixedDefaultCode (n : Nat) (childCode : List Instr) : List Instr :=
  fixedDefaultPrefix n ++ [.loop childrenCondition (defaultChildrenBody 0 childCode), .pop, .pop]

theorem fixedDefaultPrefix_run (m : Machine) (cursor : Fin W) (n : Nat)
    (hc : m.mem 0 = .val cursor) :
    run (fixedDefaultPrefix n) m =
      .ok (control (allocateStructMachine m cursor (max 1 n)) cursor (wmod n) (wmod 0)) 0 := by
  rw [fixedDefaultPrefix, run_append_ok (allocateStruct_run m cursor (max 1 n) hc)]
  rfl

/-- Every fixed element is the actual independently copied source default. -/
def DefaultBuilder.fixedReference {R : RefTy} {hm : (Ty.ref R).mapFree = true} {count : Nat}
    (child : DefaultBuilder R hm count) (n : Nat) :
    DefaultBuilder (.fixed (.ref R) n) hm (max 1 n + n * count) where
  code := fixedDefaultCode n child.code
  positive := by have hp : 1 ≤ max 1 n := Nat.le_max_left _ _; omega
  correct := by
    intro H hp base frame cursor m ha hs
    have hs₀ : cursor.val + max 1 n < W := by omega
    have hn : n < W := by
      have hn' : n ≤ max 1 n := Nat.le_max_right _ _
      omega
    have hnv : (wmod n).val = n := Nat.mod_eq_of_lt hn
    let start := allocateStructMachine m cursor (max 1 n)
    let cc : Fin W := ⟨cursor.val + max 1 n, hs₀⟩
    have hr := ha.reserveFixed n hs₀
    have hspan : cursor.val + 0 + (wmod n).val ≤ cursor.val + max 1 n := by
      rw [hnv, Nat.add_zero]
      exact Nat.add_le_add_left (Nat.le_max_right _ _) _
    obtain ⟨base₁, m', hloop, ha₁, hg₁, hb₁, helems, hstack, hprefix, hframe, hallgaps⟩ :=
      defaultChildren_sim child hp n base frame start cursor (wmod n) (wmod 0) cc 0
        (cursor.val + max 1 n) hr.1 hr.2 ha.free.above hspan (Nat.le_refl _)
        (by rw [hnv]; change 0 + n = n; omega) (by
          change cursor.val + max 1 n + n * count < W
          simpa only [Nat.add_assoc] using hs)
    let g := defaultChildrenCopy hp R hm n
    let o : MObj g.H' (.fixed (.ref R) n) := g.val
    let base' := upd base₁ g.H'.length cursor
    have haf : AllocatorRepr (referenceFixedCopy hp R hm n).heap base' frame
        ⟨cursor.val + (max 1 n + n * count), hs⟩ m' := by
      have hh := ha₁.adoptDefaultParent g .fixed o (by rw [MObj.elems_fixed]) ha.free.above (by
          intro Q q
          simpa only [header, Nat.zero_add] using hg₁ q)
        (by
          simp only [header, Nat.zero_add]
          change cursor.val + max 1 n ≤ cursor.val + max 1 n + n * count
          omega)
        (fun h => by cases h) (fun i v hv => by
          have he := helems i v hv
          simpa only [header, show (wmod 0).val = 0 from rfl, Nat.add_zero] using he)
      have heq : cc.val + n * count = cursor.val + (max 1 n + n * count) := by
        change cursor.val + max 1 n + n * count = cursor.val + (max 1 n + n * count)
        omega
      simpa only [heq] using hh
    rw [DefaultBuildResult, referenceFixedCopy_source hp R n hm]
    refine ⟨base', m', ?_, haf, upd_same _ _ _, ?_, ?_, ?_, ?_⟩
    · rw [fixedDefaultCode, run_append_ok (fixedDefaultPrefix_run m cursor n ha.free.cell),
        defaultLoop_exit hloop]
      rfl
    · exact BaseExtends.trans g.ext hb₁ (fun r => allocationBase_old base₁ cursor r)
    · calc
        m' = {start with mem := m'.mem} := hframe
        _ = {m with mem := m'.mem} := rfl
    · intro addr hz hl
      rw [hprefix addr hz (by simpa only [show (wmod 0).val = 0 from rfl, Nat.add_zero] using hl)]
      exact allocateStructMachine_other m cursor _ addr (by omega)
    · intro lo hi hg hh
      have hgap : Gap g.heap base₁ lo hi := hallgaps lo hi hg (by
        change hi ≤ cursor.val + max 1 n
        omega)
      intro Q q
      exact (Gap.adoptSingle hgap o cursor hh) q

end Solidity.Evm.Memory.Objects
