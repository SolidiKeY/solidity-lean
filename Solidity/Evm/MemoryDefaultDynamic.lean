import Solidity.Evm.MemoryDefaultFixedBuilder
import Solidity.Evm.MemoryObjectNested

/-! Runtime-length reference arrays of any certified nonrecursive child default. -/
namespace Solidity.Evm.Memory.Objects

def referenceArrayCode (childCode : List Instr) : List Instr :=
  nestedPrefix ++ [.loop childrenCondition (defaultChildrenBody 1 childCode), .pop, .pop]

theorem referenceArray_correct {R : RefTy} {hm : (Ty.ref R).mapFree = true} {count : Nat}
    (child : DefaultBuilder R hm count) {H : HTy} (hp : Heap H) (size : Fin W)
    (base : Nat → Fin W) (frame : Nat) (m : Machine) (cursor : Fin W)
    (ha : AllocatorRepr hp base frame cursor m)
    (hs : cursor.val + (size.val + 1 + size.val * count) < W) :
    let g := referenceArrayCopy hp R hm size
    ∃ base' m', run (referenceArrayCode child.code) (m.push (.val size)) = .ok (m'.push (.val cursor)) 0 ∧
      AllocatorRepr g.heap base' frame ⟨cursor.val + (size.val + 1 + size.val * count), hs⟩ m' ∧
      base' g.val.id = cursor ∧ BaseExtends H base base' ∧
      m' = {m with mem := m'.mem} ∧
      (∀ addr, 0 < addr → addr < cursor.val → m'.mem addr = m.mem addr) ∧
      (∀ lo hi, Gap hp base lo hi → hi ≤ cursor.val → Gap g.heap base' lo hi) := by
  have hs₀ : cursor.val + size.val + 1 < W := by omega
  let start := allocateMachine m cursor size
  let cc : Fin W := ⟨cursor.val + size.val + 1, hs₀⟩
  have hr := ha.reserveArray size hs₀
  obtain ⟨base₁, m', hloop, ha₁, hg₁, hb₁, helems, hstack, hprefix, hframe, hallgaps⟩ :=
    defaultChildren_sim child hp size.val base frame start cursor size (wmod 0) cc 1
      (cursor.val + size.val + 1) hr.1 hr.2 ha.free.above (by omega) (Nat.le_refl _)
      (by change 0 + size.val = size.val; omega) (by
        change cursor.val + size.val + 1 + size.val * count < W
        simpa only [Nat.add_assoc] using hs)
  let g := defaultChildrenCopy hp R hm size.val
  let o : MObj g.H' (.array (.ref R)) := ⟨g.val.1, by rw [g.val.2]; exact size.isLt⟩
  let base' := upd base₁ g.H'.length cursor
  have hz : 0 < cursor.val := Nat.lt_of_lt_of_le ha.free.reserved ha.free.above
  have haf : AllocatorRepr (referenceArrayCopy hp R hm size).heap base' frame
      ⟨cursor.val + (size.val + 1 + size.val * count), hs⟩ m' := by
    have hh := ha₁.adoptDefaultParent g .dyn o (by rw [MObj.elems_dyn]) ha.free.above
      (by
        intro Q q
        have he : max 1 (1 + size.val) = size.val + 1 := by omega
        simpa only [header, he] using hg₁ q)
      (by
        have he : max 1 (1 + size.val) = size.val + 1 := by omega
        simp only [header, he]
        change cursor.val + (size.val + 1) ≤ cursor.val + size.val + 1 + size.val * count
        omega)
      (fun _ => by
        rw [hprefix _ hz (by change cursor.val < cursor.val + 1 + 0; omega)]
        exact (allocateMachine_header m cursor size (by omega)).trans
          (congrArg Word.val (Fin.ext (Nat.mod_eq_of_lt size.isLt).symm)))
      (fun i v hv => by
        have he := helems i v hv
        simpa only [header, show (wmod 0).val = 0 from rfl, Nat.add_zero] using he)
    have heq : cc.val + size.val * count = cursor.val + (size.val + 1 + size.val * count) := by
      change cursor.val + size.val + 1 + size.val * count = cursor.val + (size.val + 1 + size.val * count)
      omega
    simpa only [heq] using hh
  refine ⟨base', m', ?_, haf, upd_same _ _ _, ?_, ?_, ?_, ?_⟩
  · rw [referenceArrayCode, run_append_ok (nestedPrefix_run m cursor size ha.free.cell),
      defaultLoop_exit hloop]
    rfl
  · exact BaseExtends.trans g.ext hb₁ (fun r => allocationBase_old base₁ cursor r)
  · calc
      m' = {start with mem := m'.mem} := hframe
      _ = {m with mem := m'.mem} := rfl
  · intro addr hz' hl
    rw [hprefix addr hz' (by change addr < cursor.val + 1 + 0; omega)]
    exact allocateMachine_other m cursor size addr (by omega) (by omega)
  · intro lo hi hg hh
    have hgap : Gap g.heap base₁ lo hi := hallgaps lo hi hg (by
      change hi ≤ cursor.val + size.val + 1
      omega)
    intro Q q
    exact (Gap.adoptSingle hgap o cursor hh) q

end Solidity.Evm.Memory.Objects
