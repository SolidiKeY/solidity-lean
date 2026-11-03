import Solidity.Backend.Passes.PreservedAllocatorControls

namespace Solidity.Backend.Passes.PreservedAllocatorObservations
open Evm Evm.Memory Evm.Compiler
open HeapBoundaryControls
open PreservedAllocatorControls
open Backend.Passes.Controls.Fixture (C)

def oldChild : HRef suffixOut.st.H Child := ⟨0,by decide +kernel⟩
def orphan : HRef suffixOut.st.H Child := ⟨1,by decide +kernel⟩
def retained : HRef suffixOut.st.H Child := ⟨2,by decide +kernel⟩
def parent : HRef suffixOut.st.H Parent := ⟨3,by decide +kernel⟩
def fresh : HRef suffixOut.st.H Child := ⟨4,by decide +kernel⟩

theorem source_heap :
    suffixOut.st.H = [Child,Child,Child,Parent,Child] ∧
    suffixOut.st.heap.len oldChild .dyn = 1 ∧
    suffixOut.st.heap.len orphan .dyn = 0 ∧
    suffixOut.st.heap.len retained .dyn = 0 ∧
    suffixOut.st.heap.len parent .dyn = 2 ∧
    suffixOut.st.heap.len fresh .dyn = 1 := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals with_unfolding_all rfl

theorem old_contents : (suffixOut.st.heap.get oldChild).val = [lenU 42 (by decide)] := by
  with_unfolding_all rfl
theorem parent_contents : (suffixOut.st.heap.get parent).val = [oldChild,retained] := by
  with_unfolding_all rfl
theorem fresh_contents : (suffixOut.st.heap.get fresh).val = [lenU 0 (by decide)] := by
  with_unfolding_all rfl

def freshMachine (next : Machine) : Machine :=
  writeMachine (allocateMachine next ⟨23,by decide⟩ ⟨1,by decide⟩) 3 w[23]

theorem suffix_code : suffixCode.code =
    declareNewCode (C := C) (Γ := Locals) 1 (.lit 1 rfl) := rfl

theorem suffix_shape {selected : Nat → Fin W} {next : Machine}
    (input : Objects.StateRepr 1 1 8 objectCode.frag second.st selected next)
    (allocator : Objects.AllocatorRepr second.st.heap selected 8 ⟨23,by decide⟩ next) :
    run suffixCode.code next = .ok (freshMachine next) 0 := by
  rw [suffix_code]
  exact (Objects.primitiveDeclare_correct input allocator (by decide) .uint (.lit 1 rfl) rfl
    (⟨1,by decide⟩ : Fin W) rfl (by decide) (by decide)).2.1

private theorem uint_word {v : PrimTy.uint.Denote} {word : Word} {n : Nat}
    (hv : v.val = (n : Int)) (hn : n < W) (h : ReprV .uint v word) :
    word = .val ⟨n,hn⟩ := by
  obtain ⟨a,rfl,ha⟩ := h
  have he : a.val = n := by omega
  exact congrArg Word.val (Fin.ext he)

def addresses (selected : Nat → Fin W) : List Nat :=
  [0,1,2,3,16,17,(selected 1).val,(selected 2).val,18,19,20,15,23,24]
def expected (selected : Nat → Fin W) : List Word :=
  [w[25],w[16],w[18],w[23],w[1],w[42],w[0],w[0],w[2],w[16],.val (selected 2),w[99],w[1],w[0]]

/-- Full reached ownership plus ACTUAL local/cursor/sentinel words determines
all fourteen cells, including every old object and the new child. -/
theorem complete {selected : Nat → Fin W} {final : Machine}
    (input : Objects.StateRepr 1 1 8 suffixCode.frag suffixOut.st selected final)
    (h0 : final.mem 0 = w[25]) (h1 : final.mem 1 = w[16]) (h2 : final.mem 2 = w[18])
    (h3 : final.mem 3 = w[23]) (h15 : final.mem 15 = w[99]) :
    (addresses selected).map final.mem = expected selected ∧ selected 1 ≠ selected 2 := by
  obtain ⟨r,hr,hc⟩ := input.pointers (.there (.there .here))
  have er : r = oldChild := Option.some.inj (hr.symm.trans (by with_unfolding_all rfl))
  subst r
  change final.mem 1 = .val (selected 0) at hc
  have ec : selected 0 = ⟨16,by decide⟩ := Word.val.inj (hc.symm.trans h1)
  obtain ⟨r,hr,hp⟩ := input.pointers (.there .here : Idx (.mem Child :: Locals) (.mem Parent))
  have er : r = parent := Option.some.inj (hr.symm.trans (by with_unfolding_all rfl))
  subst r
  change final.mem 2 = .val (selected 3) at hp
  have ep : selected 3 = ⟨18,by decide⟩ := Word.val.inj (hp.symm.trans h2)
  obtain ⟨r,hr,hn⟩ := input.pointers (.here : Idx (.mem Child :: Locals) (.mem Child))
  have er : r = fresh := Option.some.inj (hr.symm.trans (by with_unfolding_all rfl))
  subst r
  change final.mem 3 = .val (selected 4) at hn
  have en : selected 4 = ⟨23,by decide⟩ := Word.val.inj (hn.symm.trans h3)
  have hc := (input.heap.arrays .dyn oldChild).length rfl
  have hl := (input.heap.arrays .dyn orphan).length rfl
  have hr := (input.heap.arrays .dyn retained).length rfl
  have hp := (input.heap.arrays .dyn parent).length rfl
  have hn := (input.heap.arrays .dyn fresh).length rfl
  rw [source_heap.2.1] at hc
  rw [source_heap.2.2.1] at hl
  rw [source_heap.2.2.2.1] at hr
  rw [source_heap.2.2.2.2.1] at hp
  rw [source_heap.2.2.2.2.2] at hn
  change final.mem (selected 0).val = w[1] at hc
  rw [ec] at hc
  change final.mem (selected 1).val = w[0] at hl
  change final.mem (selected 2).val = w[0] at hr
  change final.mem (selected 3).val = w[2] at hp
  rw [ep] at hp
  change final.mem (selected 4).val = w[1] at hn
  rw [en] at hn
  have cv := (input.heap.arrays .dyn oldChild).elements 0 (lenU 42 (by decide))
    (by rw [MObj.elems,old_contents]; rfl)
  have nv := (input.heap.arrays .dyn fresh).elements 0 (lenU 0 (by decide))
    (by rw [MObj.elems,fresh_contents]; rfl)
  change ReprV .uint (lenU 42 (by decide)) (final.mem ((selected 0).val + 1 + 0)) at cv
  change ReprV .uint (lenU 0 (by decide)) (final.mem ((selected 4).val + 1 + 0)) at nv
  rw [ec] at cv
  rw [en] at nv
  have c42 : final.mem 17 = w[42] := uint_word rfl (by decide) cv
  have n0 : final.mem 24 = w[0] := uint_word rfl (by decide) nv
  have p0 := (input.heap.arrays .dyn parent).elements 0 oldChild
    (by rw [MObj.elems,parent_contents]; rfl)
  have p1 := (input.heap.arrays .dyn parent).elements 1 retained
    (by rw [MObj.elems,parent_contents]; rfl)
  change final.mem ((selected 3).val + 1 + 0) = .val (selected 0) at p0
  change final.mem ((selected 3).val + 1 + 1) = .val (selected 2) at p1
  rw [ep,ec] at p0
  rw [ep] at p1
  change final.mem 19 = w[16] at p0
  change final.mem 20 = .val (selected 2) at p1
  constructor
  · simp only [addresses,expected,List.map_cons,List.map_nil,h0,h1,h2,h3,h15,hc,hl,hr,hp,hn,c42,n0,p0,p1]
  · intro same
    have sep := input.heap.owner.separated orphan retained (by decide)
    simp only [Objects.cells,source_heap.2.2.1,source_heap.2.2.2.1] at sep
    change (selected 1).val + 1 ≤ (selected 2).val ∨
      (selected 2).val + 1 ≤ (selected 1).val at sep
    rw [same] at sep
    omega

end Solidity.Backend.Passes.PreservedAllocatorObservations
