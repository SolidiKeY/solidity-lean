import Solidity.Backend.Passes.HeapBoundaryControls
import Solidity.Backend.Passes.ValueCertificate

namespace Solidity.Backend.Passes.HeapObservations
open Evm Evm.Memory Evm.Compiler
open HeapBoundaryControls
open Backend.Passes.Controls.Fixture

def child : HRef first.st.H Child := ⟨0,by decide +kernel⟩
def defaultLeft : HRef first.st.H Child := ⟨1,by decide +kernel⟩
def defaultRight : HRef first.st.H Child := ⟨2,by decide +kernel⟩
def parent : HRef first.st.H Parent := ⟨3,by decide +kernel⟩

theorem source_objects :
    first.st.H = [Child,Child,Child,Parent] ∧
    first.st.heap.len child .dyn = 1 ∧
    first.st.heap.len defaultLeft .dyn = 0 ∧
    first.st.heap.len defaultRight .dyn = 0 ∧
    first.st.heap.len parent .dyn = 2 ∧
    (first.st.heap.get parent).val = [defaultLeft,defaultRight] := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals with_unfolding_all rfl

private theorem uint_word {v : PrimTy.uint.Denote} {word : Word} {n : Nat}
    (hv : v.val = (n : Int)) (hn : n < W) (h : ReprV .uint v word) :
    word = .val ⟨n,hn⟩ := by
  obtain ⟨a, rfl, ha⟩ := h
  have he : a.val = n := by omega
  exact congrArg Word.val (Fin.ext he)

def readExpression : Val C Locals .uint :=
  .readMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 0 rfl)))
def readCompiled : CompiledVal 1 mutation.frag readExpression :=
  (compileVal 1 _ readExpression).get (by decide +kernel)

theorem read_source : readExpression.evalT second.st = .ok (lenU 42 (by decide)) := by
  with_unfolding_all rfl
theorem observation_code : observation.code = readCompiled.code ++ [.mstore 3] := rfl

/-- Exact non-stack effect of the ACTUAL final compiled stage. Parent/reference
ownership must be carried across this local write, not inferred from legacy Rep. -/
theorem read_shape {selected : Nat → Fin W} {next : Machine}
    (input : StateRepr 1 1 8 mutation.frag second.st selected next) :
    run observation.code next = .ok (writeMachine next 3 w[42]) 0 := by
  obtain ⟨word, hw, ht⟩ := value_success_tail readCompiled input read_source next.stack
  have he : word = w[42] := uint_word rfl (by decide) hw
  subst word
  change run readCompiled.code next = .ok (next.push w[42]) 0 at ht
  rw [observation_code, run_append_ok ht]
  rfl

private theorem store_zero (m : Machine) (base : Fin W) (n : Nat) (w : Word)
    (hn : n < W) (positive : 0 < n) (space : base.val + 1 < W)
    (header : m.mem base.val = .val (wmod n)) :
    run writeArrayStackCode (((m.push w).push (.val base)).push w[0]) =
      .ok (writeMachine m (base.val + 1) w) 0 := by
  rw [writeArrayStackCode, arrayStack_append_eq (m.push w) base (⟨0,W_pos⟩ : Fin W) n hn header]
  have hc := arrayAddr_run (m.push w) base (⟨0,W_pos⟩ : Fin W) n hn header
  rw [if_pos positive] at hc
  rw [run_append_ok hc]
  simp only [run, Machine.push, exec_cons_zero, Instr.step, wmod_of_lt space,
    Out.ok_bind, exec_nil, writeMachine, Nat.add_zero]

theorem mutation_code : mutation.code =
    ([.mload 1, .mload 2, .push w[0]] ++ writeArrayStackCode) ++
    ([.push w[42], .mload 1, .push w[0]] ++ writeArrayStackCode) := rfl

/-- The two real emitted writes change only parent[0] and child[0]. -/
theorem mutation_shape {selected : Nat → Fin W} {mid : Machine}
    (input : Objects.StateRepr 1 1 8 allocation.frag first.st selected mid) :
    run mutation.code mid =
      .ok (writeMachine (writeMachine mid ((selected 3).val + 1) (.val (selected 0)))
        ((selected 0).val + 1) w[42]) 0 := by
  obtain ⟨r, hr, hc⟩ := input.pointers (.there .here)
  have he : TEnv.get (.there .here : Idx Locals (.mem Child)) first.st.env = some child := by with_unfolding_all rfl
  have er : r = child := Option.some.inj (hr.symm.trans he)
  subst r
  change mid.mem 1 = .val (selected 0) at hc
  obtain ⟨r, hr, hp⟩ := input.pointers (.here : Idx Locals (.mem Parent))
  have he : TEnv.get (.here : Idx Locals (.mem Parent)) first.st.env = some parent := by with_unfolding_all rfl
  have er : r = parent := Option.some.inj (hr.symm.trans he)
  subst r
  change mid.mem 2 = .val (selected 3) at hp
  have above := input.heap.owner.above parent
  change 8 ≤ (selected 3).val at above
  have ps := (input.heap.arrays .dyn parent).space
  have cs := (input.heap.arrays .dyn child).space
  have ph := (input.heap.arrays .dyn parent).length rfl
  have ch := (input.heap.arrays .dyn child).length rfl
  rw [source_objects.2.2.2.2.1] at ph
  change mid.mem (selected 3).val = w[2] at ph
  rw [source_objects.2.1] at ch
  change mid.mem (selected 0).val = w[1] at ch
  simp only [Objects.cells, source_objects.2.2.2.2.1] at ps
  change (selected 3).val + 3 ≤ W at ps
  simp only [Objects.cells, source_objects.2.1] at cs
  change (selected 0).val + 2 ≤ W at cs
  have hpre : run [.mload 1,.mload 2,.push w[0]] mid =
      .ok (((mid.push (.val (selected 0))).push (.val (selected 3))).push w[0]) 0 := by
    simp only [run, exec_cons_zero, Instr.step, Machine.next, Machine.push, hc, hp, Out.ok_bind, exec_nil]
  let changed := writeMachine mid ((selected 3).val + 1) (.val (selected 0))
  have hc' : changed.mem 1 = .val (selected 0) := by
    exact (upd_other _ _ (by omega)).trans hc
  have ch' : changed.mem (selected 0).val = w[1] := by
    have sep := input.heap.owner.separated parent child (by decide)
    simp only [Objects.cells, source_objects.2.2.2.2.1, source_objects.2.1] at sep
    change (selected 3).val + 3 ≤ (selected 0).val ∨
      (selected 0).val + 2 ≤ (selected 3).val at sep
    exact (upd_other _ _ (by rcases sep with h | h <;> omega)).trans ch
  have hpost : run [.push w[42],.mload 1,.push w[0]] changed =
      .ok (((changed.push w[42]).push (.val (selected 0))).push w[0]) 0 := by
    simp only [run, exec_cons_zero, Instr.step, Machine.next, Machine.push, hc', Out.ok_bind, exec_nil]
  have hfirst : run ([.mload 1,.mload 2,.push w[0]] ++ writeArrayStackCode) mid = .ok changed 0 := by
    rw [run_append_ok hpre]
    exact store_zero mid (selected 3) 2 (.val (selected 0)) (by decide) (by decide) (by omega) ph
  rw [mutation_code, run_append_ok hfirst]
  rw [run_append_ok hpost]
  exact store_zero changed (selected 0) 1 w[42] (by decide) (by decide) (by omega) ch'

/-- Complete cells: cursor, three locals, child header/value, BOTH default
children, parent header/BOTH links and the independent sentinel. -/
def addresses (selected : Nat → Fin W) : List Nat :=
  [0,1,2,3,16,17,(selected 1).val,(selected 2).val,18,19,20,15]
def expected (selected : Nat → Fin W) : List Word :=
  [w[23],w[16],w[18],w[42],w[1],w[42],w[0],w[0],w[2],w[16],.val (selected 2),w[99]]

theorem complete_observations {selected : Nat → Fin W} {mid : Machine}
    (input : Objects.StateRepr 1 1 8 allocation.frag first.st selected mid)
    (h0 : mid.mem 0 = w[23]) (h1 : mid.mem 1 = w[16])
    (h2 : mid.mem 2 = w[18]) (h15 : mid.mem 15 = w[99]) :
    let next := writeMachine (writeMachine mid ((selected 3).val + 1) (.val (selected 0)))
      ((selected 0).val + 1) w[42]
    let final := writeMachine next 3 w[42]
    (addresses selected).map final.mem = expected selected ∧ selected 1 ≠ selected 2 := by
  obtain ⟨r,hr,hc⟩ := input.pointers (.there .here)
  have er : r = child := Option.some.inj (hr.symm.trans (by with_unfolding_all rfl))
  subst r
  change mid.mem 1 = .val (selected 0) at hc
  have ec : selected 0 = ⟨16,by decide⟩ := Word.val.inj (hc.symm.trans h1)
  obtain ⟨r,hr,hp⟩ := input.pointers (.here : Idx Locals (.mem Parent))
  have er : r = parent := Option.some.inj (hr.symm.trans (by with_unfolding_all rfl))
  subst r
  change mid.mem 2 = .val (selected 3) at hp
  have ep : selected 3 = ⟨18,by decide⟩ := Word.val.inj (hp.symm.trans h2)
  have protect (r : HRef first.st.H Child) (empty : first.st.heap.len r .dyn = 0)
      (nc : r.id ≠ child.id) (np : r.id ≠ parent.id) :
      (selected r.id).val ≠ 3 ∧ (selected r.id).val ≠ 17 ∧ (selected r.id).val ≠ 19 := by
    have above := input.heap.owner.above r
    have sc := input.heap.owner.separated r child nc
    have sp := input.heap.owner.separated r parent np
    simp only [Objects.cells, empty, source_objects.2.1, source_objects.2.2.2.2.1] at sc sp
    change (selected r.id).val + 1 ≤ (selected 0).val ∨
      (selected 0).val + 2 ≤ (selected r.id).val at sc
    change (selected r.id).val + 1 ≤ (selected 3).val ∨
      (selected 3).val + 3 ≤ (selected r.id).val at sp
    rw [ec] at sc
    rw [ep] at sp
    change (selected r.id).val + 1 ≤ 16 ∨ 18 ≤ (selected r.id).val at sc
    change (selected r.id).val + 1 ≤ 18 ∨ 21 ≤ (selected r.id).val at sp
    rcases sc with h | h <;> rcases sp with k | k <;> omega
  have leftsafe := protect defaultLeft source_objects.2.2.1 (by decide) (by decide)
  have rightsafe := protect defaultRight source_objects.2.2.2.1 (by decide) (by decide)
  have hl := (input.heap.arrays .dyn defaultLeft).length rfl
  have hr := (input.heap.arrays .dyn defaultRight).length rfl
  have hh := (input.heap.arrays .dyn child).length rfl
  have ph := (input.heap.arrays .dyn parent).length rfl
  rw [source_objects.2.2.1] at hl
  rw [source_objects.2.2.2.1] at hr
  rw [source_objects.2.1] at hh
  rw [source_objects.2.2.2.2.1] at ph
  change mid.mem (selected 1).val = w[0] at hl
  change mid.mem (selected 2).val = w[0] at hr
  change mid.mem (selected 0).val = w[1] at hh
  change mid.mem (selected 3).val = w[2] at ph
  rw [ec] at hh
  rw [ep] at ph
  have p1 := (input.heap.arrays .dyn parent).elements 1 defaultRight
    (by rw [MObj.elems,source_objects.2.2.2.2.2]; rfl)
  change mid.mem ((selected 3).val + 1 + 1) = .val (selected 2) at p1
  rw [ep] at p1
  change mid.mem 20 = .val (selected 2) at p1
  let finish := writeMachine (writeMachine (writeMachine mid 19 w[16]) 17 w[42]) 3 w[42]
  have outside (addr : Nat) (a : addr ≠ 3) (b : addr ≠ 17) (c : addr ≠ 19) :
      finish.mem addr = mid.mem addr := by
    exact (upd_other _ _ a).trans ((upd_other _ _ b).trans (upd_other _ _ c))
  have fl := (outside (selected 1).val leftsafe.1 leftsafe.2.1 leftsafe.2.2).trans hl
  have fr := (outside (selected 2).val rightsafe.1 rightsafe.2.1 rightsafe.2.2).trans hr
  have f0 := (outside 0 (by decide) (by decide) (by decide)).trans h0
  have f1 := (outside 1 (by decide) (by decide) (by decide)).trans h1
  have f2 := (outside 2 (by decide) (by decide) (by decide)).trans h2
  have f16 := (outside 16 (by decide) (by decide) (by decide)).trans hh
  have f18 := (outside 18 (by decide) (by decide) (by decide)).trans ph
  have f20 := (outside 20 (by decide) (by decide) (by decide)).trans p1
  have f15 := (outside 15 (by decide) (by decide) (by decide)).trans h15
  have f3 : finish.mem 3 = w[42] := by rfl
  have f17 : finish.mem 17 = w[42] := by rfl
  have f19 : finish.mem 19 = w[16] := by rfl
  constructor
  · rw [ec,ep]
    change (addresses selected).map finish.mem = expected selected
    simp only [addresses,expected,List.map_cons,List.map_nil,f0,f1,f2,f3,f16,f17,fl,fr,f18,f19,f20,f15]
  · intro equal
    have sep := input.heap.owner.separated defaultLeft defaultRight (by decide)
    simp only [Objects.cells,source_objects.2.2.1,source_objects.2.2.2.1] at sep
    change (selected 1).val + 1 ≤ (selected 2).val ∨
      (selected 2).val + 1 ≤ (selected 1).val at sep
    rw [equal] at sep
    omega

end Solidity.Backend.Passes.HeapObservations
