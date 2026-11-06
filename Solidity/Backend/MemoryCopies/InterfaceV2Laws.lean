import Solidity.Backend.MemoryCopies.InterfaceV2

/-! Non-vacuity laws for V2. These use the concrete fitting input, never V1. -/
namespace Solidity.Backend.MemoryCopies.V2
open Solidity.Evm Solidity.Evm.Memory

theorem AllocatorWitness.cost_lt {cost : Nat} (w : AllocatorWitness cost) : cost < W := by
  have fits : w.cursor.val + cost < W := w.fits
  omega

theorem DefaultCertificate.cost_lt {R : RefTy} {hm : (Ty.ref R).mapFree = true}
    {cost : Nat} (c : DefaultCertificate R hm cost) : cost < W := c.feasible.cost_lt

theorem StorageWordCertificate.cost_lt {R : RefTy} {v : SVal (.ref R)}
    {hm : (Ty.ref R).mapFree = true} {cost : Nat}
    (c : StorageWordCertificate v hm cost) : cost < W := c.feasible.cost_lt

private theorem empty_code_impossible (m m' : Machine) (word : Word)
    (shape : m' = {m with mem := m'.mem})
    (execution : run [] m = .ok (m'.push word) 0) : False := by
  change Out.ok m 0 = Out.ok (m'.push word) 0 at execution
  have machines : m = m'.push word := (Out.ok.inj execution).1
  have stacks : m.stack = word :: m'.stack := congrArg Machine.stack machines
  have tail : m'.stack = m.stack := by
    simpa only [] using congrArg Machine.stack shape
  have lengths : m.stack.length = (word :: m'.stack).length := congrArg List.length stacks
  rw [tail] at lengths
  simp only [List.length_cons] at lengths
  omega

theorem DefaultCertificate.code_ne_nil {R : RefTy} {hm : (Ty.ref R).mapFree = true}
    {cost : Nat} (c : DefaultCertificate R hm cost) : c.builder.code ≠ [] := by
  intro empty
  obtain ⟨_base, m', execution, _, _, _, shape, _, _⟩ :=
    c.builder.correct c.feasible.heap c.feasible.base c.feasible.frame
      c.feasible.cursor c.feasible.machine c.feasible.represented c.feasible.fits
  rw [empty] at execution
  exact empty_code_impossible c.feasible.machine m' (.val c.feasible.cursor) shape execution

theorem StorageWordCertificate.code_ne_nil {R : RefTy} {v : SVal (.ref R)}
    {hm : (Ty.ref R).mapFree = true} {cost : Nat}
    (c : StorageWordCertificate v hm cost) : c.code ≠ [] := by
  intro empty
  obtain ⟨base', m', execution, _, _, shape, _⟩ :=
    c.correct c.feasible.heap c.feasible.base c.feasible.frame c.feasible.cursor
      c.feasible.machine c.feasible.represented c.feasible.fits
  rw [empty] at execution
  exact empty_code_impossible c.feasible.machine m' _ shape execution

theorem default_cost_W_impossible {R : RefTy} (hm : (Ty.ref R).mapFree = true) :
    ¬ Nonempty (DefaultCertificate R hm W) := by
  intro ⟨c⟩
  have bound : W < W := c.cost_lt
  exact (Nat.lt_irrefl W) bound

theorem word_cost_W_impossible {R : RefTy} (v : SVal (.ref R))
    (hm : (Ty.ref R).mapFree = true) : ¬ Nonempty (StorageWordCertificate v hm W) := by
  intro ⟨c⟩
  have bound : W < W := c.cost_lt
  exact (Nat.lt_irrefl W) bound

#print axioms AllocatorWitness.cost_lt
#print axioms DefaultCertificate.cost_lt
#print axioms StorageWordCertificate.cost_lt
#print axioms DefaultCertificate.code_ne_nil
#print axioms StorageWordCertificate.code_ne_nil
#print axioms default_cost_W_impossible
#print axioms word_cost_W_impossible
end Solidity.Backend.MemoryCopies.V2
