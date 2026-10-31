import Solidity.Backend.AbiWorld.ReturnedBytes

/-! Finite inhabited compiler applications of the arbitrary-length observer.
The entry to every call stage is produced by actual compiled setup execution.
These controls do not supply external/world or byte-addressed emission semantics. -/
namespace Solidity.Backend.AbiWorld.ReturnedBytesControls
open Evm Evm.Memory ReturnedBytes
theorem source_get {α : Type} (r : TRes α) (h : r.toOption.isSome = true) :
    r = .ok (r.toOption.get h) := by
  cases r with
  | ok a => rfl
  | error e => cases h

def C : Contract := { vars := [("saved", .prim .uint)] }
def initial : State C [] := State.init C
def bases : Nat → Fin W := fun _ => wmod 0
def machine : Machine :=
  {Machine.init with stack := [w[77]], mem := fun a =>
    if a = 0 then w[256] else if a = 127 then w[99] else w[0]}
theorem noRef {R : RefTy} (r : HRef [] R) : False := by cases r.get?
theorem initial_repr : StateRepr 1 1 128 (Frag.init []) initial bases machine ∧
    StructAllocatorRepr initial.heap bases 128 (wmod 256) machine := by
  have hh : HeapRepr initial.heap bases 128 machine :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hs : StructHeapRepr initial.heap bases 128 machine :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hx : StructArraySeparated initial.heap bases := fun _ r => (noRef r).elim
  have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl
  refine ⟨⟨?_, hh, ?_, by decide, hs, hx, ?_⟩,
    ⟨⟨hh, ?_, fun r => (noRef r).elim⟩, hs, hx, fun r => (noRef r).elim⟩⟩
  · refine ⟨hc.store, ?_, ?_, hc.net, hc.netSelf, hc.bound, ?_, hc.env, hc.funds, hc.oracle⟩
    · intro p i; nomatch i
    · intro R i hi; nomatch i
    · intro R i hi; nomatch i
  · intro R i; nomatch i
  · intro s f R r hf; exact (noRef r).elim
  · refine ⟨by decide, by decide, rfl, ?_⟩
    intro a ha
    change 256 ≤ a at ha
    simp only [machine]
    split <;> rename_i he
    · omega
    · split <;> rename_i he
      · omega
      · rfl

def u {Γ : Ctx} (n : Nat) (h : n < 2 ^ 256 := by decide +kernel) : Val C Γ .uint :=
  .simple (.lit n (PrimTy.inRange_uint_of_lt h))
abbrev Entry : Ctx := [.mem bytesR, .val .uint]
abbrev Output : Ctx := [.mem bytesR, .mem bytesR, .mem bytesR, .val .uint]
def setup : Prog C [] Entry :=
  .cons (.assign (.root "saved" rfl) (.val (u 9)))
  (.cons (.declLocal .uint (.user "marker") (some (u 42)))
  (litBytes (.user "older") [161, 178] .nil))
def prefixCert : Calls.Program 1 (Frag.init []) setup :=
  (Calls.compile 1 (Frag.init []) setup).get (by decide +kernel)
def entry : Solidity.Out C [] Entry :=
  ((setup.run initial).toOption).get (by decide +kernel)
attribute [irreducible] prefixCert entry
theorem prefix_run : setup.run initial = .ok entry  := by
  unfold entry
  exact source_get _ (by decide +kernel)
def oldRef : HRef entry.st.H bytesR := ⟨0, by decide +kernel⟩

/-- Keep the exact producer cost in the cursor type; its numeral is proved
separately, avoiding normalization of dependent allocator proof fields. -/
def prefixCursor : Fin W := ⟨(wmod 256).val + prefixCert.cost initial, by decide +kernel⟩
attribute [irreducible] prefixCursor

theorem prefix_resources : prefixCert.cost initial = 3 ∧ prefixCursor.val = 259 := by decide +kernel

/-- An ACTUAL setup run supplies a populated caller and allocator, not an
assumed nonempty state representation. -/
theorem prefix_ready : ∃ m base,
    Evm.run prefixCert.code machine = .ok m 0 ∧
    StateRepr 1 1 128 prefixCert.frag entry.st base m ∧
    StructAllocatorRepr entry.st.heap base 128 prefixCursor m ∧ m.stack = machine.stack := by
  have hi : AllocationInput 1 128 (prefixCert.cost initial) initial bases machine :=
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩
  rcases prefixCert.sound initial_repr.1 (by decide +kernel) hi with
    ⟨o, m, base, ho, ht, hr, hk, hb, hg⟩ | ⟨ho, ht⟩
  · rw [prefix_run] at ho
    cases ho
    have ha' : StructAllocatorRepr entry.st.heap base 128 prefixCursor m := by
      unfold prefixCursor
      exact hg (wmod 256) (by decide) initial_repr.2 (by decide +kernel)
    exact ⟨m, base, ht, hr, ha', hk⟩
  · rw [prefix_run] at ho; cases ho

def prefixMachine : Machine :=
  match Evm.run prefixCert.code machine with | .ok m _ => m | _ => machine
theorem nonempty_entry : ∃ base,
    Evm.run prefixCert.code machine = .ok prefixMachine 0 ∧
    StateRepr 1 1 128 prefixCert.frag entry.st base prefixMachine ∧
    StructAllocatorRepr entry.st.heap base 128 prefixCursor prefixMachine ∧
    prefixMachine.stack = machine.stack := by
  obtain ⟨m, base, ht, hs, ha, hk⟩ := prefix_ready
  have he : prefixMachine = m := by rw [prefixMachine, ht]
  rw [he]
  exact ⟨base, ht, hs, ha, hk⟩

/-- info: 'Solidity.Backend.AbiWorld.ReturnedBytesControls.prefix_resources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_resources
/-- info: 'Solidity.Backend.AbiWorld.ReturnedBytesControls.prefix_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_ready
/-- info: 'Solidity.Backend.AbiWorld.ReturnedBytesControls.nonempty_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonempty_entry

end Solidity.Backend.AbiWorld.ReturnedBytesControls
