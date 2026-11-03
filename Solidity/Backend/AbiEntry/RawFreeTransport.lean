import Solidity.Semantics.AbiEntry

/-! Ported from V13 85d13e5c7db386fd832391be5f7d04970ad31f22,
Backend/AbiWorld/RawFreeTransport. Proof structure and statements are retained; only unused simp arguments and
one inferred local type are normalized. The original
RawEntryTransport import was incidental; these declarations use only the
existing indexed semantic decoder. No codec/world modules are copied. -/

namespace Solidity.Backend.AbiEntry.RawFreeTransport
open Solidity.AbiEntry
/-- Existing word decoding performs no allocation, for every original fuel. -/
theorem word_free (data : List UInt8) (free free' f : Nat) (k : Kind) (base src a : Nat) :
    melem ⟨data,free⟩ f (.word k) base src a = melem ⟨data,free'⟩ f (.word k) base src a := by
  cases f with
  | zero => rfl
  | succ g => cases g <;> rfl

theorem cref_free (data : List UInt8) (free free' : Nat) (s : Solidity.AbiEntry.Shape) (head pos : Nat) :
    cref ⟨data,free⟩ s head pos = cref ⟨data,free'⟩ s head pos := by
  simp only [cref,Input.size]

/-- One actual calldata constructor, with the tail kept opaque. -/
theorem calldata_step (I : Input) (f : Nat) (shape : Solidity.AbiEntry.Shape) (ro : Bool)
    (ps : List Param) (pos a : Nat) :
    enter I f (⟨shape,.calldata,ro⟩ :: ps) pos a =
      match cref I shape 4 pos with
      | .error err => .error err
      | .ok (addr,len) => match enter I f ps (pos+shape.headSize) a with
        | .error err => .error err
        | .ok pair => .ok (.cons (.ref addr len) pair.1,pair.2) := by
  conv => lhs; rw [enter]
  cases hc : cref I shape 4 pos with
  | error err => simp only [bind,Except.bind]
  | ok pair =>
    obtain ⟨addr,len⟩ := pair
    simp only [bind,Except.bind,pure,Except.pure]
    cases ht : enter I f ps (pos+shape.headSize) a with
    | error err => rfl
    | ok pair => cases pair; rfl

theorem word_step (I : Input) (f : Nat) (k : Kind) (loc : Solidity.AbiEntry.Loc) (ro : Bool)
    (ps : List Param) (pos a : Nat) (hl : loc ≠ .calldata) :
    enter I f (⟨.word k,loc,ro⟩ :: ps) pos a =
      match melem I f (.word k) 4 (4+pos) a with
      | .error err => .error err
      | .ok (v,b) => match enter I f ps (pos+32) b with
        | .error err => .error err
        | .ok pair => .ok (.cons (.val v) pair.1,pair.2) := by
  cases loc with
  | calldata => exact False.elim (hl rfl)
  | value | memory =>
    conv => lhs; rw [enter]
    cases hm : melem I f (.word k) 4 (4+pos) a with
    | error err => simp only [bind,Except.bind]
    | ok pair =>
      obtain ⟨v,b⟩ := pair
      simp only [bind,Except.bind,pure,Except.pure,Shape.headSize]
      cases ht : enter I f ps (pos+32) b with
      | error err => rfl
      | ok pair => cases pair; rfl

/-- Raw entry success AND failure transport for all original fuel values.
The class condition is auxiliary: calldata entries or word-valued copies do
not allocate; body admission is a separate phase. -/
theorem enter_free (data : List UInt8) (free free' f : Nat) (ps : List Param) (pos a : Nat)
    (classes : ∀ p ∈ ps, p.loc = .calldata ∨ ∃ k, p.shape = .word k) :
    enter ⟨data,free⟩ f ps pos a = enter ⟨data,free'⟩ f ps pos a := by
  induction ps generalizing pos a with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨s,loc,ro⟩ := p
    have head : loc = .calldata ∨ ∃ k, s = .word k := classes _ List.mem_cons_self
    have tail : ∀ q ∈ ps, q.loc = .calldata ∨ ∃ k, q.shape = .word k :=
      fun q h => classes q (List.mem_cons_of_mem _ h)
    by_cases hl : loc = .calldata
    · subst loc
      rw [calldata_step,calldata_step,cref_free data free free' s 4 pos]
      cases hc : cref ⟨data,free'⟩ s 4 pos with
      | error err => rfl
      | ok pair => simp only [ih (pos+s.headSize) a tail]
    · have sk : ∃ k, s = .word k := by
        rcases head with bad | good
        · exact False.elim (hl bad)
        · exact good
      obtain ⟨k,rfl⟩ := sk
      rw [word_step _ _ _ _ _ _ _ _ hl,word_step _ _ _ _ _ _ _ _ hl,word_free data free free' f k 4 (4+pos) a]
      cases hm : melem ⟨data,free'⟩ f (.word k) 4 (4+pos) a with
      | error err => rfl
      | ok pair => simp only [ih (pos+32) pair.2 tail]

theorem entry_free (data : List UInt8) (free free' f : Nat) (ps : List Param)
    (classes : ∀ p ∈ ps, p.loc = .calldata ∨ ∃ k, p.shape = .word k) :
    entry ⟨data,free⟩ f ps = entry ⟨data,free'⟩ f ps := by
  simp only [entry,Input.size,enter_free data free free' f ps 0 0 classes]

/-- info: 'Solidity.Backend.AbiEntry.RawFreeTransport.word_free' does not depend on any axioms -/
#guard_msgs in #print axioms word_free
/-- info: 'Solidity.Backend.AbiEntry.RawFreeTransport.cref_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms cref_free
/-- info: 'Solidity.Backend.AbiEntry.RawFreeTransport.calldata_step' depends on axioms: [propext] -/
#guard_msgs in #print axioms calldata_step
/-- info: 'Solidity.Backend.AbiEntry.RawFreeTransport.word_step' depends on axioms: [propext] -/
#guard_msgs in #print axioms word_step
/-- info: 'Solidity.Backend.AbiEntry.RawFreeTransport.enter_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms enter_free
/-- info: 'Solidity.Backend.AbiEntry.RawFreeTransport.entry_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms entry_free
end Solidity.Backend.AbiEntry.RawFreeTransport
