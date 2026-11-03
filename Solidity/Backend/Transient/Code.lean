import Solidity.Backend.Transient.TypedSource

/-! Concrete numeric transient code against the independent local target run.
The existing Backend PUSH immediate and Osaka opcodes are emitted unchanged. -/
namespace Solidity.Backend.Transient

def pushWord (word : Word) : Backend.Instr :=
  .push ⟨32,by decide⟩ (toBytesBE 32 word.val)

theorem push_exact (a : Roadmap.Address) (static : Bool) (s : State) (w : Word) :
    step a static (pushWord w) s=.ok {s with machine := s.machine.push (.val w)} := by
  have bound : w.val<256^32 := by change w.val<2^256; exact w.isLt
  simp only [pushWord,step,ofBytesBE_toBytesBE 32 w.val bound,Evm.wmod_of_lt w.isLt]
  rfl

def storeCode (key value : Word) : List Backend.Instr :=
  [pushWord value,pushWord key,.op .TSTORE]
def loadCode (key : Word) : List Backend.Instr := [pushWord key,.op .TLOAD]

theorem store_code (a : Roadmap.Address) (s : State) (k v : Word) :
    run a false (storeCode k v) s=.ok (write s a k v) := by
  simp only [storeCode,run,push_exact]
  simp only [step,Evm.Machine.push,Bool.false_eq_true,↓reduceIte]
  rfl

theorem load_code (a : Roadmap.Address) (static : Bool) (s : State) (k : Word) :
    run a static (loadCode k) s=
      .ok {s with machine := s.machine.push (.val (s.bank a k))} := by
  simp only [loadCode,run,push_exact]
  simp only [step,Evm.Machine.push]

/-- Actual compiled selected write and full Source result, arbitrary Source and
existing target machine/journal. No successful run is supplied as a premise. -/
theorem compiled_write {E : Source.Env} {Γ : Source.RCtx} (slot : BoolSlot E)
    (F : Source.Fr) (normal : F.static=false) (b : Bool) (s : Source.EMState E Γ) (t : State) :
    (Source.writeAt F slot.path (.bool b)).run s=(.ok (),(s.1,sourceWrite slot F.this b s.2)) ∧
    run F.this false (storeCode slot.key (boolWord b)) t=.ok (write t F.this slot.key (boolWord b)) ∧
    Represents slot F.this (s.1,sourceWrite slot F.this b s.2) (write t F.this slot.key (boolWord b)) :=
  ⟨write_actual slot F normal b s,store_code F.this t _ _,write_represents slot F.this b s t⟩

theorem run_append (a : Roadmap.Address) (static : Bool) (first second : List Backend.Instr)
    (s : State) : run a static (first++second) s=
      match run a static first s with
      | .ok next => run a static second next
      | .error why dirty => .error why dirty := by
  induction first generalizing s with
  | nil => rfl
  | cons i first ih =>
    simp only [List.cons_append,run]
    cases step a static i s with
    | ok next => exact ih next
    | error why dirty => rfl

end Solidity.Backend.Transient
