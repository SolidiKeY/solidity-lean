import SolidityBridge.Evm
import EvmYul.UInt256
import EvmYul.EVM.PrimOps
import Cslib.Foundations.Semantics.LTS.Simulation

/-!
# Independent EVM word semantics

The reference operations and binary-operation transformer are imported
unchanged from EVMYulLean. This module relates numeric stack instructions of our
machine to those operations and to actual upstream transformer executions.
The CSLib simulation uses the projected arithmetic stack LTS.
Symbolic storage slots, gas, absolute jumps,
account addresses and calls require a different state relation and are
outside this word fragment. See `vendor/EvmYul/VENDOR.md` for the pin.
-/

namespace Solidity.Evm.External

theorem size_eq : EvmYul.UInt256.size = W := by decide

def encode (a : Fin W) : EvmYul.UInt256 :=
  ⟨⟨a.val, by simpa only [size_eq] using a.isLt⟩⟩

def decode (a : EvmYul.UInt256) : Fin W :=
  ⟨a.toNat, by simpa only [size_eq] using a.val.isLt⟩

theorem decode_encode (a : Fin W) : decode (encode a) = a := Fin.ext rfl

theorem encode_decode (a : EvmYul.UInt256) : encode (decode a) = a := by
  cases a
  rfl

theorem encode_add (a b : Fin W) :
    encode (wmod (a.val + b.val)) = EvmYul.UInt256.add (encode a) (encode b) := by
  apply congrArg EvmYul.UInt256.mk
  apply Fin.ext
  simp only [encode, wmod, Fin.val_add, size_eq]

theorem encode_sub (a b : Fin W) :
    encode (wmod (a.val + (W - b.val))) = EvmYul.UInt256.sub (encode a) (encode b) := by
  apply congrArg EvmYul.UInt256.mk
  apply Fin.ext
  change (a.val + (W - b.val)) % W =
    ((EvmYul.UInt256.size - b.val) + a.val) % EvmYul.UInt256.size
  rw [size_eq, Nat.add_comm]

theorem encode_mul (a b : Fin W) :
    encode (wmod (a.val * b.val)) = EvmYul.UInt256.mul (encode a) (encode b) := by
  apply congrArg EvmYul.UInt256.mk
  apply Fin.ext
  simp only [encode, wmod, Fin.val_mul, size_eq]

/-- Agreement of the actual stack step, with the first popped operand first. -/
theorem add_step (m : Machine) (a b : Fin W) (st : List Word) :
    Instr.add.step {m with stack := .val a :: .val b :: st} =
      m.next (.val (decode (EvmYul.UInt256.add (encode a) (encode b))) :: st) := by
  rw [← encode_add, decode_encode]
  rfl

theorem sub_step (m : Machine) (a b : Fin W) (st : List Word) :
    Instr.sub.step {m with stack := .val a :: .val b :: st} =
      m.next (.val (decode (EvmYul.UInt256.sub (encode a) (encode b))) :: st) := by
  rw [← encode_sub, decode_encode]
  rfl

theorem mul_step (m : Machine) (a b : Fin W) (st : List Word) :
    Instr.mul.step {m with stack := .val a :: .val b :: st} =
      m.next (.val (decode (EvmYul.UInt256.mul (encode a) (encode b))) :: st) := by
  rw [← encode_mul, decode_encode]
  rfl


theorem div_step (m : Machine) (a b : Fin W) (st : List Word) :
    Instr.div.step {m with stack := .val a :: .val b :: st} =
      m.next (.val (decode (EvmYul.UInt256.div (encode a) (encode b))) :: st) := by
  apply congrArg (fun v => m.next (.val v :: st))
  apply Fin.ext
  change (if b.val = 0 then 0 else a.val / b.val) = a.val / b.val
  split
  · rename_i h
    rw [h, Nat.div_zero]
  · rfl

theorem mod_step (m : Machine) (a b : Fin W) (st : List Word) :
    Instr.mod.step {m with stack := .val a :: .val b :: st} =
      m.next (.val (decode (EvmYul.UInt256.mod (encode a) (encode b))) :: st) := by
  by_cases hb : b.val = 0
  · simp only [Instr.step, decode, EvmYul.UInt256.mod, encode, EvmYul.UInt256.toNat,
      hb, Fin.isValue]
    rfl
  · apply congrArg (fun v => m.next (.val v :: st))
    apply Fin.ext
    simp only [hb, ↓reduceIte, decode, EvmYul.UInt256.toNat, EvmYul.UInt256.mod, encode,
      Fin.eta, Fin.isValue, beq_iff_eq, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.mod_val]


theorem and_step (m : Machine) (a b : Fin W) (st : List Word) :
    Instr.and.step {m with stack := .val a :: .val b :: st} =
      m.next (.val (decode (EvmYul.UInt256.land (encode a) (encode b))) :: st) := by
  apply congrArg (fun v => m.next (.val v :: st))
  apply Fin.ext
  change a.val &&& b.val = (a.val &&& b.val) % EvmYul.UInt256.size
  rw [size_eq]
  exact (Nat.mod_eq_of_lt (Nat.and_lt_two_pow a.val b.isLt)).symm

theorem or_step (m : Machine) (a b : Fin W) (st : List Word) :
    Instr.or.step {m with stack := .val a :: .val b :: st} =
      m.next (.val (decode (EvmYul.UInt256.lor (encode a) (encode b))) :: st) := by
  apply congrArg (fun v => m.next (.val v :: st))
  apply Fin.ext
  change a.val ||| b.val = (a.val ||| b.val) % EvmYul.UInt256.size
  rw [size_eq]
  exact (Nat.mod_eq_of_lt (Nat.or_lt_two_pow a.isLt b.isLt)).symm

theorem xor_step (m : Machine) (a b : Fin W) (st : List Word) :
    Instr.xor.step {m with stack := .val a :: .val b :: st} =
      m.next (.val (decode (EvmYul.UInt256.xor (encode a) (encode b))) :: st) := by
  apply congrArg (fun v => m.next (.val v :: st))
  apply Fin.ext
  change a.val ^^^ b.val = (a.val ^^^ b.val) % EvmYul.UInt256.size
  rw [size_eq]
  exact (Nat.mod_eq_of_lt (Nat.xor_lt_two_pow a.isLt b.isLt)).symm

/-- The independently implemented arithmetic fragment used below. -/
inductive Op where
  | add | sub | mul | div | mod | and | or | xor
  deriving DecidableEq, Repr

def Op.instr : Op → Instr
  | .add => .add | .sub => .sub | .mul => .mul
  | .div => .div | .mod => .mod | .and => .and | .or => .or | .xor => .xor

def Op.eval : Op → EvmYul.UInt256 → EvmYul.UInt256 → EvmYul.UInt256
  | .add => EvmYul.UInt256.add
  | .sub => EvmYul.UInt256.sub
  | .mul => EvmYul.UInt256.mul
  | .div => EvmYul.UInt256.div
  | .mod => EvmYul.UInt256.mod
  | .and => EvmYul.UInt256.land
  | .or => EvmYul.UInt256.lor
  | .xor => EvmYul.UInt256.xor

/-- The upstream interpreter's actual stack transformer, including its
program-counter update and stack-underflow result. -/
def Op.referenceStep (op : Op) : EvmYul.EVM.Transformer :=
  EvmYul.EVM.execBinOp op.eval

theorem reference_step (op : Op) (s : EvmYul.EVM.State) (a b : EvmYul.UInt256)
    (st : List EvmYul.UInt256) :
    op.referenceStep {s with stack := a :: b :: st} =
      .ok (s.replaceStackAndIncrPC (op.eval a b :: st)) := rfl

/-- The model's numeric instruction matches the actual upstream EVM
transformer on the shared stack observation; other upstream state is framed. -/
theorem reference_underflow (op : Op) (s : EvmYul.EVM.State)
    (h : s.stack.length < 2) : op.referenceStep s = .error .StackUnderflow := by
  cases hs : s.stack with
  | nil => simp only [Op.referenceStep, EvmYul.EVM.execBinOp, hs, EvmYul.Stack.pop2]
  | cons a st =>
    cases st with
    | nil => simp only [Op.referenceStep, EvmYul.EVM.execBinOp, hs, EvmYul.Stack.pop2]
    | cons b rest => simp only [hs, List.length_cons] at h; omega

structure RefCfg where
  code : List Op
  stack : List EvmYul.UInt256

/-- The reference machine uses upstream arithmetic and its own stack. -/
inductive RefTr : RefCfg → Op → RefCfg → Prop where
  | step {op : Op} {code : List Op} {a b : EvmYul.UInt256} {st : List EvmYul.UInt256} :
      RefTr ⟨op :: code, a :: b :: st⟩ op ⟨code, op.eval a b :: st⟩

def refLts : LTS RefCfg Op := ⟨RefTr⟩

/-- The disjoint union permits CSLib's standard same-carrier simulation
definition to compare the two machines. -/
inductive CombinedTr : RefCfg ⊕ Cfg → Op → RefCfg ⊕ Cfg → Prop where
  | reference {s t : RefCfg} {op : Op} (h : refLts.Tr s op t) :
      CombinedTr (.inl s) op (.inl t)
  | machine {s t : Cfg} {op : Op} (h : Evm.lts.Tr s (some op.instr) t) :
      CombinedTr (.inr s) op (.inr t)

def combined : LTS (RefCfg ⊕ Cfg) Op := ⟨CombinedTr⟩

def Represents : RefCfg ⊕ Cfg → RefCfg ⊕ Cfg → Prop
  | .inl s, .inr t => t.code = s.code.map Op.instr ∧ t.skip = 0 ∧
      t.m.stack = s.stack.map (fun a => Word.val (decode a))
  | _, _ => False

theorem op_step (op : Op) (m : Machine) (a b : EvmYul.UInt256) (st : List Word) :
    op.instr.step {m with stack := .val (decode a) :: .val (decode b) :: st} =
      m.next (.val (decode (op.eval a b)) :: st) := by
  cases op <;> simp only [Op.instr, Op.eval, add_step, sub_step, mul_step, div_step, mod_step, and_step, or_step, xor_step, encode_decode]

/-- A CSLib simulation from the external arithmetic machine to our
instruction LTS, for arbitrary code and stack, not just test vectors. -/
theorem simulation : Simulation combined Represents := by
  intro s t h op s' hs
  cases s with
  | inr s => cases h
  | inl s =>
    cases t with
    | inl t => cases h
    | inr t =>
      rcases h with ⟨hc, hk, hst⟩
      cases hs with
      | reference hs =>
        cases hs with
        | @step op code a b st =>
          let m' := {t.m with stack := .val (decode (op.eval a b)) :: st.map (fun a => .val (decode a))}
          refine ⟨.inr ⟨code.map Op.instr, 0, m'⟩, .machine ?_, rfl, rfl, rfl⟩
          cases t with
          | mk c k m =>
            dsimp only at hc hk hst ⊢
            subst c
            subst k
            apply Tr.step
            have he := op_step op m a b (st.map (fun a => .val (decode a)))
            simp only [List.map_cons] at hst
            rw [← hst] at he
            exact he

/-- Agreement with an actual upstream EVM execution, framing its remaining
state. The reference step is not an adapter-defined stack evaluator. -/
theorem upstream_step (op : Op) (m : Machine) (s s' : EvmYul.EVM.State)
    (hst : m.stack = s.stack.map (fun a => .val (decode a)))
    (hr : op.referenceStep s = .ok s') :
    ∃ m', op.instr.step m = .ok m' 0 ∧
      m'.stack = s'.stack.map (fun a => .val (decode a)) := by
  cases hs : s.stack with
  | nil =>
    have hf := reference_underflow op s (by simp only [hs, List.length_nil]; omega)
    rw [hr] at hf
    cases hf
  | cons a rest =>
    cases rest with
    | nil =>
      have hf := reference_underflow op s (by simp only [hs, List.length_cons, List.length_nil]; omega)
      rw [hr] at hf
      cases hf
    | cons b st =>
      have href := reference_step op s a b st
      have heq : {s with stack := a :: b :: st} = s := by rw [← hs]
      rw [heq, hr] at href
      have hout := Except.ok.inj href
      subst s'
      let m' := {m with stack := .val (decode (op.eval a b)) :: st.map (fun a => .val (decode a))}
      refine ⟨m', ?_, rfl⟩
      have he := op_step op m a b (st.map (fun a => .val (decode a)))
      simp only [hs, List.map_cons] at hst
      rw [← hst] at he
      exact he

end Solidity.Evm.External
