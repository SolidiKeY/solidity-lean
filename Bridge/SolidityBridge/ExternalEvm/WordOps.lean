import SolidityBridge.ExternalEvm
import EvmYul.Semantics

namespace Solidity.Evm.External

theorem decode_bool (b : Bool) : decode (Bool.toUInt256 b) = bword b := by
  cases b <;> rfl

theorem lt_step (m : Machine) (a b : Fin W) (st : List Word) :
    Instr.lt.step {m with stack := .val a :: .val b :: st} =
      m.next (.val (decode (EvmYul.UInt256.lt (encode a) (encode b))) :: st) := by
  change m.next (.val (bword (decide (a.val < b.val))) :: st) = _
  rw [EvmYul.UInt256.lt, decode_bool]
  congr 3

theorem gt_step (m : Machine) (a b : Fin W) (st : List Word) :
    Instr.gt.step {m with stack := .val a :: .val b :: st} =
      m.next (.val (decode (EvmYul.UInt256.gt (encode a) (encode b))) :: st) := by
  change m.next (.val (bword (decide (b.val < a.val))) :: st) = _
  rw [EvmYul.UInt256.gt, decode_bool]
  congr 3

theorem eq_step (m : Machine) (a b : Fin W) (st : List Word) :
    Instr.eq.step {m with stack := .val a :: .val b :: st} =
      m.next (.val (decode (EvmYul.UInt256.eq (encode a) (encode b))) :: st) := by
  change m.next (.val (bword (decide (a.val = b.val))) :: st) = _
  rw [EvmYul.UInt256.eq, decode_bool]
  have h : encode a = encode b ↔ a.val = b.val := by
    constructor
    · intro he
      exact congrArg (fun x : EvmYul.UInt256 => x.toNat) he
    · intro he
      exact congrArg encode (Fin.ext he)
  simp only [h]

theorem iszero_step (m : Machine) (a : Fin W) (st : List Word) :
    Instr.iszero.step {m with stack := .val a :: st} =
      m.next (.val (decode (EvmYul.UInt256.isZero (encode a))) :: st) := by
  change m.next (.val (bword (decide (a.val = 0))) :: st) = _
  rw [EvmYul.UInt256.isZero, decode_bool]
  apply congrArg (fun z => m.next (.val (bword z) :: st))
  simp only [EvmYul.UInt256.eq0, EvmYul.instBEqUInt256, EvmYul.instBEqUInt256.beq, encode]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, beq_iff_eq, Fin.ext_iff]
  rfl

theorem not_step (m : Machine) (a : Fin W) (st : List Word) :
    Instr.not.step {m with stack := .val a :: st} =
      m.next (.val (decode (EvmYul.UInt256.lnot (encode a))) :: st) := by
  have hmax : EvmYul.UInt256.ofNat (EvmYul.UInt256.size - 1) = encode wMax := by
    apply congrArg EvmYul.UInt256.mk
    apply Fin.ext
    change (EvmYul.UInt256.size - 1) % EvmYul.UInt256.size = W - 1
    rw [size_eq, Nat.mod_eq_of_lt (by have := W_pos; omega)]
  unfold EvmYul.UInt256.lnot
  rw [hmax]
  change m.next (.val ⟨W - 1 - a.val, _⟩ :: st) =
    m.next (.val (decode (EvmYul.UInt256.sub (encode wMax) (encode a))) :: st)
  rw [← encode_sub, decode_encode]
  apply congrArg (fun v => m.next (.val v :: st))
  apply Fin.ext
  change W - 1 - a.val = (W - 1 + (W - a.val)) % W
  have he : W - 1 + (W - a.val) = (W - 1 - a.val) + W := by omega
  rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := W_pos; omega)]

theorem shl_step (m : Machine) (n a : Fin W) (st : List Word) :
    Instr.shl.step {m with stack := .val n :: .val a :: st} =
      m.next (.val (decode (EvmYul.UInt256.shiftLeft (encode a) (encode n))) :: st) := by
  apply congrArg (fun v => m.next (.val v :: st))
  unfold EvmYul.UInt256.shiftLeft
  by_cases hn : n.val < 256
  · have hr : ¬ (encode n).val ≥ 256 := by change ¬ n.val ≥ 256; omega
    rw [if_neg hr, if_pos hn]
    apply Fin.ext
    change (a.val * 2 ^ n.val) % W =
      (a.val <<< n.val) % EvmYul.UInt256.size
    rw [size_eq, Nat.shiftLeft_eq]
  · have hr : (encode n).val ≥ 256 := by change n.val ≥ 256; omega
    rw [if_pos hr, if_neg hn]
    rfl

theorem shr_step (m : Machine) (n a : Fin W) (st : List Word) :
    Instr.shr.step {m with stack := .val n :: .val a :: st} =
      m.next (.val (decode (EvmYul.UInt256.shiftRight (encode a) (encode n))) :: st) := by
  apply congrArg (fun v => m.next (.val v :: st))
  unfold EvmYul.UInt256.shiftRight
  by_cases hn : n.val < 256
  · have hr : ¬ (encode n).val ≥ 256 := by change ¬ n.val ≥ 256; omega
    rw [if_neg hr, if_pos hn]
    apply Fin.ext
    change a.val / 2 ^ n.val =
      (a.val >>> n.val) % EvmYul.UInt256.size
    rw [Nat.shiftRight_eq_div_pow, size_eq,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt)]
  · have hr : (encode n).val ≥ 256 := by change n.val ≥ 256; omega
    rw [if_pos hr, if_neg hn]
    rfl

end Solidity.Evm.External
