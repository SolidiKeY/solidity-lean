import Solidity.Evm.SimLemmas
import Solidity.Backend.Scalar.SignedShift

/-! # Machine SAR and the Scalar signed right shift

`Evm.Instr.sar` is the memory machine's `SAR`. `Evm.sTail .shr`
(`Evm.sarCode`) emits it after clamping a negative count to `0`, as the
Scalar endpoint `Backend.Scalar.intShr` does: the source reads a negative
`int` count by its `toNat`, `0`, where raw `SAR` would read its unsigned
word and saturate. The machine lemmas (`Evm.sarCode_run`, `Evm.sar_tail`,
`Evm.sarWord_clamp`) live in `Evm/Signed.lean`, and `binInFrag .shr .int`
is `true`: `Evm.tail_simT`, and so the memory compiler's theorem, covers
`int >> int`.

`shr_int_inFrag` records the admission; `sarCode_simT` is the fragment
theorem at `.shr`/`int` (never a revert);
`machine_agrees_intShr` relates the machine word to the Scalar endpoint's
word for every intrinsic operand pair. `raw_sar_differs` is the negative
control: unclamped `SAR` disagrees with the source at count `-1`;
`saturated_fill` is a positive witness at count `256`. -/

namespace Solidity.Backend.Passes.MachineSar
open Solidity.Evm

theorem int_range (v : PrimTy.int.Denote) : -(H : Int) ≤ v.1 ∧ v.1 < H := by
  have := v.2; simpa only [PrimTy.inRange, decide_eq_true_eq] using this

/-- The source evaluates `a >> n` at `int` to `sarShr`, never reverting. -/
theorem evalT_shr (a n : PrimTy.int.Denote) :
    BinOp.shr.evalT rfl a n = some ⟨sarShr a.1 n.1, by
      simp only [PrimTy.inRange, decide_eq_true_eq]
      exact sarShr_range n.1 (int_range a)⟩ :=
  dif_pos (by simp only [PrimTy.inRange, decide_eq_true_eq]
              exact sarShr_range n.1 (int_range a))

/-- Signed right shift is in the memory compiler's fragment at `int`. -/
theorem shr_int_inFrag : binInFrag .shr .int = true := rfl

/-- **Typed agreement at `int`**: the fragment theorem `Evm.tail_simT` at
`.shr`, on any words representing the operands. -/
theorem sarCode_simT {a b : PrimTy.int.Denote} {wa wb : Word} (ha : ReprV .int a wa)
    (hb : ReprV .int b wb) (m : Machine) :
    ValOutT (BinOp.shr.ret .int) (TRes.ofOpt (BinOp.shr.evalT rfl a b))
      (run (binTail .int .shr) { m with stack := wb :: wa :: m.stack }) m :=
  tail_simT shr_int_inFrag (by decide) (by decide) rfl ha hb m

/-- The Scalar word of an intrinsic `int` is its two's complement machine word. -/
theorem encode_int_word (v : PrimTy.int.Denote) :
    (Scalar.encodeValue .int v).toNat = (sword v.1).1 := by
  have hr := int_range v
  have hW := W_eq
  have hl : toWord v.1 < W := toWord_lt (by omega) (by omega)
  simp only [sword, wmod_of_lt hl]
  simp only [Scalar.encodeValue, BitVec.toNat_ofInt, toWord]
  unfold W at hW hl ⊢
  split
  · have : v.1 % ((2 ^ 256 : Nat) : Int) = v.1 := Int.emod_eq_of_lt (by omega) (by omega)
    rw [this]
  · have : v.1 % ((2 ^ 256 : Nat) : Int) = v.1 + ((2 ^ 256 : Nat) : Int) := by
      rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [this]

/-- **The machine agrees with the Scalar endpoint `intShr`** at every pair of
intrinsic operands: both produce the encoding of the same source result, the
machine with the count on top (the memory compiler's order), the Scalar slice
with the shifted value on top (its `BinaryCertificate` order). -/
theorem machine_agrees_intShr (a n : PrimTy.int.Denote) (m : Machine) (tail : Scalar.Stack) :
    ∃ r : PrimTy.int.Denote, BinOp.shr.evalT rfl a n = some r ∧
      run (binTail .int .shr) { m with stack := .val (sword n.1) :: .val (sword a.1) :: m.stack } =
        .ok (m.push (.val (sword r.1))) 0 ∧
      Scalar.run Scalar.intShr.code (Scalar.encodeValue .int a :: Scalar.encodeValue .int n :: tail) =
        some (Scalar.encodeValue .int r :: tail) ∧
      (Scalar.encodeValue .int r).toNat = (sword r.1).1 := by
  refine ⟨_, evalT_shr a n, ?_, ?_, encode_int_word _⟩
  · have h := sar_tail m m.stack (sword a.1).2 (sword n.1).2
    simp only [Fin.eta, sgn_sword (int_range a), sgn_sword (int_range n)] at h
    rw [binTail, h]; rfl
  · rw [Scalar.intShr.correct a n tail, evalT_shr]; rfl

/-- **Negative control**: raw `SAR` without the clamp reads the count `-1`
(the word `2^256 - 1`) as a saturating count and fills with the sign,
whereas `sarCode` leaves `8` unchanged (the source value, by `sarWord_clamp`). -/
theorem raw_sar_differs (m : Machine) :
    run [.sar] { m with stack := .val wMax :: w[8] :: [] } ≠
      run sarCode { m with stack := .val wMax :: w[8] :: [] } := by
  rw [sarCode_run]
  simp only [run, exec_cons_zero, Instr.step, Machine.next, Out.ok_bind, exec_nil, ne_eq,
    Out.ok.injEq, and_true]
  intro h
  have := congrArg (fun mm => mm.stack) h
  simp only [List.cons.injEq, Word.val.injEq, and_true] at this
  revert this
  unfold sarWord sarClamp
  have hs : sgn wMax.1 < 0 := by
    show sgn (W - 1) < 0
    have := W_eq; have := H_pos; unfold sgn; split <;> omega
  have hw : ¬ wMax.1 < 256 := show ¬ (W - 1 < 256) by unfold W; decide
  have h8 : sgn 8 = 8 := by unfold sgn H; simp
  rw [if_pos hs, if_neg hw]
  intro h
  have := congrArg Fin.val h
  simp only [h8] at this
  simp [sword, toWord] at this
  rw [Nat.mod_eq_of_lt (by unfold W; decide)] at this
  omega

/-- **Positive witness** at a saturated count: `-7 >> 256` fills with the
sign on the machine (the source's `-1` there follows from `sarWord_clamp`). -/
theorem saturated_fill (m : Machine) :
    run sarCode { m with stack := w[256] :: .val (sword (-7)) :: [] } =
      .ok { m with stack := .val wMax :: [] } 0 := by
  rw [sarCode_run]
  have h := sarWord_clamp (sword (-7)).2 (show 256 < W by unfold W; decide)
  have h7 : 7 ≤ H := by unfold H; decide
  have hr : -(H : Int) ≤ -7 ∧ (-7 : Int) < H := by omega
  have h256 : sgn 256 = 256 := by unfold sgn H; simp
  simp only [Fin.eta, sgn_sword hr, h256, sarShr] at h
  rw [show (⟨256, _⟩ : Fin W) = ⟨256, show 256 < W by unfold W; decide⟩ from rfl, h]
  simp only [show ¬((256 : Int) < 256) by decide, if_false, show (-7 : Int) < 0 by decide, if_true]
  rfl

end Solidity.Backend.Passes.MachineSar
