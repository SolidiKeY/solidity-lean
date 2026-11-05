import Solidity.Evm.SimLemmas
import Solidity.Backend.Scalar.SignedShift

/-! # Machine SAR and the Scalar signed right shift

`Evm.Instr.sar` is the memory machine's `SAR` and `Evm.sTail .shr`
(`Evm.sarCode`) emits it after clamping a negative count to `0`, as the
Scalar endpoint `Backend.Scalar.intShr` does: the source reads a negative
`int` count by its `toNat`, `0`, where raw `SAR` would read its unsigned
word and saturate.

`sarCode_run` is the exact machine run on any two words; `sarCode_simT`
is the typed agreement with `BinOp.evalT .shr` at `int` in the shape of
`Evm.tail_simT` (`intShr` never reverts, so neither does the machine); and
`machine_agrees_intShr` relates the machine word to the Scalar endpoint's
word for every intrinsic operand pair. `raw_sar_differs` is the negative
control: unclamped `SAR` disagrees with the source at count `-1`.

`binInFrag .shr .int` stays `false`: the memory compiler's fragment and its
compiler theorem are unchanged by this module. -/

namespace Solidity.Backend.Passes.MachineSar
open Solidity.Evm

/-- The clamped count: `0` for a negative signed reading. -/
def clamp (n : Fin W) : Fin W := if sgn n.1 < 0 then ⟨0, W_pos⟩ else n

/-- The clamp prefix computes `clamp`: `SGT` against `0`, `ISZERO`, `MUL`. -/
theorem clamp_word (n : Fin W) :
    wmod ((bword (decide ((bword (decide (sgn n.1 < sgn 0))).1 = 0))).1 * n.1) = clamp n := by
  rw [sgn_zero]; unfold clamp
  by_cases hn : sgn n.1 < 0
  · simp only [hn, decide_true, if_true, bword]
    exact Fin.ext (by simp)
  · simp only [hn, decide_false, if_false, bword]
    exact Fin.ext (by simp [Nat.mod_eq_of_lt n.2])

/-- **The emitted sequence runs** on every pair of value words: the clamp,
then `SAR`, leaving the rest of the stack and the machine. -/
theorem sarCode_run (m : Machine) (st : List Word) (n a : Fin W) :
    run sarCode { m with stack := .val n :: .val a :: st } =
      .ok { m with stack := .val (sarWord (clamp n) a) :: st } 0 := by
  simp only [run, sarCode, exec_cons_zero, Instr.step, Machine.next, Out.ok_bind, exec_nil,
    Nat.sub_self, List.getElem?_cons_zero]
  rw [clamp_word]

/-- The source's signed right shift (`BinOp.arithInt .shr`) on two readings. -/
def sourceShr (a n : Int) : Int :=
  if n < 256 then a / 2 ^ n.toNat else if a < 0 then -1 else 0

/-- Floor division by a positive power keeps a signed reading in range. -/
theorem div_pow_range {x : Int} (k : Nat) (h : -(H : Int) ≤ x ∧ x < H) :
    -(H : Int) ≤ x / ((2 ^ k : Nat) : Int) ∧ x / ((2 ^ k : Nat) : Int) < H := by
  have hp : (0 : Int) < ((2 ^ k : Nat) : Int) := by
    have := Nat.two_pow_pos k; omega
  constructor
  · by_cases hx : 0 ≤ x
    · have := Int.ediv_nonneg hx (Int.le_of_lt hp); omega
    · have h1 : x ≤ x / ((2 ^ k : Nat) : Int) := by
        rw [Int.le_ediv_iff_mul_le hp]
        have : x * ((2 ^ k : Nat) : Int) ≤ x * 1 :=
          Int.mul_le_mul_of_nonpos_left (by omega) (by omega)
        omega
      omega
  · by_cases hx : 0 ≤ x
    · have := Int.ediv_le_self ((2 ^ k : Nat) : Int) hx; omega
    · have : x / ((2 ^ k : Nat) : Int) < 0 := Int.ediv_neg_of_neg_of_pos (by omega) hp
      have : (0 : Int) < H := by have := H_pos; omega
      omega

/-- The source result is an `int256`. -/
theorem sourceShr_range {a : Int} (n : Int) (h : -(H : Int) ≤ a ∧ a < H) :
    -(H : Int) ≤ sourceShr a n ∧ sourceShr a n < H := by
  unfold sourceShr
  split
  · rw [show ((2 : Int) ^ n.toNat) = ((2 ^ n.toNat : Nat) : Int) from
      (Int.natCast_pow 2 _).symm]
    exact div_pow_range _ h
  · have := H_pos; split <;> omega

theorem int_range (v : PrimTy.int.Denote) : -(H : Int) ≤ v.1 ∧ v.1 < H := by
  have := v.2; simpa only [PrimTy.inRange, decide_eq_true_eq] using this

/-- The source evaluates `a >> n` at `int` to `sourceShr`, never reverting. -/
theorem evalT_shr (a n : PrimTy.int.Denote) :
    BinOp.shr.evalT rfl a n = some ⟨sourceShr a.1 n.1, by
      simp only [PrimTy.inRange, decide_eq_true_eq]
      exact sourceShr_range n.1 (int_range a)⟩ :=
  dif_pos (by simp only [PrimTy.inRange, decide_eq_true_eq]
              exact sourceShr_range n.1 (int_range a))

/-- The machine word is the source result's two's complement word. -/
theorem sarWord_clamp {a n : Nat} (ha : a < W) (hn : n < W) :
    sarWord (clamp ⟨n, hn⟩) ⟨a, ha⟩ = sword (sourceShr (sgn a) (sgn n)) := by
  by_cases hneg : sgn n < 0
  · have h256 : sgn n < 256 := by omega
    have hz : (sgn n).toNat = 0 := Int.toNat_of_nonpos (by omega)
    rw [show clamp ⟨n, hn⟩ = ⟨0, W_pos⟩ from if_pos hneg]
    simp only [sarWord, sourceShr, h256, hz, if_true]
    simp
  · have hlt : n < H := by
      have := W_eq; unfold sgn at hneg; split at hneg <;> omega
    have hs : sgn n = (n : Int) := by unfold sgn; simp [hlt]
    rw [show clamp ⟨n, hn⟩ = ⟨n, hn⟩ from if_neg hneg]
    simp only [sarWord, sourceShr, hs, Int.toNat_natCast]
    by_cases h256 : n < 256
    · have : ((n : Int) < 256) := by omega
      simp only [h256, if_true, this]
      rw [show ((2 : Int) ^ n) = ((2 ^ n : Nat) : Int) from (Int.natCast_pow 2 n).symm]
    · have : ¬((n : Int) < 256) := by omega
      simp only [h256, if_false, this]
      have hW := W_pos
      by_cases ha0 : sgn a < 0
      · simp only [ha0, if_true]
        apply Fin.ext
        simp only [wMax_def, sword, toWord, wmod_def]
        rw [if_neg (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      · simp only [ha0, if_false]
        apply Fin.ext
        simp [sword, toWord]

/-- A signed reading of a two's complement word is the integer. -/
theorem sgn_sword {v : Int} (h : -(H : Int) ≤ v ∧ v < H) : sgn (sword v).1 = v := by
  have hW := W_eq
  have hl : toWord v < W := toWord_lt (by omega) (by omega)
  unfold sword; rw [wmod_of_lt hl]; exact sgn_toWord h.1 h.2

/-- **Typed agreement at `int`**, in `Evm.tail_simT`'s shape: on words
representing its operands, `binTail .int .shr` pushes the word of
`BinOp.evalT .shr`'s result, which never reverts. -/
theorem sarCode_simT {a b : PrimTy.int.Denote} {wa wb : Word} (ha : ReprV .int a wa)
    (hb : ReprV .int b wb) (m : Machine) :
    ValOutT (BinOp.shr.ret .int) (TRes.ofOpt (BinOp.shr.evalT rfl a b))
      (run (binTail .int .shr) { m with stack := wb :: wa :: m.stack }) m := by
  obtain ⟨x, rfl, hxa⟩ := ha
  obtain ⟨y, rfl, hyb⟩ := hb
  have hrun : run (binTail .int .shr) { m with stack := .val y :: .val x :: m.stack } =
      .ok (m.push (.val (sword (sourceShr a.1 b.1)))) 0 := by
    show run sarCode _ = _
    rw [sarCode_run, hxa, hyb, ← sarWord_clamp x.2 y.2]
    rfl
  rw [evalT_shr]
  exact .inl ⟨_, _, rfl, ReprV.int_word _, hrun⟩

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
  · show run sarCode _ = _
    have h := sarWord_clamp (sword a.1).2 (sword n.1).2
    simp only [Fin.eta, sgn_sword (int_range a), sgn_sword (int_range n)] at h
    rw [sarCode_run, h]; rfl
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
  unfold sarWord clamp
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
  simp only [Fin.eta, sgn_sword hr, h256, sourceShr] at h
  rw [show (⟨256, _⟩ : Fin W) = ⟨256, show 256 < W by unfold W; decide⟩ from rfl, h]
  simp only [show ¬((256 : Int) < 256) by decide, if_false, show (-7 : Int) < 0 by decide, if_true]
  rfl

end Solidity.Backend.Passes.MachineSar
