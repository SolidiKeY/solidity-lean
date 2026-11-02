import SolidityBridge.RoadmapV15.P10.SignExtensionConsumer
import Solidity.Backend.Scalar.CastChains

/-! Scalar/reference SIGNEXTEND word transport over the actual reference mask,
retaining the earlier positive and clear-residue consequences. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

private theorem and_sign_power_zero (x k : Nat) (small : x<2^k) : x &&& 2^k=0 := by
  have bound : x &&& 2^k < 2^k := Nat.lt_of_le_of_lt Nat.and_le_left small
  have h := Nat.and_mod_two_pow (a:=x) (b:=2^k) (n:=k)
  simpa only [Nat.mod_eq_of_lt bound,Nat.mod_eq_of_lt small,Nat.mod_self,Nat.and_zero] using h

private theorem sign_position (w : Fin 32) :
    (UInt256.ofNat w.val * ⟨8⟩ + ⟨7⟩).toNat = w.val*8+7 := by
  have wi : w.val < UInt256.size := Nat.lt_trans w.isLt (by decide +kernel)
  have mul : w.val*8 < UInt256.size := Nat.lt_of_le_of_lt (by have h:=w.isLt;omega : w.val*8≤248) (by decide +kernel)
  have add : w.val*8+7 < UInt256.size := Nat.lt_of_le_of_lt (by have h:=w.isLt;omega : w.val*8+7≤255) (by decide +kernel)
  change (((w.val%UInt256.size)*8)%UInt256.size+7)%UInt256.size = w.val*8+7
  rw [Nat.mod_eq_of_lt wi,Nat.mod_eq_of_lt mul,Nat.mod_eq_of_lt add]

private def referenceSignBit (w : Fin 32) : UInt256 :=
  UInt256.shiftLeft ⟨1⟩ (UInt256.ofNat w.val * ⟨8⟩ + ⟨7⟩)

private theorem sign_bit_nat (w : Fin 32) :
    (referenceSignBit w).toNat = 2^(w.val*8+7) := by
  have count := sign_position w
  have fits : w.val*8+7<256 := by have h:=w.isLt;omega
  have bounded : 2^(w.val*8+7)<UInt256.size := Nat.pow_lt_pow_right (by decide) fits
  have shift : ¬(UInt256.ofNat w.val * ⟨8⟩ + ⟨7⟩).val ≥ 256 := by
    change ¬(UInt256.ofNat w.val * ⟨8⟩ + ⟨7⟩).toNat ≥ 256
    rw [count]
    omega
  unfold referenceSignBit UInt256.shiftLeft
  rw [if_neg shift]
  change ((1 : Fin UInt256.size) <<< (UInt256.ofNat w.val * ⟨8⟩ + ⟨7⟩).val).val = _
  rw [Fin.shiftLeft_val]
  change (1 <<< (UInt256.ofNat w.val * ⟨8⟩ + ⟨7⟩).toNat)%UInt256.size = _
  rw [count,Nat.shiftLeft_eq,Nat.one_mul,Nat.mod_eq_of_lt bounded]

/-- For every byte width, a value below its sign bit is preserved by the real
reference SIGNEXTEND. The bound is explicit and does not cover negative inputs. -/
theorem signextend_positive_word (w : Fin 32) (b : Scalar.Word)
    (positive : b.toNat<2^(w.val*8+7)) :
    UInt256.signextend (.ofNat w.val) ⟨b.toFin⟩ = ⟨b.toFin⟩ := by
  have zero : UInt256.land ⟨b.toFin⟩ (referenceSignBit w) = ⟨0⟩ := by
    apply congrArg UInt256.mk
    apply Fin.ext
    change ((UInt256.mk b.toFin).val &&& (referenceSignBit w).val).val = 0
    rw [Fin.and_val]
    change b.toNat &&& (referenceSignBit w).toNat = 0
    rw [sign_bit_nat,and_sign_power_zero _ _ positive]
  have index : (UInt256.ofNat w.val).toNat ≤ 31 := by
    change w.val%UInt256.size ≤ 31
    rw [Nat.mod_eq_of_lt (Nat.lt_trans w.isLt (by decide +kernel))]
    have h:=w.isLt;omega
  have one : (1 : Fin UInt256.size) ≤ (referenceSignBit w).val := by
    change 1 ≤ (referenceSignBit w).toNat
    rw [sign_bit_nat]
    have h := Nat.two_pow_pos (w.val*8+7)
    omega
  unfold UInt256.signextend
  rw [if_pos index]
  change (if UInt256.land ⟨b.toFin⟩ (referenceSignBit w) ≠ ⟨0⟩ then _
    else UInt256.land ⟨b.toFin⟩ (referenceSignBit w-⟨1⟩)) = _
  rw [if_neg (not_not_intro zero)]
  apply congrArg UInt256.mk
  apply Fin.ext
  change ((UInt256.mk b.toFin).val &&& ((referenceSignBit w).val-(1 : Fin UInt256.size))).val = b.toNat
  rw [Fin.and_val,Fin.sub_val_of_le one]
  change b.toNat &&& ((referenceSignBit w).toNat-1) = b.toNat
  rw [sign_bit_nat]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow positive

/-- The published independent signed cleanup observes the same positive value. -/
theorem signed_clean_positive (w : Fin 32) (b : Scalar.Word)
    (positive : b.toNat<2^(w.val*8+7)) : Scalar.signedClean w b=b := by
  have half : Scalar.widthBits w-1=w.val*8+7 := by unfold Scalar.widthBits;omega
  have wide : b.toNat<2^Scalar.widthBits w := Nat.lt_of_lt_of_le positive
    (Nat.pow_le_pow_right (by decide) (by unfold Scalar.widthBits;omega))
  simp only [Scalar.signedClean,Nat.mod_eq_of_lt wide,half,if_pos positive,BitVec.ofInt_natCast]
  change BitVec.ofNat 256 b.toFin.val=b
  rw [BitVec.ofNat_finVal,BitVec.ofFin_toFin]

/-- Published intrinsic cleanup and actual fetched SIGNEXTEND agree on the
positive range. Native execution starts with the explicit width/value operands;
no preceding native PUSH execution or compiler/frame origin is asserted. -/
theorem signextend_positive_agreement (site : Site .SIGNEXTEND) (w : Fin 32)
    (b : Scalar.Word) (tail : Scalar.Stack) (positive : b.toNat<2^(w.val*8+7))
    (room : tail.length+2≤1024) (gas : 5≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let start := (modularSite site (BitVec.ofNat 256 w.val::b::tail)).state
    let next := (Assembly.chargedPrepare start 5).replaceStackAndIncrPC
      ((b::tail).map (fun x => UInt256.mk x.toFin))
    Scalar.run (Scalar.signedCode w) (b::tail)=some (b::tail) ∧
      Assembly.driverSteps 1 (fuel+2) #[] start=.ok next ∧
      EVM.X (fuel+2) #[] start=EVM.X (fuel+1) #[] next := by
  constructor
  · rw [Scalar.signed_correct,signed_clean_positive w b positive]
  · have h := signextend_fetched site (BitVec.ofNat 256 w.val) b tail room gas fuel
    have index : UInt256.mk (BitVec.ofNat 256 w.val).toFin = UInt256.ofNat w.val := by rfl
    dsimp only at h ⊢
    rw [index,signextend_positive_word w b positive] at h
    exact h

/-- Arbitrary high bits are discarded when the selected low-width residue
has a clear sign bit. The premise constrains the residue, not the full word. -/
theorem signextend_nonnegative_residue_word (w : Fin 32) (b : Scalar.Word)
    (nonnegative : b.toNat%2^Scalar.widthBits w < 2^(Scalar.widthBits w-1)) :
    UInt256.signextend (.ofNat w.val) ⟨b.toFin⟩ = ⟨(Scalar.unsignedClean w b).toFin⟩ := by
  have half : Scalar.widthBits w-1=w.val*8+7 := by unfold Scalar.widthBits;omega
  have low : b.toNat%2^Scalar.widthBits w < 2^(w.val*8+7) := by rw [←half];exact nonnegative
  have bitfits : 2^(w.val*8+7)<2^Scalar.widthBits w :=
    Nat.pow_lt_pow_right (by decide) (by unfold Scalar.widthBits;omega)
  have cleared : b.toNat &&& 2^(w.val*8+7)=0 := by
    have bound : b.toNat &&& 2^(w.val*8+7)<2^Scalar.widthBits w :=
      Nat.lt_of_le_of_lt Nat.and_le_right bitfits
    have e := Nat.and_mod_two_pow (a:=b.toNat) (b:=2^(w.val*8+7)) (n:=Scalar.widthBits w)
    simpa only [Nat.mod_eq_of_lt bound,Nat.mod_eq_of_lt bitfits,
      and_sign_power_zero _ _ low] using e
  have zero : UInt256.land ⟨b.toFin⟩ (referenceSignBit w) = ⟨0⟩ := by
    apply congrArg UInt256.mk
    apply Fin.ext
    change ((UInt256.mk b.toFin).val &&& (referenceSignBit w).val).val = 0
    rw [Fin.and_val]
    change b.toNat &&& (referenceSignBit w).toNat=0
    rw [sign_bit_nat]
    exact cleared
  have index : (UInt256.ofNat w.val).toNat≤31 := by
    change w.val%UInt256.size≤31
    rw [Nat.mod_eq_of_lt (Nat.lt_trans w.isLt (by decide +kernel))]
    have h:=w.isLt;omega
  have one : (1 : Fin UInt256.size) ≤ (referenceSignBit w).val := by
    change 1≤(referenceSignBit w).toNat
    rw [sign_bit_nat]
    have h:=Nat.two_pow_pos (w.val*8+7);omega
  have sameLow : b.toNat%2^(w.val*8+7)=b.toNat%2^Scalar.widthBits w := by
    have e := Nat.mod_mod_of_dvd b.toNat
      (Nat.pow_dvd_pow 2 (by unfold Scalar.widthBits;omega : w.val*8+7≤Scalar.widthBits w))
    rw [Nat.mod_eq_of_lt low] at e
    exact e.symm
  unfold UInt256.signextend
  rw [if_pos index]
  change (if UInt256.land ⟨b.toFin⟩ (referenceSignBit w) ≠ ⟨0⟩ then _
    else UInt256.land ⟨b.toFin⟩ (referenceSignBit w-⟨1⟩)) = _
  rw [if_neg (not_not_intro zero)]
  apply congrArg UInt256.mk
  apply Fin.ext
  change ((UInt256.mk b.toFin).val &&& ((referenceSignBit w).val-(1 : Fin UInt256.size))).val =
    (Scalar.unsignedClean w b).toNat
  rw [Fin.and_val,Fin.sub_val_of_le one]
  change b.toNat &&& ((referenceSignBit w).toNat-1) = (Scalar.unsignedClean w b).toNat
  rw [sign_bit_nat,Nat.and_two_pow_sub_one_eq_mod,sameLow]
  unfold Scalar.unsignedClean
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) b.isLt)]

/-- The existing intrinsic signed cleanup selects exactly that unsigned
residue when its sign bit is clear, with no bound on discarded high bits. -/
theorem signed_clean_nonnegative_residue (w : Fin 32) (b : Scalar.Word)
    (nonnegative : b.toNat%2^Scalar.widthBits w < 2^(Scalar.widthBits w-1)) :
    Scalar.signedClean w b=Scalar.unsignedClean w b := by
  simp only [Scalar.signedClean,Scalar.unsignedClean,if_pos nonnegative,BitVec.ofInt_natCast]

/-- Truncating nonnegative-residue transport through actual fetched execution;
initial operands are explicit and no native prefix or source origin is assumed. -/
theorem signextend_nonnegative_residue_agreement (site : Site .SIGNEXTEND) (w : Fin 32)
    (b : Scalar.Word) (tail : Scalar.Stack)
    (nonnegative : b.toNat%2^Scalar.widthBits w < 2^(Scalar.widthBits w-1))
    (room : tail.length+2≤1024) (gas : 5≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let start := (modularSite site (BitVec.ofNat 256 w.val::b::tail)).state
    let next := (Assembly.chargedPrepare start 5).replaceStackAndIncrPC
      ((Scalar.unsignedClean w b::tail).map (fun x => UInt256.mk x.toFin))
    Scalar.run (Scalar.signedCode w) (b::tail)=some (Scalar.unsignedClean w b::tail) ∧
      Assembly.driverSteps 1 (fuel+2) #[] start=.ok next ∧
      EVM.X (fuel+2) #[] start=EVM.X (fuel+1) #[] next := by
  constructor
  · rw [Scalar.signed_correct,signed_clean_nonnegative_residue w b nonnegative]
  · have h := signextend_fetched site (BitVec.ofNat 256 w.val) b tail room gas fuel
    have index : UInt256.mk (BitVec.ofNat 256 w.val).toFin = UInt256.ofNat w.val := by rfl
    dsimp only at h ⊢
    rw [index,signextend_nonnegative_residue_word w b nonnegative] at h
    exact h

private theorem or_high_fill (x n k : Nat) (kn : k≤n) (bound : x<2^n) :
    x ||| (2^n-2^k)=x%2^k+(2^n-2^k) := by
  have factor : 2^k*(2^(n-k)-1)=2^n-2^k := by
    rw [Nat.mul_sub_left_distrib,Nat.mul_one,←Nat.pow_add,Nat.add_sub_of_le kn]
  calc
    x ||| (2^n-2^k) = x ||| (2^k*(2^(n-k)-1)) := by rw [factor]
    _ = 2^k*(2^(n-k)-1)+x%2^k := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_or,Nat.testBit_two_pow_mul,
        Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos k))]
      simp only [Nat.testBit_two_pow_sub_one]
      by_cases low : i<k
      · simp only [low,if_pos,show ¬i≥k from by omega,decide_false,Bool.false_and,
          Bool.or_false,Nat.testBit_mod_two_pow,decide_true,Bool.true_and]
      · rw [if_neg low]
        by_cases high : i<n
        · have inside : i-k<n-k := by omega
          simp only [show i≥k from by omega,decide_true,Bool.true_and,inside,Bool.or_true]
        · have outside : ¬i-k<n-k := by omega
          have xb : x.testBit i=false := Nat.testBit_lt_two_pow
            (Nat.lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) (by omega)))
          simp only [outside,decide_false,Bool.and_false,Bool.or_false,xb]
    _ = x%2^k+(2^n-2^k) := by rw [factor,Nat.add_comm]

private theorem sign_bit_set (x k : Nat) (negative : 2^k≤x%2^(k+1)) :
    x.testBit k=true := by
  have bound : x%2^(k+1)<2^(k+1) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have twice : 2^(k+1)=2^k+2^k := by rw [Nat.pow_succ,Nat.mul_two]
  have div : x%2^(k+1)/2^k=1 := by
    apply Nat.div_eq_of_lt_le
    · simpa only [Nat.one_mul] using negative
    · change x%2^(k+1)<2*2^k
      rw [Nat.two_mul,←twice]
      exact bound
  have parity : x/2^k%2=1 := by
    rw [←Nat.mod_mul_right_div_self,←Nat.pow_succ,div]
  simp only [Nat.testBit_eq_decide_div_mod_eq,parity,decide_true]

/-- Negative low residues use the actual upper-bit fill, not unsigned cleanup. -/
theorem signextend_negative_residue_word (w : Fin 32) (b : Scalar.Word)
    (negative : 2^(Scalar.widthBits w-1)≤b.toNat%2^Scalar.widthBits w) :
    UInt256.signextend (.ofNat w.val) ⟨b.toFin⟩=⟨(Scalar.signedClean w b).toFin⟩ := by
  have half : Scalar.widthBits w-1=w.val*8+7 := by unfold Scalar.widthBits;omega
  have width : Scalar.widthBits w=(w.val*8+7)+1 := by unfold Scalar.widthBits;omega
  have bit : b.toNat.testBit (w.val*8+7)=true := sign_bit_set _ _ (by
    rw [←width,←half]
    exact negative)
  have nonzero : UInt256.land ⟨b.toFin⟩ (referenceSignBit w) ≠ ⟨0⟩ := by
    intro zero
    have e := congrArg UInt256.toNat zero
    change ((UInt256.mk b.toFin).val &&& (referenceSignBit w).val).val=0 at e
    rw [Fin.and_val] at e
    change b.toNat &&& (referenceSignBit w).toNat=0 at e
    rw [sign_bit_nat] at e
    have test := congrArg (fun x : Nat => x.testBit (w.val*8+7)) e
    simp only [Nat.testBit_and,bit,Nat.testBit_two_pow_self,Bool.true_and,
      Nat.zero_testBit,Bool.true_eq_false] at test
  have index : (UInt256.ofNat w.val).toNat≤31 := by
    change w.val%UInt256.size≤31
    rw [Nat.mod_eq_of_lt (Nat.lt_trans w.isLt (by decide +kernel))]
    have h:=w.isLt;omega
  have positive : 0<(referenceSignBit w).toNat := by
    rw [sign_bit_nat]
    exact Nat.two_pow_pos _
  have mask : (UInt256.size.toUInt256-referenceSignBit w).toNat=UInt256.size-2^(w.val*8+7) := by
    change ((0 : Fin UInt256.size)-(referenceSignBit w).val).val=UInt256.size-2^(w.val*8+7)
    rw [Fin.coe_sub_iff_lt.mpr (show (0 : Fin UInt256.size)<(referenceSignBit w).val from positive)]
    change UInt256.size+0-(referenceSignBit w).toNat=UInt256.size-2^(w.val*8+7)
    rw [Nat.add_zero,sign_bit_nat]
  have hp : 0<2^(w.val*8+7) := Nat.two_pow_pos _
  have hf : 2^(w.val*8+7)<UInt256.size := by
    have h : (referenceSignBit w).toNat<UInt256.size := (referenceSignBit w).val.isLt
    rw [sign_bit_nat] at h
    exact h
  have fits : b.toNat ||| (UInt256.size-2^(w.val*8+7))<UInt256.size :=
    Nat.or_lt_two_pow b.isLt (by change UInt256.size-2^(w.val*8+7)<UInt256.size;omega)
  have fill := or_high_fill b.toNat 256 (w.val*8+7) (by have h:=w.isLt;omega) b.isLt
  change b.toNat ||| (UInt256.size-2^(w.val*8+7))=
    b.toNat%2^(w.val*8+7)+(UInt256.size-2^(w.val*8+7)) at fill
  have twice : 2^Scalar.widthBits w=2^(w.val*8+7)+2^(w.val*8+7) := by
    have h:=Scalar.width_half w
    rw [half] at h
    exact h
  have neg : 2^(w.val*8+7)≤b.toNat%2^Scalar.widthBits w := by rw [←half];exact negative
  have rb : b.toNat%2^Scalar.widthBits w<2^Scalar.widthBits w := Nat.mod_lt _ (Nat.two_pow_pos _)
  have div : b.toNat%2^Scalar.widthBits w/2^(w.val*8+7)=1 := by
    apply Nat.div_eq_of_lt_le
    · simpa only [Nat.one_mul] using neg
    · change b.toNat%2^Scalar.widthBits w<2*2^(w.val*8+7)
      rw [Nat.two_mul,←twice]
      exact rb
  have low := Nat.mod_mod_of_dvd b.toNat (Nat.pow_dvd_pow 2 (by omega : w.val*8+7≤Scalar.widthBits w))
  have split := Nat.mod_add_div (b.toNat%2^Scalar.widthBits w) (2^(w.val*8+7))
  rw [low,div,Nat.mul_one] at split
  have maximum : 2^Scalar.widthBits w≤UInt256.size :=
    Nat.pow_le_pow_right (by decide) (Scalar.widthBits_bounds w).2
  unfold UInt256.signextend
  rw [if_pos index]
  change (if UInt256.land ⟨b.toFin⟩ (referenceSignBit w) ≠ ⟨0⟩
    then UInt256.lor ⟨b.toFin⟩ (UInt256.size.toUInt256-referenceSignBit w) else _) = _
  rw [if_pos nonzero]
  apply congrArg UInt256.mk
  apply Fin.ext
  change ((UInt256.mk b.toFin).val ||| (UInt256.size.toUInt256-referenceSignBit w).val).val =
    (Scalar.signedClean w b).toNat
  rw [Fin.or_val]
  change (b.toNat ||| (UInt256.size.toUInt256-referenceSignBit w).toNat)%UInt256.size = _
  rw [mask,Nat.mod_eq_of_lt fits,fill,Scalar.signedClean_nat,if_neg (Nat.not_lt_of_ge negative)]
  change b.toNat%2^(w.val*8+7)+(UInt256.size-2^(w.val*8+7))=
    b.toNat%2^Scalar.widthBits w+(UInt256.size-2^Scalar.widthBits w)
  omega

/-- Every declared byte width and every word value, including truncation and
negative residues, agrees with the existing intrinsic cleanup. -/
theorem signextend_width_word (w : Fin 32) (b : Scalar.Word) :
    UInt256.signextend (.ofNat w.val) ⟨b.toFin⟩=⟨(Scalar.signedClean w b).toFin⟩ := by
  by_cases nonnegative : b.toNat%2^Scalar.widthBits w<2^(Scalar.widthBits w-1)
  · rw [signextend_nonnegative_residue_word w b nonnegative,
      signed_clean_nonnegative_residue w b nonnegative]
  · exact signextend_negative_residue_word w b (by omega)

/-- Every index word: declared-width cleanup below32 and the actual identity
rule otherwise. This is a theorem over existing definitions, not a new machine. -/
theorem signextend_all_word (a b : Scalar.Word) :
    UInt256.signextend ⟨a.toFin⟩ ⟨b.toFin⟩ =
      ⟨(if h : a.toNat<32 then Scalar.signedClean ⟨a.toNat,h⟩ b else b).toFin⟩ := by
  by_cases small : a.toNat<32
  · rw [dif_pos small]
    have index : UInt256.ofNat a.toNat=UInt256.mk a.toFin := by
      apply congrArg UInt256.mk
      apply Fin.ext
      change a.toNat%UInt256.size=a.toNat
      exact Nat.mod_eq_of_lt a.isLt
    rw [←index]
    exact signextend_width_word ⟨a.toNat,small⟩ b
  · rw [dif_neg small]
    exact signextend_large_word a b (by omega)

/-- The result expression is exactly the published intrinsic step. -/
theorem signextend_scalar_result (a b : Scalar.Word) (tail : Scalar.Stack) :
    Scalar.step (.op .SIGNEXTEND) (a::b::tail)=
      some ((if h : a.toNat<32 then Scalar.signedClean ⟨a.toNat,h⟩ b else b)::tail) := by
  rfl

/-- All index/value words, including both sign branches, truncation and large
indices. Native execution begins with the explicit represented operands; prefix
execution, source compiler origin and full Osaka agreement remain separate. -/
theorem signextend_all_agreement (site : Site .SIGNEXTEND) (a b : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+2≤1024) (gas : 5≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let result := if h : a.toNat<32 then Scalar.signedClean ⟨a.toNat,h⟩ b else b
    let start := (modularSite site (a::b::tail)).state
    let next := (Assembly.chargedPrepare start 5).replaceStackAndIncrPC
      ((result::tail).map (fun x => UInt256.mk x.toFin))
    Scalar.step (.op .SIGNEXTEND) (a::b::tail)=some (result::tail) ∧
      Assembly.driverSteps 1 (fuel+2) #[] start=.ok next ∧
      EVM.X (fuel+2) #[] start=EVM.X (fuel+1) #[] next := by
  refine ⟨signextend_scalar_result a b tail,?_⟩
  have h := signextend_fetched site a b tail room gas fuel
  dsimp only at h ⊢
  rw [signextend_all_word] at h
  exact h

#print axioms signextend_all_word
#print axioms signextend_scalar_result
#print axioms signextend_all_agreement
#print axioms signextend_negative_residue_word
#print axioms signextend_width_word
#print axioms signextend_nonnegative_residue_word
#print axioms signed_clean_nonnegative_residue
#print axioms signextend_nonnegative_residue_agreement
#print axioms signextend_positive_agreement
#print axioms signextend_positive_word
#print axioms signed_clean_positive
end SolidityBridge.RoadmapV15.P10
