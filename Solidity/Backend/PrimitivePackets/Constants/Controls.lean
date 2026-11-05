import Solidity.Backend.PrimitivePackets.Constants.Agreement

/-! Kernel controls: every legal width/sign, signed and unsigned endpoints,
outside-range and fractional refusal, wrong sign/width/word and low fuel. -/
namespace Solidity.Backend.PrimitivePackets.Constants.Controls
open Evm Evm.Memory Solidity.Lowering.V07

def i8 : Source.IntTy := ⟨true,8,by decide⟩
def u16 : Source.IntTy := ⟨false,16,by decide⟩

theorem endpoints (t : Source.IntTy) : t.lo ≤ t.hi := by
  have h := t.wrap_mem 0
  omega

theorem below_refused {D : Source.Layout} (t : Source.IntTy) :
    Source.constVal (Source.Q.ofInt (t.lo-1)) (.int t) =
      (.error (.stuck "integer out of range") : Source.R (Source.Val D (.int t))) :=
  source_refused t (t.lo-1) (by omega)

theorem above_refused {D : Source.Layout} (t : Source.IntTy) :
    Source.constVal (Source.Q.ofInt (t.hi+1)) (.int t) =
      (.error (.stuck "integer out of range") : Source.R (Source.Val D (.int t))) :=
  source_refused t (t.hi+1) (by omega)

theorem fractional_refused {D : Source.Layout} (t : Source.IntTy) :
    Source.constVal ⟨3,2,by decide⟩ (.int t) =
      (.error (.stuck "fractional constant at an integer type") : Source.R (Source.Val D (.int t))) := by
  rfl

theorem lower {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (t : Source.IntTy) (m : Machine) (tail : List Word) :
    run (selected (C:=C) offset F t t.lo ⟨Int.le_refl _,endpoints t⟩).code {m with stack := tail} =
      .ok ({m with stack := tail}.push (.val (sword t.lo))) 0 :=
  target_success offset F t t.lo _ m tail

theorem upper {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (t : Source.IntTy) (m : Machine) (tail : List Word) :
    run (selected (C:=C) offset F t t.hi ⟨endpoints t,Int.le_refl _⟩).code {m with stack := tail} =
      .ok ({m with stack := tail}.push (.val (sword t.hi))) 0 :=
  target_success offset F t t.hi _ m tail

theorem wrong_word {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (t : Source.IntTy) (z : Int) (h : t.lo ≤ z ∧ z ≤ t.hi)
    (m : Machine) (tail : List Word) (wrong : Word) (different : .val (sword z) ≠ wrong) :
    run (selected (C:=C) offset F t z h).code {m with stack := tail} ≠
      .ok ({m with stack := tail}.push wrong) 0 := by
  rw [target_success]
  intro same
  have stacks := congrArg (fun o => match o with | Out.ok state _ => state.stack | _ => []) same
  exact different (List.cons.inj stacks).1

theorem zero_fits (t : Source.IntTy) : t.lo ≤ 0 ∧ 0 ≤ t.hi := by
  have hp := Source.two_pow_pos t.bits
  have hs := Source.two_pow_pos (t.bits-1)
  cases sign : t.signed <;>
    simp only [Source.IntTy.lo,Source.IntTy.hi,sign,Bool.false_eq_true,if_true,if_false] <;> omega

theorem zero {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (t : Source.IntTy) (m : Machine) (tail : List Word) :
    run (selected (C:=C) offset F t 0 (zero_fits t)).code {m with stack := tail} =
      .ok ({m with stack := tail}.push (.val (sword 0))) 0 :=
  target_success offset F t 0 _ m tail

theorem wrong_signed_result {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (m : Machine) (tail : List Word) :
    run (selected (C:=C) offset F i8 (-1) (by decide)).code {m with stack := tail} ≠
      .ok ({m with stack := tail}.push (.val (wmod 255))) 0 :=
  wrong_word offset F i8 (-1) (by decide) m tail _ (by decide)

theorem signed_minus_one_word : sword (-1) ≠ wmod 255 := by decide

theorem signed_minus_one_read : sgn (sword (-1)).val = -1 :=
  signed_read i8 (-1) (by decide) rfl

theorem unsigned_max_read : ((sword 255).val : Int) = 255 :=
  unsigned_read .u8 255 (by decide) rfl

theorem wrong_width_refused {D : Source.Layout} :
    Source.constVal (Source.Q.ofInt 256) (.int .u8) =
      (.error (.stuck "integer out of range") : Source.R (Source.Val D (.int .u8))) :=
  source_refused .u8 256 (by decide)

theorem wrong_sign_refused {D : Source.Layout} :
    Source.constVal (Source.Q.ofInt (-1)) (.int .u8) =
      (.error (.stuck "integer out of range") : Source.R (Source.Val D (.int .u8))) :=
  source_refused .u8 (-1) (by decide)

theorem low_fuel {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (s : Source.EMState E Γ) (t : Source.IntTy) (z : Int) (h : t.lo ≤ z ∧ z ≤ t.hi) :
    (Source.evalE G F 0
      (.conv (.const (Source.Q.ofInt z)) (.inl (IntegerConstants.allowed E t z h)))).run s =
      (.error .timeout,s) := by
  rfl

-- These clients instantiate actual joint Source/selection/target execution;
-- G can carry either pipeline, F either checked mode, and m any populated frame.
def signed_min {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (SF : Source.Fr) (s : Source.EMState E srcΓ)
    (F : Frag Γ) (m : Machine) (tail : List Word) :=
  success (C:=C) G SF 0 s 0 F i8 (-128) (by decide) m tail

def signed_max {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (SF : Source.Fr) (s : Source.EMState E srcΓ)
    (F : Frag Γ) (m : Machine) (tail : List Word) :=
  success (C:=C) G SF 0 s 0 F i8 127 (by decide) m tail

def unsigned_max {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (SF : Source.Fr) (s : Source.EMState E srcΓ)
    (F : Frag Γ) (m : Machine) (tail : List Word) :=
  success (C:=C) G SF 0 s 0 F .u8 255 (by decide) m tail

def wider_positive {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (SF : Source.Fr) (s : Source.EMState E srcΓ)
    (F : Frag Γ) (m : Machine) (tail : List Word) :=
  success (C:=C) G SF 0 s 0 F u16 256 (by decide) m tail

end Solidity.Backend.PrimitivePackets.Constants.Controls
