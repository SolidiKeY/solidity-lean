import Solidity.Backend.Scalar.Widths
import Solidity.Backend.Scalar.Bitwise
import Solidity.Backend.Scalar.Heights
import Solidity.Backend.Passes.ValueCertificate

/-! G25 consumer of published width/bitwise certificates. The source is the
existing typed mask expression, NOT assumed frontend width expansion. Numeric
slice execution and symbolic compiled execution stay distinct. -/
namespace Solidity.Backend.Passes.WidthApplication
open Backend.Scalar

theorem mask_bound (w : Fin 32) : 2 ^ widthBits w - 1 < 2 ^ 256 := by
  have power : 2 ^ widthBits w ≤ 2 ^ 256 :=
    Nat.pow_le_pow_right (by decide) (widthBits_bounds w).2
  have positive : 0 < 2 ^ widthBits w := Nat.pow_pos (by decide)
  omega

def maskValue (w : Fin 32) : PrimTy.uint.Denote :=
  lenU (2 ^ widthBits w - 1) (mask_bound w)

theorem mask_encoding (w : Fin 32) :
    encodeValue .uint (maskValue w) = BitVec.ofNat 256 (2 ^ widthBits w - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [encode_uint_toNat]
  simp only [maskValue,lenU,Int.toNat_natCast,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (mask_bound w)]

/-- Derive the existing intrinsic operation's result from TWO published
certificates. Neither bitwise arithmetic nor width cleanup is reimplemented. -/
theorem operation (w : Fin 32) (value : PrimTy.uint.Denote) :
    ∃ result, BinOp.band.evalT rfl (maskValue w) value = some result ∧
      encodeValue .uint result = unsignedClean w (encodeValue .uint value) := by
  have cleaned := unsigned_correct w (encodeValue .uint value) []
  have typed := uintAnd.correct (maskValue w) value []
  have same :
      run (unsignedCode w) [encodeValue .uint value] =
      run uintAnd.code [encodeValue .uint (maskValue w),encodeValue .uint value] := by
    rw [unsignedCode,run,step_pushWord,mask_encoding]
    rfl
  rw [same,typed] at cleaned
  cases evaluated : BinOp.band.evalT rfl (maskValue w) value with
  | none =>
    rw [evaluated] at cleaned
    cases cleaned
  | some result =>
    rw [evaluated] at cleaned
    exact ⟨result,rfl,(List.cons.inj (Option.some.inj cleaned)).1⟩

variable {C : Contract} {Γ : Ctx}
def expression (w : Fin 32) (operand : Val C Γ .uint) : Val C Γ .uint :=
  .binop .band rfl rfl
    (.simple (.lit (maskValue w).val (maskValue w).property)) operand

theorem source (w : Fin 32) (operand : Val C Γ .uint) (state : State C Γ)
    {value : PrimTy.uint.Denote} (evaluated : operand.evalT state = .ok value) :
    ∃ result, (expression w operand).evalT state = .ok result ∧
      encodeValue .uint result = unsignedClean w (encodeValue .uint value) := by
  obtain ⟨result,operation,encoded⟩ := operation w value
  refine ⟨result,?_,encoded⟩
  simp only [expression,Val.evalT,Simple.evalT,PrimTy.ofLit,BinOp.shortT,
    evaluated,bind,Except.bind]
  change TRes.ofOpt (BinOp.band.evalT rfl (maskValue w) value) = .ok result
  rw [operation]
  rfl

/-- Actual existing target constructors and Memory.ValFrag composition. -/
def compiled {b : Nat} {F : Evm.Frag Γ} (w : Fin 32) (operand : Val C Γ .uint)
    (given : Evm.Memory.CompiledVal b F operand) :
    Evm.Memory.CompiledVal b F (expression w operand) where
  code := Evm.Memory.binaryCode .uint .band
    (Evm.compileVal b (.simple (.lit (maskValue w).val (maskValue w).property))) given.code
  cert := .binary .band rfl rfl _ _ _ _ (.core _ rfl) given.cert

/-- The SAME intrinsic result is observed by the owner's numeric cleanup and
by actual symbolic compilation, preserving the entire machine below the word.
Physical numeric prefix capacity remains explicit, not inferred from tails. -/
theorem application {b L frame : Nat} {F : Evm.Frag Γ}
    (w : Fin 32) (operand : Val C Γ .uint)
    (given : Evm.Memory.CompiledVal b F operand)
    {state : State C Γ} {base : Nat → Fin Evm.W} {machine : Evm.Machine}
    (input : Evm.Memory.StateRepr L b frame F state base machine)
    {value : PrimTy.uint.Denote} (evaluated : operand.evalT state = .ok value)
    (saved : List (Fin Evm.W))
    (capacity : stackBound (unsignedCode w) ((saved.length+1 : Nat) : Int) = true) :
    ∃ result word,
      (expression w operand).evalT state = .ok result ∧
      Evm.ReprV .uint result word ∧
      encodeValue .uint result = unsignedClean w (encodeValue .uint value) ∧
      run (unsignedCode w) (encodeValue .uint value ::
        saved.map (fun a => BitVec.ofNat 256 a.val)) =
        some (encodeValue .uint result :: saved.map (fun a => BitVec.ofNat 256 a.val)) ∧
      Evm.run (compiled w operand given).code {machine with stack := saved.map Evm.Word.val} =
        .ok ({machine with stack := saved.map Evm.Word.val}.push word) 0 ∧
      stackBound (unsignedCode w) ((saved.length+1 : Nat) : Int) = true := by
  obtain ⟨result,source,encoding⟩ := source w operand state evaluated
  obtain ⟨word,represented,target⟩ :=
    value_success_tail (compiled w operand given) input source (saved.map Evm.Word.val)
  refine ⟨result,word,source,represented,encoding,?_,target,capacity⟩
  rw [encoding]
  exact unsigned_correct w (encodeValue .uint value) _

theorem prefix_safe (w : Fin 32) (value : PrimTy.uint.Denote) (saved : Stack)
    (capacity : stackBound (unsignedCode w) ((saved.length+1 : Nat) : Int) = true)
    (before after : Backend.Program) (code : before ++ after = unsignedCode w)
    {reached : Stack} (target : run before (encodeValue .uint value :: saved) = some reached) :
    reached.length ≤ 1024 := by
  apply prefix_capacity before after target
  rw [code]
  exact capacity

end Solidity.Backend.Passes.WidthApplication
/-- info: 'Solidity.Backend.Passes.WidthApplication.mask_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.WidthApplication.mask_bound
/-- info: 'Solidity.Backend.Passes.WidthApplication.mask_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.WidthApplication.mask_encoding
/-- info: 'Solidity.Backend.Passes.WidthApplication.operation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.WidthApplication.operation
/-- info: 'Solidity.Backend.Passes.WidthApplication.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.WidthApplication.source
/-- info: 'Solidity.Backend.Passes.WidthApplication.application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.WidthApplication.application
/-- info: 'Solidity.Backend.Passes.WidthApplication.prefix_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.WidthApplication.prefix_safe

namespace Solidity.Backend.Passes.WidthApplication
open Backend.Scalar
variable {C : Contract} {Γ : Ctx}

theorem source_revert_iff (w : Fin 32) (operand : Val C Γ .uint) (state : State C Γ) :
    (expression w operand).evalT state = .error .revert ↔
      operand.evalT state = .error .revert := by
  cases evaluated : operand.evalT state with
  | ok value =>
    obtain ⟨result,success,_⟩ := source w operand state evaluated
    rw [success]
    simp only [reduceCtorEq]
  | error halt =>
    have failed : (expression w operand).evalT state = .error halt := by
      simp only [expression,Val.evalT,Simple.evalT,PrimTy.ofLit,BinOp.shortT,
        evaluated,bind,Except.bind]
    rw [failed]

/-- An operand failure is preserved BEFORE cleanup. No successful numeric
operand is invented, and no statement about byte-level revert data is made. -/
theorem target_revert_iff {b L frame : Nat} {F : Evm.Frag Γ}
    (w : Fin 32) (operand : Val C Γ .uint)
    (given : Evm.Memory.CompiledVal b F operand)
    {state : State C Γ} {base : Nat → Fin Evm.W} {machine : Evm.Machine}
    (input : Evm.Memory.StateRepr L b frame F state base machine) (tail : List Evm.Word) :
    Evm.run (compiled w operand given).code {machine with stack := tail} = .revert ↔
      operand.evalT state = .error .revert :=
  (value_revert_iff (compiled w operand given) input tail).trans (source_revert_iff w operand state)

theorem bytes (w : Fin 32) :
    Backend.decode (Backend.encode (unsignedCode w)) = some (unsignedCode w) :=
  Backend.decode_encode _

end Solidity.Backend.Passes.WidthApplication
/-- info: 'Solidity.Backend.Passes.WidthApplication.source_revert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.WidthApplication.source_revert_iff
/-- info: 'Solidity.Backend.Passes.WidthApplication.target_revert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.WidthApplication.target_revert_iff
/-- info: 'Solidity.Backend.Passes.WidthApplication.bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.WidthApplication.bytes
