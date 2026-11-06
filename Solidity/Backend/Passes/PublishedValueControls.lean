import Solidity.Backend.Passes.PublishedValues
import Solidity.Evm.Correct

/-! Actual shared instruction/byte observations, physical input, and guard
controls. Numeric component outcomes are not full fetched-EVM executions. -/
namespace Solidity.Backend.Passes.PublishedValueControls
open Backend.Environment
open Evm.Memory

def C : Contract := contract!{ }
def self : Fin Evm.W := ⟨7, by decide⟩
def state : State C [] := Evm.freshT C 41 (by decide) self
def machine : Evm.Machine := Evm.Machine.init (fun _ => 41) self
def frame : Frame :=
  { self := account (lenU 7 (by decide)), sender := account (lenU 0 (by decide)),
    value := lenU 0 (by decide), time := lenU 0 (by decide),
    funds := fun _ => lenU 41 (by decide) }

theorem represented : Represents frame state := ⟨rfl,rfl,rfl,rfl,rfl⟩

private theorem noRef {R : RefTy} (r : HRef [] R) : False := by cases r.get?

def bases : Nat → Fin Evm.W := fun _ => ⟨0, by decide⟩
theorem physical_input : StateRepr 1 0 0 (Evm.Frag.init []) state bases machine := by
  exact ⟨Evm.Sim.init C 41 (by decide) (fun _ => 41) self rfl,
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r _ _ => (noRef r).elim⟩,
    (fun i => nomatch i), by decide,
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩,
    (fun _ r => (noRef r).elim), RefFieldsRepr.withoutStructs _ _ _ (fun r => noRef r)⟩

def rhs : PrimTy.uint.Denote := lenU 3 (by decide)
def expr : Val C [] .uint := PublishedValues.expression .selfAddress rhs
def compiled : CompiledVal 0 (Evm.Frag.init []) expr :=
  (compileVal 0 (Evm.Frag.init []) expr).get (by decide +kernel)

theorem intrinsic_value : expr.evalT state = .ok (lenU 4 (by decide)) := by rfl

theorem physical_value (tail : List Evm.Word) :
    ∃ w, Evm.ReprV .uint (lenU 4 (by decide)) w ∧
      Evm.run compiled.code {machine with stack := tail} =
        .ok ({machine with stack := tail}.push w) 0 :=
  PublishedValues.symbolic_value state frame represented .selfAddress rhs compiled physical_input tail

def bytesCode : List Backend.Instr := PublishedValues.code .selfAddress ⟨3,by decide⟩
theorem instructions : bytesCode =
    [constant 1 ⟨3,by decide⟩, .op .ADDRESS, .op .SUB] := rfl

theorem bytes : Backend.encode bytesCode = [0x60,0x03,0x30,0x03] := rfl

theorem byte_roundtrip : Backend.decode [0x60,0x03,0x30,0x03] = some bytesCode :=
  PublishedValues.decode_code .selfAddress ⟨3,by decide⟩

private theorem address_observation : observe frame .selfAddress = lenU 7 (by decide) := rfl
private theorem wrap_four : wrap (7 + 2^256 - 3) = lenU 4 (by decide) := by decide +kernel

theorem numeric_tail (tail : List Backend.Environment.Word) (m : Memory) :
    runSlice frame bytesCode ⟨tail,m⟩ = some ⟨lenU 4 (by decide)::tail,m⟩ := by
  have h := PublishedValues.mixed_run frame .selfAddress ⟨3,by decide⟩ tail m
  rw [address_observation] at h
  change runSlice frame bytesCode ⟨tail,m⟩ = some ⟨wrap (7 + 2^256 - 3)::tail,m⟩ at h
  rw [wrap_four] at h
  exact h

theorem wrong_environment :
    runSlice frame (PublishedValues.code .msgSender ⟨3,by decide⟩) ⟨[],fun _ => 0⟩ ≠
      some ⟨[lenU 4 (by decide)],fun _ => 0⟩ := by
  intro h
  have hs := congrArg (fun x => x.map (fun s => s.stack.map (fun w => w.val))) h
  have bad : (some [((2^256 : Nat)-3 : Int)] : Option (List Int)) = some [4] := hs
  have := List.cons.inj (Option.some.inj bad)
  have he : ((2^256 : Nat)-3 : Int) ≠ 4 := by decide
  exact he this.1

theorem wrong_order :
    runSlice frame [select .selfAddress,constant 1 ⟨3,by decide⟩,.op .SUB] ⟨[],fun _ => 0⟩ ≠
      some ⟨[lenU 4 (by decide)],fun _ => 0⟩ := by
  intro h
  have hs := congrArg (fun x => x.map (fun s => s.stack.map (fun w => w.val))) h
  have bad : (some [((2^256 : Nat)-4 : Int)] : Option (List Int)) = some [4] := hs
  have he : ((2^256 : Nat)-4 : Int) ≠ 4 := by decide
  exact he (List.cons.inj (Option.some.inj bad)).1

/-- The published environment component supports this observation; the legacy
symbolic value recognizer still refuses it. No fragment predicate is erased. -/
theorem self_balance_refused :
    (compileVal 0 (Evm.Frag.init []) (.simple (.env .selfBalance rfl) : Val C [] .uint)).isNone = true :=
  by decide +kernel

/-- Success at all actual boundaries does not dispense with stack capacity. -/
theorem actual_prefix_capacity (tail : List Backend.Environment.Word)
    (bound : tail.length + 2 ≤ 1024) :
    tail.length ≤ 1024 ∧ (rhs::tail).length ≤ 1024 ∧
    (observe frame .selfAddress::rhs::tail).length ≤ 1024 ∧
    (lenU 4 (by decide)::tail).length ≤ 1024 := by
  simp only [List.length_cons]
  omega

/-- Even though this local evaluator allows arbitrary mathematical tails,
1023 saved words cannot accommodate the two operand pushes on a real stack. -/
theorem capacity_negative : ¬ (1023 + 2 ≤ 1024) := by decide

def invocation : Backend.Scalar.CheckedInvocation Backend.Scalar.checkedUintSub
    (state.envVal .selfAddress) (lenU 9 (by decide)) [99] where
  testCapacity := by decide +kernel
  bodyCapacity := by decide +kernel

theorem reached_guard_prefix (m : Memory) :
    runSlice frame [constant 1 ⟨9,by decide⟩, select .selfAddress]
      ⟨[lenU 99 (by decide)],m⟩ =
        some ⟨[lenU 7 (by decide),lenU 9 (by decide),lenU 99 (by decide)],m⟩ :=
  PublishedValues.operands frame .selfAddress ⟨9,by decide⟩ [lenU 99 (by decide)] m

theorem reached_guard :
    Backend.Scalar.guarded Backend.Scalar.checkedUintSub.test Backend.Scalar.checkedUintSub.body
      Backend.Scalar.overflowFailure
      (Backend.Scalar.encodeValue .uint (observe frame .selfAddress)::
        Backend.Scalar.encodeValue .uint (lenU 9 (by decide))::[99]) =
      some (.error Backend.Scalar.overflowFailure) :=
  PublishedValues.checked_application Backend.Scalar.checkedUintSub state frame represented .selfAddress
    (lenU 9 (by decide)) [99] invocation

theorem guard_bytes : Backend.encode Backend.Scalar.checkedUintSub.test = [0x81,0x81,0x10] ∧
    Backend.encode Backend.Scalar.checkedUintSub.body = [0x03] := ⟨rfl,rfl⟩

theorem guard_is_not_division : Backend.Scalar.overflowFailure ≠ Backend.Scalar.divisionFailure := by decide +kernel

theorem ignored_guard (tail : Backend.Scalar.Stack) :
    Backend.Scalar.run Backend.Scalar.checkedUintSub.body (7::9::tail) =
      some ((7-9 : BitVec 256)::tail) ∧
    Backend.Scalar.guarded Backend.Scalar.checkedUintSub.test Backend.Scalar.checkedUintSub.body
      Backend.Scalar.overflowFailure (7::9::tail) = some (.error Backend.Scalar.overflowFailure) := by
  constructor <;> rfl

theorem actual_observation (tail : List Evm.Word) :
    ∃ a : Fin Evm.W,
      Evm.run compiled.code {machine with stack := tail} =
        .ok ({machine with stack := tail}.push (.val a)) 0 ∧
      Backend.Scalar.encodeValue .uint (lenU 4 (by decide)) = BitVec.ofNat 256 a.val := by
  obtain ⟨w, hw, ht⟩ := physical_value tail
  obtain ⟨a, rfl, ha⟩ := PublishedValues.represented_word hw
  exact ⟨a, ht, ha⟩

def checkedExpr : Val C [] .uint :=
  .binop .sub rfl rfl (.simple (.env .selfAddress rfl)) (.simple (.lit 9 rfl))
def checkedCompiled : CompiledVal 0 (Evm.Frag.init []) checkedExpr :=
  (compileVal 0 (Evm.Frag.init []) checkedExpr).get (by decide +kernel)

theorem intrinsic_failure : checkedExpr.evalT state = .error .revert := rfl

/-- Coarse symbolic revert remains distinct from the scalar component's
Panic(0x11) byte observation; this is not a public ABI adequacy theorem. -/
theorem coarse_failure (tail : List Evm.Word) :
    Evm.run checkedCompiled.code {machine with stack := tail} = .revert :=
  (value_revert_iff checkedCompiled physical_input tail).mpr intrinsic_failure

end Solidity.Backend.Passes.PublishedValueControls
