import Solidity.Backend.AbiWorld.PanicCallFrame
import Solidity.Semantics.AllocBytes
import Solidity.Backend.AbiWorld.ErrorReadWindowControls

namespace Solidity.Backend.AbiWorld.PanicCallFrameControls
open Semantics Failure PanicReadWindow PanicCallFrame

def contract : Contract := {vars := []}
abbrev Γ : Ctx := [.val .uint,.val .uint,.mem bytesR,.mem bytesR]
def initial : State contract [] :=
  {State.init contract with tx := {selfAddress := ⟨7,by decide⟩}}
def older := initial.allocPush (bytesObj initial.H [161,178] (by decide))
def caller : State contract Γ :=
  ((older.push (t:=.mem bytesR) (TEnv.get .here older.env)).push
    (t:=.val .uint) ⟨77,by decide⟩).push (t:=.val .uint) ⟨0,by decide⟩
def call (a : Nat := 7) (ha : a < 2^256 := by decide) : ExtCall contract Γ :=
  ⟨.lit a (PrimTy.inRange_uint_of_lt ha),"callee",[]⟩
def branch (n : Nat) (hn : n < 2^256) : Prog contract Γ (.val .bool :: Γ) :=
  .cons (.assignLocal .here (.simple (.lit n (PrimTy.inRange_uint_of_lt hn))))
    (.cons (.declLocal .bool (.user "clauseLocal") (some (.simple (.bool true)))) .nil)
def panicBranch : Prog contract (.val .uint :: Γ) (.val .bool :: .val .uint :: Γ) :=
  .cons (.assignLocal (.there .here) (.simple (.local .here)))
    (.cons (.declLocal .bool (.user "clauseLocal") (some (.simple (.bool true)))) .nil)
def attempt (body : Prog contract [] []) (a : Nat := 7) (ha : a < 2^256 := by decide) : Stmt contract Γ Γ :=
  .tryCall (call a ha) .nil (branch 10 (by decide)) (branch 20 (by decide))
    (.some (.user "panicCode")) panicBranch (branch 30 (by decide)) .nil body true

def observe (σ : State contract Γ) : Int × Int × Nat × List (Nat × List Nat) :=
  ((TEnv.get .here σ.env).val,(TEnv.get (.there .here) σ.env).val,σ.H.length,
    ([TEnv.get (.there (.there .here)) σ.env,
      TEnv.get (.there (.there (.there .here))) σ.env] : List (Option (HRef σ.H bytesR))).filterMap
       (fun r => r.map (fun r => (r.id,(σ.heap.get r : MObj σ.H bytesR).1.map (fun b => b.val.toNat)))))

/-- Arbitrary code and trailing bytes, with actual callee execution, exact
code binding/pop, preserved marker, older aliases and their ordered bytes. -/
theorem application (n : Nat) (hn : n < 2^256) (suffix : List UInt8) :
    ((attempt (callee (encodePanic n ++ suffix))).runR caller).map (fun o => observe o.st) =
      .ok ((n:Int),77,1,[(0,[161,178]),(0,[161,178])]) := by
  have h := selected caller (call 7) (by decide) rfl n hn suffix
    (branch 10 (by decide)) (branch 20 (by decide)) (.some (.user "panicCode"))
    panicBranch (branch 30 (by decide))
  exact (congrArg (fun r => r.map (fun o => observe o.st)) h).trans (by rfl)

theorem zero_receiver (n : Nat) (suffix : List UInt8) :
    ((attempt (callee (encodePanic n ++ suffix)) 0).runR caller).halt? = some .revert := by rfl

theorem truncated_not_panic :
    ((attempt (callee ((encodePanic 300).take 35))).runR caller).map (fun o => observe o.st) =
      .ok (30,77,1,[(0,[161,178]),(0,[161,178])]) := by with_unfolding_all rfl

theorem full_word_not_byte :
    ((attempt (callee (encodePanic 300 ++ [255]))).runR caller).map (fun o => (observe o.st).1) ≠ .ok 44  := by
  have h := application 300 (by decide) [255]
  have hm : (((attempt (callee (encodePanic 300 ++ [255]))).runR caller).map (fun o => observe o.st)).map Prod.fst =
      ((attempt (callee (encodePanic 300 ++ [255]))).runR caller).map (fun o => (observe o.st).1) := by
    cases (attempt (callee (encodePanic 300 ++ [255]))).runR caller <;> rfl
  have projected := congrArg (fun r : TRes (Int × Int × Nat × List (Nat × List Nat)) => r.map Prod.fst) h
  change (((attempt (callee (encodePanic 300 ++ [255]))).runR caller).map (fun o => observe o.st)).map Prod.fst = .ok (300:Int) at projected
  rw [hm] at projected
  intro bad
  have impossible : (300:Int) = 44 := Except.ok.inj (projected.symm.trans bad)
  omega

theorem wrong_selector_not_panic :
    ((attempt (callee (0 :: (encodePanic 300).drop 1))).runR caller).map (fun o => observe o.st) =
      .ok (30,77,1,[(0,[161,178]),(0,[161,178])]) := by with_unfolding_all rfl

theorem overflow_wraps :
    (decodePanic (encodePanic (2^256))).map Subtype.val = some (0:Int) := by decide +kernel

/-- Out-of-word naturals are not the code read from their modular bytes. -/
theorem overflow_not_natural :
    (decodePanic (encodePanic (2^256))).map Subtype.val ≠ some (2^256:Int) := by decide +kernel

def codes : List Nat := [0,1,17,18,33,49,50,65,81,300,2^255,2^256-1]
def suffix : List UInt8 := [222,173,0,255]
def packets : List (List UInt8) := codes.map (fun n => encodePanic n ++ suffix)

local instance (a : Nat) (bs : List UInt8) : Decidable (Fits a bs) :=
  inferInstanceAs (Decidable (a<wordLimit ∧ bs.length<wordLimit ∧ a+bs.length≤wordLimit))
theorem code_bounds : codes.all (fun n => decide (n < wordLimit)) = true := by decide
theorem emitter_capacity : codes.all (fun n => decide (Fits 8 (encodePanic n))) = true := by decide

theorem emitted_member (n : Nat) (member : n ∈ codes) :
    let hn := of_decide_eq_true ((List.all_eq_true.mp code_bounds) n member)
    Slice.checkedRun (emit 8 (.panic ⟨n,hn⟩)) ErrorReadWindowControls.machine =
      some ({ErrorReadWindowControls.machine with memory := Slice.putBytes ErrorReadWindowControls.machine.memory 8 (encodePanic n)},some (Roadmap.Outcome.revert (encodePanic n))) ∧
    decodePanic (Slice.getBytes (Slice.putBytes ErrorReadWindowControls.machine.memory 8 (encodePanic n)) 8 36) = some (word n hn) := by
  have hn := of_decide_eq_true ((List.all_eq_true.mp code_bounds) n member)
  simpa only [List.append_nil] using PanicReadWindow.emitted ⟨n,hn⟩ 8 [] ErrorReadWindowControls.machine
    (of_decide_eq_true ((List.all_eq_true.mp emitter_capacity) n member)) (by decide)
end Solidity.Backend.AbiWorld.PanicCallFrameControls
#print axioms Solidity.Backend.AbiWorld.PanicCallFrameControls.application
#print axioms Solidity.Backend.AbiWorld.PanicCallFrameControls.zero_receiver
#print axioms Solidity.Backend.AbiWorld.PanicCallFrameControls.truncated_not_panic
#print axioms Solidity.Backend.AbiWorld.PanicCallFrameControls.full_word_not_byte
#print axioms Solidity.Backend.AbiWorld.PanicCallFrameControls.wrong_selector_not_panic
#print axioms Solidity.Backend.AbiWorld.PanicCallFrameControls.code_bounds
#print axioms Solidity.Backend.AbiWorld.PanicCallFrameControls.emitter_capacity
#print axioms Solidity.Backend.AbiWorld.PanicCallFrameControls.emitted_member
#eval IO.println ("PANIC_PACKETS=" ++ Solidity.Backend.AbiWorld.ErrorReadWindowControls.jsonPackets Solidity.Backend.AbiWorld.PanicCallFrameControls.packets)
#eval IO.println ("PANIC_CODES=" ++ "[" ++ String.intercalate "," (Solidity.Backend.AbiWorld.PanicCallFrameControls.packets.map (fun bs => toString (((Solidity.Semantics.decodePanic bs).map Subtype.val).getD (-1)))) ++ "]")
#eval IO.println ("PANIC_EMITTED_BYTES=" ++ Solidity.Backend.AbiWorld.ErrorReadWindowControls.jsonPackets (Solidity.Backend.AbiWorld.PanicCallFrameControls.codes.map (fun n => Solidity.Backend.Failure.Slice.getBytes (Solidity.Backend.Failure.Slice.putBytes Solidity.Backend.AbiWorld.ErrorReadWindowControls.machine.memory 8 (Solidity.Semantics.encodePanic n)) 8 36)))

#print axioms Solidity.Backend.AbiWorld.PanicCallFrameControls.overflow_wraps
#print axioms Solidity.Backend.AbiWorld.PanicCallFrameControls.overflow_not_natural
