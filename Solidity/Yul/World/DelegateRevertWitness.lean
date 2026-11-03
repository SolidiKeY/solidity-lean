import Solidity.Yul.World.DelegateRevertControls
namespace Solidity.Yul.World.DelegateRevertWitness
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.DelegatePhysical
open Solidity.Yul.World.DelegateRevertPort

def old : Bytes := [0xa1,0xa2,0xa3,0xa4]
def heap (G : Glob env) : Source.Heap env.layout := ((StateCallChecks.heap G).alloc ⟨.bytes .memory,.bytes old⟩).1

theorem live (G : Glob env) (a : Nat) (present : ((heap G).cells a).isSome) : a<2 := by
  by_cases inside : a<2
  · exact inside
  have outside : ¬a<2 := inside
  have bound : (heap G).next≤a := by change 2≤a; omega
  rw [(heap G).bounded a bound] at present
  cases present

def placement (G : Glob env) : Placement (heap G) where
  address a:=if a=0 then 128 else 256
  shape _:=.bytes 4
  free:=320
  free_start:=by decide
  distinct a b ha hb eq := by
    have aa:=live G a ha; have bb:=live G b hb
    by_cases az : a=0 <;> by_cases bz : b=0
    · omega
    · simp only [if_pos az,if_neg bz] at eq; omega
    · simp only [if_neg az,if_pos bz] at eq; omega
    · omega
  typed a τ d found := by
    by_cases az : a=0
    · subst a
      change some (⟨.bytes .memory,.bytes (input G)⟩ : Σ σ,Source.Data env.layout σ)=some ⟨τ,d⟩ at found
      cases found
      simpa only [input_length] using HasMemoryShape.bytes (D:=env.layout) (l:=.memory) (input G)
    · by_cases ao : a=1
      · subst a
        change some (⟨.bytes .memory,.bytes old⟩ : Σ σ,Source.Data env.layout σ)=some ⟨τ,d⟩ at found
        cases found
        exact HasMemoryShape.bytes (D:=env.layout) (l:=.memory) old
      · have bound : (heap G).next≤a := by change 2≤a; omega
        rw [(heap G).bounded a bound] at found
        cases found
  starts a _ := by split <;> decide
  ends a _ := by split <;> decide
  separate a b ha hb ne := by
    have aa:=live G a ha; have bb:=live G b hb
    by_cases az : a=0 <;> by_cases bz : b=0
    · omega
    · simp only [if_pos az,if_neg bz]; left; decide
    · simp only [if_neg az,if_pos bz]; right; decide
    · omega

def inputEntry (G : Glob env) : HeapByteEntry (heap G) := ⟨0,false,input G,rfl⟩
def outputEntry (G : Glob env) : HeapByteEntry (heap G) := ⟨1,false,old,rfl⟩
def memory (G : Glob env) := encodeByteHeap (placement G) [inputEntry G,outputEntry G]
  (mstore (mstore (fun _=>0x5a) 64 320) 96 0)

theorem distinct_entries (G : Glob env) : ([inputEntry G,outputEntry G].map HeapByteEntry.id).Nodup := by
  change ([0,1] : List Nat).Nodup
  decide

def locals : Locals env.layout [ReturningCall.uint,.bytes .memory,.bytes .memory] :=
  .cons (.int 0x99 (by decide)) (.cons (.memRef rfl 1) (.cons (.memRef rfl 1) .nil))
def fnLocals : Locals env.layout [.bytes .memory,.bytes .memory] := .cons (.memRef rfl 1) (.cons (.memRef rfl 1) .nil)
def source (G : Glob env) : EMState env [ReturningCall.uint,.bytes .memory,.bytes .memory] :=
  ⟨locals,{(DelegateRevertControls.source G).2 with heap:=heap G,fnLocals:=⟨[.bytes .memory,.bytes .memory],fnLocals⟩}⟩

theorem loaded (G : Glob env) : PhysicalHeapPort.port.load (memory G) 160 4=some (input G) := by
  have actual:=PhysicalHeapPort.load_encoded (heap G) (placement G) [inputEntry G,outputEntry G] (distinct_entries G)
    (inputEntry G) List.mem_cons_self (mstore (mstore (fun _=>0x5a) 64 320) 96 0)
  simpa only [inputEntry,PhysicalHeapPort.payloadOffset,placement,input_length] using actual

theorem reads (G : Glob env) : (outputEntry G).Reads (placement G) (memory G) :=
  encodeByteHeap_reads (placement G) [inputEntry G,outputEntry G] (distinct_entries G)
    (mstore (mstore (fun _=>0x5a) 64 320) 96 0) (outputEntry G) (List.mem_cons_of_mem _ List.mem_cons_self)

def run (G : Glob env) := DelegateRevertPort.run G 0 (by decide) (source G)
  DelegateChecks.sender DelegateChecks.target DelegateChecks.value 10000 (by decide) rfl
  DelegateRevertControls.residue rfl DelegateRevertControls.encoding DelegateRevertControls.plan
  (Option.some_get DelegateRevertControls.ready).symm DelegateRevertControls.observer rfl (memory G) 160 4 (loaded G)
  (placement G) (outputEntry G) 1 4 2

def expected (G : Glob env) := HeapOutputTransport.image
  (completed G (source G) DelegateRevertControls.residue DelegateRevertControls.encoding DelegateRevertControls.observer)
  (heap G) (heap_eq G (source G) DelegateRevertControls.residue DelegateRevertControls.encoding DelegateRevertControls.observer)
  (placement G) (outputEntry G) (memory G) 1 [0x11,0x22]

theorem run_exact (G : Glob env) : run G=some (.ok (.revert (errorData G)),expected G) := by
  apply argument_copy
  · change (3 : Nat)≤4
    decide
  · exact (reads G).1
  · exact (reads G).2

theorem alias_readback (G : Glob env) :
    (DelegateRevertHeap.copied (source G) (outputEntry G) 1 [0x11,0x22]).2.heap.get 1=
      some ⟨.bytes .memory,.bytes [0xa1,0x11,0x22,0xa4]⟩ :=
  DelegateRevertHeap.alias (source G) (outputEntry G) 1 [0x11,0x22] 1 rfl

theorem actual_mutation (G : Glob env) :
    (DelegateRevertHeap.copied (source G) (outputEntry G) 1 [0x11,0x22]).2.heap.get 1≠(source G).2.heap.get 1 := by
  rw [alias_readback]
  change some (⟨.bytes .memory,.bytes [0xa1,0x11,0x22,0xa4]⟩ : Σ σ,Source.Data env.layout σ)≠some ⟨.bytes .memory,.bytes old⟩
  intro same
  have payload := Source.Data.bytes.inj (eq_of_heq (Sigma.mk.inj (Option.some.inj same)).2)
  exact (by decide : ([0xa1,0x11,0x22,0xa4] : Bytes)≠old) payload

theorem input_untouched (G : Glob env) :
    (DelegateRevertHeap.copied (source G) (outputEntry G) 1 [0x11,0x22]).2.heap.get 0=(source G).2.heap.get 0 :=
  DelegateRevertHeap.other (source G) (outputEntry G) 1 [0x11,0x22] 0 (show (0 : Nat)≠1 from by decide)

def childEntry (G : Glob env) : EMState env [] := ⟨Source.L0 env,{(source G).2 with heap:=Source.Heap.empty}⟩

theorem actual_body_reverts (G : Glob env) :
    (Source.callInternal (glob true G) (DelegateBody.frame account DelegateChecks.sender DelegateChecks.value 1)
      7 ReturningCall.answerDecl .nil [ReturningCall.uint]).run (childEntry G)=
      (.error (.revert (errorData G)),changed (childEntry G) account) :=
  DelegateBody.internal_revert G account DelegateChecks.sender DelegateChecks.value 1 (childEntry G)

theorem source_write_is_nontrivial (G : Glob env) :
    ((childEntry G).2.ex.world.accounts account).storage.read flagPath=some (.bool false) ∧
    ((changed (childEntry G) account).2.ex.world.accounts account).storage.read flagPath=some (.bool true) := ⟨rfl,rfl⟩

theorem full_image (G : Glob env) :
    expected G=(completed G (source G) DelegateRevertControls.residue DelegateRevertControls.encoding DelegateRevertControls.observer,
      some ((Solidity.Backend.Environment.writeBytes (memory G) 289 [0x11,0x22],
        DelegateRevertHeap.copied (source G) (outputEntry G) 1 [0x11,0x22]),
        (DelegateRevertControls.residue,DelegateRevertControls.encoding),
        (completed G (source G) DelegateRevertControls.residue DelegateRevertControls.encoding DelegateRevertControls.observer).2)) :=
  DelegateRevertHeap.image_exact G (source G) _ _ _ (placement G) (outputEntry G) (memory G) 1 [0x11,0x22]

theorem wrong_heap (G : Glob env) : (StateCallChecks.heap G).get 1=none ∧ (heap G).get 1=some ⟨.bytes .memory,.bytes old⟩ := ⟨rfl,rfl⟩

def after (G : Glob env) := DelegateRevertHeap.copied (source G) (outputEntry G) 1 [0x11,0x22]

theorem alias_evaluation (G : Glob env) :
    (Source.bytesOfRV (E:=env) ReturningCall.parentFrame 1 (.val ((after G).1.get (.there .here)))).run (after G)=
      (.ok [0xa1,0x11,0x22,0xa4],after G) ∧
    (Source.bytesOfRV (E:=env) ReturningCall.parentFrame 1 (.val ((after G).1.get (.there (.there .here))))).run (after G)=
      (.ok [0xa1,0x11,0x22,0xa4],after G) ∧
    (Source.bytesOfRV (E:=env) ReturningCall.parentFrame 1 (.val ((after G).2.fnLocals.2.get .here))).run (after G)=
      (.ok [0xa1,0x11,0x22,0xa4],after G) := ⟨rfl,rfl,rfl⟩

theorem source_memOK (G : Glob env) : Source.MemOK env (heap G).ty (source G) := by
  have ok : HeapOK (E:=env) (heap G) := HeapOK.alloc (StateCallChecks.caller_memOK G).1.1.heap (.bytes old)
  have shaped : HeapShaped (E:=env) (heap G) :=
    HeapShaped.alloc (E:=env) (x:=⟨.bytes .memory,.bytes old⟩) (StateCallChecks.caller_memOK G).2.1 trivial
  have inner : HeapInner (E:=env) (heap G) :=
    HeapInner.alloc (E:=env) (x:=⟨.bytes .memory,.bytes old⟩) (StateCallChecks.caller_memOK G).2.2 trivial
  exact ⟨⟨⟨ok,HeapTy.Le.refl _⟩,⟨trivial,⟨⟨.bytes .memory,rfl,rfl⟩,⟨⟨.bytes .memory,rfl,rfl⟩,trivial⟩⟩⟩⟩,shaped,inner⟩

theorem after_memOK (G : Glob env) : Source.MemOK env (heap G).ty (after G) :=
  DelegateRevertHeap.memOK (source G) (outputEntry G) 1 [0x11,0x22] (heap G).ty (source_memOK G)
end Solidity.Yul.World.DelegateRevertWitness
